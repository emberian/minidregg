# The Mini SDK

`native/mini-sdk` (Rust, crate `minidregg-mini-sdk`, lib `mini_sdk`) and `native/mini-sdk-ts`
(TypeScript, `@minidregg/sdk`) are the client SDK for Mini: how an app, an agent, a bot or a
browser extension asks the world to do something on a member's behalf without ever signing
bytes the member did not see. Design rationale: `docs/design/SDK-DESIGN.md`.

## The surface

```text
Profile ─► Intent (one typed cut) ─► explain() ─► Confirmation (nonce-bound)
        ─► sign (only consent-returned headers, only under the Confirmation) ─► sealed call
        ─► submit ─► Receipt | Refused | Uncertain ─► lookup (the SAME call bytes)
```

Two nouns:

- **`Receipt`** — exactly the Host's `inspect outcome` presentation of
  `NativeHostCodec.Receipt`: `confirmation` (`installed` | `replayed` |
  `recoveredAfterUncertainResponse`), `transactionId`, `eventId`, `acceptedCount`, `worldRoot`.
- **`Attempt`** — custody of one exact call and what became of it (`custody` module, below).

| Piece | Rust | TS | wasm32 |
|---|---|---|---|
| Profiles: `blake3 derive_key("mini/<generation>", seed64)` → Ed25519, Bread's store format | `profile` | `profile.ts` | yes |
| `Intent` over the cuts Observe/Invoke/Reserve/Install/Release/Retire; canonical bytes; `InvocationId` | `contracts` | `contracts.ts` | yes |
| `Intent::lower` → the authoring JSON the local Host's `author intent` reads (Invoke only) | `contracts` | `contracts.ts` | yes |
| `explain()` over Host-presented JSON, bound to the intent/plan/header digests | `explain` | `explain.ts` | yes |
| `Presented` / `Confirmation` / `sign_transaction` | `confirm`, `sign` | `confirm.ts` | yes |
| Attempt custody machine; external `Delivery` custody | `custody` | `custody.ts` (attempts) | yes |
| Consent-process client (ops 220/221/222/224) | `consent` (feature `native`) | — | no |
| Local Host codec client (ops 7–11) | `host` (`native`) | — | no |
| Operator-socket client (prepare/submit/lookup/challenge) | `operator` (`native`) | — | no |
| Filesystem custody: leased records, retained attempt dirs | `store` (`native`) | — | no |
| The whole sequence | `flow::Client` (`native`) | — | no |

## Trust level: CLIENT-LOCAL

- Runs on the member's device; key material never leaves it.
- Trusts the device, the member's **independently selected** local semantic Host image and
  consent executable (chosen by local custody — `MINI_LOCAL_HOST`, `MINI_CONSENT_HOST`,
  `MINI_CONSENT_CONFIG` — never by the operator), and the SDK's framing and signing.
- Does not trust the operator socket: its challenge and plan are offers. Before a key signs,
  the Lean consent process re-derives them from the retained intent and an independently
  admitted source prefix and returns the exact header bytes this key may sign. The SDK signs
  those bytes and nothing else.
- Does not trust served presentations: `explain()` renders only the member's own Host's
  decoding. The SDK never decodes Lean canonical bytes itself.

## How a client uses it (Rust, native)

```rust
use mini_sdk::{contracts::*, custody::{Attempt, Phase}, flow::Client, store::AttemptDir};

let profile = mini_sdk::profile::store::active()?.ok_or("no profile")?;
let mut client = Client {
    host: mini_sdk::host::LocalHost::start(&local_host, &settings)?,
    consent: mini_sdk::consent::Consent::start(&consent_host, &settings)?,
    operator: mini_sdk::operator::Operator::new(&socket, &config, Some(host_sha256))?,
    key: profile.mini_key(0),
};
let intent = Intent { actor, request_salt, cut: Cut::Invoke { targets, family: None } };
let attempt = Attempt::first(intent.invocation_id()?, intent_nonce, command_nonce);
let mut prepared = client.prepare(&intent, attempt, &domain)?;
show(&prepared.presented.explanation.text);          // the member reads it
let confirmation = prepared.presented.confirm(ui_nonce)?; // only on their accept
let dir = AttemptDir(attempt_path);
let call = client.seal(&mut prepared, &confirmation, &dir)?; // fsynced before any send
let mut attempt = prepared.attempt;
match client.transmit(&mut attempt, &call, false)? {
    Phase::Uncertain { .. } => { client.transmit(&mut attempt, &call, true)?; } // exact lookup
    Phase::Refused { .. } | Phase::NeverSent { .. } => { /* attempt.successor(fresh, fresh) */ }
    _ => {}
}
```

Rules the types enforce: a lost reply is answered by `lookup` of the same call bytes, never a
new nonce; a successor attempt exists only after a Host refusal or a call that certainly never
left (`NeverSent`), and needs fresh intent and command nonces; a confirmation is for one
invocation, attempt, intent, plan, header list and reading — change any and nothing signs.

A bot or bridge that posts to an external destination uses `custody::Delivery` with
`store::Record`: retain `start` before the send, `complete` only on destination evidence; a
started, uncompleted delivery is UNKNOWN and is never re-sent (`mini-discord-mirror` does this).

## How a browser or JS app uses it

`@minidregg/sdk` builds intents, computes `InvocationId`, lowers, renders `explain()`, checks
confirmations, signs, and runs the attempt machine — byte-identical to the Rust core. It has no
consent process: a browser is not a full peer. A web page or extension reaches the member's
local Host and consent process through a native-messaging bridge to a member-held replica (the
extension precondition, `SDK-DESIGN.md` §8); until that bridge or a thin-peer consent producer
exists, a browser surface must not sign Mini plans.

## Tests and the differential

- `cargo test --offline --locked --features native` in `native/mini-sdk`: unit tests (custody
  machine, explain totality, confirmation binding, consent/operator framing against scripted
  processes and a real Unix socket) and `tests/golden.rs`.
- `golden/vectors.json`: hand-written inputs, the core's outputs under `expect`. Two external
  pins: Bread's `dregg/0` vector `335840a9…8b9a`, and lowering that reproduces a real
  admitted `intent.json` (`tests/fixtures/`, outcome `installed`). Regenerate only for an
  announced format change: `MINI_SDK_REGEN=1 cargo test --test golden`.
- `npm test` in `native/mini-sdk-ts`: rebuilds the wasm oracle (`--features wasm`,
  `wasm-bindgen --target nodejs`) every run, recomputes every golden value in pure TS, and runs
  TS against the fresh wasm on golden and mutated inputs. Requires node ≥ 23.6 (type stripping).

## What it does not do

- **Execute.** The Host executes, and re-executes on every replay; that is Mini's evidence.
- **Prove.** Mini admission has no proof carrier; the SDK attaches none.
- **Check plans.** The plan check is the Lean consent process; the SDK is its client.
- **Decode canonical bytes.** The local Host does (`inspect`); the SDK renders its output.
- **Lower Reserve/Install/Release/Retire.** Those cuts have no common native wire yet; `lower`
  refuses them by name. TODO(W2.A): the intent encoding becomes the Lean contract codec's.
- **Objective consent (op 227)** is not wrapped until lane W1.2 lands its Objective half.

## Migration (deletion, not addition)

Each consumer that moves deletes its copy: Discord `custody.rs` (done); next
`app_document.rs`'s status machine, `job.rs`, `selected_exchange.rs`, `publisher.rs`, the
Hermes step ledger, the provider spool; then `submit_once`/`retry`, then the client halves of
`client_consent.rs` and `transport.rs` once their owning lanes land.
