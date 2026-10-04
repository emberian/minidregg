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
| Profiles: `blake3 derive_key("mini/<generation>", seed64)` → Ed25519 (+ ML-DSA-65 for the hybrid), Bread's store format | `profile` | `profile.ts` | yes |
| Signers: Ed25519 and Ed25519 + ML-DSA-65 hybrid behind one `Signer`; `verify` names the failing half (`docs/SDK-PQ.md`) | `signer` | `profile.ts` (hybrid = the Rust core) | yes |
| `Intent` over the cuts Observe/Invoke/Reserve/Install/Release/Retire; canonical bytes (DEFINED by `Kernel/Contracts/Intents.lean`); `InvocationId` | `contracts` | `contracts.ts` (a wrapper over the Rust core, no second encoder) | yes |
| `Intent::lower` → the authoring JSON the local Host's `author intent` reads (Invoke only) | `contracts` | `contracts.ts` | yes |
| `explain()` over Host-presented JSON, bound to the intent/plan/header digests | `explain` | `explain.ts` | yes |
| `Presented` / `Confirmation` / `sign_transaction` | `confirm`, `sign` | `confirm.ts` | yes |
| Attempt custody machine; external `Delivery` custody | `custody` | `custody.ts` (attempts) | yes |
| Consent-process client (ops 220/221/222/224) | `consent` (feature `native`) | — | no |
| Local Host codec client (ops 7–11) | `host` (`native`) | — | no |
| Operator client (prepare/submit/lookup/challenge) over a unix socket or `ssh:DEST` (host key checking on) | `operator` (`native`) | — | no |
| Filesystem custody: leased records, retained attempt dirs | `store` (`native`) | — | no |
| The whole sequence | `flow::Client` (`native`) | — | no |

## Trust level: CLIENT-LOCAL

- Runs on the member's device; key material never leaves it.
- Trusts the device, the member's **independently selected** local semantic Host image and
  consent executable (chosen by local custody — `MINI_LOCAL_HOST`, `MINI_CONSENT_HOST`,
  `MINI_CONSENT_CONFIG` — never by the operator), and the SDK's framing and signing.
- Does not trust the operator socket (unix or ssh): its challenge and plan are offers. Before a key signs,
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
    // `socket` is an absolute unix socket path or `ssh:member@box` (see the ssh route below)
    operator: mini_sdk::operator::Operator::new(mini_sdk::operator::Route::parse(&socket)?, &config, Some(host_sha256))?,
    key: profile.mini_signer(0, mini_sdk::signer::Scheme::Ed25519),
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
  processes and a real Unix socket) and `native/mini-sdk/tests/golden.rs`.
- `native/mini-sdk/golden/vectors.json`: hand-written inputs, the core's outputs under `expect`. Two external
  pins: Bread's `dregg/0` vector `335840a9…8b9a`, and lowering that reproduces a real
  admitted `intent.json` (`native/mini-sdk/tests/fixtures/`, outcome `installed`). Regenerate only for an
  announced format change: `MINI_SDK_REGEN=1 cargo test --test golden`.
- `golden/intents.json` → `golden/lean-intents.json`: the intent inputs, and the bytes (or
  refusals) that Lean's exported entry points produced for them
  (`lean --run Kernel/Contracts/IntentVectors.lean golden/intents.json`). The Rust suite and the TS
  suite require the SDK's encoder to match every admitted row byte for byte and refuse every
  refused row. A stale file (inputs changed, vectors not re-emitted) fails.
- `npm test` in `native/mini-sdk-ts`: rebuilds the wasm core (`--features wasm`,
  `wasm-bindgen --target nodejs`) every run. The intent encoder, canonical JSON, lowering and the
  hybrid scheme are the core itself (no TS copy); what TS still carries natively (derivation,
  Ed25519, explain, digests) is recomputed independently and run against the fresh wasm on golden
  and mutated inputs. Requires node ≥ 23.6 (type stripping).
- `examples/intent.{rs,ts}`: one worked program per SDK (no Host): build an intent, print its bytes
  and digest, sign under both schemes, verify, refuse a tampered signature. Both print the same
  text, pinned by `examples/intent.expected`; the bytes are cross-checked against Lean's row.

## The ssh route

`ssh:DEST` (`operator::Route`) runs one `ssh -T DEST` session per `Operator` whose stdio is the box's
`mini socket-proxy` (the only command the member's key may run), carrying the unix socket's frames
one reply per request, so the signing key never leaves the member's machine. The SDK builds the
command itself (`BatchMode=yes`, `StrictHostKeyChecking=yes`, `ClearAllForwardings=yes`,
`ControlPath=none`, `ConnectTimeout`, optional `-i`/`-F`): host key checking cannot be weakened by ssh
config. The request is written only after ssh reports `Entering interactive session`; everything
before that is certainly-unsent with a NAMED refusal (host key verification failed, authentication
refused, destination unreachable, session not established within Ns); everything after the write is
uncertain, the session is closed, and the exact request is never resent (a lost reply is a `lookup`
of the same call bytes). `MINI_SSH` names another OpenSSH-compatible program.

## What it does not do

- **Execute.** The Host executes, and re-executes on every replay; that is Mini's evidence.
- **Prove.** Mini admission has no proof carrier; the SDK attaches none.
- **Check plans.** The plan check is the Lean consent process; the SDK is its client.
- **Decode canonical bytes.** The local Host does (`inspect`); the SDK renders its output.
- **Lower Reserve/Install/Release/Retire.** Those cuts have no common native wire yet; `lower`
  refuses them by name.
- **Objective consent (op 227)** is not wrapped until lane W1.2 lands its Objective half.

## Migration (deletion, not addition)

Each consumer that moves deletes its copy: Discord `custody.rs` (done); next
`app_document.rs`'s status machine, `job.rs`, `selected_exchange.rs`, `publisher.rs`, the
Hermes step ledger, the provider spool; then `submit_once`/`retry`, then the client halves of
`client_consent.rs` and `transport.rs` once their owning lanes land.
