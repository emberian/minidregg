# Mini SDK — design note (lane W2.H, 2026-10-04)

Question (Ember): does Mini need its own SDK + browser extension like Bread has?
Answer: the SDK now; the extension when a Mini web surface (Studio/web) is member-reachable.
This note fixes the SDK's shape and designs the extension so that building it later is
lowering, not redesign. Tags: READ = read at source in this clone (base c8fdd000 rebased on
github/main 44b2446a); INFERRED = my reasoning.

## 1. The surface: two nouns, one authorized shape

Bread's shape is `Identity → turn() → typed verbs → .sign() → .submit() → Receipt`. Mini's
signing flow is already split across processes (READ `native/resource-client/src/main.rs`
`submit_once`, `client_consent.rs`, `Host/ClientConsentCore.lean`): a local Lean Host authors
and decodes canonical bytes (ops 7–11), the remote operator socket proposes a challenge and a
plan (ops 4, 1), an independently selected local consent process (`minidregg-client-consent`,
ops 220/221/222/224/226/227) re-derives the plan from the retained intent and an independently
admitted source prefix and returns the exact header bytes a key may sign. The SDK names that
flow; it does not re-derive any of it.

```text
Profile ──► Intent (one typed cut) ──► .explain()  ─► Confirmation (nonce-bound)
                                    ──► .sign(consent, confirmation)  ─► SignedCall
SignedCall ──► .submit(operator) ──► Receipt | Refused | Uncertain ──► .lookup() (same call)
```

* **Noun 1 — `Receipt`**: exactly `NativeHostCodec.Receipt` as the Host's `inspect outcome`
  presents it: `{type:"confirmed", confirmation, transactionId, eventId, acceptedCount,
  worldRoot}` (READ fixture `outcome.json`). Objective needs no new receipt type (R2-2 hop 14).
* **Noun 2 — `Attempt` custody**: the retained exact call and its classified outcome. One
  implementation (§3) replaces the ~40 retained-attempt-directory copies (scout D §3).

`Intent` is built from the SHARED-CONTRACTS cuts, never from free text:
`Observe(resource, projection, viewer)`, `Invoke(resources, command, actor, guards)`,
`Reserve(candidate, footprint, law, obligation)`, `Install(candidate, preimage, effects,
obligation)`, `Release(result projection, audience, law)`, `Retire(obligation, evidence)`, over
`ObjectRef` (native id + governing domain + kind), `RevisionRef` (exact root, never
latest-by-name), `ArtifactRef` (digest, length, format). The SDK defines these to match
SHARED-CONTRACTS. The canonical bytes are DEFINED in Lean, `Kernel/Contracts/Intents.lean`
(`intentCodec`, frame `DREGG/CONTRACT/INTENT/v1`, built from the repo's one `StreamCodec`
nucleus; `@[export] minidregg_intent_encode`), and the SDK carries ONE client-side encoder
(`native/mini-sdk/src/contracts.rs`) that is held to Lean byte for byte by
`golden/lean-intents.json`, which Lean's own entry points emit
(`Kernel/Contracts/IntentVectors.lean`). The TypeScript SDK has no encoder: it reaches the Rust
core through wasm. (Earlier, the SDK owned a `MINI/SDK/INTENT/v1` encoding with a copy in each
language; both are deleted and the format changed: every `InvocationId` changed.)

Only `Invoke` (and `Observe` as the read half) lowers to today's wire: the authoring JSON
`{subject, nonce, grants, purpose:{type:"prepare", draft:{type:"invoke", command:{subject,
nonce, targets, family?}}}}` that `mini` hands to Host op 7 (READ `intent.json` fixture,
`workspace.rs` `unsigned_invocation_command`, `invocation_family`). Reserve/Install/Release/
Retire have no common wire yet (scout D §3: "Retire: names only"); the SDK types exist so
consumers stop inventing per-domain shapes, and their `lower()` refuses with a named reason
rather than guessing a wire.

## 2. Identities: four distinct numbers, never conflated

SHARED-CONTRACTS separation #11. `InvocationId` = SHA-256 of the canonical intent, which
includes a client-chosen 16-byte `request_salt` fixed at creation (two deliberate identical
transfers are two invocations). `attempt` = 1,2,… under one InvocationId; a new attempt is
legal only after the previous one is DEFINITELY not admitted (refused before effect, or never
transmitted — no `call.bin`). `command nonce` = the decimal u128 inside the signed command,
fresh per attempt. `intent nonce` = the observation intent's own nonce. A lost reply is
recovered by exact lookup of the SAME call bytes (Host op 3), never by a new nonce
(this is bug D7, job settle). The custody state machine makes the wrong move unrepresentable.

## 3. Attempt custody: one state machine

```text
Drafted ─prepare─► Prepared{intent,plan,headers sha} ─sign─► Sealed{call sha, fsynced}
Sealed ─transmit─► Confirmed(Receipt) | Refused(reason) | Uncertain
Uncertain ─lookup(same call)─► Confirmed | Refused | Uncertain        (never resubmit-as-new)
Refused | NeverSent ─next_attempt─► Drafted(attempt+1, fresh command nonce)
```

`confirmation ∈ {installed, replayed, recoveredAfterUncertainResponse}` all mean Confirmed
(READ `workspace.rs` `retained_attempt_outcome`). "Newest explicit refusal wins unless any
confirmation exists" is kept exactly. Storage is a trait: the native store writes the existing
attempt-directory layout (`call.bin`, `outcome.json`, `retry-*`), owner-private, fsync then
rename; the browser store is extension storage. External delivery (a Discord webhook post) uses
the same machine with `Uncertain` resolvable only by operator-supplied destination evidence —
destination custody is not Mini custody (DISCORD-WORLD-ENTRANCE).

## 4. `.explain()` and nothing signs blind

`explain()` is a pure, total function from Host-PRESENTED JSON (the local Host's decoding of
the exact bytes — the SDK never decodes Lean canonical bytes itself) to text lines: the
invocation's targets/actions as authored, then the plan's height, world root and each signing
slot (role, key id, epoch, validUntil). Unknown action/payload types render as
`UNKNOWN … — do not sign blind`, never elided. The reading is bound to
`[intent sha256] [plan sha256] [headers sha256]`.

`.sign()` requires two things: (a) the consent host's headers for this exact
(intent.bin, plan.bin) — op 222 — and (b) a `Confirmation` whose digest is
`SHA-256("MINI/SDK/CONFIRM/v1" ‖ invocationId ‖ attempt ‖ sha(intent) ‖ sha(plan) ‖
sha(headers) ‖ sha(explanation text) ‖ confirmNonce)`. The SDK signs exactly the header bytes
the consent host returned (ed25519 over the raw header, as `sign_headers` does today) and
nothing else. It IS NOT a consent host: the plan check is Lean (`NativeClientConsent`,
`NativeSpecializedConsent`); the SDK is the client of the consent process's stdio frame
protocol (`[u32 len][op][payload]`, READ `client_consent.rs::round_trip`), so there is still
exactly one plan check. `transport.rs`'s 29-opcode operator-plan check (ops 224) stays where it
is; SDK callers that use specialized opcodes call `consent.operator_plan` the same way.

## 5. Trust level: CLIENT-LOCAL (stated like Bread's)

Runs on the member's device. Trusts: the device, the member's selected local semantic Host
image and consent executable (selected by local custody, never by the operator), and the SDK's
correct framing/signing. Does NOT trust: the operator socket (its challenge and plan are offers
re-derived by consent), served presentations (only the local Host's decoding is rendered), or
other members (mediated by capabilities). Key material stays on device. The SDK does not
execute, prove, or decide admission: the Host executes and re-executes on every replay
(deterministic re-execution is Mini's evidence, R2-2 §4); proofs are not part of mini
admission.

## 6. wasm32 constraint

The offline core (`mini-sdk`, default features off) builds for `wasm32-unknown-unknown`: no
Lean link, no processes, no filesystem, no sockets. It contains profiles + derivation, the
intent types + canonical encoding + InvocationId, the confirmation digest, `explain()`, header
signing, and the custody state machine. The `native` feature adds the consent-process client,
the operator-socket client (`[u32 len][version 1|2][u32 cfgLen][cfg][hostSha?][op][payload]`,
READ `transport.rs::invoke_inner`) and the filesystem custody store. A wasm build therefore
cannot reach consent by itself: in a browser, consent and the local Host are reached through a
native-messaging host (§8). The SDK builds and signs; the Host executes.

## 7. What moves in, over time (deletion, not addition)

Each move deletes a copy; no move keeps both. (1) Attempt custody: `retained_attempt_outcome`,
`accepted_outcome` and the per-family status machines in `app_document.rs`, `job.rs`,
`selected_exchange.rs`, `publisher.rs`, Discord `custody.rs`, the Hermes step ledger, the
provider spool (scout D: 40 files). (2) The plan/seal/submit/lookup sequence (`submit_once`,
`retry`) and its 30 per-family re-spellings. (3) The consent frame client (`client_consent.rs`
`invoke/round_trip/pair/headers`) — after W1.2 lands the Objective half, `resource-client`
calls `mini_sdk::consent` and its copy is deleted. (4) The operator-socket frame client
(`transport.rs` client half; the server half stays). Order: custody first (largest, bug-dense:
D2, D5, D7 were bugs in copies), then submit/lookup, then consent/transport after their owning
lanes land.

## 8. The extension (build when Studio/web is member-reachable)

**Precondition (explicit):** the extension needs either a native-messaging bridge to a
member-held replica or the thin-peer consent producer (R2-1 lists thin remote witnesses as
OPEN). A member-reachable web surface is necessary but not sufficient.

A Cipherclerk-shaped MV3 extension, same architecture as Bread's (page `window.mini` →
nonce-scoped content bridge with per-origin/per-method grants → background service worker):

* **Profiles**: named identities from the shared profile store format; key at rest under
  PBKDF2/AES-GCM as Bread's; one recovery phrase.
* **Intent in, explanation out**: a page submits a typed `Intent` (never a label a bot or page
  interprets as a command — DISCORD-WORLD-ENTRANCE "typed action selection binds exact
  object/revision/actor/action/args"). The background obtains Host presentations and consent
  headers, renders `explain()` (the same Rust, compiled to wasm, so text is byte-identical to
  the CLI's), and opens a confirmation popup bound to the Confirmation digest and a one-shot
  nonce; only that accept releases signatures.
* **The full-peer obstacle (INFERRED from READ docs/CLIENT-SIGNING-CONSENT.md)**: today's
  consent producer is a FULL PEER (it re-admits the source prefix). A browser cannot be one.
  So the extension talks to a local `mini-consent-bridge` native-messaging host (Chrome/Firefox
  native messaging is already `[u32 len][json]` over stdio — the same shape as the consent
  frame) running beside a member-held full replica; or it waits for the thin-peer producer
  (checked read-footprint planner with authenticated openings) that the doc names as missing.
  An extension that signs operator-proposed plans without one of these would reopen hole #2
  (R2-1). This is the gating fact, more than the web surface itself.
* **Submit + receipts**: submit through the operator endpoint the profile pins; custody of the
  exact call in extension storage; `Uncertain` → exact lookup; a receipt list fed by the
  member's signed `since` reads (no unauthenticated event feed exists yet).

## 9. Profile derivation: adopt Bread's store and function, not its key

Decision: Mini profiles live in the same store as Bread's (`$DREGG_HOME/profiles/<name>.json`,
`seed_hex` = 64-byte master seed) and use the same function, `blake3::derive_key(path, seed)` →
Ed25519, at a distinct path family **`mini/<generation>`** (`mini/0` first; a key rotation's
committed next key is `mini/<g+1>`). Why share the store: one recovery phrase, one custody
story, one extension profile list. Why not share the key (Bread uses `dregg/0`): Mini signs raw
Lean-canonical header and intent bytes with no ed25519-level prefix, Bread signs
`dregg-action-sig-v3:` messages; with one key, safety would rest on an argument that the two
byte languages never overlap. Distinct keys remove the question, and keep a member's Bread and
Mini identities unlinkable. Rotation by path makes a seed backup recover every generation; a
seed compromise needs a new seed, which is the honest boundary (rotation protects against key
file loss, not seed loss). Golden vector: seed `00..3f` at `mini/0` is pinned in both the Rust
and TS test suites; `dregg/0` → `335840a9…8b9a` is pinned too, so drift against Bread's
derivation fails here.
