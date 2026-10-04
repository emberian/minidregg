# SDK post-quantum keys: what exists, and what the Host must change

Ember prefers PQ/hybrid. The SDK now signs hybrid end to end on the client side; **the Host does not
admit a hybrid key yet.** This note says exactly what exists and exactly what the Host must change,
read from source at `main` (every file and line below was read, not inferred).

## What the SDK has (client side, executed)

`native/mini-sdk/src/signer.rs` is the signer abstraction. Everything that signs takes a
`&dyn Signer` (`sign.rs`: `sign_intent`, `sign_observation_headers`, `sign_transaction`;
`flow::Client.key`; `consent::Consent` takes the public key as bytes). TS mirrors it
(`Profile.signer(generation, scheme)`, `verify(scheme, ...)`, `signTransaction(signer, ...)`).

| scheme | algorithm code | public key | signature |
|---|---|---|---|
| `Ed25519` | 1 | `ed[32]` | `ed[64]` |
| `HybridEd25519MlDsa65` | 2 (reserved here; the Host defines it) | `ed[32] ‖ ml[1952]` | `ed[64] ‖ ml[3309]` |

* The Ed25519 half signs the raw frame, byte-identical to what the Ed25519 scheme signs, so a Host that
  admits a hybrid key record can verify that half with the verifier it already has.
* The ML-DSA-65 half is FIPS 204 (`fips204 =0.4.6`, pure Rust, already pinned in
  `native/joint-agreement-crypto/Cargo.lock`), seeded entry points only (no RNG, builds for wasm32),
  FIPS 204 context string `MINI/SDK/HYBRID/ML-DSA-65/v1`, deterministic variant (`rnd = 0^32`).
* Keys derive from the profile seed: Ed25519 from `blake3::derive_key("mini/<g>", seed)` (unchanged),
  ML-DSA from `blake3::derive_key("mini/<g>/ml-dsa-65", seed)` (a distinct path, so the PQ key rotates
  with the generation and is not derivable from the Ed25519 key).
* A hybrid signature verifies only if BOTH halves do. The refusal names the half. Tests: sign, verify,
  wrong message, wrong key in either half, either half tampered, ML-DSA half spliced from another
  message, Ed25519-only signature presented as hybrid (refused: a strip is not a downgrade),
  signing under a confirmation, golden pins in `golden/vectors.json` (`signers`), wasm vs TS parity.
* TypeScript has **no separate PQ implementation**: the hybrid scheme is the Rust core's `fips204`
  through wasm. There is no `@noble/post-quantum` in Mini's TS SDK, so the inconsistency
  `cv 01a0f52e-774e` describes (an unaudited JS signer beside a wasm hybrid refusal) does not exist
  here. It still exists in Bread's `sdk-ts` (a different repo); that is not touched.

**Stated difference from Bread.** Bread's `dregg_turn::pq` derives its ML-DSA key through a
Lean-verified keygen core; `fips204` is a pure-Rust FIPS 204 implementation that is not
Lean-verified. That is a trust-base difference, named here, not a hidden one.

## What the Host must change (nothing below exists; each is a Lean/Rust edit)

The Host verifies a participant or fleet signature in exactly one place: the credential signed
envelope. `FleetTurn.admitNative` (`Kernel/FleetTurn.lean:563`), `ParticipantKeyEnrollment.admitNative`,
`SubjectKeyRotation`, and the observation/intent path all call
`CredentialSignatureAdmission.verifyNative`, which calls `CredentialSignatureIO.verify`, which spawns
`native/credential-signature-verifier`. Ed25519 is fixed at five layers:

1. **Algorithm code and the signed header.** `Compiler/CredentialSignatureAdmission.lean:43`
   `def ed25519Algorithm : Nat := 1`. Add `hybridAlgorithm : Nat := 2`.
   * `Selected` (`:120-121`) and `select` (`:136-141`) accept only `algorithm = ed25519Algorithm`
     and `publicKey.length = 32`; they refuse `.unsupportedAlgorithm` / `.publicKeyLength`
     otherwise. Accept `(1, 32)` or `(2, 1984)`.
   * `header` (`:213`) hard-codes `algorithm := ed25519Algorithm`. It must be `key.algorithm`, or a
     hybrid key's signed header would name the wrong scheme and `Admission`
     (`Kernel/CredentialSignedEnvelopeController.lean:314`, `key.algorithm != envelope.header.algorithm
     -> .wrongAlgorithm`) would refuse every hybrid envelope.
   * `verifyNative` (the `CredentialSignatureIO.verify config prepared.controller.key.publicKey ...`
     call) must dispatch on `prepared.controller.key.algorithm`.
2. **The native IO boundary.** `Compiler/CredentialSignatureIO.lean:55-56` and `:77-78` reject any
   public key not 32 bytes (`.publicKeyLength`) and any signature not 64 bytes (`.signatureLength`)
   before the process is spawned. Add `verifyHybrid` with widths 1984 / 3373 (the envelope's
   `signature` field is a length-prefixed `bytesStream`, `CredentialSignedEnvelopeController.lean:155`,
   so the wire already carries it) and a `verify-hybrid` verb.
3. **The native verifier.** `native/credential-signature-verifier/src/main.rs`: `verify` reads exactly
   `PUBLIC_KEY_LENGTH` / `SIGNATURE_LENGTH` (`:29-30`) and calls `verify_strict`. Add a
   `verify-hybrid` verb (add `fips204 = "=0.4.6"`, features `ml-dsa-65`, to its `Cargo.toml`): split
   the key at 32 and the signature at 64, `verify_strict` the Ed25519 half over the frame, then
   `ml_dsa_65::PublicKey::verify(frame, sig, b"MINI/SDK/HYBRID/ML-DSA-65/v1")`; answer `verified\n`
   only if BOTH hold. (It must never accept an Ed25519-only signature for a hybrid key: the key
   record, not the signature, decides which scheme is required.)
4. **Every key-shape gate.** Each restates `algorithm = ed25519Algorithm ∧ publicKey.length = 32`.
   Replace all of them by one predicate `CredentialSignatureAdmission.wellFormedKey` (`(1,32) ∨ (2,1984)`):
   * `Kernel/ParticipantKeyEnrollment.lean:311-312` (the `Accepted` shape) and `:336-337` (admission);
   * `Kernel/SubjectKeyRotation.lean:156-157` and `:175-176`;
   * `Kernel/NativeObservationController.lean:449-450` (`intentKey`, the key an observation must be
     signed by);
   * `Kernel/NativeCurrentSigningKey.lean:26` and `:37` (`select`);
   * `Kernel/PayEnrolV2Decision.lean:169` and `:174`.
5. **Fixed 64-byte signature checks on the client wire.** `Host/Json.lean:3714` (the op 9 `signatures`
   codec: "every signature must contain exactly 64 bytes"), `Compiler/NativeObservationCodec.lean:236`
   (`signature.length == 64` on observation signatures), `Host/Json.lean:5347`. And the consent
   process: `Host/ClientConsentCore.lean:320` requires `signer.length == 32 && key == signer`,
   so consent ops 220/221/222 (which the SDK's `Consent` already frames with the key as bytes) refuse a
   1984-byte key until this is generalized.

Also, and easy to miss:

* **`Compiler/CanonicalRuntimeProfile.lean:160`** pins `[ed25519Algorithm, envelopeCodecVersion]` into
  the profile digest. Adding the algorithm changes the semantics digest: a **re-genesis** (greenfield:
  a rebuild, as usual). Old key records keep working only if their algorithm stays in the pin; say so
  in the commit.
* **Next-key possession.** `ParticipantKeyEnrollment.nextPossessionFrame` (`:67`) is
  `tag ‖ publicKey ‖ nextPublicKey` and its comment says "both 32 bytes for Ed25519". The bytes
  concatenate unambiguously for any fixed widths, but `verifyNext` (`:472-476`) must verify under the
  NEXT key's scheme. Decision needed (one line, not taste-neutral): the next key inherits the
  enrolled key's algorithm (recommended: a rotation never silently downgrades), carried by the key
  record, not inferred from length.
* **The Rust clients.** `native/resource-client`'s `sign_headers` (the one function that turns
  consented headers into the Host's `signatures` list) now signs through `mini_sdk::signer::Signer`,
  so its output width is the scheme's. `mini keygen` still generates an Ed25519 seed and key files
  are still one 32-byte seed: a hybrid key file (Ed25519 seed + ML-DSA `xi`) and `mini keygen
  --scheme hybrid` wait for the Host to admit algorithm 2, because a key the Host refuses to
  enrol is not a feature. The other per-protocol Ed25519 signatures in the crate (sshsig, relay
  hello, cohort frames, room keys) are Ed25519 by their own protocols and are not this list.
* **Fleet.** `FleetTurn` needs no change of its own: it admits through `verifyNative`. "FleetTurn
  admission requires both when the key record is hybrid" is exactly rule 3.

## Why not ship the SDK half alone as a "hybrid" that the Host verifies as Ed25519

Because it would be a downgrade labelled hybrid: a Host that checks only the Ed25519 half accepts a
signature whose ML-DSA half is garbage or missing, and nothing says so. The SDK signs hybrid; the
Host refuses to admit a hybrid key record today (`.unsupportedAlgorithm`); that refusal is the correct
state until rule 3 exists. Do not relax it to Ed25519-only verification.
