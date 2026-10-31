# Restricted PQ cohort cascade and broadcast mailbox

Status: research line (traffic stack 2), outside the public candidate (`docs/DEMO-PREFIX-2026-10-26.md`, R9). The code
exists with unit tests; a two-host receiving run is recorded (below). There is no deployment and no proved anonymity
statement. What it hides, from whom, its premises and its costs are in `docs/TRAFFIC-PRIVACY-PROFILE-P1.md`; this file
says what the code builds.

`src/pq_mailbox.rs` is a restricted batch composition, not the Outfox packet format and not an inherited security
proof of Outfox, Echomix or NymHS. The header of that file says the same.

## Construction

- A public fixed cohort contributes exactly one equal-size packet per epoch, real or dummy. Three independent relay
  operators process complete batches in order, then a separate mailbox receiver (`LAYERS = 4` in `pq_mailbox.rs`).
- Every layer is sealed to a hybrid X25519 + ML-KEM-768 key (`native/hybrid_kem.rs`; layers in
  `native/crypto_transit.rs`, suite v2, with XChaCha20-Poly1305 and a key/cipher commitment). The layer overhead is
  `crypto_transit::OVERHEAD_BYTES`. Batch and manifest frames are `MPB2` / `MPM2` (`BATCH_MAGIC`, `MANIFEST_MAGIC` in `pq_mailbox.rs`); a v1 (pure
  ML-KEM-768) frame refuses by name (`V1_REFUSAL`). Public epoch, width, payload capacity and hop are bound as
  transcript and associated data.
- Profile bounds: width 2..=64 and payload 1024..=262144 bytes (`Profile::check`); the CLI defaults are width 4 and
  payload 65536 (`run` in `pq_mailbox.rs`).
- **Active admission guard.** AEAD plus a shuffle alone does not close injection, replacement or n-1 attacks. Each
  client privately submits hashes of its packet at every stage with its authenticated cohort slot. The registrar
  publishes independently sorted exact hash sets per stage with separate registrar/operator MACs; each relay and the
  receiver check their manifest MAC, the complete admitted input set and the complete peeled output set before any
  claim, forwarding or native effect. Any dropped, duplicated, injected or changed packet refuses the whole epoch.
  The registrar is an additional trust assumption (it sees the private route commitments).
- **Custody.** The complete batch input hash is journaled and a claim is written before processing; the complete output
  is cached; a changed replay refuses; a claim without output after a crash is uncertain and never reprocessed. The
  receiver dispatches only through `scheduled_transport::dispatch_once` (`process_mailbox` in `pq_mailbox.rs`), the durable dispatch
  marker written before the native exchange (the module header of `src/scheduled_transport.rs`), so an unknown outcome is never
  dispatched twice and no verdict is invented.
- **Replies.** The receiver publishes W equal-size reply ciphertexts in one broadcast batch in shuffled order. Every
  client scans the whole batch; a reply opens only under the one-time 32-byte capability embedded inside the receiver's
  protection. The client journals `spent` before releasing a reply (`consume_broadcast` in `pq_mailbox.rs`). Capability class quotas
  are 128, 64 and 64 for the three classes (`live_save_cap` in `pq_mailbox.rs`).
- A real carrier over its quota is replaced by a same-shape cover packet and an owner-private `*.private-refusal`
  (`run` in `pq_mailbox.rs`); a refusal there is a physical carrier outcome, never a Mini outcome.

## Operator path

`mini mix --action ...` (`pq_mailbox::run`; not in `USAGE`): `key` (hybrid operator or receiver key),
`registrar-key` (a 32-byte registrar/operator MAC pin), `native-key` (the hybrid Ed25519 + ML-DSA-65 roster key,
`cohort_tcp::generate_native_key`), `seal`, `batch`, `relay`, `mailbox`, `scan`. Every ordinary action takes `--epoch`,
`--width`, `--payload-bytes` and `--state`; batch, relay and mailbox outputs require public `--origin-ms` and
`--tick-ms`, release at the configured stage time and fail closed on a missed epoch with no catch-up burst. The
networked form is `mini mix-live` (`COHORT-TCP.md`). Ordinary native signatures stay classical: the packet key exchange
is hybrid, the mix is not a full post-quantum stack.

## Evidence and open obligations

`docs/evidence/traffic-v13/v13-two-host/receiving.log` records a two-host run at a 1 s tick: all-cover and
native-delayed poles each delivered 768 roster-enrolled fixed TCP records with a valid broadcast every epoch, the
native-delayed pole made 16 exact source calls, and `planted-faults.summary` records two planted faults detected
(wrong-slot key, dropped cover). That commit (954a5d86) names MCE3 enrollment; the cohort code has since moved to MCE4
(`COHORT-TCP.md`) and the run has not been repeated on it. Unit tests: `cargo` tests in `pq_mailbox.rs` and
`cohort_tcp.rs`; the filtered selection used for the pipeline checks is `native/resource-client/scripts/check-traffic-pipeline.sh`.

Open (profile P1): the reduction from these checks plus an honest shuffle to an observation game; a worst-case time
certificate for variable native Host work (a deadline is private only with one, or with a source-owned asynchronous
continuation); forward secrecy, rollback defense and an external anti-rollback anchor are not claimed.
