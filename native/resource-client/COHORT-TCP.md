# Guarded cohort TCP adapter

Status: research line (traffic stack 2), outside the public candidate (`docs/DEMO-PREFIX-2026-10-26.md`, R9). The
code exists with unit tests (`cohort_tcp::tests`); a two-host receiving run is recorded in
`docs/evidence/traffic-v13/` (see `PQ-MAILBOX.md`, "Evidence"). No independent-host deployment, public rekey/lifecycle
service or privacy proof exists.

`src/cohort_tcp.rs` (`mini mix-live`, `cohort_tcp::run`) connects the PQ packet/registrar/relay/mailbox path of
`PQ-MAILBOX.md` to fixed enrolled TCP links. It carries exact source frames and manufactures no Mini outcome;
enrollment slots are not Mini sender authority. The registrar remains an additional trust assumption, and the receiver
still sees ordinary native signatures and graph.

## Roster enrollment (MCE4)

The public cohort roster is the only admission authority: JSON `minidregg-cohort-roster-v3` with exactly five fields
(`parse_roster` in `cohort_tcp.rs`), each member and operator carrying a `native` key and a `linkKey`. `native` is the hybrid
Ed25519 + ML-DSA-65 signature key (`mini_sdk::signer`, `Scheme::HybridEd25519MlDsa65`) and `linkKey` is the hybrid
X25519 + ML-KEM-768 public key (`hybrid_kem::PUBLIC_LEN`). Its exact-byte SHA-256 enters every transcript, so both ends
must hold the same roster. The `LINK ENROLLMENT (MCE4)` comment above `ENROLL_MAGIC` in `cohort_tcp.rs` is the contract:

- the receiver sends a fresh challenge (`MCE4`, `ENROLL_MAGIC`);
- the sender answers with two hybrid encapsulations (to the receiver's roster-pinned static key and to a per-connection
  ephemeral key) and a hybrid signature over (domain, profile, roster digest, start epoch, the whole challenge, both
  ciphertexts); the receiver admits only if both signature halves verify;
- the link key is derived from both encapsulations and the signed transcript, and the receiver's acknowledgement proves
  it holds the roster link secret;
- garbage, a non-roster or wrong-slot key, a replayed response and a stalled peer are dropped and the listener
  re-accepts until the public start deadline; a handshake is bounded at 3 s (`HANDSHAKE_MS`).

An `MCE2` or `MCE3` challenge, a v1 or v2 roster, a bare 32-byte Ed25519 roster key and a pure ML-KEM link key all
refuse by name (`RosterEntry` and `parse_roster`, and `enroll_sender`, in `cohort_tcp.rs`). The cohort native key is a separate hybrid key from
`mini mix --action native-key`, not the participant's Ed25519 Mini identity; the Host admits no hybrid identity yet
(`docs/SDK-PQ.md`). The profile pin carries codec `MCE4` and state from an earlier codec refuses to resume.

## Actions

`mini mix-live --action send|receive|cover|registrar|relay|mailbox|scan` (the action match in `run`, `cohort_tcp.rs`). Common public
arguments: `--generation`, `--slot`, `--phase`, `--width`, `--payload-bytes`, `--origin-ms`, `--tick-ms`,
`--first-epoch`, `--epochs`, `--state`, `--records`, `--processing-slots`, `--roster`. Bounds are in `Profile::check`
(`cohort_tcp.rs`): width 2..=64, payload 1024..=262144, tick 100..=60000 ms, 1..=4096 epochs, processing slots
1..=32 (default 2, `--processing-slots` in `run`). Phases 0..5 mean client contribution, registrar batch, relay 0/1/2 output, and the whole
broadcast. Senders take `--native-key`, receivers `--link-secret` and `--link-public` (`mix --action key`). Network-fed
workers consume an input directory only if its marker names the exact upstream link (phase, slot) and the roster's
sender key, so an operator's directory list cannot relabel a slot.

Properties the code keeps, with the place to read them:

- Outer wires are sealed under the connection key and never persisted; a resumed link re-enrolls (`send` in `cohort_tcp.rs`).
- The clocked network loop reads in-memory prepared wires or a fallback and writes the socket; no fsync, native
  execution or packet sealing runs on it. Lifetime inventory is bounded at 64 MiB (`send` and `receive`). A slot past its
  scheduling allowance is a declared fault with no catch-up burst (`wait`), and a future-only resume cannot retransmit a
  released epoch (`prepare_live_wire`; `--resume-epoch` in `run`).
- Durable record adoption publishes an availability token only after the record is written; a crash-lost token stays
  fail-closed until exact re-adoption.
- The mailbox offers cores to the source-owned `AsyncDispatch` (`src/async_dispatch.rs`, journal in
  `src/scheduled_transport.rs`): the gateway durably reserves class, access and exact request, fixed workers perform the
  native exchange, and a physical continuation is outside the native frame and is not a Mini Pending or receipt.
  `scan` releases only capability-authenticated physical outcomes and keeps the spent/opened fences.
- The mailbox stays resident for `--custody-hold-ms` (default 600000) after the configured lifetime
  (the `custody-hold-ms` argument and the residence wait in `worker`, `cohort_tcp.rs`).

## Qualification

The receiving orchestration is `native/resource-client/cohort-native-tcp.py` (it passes `--roster`); the focused test
selection is `native/resource-client/scripts/check-traffic-pipeline.sh` and
`native/resource-client/scripts/check-cohort-async.sh`. This is
a local process and TCP experiment, not an independent-host deployment, and a lateness or readiness result there is not
a worst-case time certificate. The formal reduction to an observation game and the source-private evaluator remain open
(`docs/TRAFFIC-PRIVACY-PROFILE-P1.md`).
