# Proofs lane state

Present-state record of the proofs lane, rewritten whole when its shape changes.

## Where things are

- Mac worktrees under `/Users/ember/dev/minidregg-lanes/`: `proofs` (branch `lane/proofs`, the statement
  fixes), `proofs-effects` (`lane/proofs-effects`), `proofs-fixtures` (`lane/proofs-fixtures`).
- hbox, all under `/home/hbox/lanes/proofs/` (NVMe):
  - `src`: `lane/proofs` tree. Lean builds with `build.sh TARGETS` (swarm-build 28 G, a seated sysroot
    `seated/` caps it at 3 compilers via `PROOFS_SEATS`). Candidate builds with `build-cand.sh SHA`
    (integ-build2 adapted: rust-check, host, consent, rust, pack, then umbrellas; `SEATS=3 MEM=28G`;
    PID file `build.pid`; stage lines in `COMMANDS.log`; candidates in `candidates/<sha>`).
  - `msrc`: a main/staging tree (719d7b7a) for fixture work without the statement fixes; `build-m.sh`.
  - `worlds/`: scratch worlds (acc2 objective acceptance, doc1 document write, both from candidate
    c7aa7e8c4), `dbg/` (journal replay probes).
- Detached jobs: `setsid nohup ... < /dev/null & echo $! > X.pid` (a plain nohup under ssh died with
  the session).

## Landed or sent

- 75cd46376 EngineProofs + BirthPlanPoles (landed).
- 0ca243107 PrepareProofs + HostTeethProofs against the admission gate (landed).
- f5d351a96 both Native fixtures (landed as 06831831c): journal-order images (`Image.ofAccepted`;
  `acceptedRev` is newest first), `Config.ofInputs`, byte lanes as relations to the run with
  off-by-one teeth, transcripts recorded by `scripts/native-accepted-fixture/verify-shim.c`.
- `lane/proofs` bf716681b (sent, one sha over main ceae90623): the statement fixes (witnessed refused
  at install and admission, journal apex, writeOnceNonzero, [LC-fs-adaptive] PARTIAL), their witnesses
  (`checkReady_denyIfCredential`, `plan_refuses_witnessed_inhabited`), the retained event stated as
  exactly the signed ingress, and the accepted run re-recorded from candidate 3b88b1954 (the grammar
  change rotates the Objective front-end identity).

## Open for a decision

- Genesis does not refuse a factory predicate that mentions `witnessed`; such a world refuses every
  birth (fail-closed) instead of refusing at genesis.
- objective-native-acceptance.py `all` fails at `publish-variant` (it runs `lean --run` without the
  kernel dynlib); after the steps the fixture uses.
- Any later change to the Objective front-end sources rotates its identity and needs the accepted
  fixture re-recorded from a candidate built with it (generate.sh, fresh world).
