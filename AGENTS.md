# Working on Mini

Read [HANDOFF.md](HANDOFF.md) first for the current agent-grain construction
record and suite handoff. The suite's graph owns task status; dated build/runtime
evidence is scoped to its exact source. Read relevant source before asserting
that older architecture or status text is current.

- Mini is the New World's construction home. Lean owns semantics and admission;
  Rust provides the physical client/custody boundary. Do not introduce a Python
  platform or reimplement semantic decisions in a transport wrapper.
- Existing grants face current rules; policy revision is distinct from revocation.
  Deliberate management lockout is permitted; do not add an owner recovery bypass.
- Preserve unrelated WIP. Root owns Git in shared trees, on current `main`;
  subagents edit only their assigned files. No stash/reset, branch/worktree changes,
  or blanket staging. Inspect full-file diffs before committing named paths.
- Use `scripts/build-native-host.sh` and `scripts/build-native-acceptance-runner.sh`
  for the recorded native route. Read their help first. Build in independent
  snapshots with independent writable package state. At most two local Lean
  compiler seats; `LEAN_NUM_THREADS` alone does not bound Lake process fanout.
- Preserve admitted-history, current-authority, exact-preimage and uncertain-reply
  semantics when optimizing. General proofs and actual receiving-path evidence
  are separate obligations; a source check does not establish deployment.
- Publish scoped checkpoints regularly. Ember allows per-commit unsigned fallback
  when unavailable for 1Password signing; do not change global signing settings.
