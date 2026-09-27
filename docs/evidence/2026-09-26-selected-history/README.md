# Selected historical step: narrow Lean check

The new `Kernel/FnSelectedHistoricalStep.lean` was checked directly in the
independent warm source snapshot
`/tmp/minidregg-selected-historical-step`, cloned from certified
`/tmp/minidregg-provider-ownr-native`. Its imported
`Kernel/NativeHostReplay.olean` was already present. No Host or full Lake
umbrella was run for this check.

The command was `LEAN_NUM_THREADS=2 lake env lean
Kernel/FnSelectedHistoricalStep.lean`, with a claimed local Lean seat. It
exited 0. The exact stdout/stderr transcript is in [narrow-lean.log](narrow-lean.log).
The only warnings concern clone-local package metadata. The five named
theorems' axiom readbacks list `propext`, `Classical.choice`, and
`Quot.sound`; no extra axiom or `#guard` is used.

The compiled source SHA-256 was
`42ad8ecda6017eace736beec4c90ab4f20c6c54ca0db26985b2e3e2162cdbf5a`.
After the check, one documentation comment was changed to remove an
unproved uniqueness word; the final source SHA-256 is
`03e672e224713fd31f30377241aa55471765413921377a862c44fbb6137e16a4`.
A `diff -u` between the checked snapshot source and final main-tree source
showed exactly that one comment-line change. The final source was not
recompiled because the executable declarations and proofs are identical.

The module states a selection relation and general admitted-trace
decomposition. It does not provide a cryptographic selective witness,
disclose fewer bytes in the current fn package, or prove confidentiality.
