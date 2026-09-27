# Bounded cold replay phase measurement

Use only a fresh byte-identical copy of the retained post-reserve Store and a
config whose storage root points to that copy. Pin the certified Host, config,
signed observation, helper executables, and their hashes. Run one direct CLI
query as the cold baseline and one persistent-service challenge/query sequence
on a second Store copy. Record separate process startup, first request, second
same-image request, exact raw view hash, and pre/post Store hash. A socket file
appearing does not prove Host startup finished; time the first successful frame.
No live Store is opened. Preserved attempt directories are read only to seed
independently owned copies; no measured process points back to those originals.

For source phase attribution, use a private source copy and one bounded Lean
seat only after the qualified native baseline. Add measurement-only elapsed
accumulators around `derive`, `advance`, `validateLoaded`, and
`imageBoundaryCanonical` in `Kernel/NativeHostReplay.lean`'s `walk`
(lines 1999–2040), with
per-phase totals and accepted-entry count written to private stderr. Retain the
exact output and Store hash checks; keep instrumentation out of the shared
source and release build. One run, a 600-second timeout, and a terminal verdict
are enough to decide which phase merits proof work. Do not infer phase share
from whole-process CPU or the earlier six cSHAKE stack samples.

A candidate optimization, contingent on that measurement, is checked successor
validation in place of repeatedly scanning every cell and selected policy in
`Kernel/NativeHostContext.lean`'s `validateLoaded` (lines 156–190). It must
prove for every validated
prior image and admissible derived intent that the successor result equals full
`validateLoaded` on `advance`, including every role, policy-source, authority,
and factory-pin check. Full genesis/final validation, exact canonical receipt
boundaries, and current-image observation authorization remain unchanged.
