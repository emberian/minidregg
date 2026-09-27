# Lifecycle observation roots and durable read guards

BEGIN keeps the signed package observation bound to the package's logical payload root, then derives its extra durable read guard from the selected live cell's physical root. ClaimCurrent does the same for signed app and package observations. ClaimCore emits the package physical guard; the app's old physical root is already checked by the DRC target write, so an overlapping app read guard is not added.

Source SHA-256:

- `Kernel/ApplicationLifecycleBeginReceiver.lean`: `6c6c43b337dfac4de8417eef2569d83d4e1d2d0bbfe8d05f51a7cedb5763c4a3`
- `Kernel/ApplicationLifecycleClaimCurrent.lean`: `71b12ed7014819b1370b07947018b78a70f2954aa0987a17d41d443fb0f0c959`
- `Kernel/ApplicationLifecycleClaimCore.lean`: `fd9290670794ffd7fcd056ac9bac11cd42a10b062a4c5dd8d51da6e226d673d3`
- Shared `Kernel/PhysicalResourceReadGuard.lean`: `2c447ebbd5846308eab23486c59a235352343343477ce4f227c9589945334f8d`

An independent Persvati snapshot serially emitted source-matched OLeans for ApplicationGrain, BEGIN, ClaimHistory, ClaimCurrent, ClaimCore, and Replay under a 2-CPU/16-GiB scope; the final command exited 0 with no Lean errors. [BEGIN log](begin.log) SHA-256 `f80eed4cfad1d223c81a6ebbcab995be1ca97e80bb37cc4d32b21b89c8d64cfd` and [dependent closure log](closure.log) SHA-256 `e30ddbde5cc261fcad64e1fea3a68981abb188286fc5eaa34fb71a613bbc4224`. This is a source check, not a native lifecycle launch or completion gate.

Provenance correction: the retained snapshot's old Replay OLean `5a9c92d4a4883581a33772370945812758ef8989e8045e1a07d94e38cf0e0645` cannot be source-matched to final Replay source `bcbf2b45c0bfbc29d6c0a98f9b1bb853c269f5981b81a7ad154297f534588230`; the snapshot held Replay source `024da48057190a71070455646fcc48ae18f74907d46e89e27077ec8f574d897f` when audited. Preserve the original logs above as the dated record, but do not use that cached OLean as final Replay evidence. The corrected dispatch dependencies are listed in the [dispatch history evidence](../2026-09-27-application-dispatch-history/README.md). An exact-source direct Replay recompile produced OLean SHA-256 `10bdd5692b6754e18bb85cc974811b1a5b22f4c72ed3e1abd66c870e23ba09f2`; its [superseding log](../2026-09-27-application-dispatch-history/replay-recheck-bcbf.log) SHA-256 `39c33822a78b44e76f71deb158f654a312fb09f7908401571a6efed47f03c4a4` exited 0 with no Lean errors.
