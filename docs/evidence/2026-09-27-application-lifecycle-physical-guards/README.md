# Lifecycle observation roots and durable read guards

BEGIN keeps the signed package observation bound to the package's logical payload root, then derives its extra durable read guard from the selected live cell's physical root. ClaimCurrent does the same for signed app and package observations. ClaimCore emits the package physical guard; the app's old physical root is already checked by the DRC target write, so an overlapping app read guard is not added.

Source SHA-256:

- `Kernel/ApplicationLifecycleBeginReceiver.lean`: `6c6c43b337dfac4de8417eef2569d83d4e1d2d0bbfe8d05f51a7cedb5763c4a3`
- `Kernel/ApplicationLifecycleClaimCurrent.lean`: `71b12ed7014819b1370b07947018b78a70f2954aa0987a17d41d443fb0f0c959`
- `Kernel/ApplicationLifecycleClaimCore.lean`: `fd9290670794ffd7fcd056ac9bac11cd42a10b062a4c5dd8d51da6e226d673d3`
- Shared `Kernel/PhysicalResourceReadGuard.lean`: `2c447ebbd5846308eab23486c59a235352343343477ce4f227c9589945334f8d`

An independent Persvati snapshot serially emitted source-matched OLeans for ApplicationGrain, BEGIN, ClaimHistory, ClaimCurrent, ClaimCore, and Replay under a 2-CPU/16-GiB scope; the final command exited 0 with no Lean errors. [BEGIN log](begin.log) SHA-256 `f80eed4cfad1d223c81a6ebbcab995be1ca97e80bb37cc4d32b21b89c8d64cfd` and [dependent closure log](closure.log) SHA-256 `e30ddbde5cc261fcad64e1fea3a68981abb188286fc5eaa34fb71a613bbc4224`. This is a source check, not a native lifecycle launch or completion gate.
