# Lower fn progress history and frontier core

This source cut separates exact v1 scope/codec/command recognition from the
live Host operation layer so native replay can import it without a dependency
cycle. Existing public progress names remain available. Named compatibility
theorems prove unchanged name validation, full signed-command comparison and
the legacy transaction marker. The pure new frontier transition checks scan
bounds and the predecessor receipt shared by empty and selected progress.
It is not an admission certificate or a transport-completeness proof.

Frozen source SHA-256 values:

```
5147fac1516ff6b40f9f3d749cf12821e76746a680380b451103def4be704ee8  Kernel/FnConsumerScope.lean
b5854ce65e055e84ddf224f786477356be831cda8fffa54ae22ca8694043877d  Kernel/FnConsumerProgressHistory.lean
cc9860b9a5beb8d1cad4af62bb7f0ccbf24d823426a1b9b45e3e54d6cac51d8f  Kernel/FnConsumerProgress.lean
fee18bafa1d528c7a7626955c99daa4b4ba796f4383eae99efce1a6d425ee06e  Kernel/FnConsumerFrontierCore.lean
```

The private narrow closure reported `Build completed successfully (3110
jobs)`; a subsequent check including the compatibility theorems reported
`Build completed successfully (3104 jobs)`. Root inspected the source diff,
hashes and terminal verdicts in
`/tmp/minidregg-selective-receiver-20260927/FnConsumerScopeHistory-build.log`
and `FnConsumerProgress-compat-build.log`. The first closure included staged
event17/event19 modules; this commit preserves only the lower reusable split
and pure core. Those job totals include dependencies and are not test counts.

Replay-minted frontier authority, CAS receivers, Host routing and the native
empty/selected/ACK journey are still under construction. No fn POST or ACK
was performed to validate this source split.
