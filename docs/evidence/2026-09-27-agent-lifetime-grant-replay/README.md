# Event27 original-prefix admission checkpoint

`Kernel/NativeHostReplay.lean` SHA-256 `331edcf9f45912f61f8733cb3b86e9bdb7131c52928a2af96c51d4368b031f88` adds event27 to the native semantic replay walk. This is source-only: no Host.Main route or event26 dispatch exists here, and no native Store fixture has run.

The verifier's prior ticket context now retains the receipt minted after the original record was matched, advanced, and post-image validated. A lifetime-grant candidate requires a previously admitted **event22** issue at the exact named index, equality with its full receipt, the complete record still at that index, strict original ticket app/session/subject/task-origin/ceiling equality, and native admission of the new birth and current signed app delegation on the same opened image. The resulting `NativeAdmission` branch takes `LifetimeGrantIssueAt`; the lower intent template alone has no submit route. Full replay and exact-readback continuation both retain the walk-derived prior receipt. The existing receipt constructors keep their exact transaction ID, event ID, accepted-count and image-boundary values; this cut only passes each constructed receipt into the prior-issue context. The walk image-boundary calculation itself is unchanged.

Narrow check ran in isolated hbox overlay `/tank/dregg-build/mini-lifetime-grant-review-20260927` with the exact 55d3868 source and copied source-qualified prefix-292 artifacts (`manifest.json` SHA-256 `0c0b8fd0aedf4f97650d3ad4d369629e955943fd472c0ec089eb4de0f017d1cd`) plus the previously qualified additive grant modules:

```sh
LEAN_NUM_THREADS=2 lake env lean Kernel/NativeHostReplay.lean > replay.log 2>&1
```

Exit 0; `replay.log` SHA-256 `3466e88f21218fe7c070c50a9908a0d67b1b5c726a8280006163c771fdbcd1e3` contains only the pre-existing six standard `#print axioms` reports (`propext`, `Classical.choice`, `Quot.sound`). The certified prefix and active builder were not changed.
