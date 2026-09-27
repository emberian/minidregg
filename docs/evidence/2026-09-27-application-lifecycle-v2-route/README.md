# Descriptor-bound lifecycle Host route — source check

This cut routes fresh BEGIN through `ApplicationLifecycleBeginV2Receiver.receiveVerified` (op22) and fresh claim through `ApplicationLifecycleClaimV2Receiver.receiveVerified` (op26). The claim's committed reservation bytes are written and flushed only inside `Reservation.withFreshTip`; this is a point-in-time physical-tip check, not a lease on a later process launch. Ops23/27 and the two lookup CLI commands return only verifier-walk-selected original receipts, recognizing retained v1 or v2 records. Fresh v1 submission is refused.

The new `Kernel/ApplicationLifecycleV2Lookup.lean` and changed `Host/Main.lean` compiled serially with Lean exit 0 and empty diagnostics in an independent Persvati overlay. The overlay imported source-matched v2 replay/receiver OLeans from the frozen `selected-prefix-codec` snapshot; existing dispatch/share/Host OLeans were copied as ordinary files from the independent `dispatch-final-20260927-spkcompat` snapshot. This is a bounded source/OLean gate, not a native link or physical BEGIN/claim acceptance.

| Source or artifact | SHA-256 |
| --- | --- |
| `Kernel/ApplicationLifecycleV2Lookup.lean` | `155557838696ce6b9a5c788ad9cf32bd0fcd2b234a062835a1011319523e1ce0` |
| `Host/Main.lean` | `1b74aecd6595db24499a538bb9907204ddb3c0ab3cb3095e679f4238c3065afe` |
| lookup OLean | `d5e30dc1329fe50043faf24c72ccdbf9c07dd7f50f25af7ca2bad9b4114697b2` |
| Main OLean | `0581ff623611f1776847343b1d58383204a5ff82c3141584794303f6a6d31a0c` |
| imported `Kernel/NativeHostReplay.lean` | `07820191f138e1040bd400adb03bf075352457f25d1c2dcfbd6c1d9a673e041a` |
| imported Replay OLean | `a67d55fa5c2a2541d838113ed19c487fc3b068ba5f7e9a6b6fe4528410f01ef7` |

The exact commands were `lean Kernel/ApplicationLifecycleV2Lookup.lean -o ... -i ... -c ...` and then `lean Host/Main.lean -o ... -i ... -c ...` with `LEAN_NUM_THREADS=2` and the private overlay first in `LEAN_PATH`. Both logs were zero bytes (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). No native executable or fixture is certified by this record.
