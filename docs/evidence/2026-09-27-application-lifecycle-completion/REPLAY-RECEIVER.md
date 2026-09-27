# Event-18 chronological admission and exact-CAS receiver

This source checkpoint extends the frozen event-17/19 Replay overlay from
`persvati:/home/ember/build/minidregg-dispatch-inspect-overlay` with checked
lifecycle completion event 18. Its frontier source was frozen before event-20
namespace registration; event 20 is not part of this verdict. The overlay's
`FnConsumerFrontierReplay.olean` is SHA-256
`8f700d3deeb62e7662a604f48dd1aaeb2afc1884b24e05db020099020afdb2c9`.
The new sources were compiled in an independent `/tmp/minidregg-completion-src`
source and `/tmp/minidregg-completion-olean` artifact overlay with
`LEAN_NUM_THREADS=2`, in Replay→Receiver→Lookup order. All three direct Lean
checks exited zero, with no Lean error or `sorryAx` diagnostic.

| Module | Source SHA-256 | OLean SHA-256 |
| --- | --- | --- |
| `Kernel/NativeHostReplay.lean` | `74fa2da7f6fd7ae690737880394011dbb27561d2ddf12e5476839442f3206328` | `91e0ec45b4f575352e9391a74c74f60d4220de6305805fa91773be4bb57b5703` |
| `Kernel/ApplicationLifecycleCompletionReceiver.lean` | `2ecabb9eb254acc8eeef9eb2dd784bbb02548a316f03b5cb78367e18a10cc215` | `661ef0d25f7b6241a926362e9bf419da9a744e687b70a3db03209fbe30ac787b` |
| `Kernel/ApplicationLifecycleCompletionLookup.lean` | `5625b9f2885d5d24d693d357ee644ca76280b3c7142a82bce4115b1e1124a0ba` | `20d55135c133c364f70a968483cde5a541ae51b82c76f4fb736d1f6e183c3822` |
| `Host/ApplicationLifecycleClaimInspection.lean` | `c75466cad5cdc37654afb4241ab2f57fb4b70e8c4a0a243000c7177a4ff7e0e0` | `133511ad516a7a7e5065eb75aed95d328997607825953fe2f012e990434c2b5a` |

`PriorClaimV2` is inserted only after a v2 claim's source admission, complete
record match, durable advance, and validated successor. `CompletionAt` requires
the completion's independently re-admitted exact-prefix claim to match that
same prior record, index, and canonical ingress. The named
`CompletionAt.original_claim_record_at` theorem exposes the exact retained
record equality. Only this typed admission can produce Replay event 18.
`receiveVerified` submits the same intent through one CAS, requires exact
post-image byte readback before `Confirmed`, and retains the verified successor.
The lookup only returns a receipt selected from an already verified history;
it cannot submit the report or repeat a physical effect.

No Host op38/39 route, configured completion key parser, operator signature,
native Host binary, or actual physical lifecycle operation is qualified here.
The v2 claim inspector is strict presentation of the canonical committed
frame and echoes all bytes. Its JSON does not replace raw op26 callback
custody or the physical host's one-parse signed-SPK comparison.
