# STOP running-witness operator plan v2

This source cut makes STOP planning a distinct operator-private frame. INSTALL and first-create retain the byte-identical `DREGG/APPLICATION/LAUNCH-BEGIN-OPERATOR-PLAN/v1` codec. The v1 author and assembler now refuse STOP. A STOP request can be planned only against the current verified image: `prepareStopRequestVerified` selects the newest natively admitted event25 running completion for the app and returns `DREGG/APPLICATION/LAUNCH-STOP-OPERATOR-PLAN/v2`.

The v2 plan carries that event25's accepted index, full four-field receipt, prior running generation, unit, image, invocation ID, control group, and exact volume Custody. The source-derived STOP operation generation is the next generation; the physical unit is the prior running generation. `inspectStopPlan` echoes the exact canonical request/plan bytes and those source-selected fields for custodian comparison. `stopPlan_decode_encode` is a general codec round-trip theorem. The read-only JSON projection is not a launch or stop permit; fresh claim confirmation and comparison with the retained host journal are separate gates.

The two changed source files compiled serially in the independent hbox overlay `/tank/dregg-build/minidregg-55d3868-launch-v2-narrow`, based on its previously qualified STOP/Replay closure:

```sh
LEAN_NUM_THREADS=2 lake env lean -o .lake/build/lib/lean/Host/ApplicationLifecycleLaunchBeginAuthoring.olean Host/ApplicationLifecycleLaunchBeginAuthoring.lean
LEAN_NUM_THREADS=2 lake env lean -o .lake/build/lib/lean/Host/ApplicationLifecycleLaunchBeginInspection.olean Host/ApplicationLifecycleLaunchBeginInspection.lean
```

The exclusive seat `/tank/dregg-build/minidregg-55d3868-cycle/lean-seat-2` was acquired atomically and released by trap. Both commands exited 0 and the retained diagnostics `author.log` and `inspect.log` are empty. Full source SHA-256 hashes are in `SHA256SUMS`. OLean SHA-256: BeginAuthoring `b4c6a4073e721cf99261f37939dfc4807987533e554847d72a2240295a344a61`; BeginInspection `e2799a9f4e8027985b8edca5bcc411647bc2e13fa67082862ca4364b4e699038`.

This is source qualification only. Host.Main/Json op66/67 STOP routing, a fresh op26 claim inspector that reselects the same running witness, the Rust journal/volume comparison and physical fence, linked binaries, and native acceptance remain separate gates. No physical STOP or continuation was run.
