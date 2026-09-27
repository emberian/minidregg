# Launch-bound lifecycle replay checkpoint (2026-09-27)

`Kernel/NativeHostReplay.lean` SHA-256 `2a1bdafde58aef3aa5c8cbc8c9902abeea23309a6f5b8f62d99db2b628426ea2` was checked against the committed v3 lower modules (commit `37db8f7`), corrected participant grant sources, and the immutable 55d3868 prefix-292 OLean set (manifest SHA-256 `0c0b8fd0aedf4f97650d3ad4d369629e955943fd472c0ec089eb4de0f017d1cd`). Independent writable overlay: `/tank/dregg-build/minidregg-55d3868-launch-v2-narrow` on hbox. One bounded compiler at a time under atomically claimed seat2, `LEAN_NUM_THREADS=2`.

Direct commands from the overlay root:

```
lake env lean -o .lake/build/lib/lean/Kernel/NativeHostReplay.olean Kernel/NativeHostReplay.lean
lake env lean -o .lake/build/lib/lean/Kernel/NativeHost.olean Kernel/NativeHost.lean
lake env lean -o .lake/build/lib/lean/Kernel/NativeHostSession.olean Kernel/NativeHostSession.lean
```

All three exited 0. Replay OLean SHA-256 `9a61bf9efa6ef4834abf7a8195730318c803980d9a9e866a75f38a294b142cf9`. Replay log `/tmp/mini-v3-replay-typed.log` SHA-256 `3466e88f21218fe7c070c50a9908a0d67b1b5c726a8280006163c771fdbcd1e3` contains only the six existing axiom-report lines (propext, Classical.choice, Quot.sound), no errors. Dependent logs are `/tmp/mini-v3-NativeHost-typed.log` SHA-256 `f8cae924f19b8c131664bfbe870d6ca4eb6e01825e204e562130326fa4357d1c` (the same existing axiom reports) and `/tmp/mini-v3-NativeHostSession-typed.log` SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (empty); both exited 0.

The replay walk now separately retains source-admitted event23 BEGIN, event24 claim, and event25 completion after full record comparison, durable advance, and successor validation. Continue admission requires an exact event25 completed-create receipt and custody, original-prefix native re-admission, full record match, and a matching same-walk certificate. Private `BeginAtV3` retains the dependent `BeginV3History.continue` witness through `NativeAdmission`, `Derived`, and `PriorBeginV3`; it cannot be reduced to bare lower admission after checking. The `Verified.selectCreated` and fresh admission APIs expose this check to source authoring and receivers. Existing v1/v2 history grammar remains separate.

This is a source/OLean checkpoint, not a linked native Host or physical launch acceptance. Upper v3 receivers, lookup routes, Main op66–71 integration, and resident physical comparison are still required before enabling START.
