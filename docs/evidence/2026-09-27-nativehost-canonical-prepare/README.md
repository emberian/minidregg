# Canonical-byte Host signing-plan source check

`Kernel/NativeHost.prepareLoaded` now computes the current image boundary from `opened.durable.bytes`, which is already the validated canonical durable encoding. `NativeHostContext.imageBoundaryCanonical_loaded` proves equality with the previous `imageBoundary config opened.durable.image` computation. This changes no authority, current-state, signature, or replay check.

The changed NativeHost source SHA-256 is `d96387c79eaa9935278abb8c39a50e789486a861b2e79799b71f5e8b70de68dc`. In the isolated source-qualified STOP overlay `/tank/dregg-build/minidregg-55d3868-launch-v2-narrow` on hbox, `LEAN_NUM_THREADS=2 lake env lean -o .lake/build/lib/lean/Kernel/NativeHost.olean Kernel/NativeHost.lean` exited 0 (existing axiom-report lines only), followed by the unchanged `Kernel/NativeHostSession.lean` direct check, exit 0 with empty log. New NativeHost OLean SHA-256 is `4ccadcb4d54f40c7290c7132e209e319008dd74acb367b75d1cb919a5719de1d`; Session OLean SHA-256 is `fae5833e77c831595a10b849802118d692e6aa85d204b8494a499690bff04ca1`. The exclusive Lean seat was released.

This is source equivalence and narrow compilation, not a native timing result. No latency improvement is claimed until source-matched native before/after measurement.
