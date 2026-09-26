# Canonical loaded-byte observation boundary

Commit `83ba61e` changed `Kernel/NativeObservationController.lean` (SHA-256
`5ec4519df86610592ea4d473a428152fe4c69b62c7d2468bbe5a1594dcd791a9`)
to hash the canonical bytes retained in `DurableReceiverIO.Loaded` instead of
re-encoding the loaded journal at each observation boundary. The theorem
`loadedImageBoundary_exact` derives equality with the original
`NativeHostCodec.imageBoundary` from `Loaded.canonical`; the compiled exactness
lemmas carry this through effect identity, signature marker, binding bytes,
request, and signed header. The challenge and grant check retain the same
current loaded image and still compute one boundary each. This change removes
redundant *encoding*, not the remaining 1+N boundary hashes in authorization.

The narrow check used the independent
`/tmp/minidregg-overnight-20260926-fn-review` snapshot with the coherent
current `Compiler/DurableReceiverIO.lean` and OLean copied from the selected
bbf snapshot:

```sh
LEAN_NUM_THREADS=2 lake env lean Kernel/NativeObservationController.lean \
  -o .lake/build/lib/lean/Kernel/NativeObservationController.olean \
  -i .lake/build/lib/lean/Kernel/NativeObservationController.ilean \
  -c .lake/build/ir/Kernel/NativeObservationController.c --json
```

Lean exited 0. The [bounded compiler log](observation-loaded-boundary.log)
has SHA-256 `8e62751d8df22882452160f0b469c0eb13ab224942de668dd7cfa69ad23e1e8a`;
it contains only unused-variable/section linter warnings. A proposed
shared-boundary dependent cast did not compile and was removed before this
commit. No host latency improvement is claimed until a source-matched native
comparison is run.
