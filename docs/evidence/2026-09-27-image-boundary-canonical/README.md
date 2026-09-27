# Canonical-byte image boundary source proof

`Kernel/NativeHostContext.lean` adds `imageBoundaryCanonical config bytes`,
which uses the existing image-boundary domain, profile semantics and full
cSHAKE256 hash. For every image,
`imageBoundaryCanonical config (DurableReceiverCodec.encode image)` equals the
existing `imageBoundary config image`. For a checked `Durable`, the second
theorem substitutes its `Loaded.canonical` equality to show the already
retained `durable.bytes` give that same boundary. Neither theorem weakens
native admission, image validation, historical replay, or post-CAS readback.

The source SHA-256 is
`3fc07451fa5ce7eb3cb0733e45a7317bccb931b22ff175f7b5c294f7c1c747b0`.
An isolated APFS clone of a warm Mini source/OLean snapshot compiled the one
module with `LEAN_NUM_THREADS=2 lake env lean -o
.lake/build/lib/lean/Kernel/NativeHostContext.olean
Kernel/NativeHostContext.lean`. Log:
`/tmp/mini-image-boundary-context-final.log` SHA-256
`12ed7237da36b5ce4ea7c77e834a9e6b8de5944d429393fac2a01a70893278bc`.
Both named theorems compiled; their reported axiom set is `propext`,
`Classical.choice`, `Quot.sound`. The local Lean seat was released.

This is a source-only checkpoint. `NativeHostReplay.walk` still calls the old
image-taking function and no native latency result is claimed. The intended
consumer substitution is only the receipt construction after a checked
advance: `imageBoundaryCanonical config next.bytes` for
`imageBoundary config next.image`, justified by
`imageBoundaryCanonical_loaded config next`. It still hashes the complete
canonical image; the optimization avoids one repeated encoding. A later
source-matched copied-Store gate must compare complete signed views, original
four-field receipts and physical SQLite bytes before claiming a speedup.
