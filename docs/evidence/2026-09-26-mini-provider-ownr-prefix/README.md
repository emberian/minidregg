# Qualified fn own-R injection repair image (2026-09-27 UTC)

The first [own-R native image](../2026-09-26-mini-provider-ownr/README.md)
was source-qualified, but the fresh A runtime gate found that fn delivers an
authenticated, hop-local 75-byte header prefix ahead of the exact accepted R
carrier. Its strict byte comparison refused that valid delivery. This image
changes only `Host/Main.lean` to the isolated, narrow-compiled and focused
fixture-probed repair SHA-256
`c74496b8764b4b24b526c0db82abfddcf6bdd4f25c626177359bf890db0726e2`.
The helper admits only the specified bounded fn prefix and requires the rest
of the delivered bytes to equal the accepted carrier exactly. It remains a
qualified fn-only source cut; the later composite-grain Host source is absent.

The guarded Main-only suffix build validated the previous 172-module source,
Lean artifact, package artifact, toolchain, and binary provenance. It reused
171 unchanged imported modules, compiled `Host.Main`, and linked 3,105
response objects. All 172 source hashes and four output artifacts were
reverified. The no-argument `usage_exit=1` is expected.

The Mac arm64 executable is
`/tmp/minidregg-overnight-20260926/minidregg-host-provider-ownr-prefix`,
SHA-256 `6e76d0dafd52ea0aba2c8f87a846d93ed3544eca215ebb4471b4e4f9d05ba651`.
See the [manifest](mac-manifest.txt), [source hashes](mac-source-sha256.txt),
[artifact hashes](mac-artifact-sha256.txt), [closure](mac-source-modules.txt),
and [incremental validation](mac-incremental-validation.txt). The fresh A
runtime re-test is separate; this image was not deployed to a live service.
