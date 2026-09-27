# GitWeb fd 3 session-cache capacity probe — 2026-09-27

This is a private physical component test on persvati, still using **synthetic
session projections**, not Mini dispatch admission. It extends the earlier
[copied-volume GitWeb test](GITWEB-SESSION-PROBE-2026-09-27.md). Resource 991003
was not launched or written. The quiescent copied resource 991013 retained
the exact bare-repo branch tip
`27c7e7dbe3c66cc5d8381748d0b0e5fbae05bafc` before and after the run.

The signed SPK SHA-256 was
`2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa`.
The tested committed `rpc_adapter.rs` SHA-256 was
`19aa24b2db599b1325c3466e16163b2c98c3bd21ecd6b024435540f0c4d48a2a`.
The capacity-option fixture source `gitweb-session-smoke.rs` SHA-256 was
`eed950a9bbbc9517ac7e0531e98a805910fac914860da47b450d3197486ae754`;
the two-job Linux release build and strict binary Clippy passed. Its exact
root-owned ELF at
`/opt/minidregg-gitweb-session-20260927/bin/gitweb-session-smoke`
was SHA-256 `e22176a7596d3b752257096da3d3a4becc072e63a118594135fafdd47a4a8125`.

The single transient unit `mini-spk-gitweb-session-991013-capacity.service`
used locked UID 995, `NoNewPrivileges=yes`, `PrivateNetwork=yes`,
`KillMode=control-group`, `MemoryMax=1G`, `TasksMax=64`, `CPUQuota=100%`, and
`RuntimeMaxSec=300`. It ran only the signed `continueCommand` with the
copied 512 MiB ext4 `/var`. No public listener or Mini Store was involved.
The source command added the `--capacity` flag to the prior fixed image,
volume, bwrap, volume cap and expected commit argv.

After the initial Web/API checks, the fixture created 33 distinct read-only
WebSessions with different synthetic session resource, subject and identity
values. All returned GitWeb summary HTML. The app-side creation count then
reached 38 (five earlier sessions plus 33) while only 32 capabilities remained
cached. Reopening the first of the 33 created session 39, with the cache still
at 32: the least-recently-used capability had been evicted and recreated.
The same subject's write-capable Git receive-pack advertisement returned 200
before attenuation and 403 afterward. The guest upload-pack advertisement
contained the exact retained commit. The HTML result was accepted because it
identified that commit **or the known fixture title**; the exact-commit proof
comes from upload-pack and the independent repository-tip read, not the HTML
check alone. The deliberately expired final request was read-only and its
driver refused another dispatch; this does not qualify uncertain delivered
writes.

The unit returned `Result=success`, exit 0 in 3.309 seconds, with 3.262 seconds
of CPU and 175.1 MiB peak memory. Afterward it was inactive, MainPID 0,
ControlGroup empty, with no UID 995 process or host listener on the tested app
ports. The private 991013 volume remains mounted and verified. The retained
keyless [unit log](../../docs/evidence/2026-09-27-spk-gitweb-session/capacity-unit.log)
has SHA-256 `5381efcb83be4e08fb22c1589b377ec37fcc30121ea9115351189187469b7e08`.

This closes the physical 33-session cache behavior for this one SPK and
runtime image. It does not turn synthetic projections into authority, prove
general app session semantics, or enable the product endpoint. Each future
browser/API request still needs its own current Mini-checked dispatch permit.
