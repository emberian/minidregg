# Reusable grain-origin source gate (2026-09-26)

`Host/GrainOriginSource.lean` SHA-256
`b8a8a93d530bbb497f776d921b1aad4885d484ef6eec05faa89cb148a7cbcb72`
typechecks in the independent APFS clone
`/tmp/minidregg-overnight-20260926-grain-origin` with
`LEAN_NUM_THREADS=2 lake env lean Host/GrainOriginSource.lean`.

The pure `render` API takes bounded Mini evidence package bytes, an independently
verified native receipt, operator article context, and selected grain/parent/
publication targets. It rechecks receipt equality and the signed command shape,
then returns strict source bytes with a parser roundtrip proof. Native verification
of the package under the pinned origin config remains the caller's IO premise.

The focused probe [`probe-grain-origin-source.lean`](../../../scripts/probe-grain-origin-source.lean)
used the durable accepted package
[`7003-package.bin`](../2026-09-26-hermes-grain-origin/7003-package.bin)
(139,470 bytes, SHA-256 `9be53614a920fae1a2522d94f93f5b6804b137a74fffb91b4953fd2cd75a81ab`),
grain task 7102, parent task 7101, publication target 7003, `fn.test`, and
`Sat, 26 Sep 2026 09:45:00 +0000`. Its output matched the durable
[`R.source`](../2026-09-26-hermes-grain-origin/R.source) byte for byte
(191,283 bytes, SHA-256 `8b2da29b05723e1f4f48f1889f84a9e8037cbfef1a23ccc0c7ece04ae0f0a488`).
It also rejected a different receipt, a CRLF-injected subject, and an absent
named publication target. Exact output: [`exact-r.log`](exact-r.log).

The probe obtains its receipt from the package solely to test deterministic
rendering. Production invocation must pass the receipt returned by native
`FnEvidence.verify` under an independently selected origin pin.
