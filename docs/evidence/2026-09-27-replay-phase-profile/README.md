# Private f461 cold replay phase profile

This is measurement-only instrumentation of the certified `f461f39` source
cut, not a new production Host or an optimization. The exact baseline source
archive is SHA-256 `86dd1cecb72c361584c66f22fc506b6011d9b5b624da75c9468d56ed368d35e6`.
Only a plain private Persvati copy of `Kernel/NativeHostReplay.lean` changed;
the complete [instrumentation diff](instrumentation.diff) is SHA-256
`5086795b268a0f202b8c5fedb0aa460e26c2eeefcec6871e5e8cd98d0d95bc8e`.
The final instrumented source is SHA-256
`d3dfc3bf26ed667548694c42578979bd4dae7abee05ac61f381b0bc8346da53d`.
No shared Kernel source or live Store changed.
The [portable file checksum manifest](portable-sha256.txt) covers every
retained probe, raw timing projection, and instrumentation diff in this
directory; private Store bytes, signatures, and full diagnostic stderr are
excluded.

The private incremental suffix build used certified f461 artifacts and one
serialized Lean compiler with two threads and two native C jobs. It rebuilt
85 affected modules, checked all 343 source modules, reused 2,933 qualified
package objects, linked 3,276 response objects, and passed its usage probe.
Its manifest SHA-256 is
`e4f52d548ed5bc0b1f0f136f8c8ac5cd29812be4f06a021936b19bdb1e4bedbb`;
the clearly labeled diagnostic ELF SHA-256 is
`4b17acefc7cd96a0e17876cc93f46b7428180120ae4c50ef3381aedf222bef14`.
Build files remain private under
`/home/ember/build/minidregg-f461-replay-profile-v2-20260927/output-r2b`.
The inherited `.git` metadata in that cache is not source provenance.

One query ran under a 600-second timeout against an independent byte-identical
copy of the retained post-reserve SQLite Store. It exited 0, returned the
certified 101-byte raw view SHA-256
`dac7842a355077c58af33704f2fcf22bc70a20fb9a4de5ba3c3bf1c2a1f1708d`,
and left the physical Store at its exact before/after SHA-256
`4c3685f51196665e95605462e5779b46bc2fff271e2b82609e2021e6f239dbb5`.
Wall time was 103.13 s and user CPU 94.55 s on this one ambient-load run.
Private raw stderr SHA-256 is
`21901c7ec3859b422f483686054c2401098fe465582a47d2d447439dd3ce8800`;
the time log SHA-256 is
`f8fcc8508252ca5709fdd5f33713fb85addc99ceaf2e02e2ff025da6af3290aa`.
They remain under `/tank/dregg-build/minidregg-f461-replay-profile-v2-20260927`.
Portable, redacted copies are [the 17 raw phase lines](phase-lines.txt)
(SHA-256 `61378b798b6b40910f59083f92a8b76ece0176dbef9e7d9aa060b71913916613`)
and [the time summary](time-summary.txt)
(SHA-256 `609581da9e9feaa31e37670e9f2a8853f42d77aab90ca84753ffe62ccffed016`).
Only the diagnostic `boundary_value` was removed from the phase lines; indices
and every interval remain intact. The bounded [build summary](build-summary.txt)
(SHA-256 `5dedd6eabd1a25dc8b3b256921e3190e1ccac0079c8fcdbdc08a45c9b265bebe`)
records the manifest counts and diagnostic binary checksum without copying the
private Store, view, or signatures.

| `NativeHostReplay.walk` interval, 17 accepted records | Measured wall total |
| --- | ---: |
| `derive` call/return | 70.91 s |
| `recordMatches` | 2.13 s |
| `advance` call/return | 18.38 s |
| `validateLoaded` call/return | 1.93 s |
| forced canonical `imageBoundary` hash | 2.36 s |

These are sequential monotonic intervals, not exclusive CPU attribution. Pure
fields can be forced by a later consumer; read `derive + recordMatches` and
`advance + validateLoaded + boundary` as the safer groups. Generated C confirms
the boundary hash runs before the stop clock and occurs only once: the compiler
reuses that value for the original receipt. The first diagnostic binary put
its stop clock before that pure hash was forced and produced a false
nanosecond-scale boundary reading; its wall time is not a comparable benchmark.
One cold run under changing machine load cannot establish a speedup.

A read-only strict image-codec probe of the copied canonical blob (SHA-256
`94be9a9d858e1ebffab710b1e8d4d0d8d97dfd555cc71ac0507910a3b13aaa49`)
found event versions `[2,1,1,1,1,1,3,3,3,3,3,2,3,3,3,3,3]`.
The exact [probe source](event-version-probe.lean)
(SHA-256 `28a2187ccc612293ecd8cd70842499a696d66ac223a807c69b5e7dcd82d50ca2`)
and [probe output](event-versions.txt)
(SHA-256 `9272b73c2c8763ee724d27979f7e4f27d18e9334985cfd6f0e76268c9105ab26`)
are retained here. The probe source points to the private copied canonical
image by path; the image itself is not published.
`derive` at index 0 (ordinary resource birth, event 2) took 25.33 s; indexes
13 and 15 (event version 3) took 22.55 s and 9.54 s. Those three derive
intervals account for 57.42 s of 70.91 s. Event version alone does not
identify the admission branch. A second strict [kind probe](event-kind-probe.lean)
and its [17-line result](event-kinds.txt) show that indexes 10, 13, and 15
are **grain births**, while generic signed invocations are indexes 6–9, 12,
14, and 16. The event 2 path re-admits through
`ResourceBirthPolicyController.Concrete.admitDecodedNative`.

I therefore ran one more measurement-only binary, adding the exact
[event 3 subphase diff](event3-instrumentation.diff) to a separate private
copy of the phase-instrumented source. The private source SHA-256 was
`ef8cd465943d1783941df9686d8e68805fa09b45db5b30204eaa564699a5e633`;
its 343/343 source-qualified incremental build manifest SHA-256 was
`383c5c720e4e855be854dddabfd7e05bd62fda398ed74ba1d0c260ca5f02e79f`
and diagnostic ELF SHA-256 was
`dfc8f1448bd91c28cb6426b02e17fa68259079328ecfab073c08189aa12b2239`.
The separate copied-Store query exited 0, returned the same certified raw
view SHA-256 `dac7842a355077c58af33704f2fcf22bc70a20fb9a4de5ba3c3bf1c2a1f1708d`,
and left its SQLite Store at the same before/after SHA-256
`4c3685f51196665e95605462e5779b46bc2fff271e2b82609e2021e6f239dbb5`.
Its [redacted subphase lines](event3-subphases.txt) and
[time summary](event3-time-summary.txt) are retained without private
boundary values. Generated C calls each timed directory and deployment load
before a separate call to the original preparation function; the original
admission result is used unchanged.

Across seven **generic** event 3 invocations, diagnostic directory reloads
totaled 0.095 s, authority reloads 0.114 s, original preparation 0.500 s,
and native admission 2.084 s. This extra-probe run had 72.26 s wall time;
its grain-birth indexes 10, 13, and 15 consumed 24.54 s of 48.60 s total
`derive`. The probes add work and ambient load differed, so this is not a
speed comparison. It does rule out duplicate directory/authority loads as
the dominant cost on this image. The next measured source boundary is
`GrainResourceBirthReceiver.receiveLoaded` and the replay equivalent:
`prepareSourceBirth`, `GrainResourceBirthTransaction.prepareTargets`,
`GrainResourceBirthAdmission.admitDecodedNative`, and the final durable intent.
Any optimization must prove the same accepted intent or refusal for every
original-prefix input and retain all signature, policy, physical-shape,
nullifier, full-record, post-image, and receipt checks. No such optimization
was made here. Full `validateLoaded` was only 1.93 s in the first run, so a
delta validator is not the first target for this image.
