# Event28 source checkpoint

This is a source-only gate for the missing post-START enrollment path. It does
not claim native acceptance or an r3 Store mutation.

The event28 request names an already issued ticket index/resource, a role,
capability selectors and a nonce. Verified Replay selects the exact original
event22 issue from its same-walk history, checks its complete four-field receipt
and retained record, then admits the joint session/descriptor command at the
current image. Three independently signed app, installed-manifest and ticket
observations add physical read guards to that one intent. The app need only be
observed; participant operators do not receive app-mutate authority. Current
source construction checks serving phase, installed interface/schema and role
ceiling, actual session generation, and the stable descriptor atom's exact old
record for renewal. The event stores the complete ingress as version 28.

The operator plan is a proposal. Its canonical source-selected signing slots
are the ordinary joint invocation slots followed by app, manifest and ticket
observation slots. Detached assembly reselects the current Verified image and
requires byte-identical plan before packaging signatures. Native submit and
receipt-only lookup are a following cut; no physical admission follows from an
inspected plan.

Direct Lean checks used an isolated writable overlay
`/home/ember/build/minidregg-session-enroll-source-20260927` on Persvati over
the certified cb55 source/OLean closure
`/home/ember/build/minidregg-cb55b81-native-20260927`. Each new module was
compiled serially with Lean 4.30 and `LEAN_NUM_THREADS=2`; no broad Lake build
or live Store write was performed. Source, Construction, Admission, Intent,
Authoring and Inspection logs are empty at exit 0. NativeHostReplay exits 0
with only the existing propext/Classical.choice/Quot.sound axiom report lines.

Exact source SHA256 at this checkpoint:

```
fc57e2688b218d2b4545429a073b8441f5b2a2f84db5b75caeb37e481857e5b0  Kernel/ApplicationGrainSessionEnrollmentSource.lean
2787f9edf2fcfb3c5926fecf9dd8f38fe1df8553f177fb38c9754876765f2f2b  Kernel/ApplicationGrainSessionEnrollmentConstruction.lean
6d8f213ae9413a6a76dfd0590647e23652ec6df2f906bd48ab6d0316cdc3ad5b  Kernel/ApplicationGrainSessionEnrollmentAdmission.lean
1c20aef298db3714d4d2f6360f8a62478e01f79faab9d806affcb2d6f61dcccd  Kernel/ApplicationGrainSessionEnrollmentIntent.lean
fd62924391e36a7b8285fbb55a5b19cab9fc099753e7c6f96b8f82f29f2f197f  Kernel/NativeHostReplay.lean
51eab7c1da1620004134068840fd439b6b5767b859d713a082cf2232eea30c36  Host/ApplicationGrainSessionEnrollmentAuthoring.lean
4a9629b2f2b83bd6c29a39cc89b0e8711ff76e6fa0d7c3b77be4f9f591ee70b6  Host/ApplicationGrainSessionEnrollmentInspection.lean
```

Operational prerequisite for the existing r3 allocation: each participant's
event22 ticket-observe capability and Bob/agent app-observe capabilities require
explicit narrow delegation before enrollment. The three observation headers
inherit the joint command subject, so Bob/agent manifest-observe capabilities
also require admitted observe-only delegation. Alice's owner capability can
serve her own manifest observation. No broad app-mutate grant is implied.
