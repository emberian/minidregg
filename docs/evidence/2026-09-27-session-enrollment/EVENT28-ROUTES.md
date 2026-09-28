# Event28 receiving and Host routes

Source-only qualification. This cut has not been submitted to a native Store.
The final native build must include committed ordinary-birth exact-readback
repair 2721253; the cb55 OLeans below were only a warm dependency baseline for
the bounded source check.

Op82 decodes the strict request and returns a current Verified enrollment plan.
Op83 accepts `u32le(plan length) || plan || signaturesCodec.encode(raw64 list)`,
reselects the current verified ticket and image, requires byte-identical plan,
then returns one strict event28 ingress. The plan presents one ordered `slots`
array: ordinary joint invocation slots, then app, manifest, ticket observation
slots. Each carries exact `headerHex` and decoded signature key/epoch/algorithm.
Host JSON kinds are `application-session-enrollment-request` (author/inspect),
`application-session-enrollment-plan` (inspect), and
`application-session-enrollment-ingress` (inspect). Inspection is presentation,
not authority.

Op84 joins the verifier's admitted event22 ticket to the current native joint
command and signed app/manifest/ticket reads. It performs one CAS and validates
the exact physical post-image; the resulting typed Verified successor updates
the resident session without a cold reopen. Nonexact readback returns uncertain
and never resubmits. Op85 takes the exact ingress and selects only its original
verified four-field receipt, with no write or dispatch permit. All four ops are
intended for the owner-private broker; public transport must refuse them.

The operator-private op38 completion diagnostic propagates the bounded lower
admission refusal detail. It does not change completion admission or public
transport access.

Direct serial Lean 4.30 checks used the independent writable Persvati overlay
`/home/ember/build/minidregg-session-enroll-source-20260927` over certified
cb55 OLeans. `ApplicationGrainSessionEnrollmentReceiver`,
`ApplicationLifecycleCompletionV2Receiver`, and `Host.Main` exit 0 with empty
logs. `Host.Json` exits 0 with its pre-existing grainPolicy warnings and axiom
reports; there are no new errors. No broad Lake build or live Store write ran.

```
8b6d5fdf72f80af9d75abf6f049f88ff7998807780011acf675701f74b8f6df8  Kernel/ApplicationGrainSessionEnrollmentReceiver.lean
a5958e190c4190475f142c3a3c7f6c8a85176ff1426ee981b3681ed7eae78e19  Kernel/ApplicationLifecycleCompletionV2Receiver.lean
4a9629b2f2b83bd6c29a39cc89b0e8711ff76e6fa0d7c3b77be4f9f591ee70b6  Host/ApplicationGrainSessionEnrollmentInspection.lean
9197acfcbd02ee58b3bcc06d49e6241fe0d7109e7b3ce35640f88f2d390150db  Host/Json.lean
8586f2a7d95dbd4a62ed268999cf0849c8e824d9c43fbb1d49020ed545187cb6  Host/Main.lean
```

Operational gates before the five planned r3 enrollments: explicitly admit
participant-specific observe-only grants for app, manifest and each event22
ticket; run a source-qualified native build; then check stale serving generation
and physical root, wrong ticket/receipt, role above ceiling, stale renewal
preimage, one-CAS exact replay, and receipt-only recovery on a copied Store.
