# STOP-only plan and verified claim join — source gate

Op66 now returns the strict `LAUNCH-STOP-OPERATOR-PLAN/v2` for a STOP request.
Its witness is selected from the latest admitted event25 running completion in
the current Verified image. INSTALL/create/continue retain the prior v1 plan
bytes. Op67 accepts the two plan frames through distinct strict decoders;
the v1 assembler refuses STOP and the v2 assembler requires the running
witness shape. `inspect application-lifecycle-launch-stop-plan` presents the
exact plan, request, signed slots, and prior running receipt/incarnation.

The read-only CLI
`inspect-stop-claim STOP-PLAN.bin FRESH-COMMITTED-CLAIM.bin RESULT.json`
loads and verifies the current Mini image once. It requires the retained
plan's unsigned BEGIN to equal the admitted event23 original after inserting
only the recorded detached signatures, requires the event24 original claim
and exact receipt to match the committed frame, and reselects the prior
event25 running witness from the same Verified walk. Its JSON echoes both
input frames, original BEGIN/claim receipts, the selected running receipt,
and the existing strict plan/claim inspection views. It is presentation, not
a launch permit. The physical caller must compare the echoes with its
retained op66 response and fresh CAS-winner op26 callback, then fence its
current protected unit before acting.

Changed source pins:

| File | SHA-256 |
| --- | --- |
| `Host/ApplicationLifecycleStopClaimInspection.lean` | `5db1793140836a281e9abaf6a6a5694c1e8ed09564ca471e365fdcb5b9b53e3e` |
| `Host/Json.lean` | `45fe89d6c1482d5fd28b82822e68ff33afe4dd291c074eee53cf339f2c190257` |
| `Host/Main.lean` | `fb4624bea78b183f1a0fadb76d67a7fb117f7a360ffae64d6253ebfcd409473e` |

Imported frozen STOP plan modules: BeginAuthoring source
`a6ea2d960f9f8e27aac5eed87adb571b53d6d98ffbb2e5a8db02250b10f294f1`
and BeginInspection source
`d95962475aa8a5a57d522d3a4cfe0b18d47a7fc556b903a42ecf7958e1d0e482`.
An independent writable hbox overlay imported source-matched OLeans and
compiled the new inspector, Json, and Main serially with `LEAN_NUM_THREADS=2`.
All three direct Lean commands exited 0. Inspector and Main logs are empty;
Json reports existing linter/axiom notes. Resulting OLean SHA-256 values are
`e3b6330da9c2e8b127d3723a781c501049d75e0659c7055308c1773b9cc48eb7`,
`b62530846d7f2533ff0bd63b397a2e779a735e79517ced501927fe7c7226e222`,
and `daecbebfefe60466dd66d66502aa1057c5c12560bbaf29369d51eae5084d1843`.

No linked native binary or physical STOP action was accepted by this source
gate. The inspector does not replace the fresh op26 permit, a current host
journal check, or the signed v2 physical report.
