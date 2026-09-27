# Event26 lifetime dispatch authoring and inspection (source-only)

This cut adds separate v3 signing plans for the ordinary purse reserve and
the post-reserve paid dispatch, plus read-only JSON inspection. It does not
route Host commands or establish a native event26 delivery.

Source at the narrow check:

| File | SHA-256 |
| --- | --- |
| `Kernel/ApplicationDispatchAuthoring.lean` | `1677fdecb2d98619d7a01eda1da15f55d51a81b2729443de5b75106e95beb439` |
| `Kernel/ApplicationAgentLifetimeDispatchPaidAuthoring.lean` | `cbe6bd08d90078ef76085a8bd25f670ba31cc4e2549497675ba3c8dcd7af4343` |
| `Host/ApplicationAgentLifetimeDispatchPaidInspection.lean` | `41d0a89cc0ebdbf30a39035bbd36765a74cdcf94eb17842e775cf84d36f67a39` |
| `Host/ApplicationAgentLifetimeDispatchInspection.lean` | `3e05f1c8d338a7b9830684c1095f17af73a8f8667951d1fffd80338dac6fcc42` |

In the isolated hbox overlay
`/tank/dregg-build/mini-lifetime-grant-review-20260927`, all four
`LEAN_NUM_THREADS=2 lake env lean -o .lake/build/lib/lean/<Module>.olean <Module>.lean`
commands exited 0. Seat2 was atomically claimed and released for each serial
gate. Exact OLean SHA-256 values in module order above were
`0c54dddaebb13304f464a149dfa1a17396fdeac6e1b5c37086f6a937bc653f6c`,
`fa8cbba0ec2cee77640e4f9e40944327f5cf6f8ac973d8a2ccae928c9923ae03`,
`7716f34ee359bec36cb091b5558821ab8e18fd53df94590fdd5adbe73378a952`,
and `af1ad6c0bf7d14bb6aca7051d5b4473e96eac15e61e86cdd136aaf7cff965192`.
Saved logs were
`/tmp/mini-event26-shared-author-r1.log`,
`/tmp/mini-event26-paid-author-r1.log`,
`/tmp/mini-event26-paid-inspection-r3.log`, and
`/tmp/mini-event26-committed-inspection-r1.log`. Each was empty (SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`);
the shell printed `PASS` only after all commands exited successfully.
This is a direct Lean gate, not a native Host build or runtime acceptance.

The v3 author request's `inspectRequest` exposes full fixed selectors,
exact canonical HTTP bytes/digest, and decoded method, path, query, ordered
headers (including each generated flag), and body before signing. The same
`http` view appears in both plan inspectors so the controller can compare
the source-decoded request to its retained request without implementing a
second Lean codec. The reserve plan exposes
the current source-selected app/session/parent/purse generations, original
event22 and event27 four-field receipts, certified initialized grant root,
and current full grant/parent/purse physical roots. The paid plan retains
the same historical binding plus the exact admitted reserve receipt and
index. Its selector request contains an empty HTTP placeholder; the full
request occurs once in the unsigned app ingress. Its inspector exposes all
app, grant-observation, and payer signing headers. The purse physical root
is a **current fence at each plan stage** and normally differs before and
after the ordinary reserve. Do not compare those two roots as a historical
identity. The original event22/event27 receipts, grant identity, and reserve
context are the historical/canonical bindings.

The committed-frame inspector exposes the source-projected current
app/session/parent/purse coordinates separately from the original
generation-bound session origin, together with the exact event22/event27
receipts, grant roots, reserve receipt, request digest, and event26 receipt.
This JSON is a decoded view of bytes. Only a native fresh-CAS
`ApplicationAgentLifetimeDispatchReceiver.Permit` can authorize fd3
delivery; a replayed/already-present image or decoded JSON cannot.

Pending: Host Main/Json routes, native event27 grant issuance, native event26
qualified build and actual Rust consumer/recovery. No provider or app call
was made for this evidence.
