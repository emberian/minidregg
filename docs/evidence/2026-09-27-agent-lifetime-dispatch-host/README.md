# Event26 Host route source gate

This bounded source cut connects the committed event26 receiver and source
authoring to operator-private Host and resource-client routes. It has **no
native ELF or physical delivery verdict**. The independent overlay is
`/tank/dregg-build/minidregg-fn-frontier-narrow-20260927`; the lower
`ApplicationAgentLifetimeDispatchPaidAuthoring` source/OLean pair is
`7209c857849b9a7256fd049edfad376f5a1537fb65a3cecca73e9716f23b61cf` /
`ffbbfb47ee2946ef59c26e81342cd31986e01756f1dcdd37ff9a12902edf8280`.
It adds the exact current `appPhysicalRoot` and `sessionPhysicalRoot` to both
source plans; these fields are displayed alongside grant, parent, and purse
physical roots before custody signs. The receiver still re-admits all current
and historical facts at submit.

| Source | SHA-256 | Direct OLean SHA-256 |
| --- | --- | --- |
| `Host/ApplicationAgentLifetimeDispatchPaidInspection.lean` | `7b2122d85dbb83cc3a94e30ca5e6a7af4230d3a177e9e3c753817a245e239f58` | `2813ddb63adfe0aaec6933b354db40b2b5ba06cb60a90cd32929d6396ddff20d` |
| `Host/Json.lean` | `2c4de8e1becc6790e2845a4e3aac5dc7361efa8fdc6616020892cd9e954e7be3` | `99d110dfc50485f7e91626a90db3a48f0a6781fee232cb1064897b01a8131510` |
| `Host/Main.lean` | `4ce6e6b10a7a6be9b624143045b04bedb53d479d322a978babad5662a985ae0c` | `fb06423d621c5a47ee6142a5b3b34746589820e6345d45fd0142d3bdf720c2a1` |
| `Host/ApplicationLifecycleStopClaimInspection.lean` | `58ed25fd9a222c0308bc27e57788f0dd87ad0f83febbaf6b3bc6d186580d7e39` | `398193efb0fad2f4370a7e87bf6cfc01d3db385eed508d3617811adc9bafeb81` |
| `native/resource-client/src/transport.rs` | `c86163896fa1f99a7330d46212ab3fcc8be849554abd95fec7842f3b066d652e` | Rust focused test PASS |

The hbox serial commands used `LEAN_NUM_THREADS=2 lake env lean` with `-o`
into this writable overlay for inspection, JSON, and Main in that order. Logs
`/tmp/mini-event26-final-{inspection,json,main}.log` have SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`,
`8f278cb02e04bc3c861e1f43a67395df1479fa9a7445ad78742ca076779591d8`,
and `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
JSON emitted only existing unused-simp warnings; all three exited successfully
with no errors. The focused resource-client `cargo nextest` route test passed
1/1; `cargo fmt --check` passed. An earlier test attempt did not reach tests
because another lane's uncommitted Rust paid client draft was mid-edit; the
retry after that draft compiled is the verdict.
The four captured direct Lean logs and focused broker test log are beside this
README; `SHA256SUMS` pins them. The successful broker log is SHA-256
`fa692ab0e4719c92acb237f24fb3c2706eb2affe3061d94f3d49fb5163fbf480`.

Private Host contract:

- 80 takes a strict lifetime reserve request, requires startup
  `agentLifetimeDispatchFixed` selectors, and returns a current-image
  `ReservePlan`. 81 takes `LE32(plan, strict signature-list)` and returns
  the source-encoded ordinary `callCodec .invoke` for native op2.
- 78 takes a strict lifetime paid request, checks the same fixed selectors,
  and returns a compact one-HTTP-copy `PaidPlan`. 79 takes
  `LE32(plan, LE32(app signature-list, LE32(raw64 grant signature,
  payer signature-list)))` and returns canonical event26 ingress.
- 76 emits the distinct committed event26 permit only from the receiver's
  exact fresh CAS/readback and `withFreshTip` callback. All other outcomes are
  strict `Outcome`; 77 is receipt-only lookup and never yields a permit.
- JSON author/inspect kinds are `application-agent-lifetime-reserve-request`
  and `application-agent-lifetime-paid-request`; plan inspection kinds are
  `application-agent-lifetime-reserve-plan` and
  `application-agent-lifetime-paid-plan`. The committed-frame inspection kind
  is `application-agent-lifetime-dispatch-committed`. Inspection is read-only.
  Broker 76–81 remains operator-private and bounded.

The small independent STOP read-only inspector addition echoes typed
four-field `beginReceipt` and `claimReceipt` beside the existing exact hex
values. It does not mint a physical STOP permit. Physical event26 dispatch and
STOP remain dependent on a newly linked source-qualified Host and the external
runtime's journal/fence checks.
