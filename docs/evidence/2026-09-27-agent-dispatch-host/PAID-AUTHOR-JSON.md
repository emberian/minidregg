# Paid agent dispatch operator authoring and inspection

The strict `Host.Json.author` kinds are `application-agent-reserve-request`
and `application-agent-paid-request`. The reserve request has an exact nested
`base` in the existing `application-dispatch-request` shape, plus the fixed
parent/purse capability selectors, payer subject, nonnegative reserve and
charge, and reserve operation ID. Its only body-bearing field is `base.http`.
The paid request takes exact canonical `fixedRequestHex` and the *framed*
`contextHex` returned by the source reserve plan, plus `reserveIndex`. It
strictly decodes both source codecs. The operator Main route must compare
the reserve request's fixed selectors with its startup custody pin before
exposing a signing plan; this JSON route is not a signer or authority.

`Host.Json.inspect` accepts the corresponding request kinds and echoes exact
canonical request bytes and selectors, HTTP digest, and, for the paid request,
the canonical reserve context, original reserve index, app/session/ticket,
parent/purse generations, payer, reserve amount, charge, and operation IDs.
The separate source-owned `ApplicationDispatchAgentPaidInspection` presents
`application-agent-reserve-plan` and
`application-agent-paid-dispatch-plan` through Main. Its plan output includes
`canonicalPlanHex`, ordered exact signing headers, key IDs/epochs and message
bytes, image boundaries and height, and the full canonical HTTP request.
The paid plan's `compactSelectorRequestHex` deliberately omits the duplicate
HTTP body; the full request appears once in `canonicalHttpHex` and the app
ingress. A reserve receipt is available only after native reserve acceptance;
the paid plan carries its selected verified `reserveIndex`, not a caller-made
receipt. Native event21 admission remains the authority and rechecks the
reserve/history/current purse and app plan before delivery.

In a private Persvati overlay, final PaidAuthoring and PaidInspection OLeans
were copied as ordinary files into the coherent completion overlay, then
`Host.Json` compiled directly with `LEAN_NUM_THREADS=2`. A focused executable
roundtrip authored and inspected both request frames, including the framed
reserve context, and printed `paid request authoring roundtrip: ok`. This is
a source/codec gate, not a linked Host or accepted paid dispatch.

| Artifact | SHA-256 |
| --- | --- |
| `Host/Json.lean` | `67aef90a39bf52ebc841acac854f716d321bab2a775908a6c829e64f6bd5694e` |
| `Kernel/ApplicationDispatchAgentPaidAuthoring.lean` | `d79aba4f397d9d506b502689a5a801b0ec34ca3c204bc1fa0eaf38fd72b21c95` |
| `Host/ApplicationDispatchAgentPaidInspection.lean` | `dd0a9b82bffc1982b2749a11d4ab03dcab41c9b1a08fa25c7ed97ec0215c8631` |
| private `Host/Json.olean` | `a58005a8db76ba10ac9ebdb56f750106e80fa92d941d7e2bf8cf10fb0d4d6aaf` |
| private PaidAuthoring / PaidInspection OLeans | `44d987d9c22747f8073391e71018743dfbb6547c671402d73eb47e6c25d0389a` / `632d503b4b6c73a0947e66eb3ef1b3deddc2debb45467bf7c82fbf3242ebef71` |
| private Json compile log | `90e72ed14136d3c102d08c5a70fff479625efe3ef05adaaac5bdb3f546b1a897` |
| private request roundtrip source / log | `f8858a0f91fffd0eef4db6ef76cfd18cab3a2a473ee0331e9ca60a311c906578` / `3fa160234ca88831728bb016c3b39ac3b5e958131e5581ca969dbed2ca660d03` |

Private files are under `/tmp/minidregg-completion-src/Host/Json.lean`,
`/tmp/minidregg-paid-union/{Host,Kernel}/`, `/tmp/minidregg-paid-Json.log`,
and `/tmp/mini-paid-author-check.{lean,log}` on Persvati. Source and private
compiled source copies matched by SHA-256.
