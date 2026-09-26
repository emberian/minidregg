# Workroom content R: B receive recovery boundary

This is an interim keyless record. Fresh B used the certified native Host
`/tmp/minidregg-overnight-20260926/minidregg-host-postbbf` (SHA-256
`919c3b7b64b7bff11d47a52993c7700b8028aa8596013cf396f41fd4f98c3038`)
and public Mini client from `dee5f8d` (SHA-256
`4e4beea360b5c0144b49ac6e4a08132e1ab7646d08a8a532bcc9091ba9c0b982`).
The operator-pinned B config has SHA-256
`c54ce20f72d8ba64fc5c4a16db857e816628562b52eb6e18c084da3c0e49eda8`.
Private exact state is retained at
`/tmp/mini-workroom-publisher-20260926/b-drain-state`; no raw call,
carrier, key, or credential is copied here.

One `consumer-drain-once --max-pages 16` typed poll returned
`accepted-decision` with an inner `proposed-fresh` publication decision.
Its complete op12 frame was 2,605,129 bytes (SHA-256
`e3991988f0eecc86a566541bdd16662c267ca298bcbe95785a1976aaa45519b0`).
The Lean-authored intent was 1,301,871 bytes (SHA-256
`624239ea1e8ad630884c403bb687ea4a0da2105585f319b1c780cf7fac41efad`).
The worker used `submit --prepare-only true` and durably retained the exact
1,302,784-byte `call.bin` (SHA-256
`4ceab566aeadb47ae29147aa53305482d56c8f3fc619043c5e863a516b628a23`)
before changing its state to `Sending`.

The socket submission lost its Host reply at the 600-second frame-read
deadline: `mini: uncertain host response read: frame read deadline`.
It retained no outcome and sent no fn ACK. An attempted read-only socket lookup
failed at the broker's 30-second Host request-write deadline, also without an
outcome. The stopped worker remains in `Sending`; no second submit, new intent,
or ACK was made.

One direct, read-only lookup of that same retained call against the same
certified Host and pinned config completed after about nine minutes. The
132-byte canonical outcome (SHA-256
`39e04ff688e63d0d8d568cd2ead0b652e7d723eff4f9bac8c36d2b88f169b822`)
decoded to `type=confirmed`, `confirmation=replayed`, accepted count `3`,
transaction ID
`82876784764185867945530134274097760617071008281531308989391057144998338336180`,
event ID
`76255522961118423695046404792380634000584551157555388805752752222329055606806`,
and image boundary
`29936162402506592586987268492039189617605932909123840279128651316255128051042`.
The exact lookup JSON has SHA-256
`0e95aa9951a4624f1f800e474b6fa7eab3155a78e90bab64d8b8b967337cdeb0`.
This proves the original call installed once despite the lost socket response.

The B worker has **not** durably ACKed fn or completed its signed inbox readout.
The next step is same-call lookup and ACK using the separately source-qualified
faster Mac Host; the old Host's timeout and this exact pending state remain
retained. No further B poll or R POST is authorized by this interim record.
