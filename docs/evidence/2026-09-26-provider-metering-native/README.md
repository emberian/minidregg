# Read-only provider usage quote through Mini

On Persvati, the certified Linux Host `minidregg-host-provider-metering-op6`
(SHA-256 `51f790fa55f734772c37330dc0ab7408f3438d4e168b74bd6432d0b1cdb111f6`)
and committed pinned-v2 `mini` client (SHA-256
`fee5bc861d74c9e432db2374ede36b62852a80346a46f1dc89133dfa79bf11eb`)
ran against an isolated copy of the finished gateway-r1 Store at
`/tmp/mini-provider-metering-native-20260926`. The Host build certified its
171-module linked source closure and native artifacts. The linked source
includes `Kernel.ProviderMetering`, `Host.ProviderUsage`, and the Host op19/op6
route. `Host.ProviderUsageAudit` is a separate narrow executable parser gate;
its closed examples are not kernel proofs. No upstream request, signing
operation, or Mini settlement occurred in this check.

The operator config pins provider resource `7204`, model
`mini-hermes-protocol-fixture`, tariff version `1`, and rates of 1,000,000
permission micro-units per million input/output tokens. A direct Host profile
query returned those pins and tariff digest
`53031313001255559760487189251062546394318675101431160549090574078503637496084`.
The complete SSE test response reports one prompt token and two completion
tokens with a finished choice, one terminal usage event, and a terminated
`[DONE]` event. The exact retained gateway-r1 request bytes (SHA-256
`e4d0dc1453fb8af7ad3ce6fde8cd68a48956bed0d2add53305215d0f6463896b`)
were used for all cases; those request bytes remain in the private Persvati
fixture because they contain an earlier conversation.

The private `mini serve` socket was started on the copied Store. Four
`mini meter --host HOST --config CONFIG --socket SOCKET --metadata META
--request REQUEST --response RESPONSE --dir NEW-ATTEMPT` calls produced:

| Case | Host op | Result |
| --- | ---: | --- |
| Complete SSE, reserve 3 | 19 | Typed quote, charge 3; source-authored `settle` operation with charge 3 |
| Unterminated `[DONE]` event | 255 | Explicit refusal; full `reply.frame` retained |
| Retained stream without terminal usage | 255 | Explicit refusal; full `reply.frame` retained |
| Complete SSE, reserve 2 | 255 | Explicit over-reserve refusal; full `reply.frame` retained |

The safe local [metadata](metadata.json), [over-reserve metadata](over-reserve.json),
[complete SSE](complete.response), [truncated SSE](truncated.response), and
[missing-usage SSE](missing-usage.response) are retained here. The first
missing-usage check used the earlier fake-provider stream; a second native
check used the safe local equivalent and produced the **same** 255 reply frame
SHA-256. The four bounded raw frames are [valid](valid.reply.frame),
[truncated](truncated.reply.frame), [missing usage](missing.reply.frame), and
[over-reserve](overreserve.reply.frame). The typed projection is
[meter.json](meter.json).

The private attempts remain at
`/tmp/mini-provider-metering-native-20260926/attempt-{valid,truncated,missing,overreserve}`.
Their `reply.frame` SHA-256 values in that order are
`3bbfa6e53aa4bc2b4e6af210bbb952be0dbd0ff6377a53f54030c04d0686e44a`,
`9354e47a951f220d92c77c9677961a81a724dfa9c533161ac19fdcb0a90dba9c`,
`d1a6dbc89a88a34199188120946c903f53d77da7ecb603f340f98fbfd154a555`,
and `20fbc452559d88e1172749837a15aea66b89f16b55dfdb5d830dad3991070473`.
The typed quote is SHA-256
`6c2c9342e0701c42745921c00b5c449f7265d0e08aa8058cf16b8c5d5c39c751`.
The copied SQLite image and untouched r1 original both remain SHA-256
`4c099dae65a3cf8ccff7b1603ca9930e695be57b30803237d29294db3d8143a1`.

This is a source-owned quote over **provider-reported** usage under a configured
tariff. It neither proves an invoice nor authorizes a Mini charge by itself.
The runtime consumer must bind exact request/response/header bytes, operator
tariff and model, signed provider hold, and parent witness before submitting
the source-authored settlement through ordinary Mini admission. Missing usage
has no fixed-charge fallback.
