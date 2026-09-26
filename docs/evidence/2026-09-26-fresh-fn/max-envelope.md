# Selected Mini fn consumer envelope probe

The pure Lean probe `scripts/probe-fn-consumer-max-envelope.lean` (SHA-256
`ef45fb708c4cac1bb70eaa60501dcb0cf410ded3ff9f14145240766c84b3c8c7`)
passed against the coherent B `Host.Main` build in
`/tmp/minidregg-overnight-20260926-final`. It constructed a canonical
FnEvidence V2 package of exactly 1,048,576 bytes, a synthetic 1,516,384-byte
carrier, a 196,608-byte Store poll event, and a separate 65,538-byte
historical verdict event. It checked strict decode/re-encode for the package,
binding, portable inbox, Store poll inbox, command, observation intent,
conflict evidence and conflict command, and exercised the conflict nonce and
atom construction.

The full opcode-12 response shape included the nested
`fn-poll-consumer-decision-v1` metadata, Mini origin receipt, fresh decision,
hex-encoded intent, outer `fn-consumer-poll-session-v1` fields, and opcode byte.
Its encoded size was **5,660,971 bytes** under the selected
`maxHostFrameBytes` of **6,194,884**, leaving **533,913 bytes**. Measured inner
sizes were binding 1,048,770; portable inbox 1,518,487; Store poll inbox
262,280; command 2,829,885; observation intent 2,829,971; and conflict
command 2,829,685 bytes. The [exact probe log](max-envelope-op12.log) has
SHA-256 `7c5c63fb84f3a3cd034f4012bee844cc2568a8ecd154466f509666d0eddfec6e`.
The earlier [direct-inner log](max-envelope-inner.log) also passed before the
actual opcode-12 JSON measurement.

This checks Mini's selected bounded reader and complete response allocation;
the filler package and carrier are not fn-authenticated articles, the command
is not submitted to a receiver, and the 196,608-byte poll event is not a
universal limit of current fn HEAD. Actual fn acceptance remains governed by
the selected Store operator profile and the distinct live A/B exchange.
