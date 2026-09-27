# Disabled agent API transport contract

`native/spk-host/src/agent_api_wire.rs` SHA-256
`ddeb56bcadd59dd697a982952aacaae150cc1191bf322e68e928ddd33966261b`
defines a private transport frame only. It creates no socket or app listener and
does not accept a Mini permit. Agent dispatch remains unavailable until the
separate event21 reserve/permit/projection and caller-only fence qualify. Human
event11 op34 cannot authorize this route.

The frame is a 4-byte big-endian length (1–262144), then strict tagged JSON.
`hello` has `protocol`; `dispatch` has `protocol`, canonical decimal
`operation_id`, HTTP `method`, relative `path`, `query`, ordered ordinary
`headers` with `name` and `value`, and lowercase `body_hex` (≤65536 decoded
bytes). `inspect` has `protocol` and exact `operation_id`. Protocol is
`mini-spk-agent-api-v1`. The request has no subject, session, ticket, or
purse selector. A fixed socket binding carries those operator-selected
coordinates and a systemd InvocationID; its SHA-256 is a transport comparison
key, not Mini authority. Read/write use one 30-second absolute frame deadline.

Response variants are `binding`, `http`, `refused`, `uncertain`, and
`inspection`; every nonbinding variant echoes the operation ID and binding
digest. A future server must enforce owner-controlled path/ACL, fixed
SO_PEERCRED UID, exact inode and binding comparison, durable one-send journal,
and inspect without resubmission. Caller EOF does not prove Mini cancellation.
The caller's hard stop must fence only its own dispatch attempt, never the
shared SPK app unit.

For component validation, the new module was copied into the private hbox
snapshot `/tmp/mini-spk-http-response-20260927/native/spk-host`, and its module
declaration was added **only to that snapshot's** `lib.rs`. With two Cargo jobs,
offline locked `cargo nextest run` passed 73/73 and strict all-target Clippy
passed. That snapshot includes the owned resident completion files but retains
earlier pinned copies of concurrently edited `rpc_adapter.rs`, `sandbox.rs`,
and `spawn_gate.rs`. No app, Mini Store, controller, or network service ran.
