# Retained Hermes session, second Mini publication, and timeout boundary

This run resumed the r5 Mini store and the same unmodified upstream Hermes ACP
session `61a3176e-4a07-4a4f-9a3a-11b678a95e3e`. The frozen controller repaired
only the prior scoped workspace fingerprint error, then sent `session/load` for
that exact ID. The upstream worker logged restoration of six messages from its
SQLite DB, registration of the three Mini MCP tools, and successful load before
the second `session/prompt`. `worker-events.json` is a bounded classification
of those worker log events; it contains no prompt or tool-result bodies.

The second prompt's signed `mini_read_resource` saw object 7003 root
`55070908931993074135985362517665169451634431671625479692889086081017559966815`.
The local fixture asked `mini_publish` to create field 2 with value 2, using
that observed root as `expectedTargetRoot`. The native tool-settle call was
**confirmed installed**, `acceptedCount: 20`. A separate signed cap94 query
then returned root
`113165090123915682967404063493066207533634109815478468793224753513096677075760`
with fields 0=1 and 2=2. The exact accepted call is `tool-settle-call.bin`
(SHA-256 `6020448383650df11cdbfaf0faeee5e176c1153f6e8986892f7bc6c3425cb163`).

This is **not a successful Hermes tool receipt**. Upstream Hermes timed out
`mini_publish` at its default 300 seconds and the fixture rejected the wrapped
error; the worker later reached its 600-second systemd limit. Mini's native
settlement completed after Hermes had timed out. The controller then cleared
the tool hold and settled the parent allowance in native attempt 55,
`acceptedCount: 22`. `journal-projection.json` shows no remaining child,
pending operation, hold, settlement, or unresolved external effect. The exact
session ID remains with `loadVerified: true` and `pendingPrompt: true`, marking
the interrupted turn. No new ACP session was silently created or retried.

The Linux host binary SHA-256 was
`faf1f8371f692c404acd5b4c5727bd2019249c1b5f7d1850022789d35f4ee30f`.
The controller and sandbox MCP proxy were identical binaries SHA-256
`023be6b425b47312777b1e23855aab7478a1b992d18256c43de9990e06aee18f`,
from frozen `main.rs` SHA-256
`06225a4d8198383091a2b97fc08baa071028ded505ff93134074faed041fbf6c`.
The local deterministic provider binary SHA-256 was
`eb39042732749593fef4ed51269f0a2565b48d961f8403f9acb0d86d69277c24`,
from source SHA-256
`f59cbaab84d8170227fc45c5dba506fce5ea9ebcb8716407d55a5926502f632d`.
Current source may differ because HTTP parsing was subsequently hardened; no
provider/auth service was contacted beyond the loopback fixture.

The raw final controller journal remains at
`/tmp/mini-hermes-provider-codec/evidence-real-r5/runtime-state/journal.json`
on Persvati (SHA-256
`38be769b6bb0ee27506878479cd24728bdaf379d4c18d57935ca0d8613d0e417`).
The published journal file here omits its runtime binding and config. The
Store snapshot taken after the acceptedCount 22 parent settlement, with its
exact original pinned config, is under
`/tmp/mini-hermes-provider-codec/perf-snapshot-r6/` for read-only latency
analysis; no live keys or config are included in this evidence directory.
