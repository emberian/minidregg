# Hosted Hermes as a participant: kill, restart, resolution (2026-09-30)

Two runs of `native/grain-runtime/hermes-journey.sh` on persvati, each on a fresh private Store.
Pinned Host `e22d16b-r3` (SHA-256 `7239…e3db2`), client `mini-0007925` (`3e9c…4513d`), store and
verifier helpers `ad03…e193f` / `c840…0892b`. Exact input hashes: `*/inputs.sha256`.

**Provider: deterministic.** No Hermes checkout exists on persvati. The agent is
`native/grain-runtime/fixture/hermes-deterministic-acp`, a scripted ACP agent (no inference, no key)
installed as `/agent/hermes-acp` inside the real bwrap + systemd worker sandbox (`--network none`).
It makes every effect through the controller's MCP tools via the real `grain-runtime mcp-stdio` edge;
those tools run the same `mini workspace` client the humans use. Its full MCP exchange is
`*/agent-log.jsonl`; what it reported is in `*/phase-*.connector.log`.

| run | grain-runtime | kill landed | restart | resolution of the killed write |
|---|---|---|---|---|
| j3 | `d649ee25…` (commit 2 without breaker reconciliation) | 40 ms after `call.bin`, no `outcome.json` | systemd, 2.4 s | `refused`, `absent-after-submitter-stop` (`ws-attempt-14-retry-0001.json` = `{"type":"absent"}`); Hermes rewrote it (op 55 `performed`) |
| j4 | `1fb94522…` (commit 2) | 600 ms after `call.bin`, no `outcome.json` | systemd, 2.3 s | `performed`, `exact-lookup` (`replayed`, acceptedCount 11) |

Both: startup recovery ran with no operator command (`startup-recovery.json`, `priorRunStopped: true`),
proved the gated worker stopped, settled the parent hold with the `own-managed-law` origin proof,
derived the external-effect acknowledgement for the `--network none` worker, and left the task
`detached`. The next attach recognized the stale generation-1 law as the controller's own and renewed
to generation 3 (the recorded 09-28 refusal). Hermes reloaded its session, listed its attempts
(`mini_workspace_attempts`), read back field 2 = 1, delegated `observe` to the friend and exported the
recipient reference (`reference-hermes-to-friend.json`); the friend imported it with the ordinary CLI
and read field 2 = 1 (`friend-read.json`); the sponsor read the same (`sponsor-read.json`).

j4 also ran the breaker: a hard attachment dropped mid-prompt interrupted it after 1 of 5 directives
and the controller settled the parent hold itself (reconciliation decision 99); a soft attachment
closed mid-prompt let all 3 directives complete and settle (phase E).

Boundaries: the hosted grain's two subjects are genesis enrollments (the only AgentGrain birth route
on this Host admits only against the genesis image); the friend enrolled through `mini enroll`.
No inference, no provider spend, no network for the worker. Startup recovery took 65–74 s on a
loaded box (load ≈ 23), dominated by sequential signed Mini round trips. All services stopped
(`timeline.tsv`, last line); Stores and attempts are retained under the run directories on persvati
(`/home/ember/build/mini-product-20260930/m5-hermes/run/j3`, `j4`); no keys are copied here.
