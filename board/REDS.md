# Reds (owned by the builder, rewritten whole each round)

Tip: `976f31067e01` (receipt continuity: no verifier process for a read whose point is already known). Round finished 2026-11-07T01:45Z.
green: `eb932b7c6547`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-976f3106`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log eb932b7c6547..976f31067e01`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `976f3106` receipt continuity: no verifier process for a read whose point is already known (owner: apps-hermes)
- `b4e212ca` transport: one verified sealed snapshot per pinned image per process (owner: apps-hermes)
- `1b753fe1` consent catch-up: an empty intent, not full readiness (236), which spun demo providers (owner: apps-hermes)
- `19264a68` consent: admit other writers' records as they land, through full readiness (236) (owner: apps-hermes)
- `17c13732` newparticipant-acceptance: a restored world template takes this caller's binary paths (owner: apps-hermes)
- `dd70c487` door tests: every accepted submission answers 303
- `dcc46f4e` door: a submission lands on the status page, which names what is queued and refreshes itself; the pa

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.159 | 0.204 | 1.287 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 29.617 | 74.825 | 2.526 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.149 | 0.166 | 1.118 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 34.663 | 71.293 | 2.057 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.400 | 0.387 | 0.968 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 377.959 | 246.013 | 0.651 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-976f3106/flatness.log | - | - | - | - | host-execution, store-retained |
