# Reds (owned by the builder, rewritten whole each round)

Tip: `17c137325e35` (newparticipant-acceptance: a restored world template takes this caller's binary paths). Round finished 2026-11-06T20:19Z.
green: `477bf8e9eb81`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-17c13732`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 477bf8e9eb81..17c137325e35`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `17c13732` newparticipant-acceptance: a restored world template takes this caller's binary paths (owner: apps-hermes)
- `dd70c487` door tests: every accepted submission answers 303
- `dcc46f4e` door: a submission lands on the status page, which names what is queued and refreshes itself; the pa

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.155 | 0.206 | 1.328 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 32.439 | 59.421 | 1.832 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.138 | 0.156 | 1.129 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 24.696 | 82.557 | 3.343 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.359 | 0.293 | 0.816 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 215.393 | 220.969 | 1.026 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-17c13732/flatness.log | - | - | - | - | host-execution, store-retained |
