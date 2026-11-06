# Reds (owned by the builder, rewritten whole each round)

Tip: `dd70c487d4d0` (door tests: every accepted submission answers 303). Round finished 2026-11-06T19:58Z.
green: `477bf8e9eb81`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-dd70c487`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 477bf8e9eb81..dd70c487d4d0`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `dd70c487` door tests: every accepted submission answers 303
- `dcc46f4e` door: a submission lands on the status page, which names what is queued and refreshes itself; the pa

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.188 | 0.226 | 1.205 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 50.894 | 82.041 | 1.612 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_cpu_ms | 0.147 | 0.257 | 1.748 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 29.290 | 129.305 | 4.415 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.556 | 0.381 | 0.685 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 165.898 | 153.760 | 0.927 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-dd70c487/flatness.log | - | - | - | - | host-execution, store-retained |
