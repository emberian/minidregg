# Reds (owned by the builder, rewritten whole each round)

Tip: `19264a688e23` (consent: admit other writers' records as they land, through full readiness (236)). Round finished 2026-11-07T00:15Z.
green: `03708c9a373e`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-19264a68`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 03708c9a373e..19264a688e23`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `19264a68` consent: admit other writers' records as they land, through full readiness (236) (owner: apps-hermes)
- `17c13732` newparticipant-acceptance: a restored world template takes this caller's binary paths (owner: apps-hermes)
- `dd70c487` door tests: every accepted submission answers 303
- `dcc46f4e` door: a submission lands on the status page, which names what is queued and refreshes itself; the pa

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.187 | 0.225 | 1.199 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 34.489 | 62.879 | 1.823 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.135 | 0.201 | 1.486 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 26.757 | 90.920 | 3.398 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.443 | 0.418 | 0.943 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 154.436 | 162.592 | 1.053 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-19264a68/flatness.log | - | - | - | - | host-execution, store-retained |
