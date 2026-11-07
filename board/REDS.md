# Reds (owned by the builder, rewritten whole each round)

Tip: `b4e212ca447f` (transport: one verified sealed snapshot per pinned image per process). Round finished 2026-11-07T01:09Z.
green: `eb932b7c6547`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-b4e212ca`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log eb932b7c6547..b4e212ca447f`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `b4e212ca` transport: one verified sealed snapshot per pinned image per process (owner: apps-hermes)
- `1b753fe1` consent catch-up: an empty intent, not full readiness (236), which spun demo providers (owner: apps-hermes)
- `19264a68` consent: admit other writers' records as they land, through full readiness (236) (owner: apps-hermes)
- `17c13732` newparticipant-acceptance: a restored world template takes this caller's binary paths (owner: apps-hermes)
- `dd70c487` door tests: every accepted submission answers 303
- `dcc46f4e` door: a submission lands on the status page, which names what is queued and refreshes itself; the pa

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.156 | 0.178 | 1.139 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 30.545 | 61.016 | 1.998 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.122 | 0.168 | 1.378 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 22.831 | 79.253 | 3.471 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.395 | 0.327 | 0.828 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 435.291 | 231.008 | 0.531 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-b4e212ca/flatness.log | - | - | - | - | host-execution, store-retained |
