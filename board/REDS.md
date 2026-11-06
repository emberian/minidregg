# Reds (owned by the builder, rewritten whole each round)

Tip: `0a92413139bd` (consent: admit other writers' records as they land (frame 237), off the member's command p). Round finished 2026-11-06T23:38Z.
green: `477bf8e9eb81`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-0a924131`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 477bf8e9eb81..0a92413139bd`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `0a924131` consent: admit other writers' records as they land (frame 237), off the member's command path (owner: apps-hermes)
- `17c13732` newparticipant-acceptance: a restored world template takes this caller's binary paths (owner: apps-hermes)
- `dd70c487` door tests: every accepted submission answers 303
- `dcc46f4e` door: a submission lands on the status page, which names what is queued and refreshes itself; the pa

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.229 | 0.242 | 1.053 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 36.905 | 107.071 | 2.901 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_cpu_ms | 0.159 | 0.272 | 1.719 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 25.791 | 126.634 | 4.910 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.608 | 0.494 | 0.812 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 169.264 | 170.608 | 1.008 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-0a924131/flatness.log | - | - | - | - | host-execution, store-retained |
