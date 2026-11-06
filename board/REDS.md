# Reds (owned by the builder, rewritten whole each round)

Tip: `2198ead7c9b9` (install-hermes: create resumes after a confirmed birth; rewritten socket units restart). Round finished 2026-11-06T00:16Z.
green: `f1835938bf6e`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-2198ead7`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| gate:composed:residents | composed residents fail | not rerun | no | member-side, infra | fail: residents: RuntimeError: dictionary changed size during iteration; see /ci-composed/ |
| gate:composed:restart | composed restart blocked | not rerun | no | host-execution | blocked: prerequisite residents has not passed |

Suspect commits since green (`git log f1835938bf6e..2198ead7c9b9`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `2198ead7` install-hermes: create resumes after a confirmed birth; rewritten socket units restart (owner: apps-hermes)
- `18667cd9` builder: REDS.md for f1835938bf6e (0 red) (owner: build-loop)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.177 | 0.199 | 1.128 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 28.454 | 71.072 | 2.498 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.136 | 0.184 | 1.347 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 22.672 | 72.902 | 3.215 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.289 | 0.296 | 1.023 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 129.395 | 135.531 | 1.047 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-2198ead7/flatness.log | - | - | - | - | host-execution, store-retained |
