# Reds (owned by the builder, rewritten whole each round)

Tip: `7670c1ef08c9` (census: the member-command census in the repo, every row against the 10 ms budget). Round finished 2026-11-08T21:09Z.
green: `e8e3bb8c83cc`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-7670c1ef`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log e8e3bb8c83cc..7670c1ef08c9`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `7670c1ef` census: the member-command census in the repo, every row against the 10 ms budget
- `1fca8363` past reads off the log: a cell's bytes at a height are its last write there; no checkpoint on a memb (owner: apps-hermes)
- `9b7a6af2` builder: REDS.md for e8e3bb8c83cc (0 red) (owner: build-loop)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.187 | 0.258 | 1.381 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 42.894 | 135.682 | 3.163 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_cpu_ms | 0.142 | 0.323 | 2.271 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 44.698 | 148.965 | 3.333 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.562 | 0.689 | 1.227 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 260.892 | 354.224 | 1.358 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-7670c1ef/flatness.log | - | - | - | - | host-execution, store-retained |
