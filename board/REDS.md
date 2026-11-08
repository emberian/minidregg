# Reds (owned by the builder, rewritten whole each round)

Tip: `338280802421` (policy sources: a source cell's record digest is hashed off its cached bytes, never re-enc). Round finished 2026-11-08T21:58Z.
green: `e8e3bb8c83cc`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-33828080`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log e8e3bb8c83cc..338280802421`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `33828080` policy sources: a source cell's record digest is hashed off its cached bytes, never re-encoded
- `d3a392f2` builder: REDS.md for 7670c1ef08c9 (1 red) (owner: build-loop)
- `7670c1ef` census: the member-command census in the repo, every row against the 10 ms budget
- `1fca8363` past reads off the log: a cell's bytes at a height are its last write there; no checkpoint on a memb (owner: apps-hermes)
- `9b7a6af2` builder: REDS.md for e8e3bb8c83cc (0 red) (owner: build-loop)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.220 | 0.255 | 1.161 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 80.527 | 135.178 | 1.679 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.200 | 0.280 | 1.402 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 49.846 | 167.194 | 3.354 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.550 | 0.531 | 0.966 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 347.450 | 201.848 | 0.581 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-33828080/flatness.log | - | - | - | - | host-execution, store-retained |
