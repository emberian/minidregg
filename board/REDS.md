# Reds (owned by the builder, rewritten whole each round)

Tip: `1d11b2f5798e` (builder: REDS.md for 338280802421 (1 red)). Round finished 2026-11-08T22:21Z.
green: `e8e3bb8c83cc`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-1d11b2f5`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log e8e3bb8c83cc..1d11b2f5798e`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `1d11b2f5` builder: REDS.md for 338280802421 (1 red) (owner: build-loop)
- `6fa4a982` PERF-CLIENT: row 30 fixed; rows 36 (whole-state validation per write) and 37 (index rows per append)
- `33828080` policy sources: a source cell's record digest is hashed off its cached bytes, never re-encoded
- `d3a392f2` builder: REDS.md for 7670c1ef08c9 (1 red) (owner: build-loop)
- `7670c1ef` census: the member-command census in the repo, every row against the 10 ms budget
- `1fca8363` past reads off the log: a cell's bytes at a height are its last write there; no checkpoint on a memb (owner: apps-hermes)
- `9b7a6af2` builder: REDS.md for e8e3bb8c83cc (0 red) (owner: build-loop)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.301 | 0.303 | 1.009 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 73.992 | 160.259 | 2.166 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.425 | 0.305 | 0.718 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 61.400 | 137.845 | 2.245 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.667 | 0.776 | 1.163 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 356.205 | 368.355 | 1.034 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-1d11b2f5/flatness.log | - | - | - | - | host-execution, store-retained |
