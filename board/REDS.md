# Reds (owned by the builder, rewritten whole each round)

Tip: `b2d88f3ae0be` (open: record bodies and checkpoints are packed; the whole-log read is paged). Round finished 2026-11-09T00:51Z.
green: `e8e3bb8c83cc`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-b2d88f3a`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log e8e3bb8c83cc..b2d88f3ae0be`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `b2d88f3a` open: record bodies and checkpoints are packed; the whole-log read is paged (owner: bytes-repr)
- `63fd8bd9` builder: REDS.md for c396f7746991 (1 red) (owner: build-loop)
- `c396f774` PERF-CLIENT: rows 32, 36 and 37 measured after validation by step and the held node rows; rows 38 an
- `da318a3e` node rows held: the serving Host answers its own index reads from the rows it wrote
- `b88411fc` validation by step: a write is validated over the cells it wrote; residents wake on the head marker (owner: apps-hermes)
- `cf4889e2` builder: REDS.md for 1d11b2f5798e (1 red) (owner: build-loop)
- `1d11b2f5` builder: REDS.md for 338280802421 (1 red) (owner: build-loop)
- `6fa4a982` PERF-CLIENT: row 30 fixed; rows 36 (whole-state validation per write) and 37 (index rows per append)
- `33828080` policy sources: a source cell's record digest is hashed off its cached bytes, never re-encoded
- `d3a392f2` builder: REDS.md for 7670c1ef08c9 (1 red) (owner: build-loop)
- `7670c1ef` census: the member-command census in the repo, every row against the 10 ms budget
- `1fca8363` past reads off the log: a cell's bytes at a height are its last write there; no checkpoint on a memb (owner: apps-hermes, bytes-repr)
- `9b7a6af2` builder: REDS.md for e8e3bb8c83cc (0 red) (owner: build-loop)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.226 | 0.231 | 1.021 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 49.551 | 96.808 | 1.954 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.178 | 0.267 | 1.496 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 29.954 | 78.693 | 2.627 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.797 | 0.763 | 0.957 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 647.059 | 279.514 | 0.432 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-b2d88f3a/flatness.log | - | - | - | - | host-execution, store-retained |
