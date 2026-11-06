# Reds (owned by the builder, rewritten whole each round)

Tip: `f7238232e614` (Merge lane/tower256-prover-exe: compiled honest prover (ell 4/m 2, ell 8/m 3) and the firs). Round finished 2026-11-06T19:38Z.
green: `477bf8e9eb81`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-f7238232`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 477bf8e9eb81..f7238232e614`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `f7238232` Merge lane/tower256-prover-exe: compiled honest prover (ell 4/m 2, ell 8/m 3) and the first ContentC
- `10769766` tower256 docs: compiled prover counts, and the umbrella build peak (19.4 GB at one worker)
- `f54c4205` builder: REDS.md for 477bf8e9eb81 (0 red) (owner: build-loop)
- `3abdb6ef` tower256: ContentCert, the first instance, on the cube-Merkle commitment
- `927fbfcb` tower256: the honest succinct prover at any ell, m, compiled as lean_exe tower256-prover-run

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.155 | 0.164 | 1.055 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 29.242 | 63.532 | 2.173 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.134 | 0.155 | 1.153 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 22.427 | 86.608 | 3.862 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.291 | 0.322 | 1.107 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 120.404 | 194.438 | 1.615 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-f7238232/flatness.log | - | - | - | - | host-execution, store-retained |
