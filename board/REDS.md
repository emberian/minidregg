# Reds (owned by the builder, rewritten whole each round)

Tip: `6a8bdd25cab5` (Kernel.Job: the pole facts by `decide +kernel`, not elaborator `decide`). Round finished 2026-11-06T21:20Z.
green: `477bf8e9eb81`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-6a8bdd25`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 477bf8e9eb81..6a8bdd25cab5`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `6a8bdd25` Kernel.Job: the pole facts by `decide +kernel`, not elaborator `decide`
- `860388dd` builder: REDS.md for 7977ef501b89 (1 red) (owner: build-loop)
- `7977ef50` builder: REDS.md for 17c137325e35 (1 red) (owner: build-loop)
- `4e61731b` builder: REDS.md for dd70c487d4d0 (0 red) (owner: build-loop)
- `ba2d1a93` newparticipant-acceptance: a restored world template takes this caller's binary paths (owner: apps-hermes)
- `933271fe` builder: REDS.md for dd70c487d4d0 (1 red) (owner: build-loop)
- `35c2decf` builder: REDS.md for f7238232e614 (1 red) (owner: build-loop)
- `f7238232` Merge lane/tower256-prover-exe: compiled honest prover (ell 4/m 2, ell 8/m 3) and the first ContentC
- `10769766` tower256 docs: compiled prover counts, and the umbrella build peak (19.4 GB at one worker)
- `f54c4205` builder: REDS.md for 477bf8e9eb81 (0 red) (owner: build-loop)
- `3abdb6ef` tower256: ContentCert, the first instance, on the cube-Merkle commitment
- `927fbfcb` tower256: the honest succinct prover at any ell, m, compiled as lean_exe tower256-prover-run

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.241 | 0.280 | 1.163 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 86.613 | 138.613 | 1.600 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.228 | 0.290 | 1.272 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 61.995 | 164.558 | 2.654 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.645 | 0.888 | 1.377 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 311.671 | 395.608 | 1.269 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-6a8bdd25/flatness.log | - | - | - | - | host-execution, store-retained |
