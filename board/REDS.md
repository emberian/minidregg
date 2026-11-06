# Reds (owned by the builder, rewritten whole each round)

Tip: `f6e5069b2126` (builder: REDS.md for 6a8bdd25cab5 (1 red)). Round finished 2026-11-06T21:36Z.
green: `477bf8e9eb81`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-f6e5069b`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |
| gate:composed:residents | composed residents fail | not rerun | no | member-side, infra | fail: residents: REFUSED check failed: restart drains the old exact reply and then every o |
| gate:composed:restart | composed restart blocked | not rerun | no | host-execution | blocked: prerequisite residents has not passed |

Suspect commits since green (`git log 477bf8e9eb81..f6e5069b2126`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `f6e5069b` builder: REDS.md for 6a8bdd25cab5 (1 red) (owner: build-loop)
- `dcf53d2d` Merge lane/tower256-prover-exe: ContentCert gaps closed, work 9104 native kernel, lighter Tower256 m
- `6a8bdd25` Kernel.Job: the pole facts by `decide +kernel`, not elaborator `decide`
- `6fd5d4f6` tower256: interpreted teeth leave the umbrella; FinalPolynomialCheck stops kernel-reducing a product (owner: read-path)
- `860388dd` builder: REDS.md for 7977ef501b89 (1 red) (owner: build-loop)
- `d88a8fb3` tower256: the native kernel for work 9104, pinned byte for byte to the Lean prover
- `7977ef50` builder: REDS.md for 17c137325e35 (1 red) (owner: build-loop)
- `4e61731b` builder: REDS.md for dd70c487d4d0 (0 red) (owner: build-loop)
- `6d0b249e` tower256 ContentCert: nonempty records, and the table's verdict is breadstuffs' DfaAccepts
- `ba2d1a93` newparticipant-acceptance: a restored world template takes this caller's binary paths (owner: apps-hermes)
- `933271fe` builder: REDS.md for dd70c487d4d0 (1 red) (owner: build-loop)
- `35c2decf` builder: REDS.md for f7238232e614 (1 red) (owner: build-loop)
- `152996d0` tower256 ContentCert: one automaton root covers state count, initial state, accepting set
- `f7238232` Merge lane/tower256-prover-exe: compiled honest prover (ell 4/m 2, ell 8/m 3) and the first ContentC
- `10769766` tower256 docs: compiled prover counts, and the umbrella build peak (19.4 GB at one worker)
- `f54c4205` builder: REDS.md for 477bf8e9eb81 (0 red) (owner: build-loop)
- `3abdb6ef` tower256: ContentCert, the first instance, on the cube-Merkle commitment
- `927fbfcb` tower256: the honest succinct prover at any ell, m, compiled as lean_exe tower256-prover-run

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.265 | 0.265 | 1.000 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 68.672 | 153.021 | 2.228 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.265 | 0.308 | 1.163 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 48.233 | 167.237 | 3.467 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.755 | 0.432 | 0.572 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 316.742 | 209.955 | 0.663 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-f6e5069b/flatness.log | - | - | - | - | host-execution, store-retained |
