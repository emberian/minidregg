# Reds (owned by the builder, rewritten whole each round)

Tip: `ae74dca4ec2d` (builder: REDS.md for 69c7afc23d4a (1 red)). Round finished 2026-11-06T22:08Z.
green: `477bf8e9eb81`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-ae74dca4`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 477bf8e9eb81..ae74dca4ec2d`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `ae74dca4` builder: REDS.md for 69c7afc23d4a (1 red) (owner: build-loop)
- `04296696` Merge origin/main into the green unlearning merge
- `f77841e1` iter-check full: one shared packages directory per manifest key per box
- `13bde99c` iter-check full: the run records its own PID, and a cold box clone starts from the box's snapshot
- `69c7afc2` builder: REDS.md for f6e5069b2126 (3 red) (owner: build-loop)
- `129d828c` iter-check: a 30 GB disk floor, and memory measured as MemAvailable (+ ZFS ARC)
- `fa1e93c6` DEVELOPING.md, Makefile, scripts/iter-check: the lane loop without cold rebuilds
- `eceedcf5` Theory.NockCost.Summaries: forge's eleven concrete facts in one compiled evaluation
- `f502c83c` Theory.NockCost: forge's seven concrete facts in one compiled evaluation
- `8f77d90b` HostTeethProofs: the one cSHAKE fact is checked by compiled evaluation
- `3fd5c0ba` Kernel.ObjectLaw: the hash-bearing sample law is checked by compiled evaluation
- `f6e5069b` builder: REDS.md for 6a8bdd25cab5 (1 red) (owner: build-loop)
- `dcf53d2d` Merge lane/tower256-prover-exe: ContentCert gaps closed, work 9104 native kernel, lighter Tower256 m
- `6a8bdd25` Kernel.Job: the pole facts by `decide +kernel`, not elaborator `decide`
- `6fd5d4f6` tower256: interpreted teeth leave the umbrella; FinalPolynomialCheck stops kernel-reducing a product (owner: read-path)
- `860388dd` builder: REDS.md for 7977ef501b89 (1 red) (owner: build-loop)
- `0d427ece` Merge lane/unlearning-certs: exact-deletion and SGD unlearning certificates (initiative 16)
- `d88a8fb3` tower256: the native kernel for work 9104, pinned byte for byte to the Lean prover
- `7931bf1c` Assurance.Unlearning: Codex round 2 fixes (nonzero denominators, influence witness)
- `7977ef50` builder: REDS.md for 17c137325e35 (1 red) (owner: build-loop)
- `4e61731b` builder: REDS.md for dd70c487d4d0 (0 red) (owner: build-loop)
- `6d0b249e` tower256 ContentCert: nonempty records, and the table's verdict is breadstuffs' DfaAccepts
- `4c9d36b0` Assurance.Unlearning{Exact,Sgd}: exact deletion certificates and the SGD bound
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
| flatness-submit | PASS | submit_cpu_ms | 0.258 | 0.248 | 0.961 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 66.843 | 122.459 | 1.832 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.288 | 0.258 | 0.895 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 46.493 | 136.817 | 2.943 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.416 | 0.474 | 1.139 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 320.317 | 299.534 | 0.935 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-ae74dca4/flatness.log | - | - | - | - | host-execution, store-retained |
