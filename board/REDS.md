# Reds (owned by the builder, rewritten whole each round)

Tip: `f21eb46c1527` (Merge remote-tracking branch 'origin/dark-learning/displacement-bound-rebased' into merge-). Round finished 2026-11-06T17:10Z.
green: `8f2d63fab93f`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-f21eb46c`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 8f2d63fab93f..f21eb46c1527`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `f21eb46c` Merge remote-tracking branch 'origin/dark-learning/displacement-bound-rebased' into merge-2026-11-06
- `87625722` Merge remote-tracking branch 'origin/lane/binding-term' into merge-2026-11-06
- `48ab116a` Merge remote-tracking branch 'origin/lane/tower256-final-check' into merge-2026-11-06
- `13cdbde4` selvage-arklib bridge: mutual correlated agreement up to the Johnson radius, unconditional
- `fdde8214` Merge lane/arklib-ud-bridge (a3ca7bfa3) into the tower256 stack for the Johnson import
- `37e857e0` tower256: a round opening carries one path for its leaf pair (owner: apps-hermes, read-path)
- `f548263a` tower256: query seeds finish from the query prefix absorbed once
- `48a57e21` tower256: the succinct receipt codec, round-tripped on a real receipt (owner: read-path)
- `e224e19a` tower256: an accepting one-fold receipt, and one mutant per clause
- `dc9f2264` board: build-loop row: the lost-prompt close landed and verified
- `4e382908` builder: REDS.md for 8f2d63fab93f (0 red) (owner: build-loop)
- `567202f1` tower256: succinct additive-FRI acceptance decided by a Bool (check_iff)
- `1cccddc3` tower256: the concrete Merkle layer, computable over coordinates
- `68410097` AuditDisplacement: expected injected displacement before the first alarm is at most 2B/q
- `28824e21` selvage: binding terms for a fixed hash (SecureAt vacuity, collision-extractor cert_and)
- `c3bbbb9b` docs: Tower256 FRI work item, rate trade stated at equal message size
- `477dbf0e` docs: the Tower256 additive-FRI native prover work item, in counts
- `7015c0c0` tower256: additive FRI over a public statement of roots only (owner: apps-hermes)
- `4f04995b` tower256: the final-polynomial clause decided by a Bool over coordinates
- `049bfc45` selvage: computational binding games and budgets (Astra's binding-term patch)
- `a3ca7bfa` selvage-arklib bridge: hPG for RS discharged on the full unique-decoding radius

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.177 | 0.188 | 1.059 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 30.606 | 58.044 | 1.897 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.156 | 0.164 | 1.051 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 27.548 | 71.662 | 2.601 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.442 | 0.390 | 0.882 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 148.081 | 149.764 | 1.011 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-f21eb46c/flatness.log | - | - | - | - | host-execution, store-retained |
