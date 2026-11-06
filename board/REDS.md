# Reds (owned by the builder, rewritten whole each round)

Tip: `ec33fdd83c04` (tower256: register the additive-FRI prover as native work 9104). Round finished 2026-11-06T18:08Z.
green: `8f2d63fab93f`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-ec33fdd8`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 8f2d63fab93f..ec33fdd83c04`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `ec33fdd8` tower256: register the additive-FRI prover as native work 9104
- `f1a62ef7` tower256: one path per pair checked, and no next-level leaf on the wire (owner: read-path)
- `f23a361f` builder: REDS.md for f21eb46c1527 (1 red) (owner: build-loop)
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
| flatness-submit | PASS | submit_cpu_ms | 0.196 | 0.211 | 1.074 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | submit_wall_ms | 53.383 | 82.626 | 1.548 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.182 | 0.212 | 1.164 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 35.885 | 105.964 | 2.953 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.581 | 0.313 | 0.538 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 312.974 | 204.240 | 0.653 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-ec33fdd8/flatness.log | - | - | - | - | host-execution, store-retained |
