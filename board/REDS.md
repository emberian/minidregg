# Reds (owned by the builder, rewritten whole each round)

Tip: `8bbfc0798d57` (door: a submission lands on the status page, which names what is queued and refreshes itse). Round finished 2026-11-06T18:42Z.
green: `8f2d63fab93f`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-8bbfc079`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| gate:composed:documents | composed documents fail | not rerun | no | infra, member-side | fail: documents:protected: no stderr; see /ci-composed/c-8bbfc0/composed/state/evidence/01 |
| gate:composed:store-restart | composed store-restart blocked | not rerun | no | host-execution | blocked: prerequisite documents has not passed |

Suspect commits since green (`git log 8f2d63fab93f..8bbfc0798d57`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `8bbfc079` door: a submission lands on the status page, which names what is queued and refreshes itself; the pa
- `fae6aba9` builder: REDS.md for ec33fdd83c04 (1 red) (owner: build-loop)
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
| flatness-submit | PASS | submit_cpu_ms | 0.188 | 0.183 | 0.972 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 38.875 | 81.587 | 2.099 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.143 | 0.186 | 1.299 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 29.278 | 104.037 | 3.553 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.328 | 0.298 | 0.906 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 409.986 | 129.522 | 0.316 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-8bbfc079/flatness.log | - | - | - | - | host-execution, store-retained |
