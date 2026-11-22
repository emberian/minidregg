# Reds (owned by the builder, rewritten whole each round)

Tip: `13a1fe191b73` (feat(selvage,assurance,compiler): add GoldilocksDregg180Bridge, StreamingGdnCarryIvc, and ). Round finished 2026-11-22T18:22Z.
green: `053906870674`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-13a1fe19`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 053906870674..13a1fe191b73`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `13a1fe19` feat(selvage,assurance,compiler): add GoldilocksDregg180Bridge, StreamingGdnCarryIvc, and PocketFpga
- `83edecc7` feat(assurance,prover): add SensoryRoiZeroKnowledge and Wave-9 wearable SHE engines (wetware duress,
- `c283ffae` theory & assurance: add WetwareSafetyAndDuress (BT.1702 flicker/stego scrubber & duress vault) and W
- `1ca93a7b` compiler & prover: finalize Tower256AlgebraicCert [ZCF23] BaseFold conformance vectors & zero-leakag
- `5b6b7a90` theory: add ExactKktClearingCert (quarried fhIR-0 FHSDD001 & FHQPB001 exact SDD-to-PSD, primal-dual 
- `1cb756f8` theory: add Tower256EndianBridge (G4 32B LE vs BE Fan-Paar GF(2^256) ring/field/Frobenius wire isomo
- `b54b6bfe` assurance & prover: add PerSlotKeyConfinement (G7 / CAP-21 / L8 / F4 per-slot X25519+ML-KEM-768 conf
- `ffd55433` theory & prover: add PqSelectiveBiscuit (D8 / CAP-01,10,12 root-isolated PQ ZkBiscuit selective-disc
- `7fc423c6` assurance: add LightClientAndViewLens (25-variant ViewNode Frustum non-interference & S11 Electra/Co
- `a6ce8854` theory: add Char2Degree4SumcheckHvzk (G8/#125 char-2 degree-4 sumcheck & BaseFold round-polynomial H
- `f8c905fb` umbrellas & testdata: wire Wave-7A AFP/zkML/WHIR/Tower256AlgebraicCert modules into Theory, Selvage,
- `a869a8e7` checkpoint
- `ac619c1a` builder: REDS.md for a6466ed72287 (7 red) (owner: build-loop)
- `a6466ed7` builder: REDS.md for 0f9749114269 (7 red) (owner: build-loop)
- `0ce6d9cf` checkpiont
- `0f974911` Merge origin/main into main (integrating zkml, vfhe & selvage certificate waves)
- `c83b3193` theory, compiler & prover: add VerifiedAstTransducer, PolicyAstTransducerEmit, and private-witness T
- `2bc33e18` selvage & prover: add ContentCertificate/CertificateComposition (P1-P8, W4) and native Gruen EinSumc
- `99dfbf0e` vfhe & zkml: add BfvHoistedRescale (Hole B), ZkmlDeltaNet WY, and ZkmlGruenSumcheck
- `d58330d9` zkml: add EinSumcheck 6-block contraction metatheory and cubic sumcheck assurance
- `5c8ce467` builder: REDS.md for 2eb32b5103d4 (1 red) (owner: build-loop)
- `2eb32b51` Record integrated custody broker-test and Simplex takeover evidence
- `cf404cbc` Integrate generalized Simplex safety and executable admission guards
- `3f2968ea` Integrate child-isolated broker audit-limit test
- `d5f11dfa` Integrate delivery custody takeover and stable binding identity
- `ab2023bc` Make delivery identity independent of JSON map features
- `00fecf31` Pin generalized Simplex wrappers and clean public scope notes
- `95c41f8a` Harden broker audit-limit child isolation
- `9433fecb` kernel(simplex): guard wellFormed against f=0 at n>1, prove churnSafe_iff, and document crash resili
- `735e13a7` mini-keys: the audit-unavailable row sets its file-size limit in a child copy of the test binary
- `daa496d2` mini-sdk: a delivery declined by its destination is terminal unless observed completion supersedes i (owner: apps-hermes)
- `4d043ab0` check-rust-tests: the sdk-custody row names only tests that exist
- `d341eaf5` docs: generalize evidence for the n >= 3f+1 oracle slice (task/12332)
- `a5d81d7c` kernel(simplex): wellFormed_at_legacy: at n = 3f+1 the widened admission computes the old one
- `c2b145d8` kernel(simplex): ghost_rebase reads the commit through the _at lemmas
- `3f8d2c29` kernel(simplex): admit any roster n >= 3f+1; refinement records the executable guards
- `0a3dd1ea` docs: GENERALIZE.md for the upstream port, with its Fabric jobs
- `960f9637` docs: GENERALIZE.md maps the n >= 3f+1 safety generalization and its boundary
- `19648384` kernel(simplex): receiver _at theorems take the caller's chain, as upstream's verifiedCommit_attribu
- `c5ae228a` kernel(simplex): generic simplex safety for any roster n >= 3f+1 via explicit thresholds

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.173 | 0.195 | 1.131 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 26.626 | 60.321 | 2.266 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.139 | 0.167 | 1.207 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 14.522 | 57.751 | 3.977 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.415 | 0.315 | 0.760 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 304.598 | 147.602 | 0.485 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-13a1fe19/flatness.log | - | - | - | - | host-execution, store-retained |
