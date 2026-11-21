# Reds (owned by the builder, rewritten whole each round)

Tip: `a6466ed72287` (builder: REDS.md for 0f9749114269 (7 red)). Round finished 2026-11-21T14:03Z.
green: `053906870674`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-a6466ed7`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| ratchets | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| rust-check | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| host | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| consent | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| rust | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| pack | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| umbrella-tree | did not run | - | yes | build-loop | an earlier stage stopped the build |

Suspect commits since green (`git log 053906870674..a6466ed72287`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

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
- `5d607d21` builder: REDS.md for b8286f686194 (1 red) (owner: build-loop)
- `b8286f68` docs(append-growth): the store phase by part before and after; what an append still pays; the order 
- `c9fa8ec7` append: the Store's node insert prepared once, the NODES file written as a byte array, the holder a 
- `bbd08400` builder: REDS.md for 07eeb91a239d (1 red) (owner: build-loop)
- `07eeb91a` holder: the invariant of the held index rows, stated and proved; the hand-over only for an installed
- `ef8e5a8c` receiver: an append hands the index rows it wrote to the holder; the holder is keyed by Store root
- `39689195` builder: REDS.md for 9ac0425a6f14 (1 red) (owner: build-loop)
- `9ac0425a` ratchet(bytes-repr): 5056, the index rows compiled twins repeat existing list types (owner: bytes-repr)
- `346b2d1a` docs(append-growth): the index after its compiled half; what the root still costs; the holder hand-o
- `539bc23c` index: the journal index's compiled half, by `@[csimp]` equalities to the stated definitions
- `61a6d4ff` builder: REDS.md for f264ccfdc2bc (1 red) (owner: build-loop)
- `f264ccfd` ratchet(bytes-repr): 5033, one binder of the private index node type (owner: bytes-repr)
- `3fbeca33` docs(append-growth): the product row as its own section; what compiled outside the umbrella; what is
