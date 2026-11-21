# Reds (owned by the builder, rewritten whole each round)

Tip: `2eb32b5103d4` (Record integrated custody broker-test and Simplex takeover evidence). Round finished 2026-11-16T07:09Z.
green: `053906870674`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-2eb32b51`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 053906870674..2eb32b5103d4`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

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
- `362c2f8d` docs: what an append costs as history grows, measured and attributed
- `c0f71943` directory: `used` is the set's characteristic function; the private index evaluates a path once (owner: apps-hermes, read-path)
- `bd134ef4` receiver: `MINI_STORE_PHASES=1` prints where one durable append spends its time
- `c6081864` builder: REDS.md for 74d6535141c7 (1 red) (owner: build-loop)
- `74d65351` ratchet(bytes-repr): the ceiling is the measured count after the authority layout (owner: bytes-repr)
- `6b6c219d` docs(authority): the sixteen authority-writing journeys on this head
- `f21515be` docs(authority): the trie cost found and cut, the step and hand-off numbers, what ran on this head; 
- `2a95c410` fixtures: the accepted Objective call and the document write are re-recorded on the hashed-bits-firs

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.162 | 0.213 | 1.315 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 23.597 | 92.682 | 3.928 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.145 | 0.222 | 1.533 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 15.799 | 80.977 | 5.125 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.488 | 0.307 | 0.629 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 619.797 | 136.375 | 0.220 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-2eb32b51/flatness.log | - | - | - | - | host-execution, store-retained |
