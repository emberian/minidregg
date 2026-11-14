# Reds (owned by the builder, rewritten whole each round)

Tip: `1dccfb8f32f8` (gate: the tour phase runs THIN after the JWF dry run). Round finished 2026-11-14T20:21Z.
green: `788dfb51fb5a`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-1dccfb8f`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| gate:j14-apps | j14-apps FAIL | not rerun | yes | apps-hermes | rc=1; /ci/j-1dccfb/journey.log |
| gate:composed:composed | composed composed fail | not rerun | yes | infra, member-side | scratch world: jworld FAIL start the relay did not answer a pinned enrollment-view within 30 s |

Suspect commits since green (`git log 788dfb51fb5a..1dccfb8f32f8`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `1dccfb8f` gate: the tour phase runs THIN after the JWF dry run
- `3cdf0c15` builder: REDS.md for 2ea52602020f (3 red) (owner: build-loop)
- `2ea52602` docs(effects): what binding `append` takes, and why JJOB1 and JJOB were not run
- `b95b35aa` effects: the two money consents are bound at codes 6 and 8; their hand arms are deleted (owner: apps-hermes, bytes-repr)
- `778bc98b` effects: the scalar ghost is refuted wherever a write is admitted (owner: bytes-repr)
- `bc17d3fd` journey JDISCLOSE: the refusal line has its own variable (owner: apps-hermes)
- `c40f190a` builder: REDS.md for 23f9aac22833 (3 red) (owner: build-loop)
- `23f9aac2` effects: scalar actions are bound at code 0; their hand arms are deleted (owner: apps-hermes, bytes-repr)
- `e3026acf` builder: REDS.md for ab8af8e598aa (2 red) (owner: build-loop)
- `ab8af8e5` builder: REDS.md for 26be70adf141 (4 red) (owner: build-loop)
- `60323ede` ratchet(bytes-repr): the ceiling is the measured 4961 (owner: bytes-repr)
- `26be70ad` scalar: `prepareStore`, the root-free core; `prepareCell` is its header and then that core
- `c7560674` builder: REDS.md for 1edbeb747d44 (3 red) (owner: build-loop)
- `1edbeb74` builder: REDS.md for 355ee3c73d2c (2 red) (owner: build-loop)
- `cf053068` effects: `ComputeTargetWorldArm` is proved (owner: bytes-repr)
- `992b545f` journeys: the delivered provision folder is owner-private in the inspect, affordances and law-leaf j (owner: apps-hermes)
- `355ee3c7` builder: REDS.md for 5dc18def4886 (3 red) (owner: build-loop)
- `b0ed7787` docs: the authority cell's physical layout, a design for the ordered append's growth (not built)
- `d1b9b8e9` agreement(native): a quorum of receipts answers the client; a restarted replica asks its peers' heig (owner: apps-hermes)
- `5dc18def` effects: world actions are bound at code 4; their hand arms are deleted (owner: apps-hermes, bytes-repr)
- `868293be` builder: REDS.md for e771d8a35eda (4 red) (owner: build-loop)
- `e771d8a3` builder: REDS.md for 1bc16ab14b1b (3 red) (owner: build-loop)
- `13434214` docs(agreement): the induction is proved; what is owed is the base case
- `58bfc62c` agreement: `RelativeFaithful` from the initial network, by induction on the run
- `b6589d00` agreement: one running replica against the trail of its run (`Side`), through `finish`, a delivery a
- `b4104e1b` agreement(kernel): `rebase` meets `Rebased`; a delivery need only be in the trail if `ingest` can re
- `1bc16ab1` effects: the kind definition revision is bound at code 5; its hand arms are deleted (owner: apps-hermes, bytes-repr)
- `b7b4d99f` builder: REDS.md for cd0501b8c090 (2 red) (owner: build-loop)
- `cd0501b8` builder: REDS.md for 3677dd8f2626 (3 red) (owner: build-loop)
- `97ebc52b` docs(agreement): what `rebase` meeting `Rebased` rests on
- `cd0438bb` agreement(kernel): `ghost_start`, and the native agreement document says what is proved and what rem
- `ba86bee7` agreement(kernel): moving the origin keeps a replica's side of the trail (`ghost_rebase`)
- `b900d90c` agreement(kernel): one `step` against the floor it started from, and the trail of a run of relative 
- `3677dd8f` effects: the member patch is the declaration's; thin consent reads it by one rule (owner: apps-hermes, bytes-repr)
- `9967213b` builder: REDS.md for 884450e985c8 (5 red) (owner: build-loop)
- `884450e9` builder: REDS.md for 16ff33ac3aa2 (3 red) (owner: build-loop)
- `62299c44` json: a target's payload has one reader; the agreement decoder's private grammar is deleted
- `16ff33ac` builder: REDS.md for f0ed42e2752a (2 red) (owner: build-loop)
- `643e3927` journey THIN: the kind-read rows start their own consent provider (owner: apps-hermes)
- `50b72670` thin consent: an observe-only read's observation header is derived as the Host derives it

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.255 | 0.244 | 0.956 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 54.188 | 122.515 | 2.261 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.221 | 0.241 | 1.091 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_wall_ms | 97.571 | 148.695 | 1.524 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.666 | 0.353 | 0.530 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 332.334 | 201.288 | 0.606 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-1dccfb8f/flatness.log | - | - | - | - | host-execution, store-retained |
