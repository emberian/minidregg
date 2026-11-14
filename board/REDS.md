# Reds (owned by the builder, rewritten whole each round)

Tip: `26be70adf141` (scalar: `prepareStore`, the root-free core; `prepareCell` is its header and then that core). Round finished 2026-11-14T18:01Z.
green: `788dfb51fb5a`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-26be70ad`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| ratchets | rc=1 see /home/hbox/lanes/integ/logs/ratchets.log | - | yes | suspects' owners | /home/hbox/lanes/integ/logs/ratchets.log |
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |
| gate:j14-apps | j14-apps FAIL | not rerun | yes | apps-hermes | rc=1; /ci/j-26be70/journey.log |
| gate:composed:composed | composed composed fail | not rerun | no | infra, member-side | scratch world: jworld FAIL start the relay did not answer a pinned enrollment-view within 30 s |

Suspect commits since green (`git log 788dfb51fb5a..26be70adf141`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

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
- `eb1181a5` journey THIN: a `kindRead` beside a write is signed under thin consent; a lied view of it is refused (owner: apps-hermes)
- `a7431e4c` thin consent: a command holding an observe-only read is no longer refused `slotShape`
- `e6d38997` journey THIN: the served view comes from the proxy; the step runs all its rows again (owner: apps-hermes)
- `f0ed42e2` builder: REDS.md for e9dc4c0be201 (3 red) (owner: build-loop)
- `5c29e9be` gates(generic-simplex): the gate builds its own Rust helpers, so every caller passes one argument
- `e9dc4c0b` builder: REDS.md for 1b5666369348 (3 red) (owner: build-loop)
- `83d19700` effects: the content read and the kind read are bound at codes 3 and 7; their hand arms are deleted (owner: apps-hermes)
- `1b566636` agreement(native): four participants run end to end in the gate; tip validation, a running history d (owner: apps-hermes)
- `1936e8c1` builder: REDS.md for a64bbd6e9e09 (3 red) (owner: build-loop)
- `a64bbd6e` effects: the hand-written content handler is deleted; its poles are over the derived one
- `af2112b1` effects: `PrepareFactors` is one statement for every bound code, and proved

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.181 | 0.205 | 1.133 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 31.945 | 83.213 | 2.605 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_cpu_ms | 0.123 | 0.198 | 1.601 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 17.564 | 58.928 | 3.355 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.386 | 0.357 | 0.924 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 159.398 | 141.272 | 0.886 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-26be70ad/flatness.log | - | - | - | - | host-execution, store-retained |
