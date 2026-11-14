# Reds (owned by the builder, rewritten whole each round)

Tip: `23f9aac22833` (effects: scalar actions are bound at code 0; their hand arms are deleted). Round finished 2026-11-14T19:11Z.
green: `788dfb51fb5a`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-23f9aac2`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |
| gate:j14-apps | j14-apps FAIL | not rerun | yes | apps-hermes | rc=1; /ci/j-23f9aa/journey.log |
| gate:composed:store-restart | composed store-restart fail | not rerun | no | host-execution | fail: store-restart:world: the relay did not answer a pinned enrollment-view within 30 s; |

Suspect commits since green (`git log 788dfb51fb5a..23f9aac22833`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

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
- `eb1181a5` journey THIN: a `kindRead` beside a write is signed under thin consent; a lied view of it is refused (owner: apps-hermes)
- `a7431e4c` thin consent: a command holding an observe-only read is no longer refused `slotShape`
- `e6d38997` journey THIN: the served view comes from the proxy; the step runs all its rows again (owner: apps-hermes)
- `f0ed42e2` builder: REDS.md for e9dc4c0be201 (3 red) (owner: build-loop)
- `5c29e9be` gates(generic-simplex): the gate builds its own Rust helpers, so every caller passes one argument
- `e9dc4c0b` builder: REDS.md for 1b5666369348 (3 red) (owner: build-loop)
- `83d19700` effects: the content read and the kind read are bound at codes 3 and 7; their hand arms are deleted (owner: apps-hermes)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.184 | 0.226 | 1.226 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 35.114 | 79.478 | 2.263 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.193 | 0.248 | 1.285 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 30.213 | 98.112 | 3.247 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.601 | 0.565 | 0.940 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 335.497 | 318.891 | 0.951 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-23f9aac2/flatness.log | - | - | - | - | host-execution, store-retained |
