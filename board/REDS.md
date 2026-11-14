# Reds (owned by the builder, rewritten whole each round)

Tip: `e771d8a35eda` (builder: REDS.md for 1bc16ab14b1b (3 red)). Round finished 2026-11-14T16:45Z.
green: `788dfb51fb5a`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-e771d8a3`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| ratchets | rc=1 see /home/hbox/lanes/integ/logs/ratchets.log | - | yes | suspects' owners | /home/hbox/lanes/integ/logs/ratchets.log |
| gate:j14-apps | j14-apps FAIL | not rerun | yes | apps-hermes | rc=1; /ci/j-e771d8/journey.log |
| gate:composed:documents | composed documents fail | not rerun | no | infra, member-side | fail: documents:protected: no stderr; see /ci-composed/c-e771d8/composed/state/evidence/01 |
| gate:composed:store-restart | composed store-restart blocked | not rerun | no | host-execution | blocked: prerequisite documents has not passed |

Suspect commits since green (`git log 788dfb51fb5a..e771d8a35eda`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

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
- `fb6c706d` kernel: `prepareTarget_packed`, what one target's preparation answers; `CommutingPrepare` is proved 
- `9ed4c1bd` builder: REDS.md for 45e65f2adcb8 (3 red) (owner: build-loop)
- `45e65f2a` effects: the wrong-role pole of the content binding, proved and executed
- `843478e7` journey K12T: the lone-read row reads the Host's decoded refusal (owner: apps-hermes)
- `0e0bcde8` effects: content is bound at code 1; `Payload.content`, `Reject.content` and the content hand arms a (owner: apps-hermes)
- `561ffb5a` builder: REDS.md for 8418ba7e13e9 (3 red) (owner: build-loop)
- `8418ba7e` agreement(native)!: the native layer runs the running replica; collision-freedom is about the chains (owner: apps-hermes, read-path)
- `c68a9457` fixtures: native runs re-recorded from candidate 197c649737ae (accepted stale, doc-write stale)
- `8418300a` builder: REDS.md for 197c649737ae (3 red) (owner: build-loop)
- `197c6497` index/trie-v3: a sequence item's position is folded into the leading bits of its path (owner: apps-hermes, read-path)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.270 | 0.259 | 0.959 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 58.690 | 122.326 | 2.084 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.295 | 0.331 | 1.122 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 39.752 | 93.928 | 2.363 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.555 | 0.487 | 0.878 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 162.747 | 180.400 | 1.108 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-e771d8a3/flatness.log | - | - | - | - | host-execution, store-retained |
