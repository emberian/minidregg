# Reds (owned by the builder, rewritten whole each round)

Tip: `1bc16ab14b1b` (effects: the kind definition revision is bound at code 5; its hand arms are deleted). Round finished 2026-11-14T16:33Z.
green: `788dfb51fb5a`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-1bc16ab1`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| ratchets | rc=1 see /home/hbox/lanes/integ/logs/ratchets.log | - | yes | suspects' owners | /home/hbox/lanes/integ/logs/ratchets.log |
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |
| gate:j14-apps | j14-apps FAIL | not rerun | yes | apps-hermes | rc=1; /ci/j-1bc16a/journey.log |

Suspect commits since green (`git log 788dfb51fb5a..1bc16ab14b1b`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

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
- `b07ea189` bytes: the index's logical map is `Theory.KeyedModel.Model`; the fleet page readers take the deploye
- `5a59d8ff` builder: REDS.md for 1a7fcf5b3429 (3 red) (owner: build-loop)
- `1a7fcf5b` builder: REDS.md for 87b77ef2c594 (3 red) (owner: build-loop)
- `27025da1` effects: a refusal's detail and thin consent's shown operation are `ByteArray`
- `c1dbafe3` the Host's held index trie follows every verified suffix: a certify no longer slows the session's la (owner: apps-hermes)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.189 | 0.204 | 1.079 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 32.486 | 76.829 | 2.365 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.136 | 0.195 | 1.432 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 16.879 | 58.207 | 3.448 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.680 | 0.959 | 1.410 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 270.701 | 301.108 | 1.112 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-1bc16ab1/flatness.log | - | - | - | - | host-execution, store-retained |
