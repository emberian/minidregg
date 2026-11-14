# Reds (owned by the builder, rewritten whole each round)

Tip: `16ff33ac3aa2` (builder: REDS.md for f0ed42e2752a (2 red)). Round finished 2026-11-14T14:41Z.
green: `788dfb51fb5a`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-16ff33ac`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| ratchets | rc=1 see /home/hbox/lanes/integ/logs/ratchets.log | - | yes | suspects' owners | /home/hbox/lanes/integ/logs/ratchets.log |
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |
| gate:j14-apps | j14-apps FAIL | not rerun | yes | apps-hermes | rc=1; /ci/j-16ff33/journey.log |

Suspect commits since green (`git log 788dfb51fb5a..16ff33ac3aa2`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

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
- `e11c5f90` agreement(docs): the native adoption of the running replica, as one change in six parts
- `3cc1805a` agreement(kernel)!: a COMMIT is signed over the chain's length and running digest, log format 10 (owner: read-path)
- `ffced202` agreement(kernel): support above a commit extends it; the running replicas' statement is on the abst
- `9c34ae47` agreement: restore the twelve Simplex files that e5725f727 reverted
- `255d3e24` board: build-loop's builder section is the 2026-11-14 restore's present state
- `b21b685f` effects: content's declaration moves upstream of the registry, over the registry's context; `Effect.
- `dafce5e7` restore the registry lane's landed work that e5725f727 put back to its 9d6ae8aac text (owner: apps-hermes)
- `87b77ef2` builder: REDS.md for 120e113e9c73 (3 red) (owner: build-loop)
- `54dee83b` fixtures: native runs re-recorded from candidate a4472f3f65b2 (accepted stale, doc-write stale)
- `99e9e84c` journeys: what the first Host run of the light fleet line showed (owner: apps-hermes)
- `2d17fe4e` `mini audit --from ANCHOR`: the audit resumed at the anchor an accepting audit left (owner: apps-hermes)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.189 | 0.214 | 1.128 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 27.401 | 56.530 | 2.063 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.145 | 0.190 | 1.311 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 20.523 | 52.687 | 2.567 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.395 | 0.310 | 0.784 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 427.204 | 125.340 | 0.293 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-16ff33ac/flatness.log | - | - | - | - | host-execution, store-retained |
