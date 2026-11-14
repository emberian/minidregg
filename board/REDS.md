# Reds (owned by the builder, rewritten whole each round)

Tip: `a64bbd6e9e09` (effects: the hand-written content handler is deleted; its poles are over the derived one). Round finished 2026-11-14T13:42Z.
green: `788dfb51fb5a`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-a64bbd6e`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| ratchets | rc=1 see /home/hbox/lanes/integ/logs/ratchets.log | - | yes | suspects' owners | /home/hbox/lanes/integ/logs/ratchets.log |
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |
| gate:j14-apps | j14-apps FAIL | not rerun | yes | apps-hermes | rc=1; /ci/j-a64bbd/journey.log |

Suspect commits since green (`git log 788dfb51fb5a..a64bbd6e9e09`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

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
- `e5725f72` the concierge branch on the lane: one incoming reader, the till grant follows the week price, `notAc (owner: apps-hermes, build-loop)
- `120e113e` builder: REDS.md for a4472f3f65b2 (3 red) (owner: build-loop)
- `47d92a43` agreement(kernel)!: the cap on a member's share of a view record is the specification's, log format 
- `a4472f3f` docs: the effects revival's present state, and what the content migration takes
- `04fe80dd` laws: every joint participant the MUD laws trust is bound to its birth; `LawView.Turn` carries ident (owner: apps-hermes)
- `10b3ed1c` thin consent: a registered observation is displayed without a served view
- `4a8e4524` kernel: an unread payload tag is refused by name at the receiver; a registered refusal prints its de (owner: apps-hermes)
- `93f35b64` effects: `RegistryKeystone`, `RegistryAccepted` and `RegistryTeeth` are proved
- `9d6ae8aa` effects: the Hosted Revival lifecycle follows the engine (`select` and `pack` take the context, a re
- `daa0a798` fleet plan and submit on the light opening; the audit resumed at an anchor; the client pages op 180  (owner: apps-hermes)
- `400531af` agreement(kernel)!: the running replica keeps blocks relative to its committed height, log format 8
- `8400b3f7` agreement(verify): executed controls run compiled, the reachable witness is a short run

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.168 | 0.223 | 1.332 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 38.293 | 60.979 | 1.592 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_cpu_ms | 0.127 | 0.204 | 1.609 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 15.939 | 53.715 | 3.370 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.361 | 0.322 | 0.892 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 130.692 | 132.907 | 1.017 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-a64bbd6e/flatness.log | - | - | - | - | host-execution, store-retained |
