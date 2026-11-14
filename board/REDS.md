# Reds (owned by the builder, rewritten whole each round)

Tip: `87b77ef2c594` (builder: REDS.md for 120e113e9c73 (3 red)). Round finished 2026-11-14T10:31Z.
green: `788dfb51fb5a`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-87b77ef2`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| ratchets | rc=1 see /home/hbox/lanes/integ/logs/ratchets.log | - | yes | suspects' owners | /home/hbox/lanes/integ/logs/ratchets.log |
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |
| gate:j14-apps | j14-apps FAIL | not rerun | yes | apps-hermes | rc=1; /ci/j-87b77e/journey.log |

Suspect commits since green (`git log 788dfb51fb5a..87b77ef2c594`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

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
- `6407fcd6` builder: REDS.md for 86ccb09c7e81 (5 red) (owner: build-loop)
- `86ccb09c` builder: REDS.md for 7db8a63a850e (1 red) (owner: build-loop)
- `9c761504` fleet reads off the journal index: exactness proved, the page read with a horizon, op 180 pages by p (owner: apps-hermes)
- `631425b9` journal index: sequence families 3 and 4, fleet head/incoming/poll/lookup on the light opening (inde (owner: read-path)
- `dc6d032a` wip index family 2 (owner: read-path)
- `e65459d9` `room new --concierge` takes `--refund-limit`; j17 names one (owner: apps-hermes)
- `751b07ff` demo-seed: remove `public-read-max-cost`, renamed `public-read-request-bytes`
- `7745da9c` Activity: a migration's fee is bounded at the gate; a turn's end debits only held seats
- `d31ba6ca` The resource-transaction money leg uses the one gross-debit footprint (owner: apps-hermes)
- `4e81a7ca` One birth branch core: `Kernel.BranchAdmission` (owner: apps-hermes)
- `c8e19e50` `AccountGrant.Held` and `AccountGrant.RootOwner`: the pay assignment is the owner's alone
- `962efddf` `Scope.maxCost` is `Scope.perRequestBytes` (owner: apps-hermes, bytes-repr, read-path)
- `a3987eba` Request cost is an encoded length everywhere: birth, Book effect and resource-transaction legs (owner: apps-hermes)
- `9372f1f6` agreement(kernel)!: idle timer and view window, log format 7 (owner: read-path)
- `aba2c4d7` agreement(verify): the jump-starvation control runs against the current step again
- `9f7f404a` agreement(kernel)!: the checked set is retained and a committed payload leaves the offers
- `7db8a63a` builder: REDS.md for e97b99da1fa7 (1 red) (owner: build-loop)
- `9be139da` kernel: `Payload.registered`, the open payload constructor; the cited read is one declaration and it (owner: apps-hermes)
- `e97b99da` builder: REDS.md for aac9eba601a1 (1 red) (owner: build-loop)
- `787333fc` laws: the sheet law requires its cited rooms' birth; a verdict law and a land that cites it; the hea (owner: apps-hermes, read-path)
- `9b711740` kernel: `fieldRead`, an observe-only read of a declared cell bound by value; a joint participant's i (owner: apps-hermes)
- `881ceb8e` kernel: a declared cell's law state is built for the slots the law reads; a cited footprint refuses  (owner: apps-hermes)
- `aac9eba6` agreement(kernel)!: erasable commit floor (`forget`, `liveStep`, floor evidence relay), log format 6 (owner: read-path)
- `77539c37` builder: REDS.md for 578fdbf35ab3 (1 red) (owner: build-loop)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.208 | 0.237 | 1.136 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 38.897 | 84.844 | 2.181 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.167 | 0.235 | 1.406 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 23.688 | 64.811 | 2.736 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.502 | 0.304 | 0.606 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 471.578 | 136.604 | 0.290 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-87b77ef2/flatness.log | - | - | - | - | host-execution, store-retained |
