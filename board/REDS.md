# Reds (owned by the builder, rewritten whole each round)

Tip: `86ccb09c7e81` (builder: REDS.md for 7db8a63a850e (1 red)). Round finished 2026-11-14T08:07Z.
green: `788dfb51fb5a`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-86ccb09c`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| host | rc=1 ✖ [2156/2549] Building Kernel.ResourceBirthController (122s) | - | no | suspects' owners | /home/hbox/lanes/integ/logs/host.log |
| consent | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| rust | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| pack | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| umbrella-tree | did not run | - | no | build-loop | an earlier stage stopped the build |

Suspect commits since green (`git log 788dfb51fb5a..86ccb09c7e81`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

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
- `578fdbf3` jwell: a well refusal is read from the client's own report; the past-grant row expects `valueBound` (owner: apps-hermes)
- `6bc7ceeb` Fleet turn: the request's cost is the encoded command's length, like every other signed command
- `65530eba` fixtures: native runs re-recorded from the lane candidate 6ac47818be95 (accepted stale, doc-write st
- `35cca4bb` fleet-journey: a bounded delegated spend, at the bound, past it, and with no bound (owner: apps-hermes)
- `499e06c7` Activity payer: the grant bounds what the decided turn posts, for every turn kind
- `b5412a36` Value bound, strict: the resource-transaction path and every realm-well command (owner: apps-hermes)
- `e82efb87` Activity payer: a named `valueBound` refusal; the reject codec is edition v3 (owner: read-path)
- `95fd7574` Client: delegated account `transfer` grants carry a balance bound, or are refused early (owner: apps-hermes)
- `ab8a9ea8` Value bound, strict: a delegated capability must set the bound on every balance it debits (owner: apps-hermes)
- `ddc8ae89` FRIENDS: `delegate` with `--fields` and `--max-delta`, and what `MAX-COST` does not bound
- `252ac457` Kernel.ResourceMoneyValueBound: the two gross-debit footprints agree under `Covered` (stated)
- `b9b6a020` Activity payer: the payer's grant bounds the declared payment, before the run
- `54081815` Seat turn: the account grant bounds the turn's gross debit of the account it spends
- `f2225954` Purse refill, job fund and claim: the presented grant bounds the debit of the paying account
- `9aefe693` Fleet turn: the spend grant bounds the turn's gross debit of the paying account
- `28546122` Grain-backed birth: the same value bound on every source branch
- `40c68b05` Shell: `delegate` takes `--fields` and `--max-delta`, the value bound of a spend grant (owner: apps-hermes)
