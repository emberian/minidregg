# Reds (owned by the builder, rewritten whole each round)

Tip: `7db8a63a850e` (builder: REDS.md for e97b99da1fa7 (1 red)). Round finished 2026-11-14T08:00Z.
green: `788dfb51fb5a`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-7db8a63a`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log 788dfb51fb5a..7db8a63a850e`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

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
- `1d3d28d3` Birth: each source branch's capability bounds the birth's gross debit of its account (owner: apps-hermes)
- `4788bffc` Theory.CapabilityValueBound: the value bound a capability carries, stated once for every debit
- `e3226a3d` builder: REDS.md for 788dfb51fb5a (0 red) (owner: build-loop)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.208 | 0.219 | 1.056 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 40.321 | 101.145 | 2.509 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.218 | 0.251 | 1.150 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 21.619 | 81.342 | 3.763 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.723 | 0.736 | 1.018 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 213.607 | 271.111 | 1.269 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-7db8a63a/flatness.log | - | - | - | - | host-execution, store-retained |
