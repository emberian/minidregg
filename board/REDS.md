# Reds (owned by the builder, rewritten whole each round)

Tip: `9dc9c138cb32` (conversations: a channel id fits the Host's 64-character identifier shape). Round finished 2026-10-31T21:52Z.
green: `83e926874e38`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-9dc9c138`.

| stage | signature | reruns? | same place as last round? | detail |
|---|---|---|---|---|
| umbrella-tree | running | - | no | the umbrellas have not finished; this file is rewritten when they do |
| gate:flatness-submit | flatness-submit FAIL | not rerun | yes | rc=1; /ci/f-9dc9c1/submit.log |
| gate:flatness-run | flatness-run FAIL | not rerun | yes | exit=1; /home/hbox/lanes/integ/gate-9dc9c138/flatness.log |
| gate:composed | composed FAIL | not rerun | yes | rooms=pass; churn=pass; documents=pass; apps=pass; connector=pass; residents=fail: residents: REFUSED prepoll-filler-068 refused with status 3; retained 00194-prepoll-; restart=blocked: prerequisite residents has not passed; store-restart=fail: store-restart:world: mini-health: unhealthy — remaini |

Suspect commits since green (`git log 83e926874e38..9dc9c138cb32`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `9dc9c138` conversations: a channel id fits the Host's 64-character identifier shape
- `0edb4f26` board: privacy row, the opening circuit cost and the backend decision (astra round 18)
- `d807ddc9` board: privacy row, root format v2 and the custody shape landed; the authority rebuild routed
- `fbb425cc` Merge remote-tracking branch 'origin/main' into seat/host-execution
- `cf989744` Merge remote-tracking branch 'origin/main' into seat/host-execution
- `1aebf0ac` host-execution: the session's full image is brought to the head only when asked; a birth adopts its  (owner: build-loop, host-execution)
- `a4b37cd2` declarations: a route path loses one trailing slash and refuses an ambiguous one by name
- `cf368e4f` privacy: fixed-width inner digests and framed custody bytes; a public outer shape (owner: privacy, read-path)
- `3dcc5991` board: apps-hermes row: Scrumblr qualify reaches the call; the Host refuses the trailing-slash conve (owner: apps-hermes)
- `56344846` GrantPlan's constructor is public: no guarantee rests on who builds one (owner: apps-hermes)
- `997eba97` REDS.md: the j14-apps bootstrap red on 76511e768 (consent provider), fixed by 86c9dbddb
- `f53c9e07` docs/RETAINED-MODE.md: continuation: L0 measured, R1 landed, the refresh next (owner: store-retained)
- `83a22958` board: store-retained row: R1 landed (49cf4f2d2), next is the session refresh (owner: store-retained)
- `49cf4f2d` R1: op 5 reads the challenge op 4 planned over the same light opening instead of planning it again (owner: apps-hermes)
- `76d0fcd4` board: member-side row: 86c9dbddb confirmed end to end; measurement world
- `72c0ecf4` builder: REDS.md for d2d0ec8819b3 (8 red)
- `6b104c63` privacy: the sponge starts at the public midstate; the costs, build-checked
- `93023640` board/RULINGS: the hash choice
- `9155b21f` board: store-retained row: L0 before/after on grow2 (Host CPU story 8 1200 -> 700 ms, slope +610 ->  (owner: store-retained)
- `140bb771` board: build-loop row, builder rounds no longer wait for umbrellas (owner: build-loop)
- `eb4b7e7b` builder: the umbrellas no longer hold the next round (owner: build-loop)
- `aaec61fc` privacy: cSHAKE256 at a public input length as an Air system over ZMod 2
- `0a9c7e7c` board: privacy row, the Keccak permutation landed; substrate and next steps from astra round 17
- `81afc702` privacy: Keccak-f[1600] as an Air constraint system over ZMod 2
- `d4972329` native-loop, lane-tree: find pool.env from LANE_POOL_ROOT and /srv/pool too (owner: build-loop)
- `2fef8ab0` Merge remote-tracking branch 'origin/main' into seat/host-execution
- `dadd9a46` board: host-execution row: slice 2 landed; measurement blocked on consent red (owner: host-execution)
- `dfb7a9f8` board: build-loop row: the candidate-transfer rule; b9450147f copy restarted through it (owner: build-loop)
- `a97b13c4` scripts/pipeline/candidate-transfer: a candidate lands only whole and verified (owner: build-loop)
- `27f85e89` board/seats/read-path.md: member-side is ab7b4fe7fb687e0ca
- `5192781d` board: build-loop row: the gate runs on dregg-build2; pool package hashes; b9450147f copy (owner: build-loop)
- `1f27a71f` Merge remote-tracking branch 'origin/main' into seat/host-execution
- `95c09a2a` host-execution: KN2 2b slice 2: births are planned and submitted on the light opening (owner: host-execution)
- `cacb622d` board: member-side row: FORMAT (a) baseline from privacy
- `935ab295` board/REDS.md: the first dregg-build2 gate (76511e768): every row is the consent provider exit fixed
- `48b1f670` board: privacy seat, new agent id a7bf41b0d8bb24813; FORMAT (a) timing with member-side
- `b14e9a00` board: privacy row, the bounded shape done, the circuit codec next
- `4038d369` privacy: the opening relation is bounded in shape (owner: privacy)
- `971b5889` board: privacy seat row after the 98-byte leaves and FORMAT (a)
- `85f5affe` board: member-side row: FORMAT (a) landed (f28cd8457)
