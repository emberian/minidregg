# Reds (owned by the builder, rewritten whole each round)

Tip: `960da1d8d9a8` (builder: REDS.md for 9dc9c138cb32 (4 red)). Round finished 2026-10-31T21:53Z.
green: `83e926874e38`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-960da1d8`.

| stage | signature | reruns? | same place as last round? | detail |
|---|---|---|---|---|
| rust-check | did not run | - | no | an earlier stage stopped the build |
| host | did not run | - | no | an earlier stage stopped the build |
| consent | did not run | - | no | an earlier stage stopped the build |
| rust | did not run | - | no | an earlier stage stopped the build |
| pack | did not run | - | no | an earlier stage stopped the build |
| umbrella-tree | did not run | - | no | an earlier stage stopped the build |

Suspect commits since green (`git log 83e926874e38..960da1d8d9a8`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `960da1d8` builder: REDS.md for 9dc9c138cb32 (4 red)
- `4c6c3676` board: privacy row, the held authority cell landed (store-retained)
- `c3a46c03` board: store-retained row: R6(i) held authority cell landed (bdfa9428c, c3a28038a); boxes are hbox t (owner: store-retained)
- `c3a28038` R6(i): the held-cell teeth and satisfiable lemmas reduce the match before the dite rewrite
- `bdfa9428` R6(i) authority: a light write hands the session its authority post-cell; adopt takes it without a d (owner: host-execution)
- `e46759f4` conversation paths: the controller's reserve projection admits the trailing slash too (owner: apps-hermes)
- `1c670cee` conversation paths: the Host carries the app's own endpoint byte-exact, one trailing slash included  (owner: apps-hermes, read-path)
- `cc93292e` board: apps-hermes row: trailing-slash and channel-id fixes landed; Scrumblr now fails in the app's  (owner: apps-hermes)
- `acfab457` board: member-side row: the measurement overlay carries f28cd8457
- `e2d7800e` board: privacy row, builds back on hbox; bb2 t4 released
- `ca0fc018` board: member-side row: boxes after build-loop moved builds back to hbox
- `64ebbb5c` board: infra seat, back on hbox
- `f39379b6` build-loop: minidregg builds on hbox again (obend has dregg-build2); the builder is live there (owner: build-loop)
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
