# Reds (owned by the builder, rewritten whole each round)

Tip: `d2d0ec8819b3` (builder: REDS.md for ffa7a77f2182 (8 red)). Round finished 2026-10-31T20:31Z.
green: `83e926874e38`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-d2d0ec88`.

| stage | signature | reruns? | same place as last round? | detail |
|---|---|---|---|---|
| umbrella-tree | rc=1 see /home/hbox/lanes/integ/logs/umbrella-tree.log | - | yes | /home/hbox/lanes/integ/logs/umbrella-tree.log |
| rerecord | rc=1 FAILED create-notes rc=1: workspace continuity: legacy; initialize with workspace --action continuity-init --name REF | - | yes | /home/hbox/lanes/integ/logs/rerecord.log |
| umbrella | RED TokenCensus | - | yes | /home/hbox/lanes/integ/logs/umbrella-tree.log |
| gate:flatness-submit | flatness-submit FAIL | not rerun | yes | rc=2; /ci/f-d2d0ec/submit.log |
| gate:flatness-get | flatness-get FAIL | not rerun | yes | rc=1; /ci/f-d2d0ec/get.log |
| gate:flatness-run | flatness-run FAIL | not rerun | yes | exit=1; /home/hbox/lanes/integ/gate-d2d0ec88/flatness.log |
| gate:j14-apps | j14-apps FAIL | not rerun | yes | rc=1; /ci/j-d2d0ec/journey.log |
| gate:composed | composed FAIL | not rerun | yes | scratch world: jworld: port 22640 in use |

Suspect commits since green (`git log 83e926874e38..d2d0ec8819b3`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `d2d0ec88` builder: REDS.md for ffa7a77f2182 (8 red)
- `6d73b30b` board/seats/read-path.md: ops 4 and 5 on the light opening
- `85cf77fb` board: build-loop row: seam 1 landed (365 -> 4 modules), hot-swap command written (owner: build-loop)
- `8cbe36d6` Ops 4 and 5 on the light opening: a current read no longer opens the full image
- `f2002e58` Merge lane/seam1-epoch-main 1d4f01724: seam 1, the codec census behind a private import
- `0c324923` composed-inputs, world-down: custodian mode for a user-namespaced composed container (CUSTODIAN_SOCK (owner: build-loop, infra)
- `eb705710` board: infra seat: Stage A done
- `f6d32382` lane-tree: parse the whole script before running it (owner: build-loop)
- `390a2777` board: member-side row rewritten after 76511e768
- `76511e76` authority projection: the revoked set and the parents are read from the cell, never enumerated (owner: apps-hermes, host-execution)
- `d5414ef3` board: host-execution row: ops 4/5 go to read-path (owner: host-execution)
- `2bcdc224` integ-build: prime the cargo cache before the --offline stages (owner: build-loop)
- `21cbfc7d` privacy: fixed-size 98-byte leaves; the opening over the path-keyed image (owner: privacy)
- `dcc62459` board: host-execution row: slice 1 landed (owner: host-execution)
- `4fb01226` host-execution: KN2 2b slice 1: the Host session opens the light opening only
- `05e384e6` board: infra seat: dregg-infra homes (anchor canonical, bb2 second copy), bb2 as build box
- `42d90df3` lane-tree warm copies .lake/native; the builder runs integ-build from the tip it builds (owner: build-loop)
- `ba8577ef` board: apps-hermes row carries the new agent id (owner: apps-hermes)
- `743771f1` board: apps-hermes row: op66 shape diagnostic landed (owner: apps-hermes)
- `90fba62e` launch BEGIN authoring: the shape refusal names the conjunct that failed (owner: host-execution)
- `b9f1fa98` dregg-build2 is the build box: the builder build in the repo (integ-build), row rewritten (owner: build-loop)
- `17774b48` board: apps-hermes row: packages ready, op66 shape conjuncts, live runs blocked on a world (owner: apps-hermes)
- `23ad753b` hummingbird: a repackage with apiPath "/" (recipe, new app and package id); the declaration pins it
- `ffa7a77f` board: apps-hermes row (owner: apps-hermes)
- `07c8e05a` board/seats/read-path.md: a128a7497 landed, persvati worktree
- `a128a749` Signature admission: the controller is handed its state and registry, not their encodings (owner: apps-hermes, read-path)
- `a38ed5c6` board/seats/read-path.md: the verifyNative batch, written
- `4e76674a` store codec: pin chainAfter_iff's axioms; member-side row rewritten (owner: read-path)
- `ef645f1b` board/seats/read-path.md: host-execution is a24974e84d3c540d1
- `e1d55520` board/REDS.md: green is 83e926874 (batch 4); the suspect range was the tip~20
- `3890c94a` board/seats/read-path.md: where the unchecked registryDigest patch is
- `e63d22b8` board/seats/read-path.md: what is in flight while hbox is down
- `96087dd7` board: host-execution row: 2b slices 1 and 2 in flight (owner: host-execution)
- `43995c7f` store codec: the payload's order check encodes each address once (owner: read-path)
- `6b36bba9` board: store-retained row: hbox down, measurement moves to persvati (owner: store-retained)
- `f7da3dd5` board/seats/read-path.md: the op 5 profile and 143caf2fc
- `08340bac` j14-apps qualify skips the Davros probe; a failed foreground application API call logs why it ended  (owner: apps-hermes, member-side)
- `2c3ce1c9` board: store-retained row: L0 landed (802ba8c69), numbers, next (owner: store-retained)
- `03c8af2c` docs/RETAINED-MODE.md: continuation after L0 landed (802ba8c69), inventory rows R6/R7, client refs i (owner: store-retained)
- `143caf2f` op 5: each grant's selection, request and header worked out once per read (owner: apps-hermes)
