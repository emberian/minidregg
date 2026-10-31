# Reds (owned by the builder, rewritten whole each round)

Tip: `4b750eb674ff` (builder: REDS.md for 9dc9c138cb32 (8 red)). Round finished 2026-10-31T23:21Z.
green: `83e926874e38`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-4b750eb6`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | no | build-loop | the umbrellas have not finished; this file is rewritten when they do |
| gate:flatness-submit | flatness-submit FAIL | not rerun | yes | host-execution, store-retained | rc=2; /ci/f-4b750e/submit.log |
| gate:flatness-get | flatness-get FAIL | not rerun | no | read-path | rc=1; /ci/f-4b750e/get.log |
| gate:flatness-run | flatness-run FAIL | not rerun | yes | host-execution, store-retained | exit=1; /home/hbox/lanes/integ/gate-4b750eb6/flatness.log |
| gate:composed:residents | composed residents fail | not rerun | yes | member-side, infra | fail: residents: WAITING root canonical provider custody publication absent: /ci/c-4b750e/ |
| gate:composed:restart | composed restart blocked | not rerun | yes | host-execution | blocked: prerequisite residents has not passed |

Suspect commits since green (`git log 83e926874e38..4b750eb674ff`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `4b750eb6` builder: REDS.md for 9dc9c138cb32 (8 red)
- `dbe87447` Merge remote-tracking branch 'origin/main' into seat/host-execution
- `7eca2241` board: host-execution row: rounds 3 and 4, persvati measuring, hbox tree (owner: host-execution)
- `82ef64a4` board: apps-hermes row: WBO certifier starves during the qualify; refusal decode fixed; referer ruli (owner: apps-hermes)
- `a1e69615` lifetime agent: op76's refusal names its reason instead of one fixed sentence (owner: apps-hermes)
- `2e85f567` Merge remote-tracking branch 'origin/main' into seat/host-execution
- `a1769318` host-execution: key status, the certify view and a birth's authored intent read the light served sta (owner: host-execution)
- `bbfa5e08` board: build-loop row: builder restart, fd-8 fix (owner: build-loop)
- `f1d2d3bb` builder: children never inherit builder.lock (fd 8) (owner: build-loop)
- `147b9825` lifetime agent: a controller's named refusal reaches the caller as a refusal (law 10) (owner: apps-hermes)
- `8bd59df6` board: build-loop row: hbox disk sweep, the build.lock fix, the gate edge at 3ddd90f (owner: build-loop)
- `3ef7de9a` builder: the umbrella tree never holds build.lock; a held lock defers the round; reds carry an owner (owner: build-loop)
- `3e9f365a` builder: REDS.md for 60f43c435020 (6 red)
- `24b05cd6` board/seats/read-path.md: a128a7497, 143caf2fc, 8cbe36d62 measured
- `60f43c43` board: apps-hermes row: Scrumblr qualifies; WBO tail-bound and Hummingbird referer header named (owner: apps-hermes)
- `eac80ad0` application attachment: a package that declares no roles attaches with roleId none or allAccess (owner: build-loop)
- `7de8305d` builder: REDS.md for 960da1d8d9a8 (6 red)
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
