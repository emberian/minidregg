# Reds (owned by the builder, rewritten whole each round)

Tip: `ef2a21c94a3c` (builder: REDS.md for 78f347a6af51 (5 red)). Round finished 2026-10-31T23:24Z.
green: `83e926874e38`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-ef2a21c9`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| host | rc=1 see /home/hbox/lanes/integ/logs/host.log | - | yes | suspects' owners | /home/hbox/lanes/integ/logs/host.log |
| consent | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| rust | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| pack | did not run | - | yes | suspects' owners | an earlier stage stopped the build |
| umbrella-tree | did not run | - | yes | build-loop | an earlier stage stopped the build |

Suspect commits since green (`git log 83e926874e38..ef2a21c94a3c`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `ef2a21c9` builder: REDS.md for 78f347a6af51 (5 red)
- `a2363bbb` board: member-side row after 22cac1ee0
- `22cac1ee` client: one Host reply check names every outcome; the grain recovery test drives the codec session (owner: member-side)
- `78f347a6` builder: REDS.md for 4b750eb674ff (6 red)
- `142d5b99` board: apps-hermes row: referer sender and twins, image-free plan currency, new seat id (owner: apps-hermes)
- `7acbdd87` plans stay valid across a moved image: currency is compared modulo each signing plan's root and heig (owner: apps-hermes, member-side)
- `8bfffe59` referer: the senders reduce it to a same-origin path; every twin checks Lean's value rule (owner: apps-hermes, build-loop, member-side)
- `1b0f7cb2` board: apps-hermes row: certifier was a harness bug; payer-plan ruling and referer status (owner: apps-hermes)
- `7ac9217f` dispatch admission: `referer` is an ordinary header, admitted only as a same-origin path (statement 
- `15f9987f` builder: land its own fixture rerecord on main (root's ruling) (owner: build-loop)
- `842bc749` Merge remote-tracking branch 'origin/main' into seat/host-execution
- `8facc1e7` board: host-execution row: measured slices, law-17 cause, next order (owner: host-execution)
- `520e33d2` board: build-loop row: new seat a4141abe7297fdc4b; builder relaunched; akapug #4 and #5 landed (owner: build-loop)
- `64c34e22` fixtures: native runs re-recorded from candidate 9dc9c138cb32 (accepted stale, doc-write stale)
- `ae98da48` fleet-sign join: bind the selected socket before any key, enrollment or funding (PR #4) (owner: member-side)
- `d9f333db` capture test: hold the stdout lock so libtest's result lines stay out of the capture (owner: member-side)
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
