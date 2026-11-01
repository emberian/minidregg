# Reds (owned by the builder, rewritten whole each round)

Tip: `d5e858b2222b` (builder: REDS.md for 467e698ef56f (5 red)). Round finished 2026-11-01T02:12Z.
green: `83e926874e38`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-d5e858b2`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |
| gate:flatness-submit | flatness-submit FAIL | not rerun | yes | host-execution, store-retained | rc=1; /ci/f-d5e858/submit.log |
| gate:flatness-run | flatness-run FAIL | not rerun | yes | host-execution, store-retained | exit=1; /home/hbox/lanes/integ/gate-d5e858b2/flatness.log |
| gate:composed:residents | composed residents fail | not rerun | yes | member-side, infra | fail: residents: REFUSED timeout: managed fixture provider; see /ci/c-d5e858/composed/stat |
| gate:composed:restart | composed restart blocked | not rerun | yes | host-execution | blocked: prerequisite residents has not passed |

Suspect commits since green (`git log 83e926874e38..d5e858b2222b`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `d5e858b2` builder: REDS.md for 467e698ef56f (5 red)
- `dc721e35` conversations: a receive names the app's own rejection (refuseOn), and an incomplete one says what a
- `2ca521af` board: store-retained row: held served state in flight (overlay 4f60d20e9ef7, persvati verdict owed) (owner: store-retained)
- `f937f2b3` mini serve: the serving Host's PID beside the socket (mini.host.pid) (owner: member-side)
- `e63abb0e` board: host-execution row: per-birth doc new profile, second delegate (owner: host-execution)
- `f9a530be` board: host-execution row: lifecycle port landed (2edf8a1ce), next steps, delegate (owner: host-execution)
- `2edf8a1c` host-execution: the app-lifecycle turns serve from the light opening (KN2 2b PORT-C, lifecycle first (owner: build-loop, host-execution)
- `a1f503b0` board: member-side row: orphans stopped and logged; standing rule
- `007cedb6` board: privacy row, consent walk measured near flat after a014ff501; Host still grows
- `b15b9075` board: member-side row: a014ff501 after-number
- `467e698e` client test: name the Host operation constants in the outcome-reply test (owner: member-side)
- `043c2c58` board: member-side row after a014ff501
- `a18cfe5c` board: host-execution row: new seat a0dec24192aead1f1; 7acbdd878 reviewed (owner: host-execution)
- `64a7cf8a` board: apps-hermes row: host-execution seat id, seams updated (owner: apps-hermes)
- `6cde1ddc` builder: REDS.md for ebed79cf874a (5 red)
- `ebed79cf` board: privacy row, relativeTo reviewed (a014ff501)
- `a014ff50` authority load on a walk: a decoded cell takes the held cell's trie by their difference
- `cc5cbd90` Merge remote-tracking branch 'origin/main' into seat/host-execution
- `77f8480f` board: host-execution row: complete continuation for the next seat (owner: host-execution)
- `be581573` builder: REDS.md for 920a4a31412c (5 red)
- `920a4a31` Merge remote-tracking branch 'origin/main' into seat/host-execution
- `d0d40855` host-execution: a first walk opens the Store in full once
- `29a754fe` board: privacy row, FORMAT (a) timing measured: per-write cost still grows; cause and routing
- `6c584257` board: member-side row: persvati doc new numbers, law 17 red
- `c50c4f77` builder: REDS.md for ef2a21c94a3c (5 red)
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
