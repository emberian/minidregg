# Reds (owned by the builder, rewritten whole each round)

Tip: `d5e858b2222b` (builder: REDS.md for 467e698ef56f (5 red)). Round finished 2026-11-01T02:50Z.
green: `83e926874e38`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-d5e858b2`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |
| gate:composed:residents | composed residents fail | not rerun | yes | member-side, infra | fail: residents: REFUSED timeout: managed fixture provider; see /ci/c-d5e858/composed/stat |
| gate:composed:restart | composed restart blocked | not rerun | yes | host-execution | blocked: prerequisite residents has not passed |

Suspect commits since green (`git log 83e926874e38..d5e858b2222b`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `d5e858b2` builder: REDS.md for 467e698ef56f (5 red) (owner: build-loop)
- `dc721e35` conversations: a receive names the app's own rejection (refuseOn), and an incomplete one says what a
- `2ca521af` board: store-retained row: held served state in flight (overlay 4f60d20e9ef7, persvati verdict owed) (owner: store-retained)
- `f937f2b3` mini serve: the serving Host's PID beside the socket (mini.host.pid) (owner: apps-hermes)
- `e63abb0e` board: host-execution row: per-birth doc new profile, second delegate
- `f9a530be` board: host-execution row: lifecycle port landed (2edf8a1ce), next steps, delegate
- `2edf8a1c` host-execution: the app-lifecycle turns serve from the light opening (KN2 2b PORT-C, lifecycle first
- `a1f503b0` board: member-side row: orphans stopped and logged; standing rule
- `007cedb6` board: privacy row, consent walk measured near flat after a014ff501; Host still grows
- `b15b9075` board: member-side row: a014ff501 after-number
- `467e698e` client test: name the Host operation constants in the outcome-reply test (owner: apps-hermes)
- `043c2c58` board: member-side row after a014ff501
- `a18cfe5c` board: host-execution row: new seat a0dec24192aead1f1; 7acbdd878 reviewed
- `64a7cf8a` board: apps-hermes row: host-execution seat id, seams updated (owner: apps-hermes)
- `6cde1ddc` builder: REDS.md for ebed79cf874a (5 red) (owner: build-loop)
- `ebed79cf` board: privacy row, relativeTo reviewed (a014ff501)
- `a014ff50` authority load on a walk: a decoded cell takes the held cell's trie by their difference
- `cc5cbd90` Merge remote-tracking branch 'origin/main' into seat/host-execution
- `77f8480f` board: host-execution row: complete continuation for the next seat
- `be581573` builder: REDS.md for 920a4a31412c (5 red) (owner: build-loop)
- `920a4a31` Merge remote-tracking branch 'origin/main' into seat/host-execution
- `d0d40855` host-execution: a first walk opens the Store in full once
- `29a754fe` board: privacy row, FORMAT (a) timing measured: per-write cost still grows; cause and routing
- `6c584257` board: member-side row: persvati doc new numbers, law 17 red
- `c50c4f77` builder: REDS.md for ef2a21c94a3c (5 red) (owner: build-loop)
- `ef2a21c9` builder: REDS.md for 78f347a6af51 (5 red) (owner: build-loop)
- `a2363bbb` board: member-side row after 22cac1ee0
- `22cac1ee` client: one Host reply check names every outcome; the grain recovery test drives the codec session (owner: apps-hermes)
- `78f347a6` builder: REDS.md for 4b750eb674ff (6 red) (owner: build-loop)
- `142d5b99` board: apps-hermes row: referer sender and twins, image-free plan currency, new seat id (owner: apps-hermes)
- `7acbdd87` plans stay valid across a moved image: currency is compared modulo each signing plan's root and heig (owner: apps-hermes)
- `8bfffe59` referer: the senders reduce it to a same-origin path; every twin checks Lean's value rule (owner: apps-hermes)
- `1b0f7cb2` board: apps-hermes row: certifier was a harness bug; payer-plan ruling and referer status (owner: apps-hermes)
- `7ac9217f` dispatch admission: `referer` is an ordinary header, admitted only as a same-origin path (statement 
- `15f9987f` builder: land its own fixture rerecord on main (root's ruling) (owner: build-loop)
- `842bc749` Merge remote-tracking branch 'origin/main' into seat/host-execution
- `8facc1e7` board: host-execution row: measured slices, law-17 cause, next order
- `520e33d2` board: build-loop row: new seat a4141abe7297fdc4b; builder relaunched; akapug #4 and #5 landed
- `64c34e22` fixtures: native runs re-recorded from candidate 9dc9c138cb32 (accepted stale, doc-write stale)
- `ae98da48` fleet-sign join: bind the selected socket before any key, enrollment or funding (PR #4) (owner: apps-hermes)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | FAIL | submit_cpu_ms | 36.000 | 189.000 | 5.250 | 2.000 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 62.938 | 228.739 | 3.634 | 2.000 | host-execution, store-retained |
| flatness-submit | FAIL | propose_cpu_ms | 18.000 | 60.000 | 3.333 | 2.000 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 57.810 | 331.049 | 5.726 | 2.000 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 128.000 | 77.000 | 0.602 | 1.958 | read-path |
| flatness-get | PASS | get_wall_ms | 238.341 | 176.910 | 0.742 | 1.958 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-d5e858b2/flatness.log | - | - | - | - | host-execution, store-retained |
