# Reds (owned by the builder, rewritten whole each round)

Tip: `ffa7a77f2182` (board: apps-hermes row). Round finished 2026-10-31T19:29Z.
green: `83e926874e38`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-ffa7a77f`.

| stage | signature | reruns? | same place as last round? | detail |
|---|---|---|---|---|
| umbrella-tree | rc=1 see /home/hbox/lanes/integ/logs/umbrella-tree.log | - | yes | /home/hbox/lanes/integ/logs/umbrella-tree.log |
| rerecord | rc=1 FAILED create-notes rc=1: workspace continuity: legacy; initialize with workspace --action continuity-init --name REF | - | no | /home/hbox/lanes/integ/logs/rerecord.log |
| umbrella | RED TokenCensus | - | no | /home/hbox/lanes/integ/logs/umbrella-tree.log |
| gate:flatness-submit | flatness-submit FAIL | not rerun | yes | rc=2; /ci/f-ffa7a7/submit.log |
| gate:flatness-get | flatness-get FAIL | not rerun | yes | rc=1; /ci/f-ffa7a7/get.log |
| gate:flatness-run | flatness-run FAIL | not rerun | yes | exit=1; /home/hbox/lanes/integ/gate-ffa7a77f/flatness.log |
| gate:j14-apps | j14-apps FAIL | not rerun | yes | rc=1; /ci/j-ffa7a7/journey.log |
| gate:composed | composed FAIL | not rerun | yes | scratch world: jworld FAIL enroll member-4 FAILED at `enroll plan member-4 7b280f13ad9dbf12de67498a294c551ad1a3a518390552be767a559c0e9ca2be c3fd9e94b96a0ee660052a7581fd87cc86260a6674920693c96a57a908d71589 6ebdce90836bea743b88f993f4bc5 |

Suspect commits since green (`git log 83e926874e38..ffa7a77f2182`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

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
- `802ba8c6` L0: the Store and the World's cells are persistent trees (Theory.SparseMap); WorldCompact deleted (owner: host-execution, privacy, read-path, store-retained)
- `f9fcaa25` privacy: the selective opening's fixed relation, and proof systems in the ROM with costs (owner: privacy)
- `3fefbd60` board: member-side seat taken by ab7b4fe7fb687e0ca
- `5a0cb3b4` board: member-side row rewritten whole as the continuation for a fresh seat
- `07e2c47a` builder: fetch green by explicit refspec; never print the tip~20 as green (owner: build-loop)
- `19e29931` board: member-side row 19, what the catch-up still spends
- `0d9e6e75` hermes runtime root: the entrypoint names a python minor-version mismatch; pins.json records the ver (owner: apps-hermes, build-loop)
- `78f7ef89` room write: resubmitting a write that was never sealed names it instead of failing in `mini retry` (owner: apps-hermes)
- `87f6e7e3` board: apps-hermes row: H1b live check green (owner: apps-hermes)
- `605b9243` board: host-execution row: new agent id a24974e84d3c540d1 (owner: host-execution)
- `ed875b89` perf(consent): a provider's Store-side target carries no World (owner: member-side)
- `6eb34142` board: host-execution row: KN2 2b inventory (owner: host-execution)
- `6fa3ebfa` board: host-execution row: refresh growth gone on the lane head; KN2 2b first (owner: host-execution)
- `525ac54e` board/RULINGS: KN2 2b owners for the Store open
- `151e7217` board: build-loop row: the builder runs; integrator remnants removed (owner: build-loop)
- `a15e97b1` board/seats/read-path.md: cold first read and restart traced to the full Store open
- `adf73b9e` docs: INTEGRATOR-STATE.md removed: the integrator is retired, the builder and board/ replace it
- `6ca201aa` builder: REDS.md for 997905c0bc9c (6 red)
- `7132a51e` builder: the unattended loop on the main tip (board/README.md), owned by build-loop (owner: build-loop)
- `6d26f91c` board: REDS rows from the forge composed runs of batches 7 and 8
- `32f94157` board: apps-hermes seat row rewritten (owner: apps-hermes)
- `fb450589` j14-apps: a failed foreground qualify keeps the controller's tool result and journal (owner: member-side)
- `5248c6fe` grain-runtime: the foreground typed executor journals why a prepared request failed (owner: apps-hermes)
