# Retained r3 workroom recovery, 2026-09-27

This is the same retained GitWeb r3 Store used for the confirmed first birth. It is not a new fixture or a fresh genesis. The first workroom continuation failed because its Unix socket path exceeded `SUN_LEN`; recovery `workroom-recovery-0001` reached a signed first query but failed while formatting metadata because the retained script referred to an unbound jq `$cap`. Both failed attempts remain untouched.

The committed one-token generator repair is `b252d67`. The reviewed, append-only recovery script is `scripts/spk-platform/recover-r3-workroom-query.sh` at `6d9980f`, SHA-256 `eec68c4b3bb0b181a34d8ae3b49c284261133ae5797403249d47e2dc64772542`. It pinned the complete existing first-query tree and empty aggregate, re-inspected its exact `view.bin` with the selected source Host, compared the decoded JSON and allocation intent, and reused only that query. The remaining seven signed resource queries, parent policy checks, and six delegated witness checks ran in the original order. The generated recovery script SHA is retained in the protected action.

The action ran as a **user** systemd service `mini-spk-platform-r3-workroom-query-recovery-client-session.service`, invocation `3637e759f4284bb98c58c76f49316c99`. Its journal recorded start at 19:54:14 and 3m40.700s CPU consumed at 19:57:59 EDT, with 1.8 GiB peak memory and no failure entry. The transient unit was collected; `LoadState=not-found` alone is not the verdict. The signed phase evidence, `workroom.completed`, recovery link, and exact hash manifests verify completion. Workroom stderr and unit stderr are empty.

Protected live evidence root: `/var/lib/minidregg/spk/fixtures/gitweb-v2-20260927-client-session-r3`. The original action remains under `continuations/gitweb-journey/base-resume-0001`; failed attempt `workroom-recovery-0001` and successful `workroom-recovery-0002` are separate siblings. The first-query archive is `workroom-recovery-0002/retained-query`; its original signed artifacts remain under `base/workroom/agents/verified/hermes-a-controller`. The public [keyless result](keyless-result.json) contains only the original first-birth receipt fields and counts.

Key hashes (SHA-256):

| Artifact | SHA-256 |
| --- | --- |
| Retained query manifest | `4a016fec1b22db92913998d1fb002998bd24a61aa502253faa12b1e03f058224` |
| Source-reinspected first view JSON | `b5cd1981db884370af9b5c58346d3546d963468a921d8925df06e75eaa118f11` |
| Signed workroom birth evidence | `71604759803d1e97915310314cf15b50ad6afc0f1b6947d32feaee07805c69ad` |
| Eight born-view lines | `003053664584449aca287ff9937ae7694efda19e13a450b241ddf2fad7f9842c` |
| Recovery success manifest | `b992d08ef9521a8cc8b241cb3a600c2e97931de5548adc616a862aa108f42f39` |
| Recovery link | `e33e85f7d87074f9071b586cdc05c136ec2a60f2a019d74b727c6174c11a573f` |
| Workroom completion marker | `25973567adbeab3a449724ac38c9e1c4b74660caa3ae1b8b94f94a3092a24575` |
| Store after workroom | `449278317fac429751ee208b39f5d6b97328c3fa84bf4fbcf6f1a962bb4bf5a9` |

Before this action, the accepted first-birth Store SHA was `e5515e158fdfb03afdafc3951a3a73c2b779bac37eb8428a146c8244611e30e5`. It changed during the workroom's accepted delegation transactions. The app phase was absent when the workroom action completed. The next app/handoff action is separately bounded and must have its own outcome; this evidence does not claim INSTALL, START, browser, or agent acceptance.

The static jq audit checked externally bound `$name` references against `--arg`/`--argjson` and local `as $name` in 61 retained workroom, 42 application, 5 handoff, and 42 generator programs. The known `$cap` typo was the sole missing binding. This is a syntactic audit, not an execution-semantics claim. A read-only dry run of the exact retained first view through the pinned Host inspector and allocation/grain jq predicates passed before the recovery action was created.
