# Reds (owned by the builder, rewritten whole each round)

Tip: `997905c0bc9c` (docs: INTEGRATOR-STATE.md: D2 fixed on staging, resubmit finding). Round finished 2026-10-31T17:23Z.
green: `83e926874e38` (batch 4; this round's builder had no origin/green and printed the tip~20, fixed). Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-997905c0`.

| stage | signature | reruns? | same place as last round? | detail |
|---|---|---|---|---|
| umbrella-tree | rc=1 see /home/hbox/lanes/integ/logs/umbrella-tree.log | - | yes | /home/hbox/lanes/integ/logs/umbrella-tree.log |
| gate:flatness-submit | flatness-submit FAIL | not rerun | yes | rc=1; /ci/f-997905/submit.log |
| gate:flatness-get | flatness-get FAIL | not rerun | yes | rc=1; /ci/f-997905/get.log |
| gate:flatness-run | flatness-run FAIL | not rerun | yes | exit=1; /home/hbox/lanes/integ/gate-997905c0/flatness.log |
| gate:j14-apps | j14-apps FAIL | not rerun | yes | rc=1; /ci/j-997905/journey.log |
| gate:composed | composed FAIL | not rerun | yes | rooms=pass; churn=pass; documents=pass; apps=pass; connector=pass; residents=fail: residents: REFUSED prepoll-filler-070 refused with status 3; retained 00194-prepoll-; restart=blocked: prerequisite residents has not passed; store-restart=fail: store-restart:world: mini-health: unhealthy — remaini |

Suspect commits, newest first. This round listed `c849687da03b..997905c0bc9c` (the tip~20, from the green-fetch bug); green is `83e926874e38` (batch 4), and the next round counts from it; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `997905c0` docs: INTEGRATOR-STATE.md: D2 fixed on staging, resubmit finding
- `5fa44a57` Merge commit '837c3f457' into integ/staging (owner: member-side)
- `b5c9e6cc` docs: INTEGRATOR-STATE.md: D2 evidence location
- `9beaae97` docs: INTEGRATOR-STATE.md: batch 8 verdict, codec theory refuted, D2, app-reds retiring
- `837c3f45` A protected document's enrollment phase stays in the workspace (owner: member-side)
- `6492ca51` Merge commit 'caa988a88' into integ/staging
- `9a570e5a` grain-runtime codec: a controller command that sets MINI_CODEC_RESIDENT=0 gets an in-process codec H (owner: apps-hermes)
- `6ff34ee4` Merge commit 'acd9d5f52' into integ/staging
- `caa988a8` refactor(client): one reading of a session's delegated consent and shared codec (owner: member-side)
- `1607390a` docs: INTEGRATOR-STATE.md: hot-path follow-ups on staging
- `9540a646` Merge commit '75d97b3519ba3c34d4f2cde1cdb45a3cf5923c22' into integ/staging
- `acd9d5f5` docs: APP-REDS-STATE.md: continuation at the context limit
- `b83b6a0f` docs: INTEGRATOR-STATE.md: private-cells FORMAT (a) WIP status
- `75d97b35` hot-path: a turn's derivation decodes each written post once
- `46ba70e4` hot-path: C1 audit follow-ups: refs never point ahead; channel theorems cover moved appends
- `1cd40828` docs: INTEGRATOR-STATE.md: shared streams crate and qualification single path on staging
- `479e6847` Merge commit 'b59364ba5' into integ/staging
- `b59364ba` docs: PERF-APPS.md: batch 5, the codec child is the qualification's only path
- `a66d51f1` spk-host: the qualification's codec child is its only path (owner: apps-hermes)
- `0c05fe27` Merge commit '096c881e5' into integ/staging
- `096c881e` test(client): closed_stdout accepts a mini that wrote before the reader left (owner: member-side)
- `0e43880c` docs: INTEGRATOR-STATE.md: perf-apps batch 4 on staging
- `4315513a` docs: PERF-APPS.md: batch 4, the qualification on one codec child
- `66ccd307` spk-host: a launch qualification's steps share one storeless codec child (owner: apps-hermes)
- `f5441749` fix(client): one closed-stdout implementation for every client binary (owner: apps-hermes, member-side)
- `358a7964` docs: INTEGRATOR-STATE.md: C1 audit details
- `27272500` docs: INTEGRATOR-STATE.md: C1 audit sound, owed items
- `9877025d` docs: EXORCISM-CONTINUATION.md: reference names read only when asked, measured
- `0a28480b` docs: INTEGRATOR-STATE.md: C1 fixed on staging, birth plan numbers
- `33106c33` Merge commit 'a9e738baf' into integ/staging
- `a9e738ba` hot-path: a stream append is computed at the head it meets, not its planned root
- `478f170a` A page that names nothing reads no reference file (owner: member-side)
