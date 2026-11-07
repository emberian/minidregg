# Reds (owned by the builder, rewritten whole each round)

Tip: `20c68da6f504` (Merge remote-tracking branch 'origin/main' into lane/perf-client-census). Round finished 2026-11-07T03:37Z.
green: `eb932b7c6547`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-20c68da6`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| umbrella-tree | running | - | yes | build-loop | the umbrellas have not finished; this file is rewritten when they do |

Suspect commits since green (`git log eb932b7c6547..20c68da6f504`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `20c68da6` Merge remote-tracking branch 'origin/main' into lane/perf-client-census
- `37a2dc2c` submit: the served directory's identity check is one hashed pass; credit picks its account from the  (owner: apps-hermes)
- `ba9c5566` builder: REDS.md for c9717142f088 (1 red) (owner: build-loop)
- `c9717142` Merge remote-tracking branch 'origin/main' into lane/init8-flashprove-audit
- `3db155aa` builder: REDS.md for f2dae81d3680 (1 red) (owner: build-loop)
- `0b5050ab` Merge remote-tracking branch 'origin/main' into lane/init8-flashprove-audit
- `f2dae81d` Merge remote-tracking branch 'origin/main' into lane/perf-client-op5
- `897c7532` PERF-CLIENT: row 27, op 5 through the issued index
- `14682b57` issuer evidence reads a held issued index, not a search over the authority cell
- `8a9cecbd` Merge remote-tracking branch 'origin/main' into lane/init8-flashprove-audit
- `04b10f50` builder: REDS.md for 1c71a6fe2d94 (1 red) (owner: build-loop)
- `1c71a6fe` builder: REDS.md for 976f31067e01 (1 red) (owner: build-loop)
- `a0ad8559` PERF-CLIENT: row 28, receipt continuity verifier processes
- `3e6b24eb` Merge remote-tracking branch 'origin/main' into lane/perf-client
- `9b117157` receipt continuity: no verifier process for a read whose point is already known (owner: apps-hermes)
- `200cb5f5` builder: REDS.md for 893ccd7293de (1 red) (owner: build-loop)
- `893ccd72` builder: REDS.md for b4e212ca447f (1 red) (owner: build-loop)
- `df08e974` transport: one verified sealed snapshot per pinned image per process (owner: apps-hermes)
- `93b2bf25` builder: REDS.md for eb932b7c6547 (0 red) (owner: build-loop)
- `72ec2542` PERF-CLIENT: row 19 through an empty intent; rows 26 (236 upgrade spin) and 27 (op 5 grows with birt
- `f4c97613` Selvage.AuditExact: [EX-transport] only on opened, exit-0 calls (codex round 3)
- `ee48f59d` Selvage: AuditChecked (any checker) and AuditExact (exact recompute of gpt-oss-20b), initiative 8
- `944f02da` Selvage.AuditFlashProve: an accepting checker meets the bad event (compiled evaluation)
- `2059a06e` Selvage.AuditFlashProveDecide: opening, round and rate rules exported (codex round 2)
- `7fdb32a2` Selvage.AuditFlashProve: run-level bad event after codex round 1
- `ad6c678a` Selvage: AuditSampling instantiated over FlashProve cp_verify (initiative 8)

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | PASS | submit_cpu_ms | 0.159 | 0.168 | 1.056 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | submit_wall_ms | 29.324 | 70.216 | 2.394 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | propose_cpu_ms | 0.131 | 0.161 | 1.228 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 27.519 | 67.307 | 2.446 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 0.354 | 0.323 | 0.912 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 139.391 | 152.995 | 1.098 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-20c68da6/flatness.log | - | - | - | - | host-execution, store-retained |
