# Reds (owned by the builder, rewritten whole each round)

Tip: `621be51f18e8` (perf(kernel,compiler): eliminate duplicate per-write decodes, leg patches, pin hashes, and). Round finished 2026-11-01T08:43Z.
green: `dbb0dc30de44`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-621be51f`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| host | rc=1 error: Kernel/TurnOfIntent.lean:1844:18: Tactic `rewrite` failed: Did not find an occurrence of the pattern | - | no | suspects' owners | /home/hbox/lanes/integ/logs/host.log |
| consent | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| rust | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| pack | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| umbrella-tree | did not run | - | no | build-loop | an earlier stage stopped the build |

Suspect commits since green (`git log dbb0dc30de44..621be51f18e8`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `621be51f` perf(kernel,compiler): eliminate duplicate per-write decodes, leg patches, pin hashes, and un-narrow
- `cb40b2bb` builder: REDS.md for dbb0dc30de44 (0 red) (owner: build-loop)
