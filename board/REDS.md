# Reds (owned by the builder, rewritten whole each round)

Tip: `3c6b99064d42` (builder: REDS.md for 359ace71edac (5 red)). Round finished 2026-11-01T03:35Z.
green: `83e926874e38`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-3c6b9906`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| host | rc=1 error: build failed | - | no | suspects' owners | /home/hbox/lanes/integ/logs/host.log |
| consent | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| rust | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| pack | did not run | - | no | suspects' owners | an earlier stage stopped the build |
| umbrella-tree | did not run | - | no | build-loop | an earlier stage stopped the build |

Suspect commits since green (`git log 83e926874e38..3c6b99064d42`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `3c6b9906` builder: REDS.md for 359ace71edac (5 red) (owner: build-loop)
- `48b93d3c` write-path: eliminate target cell re-hash in observation prepare and post-bytes decode in birth prep (owner: apps-hermes)
- `f7031ae1` fixtures: native runs re-recorded from candidate 359ace71edac (accepted stale, doc-write stale)
- `9c4cc12b` enrol-resume: synchronize background ticker stop with last-tick timestamp (owner: apps-hermes)
- `a6cfdc7b` gate: perform composed root handoffs and broker supervision; skip flatness on phase reruns
- `359ace71` builder: REDS.md for e00408f660e6 (7 red) (owner: build-loop)
- `f81ce864` Kernel.ApplicationShareIssueHistorical: pass Ground.ofLoaded to IssuedEvidence.fromAccepted
- `e78141bf` fixtures: update leg projections in accepted and doc-write authorities for fold v2
- `e00408f6` builder: REDS.md for d5e858b2222b (3 red) (owner: build-loop)
- `2157f5ce` pipeline: scope per-round umbrella-tree to fast census targets unless instrument changed
- `8159a9e6` residents: restart fixture provider across world roots and reap on world-down
- `638e164b` board: store-retained handoff (wind-down): landed shas, the held served state's WIP and diagnosis, b (owner: store-retained)
- `43b1aad6` board: apps-hermes row: handoff (wind-down), runner, per-app status, box state (owner: apps-hermes)
- `c0ac6488` board: host-execution row: whole handoff at wind-down (landed, wip/he-enrol state, next steps, reds,
- `d5845544` board: member-side row rewritten whole as the handoff (wind-down)
- `0b728dc3` board/seats/read-path.md: rewritten whole as the handoff for a new agent
- `bcbb92e3` board: privacy seat handoff, rewritten whole for a new agent
- `85a8f4c8` board: build-loop row rewritten whole as the handoff (builder stop/start, pool, reds, boxes)
- `cd493933` board: infra seat rewritten whole as a handoff for a new agent
- `60611b9f` board: member-side row: standing worlds
- `ea8a115c` board: build-loop row: flatness published not gating; world reaping; fleet survey counts
- `9317f32f` builder: flatness is published, never a red; finished gate worlds are reaped after each verdict (owner: build-loop)
- `c509ff14` builder: REDS.md for d5e858b2222b (5 red) (owner: build-loop)
- `f68a50de` board: apps-hermes row: refuseOn, Hummingbird locations, WBO bounds, hosted event filter, live state (owner: apps-hermes)
- `8834e486` hosted conversations: a socket.io receive names its awaited events; the Host drains the rest uncharg (owner: apps-hermes)
- `462919a4` invoke: target pre-roots and read guards come from the ground's snapshot, not a re-hash (owner: apps-hermes)
- `c4a1e4cf` An append reads its document from propose's own signed read (owner: apps-hermes)
- `fd822f76` board/seats/read-path.md: the whole continuation for the next read-path seat
- `48dc530f` board: build-loop row: idle leases taken after 30 min, pool grown to 11, rerecord race fixed
- `14f9cbb2` Op 5's opening cache picks by the cell root; the reply frame is not copied
- `fd1686db` integ-build: the rerecord holds the umbrella tree; land_regen diffs against the regen's own parent (owner: build-loop)
- `cbe54d87` lane-tree: a lease idle 30 minutes with no process in its tree is taken
- `90c8cbed` board: host-execution row: restore the worktree line
- `f45beda2` board: host-execution row: seat id a559316c0cc2b4b14, delegates state
- `6ccd0cd4` board: host-execution row: e71c9ab59, he-births commits, dispatch ruling
- `913e66cd` invoke: the read guards take the written ids without building the target writes (owner: apps-hermes)
- `901d910c` World legs carry only their changed ops; the turn's pin guards the rest (fold v2) (owner: read-path)
- `40cde03d` wbo: rectangle.write's numbers carry WBO's own bounds; the qualify size is 10
- `df55c10a` hummingbird: analytics.record correlates on its event in the live locations stream, not on a referer
- `8f659b53` board: member-side row: held pair cause; bind? on the walk next
