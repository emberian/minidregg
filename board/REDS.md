# Reds (owned by the builder, rewritten whole each round)

Tip: `446f0c1c9d1f` (builder: REDS.md for 29f27f657a11 (5 red)). Round finished 2026-11-01T06:15Z.
green: `83e926874e38`. Builder: hbox `/home/hbox/lanes/integ`, logs `/home/hbox/lanes/integ/builder`, gate `/home/hbox/lanes/integ/gate-446f0c1c`.

| stage | signature | reruns? | same place as last round? | owner | detail |
|---|---|---|---|---|---|
| gate:j14-apps | j14-apps FAIL | no: passed on rerun (flaky) | yes | apps-hermes | rc=1; /ci/j-446f0c/journey.log |
| gate:composed:residents | composed residents fail | no: passed on rerun (flaky) | no | member-side, infra | fail: residents: REFUSED driver ended before the end_turn gate; see driver-before-cut.stde |
| gate:composed:restart | composed restart blocked | no: passed on rerun (flaky) | yes | host-execution | blocked: prerequisite residents has not passed |

Suspect commits since green (`git log 83e926874e38..446f0c1c9d1f`), newest first; owners are the seats whose
`Owns:` line (board/seats/*.md) names a path the commit touched:

- `446f0c1c` builder: REDS.md for 29f27f657a11 (5 red) (owner: build-loop)
- `b97d545f` gate,sweep: isolate composed root-sealed frame under /ci-composed and use FLATNESS_LO=20 (owner: build-loop)
- `29f27f65` builder: REDS.md for 340481687d62 (1 red) (owner: build-loop)
- `591b72ba` fixtures: native runs re-recorded from candidate 340481687d62 (accepted stale, doc-write stale)
- `64f874d3` rerecord,builder: pass libmini_kernels_lean to fixture elaboration check and skip rerecord-only tips (owner: build-loop)
- `34048168` builder: REDS.md for 19d6c139081f (2 red) (owner: build-loop)
- `ff1e3338` fixtures: native runs re-recorded from candidate 19d6c139081f (accepted stale, doc-write stale)
- `f8ba05d7` composed,client: skip propose view-document when run-free, use system controller manager, and replan (owner: apps-hermes)
- `19d6c139` builder: REDS.md for 78797a80cb02 (4 red) (owner: build-loop)
- `781e067f` fixtures: native runs re-recorded from candidate 78797a80cb02 (accepted stale, doc-write stale)
- `78797a80` builder: REDS.md for b6a6dfcd4a08 (4 red) (owner: build-loop)
- `17665e50` fixtures: native runs re-recorded from candidate b6a6dfcd4a08 (accepted stale, doc-write stale)
- `c4ecabe0` store-retained: hold served cell state in a persistent map and bind replayed suffixes once
- `b6a6dfcd` builder: REDS.md for 3c6b99064d42 (5 red) (owner: build-loop)
- `695fddbe` invoke: share postBytes in targetWriteFast to match packedWrite (owner: apps-hermes)
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

## Flatness (published, does not gate `green`)

| row | verdict | metric | early | late | ratio | bound | owner |
|---|---|---|---|---|---|---|---|
| flatness-submit | FAIL | submit_cpu_ms | 30.000 | 57.000 | 1.900 | 1.590 | host-execution, store-retained |
| flatness-submit | PASS | submit_wall_ms | 50.321 | 77.098 | 1.532 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_cpu_ms | 5.000 | 17.500 | 3.500 | 1.590 | host-execution, store-retained |
| flatness-submit | FAIL | propose_wall_ms | 31.652 | 89.403 | 2.825 | 1.590 | host-execution, store-retained |
| flatness-get | PASS | get_cpu_ms | 58.000 | 53.000 | 0.914 | 1.856 | read-path |
| flatness-get | PASS | get_wall_ms | 172.203 | 158.034 | 0.918 | 1.856 | read-path |
| flatness-run | FAIL | no numbers: exit=1; /home/hbox/lanes/integ/gate-446f0c1c/flatness.log | - | - | - | - | host-execution, store-retained |
