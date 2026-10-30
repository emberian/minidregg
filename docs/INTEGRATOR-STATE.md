# Integrator state

Present-state record of the integration lane, rewritten whole when its shape changes. A successor reads this,
then `hbox:/home/hbox/lanes/integ/COMMANDS.log` (every build stage, gate verdict and tidy act, one line each).
dregg-build and dregg-ref were deleted 2026-10-28; their history is in this file's git history.

## Shape

One integrator (Opus). Kimi (`claude-kimi -p`, read-only) reviews a batch of landings every few plus anything big or
risky. Kimi cannot read the session scratchpad: put a patch inline in the prompt (keep it under ~60 KB) or ask it to
read repo paths. Lanes push branches and send shas; the integrator merges into `integration/staging` on the Mac,
builds staging's tip on hbox, moves main to it once its host stage is green, gates, reports. No codec pins/census.
Statements may be rephrased, never weakened. ATLAS law 17: never slower over time (flatness bench = the one perf
gate; hot-path sends it, wire it into the gate).

## Where things are

- Mac landing worktree `/Users/ember/dev/minidregg-lanes/integration-r2` (branch `integ/main` = staging, pushed to
  `origin/integration/staging`); a scratch worktree of main at the session scratchpad `integ2/wt-main`.
  Mac checks: `CARGO_TARGET_DIR=/Users/ember/dev/minidregg-lanes/target-integ`, filtered `cargo test --bin mini -- apps::`
  etc. (the apps_front connector test fails only inside the group).
- hbox tree `/home/hbox/lanes/integ/src` (NVMe `/`; rpool/othersys is not ours). Build `integ-build2.sh SHA`
  (pid file integ/build.pid): rust-check, host, consent, umbrellas (non-fatal), rust, pack -> `integ/candidates/<sha>/READY`.
  Run with `SEATS=4 MEM=40G`; keep combined Lean caps on hbox near 60 GB so ~30 GB stays for test worlds, and stagger
  host stages with the hot-path lane (a9bba0bc5f114fc06). Incremental build 6-10 min; a deep StoreCodec change ~40-60 min.
- Gate `integ/gate9.sh SHA` (newest; never edit a script in place, number the next one). Env: PHASES ("tour composed
  enrol"), SUF, HARNESS (overlay scripts/ + resource-client scripts + journey.d from a sha), EDGE_REV=69c17a3 (dregg-infra
  tree integ/dregg-infra-<rev>), PORT and JWORLD_ROUTE_FRONT_PORT unique per concurrent run, JWORLD_MANAGEMENT=sponsor
  (distinct breaks app births; see reds), JWORLD_ROOT_HANDOFFS=1 default, TOUR_FROM, KEEP_WORLD=1 (leave the composed world
  up; the log line says how to take it down). Results integ/gate-<sha8><SUF>/; runs under /ci. Playwright
  /tank/dregg-build/rows-0ce31391/pw/node_modules (browsers ~/.cache/ms-playwright). Infra also offers `ssh composed-box`
  (a container on dregg-forge) for composed if hbox root setup gets crowded; not used yet.

## Main and candidates (2026-10-30 ~10:55 EDT)

Main = staging = ee29d4fa7 (+docs). Newest READY candidate: ee29d4fa7d4a46f11f5ee6d0d4bee2a2c2df32e8 (proofs only over c7aa7e8c4) (binaries = 41590f420's:
everything through apps-agents 06e6c30eb, infra c3d17f136 chat join, Firefly; harness through infra's residents work:
e365dd7e6, df0ea4252, 21a117df3, d9d3bdfc2 Hermes account adopt, 2418692c7/1531ec571 root hand-off, c7aa7e8c4 fixture ACP).

| candidate | verdict |
|---|---|
| 41590f420 | gate12 distinct: tour 73/73, j14-apps PASS (5 rows), composed rooms/churn/documents/apps/connector/store-restart PASS; residents/restart judged on forge only |
| 5f18b9f50 | RED (source-capability dedup broke births); reverted aa5a80b2a |
| c7aa7e8c4 | READY 10:51; named to infra and the scout |
| ee29d4fa7 | READY 11:05 = c7aa7e8c4 + proofs 75cd46376 (Lean only). Umbrellas: EngineProofs and BirthPlanPoles fixed; now red: Fixtures.NativeAcceptedFixture, NativeDocWriteFixture, Effects.Revival.PrepareProofs (prepareFactors sorryAx at :282), HostTeethProofs (imports it); proofs lane has them |

Composed authority: infra's forge composed container (residents needs root). There, residents passes through
registration, summon, requests, prepoll, provider custody copy and the Hermes turn reaching the provider, then the
fixture ACP closes its stream at prompt 11 (infra digging; my pointers: release-end-turn visibility, MCP closed after each
prompt, the fixture's own refusals). hbox gate12 covers tour, j14-apps, flatness.

Lanes that send shas (2026-10-30): proofs Opus af4b3ea612564dea5 (umbrella reds, statement fixes), app-reds Sonnet
a17f4172949caca14 (OwnTracks, Hummingbird, controller-world tests, WBO, missing declarations), scout Sonnet
a3d575cdd7a822f6b (every journey row + stress on the newest candidate; routes faults), infra add189844d158e3a7,
iteration speed Opus a141a9c535501bbd7 (Lean seams at codec/store/world-root: deep batched landings, warned ahead so
other Lean landings hold for one closure; lane-tree warm pool; hot-swap of one crate into a KEEP_WORLD world, on top of
gate12 KEEP_WORLD and infra's composed-gate resume). First: Lean v4.30.0 -> v4.35.0 + Mathlib as one sha off main;
on its "HOLD LEAN" message hold all other Lean landings (proofs lane) until the bump's candidate is READY, then they
rebase; Rust-only landings keep flowing; build the bump alone on hbox.
Name every new candidate to infra and the scout. Cut a candidate per landing batch (about 5 min Rust-only).

gate12: `EDGE_REV=69c17a3 JWORLD_MANAGEMENT=distinct KEEP_WORLD=1 PORT=.. JWORLD_ROUTE_FRONT_PORT=.. bash gate12.sh SHA`
(gate10 + j14-apps; j14 inputs integ/j14-hroot, j14-data, j14-secrets; run under /ci). Down a kept world with the
candidate's scripts/spk-platform/world-down.sh RUN/inputs, then dregg-infra-69c17a3/edge/mini/journey/jworld-scratch.sh
down RUN/w (as hbox with XDG_RUNTIME_DIR/DBUS); log DOWN. No world kept up.
Stray jweb-frontend `mini web --body` children of old gates (pids 806516, 2013999, 1482603, 1728806) were stopped
2026-10-30 by exact PID after checking their command lines (root ruling: stale leftovers of our own runs).

## The connector red: two causes, both fixed

1. spk-browser-proxy is TLS 1.3 + X25519MLKEM768 only; the export shelled out to /usr/bin/curl (OpenSSL < 3.5 has no
   hybrid group). 69251145d/6b1c05490: the export runs on rustls/aws-lc-rs in the client (Kimi-reviewed; overflow,
   deadline and framing fixes taken).
2. Sheet jd3 was never written, so EtherCalc answered 404 and the entrance 503. Infra's 552a316e7 seeds it
   (connector:sheet step); 27c274052 makes publish print one JSON document. Connector PASS on 994e36d08.

## Market packages for the demo box

dregg-forge:/var/lib/spk-fresh/qualified-2026-10-29/out/{local.json,adopt.tsv}: 20 packages; files under
../apps/<app>/out/<app>.spk; earlier outs kept as out.prev-N (session-made, removable). Regenerate: link or copy the
package into apps/<app>/out/<app>.spk (spk-fresh's forge copies live under /srv/spk-build/<app>/out/), move out aside,
`python3 -I repo/deploy/market/fresh-index.py --apps $Q/apps --recipes $Q/repo/apps/packages --spk-tool
/var/lib/spk-fresh/tools/spk --out $Q/out`, copy local.json to native/resource-client/tests/fixtures/
fresh-local-index-2026-10-29.json, run `cargo test --bin mini -- apps::tests` (24). FEATURED still upstream: WBO
rhtntjye (wbo.json names upstream), r8y55acm, zxent02j, uws252ya. SPK-fresh (a58fcf100f4438710): queue complete (Firefly last); all eight reruns pass the forged-identity row.

## In flight

- Infra (add189844d158e3a7): distinct composed residents/restart on 41590f420 (forge container).
- deploy/spk-host/tests/test_controller_world.py: 8 errors, 2 failures on hbox (ancestor custody refused under
  /home/hbox, ProtectHome=tmpfs expectation); environment or regression unknown, for lane/apps-agents.

## Reds

- Flatness submit (law 17): submit wall 4.97x, propose CPU 9.27x over 1000 ops (bound 2x); GET PASS. The hot-path
  codex batch is landed; its HOT-PATH-STATE.md names the remaining costs (cold-start snapshots, persistent whole-cell
  writes). No lane is on it now; a hot-path successor starts from docs/HOT-PATH-STATE.md.
- Composed: residents (sponsor-mode refusal by design) and restart, pending distinct-mode births (infra).
- Umbrellas: Fixtures.NativeAcceptedFixture, NativeDocWriteFixture, BirthPlanPoles, Effects.Revival.EngineProofs.
- OwnTracks username normalization; Hummingbird native conversation qualification.

## Not landed / held

cx-oracle dd80466a1 and codex/oracle-v7-qualification b32f15604 (conflict; wait for oracle7); statement-fixes (WIP);
qualify-doc-contention (WIP).

## Next steps

1. Read gate-41590f42 (j14-apps row, composed distinct); merge infra's fix shas, rebuild, regate until residents and
   restart pass; hand the green candidate to infra for the ship.
2. Down kept worlds when done (/ci/c-41590f).

## Hygiene done 2026-10-29

/var/lib/mini-spk-worlds emptied through install-user-world remove (each logged in COMMANDS.log); my old rpool tree
/othersys/lanes/integ removed. Rules: named-file commits with `git commit -F`; never `git add -A` or `git stash`;
filtered tests; PID files; stop only by PID file; lake/git on hbox as hbox; disk pressure = stop and tell ember.
