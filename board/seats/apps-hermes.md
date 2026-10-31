# Seat: apps-hermes

Agent: afb920b22b17049cd (distilled from a33e42314aa08ab3a, retired) (carries app-reds and perf-apps; hbox work area /home/hbox/lanes/app-reds-cont)
Owns: grain-runtime, spk-host, the apps worker, Hermes controller and gateway, refusal rendering
Quest: Hermes final say (H1b), the START reds, the refusal-clause sweep, live Hummingbird/WBO/Scrumblr

## Landed on main (this session)
- H1b CAUSE (f3d8f3fa5): traced by syscall trace on hbox (j14-apps on dc61016cb-codec, bpftrace of -104/-32 with
  sys and fd). The final say's `mini` child, 3 ms after exec, reads ECONNRESET on the hello of the controller's
  consent peer.sock: the consent service served 4 connections and silently closed the 5th (4 live: a standing
  Hermes-side mini plus 3 concurrent controller children). Not the codec resident, proxy or ServeBounds. Fix:
  16 served, 64 queued up to 30 s, refusal logged. LIVE: j14-apps passes (rc 0, final say succeeds) on dc61016cb-codec with this fix applied to the candidate's own source (hbox /ci/j-ar4); a mini built from main does not run on the dc61016cb Host (kind skew), so check on main's builder next.
- START reds (fda2e4193): route socket past sun_path binds through a bounded alias `<state>/rt/<digest>/http.sock`
  (route_socket.rs); `grain route` publishes it as "socket"; lookup with no accepted original names its outcome.
  The "custody lacks confirmation" was a not-confirmed outcome read as a missing field (a consequence of the
  crash-looping resident). Reproduction on a world with 20-digit ids owed (own/ bins in the work area).
- Refusal sweep second half: journey rows j12/j12w/j14/jpay6/jdisclose assert the clause; typed foreground logs why
  a reply is malformed; room write and foreground executor journal why a write/request failed.
- Branches lane/app-reds*, lane/perf-apps deleted (all content on main; 40cb4aa59 deliberately dropped).

- Unsealed attempt named (78f7ef896); hermes root entrypoint names a python minor mismatch (pins.json pythonVersion);
  j14-apps qualify skips the Davros probe and the foreground API wrapper logs why a call ended undecided (08340bac9).

## Packages for the live runs (no world needed; done)
- WBO: already built and qualified (wbo-r2, package d3b06718..., forge /var/lib/spk-fresh/apps/wbo-r2/out/wbo.spk).
- Scrumblr: forge /srv/spk-build/scrumblr/out/scrumblr-0.5-1.spk (package 57fa8aab..., apiPath "/").
- Hummingbird: repackaged with apiPath "/" (23ad753b7; apps/packages/hummingbird, forge
  /srv/spk-build/hummingbird/out/hummingbird-0.4.1-api.spk, app 434g078h..., package c7287dfb...); declaration repointed.
- Copies of all three: this session's scratchpad .../scratchpad/spk/{wbo,scrumblr,hummingbird}.spk (ship to the new box).

## Live qualification (blocked on a grain world; hbox is down, dregg-build2 pending)
- Runner (hbox only so far): /home/hbox/lanes/app-reds-cont/ar-j14run2.sh CAND SUF DECL ALIAS ROLE SPK, over an overlay
  candidate (lane-build overlay of main's mini/grain-runtime/spk-host roles on a batch candidate). Aliases/roles:
  Scrumblr sb/0, Hummingbird hb/1 (manager), WBO per its declaration.
- Scrumblr qualify ended native-outcome-unknown (app API attempt uncertain, cause unlogged then; 08340bac9 logs it).
  Rerun first on dregg-build2 once grain worlds work there.

## op66-plan refusal (read, no world)
`launch BEGIN authorization, descriptor or action shape refused` is the single throw at
Host/ApplicationLifecycleLaunchBeginAuthoring.lean:260 for `Ingress.shape` (Kernel/ApplicationLifecycleBeginV3Ingress.lean):
operationId = derived authorization id; Source.valid (app, packageManifest, snapshotManifest pairwise distinct;
before.phase = requiredPhase, install 0; generation/versions >= 0; image and process identity 1..256 bytes);
descriptor.matchesManifest (descriptor.valid: package, 1..64 create commands, continue command, <= 1 MiB;
manifest.valid: interface ids unique, schemas valid); packageDigest = descriptor.root; imageIdentity = descriptor's;
volume = volumeId domain app; start binding for START. Facts: descriptor and manifest conjuncts are the same bytes
that pass on hbox, so the world-dependent ones are phase (app cell not at 0) and the three-resource distinctness.
Done (90fba62e4): shapeClause names the failing conjunct in the refusal text; lane-check clean on bb2. Next: read the
named clause from one install on a world.

## Open
1. Rerun Scrumblr, then Hummingbird and WBO qualify; `mini apps install` measurement on a main-built world.
2. Read the op66 shape clause from one install (diagnostic landed 90fba62e4).
3. E3/E4, E7, decider side of G2 (host-execution owns Host-turn costs of app create: a0fee5643746e520c).
