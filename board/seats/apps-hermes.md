# Seat: apps-hermes

Agent: a33e42314aa08ab3a (carries app-reds and perf-apps; hbox work area /home/hbox/lanes/app-reds-cont)
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

## Live qualification (in progress)
- Overlay candidate from main (lane-build overlay over batch 9 997905c0b: mini, grain-runtime, spk-host roles) in
  hbox /home/hbox/lanes/app-reds-cont/lane/ov; runner ar-j14run2.sh CAND SUF DECL ALIAS ROLE SPK (j14-apps qualify).
- Scrumblr (spk from forge /srv/spk-build/scrumblr/out, role 0): world, attach reach qualify; the foreground
  qualify ends native-outcome-unknown, application API attempt phase uncertain, no cause recorded (log added in
  08340bac9). Next: rerun with that log. WBO spk is not on the forge; build it from apps/packages/wbo/build.sh.
  Hummingbird has no package in apps/packages (needs a repackage with apiPath).

## Open
1. WBO and Hummingbird packages, then their qualify; `mini apps install` measurement on a main-built world.
2. E3/E4, E7, decider side of G2, op66-plan for EtherCalc/Etherpad on the demo world (host-execution owns the
   Host-turn costs of app create: a0fee5643746e520c).
