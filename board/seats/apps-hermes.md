# Seat: apps-hermes

Agent: a33e42314aa08ab3a (carries app-reds and perf-apps; hbox work area /home/hbox/lanes/app-reds-cont)
Owns: grain-runtime, spk-host, the apps worker, Hermes controller and gateway, refusal rendering
Quest: Hermes final say (H1b), the START reds, the refusal-clause sweep, live Hummingbird/WBO/Scrumblr

## Landed on main (this session)
- H1b CAUSE (f3d8f3fa5): traced by syscall trace on hbox (j14-apps on dc61016cb-codec, bpftrace of -104/-32 with
  sys and fd). The final say's `mini` child, 3 ms after exec, reads ECONNRESET on the hello of the controller's
  consent peer.sock: the consent service served 4 connections and silently closed the 5th (4 live: a standing
  Hermes-side mini plus 3 concurrent controller children). Not the codec resident, proxy or ServeBounds. Fix:
  16 served, 64 queued up to 30 s, refusal logged. Live j14-apps check with the new `mini` still owed.
- START reds (fda2e4193): route socket past sun_path binds through a bounded alias `<state>/rt/<digest>/http.sock`
  (route_socket.rs); `grain route` publishes it as "socket"; lookup with no accepted original names its outcome.
  The "custody lacks confirmation" was a not-confirmed outcome read as a missing field (a consequence of the
  crash-looping resident). Reproduction on a world with 20-digit ids owed (own/ bins in the work area).
- Refusal sweep second half: journey rows j12/j12w/j14/jpay6/jdisclose assert the clause; typed foreground logs why
  a reply is malformed; room write and foreground executor journal why a write/request failed.
- Branches lane/app-reds*, lane/perf-apps deleted (all content on main; 40cb4aa59 deliberately dropped).

## Open
1. Unsealed attempt: `retry --mode submit` on an attempt with no call.bin fails ("attempt has no retained ...");
   resubmit_unsubmitted_write should name it (never sealed: author again). Rare once the consent bound is fixed.
2. Live Hummingbird conversation run, then WBO and Scrumblr (typed_applications foreground, built, unrun).
3. E3/E4, E7, decider side of G2, Hermes worker interpreter (venv symlinks /usr/bin/python3.12; box has 3.13),
   op66-plan for EtherCalc/Etherpad on the demo world.
4. perf-apps continuation (docs/PERF-APPS.md): measure `mini apps install` end to end and the first page now that
   the START fixes are on main; Host-turn costs of app create go to host-execution (a0fee5643746e520c).
