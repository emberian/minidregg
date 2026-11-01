# Seat: apps-hermes (handoff, 2026-11-01 02:25Z)

Agent: none live. Last: a990f9e07566fd55c (wound down at root's word). Earlier: afb920b22b17049cd, a33e42314aa08ab3a.
Read any of them with `cv show agent-<id>`.

Owns: grain-runtime, spk-host, the apps worker (resource-client apps_worker), the Hermes controller and gateway, route
and conversation declarations (apps/interfaces/*.json, apps/interfaces/format.schema.json,
protocol/hosted-conversation.json with its generator scripts/hosted-conversation.py), and refusal rendering.
Ember's terms: apps are agent-hackable web2 apps wired into Mini so agents act through typed tools; Hermes must work;
refusals name their clause; nothing slows down with history; read code before profiling.

## Landed on main (all checked; no wip branches, nothing unpushed)
- 8bfffe590 referer, sender and twins. scripts/host-operations.py generates `referer_value_ok`, `ordinary_header_ok`
  (twins of Lean Kernel/ApplicationDispatchAdmission refererValueOk/ordinaryHeaderOk; the check pins the Lean body) and
  `same_origin_referer`. The browser entrance, app bindings and controller reduce the referer to a same-origin path;
  the wire decoders, dispatch_web_input and spk-rpc check it.
- 7acbdd878 plans stay valid across a moved image. Kernel/SigningPlanImage.lean `imageFree`; PaidPlan, grant op75 and
  session enrollment op83 currency compare modulo world root and height. Theorems: fixes all else, moved image rfl,
  teeth. resource-client `reply_or_outcome` names Host outcomes; spk-host logs `op-timing opN reply=R ms=T`.
  (467e698ef, by member-side: named op constants in my test. Run `python3 scripts/host-operations.py check` after any
  Rust edit with op bytes.)
- dc721e35c declaration `refuseOn`: a receive names the app's rejection as "app-refused: <reason>" (decided). An
  incomplete conversation lists the frames that did arrive.
- 3305b4b09 unclassified controller errors and failed polls carry their text.
- df55c10a2 Hummingbird analytics.record takes `event` only and matches it in the `locations` stream. Hummingbird reads
  URLs only from Referer, which a Sandstorm bridge never forwards (its headerWhitelist lacks it).
- 40cde03d5 WBO rectangle.write inputs carry WBO 2.18's bounds (integer size 10-500, opacity 0.1-1, geometry
  0-655360); qualify size 10.
- 8834e4862 hosted contract: a socket.io receive may carry condition {"events":[...]}; spk-host drains other event
  packets uncharged. This CHANGES THE RECEIVING DOMAIN; a Host older than this commit refuses the new descriptor. Also:
  socket.io endings are named, and the controller's retained-outcome error carries why.
- f68a50de8 and this row.

## Qualify status per app (j14-apps qualify on hbox)
- Scrumblr: PASSES (sbC, candidate 467e698ef, role 0). Keep it passing.
- WBO (role allAccess, with the certifier): last signature "socketio-connection-refused" (decided) after 16 calls,
  run wbO (overlay 0b6e29ae84e8 on base 467e698ef), evidence /ci/j-wbO. Next run names the app's own message (8834e4862).
  Before that: wbN "app-refused: size: invalid size" (fixed, 40cde03d5); wbK "conversation-terminal-incomplete", 79
  polls (fixed by refuseOn).
- Hummingbird (role allAccess: tracker and view-data are separate roles; the pixel needs tracker and the dashboard
  needs view-data): last signature "native-outcome-unknown: application API outcome remains retained for read-only
  inspection (unmatched: cart_adds x2, view_totals x3)", run hbF, evidence /ci/j-hbF. The app streams about 45
  frames/s and one frame per paid receive never reached `locations`; 8834e4862 is the fix, never yet run live.
- Both need a builder candidate that contains 8834e4862 (/home/hbox/lanes/integ/candidates/<sha>/READY). None existed
  at handoff; the newest was 467e698ef.

## WBO per-op cost (sent to host-execution a559316c0cc2b4b14)
wbK: 79 hosted ops in 180 s (2.28 s each). Host turns are about 1.0 s per op, flat over the run:
- op2 submit: 2.75 per op, p50 88 ms.
- op76: 171 ms.
- op78: 3 per op, p50 17 ms.
- op80: 67 ms.
- op5 query: 9.5 per op at about 8 ms.
- One-offs: op72 15.7 s and op55 10.6 s.
- The remaining ~1.2 s per op is controller-side (mini child spawns, app channel): this seat's to read.
Evidence: /ci/j-wbK/step/oracle/commands/operator-v2.stderr (Host trace) and teardown/residents-*.log (op-timing).
host-execution wants the same split on a candidate containing 2edf8a1ce; call it run wbL.

## The runner (hbox, /home/hbox/lanes/app-reds-cont)
- `ar-hrun.sh CAND_OR_OVERLAY SUF DECL ALIAS ROLE SPK` runs one j14-apps qualify (until=qualify). It writes the world to
  /ci/j-SUF, the gate to gate-SUF/rc, the log to run-SUF.log, and the controller tool result to
  /ci/j-SUF/step/oracle/commands/0095-controller-tool.stdout. Decode its last line: result.text has refusal and
  nativeReceipts.
- `ar-cert.sh SUF` must run alongside every run (`./ar-cert.sh SUF & echo $! > cert-SUF.pid`), or the run ends in
  tail-bound.
- `ar-cycle2.sh SUF DECL ALIAS ROLE SPK` (env CAND=<candidate dir>) moves pool tree t2 to origin/main, rebuilds the
  rust roles, overlays them under lane/ov2/<id>, then runs ar-hrun. ar-cycle.sh is the same with base 9dc9c138c
  hard-coded (obsolete). Before using t2, acquire it: `lane-tree acquire apps-hermes`.
- The source tree, and so the declaration, comes from the BASE candidate's source.tar. Main's declarations must be
  copied into app-reds-cont/override/apps/interfaces/ (holds wbo.json and hummingbird.json from 40cde03d5).
- Args used: Scrumblr `scrumblr.json sb 0 spk/scrumblr.spk`; WBO `wbo.json wbo allAccess spk/wbo.spk`; Hummingbird
  `hummingbird.json hb allAccess spk/hummingbird.spk`.
- Export MINIDREGG_HOST_TRACE=1 for Host per-op traces (operator-v2.stderr).
- spk-host dispatch_native tests need `umask 022` on hbox.

## Box state at handoff
- Nothing of this seat is running. No PID file in app-reds-cont names a live process; the candidate watcher is
  stopped.
- Pool tree t2 released; its diff, identical to 8834e4862, was saved to
  /home/hbox/pool/saved/t2-apps-hermes-20261101T022224Z.patch.
- Removed this session's worlds sbC, hbB-hbE, wbM and wbN with their gate and data dirs (about 7.9 GB); see
  app-reds-cont/winddown.log. Kept /ci/j-wbK, /ci/j-wbO and /ci/j-hbF as evidence. Predecessors' j-ar*, sb*, wb[A-J]
  and hbA are untouched.
- Not this seat's: mini-spk-broker@8eb1fa7d03c980f7 (running since 10-29) and failed not-found mini-spk-s* units.
  /home/hbox/pool/leases/t5-ar.pid names the retired perf-apps lane; there is no lease behind it.
- Packages: app-reds-cont/spk/{wbo,scrumblr,hummingbird}.spk; originals on dregg-forge (/var/lib/spk-fresh/apps/wbo-r2,
  /srv/spk-build/{scrumblr,hummingbird}). App sources live in their unpacked trees there.

## Next, in order
1. On a candidate >= 8834e4862: Hummingbird hbG and WBO wbL, both with the certifier, and MINIDREGG_HOST_TRACE=1 for
   wbL. Read the new signatures; send wbL's split to host-execution.
2. The controller-side ~1.2 s per hosted op (read the code first).
3. op66 shape clause from one install; `mini apps install` timing on a main-built world.

## Seams
- host-execution: a559316c0cc2b4b14.
- member-side: ab7b4fe7fb687e0ca (resource-client; merged reply checks in 22cac1ee0).
