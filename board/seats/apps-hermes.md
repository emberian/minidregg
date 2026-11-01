# Seat: apps-hermes

Agent: a990f9e07566fd55c (fresh from this file 2026-10-31 23:00Z; predecessors afb920b22b17049cd and a33e42314aa08ab3a, `cv show` for detail)
Owns: grain-runtime, spk-host, the apps worker, Hermes controller and gateway, route and conversation declarations
(apps/interfaces, protocol/hosted-conversation.json), refusal rendering
Work areas: Mac worktree /Users/ember/dev/minidregg-lanes/apps-hermes; hbox /home/hbox/lanes/app-reds-cont (pool tree t2, target/)
Quest: Hermes final say (H1b), live Hummingbird/WBO/Scrumblr qualification, refusals name their clause

## Landed on main (this session)
- 8bfffe590 referer sender and twins. Generated `referer_value_ok`, `ordinary_header_ok` and `same_origin_referer`; the
  browser entrance, app bindings and controller reduce, and the readers check.
- 7acbdd878 plans valid across a moved image: Kernel/SigningPlanImage `imageFree`; PaidPlan, grant op75 and enrollment
  op83 currency compare modulo the image. resource-client names Host outcomes. spk-host logs `op-timing`.
  (467e698ef by member-side fixed my test's literal op bytes.)
- dc721e35c `refuseOn`: a receive names the app's own rejection, as "app-refused: <reason>" (decided). An incomplete
  conversation names the frames that did arrive.
- 3305b4b09 unclassified controller errors and failed polls carry their text.
- df55c10a2 Hummingbird analytics.record correlates on `event` in the `locations` stream. Hummingbird reads URLs only
  from the referer, which Sandstorm's bridge header whitelist never forwards.
- 40cde03d5 WBO inputs carry WBO's own bounds (integer size 10-500, opacity 0.1-1, geometry 0-655360); qualify size 10.
- 8834e4862 hosted contract: a socket.io receive may list `events`; spk-host drains other event packets uncharged. This
  changes the receiving domain. Also socket.io endings are named, and the retained-outcome error carries why.

## Live qualification state (hbox)
- Scrumblr: PASSES (sbC on candidate 467e698ef).
- Hummingbird: attach with role `allAccess`. Tracker and view-data are separate roles; the pixel needs tracker and the
  dashboard needs view-data. hbF reached the beacon and saw only cart_adds and view_totals before the locations frame
  could arrive. Fixed by 8834e4862; rerun on a candidate that contains it.
- WBO: wbK (467e698ef) gives the per-op split, sent to host-execution. wbN after refuseOn: "app-refused: size: invalid
  size", fixed by 40cde03d5. wbO: "socketio-connection-refused" after 16 calls, now named by 8834e4862; rerun.
- Runners: ar-cycle2.sh (CAND env) overlays rust roles; ar-hrun.sh runs one qualify; ar-cert.sh SUF must run alongside
  every run (tail-bound otherwise). The source tree comes from the BASE candidate, so main's declarations go in
  app-reds-cont/override/apps/interfaces/ (now: wbo.json, hummingbird.json from 40cde03d5; refresh after declaration
  commits). spk-host dispatch_native tests need `umask 022` on hbox.
- Since 8834e4862 the SDK sends the new receive condition, which older Hosts refuse. Overlays need a base candidate
  that contains 8834e4862.

## Next
1. When the builder has a candidate >= 8834e4862: run Hummingbird (hbG) and WBO (wbL, MINIDREGG_HOST_TRACE=1). wbL is
   host-execution's after-measurement for 2edf8a1ce; send it the per-op split as for wbK.
2. op66 shape clause from one install; `mini apps install` measurement on a main-built world.
3. E3/E4, E7, decider side of G2.

## Seams
- host-execution (a559316c0cc2b4b14): wbK split sent (dispatch op2/op76/op78 per op; op72/op55 setup); told of the
  receiving-domain change in 8834e4862.
- member-side (ab7b4fe7fb687e0ca): merged reply checks into agent_reserve::host_reply (22cac1ee0).
