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

## Live qualification (hbox; bb2 is obend's and my files there are removed)
- Ruling (root): a route path is the app's own URL and is carried byte-exact. a4b37cd28 reverted; the Host admits one trailing "/"
  on CONVERSATION relative paths (signed_api_path::conversation_route; Host wire v3, custody projection, dispatch_inspection, and the
  controller's twin HostedRoute in grain-runtime application_api_tools). Channel ids are 37 characters (9dc9c138c).
  Commits: 1c670cee5, e46759f4e, plus the attachment roleId change below.
- SCRUMBLR QUALIFY PASSES (hbox run sbB): write a card, read it back through a fresh socket.io client; rows typed-attachment and
  native-qualification-sb. Declaration status can move from prototype-unqualified once the owner decides how it is recorded.
- WBO (runs wbA..wbJ): attach needs roleId allAccess (landed). "Certify blocks behind a conversation" was MY harness bug (a stale
  copy of the sponsor workspace.json: its socket name changes operator.sock -> operator-v2.sock during setup; ar-cert.sh now
  re-copies it each pass). With a working certifier (wbI: 766 calls, certified 256 at head 288) the tail bound is gone and WBO's
  qualify then ends "conversation-deadline" at the declaration's 120 s limit (61 ops, ~2 s per hosted op: a Host-turn cost for
  host-execution/perf, not a declaration bug; limits.seconds 300 is allowed). With certification at min-tail 128 in the middle of an op:
  "lifetime payer plan changed at current verified image" (native/resource-client/src/agent_reserve/lifetime_v3/paid.rs:350).
  RULING (host-execution a24974e84d3c540d1): the plan stays valid across moved images. paid.rs:350 must compare the re-invoked plan with
  pinned.plan modulo the image coordinates (each SigningPlan's worldRoot and height, and equivalent app-plan fields) and require
  every slot (header and message), request, bindings, grant, grantRoot, grantObservationSlot and reserveReceipt equal; never
  re-sign on a moved image. If awkward client-side, ask host-execution for a Host-side canonical "signed part" projection.
  OWED NEXT. Also check wbH's "grant op75 returned an invalid frame" against the same cause.
- Law-10 fixes landed: 147b98259 (controller refusal decode), a1e69615f (op76 sentence; printed no words in wbE).
- Hummingbird (run hbA, role 1): attach and the first socket.io steps pass; the beacon GET sends `referer` and the controller refuses
  "application API header is outside native ordinary-header profile". The header list is closed in Host/HostOperations.lean
  (ordinaryHeaderNames), Kernel/ApplicationDispatchAdmission.lean:140, native/spk-rpc/src/web.rs and grain-runtime
  application_api_tools ORDINARY_HEADERS. Root's ruling: admit `referer` only as a same-origin path-only value (same grain origin: pass the path; otherwise drop it silently, never refuse). LANDED 7ac9217f2: the Lean statement (refererValueOk, ordinaryHeaderOk, theorems with teeth), registry and generated twins, lane-check green. OWED: the sender in grain-runtime (reduce a same-origin referer to its path and drop any other before signing; add referer to ORDINARY_HEADERS; the origin comes from the route/attachment), spk-rpc web.rs ordinary list, and the Host value check in dispatch_web_input; then rerun Hummingbird (run hbA).
- Runner on hbox: /home/hbox/lanes/app-reds-cont/ar-cycle.sh SUF DECL ALIAS ROLE SPK (pool tree t2 to origin/main, rust roles, overlay on
  candidate 9dc9c138c, ar-hrun.sh run); overlays under lane/ov2; packages in spk/; evidence /ci/j-{sbB,wbA,wbB,hbA}.

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
