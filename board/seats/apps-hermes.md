# Seat: apps-hermes

Agent: a990f9e07566fd55c (fresh from this file 2026-10-31 23:00Z; predecessors afb920b22b17049cd and a33e42314aa08ab3a, `cv show` for detail)
Owns: grain-runtime, spk-host, the apps worker, Hermes controller and gateway, route and conversation declarations, refusal rendering
Work areas: Mac worktree /Users/ember/dev/minidregg-lanes/apps-hermes; hbox /home/hbox/lanes/app-reds-cont (pool tree t2, target/)
Quest: Hermes final say (H1b), live Hummingbird/WBO/Scrumblr qualification, refusals name their clause

## Landed on main
- 8bfffe590 referer, sender and twins. The generator (scripts/host-operations.py) emits `referer_value_ok` and
  `ordinary_header_ok` (twins of Lean refererValueOk/ordinaryHeaderOk; `check` pins the Lean body) and the one sender
  reduction `same_origin_referer(value, authority)`: a path passes; an http(s) URL of the grain's own authority becomes
  its path and query; anything else is dropped, never refused.
  - Senders: the browser entrance (against the request Host), app-interface bindings (mini-sdk) and the controller
    (grain-runtime parse_input; its hand-copied ORDINARY_HEADERS is deleted).
  - Readers: both agent API wire decoders, dispatch_web_input (a non-path referer is refused naming refererValueOk) and
    spk-rpc's WebSession whitelist.
  - Hummingbird's `url` is typed as a same-origin path (pattern), and its qualify uses "/analytics/<runId>".
  - Tests: mini-sdk referer_tests and a_declared_referer..., grain-runtime application_api_tools (25), spk-host (39
    filtered, on hbox).
  - Without this, 7ac9217f2's generated name list let the browser entrance sign full-URL referers that Lean refuses.
- 7acbdd878 plans stay valid across a moved image (host-execution's ruling). Kernel/SigningPlanImage.lean `imageFree`
  clears a SigningPlan's worldRoot and height (theorems: fixes everything else; moved image is rfl; slot-change teeth).
  - PaidPlan.imageFree and the inspection field `imageFreePlanHex`. Both paid.rs re-checks (payer and seal) compare it
    when the bytes differ. No re-signing.
  - The same fix for op75 grant assembleCurrent (wbH's red) and for all three session-enrollment assembleCurrent* (op83,
    infra's batch-7 apps:sheet red); each assembles `fresh`.
  - op75's refusal was marker 253, read as "invalid frame". resource-client `reply_or_outcome` names any Host outcome
    with its words (op75, op78 re-checks).
  - spk-host logs `op-timing opN reply=R ms=T` per Host turn and the session-tool ms.
  - lane-check green on hbox for all five Lean files; resource-client tests (15) and spk-host tests pass.
- Earlier (predecessors): H1b cause and fix f3d8f3fa5; START reds fda2e4193; refusal sweep; route paths byte-exact with
  one trailing "/" admitted on conversation paths (1c670cee5, e46759f4e); channel ids 37 chars (9dc9c138c); attach roleId
  allAccess; controller refusal decode 147b98259; op76 words a1e69615f; op66 shapeClause 90fba62e4; referer statement
  7ac9217f2.

## Live qualification state
- Scrumblr: qualify PASSES (hbox run sbB). Keep it passing.
- Hummingbird (hbA): blocked on the referer, now landed. Rerun needs a Host built from main >= 7acbdd878. The Lean
  admission changed, so the 9dc9c138c overlay is not enough.
- WBO (wbA..wbJ): the certifier works (harness re-copies workspace.json each pass). The payer-plan red and the op75 red
  are fixed in 7acbdd878. Remaining: conversation-deadline at the declaration's 120 s (61 hosted ops at about 2 s each;
  one op is about 1 s of reserve plan and submit plus about 1 s of paid plan, signatures, op76 and committed, at
  journald 1 s resolution). Next run gives the op-timing ms split; send it to host-execution with numbers.
  limits.seconds 300 is allowed if the per-op cost stays.
- Packages: forge /var/lib/spk-fresh/apps/wbo-r2/out/wbo.spk; /srv/spk-build/scrumblr/out/scrumblr-0.5-1.spk;
  /srv/spk-build/hummingbird/out/hummingbird-0.4.1-api.spk; copies in hbox app-reds-cont/spk/.
- Runner: /home/hbox/lanes/app-reds-cont/ar-cycle.sh SUF DECL ALIAS ROLE SPK overlays rust roles on a candidate (edit
  its candidate path to the builder's newest candidate under /home/hbox/lanes/integ/candidates once one contains
  7acbdd878); ar-hrun.sh runs the j14-apps qualify; evidence in /ci/j-<SUF>.
- hbox test note: run spk-host dispatch_native tests under `umask 022` (fixtures refuse group-writable config).

## Next
1. When the builder has a candidate >= 7acbdd878: rerun Scrumblr, Hummingbird (hbB) and WBO (wbK). Collect op-timing
   and send WBO's per-op split to host-execution (a24974e84d3c540d1).
2. op76 "printed no words" in wbE: check it with reply naming now in place.
3. op66 shape clause from one install; `mini apps install` measurement on a main-built world.
4. Then E3/E4, E7, decider side of G2 (app-create Host-turn costs are host-execution's).

## Seams
- host-execution (a24974e84d3c540d1): Lean Host files touched in 7acbdd878 (theirs to read). FnConsumerFrontierPlan and
  FnConsumerNamespacePlan have the same whole-plan compare (left to them).
- member-side (ab7b4fe7fb687e0ca): resource-client files touched in 7acbdd878. share_issue and grain_share_issue
  `expect_reply` still treat only 255 as an outcome.
