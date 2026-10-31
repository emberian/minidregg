# Seat: infra

Agent: aa72653a8ce442178 (this seat; ~390K tokens at 2026-10-31 evening)
Owns: ~/dev/dregg-infra (edge/mini, edge/demo, edge/demo/workhorse), dregg-forge (178.105.4.114: demo, nano, composed nspawn machines), the root units on forge
Quest: composed confinement Stage A then B; root-unit review; keep the forge demo current with `green`

## State
- forge demo container (`ssh demo-dry`): HALF-BUILT batch 4 b9450147f world (ship green, grain world on, three apps running earlier);
  the repair left it without a seeded lobby (members step is not idempotent: "feedback-me.json File exists"). Next: ONE fresh rebuild
  from `green` (`dregg-infra edge/demo/workhorse/forge-baseline` then `rebuild-world CANDIDATE_DIR PRETTY_HERMES SEED_OVERLAY`, ZAI=1).
  The Discord alert is OFF on the box and in the frame (DEMO_ALERT=on re-enables; CHECKLIST says re-enable at the next rehearsal).
- (hbox is down: every hbox path in dregg-infra scripts was repointed to bb2 in 6d4d1fb.)
- forge composed (the builder's row, run through me): `composed-sync CAND EDGE` then `composed-gate SRC8 CAND12 TAG` on the composed machine.
  Verdicts: batch 4 b9450147f, batch 5 1c151fce, a4cb65af3: all PASS. acc7cfa03 (batch 7): apps FAIL (apps:sheet same-Store app).
  dc61016cb (batch 8): documents FAIL (documents:protected, no stderr, evidence c-dc61-d1/.../0117-d), apps/connector/residents/restart PASS, store-restart blocked.
  Kept worlds of those two runs are down. Never run composed and a demo ship together on forge (fn user's ACL2 builds already hold load ~5).
- Disk: composed machine root 79% (47 of 59 GB), /ci/run holds 33 GB of old gate evidence (c-4159-*, c-f34b-*, ...). Root: tell me which to delete; I have not.

## dregg-infra homes (2026-10-31, after hbox died)
- Canonical `origin` = dregg-anchor:/srv/git/dregg-infra.git (fetch). Second copy: dregg-build2 `build@bb2:~/git/dregg-infra.git`. `git push origin` pushes BOTH (two pushurls).
  All 17 local branches and tags were pushed to both; main and demo-vm verified identical on local, anchor and bb2 (6d4d1fb / 0ef191b). hbox:/srv/git/dregg-infra.git is dead; nothing points at it.
- No git checkouts of dregg-infra exist on forge or bb2 (they hold copies of edge/ only: bb2:~/dregg-infra-edge, refreshed by tar from the Mac).
- The build box is dregg-build2 (`ssh bb2`, user build): candidates /srv/integ/candidates/<sha>, forge composed via bb2:~/composed-sync + `ssh composed-box` (key ~/.ssh/composed_gate_id, restricted on forge).

## Landed (dregg-infra main)
demo-custodian (host-side volume custodian wiring), demo-grain-world custodian mode (+overlay installer fd8de031a), demo-proc-visible unit, hroot-python312,
composed prjquota worlds + seccomp quotactl allowance, ship.sh overlay ids and mini-line install, pipefail help-probe fix, DEMO_ALERT off, rebuild-world,
composed-confine-a (Stage A, written, NOT applied).

## Next
1. Fresh demo rebuild from green (quiet-host wait threshold must tolerate fn's load ~5), Hermes ask/reply smoke (GLM via Z.AI row zai-glm only).
2. Stage A: `workhorse/composed-confine-a apply` then a composed rerun before calling it done; Stage B (userns + custodian for composed) coordinating the
   CUSTODIAN_SOCKET knob with build-loop; then the root-unit review (custodian, demo-nano-link, nano-proxy, composed-proc-visible, host-setup units) with before/after.
3. batch 8+ items: peer.pins in ship.sh, shared consent resident / codec units (perf-client a36d8bdfa), delete edge/mini/shell/mini-shell-ssh when no candidate lacks bin/mini-line.

## Seams needed
build-loop (a6c58cb72b0764dbb): the `green` candidate dir name on hbox and when to run forge composed. app-reds: dc61 documents:protected owner. member-side (perf-client): units above.
