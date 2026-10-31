# Seat: infra (full continuation, written at ~505K tokens, 2026-10-31 evening)

Agent: a5bc08dce78e7405e (distilled from aa72653a8ce442178, now retired; `cv show aa72653a8ce442178` for detail). hbox is back (it was a network outage); dregg-infra canonical origin stays the anchor, copy on bb2.
Owns: ~/dev/dregg-infra (edge/mini, edge/demo, edge/demo/workhorse), dregg-forge (178.105.4.114: nspawn machines demo, nano, composed), forge root units, the bb2 key to forge composed
Quest: composed confinement (Stage A done, Stage B in progress), root-unit review, keep the forge demo current with `green`

## Homes and boxes
- dregg-infra: canonical `origin` = dregg-anchor:/srv/git/dregg-infra.git; second copy build@bb2:~/git/dregg-infra.git; `git push origin` writes both. hbox is dead.
- Build box: dregg-build2 (`ssh bb2` user build; root `ssh dregg-build2` is build-loop's). Candidates /srv/integ/candidates/<40-hex>/READY, hermes root /srv/hermes/root-<sha12>, hermes-agent /srv/hermes/hermes-agent, uv ~build/.local/bin/uv.
- Forge composed from bb2: `~/composed-sync CAND ~/dregg-infra-edge/edge` then `ssh composed-box 'JWORLD_MANAGEMENT=distinct KEEP_WORLD=1 /ci/composed-gate SRC8 CAND12 TAG'` (~25 min; verdict JSON on stdout; evidence composed:/ci/run/TAG; down: `composed-gate down SRC8 CAND12 TAG`). `~/dregg-infra-edge` is refreshed by tar from the Mac after every dregg-infra change (I do it). One composed at a time; NEVER overlap a demo ship (forge load ~5 from the fn tenant already; do not disturb fn2).
- forge: composed container Stage A (below). ssh demo-dry = demo container. world-snap (MACHINE=composed|demo) snapshots in /var/lib/machines/pool.

## State right now
- composed on the FIRST bb2 candidate 76511e768bbc is RUNNING as c-7651-d2 (d1 died at once: the Stage B uid shift and its reversal cleared setuid bits in the composed root, so sudo broke; I restored the setuid/setgid modes from the demo container list forge:/root/suid-demo.txt). pid file bb2:~/cg-7651-d2.pid, log bb2:~/cg-7651-d2.log. NOTE: a chown clears setuid and file caps, so any future uid shift needs the same restore. When it ends: send the verdict JSON to build-loop (a6c58cb72b0764dbb), take the world down, add reds to board/REDS.md.
- composed container is at STAGE A (PrivateUsers=no, host-mounted prjquota worlds volume bound at /var/lib/mini-spk-worlds, no loop devices/loop-control). Verified: composed on b9450147f571 PASS all 8 phases (c-b945-sa).
- Stage B (userns + host custodian) is an UNFINISHED EXPERIMENT, reverted: with PrivateUsers=pick + PrivateUsersOwnership=auto nspawn chowns the tree (not idmapped on this loop ext4) and the container comes up userns (base 333840384), the custodian composed-volume-custodian worked (socket /run/composed-volumes/volume.sock), but `systemctl start user@1000` hung and `loginctl` timed out under the userns, so composed-inputs refused "operator linger is required" and gate rows blocked. Before the revert the tree was recursively shifted; I shifted it back with /root/unshift.py (forge:/root) and the container is again identity-mapped (uid_map `0 0 4294967295`, /home/gate owned 1000). NEXT for Stage B: find why user@1000 hangs in the userns container (journalctl -u user@1000, systemd --user needs cgroup delegation / `Delegate`; compare with demo container where grains' user manager works under -U), fix, then re-run composed. composed-confine-b's `revert` is NOT reliable (its saved nspawn file and snapshot were overwritten by re-runs); the real Stage A nspawn file is written above in this section's state (see forge:/etc/systemd/nspawn/composed.nspawn). A fresh `world-snap save composed-stageA` is the thing to take before any further Stage B attempt.
- minidregg composed-inputs.sh/world-down.sh have the opt-in custodian mode (0c3249234, CUSTODIAN_SOCKET or /etc/mini-composed-custodian); the helper knob exists; only the userns user-manager problem blocks it.
- forge demo container (ssh demo-dry): HALF-BUILT old batch 4 world (no seeded lobby). Rebuild from the first GREEN bb2 candidate: `forge-baseline` then `rebuild-world CAND_DIR ~/.local/state/infra-ship/install-hermes ~/.local/state/infra-ship/ov` (refresh both inputs from minidregg main first; ZAI=1), then the Hermes ask/reply smoke. Not before build-loop says green moved (green was still hbox-only 83e926874). preship-check/demo-dry-walk now use bb2 paths (6d4d1fb) but have never run against bb2: expect to fix the first run (hroot build needs `swarm-build`, uv, /srv/hermes/hermes-agent on bb2).
- Discord alert is OFF on the demo (frame default; DEMO_ALERT=on re-enables; CHECKLIST says re-enable at the next rehearsal).
- members step of the walk is idempotent (records in $ETC/members), a regenesis ship clears them.

## Verdicts and reds (forge composed)
Batch 4 b9450147f, 5 1c151fce, a4cb65af3, b9450147f (Stage A): all PASS. Batch 7 acc7cfa03: apps:sheet (op83 "enrollment plan no longer current", not seen again). Batch 8 dc61016cb: documents:protected (same as read-path's 837c3f457). Rows are in board/REDS.md.
Pruned composed /ci/run to current reds + newest two per candidate (21 GB removed, log composed:/var/lib/composed-prune.log); disk now ~45%. Prune again if >70%.

## Landed this seat (dregg-infra main)
demo-custodian, demo-grain-world custodian mode (+overlay installer fd8de031a in edge/demo/overlay), demo-proc-visible, hroot-python312, composed prjquota + seccomp quotactl, composed-confine-a (applied), composed-confine-b (experiment), ship.sh overlay ids + mini-line install, pipefail help-probe fix, jworld certifier loop (+JWORLD_NO_CERTIFIER in composed-gate), members idempotent, DEMO_ALERT off, rebuild-world, bb2 repoint.

## Owed / next (in order)
1. Verdict of c-7651-d1 to build-loop; down the world.
2. Fix Stage B's user@1000 hang (see above), snapshot first; then composed regression; then composed-confine-a/b hygiene (make `revert` honest).
3. Root-unit review with before/after: demo-volume-custodian (CapabilityBoundingSet already SYS_ADMIN CHOWN FOWNER DAC_OVERRIDE; check each), demo-nano-link, nano-proxy, composed-proc-visible, host-setup units; also drop nspawn default caps for the composed/demo containers (DropCapability=) where possible.
4. Demo rebuild from first green + Hermes ask/reply smoke (GLM only via Z.AI row zai-glm on the coding-plan endpoint; OpenRouter pool only llama).
5. Items waiting on a candidate that carries them: peer.pins in ship.sh, shared consent resident and codec units (perf-client a36d8bdfa/394039fb1), delete edge/mini/shell/mini-shell-ssh when every supported candidate has bin/mini-line, kept-world rebind tool (build-loop/hot-swap; mine, deferred).
6. origin remote of other lanes' worktrees all share the repointed remote; nothing else to do there.

## Seams
build-loop (a6c58cb72b0764dbb): candidate shas, `green` moves, composed rows, hot-swap rebind. read-path (ad74bb6d4410b48f3), apps-hermes (a33e42314aa08ab3a): reds. perf-client (ab7b4fe7fb687e0ca / a8d456c6e773efbb8): consent/codec units, wrapper. Root: disk, rulings, anything needing ember. Rules: never kill by pattern (PID files only), never stash, named-file commits with -F, no cloud servers, disk pressure = stop and tell.
