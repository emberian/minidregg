#!/usr/bin/env bash
# scripts/burst/remote/check.sh [--tip SHA] [--role gate|lane] [--journeys] [--srv /srv] [--expect-swarm FILE]
# -- does THIS box match what burst-up promises? One `ok`/`DIFF` row per expectation, exit = DIFF count.
# Run on a hand-built box it is the behaviour diff the root asked for; run after burst-up it is the proof.
set -uo pipefail
SRV=/srv tip="" role="" journeys=0 expect_swarm="" single=0 nohbox=0
while [ $# -gt 0 ]; do case "$1" in --tip) tip=$2; shift 2 ;; --role) role=$2; shift 2 ;; --journeys) journeys=1; shift ;; --srv) SRV=$2; shift 2 ;; --expect-swarm) expect_swarm=$2; shift 2 ;; --single) single=1; shift ;; --no-hbox) nohbox=1; shift ;; *) echo "check: unknown $1" >&2; exit 64 ;; esac; done
export PATH=$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.bun/bin:$PATH
ndiff=0; ok() { printf 'ok    %-22s %s\n' "$1" "${2:-}"; }; diff() { printf 'DIFF  %-22s %s\n' "$1" "$2"; ndiff=$((ndiff+1)); }
have() { command -v "$1" >/dev/null 2>&1; }
echo "== burst-check $(hostname) $(date -u +%FT%TZ)"
for p in fuser lsof flock rsync zstd jq capnp git curl earlyoom rrsync bwrap rg sqlite3 bc xxd; do have $p && ok "pkg:$p" || diff "pkg:$p" "missing"; done
[ "$(capnp --version 2>/dev/null)" = "Cap'n Proto version 1.5.0" ] && ok capnp-1.5.0 || diff capnp-1.5.0 "$(capnp --version 2>&1)"
systemctl is-active -q earlyoom && ok earlyoom || diff earlyoom inactive
loginctl show-user "$USER" -p Linger 2>/dev/null | grep -q yes && ok linger || diff linger "no linger for $USER"
sudo -n true 2>/dev/null && ok sudo-nopasswd || diff sudo-nopasswd "sudo asks"
mountpoint -q "$SRV" && ok "srv-mount" "$(df -h "$SRV" | awk 'NR==2{print $4" free"}')" || diff srv-mount "$SRV is not a mountpoint"
if [ -x /usr/local/bin/swarm-build ]; then
  if [ -n "$expect_swarm" ]; then cmp -s /usr/local/bin/swarm-build "$expect_swarm" && ok swarm-build "repo copy" || diff swarm-build "differs from the repo's scripts/burst/swarm-build"; fi
  grep -q 'swarm-${tag}-\$\$' /usr/local/bin/swarm-build && ok swarm-build:named-scopes || diff swarm-build:named-scopes "anonymous run-r*.scope"
else diff swarm-build missing; fi
ram=$(awk '/MemTotal/ {printf "%d", $2/1024/1024}' /proc/meminfo); cap=$(sed -n 's/^MemoryMax=\([0-9]*\)G/\1/p' ~/.config/systemd/user/swarm.slice.d/50-memcap.conf 2>/dev/null)
[ -n "$cap" ] && [ "$cap" -ge $((ram*70/100)) ] && [ "$cap" -le $((ram*90/100)) ] && ok swarm.slice "${cap}G of ${ram}G" || diff swarm.slice "cap ${cap:-none}G of ${ram}G (want 70-90%)"
for t in elan lake lean cargo rustc bun; do have $t && ok "tool:$t" || diff "tool:$t" missing; done
[ -d "$SRV/mini/.git" ] && ok repo "$SRV/mini at $(git -C "$SRV/mini" rev-parse --short HEAD)" || diff repo "no $SRV/mini"
[ -n "$tip" ] && { [ "$(git -C "$SRV/mini" rev-parse HEAD 2>/dev/null)" = "$tip" ] && ok repo-tip || diff repo-tip "$(git -C "$SRV/mini" rev-parse --short HEAD 2>/dev/null) != ${tip:0:8}"; }
grep -q 'pipeline/box.env' ~/.profile && ok profile:box.env || diff profile:box.env "~/.profile does not source box.env"
grep -q 'PIPELINE_SLOT_[12]=' ~/.profile && diff profile:old-slots "PIPELINE_SLOT_1/2 still exported" || ok profile:old-slots
[ -f "$SRV/pipeline/box.env" ] && ok box.env || diff box.env missing
if [ -f "$SRV/pipeline/box.env" ]; then . "$SRV/pipeline/box.env"
  for s in $PIPELINE_SLOTS ${PIPELINE_SMALL_SLOTS:-} ${PIPELINE_GATE_SLOTS:-}; do [ -e "$s" ] && [ "$(stat -c %a "$s")" = 666 ] || diff "slot:$(basename "$s")" "missing or not 0666"; done; ok slots-exist "$(echo $PIPELINE_SLOTS | wc -w) lane, $(echo ${PIPELINE_SMALL_SLOTS:-} | wc -w) small, $(echo ${PIPELINE_GATE_SLOTS:-} | wc -w) gate"
  thr=$(nproc); n=$(echo $PIPELINE_SLOTS | wc -w); [ $(( n * LEAN_NUM_THREADS )) -ge $(( thr * 8 / 10 )) ] && [ $(( n * LEAN_NUM_THREADS )) -le $(( thr * 13 / 10 )) ] && ok slots-sized "$n x $LEAN_NUM_THREADS threads for $thr" || diff slots-sized "$n slots x $LEAN_NUM_THREADS threads vs $thr hardware threads"
  stray=$(ls "$SRV"/build-slot-* 2>/dev/null | grep -vxF -f <(printf '%s\n' $PIPELINE_SLOTS ${PIPELINE_SMALL_SLOTS:-} ${PIPELINE_GATE_SLOTS:-}) | tr '\n' ' '); [ -z "$stray" ] && ok slots-no-strays || diff slots-no-strays "slot files not in box.env: $stray"
  [ "$role" = gate ] && { [ -n "${PIPELINE_GATE_SLOTS:-}" ] && ok gate-slots "$PIPELINE_GATE_SLOTS" || diff gate-slots "none declared"; }
  [ -n "${PIPELINE_PEER:-}" ] && ok peer "$PIPELINE_PEER" || { [ "$single" = 1 ] && ok peer "(single box)" || diff peer "PIPELINE_PEER unset"; }
  echo "$PATH" | grep -q lake-shim && ok lake-shim || diff lake-shim "not on PATH via box.env"
fi
P=$SRV/pipeline/scripts
for f in lib.sh slot.sh slots build-anywhere peer-build box-peer-gate lane-check lean-ask mk-lane.sh publish-artifacts fetch-artifacts journey-runner install-sccache; do [ -x "$P/$f" ] || [ -f "$P/$f" ] || diff "script:$f" missing; done; ok scripts "$(ls "$P" | wc -l) files, from $(cat "$P/.installed-from" 2>/dev/null | cut -c1-8 || echo '? (hand-installed)')"
[ -f "$P/.installed-from" ] || diff scripts:provenance "no .installed-from (installed by hand or rsync, not burst-up)"
[ -x "$SRV/pipeline/candidate/lane-build.sh" ] && ok candidate-builder || diff candidate-builder missing
if [ -f "$SRV/warm-base/src/scripts/pipeline/mk-lane.sh" ]; then cmp -s "$SRV/warm-base/mk-lane.sh" "$SRV/warm-base/src/scripts/pipeline/mk-lane.sh" && ok mk-lane:one-copy "= the base tree's" || diff mk-lane:one-copy "$SRV/warm-base/mk-lane.sh != its tree's scripts/pipeline/mk-lane.sh"
else cmp -s "$SRV/warm-base/mk-lane.sh" "$P/mk-lane.sh" 2>/dev/null && ok mk-lane:one-copy || diff mk-lane:one-copy "$SRV/warm-base/mk-lane.sh != pipeline/scripts/mk-lane.sh"; fi
grep -q MK_LANE_PROBE "$SRV/warm-base/mk-lane.sh" 2>/dev/null && ok mk-lane:probe-aware || diff mk-lane:probe-aware "base mk-lane.sh predates MK_LANE_PROBE (an advance's verify would be refused)"
[ -x "$SRV/pipeline/repl/.lake/build/bin/repl" ] && ok lean-ask-repl || diff lean-ask-repl "not built"
[ -x "$SRV/pipeline/bin/sccache" ] && ok sccache-bin || diff sccache-bin missing
for u in pipeline-sccache pipeline-slots; do systemctl --user is-active -q $u.service && { systemctl --user is-enabled -q $u.service 2>/dev/null && ok "unit:$u" "active, enabled" || diff "unit:$u" "active but TRANSIENT/not enabled (lost on reboot)"; } || diff "unit:$u" "not active"; done
if [ "$role" = gate ]; then
  systemctl --user is-active -q pipeline-artifacts.service && ok unit:artifacts || { pgrep -f "scripts/artifact-watch" >/dev/null && diff unit:artifacts "runs in tmux, not a unit" || diff unit:artifacts "not running"; }
  systemctl --user is-active -q shared-remote-sync.timer && ok shared-remote-timer || diff shared-remote-timer inactive
  [ -d "$SRV/git/minidregg.git" ] && ok shared-remote "$(git -C "$SRV/git/minidregg.git" for-each-ref | wc -l) refs" || diff shared-remote "no $SRV/git/minidregg.git"
  [ -f "$SRV/artifacts/TIPS" ] && ok artifacts:TIPS || diff artifacts:TIPS missing
  [ -f ~/.ssh/pipeline_mirror ] && ok mirror-key || { [ "$single" = 1 ] && ok mirror-key "(single box)" || diff mirror-key "no ~/.ssh/pipeline_mirror"; }
  grep -q "_pull\|burst.*pull" ~/.ssh/authorized_keys 2>/dev/null && ok hbox-puller-authorized || { [ "$nohbox" = 1 ] && ok hbox-puller-authorized "(no --hbox)" || diff hbox-puller-authorized "hbox's read-only key is not in authorized_keys"; }
fi
if [ "$journeys" = 1 ]; then systemctl --user is-active -q pipeline-journeys.service && ok unit:journeys || { pgrep -f "scripts/journey-runner" >/dev/null && diff unit:journeys "runs in tmux, not a unit" || diff unit:journeys "not running"; }; fi
if [ "$single" = 1 ]; then ok peer-key "(single box)"; ok peer-authorized "(single box)"; else
[ -f ~/.ssh/box_peer ] && ok peer-key || diff peer-key "no ~/.ssh/box_peer"
grep -q 'box-peer-gate' ~/.ssh/authorized_keys 2>/dev/null && ok peer-authorized || diff peer-authorized "no sibling key forced to box-peer-gate"; fi
if [ -n "${PIPELINE_PEER:-}" ]; then out=$(timeout 20 ssh "$PIPELINE_PEER" slots --free 2>&1); case $? in 0|1) ok peer-gate:slots "$(echo "$out" | paste -sd, | cut -c1-60)" ;; *) diff peer-gate:slots "$out" ;; esac; fi
if [ -f "$SRV/warm-base/FROZEN" ]; then ft=$(sed -n 's/^tip=//p' "$SRV/warm-base/FROZEN"); [ -e "$SRV/warm-base/NOT-READY.txt" ] && diff warm-base "NOT-READY: $(cat "$SRV/warm-base/NOT-READY.txt" | cut -c1-80)" || ok warm-base "FROZEN ${ft:0:8}"
  [ -n "$tip" ] && { [ "$ft" = "$tip" ] && ok warm-base-tip || diff warm-base-tip "${ft:0:8} != ${tip:0:8}"; }
else diff warm-base "no FROZEN"; fi
(unset PIPELINE_SLOTS; "$P/slots" --free >/dev/null 2>&1; [ $? -le 1 ]) && ok slots-cmd "answers under a non-login shell" || diff slots-cmd "slots --free failed"
[ -d "$SRV/briefs" ] && [ -n "$(ls "$SRV/briefs" 2>/dev/null)" ] && ok briefs "$(ls "$SRV/briefs" | wc -l) files" || diff briefs "no $SRV/briefs"
[ -f "$SRV/SLOTS.txt" ] && ok SLOTS.txt || diff SLOTS.txt missing
echo "== burst-check $(hostname): $ndiff DIFF"; exit $ndiff
