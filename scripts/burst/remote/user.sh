#!/usr/bin/env bash
# scripts/burst/remote/user.sh -- the USER phase of burst-up, run ON the box as the login user (idempotent).
#
#   bash user.sh --tip SHA --stage /tmp/burst-up [--srv /srv] [--origin U@H] [--mirrors 'U@H ...'] [--peer ALIAS]
#                [--fetch-from ALIAS] [--spk FILE] [--sccache-port N] [--role gate|lane] [--journeys]
#
# From the staged repo copy ($STAGE = this checkout's scripts/burst, scripts/pipeline, deploy/candidate):
#   toolchains (elan at the tip's lean-toolchain, rustup at rust-toolchain.toml, bun pinned), $SRV/mini at TIP,
#   git identity, ~/.profile (PATH + `. box.env`), the pipeline scripts to $SRV/pipeline/scripts (what
#   scripts/pipeline/install does, from the staged copy), the candidate builder, the lean-ask REPL, sccache
#   (binary + env + a PERSISTENT user service), box.env from $SRV/burst/slots.env + the topology flags,
#   the slot watcher as a persistent service, the shared remote + its sync timer (gate role), the publisher
#   (gate) / journey runner (--journeys) as persistent services, the SPK package, the briefs ($STAGE/briefs).
set -euo pipefail
tip="" STAGE="" SRV=/srv origin="" mirrors="" peer="" from="" spk="" port=4226 role=lane journeys=0
while [ $# -gt 0 ]; do
  case "$1" in
    --tip) tip=$2; shift 2 ;; --stage) STAGE=$2; shift 2 ;; --srv) SRV=$2; shift 2 ;; --origin) origin=$2; shift 2 ;;
    --mirrors) mirrors=$2; shift 2 ;; --peer) peer=$2; shift 2 ;; --fetch-from) from=$2; shift 2 ;; --spk) spk=$2; shift 2 ;;
    --sccache-port) port=$2; shift 2 ;; --role) role=$2; shift 2 ;; --journeys) journeys=1; shift ;;
    *) echo "user.sh: unknown $1" >&2; exit 64 ;;
  esac
done
[[ $tip =~ ^[0-9a-f]{40}$ ]] || { echo "user.sh: --tip must be 40 hex" >&2; exit 64; }
[ -d "$STAGE/pipeline" ] && [ -d "$STAGE/burst" ] || { echo "user.sh: --stage DIR with pipeline/ burst/ candidate/" >&2; exit 64; }
. "$SRV/burst/slots.env"
export PIPELINE_ROOT=$SRV/pipeline ARTIFACT_ROOT=$SRV/artifacts JOURNEY_ROOT=$SRV/journeys
LOG=$SRV/burst/user-$(date -u +%Y%m%dT%H%M%SZ).log; exec > >(tee -a "$LOG") 2>&1
echo "== user phase $(date -Is) tip=$tip role=$role"
cd ~

# --- toolchains, pinned by the tip's own files ---
[ -x ~/.elan/bin/elan ] || curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
[ -x ~/.cargo/bin/rustup ] || curl -fsSL https://sh.rustup.rs | sh -s -- -y --default-toolchain stable --profile minimal
[ -x ~/.bun/bin/bun ] || curl -fsSL https://bun.sh/install | bash -s "bun-v1.3.11" >/dev/null
export PATH=$HOME/.bun/bin:$HOME/.elan/bin:$HOME/.cargo/bin:$PATH
git config --global user.name "ember arlynx"; git config --global user.email "cmrx64@gmail.com"; git config --global commit.gpgsign false

# --- the repo at TIP ---
[ -d "$SRV/mini/.git" ] || git clone -q https://github.com/emberian/minidregg.git "$SRV/mini"
git -C "$SRV/mini" cat-file -e "$tip^{commit}" 2>/dev/null || git -C "$SRV/mini" fetch -q origin "$tip" main next 2>/dev/null || git -C "$SRV/mini" fetch -q origin
git -C "$SRV/mini" checkout -q -B main "$tip"
elan toolchain install "$(cat "$SRV/mini/lean-toolchain")" 2>&1 | tail -1
rustup toolchain install "$(sed -n 's/^channel *= *"\(.*\)"/\1/p' "$SRV/mini/rust-toolchain.toml")" --profile minimal -c clippy -c rustfmt 2>&1 | tail -1

# --- profile: PATH + box.env (the one box-local file every script reads; a login shell gets it too) ---
grep -q '^# burst PATH' ~/.bashrc 2>/dev/null || { printf '# burst PATH (before the interactive guard)\nexport PATH=$HOME/.bun/bin:$HOME/.elan/bin:$HOME/.cargo/bin:$PATH\n' | cat - ~/.bashrc > ~/.bashrc.new && mv ~/.bashrc.new ~/.bashrc; }
grep -q 'bun/bin' ~/.profile 2>/dev/null || echo 'export PATH=$HOME/.bun/bin:$HOME/.elan/bin:$HOME/.cargo/bin:$PATH' >> ~/.profile
sed -i '/PIPELINE_SLOT_[12]=/d' ~/.profile
grep -q 'pipeline/box.env' ~/.profile || echo "[ -f $SRV/pipeline/box.env ] && . $SRV/pipeline/box.env   # slots, threads, sccache, lake cache (scripts/pipeline/box-env)" >> ~/.profile

# --- pipeline scripts + candidate builder, from the staged copy (what scripts/pipeline/install does) ---
mkdir -p "$PIPELINE_ROOT/scripts" "$PIPELINE_ROOT/candidate"
rsync -a --delete "$STAGE/pipeline/" "$PIPELINE_ROOT/scripts/"
rsync -a "$STAGE/candidate/lane-build.sh" "$STAGE/candidate/lib.sh" "$PIPELINE_ROOT/candidate/"
git -C "$SRV/mini" rev-parse HEAD > "$PIPELINE_ROOT/scripts/.installed-from"; echo "installed-from: $(cat "$PIPELINE_ROOT/scripts/.installed-from") (staged by burst-up)"
P=$PIPELINE_ROOT/scripts
# the warm base's mk-lane.sh is its OWN tree's scripts/pipeline/mk-lane.sh (advance/relay keep it so); refresh when it knows MK_LANE_PROBE
if [ -f "$SRV/warm-base/src/scripts/pipeline/mk-lane.sh" ] && grep -q MK_LANE_PROBE "$SRV/warm-base/src/scripts/pipeline/mk-lane.sh"; then
  install -m 755 "$SRV/warm-base/src/scripts/pipeline/mk-lane.sh" "$SRV/warm-base/.mk-lane.sh.new" && mv -f "$SRV/warm-base/.mk-lane.sh.new" "$SRV/warm-base/mk-lane.sh"
fi

# --- the persistent unit files first (install-sccache starts the persistent sccache unit when its file exists) ---
U=~/.config/systemd/user; mkdir -p "$U"
unit() { sed -e "s|@SRV@|$SRV|g" -e "s|@PORT@|$port|g" -e "s|@HOME@|$HOME|g" "$STAGE/burst/units/$1" > "$U/$1.new" && mv -f "$U/$1.new" "$U/$1"; }
unit pipeline-sccache.service; unit pipeline-slots.service
[ "$role" = gate ] && unit pipeline-artifacts.service; [ "$journeys" = 1 ] && unit pipeline-journeys.service
systemctl --user daemon-reload
# a TRANSIENT pipeline-sccache (install-sccache's own, pre-burst-up) must go before the persistent one can start
systemctl --user show pipeline-sccache.service -p FragmentPath 2>/dev/null | grep -q "/run/user" && systemctl --user stop pipeline-sccache.service 2>/dev/null || true
# --- sccache: binary + env; its server = the persistent unit (survives a reboot) ---
PIPELINE_SCCACHE_PORT=$port "$P/install-sccache" --cache-dir "$SRV/sccache" 2>&1 | tail -1

# --- box.env ---
args=(--slots "$BURST_LANE_SLOTS" --lean-threads "$BURST_LEAN_THREADS" --small-slots "$BURST_SMALL_SLOTS")
[ -n "$BURST_GATE_SLOTS" ] && args+=(--gate-slots "$BURST_GATE_SLOTS")
[ -n "$origin" ] && args+=(--origin "$origin"); [ -n "$mirrors" ] && args+=(--mirrors "$mirrors")
[ -n "$peer" ] && args+=(--peer "$peer"); [ -n "$from" ] && args+=(--fetch-from "$from")
if [ -n "$spk" ]; then install -m 644 "$spk" "$PIPELINE_ROOT/spk/$(basename "$spk")"; args+=(--spk "$PIPELINE_ROOT/spk/$(basename "$spk")"); fi
"$P/box-env" "${args[@]}" >/dev/null
. "$PIPELINE_ROOT/box.env"

# --- the lean-ask REPL (pinned to the tip's toolchain) ---
( cd "$SRV/mini" && "$P/lean-ask-install-repl" "$PIPELINE_ROOT/repl" 2>&1 | tail -1 )

# --- enable + (re)start the persistent units (they replace the transient scopes and tmux sessions) ---
want="pipeline-sccache.service pipeline-slots.service"
[ "$role" = gate ] && want="$want pipeline-artifacts.service"; [ "$journeys" = 1 ] && want="$want pipeline-journeys.service"
for u in $want; do systemctl --user enable -q "$u"; systemctl --user restart "$u"; done
sleep 1; for u in $want; do printf '%s: %s\n' "$u" "$(systemctl --user is-active "$u")"; done

# --- gate: the shared remote + its GitHub sync timer; a seed TIPS line ---
if [ "$role" = gate ]; then
  "$P/shared-remote" init 2>&1 | tail -1
  touch "$ARTIFACT_ROOT/TIPS"
fi

# --- briefs: what an agent on this box must read ---
if [ -d "$STAGE/briefs" ]; then rsync -a --delete "$STAGE/briefs/" "$SRV/briefs/"; echo "briefs: $(ls "$SRV/briefs" | wc -l) files in $SRV/briefs"; fi
echo "== user phase DONE $(date -Is)"
