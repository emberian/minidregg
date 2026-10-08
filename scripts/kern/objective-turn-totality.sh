#!/usr/bin/env bash
# Preserve the unchanged OB journeys' Stores and replay their admitted logs.
set -euo pipefail

usage() {
  cat <<'EOF'
usage: scripts/kern/objective-turn-totality.sh --bin BIN --manifest MANIFEST --runner EXE [--host HOST] [--consent CONSENT] [--root NEW_ROOT]
       scripts/kern/objective-turn-totality.sh --runner EXE --recorded ROOT

Produce and retain the seven OB journey worlds, then replay them with EXE.
ROOT defaults to a fresh short directory under this lane. MANIFEST identifies
the prebuilt base artifact set and is copied into the retained evidence.
--recorded rechecks retained Stores without running the journeys again.
An absent/empty row, failed journey, or refused turn fails the run.
Every journey and replay runs in a 10 GiB user scope with swap disabled.
EOF
}

src=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
bin= manifest= runner= root= recorded= host= consent=
while (($#)); do
  case $1 in
    --bin) bin=$2; shift 2 ;;
    --manifest) manifest=$2; shift 2 ;;
    --runner) runner=$2; shift 2 ;;
    --host) host=$2; shift 2 ;;
    --consent) consent=$2; shift 2 ;;
    --root) root=$2; shift 2 ;;
    --recorded) recorded=$2; shift 2 ;;
    --help|-h) usage; exit 0 ;;
    *) usage >&2; exit 2 ;;
  esac
done
[[ -n $runner && -x $runner ]] || { usage >&2; exit 2; }
if [[ -n $recorded ]]; then
  [[ -z $root && -z $bin && -z $manifest && -z $host && -z $consent ]] || { usage >&2; exit 2; }
  root=$(cd -- "$recorded" && pwd)
  [[ -s $root/stores.json ]] || { echo 'missing recorded stores manifest' >&2; exit 1; }
  replay=$(mktemp -d "$root/replay.XXXXXX")
  status=0
  if bash "$src/scripts/kern/replay-totality-stores.sh" "$runner" "$root/stores.json" "$replay/pole"; then
    [[ -s $root/journeys-ok ]] || status=1
  else
    status=$?
  fi
  exit "$status"
fi
[[ -n $bin && -d $bin && -n $manifest && -s $manifest ]] || { usage >&2; exit 2; }
bin=$(cd -- "$bin" && pwd)
if [[ -n $root ]]; then
  [[ ! -e $root && ! -L $root ]] || { echo 'root must be new' >&2; exit 2; }
  mkdir -m 700 -- "$root"
  root=$(cd -- "$root" && pwd)
else
  mkdir -p "$src/.lake"
  root=$(mktemp -d "$src/.lake/kp.XXXXXX")
fi
printf 'EVIDENCE %s\n' "$root"
cp -- "$manifest" "$root/artifact-manifest.json"
# Fetch paths may be replaced by another queued request. Journeys keep only
# private copies, so their Host/helper selection is stable for the whole run.
mkdir -m 700 -- "$root/bin"
for name in mini minidregg-host minidregg-link-sqlite-store \
    minidregg-credential-signature-verifier minidregg-client-consent \
    minidregg-client-consent-specialized; do
  source=$bin/$name
  if [[ $name == minidregg-host && -n $host ]]; then
    [[ -x $host ]] || { echo 'explicit Host is not executable' >&2; exit 2; }
    source=$host
  fi
  if [[ $name == minidregg-client-consent && -n $consent ]]; then
    [[ -x $consent ]] || { echo 'explicit consent provider is not executable' >&2; exit 2; }
    source=$consent
  fi
  if [[ -f $source ]]; then cp -L --reflink=auto -- "$source" "$root/bin/$name"; fi
done
bin=$root/bin
sha256sum "$bin"/* >"$root/artifact-sha256"
git -C "$src" rev-parse HEAD >"$root/source-head"
sha256sum "$src/Kernel/ObjectiveTurnTotalityRunner.lean" "$runner" >"$root/runner-sha256"
sha256sum "$src/Kernel/TurnOfIntent.lean" "$src/Kernel/World.lean" \
  "$src/Kernel/DeployedBridge.lean" >"$root/kernel-sha256"
rows=(activity objectrecord call send seats domain upgrade)
drivers=(objective-activity-native-acceptance.py objectrecord-native-journey.py
  objective-call-native-journey.py objective-send-native-journey.py
  objective-seat-native-acceptance.py objective-domain-native-journey.py
  objective-upgrade-native-journey.py)
status=0
entries=()
for i in "${!rows[@]}"; do
  row=${rows[$i]}
  journey=$src/native/resource-client/${drivers[$i]}
  # Journey roots remain short enough for their public UNIX sockets.
  unit="kp-$(basename "$root")-$row-$$"
  if systemd-run --user --scope --unit "$unit" -q -p MemoryMax=10G -p MemorySwapMax=0 \
      python3 "$journey" --bin "$bin" --root "$root/$row" \
      >"$root/$row.out" 2>"$root/$row.err"; then
    printf 'JOURNEY %s ok\n' "$row"
  else
    rc=$?
    scopeResult=$(systemctl --user show "$unit.scope" -p Result --value 2>/dev/null) || scopeResult=unavailable
    if [[ $rc == 137 || $scopeResult == oom-kill ]] || rg -q 'oom-kill|out of memory|Memory cgroup|killed by.*KILL|rc=-9|return(code)?[=: ]+-9' "$root/$row.err"; then
      printf 'JOURNEY %s oom\n' "$row" >&2
    else
      printf 'JOURNEY %s failed %s\n' "$row" "$rc" >&2
    fi
    status=1
  fi
  # Discover every pinned world, including drivers with more than one world.
  if [[ -d $root/$row ]]; then
    while IFS= read -r -d '' config; do
      entries+=("$(jq -cn --arg row "$row" --arg config "$config" '{row:$row,config:$config}')")
    done < <(find "$root/$row" -type f -name pinned-config.json -print0)
  fi
done
printf '%s\n' "${entries[@]}" | jq -s '.' >"$root/stores.json"
if [[ $status == 0 ]]; then printf 'all seven passed\n' >"$root/journeys-ok"; fi
if bash "$src/scripts/kern/replay-totality-stores.sh" "$runner" "$root/stores.json" \
    "$root/pole" >"$root/totality.out" 2>"$root/totality.err"; then
  printf 'POLE ok\n'
else
  rc=$?
  printf 'POLE failed %s\n' "$rc" >&2
  status=1
fi
cat "$root/totality.out"
cat "$root/totality.err" >&2
exit "$status"
