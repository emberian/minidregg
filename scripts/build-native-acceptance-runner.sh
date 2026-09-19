#!/usr/bin/env bash
# Compile the public CLI probe as a native executable against a linked host's
# exact object closure. Run in the same independent snapshot as that host.

set -euo pipefail

usage() {
  cat <<'EOF'
usage: scripts/build-native-acceptance-runner.sh --host-response FILE --output DIR [--driver-source FILE]

The response file must come from scripts/build-native-host.sh in this snapshot.
The driver defaults to scripts/probe-native-host-cli.lean in this snapshot.
Host.Main's entry object is replaced by the compiled AcceptanceMain entry.
EOF
}

host_response=""
output_dir=""
driver_source=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --host-response)
      [[ $# -ge 2 ]] || { usage >&2; exit 64; }
      host_response=$2
      shift 2
      ;;
    --output)
      [[ $# -ge 2 ]] || { usage >&2; exit 64; }
      output_dir=$2
      shift 2
      ;;
    --driver-source)
      [[ $# -ge 2 ]] || { usage >&2; exit 64; }
      driver_source=$2
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      printf 'unknown argument: %s\n' "$1" >&2
      usage >&2
      exit 64
      ;;
  esac
done

[[ -n "$host_response" && -n "$output_dir" ]] || { usage >&2; exit 64; }
for command in git lake file nm shasum; do
  command -v "$command" >/dev/null 2>&1 || {
    printf 'required command not found: %s\n' "$command" >&2
    exit 69
  }
done

root=$(git rev-parse --show-toplevel)
cd "$root"
[[ -f .minidregg-native-snapshot ]] || {
  printf 'independent-snapshot marker missing: %s/.minidregg-native-snapshot\n' "$root" >&2
  exit 73
}
[[ -f "$host_response" ]] || { printf 'missing response file: %s\n' "$host_response" >&2; exit 66; }
if [[ -z "$driver_source" ]]; then
  driver_source="$root/scripts/probe-native-host-cli.lean"
fi
[[ -f "$driver_source" ]] || { printf 'missing driver source: %s\n' "$driver_source" >&2; exit 66; }
if [[ -e "$output_dir" ]]; then
  printf 'refusing existing output directory: %s\n' "$output_dir" >&2
  exit 73
fi
mkdir -p "$output_dir"
output_dir=$(cd "$output_dir" && pwd -P)

host_object=.lake/build/ir/Host/Main.c.o.export
[[ $(grep -cxF "$host_object" "$host_response") == 1 ]] || {
  printf 'response must contain exactly one %s\n' "$host_object" >&2
  exit 65
}
[[ -f "$host_object" ]] || { printf 'missing host main object: %s\n' "$host_object" >&2; exit 66; }

# Lake's --setup selects package-prefixed C symbols (lp_minidregg_*), while
# direct `lake env lean -c` selects unprefixed symbols (l_*). Match the host
# object actually present in this snapshot; mixing them fails at link time.
lean_setup_args=()
if nm -gU "$host_object" | grep -q ' T _initialize_minidregg_Host_Main$'; then
  command -v jq >/dev/null 2>&1 || { printf 'jq is required for Lake-setup host objects\n' >&2; exit 69; }
  host_setup=.lake/build/ir/Host/Main.setup.json
  [[ -f "$host_setup" ]] || { printf 'missing Lake host setup: %s\n' "$host_setup" >&2; exit 66; }
  driver_setup="$output_dir/AcceptanceMain.setup.json"
  jq '.name = "AcceptanceMain"' "$host_setup" > "$driver_setup"
  lean_setup_args=(--setup "$driver_setup")
  printf 'package_namespace=minidregg\n' > "$output_dir/driver-abi.txt"
elif nm -gU "$host_object" | grep -q ' T _initialize_Host_Main$'; then
  printf 'package_namespace=unprefixed\n' > "$output_dir/driver-abi.txt"
else
  printf 'unrecognized Host.Main initializer ABI\n' >&2
  exit 65
fi

cycle_dir=${MINIDREGG_CYCLE_DIR:-/tmp/minidregg-cycle-20260919}
lean_threads=${MINIDREGG_LEAN_THREADS:-2}
case "$lean_threads" in 1|2) ;; *) printf 'MINIDREGG_LEAN_THREADS must be 1 or 2\n' >&2; exit 64 ;; esac
mkdir -p "$cycle_dir"
seat_dir=""
release_seat() {
  if [[ -n "$seat_dir" ]]; then
    rmdir "$seat_dir" 2>/dev/null || true
    seat_dir=""
  fi
}
on_exit() {
  code=$?
  trap - EXIT HUP INT TERM
  release_seat
  exit "$code"
}
for seat_number in 1 2; do
  candidate="$cycle_dir/lean-seat-$seat_number"
  if mkdir "$candidate" 2>/dev/null; then
    seat_dir=$(cd "$candidate" && pwd -P)
    break
  fi
done
[[ -n "$seat_dir" ]] || { printf 'both Lean compiler seats are occupied\n' >&2; exit 75; }
trap on_exit EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

# The basename fixes Lean's generated module/entry symbol while preserving the
# complete source bytes; the source hash is recorded beside the executable.
cp "$driver_source" AcceptanceMain.lean
shasum -a 256 "$driver_source" AcceptanceMain.lean > "$output_dir/driver-source-sha256.txt"
env LEAN_NUM_THREADS="$lean_threads" lake env lean AcceptanceMain.lean \
  -o .lake/build/lib/lean/AcceptanceMain.olean \
  -i .lake/build/lib/lean/AcceptanceMain.ilean \
  -c .lake/build/ir/AcceptanceMain.c \
  "${lean_setup_args[@]}" --json > "$output_dir/driver-lean.log" 2>&1
release_seat
trap - EXIT HUP INT TERM

toolchain=$(lake env lean --print-prefix)
driver_object=.lake/build/ir/AcceptanceMain.c.o.export
"$toolchain/bin/clang" -c -o "$driver_object" .lake/build/ir/AcceptanceMain.c \
  -I "$toolchain/include" -fstack-clash-protection -fdata-sections \
  -ffunction-sections -fvisibility=hidden -Wno-unused-command-line-argument \
  --sysroot "$toolchain" -nostdinc -isystem "$toolchain/include/clang" \
  -O3 -DNDEBUG -DLEAN_EXPORTING > "$output_dir/driver-c.log" 2>&1
nm -gU "$driver_object" | grep -q ' T _main$' || {
  printf 'compiled driver did not export main\n' >&2
  exit 66
}
if [[ ${#lean_setup_args[@]} -gt 0 ]]; then
  nm -gU "$driver_object" | grep -q ' T _initialize_minidregg_AcceptanceMain$' || {
    printf 'driver object does not use the host Lake package ABI\n' >&2
    exit 66
  }
else
  nm -gU "$driver_object" | grep -q ' T _initialize_AcceptanceMain$' || {
    printf 'driver object does not use the host direct-compiler ABI\n' >&2
    exit 66
  }
fi

response="$output_dir/native-acceptance-runner.rsp"
awk -v host="$host_object" '$0 != host {print}' "$host_response" > "$response"
printf '%s\n' "$driver_object" >> "$response"
[[ $(wc -l < "$response" | tr -d ' ') == $(wc -l < "$host_response" | tr -d ' ') ]] || {
  printf 'runner response object count differs from host response\n' >&2
  exit 65
}
binary="$output_dir/native-acceptance-runner"
/usr/bin/time -lp "$toolchain/bin/leanc" -o "$binary" "@$response" > "$output_dir/link.log" 2>&1
set +e
"$binary" > "$output_dir/usage.txt" 2>&1
usage_exit=$?
set -e
grep -q 'usage: lean --run scripts/probe-native-host-cli.lean' "$output_dir/usage.txt" || {
  printf 'linked driver did not print its usage contract\n' >&2
  exit 70
}
file "$binary" > "$output_dir/file.txt"
shasum -a 256 "$binary" "$response" "$driver_object" > "$output_dir/artifact-sha256.txt"
if [[ ${#lean_setup_args[@]} -gt 0 ]]; then
  shasum -a 256 "$driver_setup" >> "$output_dir/artifact-sha256.txt"
fi
{
  printf 'root=%s\n' "$root"
  printf 'driver_source=%s\n' "$driver_source"
  printf 'driver_source_sha256=%s\n' "$(shasum -a 256 AcceptanceMain.lean | awk '{print $1}')"
  printf 'host_response=%s\n' "$host_response"
  printf 'host_response_sha256=%s\n' "$(shasum -a 256 "$host_response" | awk '{print $1}')"
  cat "$output_dir/driver-abi.txt"
  printf 'response_objects=%s\n' "$(wc -l < "$response" | tr -d ' ')"
  printf 'usage_exit=%s\n' "$usage_exit"
  printf 'binary=%s\n' "$binary"
  printf 'binary_sha256=%s\n' "$(shasum -a 256 "$binary" | awk '{print $1}')"
} | tee "$output_dir/manifest.txt"
