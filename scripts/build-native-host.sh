#!/usr/bin/env bash
# Build the Lean-owned native host with explicit bounds and reproducible evidence.
#
# Run this from an independent snapshot.  In particular, .lake/packages must not
# contain writable symlinks into another checkout: Lake may populate a missing
# native artifact while resolving the executable closure.

set -euo pipefail

usage() {
  cat <<'EOF'
usage: scripts/build-native-host.sh [--umbrella] [--output DIR] [--binary PATH]

  --umbrella  run the literal `lake build Minidregg` gate through a serialized
              Lean wrapper, build Host.Main leanArts, then link the native host
  --binary    output executable path (default: .lake/build/bin/minidregg-host)

Environment:
  MINIDREGG_NATIVE_ALLOW_SHARED=1  permit a tree without the snapshot marker
  MINIDREGG_NATIVE_JOBS=1|2        concurrent C compiler processes (default: 2)
  MINIDREGG_LEAN_THREADS=1|2       threads in each serialized Lean process (default: 2)
  MINIDREGG_CYCLE_DIR=DIR          seat/evidence parent (default below /tmp)
EOF
}

output_dir=""
binary_path=""
build_umbrella=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --umbrella)
      build_umbrella=1
      shift
      ;;
    --output)
      [[ $# -ge 2 ]] || { usage >&2; exit 64; }
      output_dir=$2
      shift 2
      ;;
    --binary)
      [[ $# -ge 2 ]] || { usage >&2; exit 64; }
      binary_path=$2
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      printf 'build-native-host: unknown argument: %s\n' "$1" >&2
      usage >&2
      exit 64
      ;;
  esac
done

for command in git jq lake file find sort join comm xargs shasum uname; do
  command -v "$command" >/dev/null 2>&1 || {
    printf 'build-native-host: required command not found: %s\n' "$command" >&2
    exit 69
  }
done

root=$(git rev-parse --show-toplevel)
cd "$root"

case "$(uname -s):$(uname -m)" in
  Darwin:arm64) native_object_description='Mach-O 64-bit object arm64' ;;
  Linux:x86_64) native_object_description='ELF 64-bit LSB relocatable, x86-64' ;;
  *)
    printf 'build-native-host: unsupported native target: %s %s\n' \
      "$(uname -s)" "$(uname -m)" >&2
    exit 69
    ;;
esac

binary=${binary_path:-.lake/build/bin/minidregg-host}
if [[ -e "$binary" || -L "$binary" ]]; then
  printf 'build-native-host: refusing to replace existing binary: %s\n' "$binary" >&2
  exit 73
fi

snapshot_marker="$root/.minidregg-native-snapshot"
if [[ ! -f "$snapshot_marker" && "${MINIDREGG_NATIVE_ALLOW_SHARED:-0}" != 1 ]]; then
  printf '%s\n' \
    "build-native-host: missing independent-snapshot marker: $snapshot_marker" \
    'create it only inside a copied tree, or set MINIDREGG_NATIVE_ALLOW_SHARED=1' \
    'only during an agreed integration freeze' >&2
  exit 73
fi

native_jobs=${MINIDREGG_NATIVE_JOBS:-2}
lean_threads=${MINIDREGG_LEAN_THREADS:-2}
case "$native_jobs" in 1|2) ;; *) printf 'MINIDREGG_NATIVE_JOBS must be 1 or 2\n' >&2; exit 64 ;; esac
case "$lean_threads" in 1|2) ;; *) printf 'MINIDREGG_LEAN_THREADS must be 1 or 2\n' >&2; exit 64 ;; esac

cycle_dir=${MINIDREGG_CYCLE_DIR:-/tmp/minidregg-cycle-20260919}
mkdir -p "$cycle_dir/build"
if [[ -z "$output_dir" ]]; then
  output_dir="$cycle_dir/build/native-host-$(date -u +%Y%m%dT%H%M%SZ)"
fi
if [[ -e "$output_dir" ]]; then
  printf 'build-native-host: refusing existing output directory: %s\n' "$output_dir" >&2
  exit 73
fi
mkdir -p "$output_dir/lean" "$output_dir/c"
output_dir=$(cd "$output_dir" && pwd -P)

symlink_report="$output_dir/package-symlinks.txt"
find .lake/packages -maxdepth 1 -type l -print > "$symlink_report"
if [[ -s "$symlink_report" ]]; then
  printf 'build-native-host: package symlinks are not isolated; see %s\n' "$symlink_report" >&2
  exit 73
fi

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
on_signal() {
  code=$1
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
if [[ -z "$seat_dir" ]]; then
  printf 'build-native-host: both Lean compiler seats are occupied under %s\n' "$cycle_dir" >&2
  exit 75
fi
trap on_exit EXIT
trap 'on_signal 129' HUP
trap 'on_signal 130' INT
trap 'on_signal 143' TERM

start_epoch=$(date +%s)
printf 'start_utc=%s\nroot=%s\nlean_threads=%s\nnative_jobs=%s\nseat=%s\n' \
  "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$root" "$lean_threads" "$native_jobs" "$seat_dir" \
  > "$output_dir/build.log"

# `transImports` is a nonbuildable Lake facet: it parses source headers and
# recursively combines module names.  Do not substitute `:deps`; that setup
# facet fetches import artifacts and can fan out compilers.
closure="$output_dir/transitive-imports.json"
env LEAN_NUM_THREADS="$lean_threads" \
  lake --reconfigure query +Host.Main:transImports --json \
  > "$closure" 2> "$output_dir/transitive-imports.log"
jq -e 'type == "array" and length > 0' "$closure" >/dev/null

source_modules="$output_dir/source-modules.txt"
: > "$source_modules"
jq -r '.[]' "$closure" | while IFS= read -r module; do
  relative=${module//./\/}.lean
  [[ -f "$relative" ]] && printf '%s\n' "$module"
done > "$source_modules"
grep -qxF Host.Main "$source_modules" || printf '%s\n' Host.Main >> "$source_modules"

build_modules="$output_dir/build-modules.txt"
if [[ "$build_umbrella" == 1 ]]; then
  umbrella_closure="$output_dir/umbrella-transitive-imports.json"
  env LEAN_NUM_THREADS="$lean_threads" \
    lake query +Minidregg:transImports --json \
    > "$umbrella_closure" 2> "$output_dir/umbrella-transitive-imports.log"
  jq -e 'type == "array" and length > 0' "$umbrella_closure" >/dev/null
  umbrella_modules="$output_dir/umbrella-source-modules.txt"
  jq -r '.[]' "$umbrella_closure" | while IFS= read -r module; do
    relative=${module//./\/}.lean
    [[ -f "$relative" ]] && printf '%s\n' "$module"
  done > "$umbrella_modules"
  grep -qxF Minidregg "$umbrella_modules" || printf '%s\n' Minidregg >> "$umbrella_modules"
  awk '!seen[$0]++' "$umbrella_modules" "$source_modules" > "$build_modules"
else
  cp "$source_modules" "$build_modules"
fi

# Lake silently omits imports that are not members of a declared library.  That
# produced a Host.Main closure without Host.Json once.  Refuse every such local
# edge before the expensive build instead of linking an incomplete executable.
unregistered="$output_dir/unregistered-local-imports.txt"
: > "$unregistered"
# The nested grep and the outer loop both read the immutable module list.
# shellcheck disable=SC2094
# Validate the complete compilation list.  `source_modules` remains the exact
# native link closure; `build_modules` additionally carries the umbrella gate.
while IFS= read -r module; do
  source=${module//./\/}.lean
  sed -nE \
    's/^[[:space:]]*((public|meta)[[:space:]]+)*import[[:space:]]+(all[[:space:]]+)?([A-Za-z_][A-Za-z0-9_.]*).*/\4/p' \
    "$source" | while IFS= read -r imported; do
      imported_source=${imported//./\/}.lean
      if [[ -f "$imported_source" ]] && ! grep -qxF "$imported" "$build_modules"; then
        printf '%s\t%s\n' "$module" "$imported" >> "$unregistered"
      fi
    done
done < "$build_modules"
if [[ -s "$unregistered" ]]; then
  printf 'build-native-host: Lake omitted locally resolvable imports; see %s\n' "$unregistered" >&2
  exit 65
fi

if [[ "$build_umbrella" == 0 ]]; then
  index=0
  total=$(wc -l < "$build_modules" | tr -d ' ')
  while IFS= read -r module; do
    index=$((index + 1))
    safe=${module//./_}
    log="$output_dir/lean/$(printf '%04d' "$index")-$safe.log"
    one_start=$(date +%s)
    printf 'lean[%s/%s] %s start\n' "$index" "$total" "$module" | tee -a "$output_dir/build.log"
    source=${module//./\/}.lean
    stem=${module//./\/}
    mkdir -p ".lake/build/lib/lean/$(dirname "$stem")" ".lake/build/ir/$(dirname "$stem")"
    if env LEAN_NUM_THREADS="$lean_threads" lake env lean "$source" \
        -o ".lake/build/lib/lean/$stem.olean" \
        -i ".lake/build/lib/lean/$stem.ilean" \
        -c ".lake/build/ir/$stem.c" --json > "$log" 2>&1; then
      printf 'lean[%s/%s] %s PASS %ss\n' \
        "$index" "$total" "$module" "$(( $(date +%s) - one_start ))" | tee -a "$output_dir/build.log"
    else
      code=$?
      printf 'lean[%s/%s] %s FAIL(%s) log=%s\n' \
        "$index" "$total" "$module" "$code" "$log" | tee -a "$output_dir/build.log" >&2
      tail -100 "$log" >&2
      exit "$code"
    fi
  done < "$build_modules"
fi

if [[ "$build_umbrella" == 1 ]]; then
  # Lake 5 has no scheduler-width field in BuildConfig and no CLI jobs flag.
  # Keep the literal repository gate while bounding it externally: Lake itself
  # is one Lean process and this wrapper admits at most one real Lean compiler.
  # The fake sysroot points all libraries back at the real immutable toolchain,
  # but substitutes the serialized wrapper for bin/lean.
  toolchain=$(lake env lean --print-prefix)
  wrapper_root="$output_dir/serialized-lean-toolchain"
  wrapper_lock="$output_dir/lake-lean-serial.lock"
  mkdir -p "$wrapper_root/bin"
  ln -s "$toolchain/include" "$wrapper_root/include"
  ln -s "$toolchain/lib" "$wrapper_root/lib"
  ln -s "$toolchain/src" "$wrapper_root/src"
  while IFS= read -r executable; do
    name=${executable##*/}
    [[ "$name" == lean ]] || ln -s "$executable" "$wrapper_root/bin/$name"
  done < <(find "$toolchain/bin" -maxdepth 1 -type f -print)
  cat > "$wrapper_root/bin/lean" <<'EOF'
#!/usr/bin/env bash
set -u
: "${MINIDREGG_REAL_LEAN:?}"
: "${MINIDREGG_LEAN_LOCK:?}"
: "${MINIDREGG_LEAN_WRAPPER_LOG:?}"

while ! mkdir "$MINIDREGG_LEAN_LOCK" 2>/dev/null; do
  sleep 0.1
done

child=""
cleanup() {
  rmdir "$MINIDREGG_LEAN_LOCK" 2>/dev/null || true
}
forward_signal() {
  signal=$1
  [[ -z "$child" ]] || kill -"$signal" "$child" 2>/dev/null || true
}
trap cleanup EXIT
trap 'forward_signal HUP' HUP
trap 'forward_signal INT' INT
trap 'forward_signal TERM' TERM

printf 'START\t%s\t%s\t' "$(date +%s)" "$$" >> "$MINIDREGG_LEAN_WRAPPER_LOG"
printf '%q ' "$@" >> "$MINIDREGG_LEAN_WRAPPER_LOG"
printf '\n' >> "$MINIDREGG_LEAN_WRAPPER_LOG"
"$MINIDREGG_REAL_LEAN" "$@" &
child=$!
set +e
wait "$child"
code=$?
set -e
printf 'END\t%s\t%s\t%s\n' "$(date +%s)" "$$" "$code" >> "$MINIDREGG_LEAN_WRAPPER_LOG"
exit "$code"
EOF
  chmod +x "$wrapper_root/bin/lean"
  wrapper_log="$output_dir/lake-lean-wrapper.tsv"
  : > "$wrapper_log"
  lake_gate_log="$output_dir/lake-build-Minidregg.log"
  cat > "$output_dir/lake-build-Minidregg.command.txt" <<EOF
LAKE_OVERRIDE_LEAN=true LEAN_SYSROOT=$wrapper_root LEAN_NUM_THREADS=$lean_threads lake build Minidregg
EOF
  gate_start=$(date +%s)
  printf 'lake-gate Minidregg start\n' | tee -a "$output_dir/build.log"
  if env \
      LAKE_OVERRIDE_LEAN=true \
      LEAN_SYSROOT="$wrapper_root" \
      LEAN_CC="$toolchain/bin/clang" \
      LEAN_AR="$toolchain/bin/llvm-ar" \
      LEAN_NUM_THREADS="$lean_threads" \
      MINIDREGG_REAL_LEAN="$toolchain/bin/lean" \
      MINIDREGG_LEAN_LOCK="$wrapper_lock" \
      MINIDREGG_LEAN_WRAPPER_LOG="$wrapper_log" \
      lake build Minidregg > "$lake_gate_log" 2>&1; then
    printf 'lake-gate Minidregg PASS %ss\n' \
      "$(( $(date +%s) - gate_start ))" | tee -a "$output_dir/build.log"
  else
    code=$?
    printf 'lake-gate Minidregg FAIL(%s) log=%s\n' \
      "$code" "$lake_gate_log" | tee -a "$output_dir/build.log" >&2
    tail -100 "$lake_gate_log" >&2
    exit "$code"
  fi

  # `leanArts` invokes Lean with -o/-i/-c.  Build the executable's separate
  # Host library through the same wrapper after the literal umbrella gate; the
  # resulting C files feed the native link below without a duplicate source pass.
  host_gate_log="$output_dir/lake-build-Host.Main-leanArts.log"
  cat > "$output_dir/lake-build-Host.Main-leanArts.command.txt" <<EOF
LAKE_OVERRIDE_LEAN=true LEAN_SYSROOT=$wrapper_root LEAN_NUM_THREADS=$lean_threads lake build +Host.Main:leanArts
EOF
  gate_start=$(date +%s)
  printf 'lake-gate Host.Main:leanArts start\n' | tee -a "$output_dir/build.log"
  if env \
      LAKE_OVERRIDE_LEAN=true \
      LEAN_SYSROOT="$wrapper_root" \
      LEAN_CC="$toolchain/bin/clang" \
      LEAN_AR="$toolchain/bin/llvm-ar" \
      LEAN_NUM_THREADS="$lean_threads" \
      MINIDREGG_REAL_LEAN="$toolchain/bin/lean" \
      MINIDREGG_LEAN_LOCK="$wrapper_lock" \
      MINIDREGG_LEAN_WRAPPER_LOG="$wrapper_log" \
      lake build +Host.Main:leanArts > "$host_gate_log" 2>&1; then
    printf 'lake-gate Host.Main:leanArts PASS %ss\n' \
      "$(( $(date +%s) - gate_start ))" | tee -a "$output_dir/build.log"
  else
    code=$?
    printf 'lake-gate Host.Main:leanArts FAIL(%s) log=%s\n' \
      "$code" "$host_gate_log" | tee -a "$output_dir/build.log" >&2
    tail -100 "$host_gate_log" >&2
    exit "$code"
  fi

  if ! awk -F '\t' '
    $1 == "START" { if (active) exit 1; active = 1; starts++ }
    $1 == "END" { if (!active) exit 1; active = 0; ends++ }
    END { if (active || starts == 0 || starts != ends) exit 1 }
  ' "$wrapper_log"; then
    printf 'build-native-host: serialized Lean wrapper log is unbalanced: %s\n' \
      "$wrapper_log" >&2
    exit 70
  fi
  printf 'max_concurrent_real_lean=1\nwrapper_invocations=%s\n' \
    "$(grep -c '^START' "$wrapper_log")" > "$output_dir/lake-wrapper-summary.txt"
fi

# The seat covers compiler invocations, not bounded pure-C work.
release_seat
trap - EXIT HUP INT TERM

toolchain=$(lake env lean --print-prefix)
clang="$toolchain/bin/clang"
leanc="$toolchain/bin/leanc"
compile_args="$output_dir/compile-args.txt"
cat > "$compile_args" <<EOF
-I $toolchain/include
-fstack-clash-protection
-fdata-sections
-ffunction-sections
-fvisibility=hidden
-Wno-unused-command-line-argument
--sysroot $toolchain
-nostdinc
-isystem $toolchain/include/clang
-O3
-DNDEBUG
-DLEAN_EXPORTING
EOF

export toolchain output_dir
# This single-quoted text is the child bash body, not parent interpolation.
# shellcheck disable=SC2016
xargs -P "$native_jobs" -n 1 bash -c '
  set -euo pipefail
  module=$1
  stem=${module//./\/}
  c_path=".lake/build/ir/$stem.c"
  object="$c_path.o.export"
  [[ -f "$c_path" ]] || { printf "missing generated C: %s\n" "$c_path" >&2; exit 66; }
  mkdir -p "$(dirname "$object")"
  "$toolchain/bin/clang" -c -o "$object" "$c_path" \
    -I "$toolchain/include" -fstack-clash-protection -fdata-sections \
    -ffunction-sections -fvisibility=hidden -Wno-unused-command-line-argument \
    --sysroot "$toolchain" -nostdinc -isystem "$toolchain/include/clang" \
    -O3 -DNDEBUG -DLEAN_EXPORTING \
    > "$output_dir/c/${module//./_}.log" 2>&1
' build-module < "$source_modules"

package_required="$output_dir/package-modules.txt"
jq -r '.[]' "$closure" | while IFS= read -r module; do
  relative=${module//./\/}.lean
  [[ -f "$relative" ]] || printf '%s\n' "$module"
done | sort -u > "$package_required"

make_package_index() {
  find .lake/packages -type f -path '*/.lake/build/ir/*.c.o.export' -print | awk '
    {
      path=$0
      marker="/.lake/build/ir/"
      pos=index(path, marker)
      if (!pos) next
      rel=substr(path, pos + length(marker))
      sub(/\.c\.o\.export$/, "", rel)
      module=rel
      gsub(/\//, ".", module)
      print module "\t" path
    }
  ' | sort
}

package_index="$output_dir/package-object-index.tsv"
make_package_index > "$package_index"
cut -f1 "$package_index" | sort -u > "$output_dir/package-object-modules.txt"
comm -12 "$package_required" <(cut -f1 "$package_index" | uniq -d) \
  > "$output_dir/ambiguous-package-objects.txt"
if [[ -s "$output_dir/ambiguous-package-objects.txt" ]]; then
  printf 'build-native-host: ambiguous package object modules; see %s\n' \
    "$output_dir/ambiguous-package-objects.txt" >&2
  exit 65
fi

comm -23 "$package_required" "$output_dir/package-object-modules.txt" \
  > "$output_dir/missing-package-objects.txt"
missing_package_c="$output_dir/missing-package-c-paths.nul"
: > "$missing_package_c"
while IFS= read -r module; do
  [[ -n "$module" ]] || continue
  relative=${module//./\/}
  c_matches="$output_dir/candidates-${module//./_}.txt"
  find .lake/packages -type f -path "*/.lake/build/ir/$relative.c" -print > "$c_matches"
  count=$(wc -l < "$c_matches" | tr -d ' ')
  if [[ "$count" != 1 ]]; then
    printf 'build-native-host: %s generated-C candidates for missing object %s; see %s\n' \
      "$count" "$module" "$c_matches" >&2
    exit 66
  fi
  c_path=$(sed -n '1p' "$c_matches")
  printf '%s\0' "$c_path" >> "$missing_package_c"
done < "$output_dir/missing-package-objects.txt"
if [[ -s "$missing_package_c" ]]; then
  # The single-quoted child body expands task-specific variables in bash.
  # shellcheck disable=SC2016
  xargs -0 -P "$native_jobs" -n 1 bash -c '
    set -euo pipefail
    c_path=$1
    object="$c_path.o.export"
    module=${c_path#*/.lake/build/ir/}
    module=${module%.c}
    "$toolchain/bin/clang" -c -o "$object" "$c_path" \
      -I "$toolchain/include" -fstack-clash-protection -fdata-sections \
      -ffunction-sections -fvisibility=hidden -Wno-unused-command-line-argument \
      --sysroot "$toolchain" -nostdinc -isystem "$toolchain/include/clang" \
      -O3 -DNDEBUG -DLEAN_EXPORTING \
      > "$output_dir/c/package-${module//\//_}.log" 2>&1
  ' build-package < "$missing_package_c"
fi

make_package_index > "$package_index"
package_objects_tsv="$output_dir/package-objects.tsv"
join -t $'\t' -1 1 -2 1 "$package_required" "$package_index" > "$package_objects_tsv"
if [[ $(wc -l < "$package_objects_tsv" | tr -d ' ') != $(wc -l < "$package_required" | tr -d ' ') ]]; then
  printf 'build-native-host: package object resolution remained incomplete\n' >&2
  exit 66
fi
cut -f2 "$package_objects_tsv" > "$output_dir/package-objects.txt"

file -f "$output_dir/package-objects.txt" > "$output_dir/package-object-types.txt"
grep -vF "$native_object_description" "$output_dir/package-object-types.txt" \
  > "$output_dir/wrong-architecture-package-objects.txt" || true
while IFS=: read -r object _description; do
  object=${object%%[[:space:]]*}
  [[ -n "$object" ]] || continue
  c_path=${object%.o.export}
  [[ -f "$c_path" ]] || {
    printf 'build-native-host: wrong-architecture object has no generated C: %s\n' "$object" >&2
    exit 66
  }
  "$clang" -c -o "$object" "$c_path" \
    -I "$toolchain/include" -fstack-clash-protection -fdata-sections \
    -ffunction-sections -fvisibility=hidden -Wno-unused-command-line-argument \
    --sysroot "$toolchain" -nostdinc -isystem "$toolchain/include/clang" \
    -O3 -DNDEBUG -DLEAN_EXPORTING
done < "$output_dir/wrong-architecture-package-objects.txt"
file -f "$output_dir/package-objects.txt" > "$output_dir/package-object-types-final.txt"
if grep -vF "$native_object_description" "$output_dir/package-object-types-final.txt" \
    > "$output_dir/wrong-architecture-package-objects-final.txt"; then
  printf 'build-native-host: package objects remain incompatible after recompilation; see %s\n' \
    "$output_dir/wrong-architecture-package-objects-final.txt" >&2
  exit 66
fi

response="$output_dir/minidregg-host.rsp"
: > "$response"
while IFS= read -r module; do
  stem=${module//./\/}
  printf '%s\n' ".lake/build/ir/$stem.c.o.export" >> "$response"
done < "$source_modules"
cat "$output_dir/package-objects.txt" >> "$response"

# Recheck immediately before linking in case another process created the path.
if [[ -e "$binary" || -L "$binary" ]]; then
  printf 'build-native-host: refusing to replace existing binary: %s\n' "$binary" >&2
  exit 73
fi
mkdir -p "$(dirname "$binary")"
binary="$(cd "$(dirname "$binary")" && pwd -P)/$(basename "$binary")"
/usr/bin/time -p "$leanc" -o "$binary" "@$response" > "$output_dir/link.log" 2>&1

set +e
"$binary" > "$output_dir/usage.txt" 2>&1
usage_exit=$?
set -e
grep -q '^minidregg-host:' "$output_dir/usage.txt" || {
  printf 'build-native-host: linked binary did not print its usage contract\n' >&2
  exit 70
}

while IFS= read -r module; do
  source=${module//./\/}.lean
  shasum -a 256 "$source"
done < "$build_modules" > "$output_dir/source-sha256.txt"
shasum -a 256 "$binary" "$response" "$closure" > "$output_dir/artifact-sha256.txt"
if [[ "$build_umbrella" == 1 ]]; then
  shasum -a 256 "$umbrella_closure" >> "$output_dir/artifact-sha256.txt"
fi
git status --short > "$output_dir/git-status.txt"
{
  printf 'end_utc=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf 'elapsed_seconds=%s\n' "$(( $(date +%s) - start_epoch ))"
  printf 'git_head=%s\n' "$(git rev-parse HEAD)"
  printf 'root=%s\n' "$root"
  printf 'lean=%s\n' "$(lean --version | sed -n '1p')"
  printf 'toolchain=%s\n' "$toolchain"
  printf 'native_target=%s:%s\n' "$(uname -s)" "$(uname -m)"
  printf 'umbrella=%s\n' "$build_umbrella"
  if [[ "$build_umbrella" == 1 ]]; then
    printf 'lake_gate=lake build Minidregg\n'
    printf 'max_concurrent_real_lean=1\n'
    printf 'wrapper_invocations=%s\n' "$(grep -c '^START' "$wrapper_log")"
  fi
  printf 'compiled_source_modules=%s\n' "$(wc -l < "$build_modules" | tr -d ' ')"
  printf 'source_modules=%s\n' "$(wc -l < "$source_modules" | tr -d ' ')"
  printf 'package_modules=%s\n' "$(wc -l < "$package_required" | tr -d ' ')"
  printf 'response_objects=%s\n' "$(wc -l < "$response" | tr -d ' ')"
  printf 'usage_exit=%s\n' "$usage_exit"
  printf 'binary=%s\n' "$binary"
  printf 'binary_sha256=%s\n' "$(shasum -a 256 "$binary" | awk '{print $1}')"
} > "$output_dir/manifest.txt"
cat "$output_dir/manifest.txt" | tee -a "$output_dir/build.log"
