#!/usr/bin/env bash
# Build the Lean-owned native host with explicit bounds and reproducible evidence.
#
# Run this from an independent snapshot.  In particular, .lake/packages must not
# contain writable symlinks into another checkout: Lake may populate a missing
# native artifact while resolving the executable closure.

set -euo pipefail
# `comm` and `join -t TAB` compare module keys bytewise.  Use the same byte
# collation for every inventory producer and consumer, independent of the
# caller's locale (whose punctuation ordering can differ for parent modules).
export LC_ALL=C

usage() {
  cat <<'EOF'
usage: scripts/build-native-host.sh [--root MODULE --usage-prefix TEXT [--companion-of BUILD_OUTPUT]] [--umbrella [--umbrella-target MODULE]] [--incremental-host-from SNAPSHOT BUILD_OUTPUT] [--incremental-suffix-from SNAPSHOT BUILD_OUTPUT MODULE [--allow-suffix-change MODULE ...] [--allow-inserted-module MODULE ...] [--allow-unchanged-restart]] [--checkpoint-resume | --resume-failed BUILD_OUTPUT | --resume-complete-lean BUILD_OUTPUT BUILDER_SHA256 | --reuse-success-prefix-from SNAPSHOT BUILD_OUTPUT] [--output DIR] [--binary PATH]

  --umbrella  run the literal `lake build Minidregg` gate through the seated
              Lean wrapper, build Host.Main leanArts, then link the native host
  --umbrella-target MODULE
              with --umbrella: the Lake target of that step instead of Minidregg (the
              artifact publisher builds Host.Main: it links binaries of a tip the merge
              gate already judged, and the gate's umbrella is not its business; recorded
              as lake_gate= in the manifest). Repeat it to build several targets in one
              seated `lake build`
  --umbrella-only
              with --umbrella: stop after the seated umbrella step (no Host.Main leanArts,
              no link). The candidate's `umbrellas` stage elaborates the libraries no shipped
              root imports (Fixtures, ObjectiveProofs, CensusChecks) this way
  --incremental-host-from SNAPSHOT BUILD_OUTPUT
              compile only changed Host.Main after byte-checking every imported
              source, Lean artifact, and package artifact against a successful
              native build in an independent source snapshot; recompile all
              project C objects before linking
  --incremental-suffix-from SNAPSHOT BUILD_OUTPUT MODULE
              compile MODULE and every later source module in import order;
              verify the successful baseline, every earlier source/artifact,
              unchanged later sources, packages, and toolchain before reuse
  --allow-suffix-change MODULE
              require this additional later source to differ from the baseline;
              compile it in the suffix and reject any undeclared source change
  --allow-inserted-module MODULE
              require this module to be newly inserted in the native import
              closure at or after the suffix start; recompile the whole suffix
  --allow-unchanged-restart
              permit an unchanged suffix-start source only with an explicitly
              declared insertion later in the freshly computed closure
  --checkpoint-resume
              record full input and per-module checkpoints for a possible
              later failed-build resume; hashes large Lean library trees
  --resume-failed BUILD_OUTPUT
              resume the compiled prefix of a failed, non-umbrella full build
              in this same snapshot, only after checkpointed source, Lean,
              package, project, and toolchain hashes all still match
  --resume-complete-lean BUILD_OUTPUT BUILDER_SHA256
              recover a failed post-Lean link from a complete checkpointed
              Lean closure in the same snapshot. Verify every source, OLean,
              ILean, generated C and external input; allow only the named
              builder-script hash to change, then recompile all project C
              objects before package resolution and linking
  --reuse-success-prefix-from SNAPSHOT BUILD_OUTPUT
              in a new independent snapshot, reuse the longest topological
              prefix of a successful --checkpoint-resume build with an exact
              source/artifact and external-input qualification; compile every
              module from the first changed or inserted source onward
  --binary    output executable path (default: .lake/build/bin/minidregg-host)
  --root MODULE
              link the executable whose `main` is MODULE (default Host.Main);
              requires --usage-prefix; a non-Host.Main root also requires
              --binary and is exclusive with --umbrella and incremental modes
  --usage-prefix TEXT
              the linked executable, run without arguments, must print a line
              starting with TEXT (default `minidregg-host:`)
  --companion-of BUILD_OUTPUT
              a second executable from this SAME snapshot: reuse every closure
              module that BUILD_OUTPUT (a successful build of this root
              directory) compiled, after checking its source, OLean, ILean, C
              and object bytes against that build's manifests; any mismatch
              refuses. Modules outside that closure are compiled here

Environment:
  MINIDREGG_NATIVE_ALLOW_SHARED=1  permit a tree without the snapshot marker
  MINIDREGG_NATIVE_JOBS=N          concurrent C compiler processes (positive integer; default: 2)
  MINIDREGG_LEAN_THREADS=N         threads in each Lean process (positive integer; default: 2)
  MINIDREGG_LAKE_THREADS=N         Lake's worker threads, i.e. how many modules it runs at once before the
                                   seats bound them (default: 2 x MINIDREGG_LEAN_SEATS, at least 4)
  MINIDREGG_NATIVE_LAKE_CC=PATH    optional bounded compiler wrapper for Lake C jobs
  MINIDREGG_CYCLE_DIR=DIR          evidence parent (default below /tmp)
  MINIDREGG_LEAN_SEAT_ROOT=DIR     host-wide compiler seats (default /tmp/minidregg-lean-seats)
  MINIDREGG_LEAN_SEATS=N           host-wide compiler seats: at most N real Lean processes run at once on
                                   this host, across every build sharing MINIDREGG_LEAN_SEAT_ROOT (default: 2).
                                   The seats are the ONLY Lean concurrency bound: Lake builds the closure
                                   in parallel and each real Lean holds one seat while it runs.
  MINIDREGG_LEAN_SEAT_WAIT=S       seconds one Lean process waits for a free seat before it fails with 75
  MINIDREGG_LEAN_MEM_CAP=SIZE      the memory the seats share (default: the tightest cgroup memory.max this
                                   build runs under, e.g. swarm-build's scope; else SWARM_MEM_MAX, else 48G)
  MINIDREGG_LEAN_RSS_FROM=F[:F..]  further lean-module-rss.tsv tables (a previous build at this tip) merged
                                   with the tree's scripts/pipeline/lean-module-rss.tsv, per module the max.
                                   Seats are MEMORY-WEIGHTED: a module takes ceil(maxrss / (cap / seats))
                                   seats; a module with no recorded RSS takes all of them (heavy until
                                   measured); a module whose recorded RSS alone exceeds the cap refuses.
                                   (default 7200; 0 = refuse at once)
EOF
}

output_dir=""
binary_path=""
build_umbrella=0
umbrella_targets=()
umbrella_only=0
incremental_baseline_root=""
incremental_baseline_output=""
incremental_changed_module=""
incremental_suffix_mode=0
suffix_allowed_modules=()
inserted_modules=()
allow_unchanged_restart=0
resume_failed_output=""
resume_complete_output=""
resume_complete_builder_sha=""
checkpoint_resume=0
success_baseline_root=""
success_baseline_output=""
root_module=Host.Main
usage_prefix='minidregg-host:'
root_given=0
usage_given=0
companion_output=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --umbrella)
      build_umbrella=1
      shift
      ;;
    --umbrella-target)
      [[ $# -ge 2 && "$2" =~ ^[A-Z][A-Za-z0-9_.]*$ ]] || { usage >&2; exit 64; }
      umbrella_targets+=("$2")
      shift 2
      ;;
    --umbrella-only)
      umbrella_only=1
      shift
      ;;
    --incremental-host-from)
      [[ $# -ge 3 ]] || { usage >&2; exit 64; }
      [[ -z "$incremental_baseline_root" ]] || { usage >&2; exit 64; }
      incremental_baseline_root=$2
      incremental_baseline_output=$3
      incremental_changed_module=Host.Main
      shift 3
      ;;
    --incremental-suffix-from)
      [[ $# -ge 4 ]] || { usage >&2; exit 64; }
      [[ -z "$incremental_baseline_root" ]] || { usage >&2; exit 64; }
      incremental_baseline_root=$2
      incremental_baseline_output=$3
      incremental_changed_module=$4
      incremental_suffix_mode=1
      shift 4
      ;;
    --allow-suffix-change)
      [[ $# -ge 2 && -n "$2" ]] || { usage >&2; exit 64; }
      for allowed in "${suffix_allowed_modules[@]+"${suffix_allowed_modules[@]}"}"; do
        [[ "$allowed" != "$2" ]] || {
          printf 'build-native-host: duplicate suffix change: %s\n' "$2" >&2
          exit 64
        }
      done
      suffix_allowed_modules+=("$2")
      shift 2
      ;;
    --allow-inserted-module)
      [[ $# -ge 2 && -n "$2" ]] || { usage >&2; exit 64; }
      for inserted in "${inserted_modules[@]+"${inserted_modules[@]}"}"; do
        [[ "$inserted" != "$2" ]] || {
          printf 'build-native-host: duplicate inserted module: %s\n' "$2" >&2
          exit 64
        }
      done
      inserted_modules+=("$2")
      shift 2
      ;;
    --allow-unchanged-restart)
      allow_unchanged_restart=1
      shift
      ;;
    --resume-failed)
      [[ $# -ge 2 && -z "$resume_failed_output" ]] || { usage >&2; exit 64; }
      resume_failed_output=$2
      checkpoint_resume=1
      shift 2
      ;;
    --resume-complete-lean)
      [[ $# -ge 3 && -z "$resume_complete_output" &&
         "$3" =~ ^[[:xdigit:]]{64}$ ]] || { usage >&2; exit 64; }
      resume_complete_output=$2
      resume_complete_builder_sha=$3
      checkpoint_resume=1
      shift 3
      ;;
    --checkpoint-resume)
      checkpoint_resume=1
      shift
      ;;
    --reuse-success-prefix-from)
      [[ $# -ge 3 && -z "$success_baseline_root" ]] || { usage >&2; exit 64; }
      success_baseline_root=$2
      success_baseline_output=$3
      checkpoint_resume=1
      shift 3
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
    --root)
      [[ $# -ge 2 && "$2" =~ ^[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)+$ && "$root_given" == 0 ]] \
        || { usage >&2; exit 64; }
      root_module=$2
      root_given=1
      shift 2
      ;;
    --usage-prefix)
      [[ $# -ge 2 && -n "$2" && "$usage_given" == 0 ]] || { usage >&2; exit 64; }
      usage_prefix=$2
      usage_given=1
      shift 2
      ;;
    --companion-of)
      [[ $# -ge 2 && -z "$companion_output" ]] || { usage >&2; exit 64; }
      companion_output=$2
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
[[ ${#umbrella_targets[@]} -gt 0 ]] || umbrella_targets=(Minidregg)
umbrella_target="${umbrella_targets[*]}"
umbrella_tag=$(printf %s "$umbrella_target" | tr " " "+")
if [[ "$umbrella_only" == 1 && "$build_umbrella" != 1 ]]; then
  printf 'build-native-host: --umbrella-only needs --umbrella\n' >&2
  exit 64
fi
if [[ "$build_umbrella" == 1 && -n "$incremental_baseline_root" ]]; then
  printf 'build-native-host: --umbrella and incremental modes are exclusive\n' >&2
  exit 64
fi
if [[ "$root_given" != "$usage_given" ]]; then
  printf 'build-native-host: --root and --usage-prefix go together\n' >&2
  exit 64
fi
if [[ "$root_module" != Host.Main &&
      ( "$build_umbrella" == 1 || -n "$incremental_baseline_root" || -z "$binary_path" ) ]]; then
  printf 'build-native-host: a non-Host.Main root needs --binary and excludes --umbrella/incremental modes\n' >&2
  exit 64
fi
if [[ -n "$companion_output" &&
      ( "$build_umbrella" == 1 || -n "$incremental_baseline_root" || "$checkpoint_resume" == 1 ) ]]; then
  printf 'build-native-host: --companion-of is exclusive with umbrella, incremental and resume modes\n' >&2
  exit 64
fi
if [[ "$checkpoint_resume" == 1 &&
      ( "$build_umbrella" == 1 || -n "$incremental_baseline_root" ) ]]; then
  printf 'build-native-host: checkpoint/resume is exclusive with other build modes\n' >&2
  exit 64
fi
if [[ ( -n "$success_baseline_root" &&
        ( -n "$resume_failed_output" || -n "$resume_complete_output" ) ) ||
      ( -n "$resume_failed_output" && -n "$resume_complete_output" ) ]]; then
  printf 'build-native-host: resume and successful-prefix modes are exclusive\n' >&2
  exit 64
fi
if [[ ${#suffix_allowed_modules[@]} -gt 0 && "$incremental_suffix_mode" != 1 ]]; then
  printf 'build-native-host: suffix change allowlist requires --incremental-suffix-from\n' >&2
  exit 64
fi
if [[ ${#inserted_modules[@]} -gt 0 && "$incremental_suffix_mode" != 1 ]]; then
  printf 'build-native-host: inserted module allowlist requires --incremental-suffix-from\n' >&2
  exit 64
fi
if [[ "$allow_unchanged_restart" == 1 && ${#inserted_modules[@]} == 0 ]]; then
  printf 'build-native-host: unchanged restart requires an inserted module\n' >&2
  exit 64
fi
for inserted in "${inserted_modules[@]+"${inserted_modules[@]}"}"; do
  for allowed in "${suffix_allowed_modules[@]+"${suffix_allowed_modules[@]}"}"; do
    if [[ "$inserted" == "$allowed" ]]; then
      printf 'build-native-host: module cannot be both changed and inserted: %s\n' \
        "$inserted" >&2
      exit 64
    fi
  done
done

for command in jq lake file find sort join comm xargs shasum uname cmp head awk uniq realpath python3; do
  command -v "$command" >/dev/null 2>&1 || {
    printf 'build-native-host: required command not found: %s\n' "$command" >&2
    exit 69
  }
done

# The source root is this script's parent directory. It is a git checkout only
# when git names that same directory as its top level: an extracted
# `git archive` tree has no .git (and may sit inside an unrelated repository),
# so its provenance is the archive hash recorded by the caller, not git metadata.
root=$(cd "$(dirname "$0")/.." && pwd -P)
if [[ "$(git -C "$root" rev-parse --show-toplevel 2>/dev/null)" == "$root" ]]; then
  source_git=1
else
  source_git=0
fi
cd "$root"

# Fail before any compiler work when request allocations or routes diverge.
python3 "$root/scripts/host-operations.py" --root "$root" check

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
# Positive integers, bounded only so a typo cannot ask for a thousand compilers. The memory bound is
# the cgroup the caller runs in (swarm-build) and the host-wide seat count below.
case "$native_jobs" in [1-9]|[1-9][0-9]|[1-2][0-9][0-9]) ;; *) printf 'MINIDREGG_NATIVE_JOBS must be a positive integer (<= 299)\n' >&2; exit 64 ;; esac
case "$lean_threads" in [1-9]|[1-9][0-9]) ;; *) printf 'MINIDREGG_LEAN_THREADS must be a positive integer (<= 99)\n' >&2; exit 64 ;; esac

cycle_dir=${MINIDREGG_CYCLE_DIR:-/tmp/minidregg-cycle-20260919}
# Compiler capacity belongs to the host, not to one candidate's evidence.
# Every candidate and scoped build on this host must use this same root.
seat_root=${MINIDREGG_LEAN_SEAT_ROOT:-/tmp/minidregg-lean-seats}
lean_seats=${MINIDREGG_LEAN_SEATS:-2}
# Lake's worker threads = its compiler concurrency (the wrapper comment below); the seats bound it.
lake_threads=${MINIDREGG_LAKE_THREADS:-$(( 2 * lean_seats > 4 ? 2 * lean_seats : 4 ))}
case "$lake_threads" in [1-9]|[1-9][0-9]|[1-2][0-9][0-9]) ;; *) printf 'MINIDREGG_LAKE_THREADS must be a positive integer (<= 299)\n' >&2; exit 64 ;; esac
case "$lean_seats" in [1-9]|[1-9][0-9]) ;; *) printf 'MINIDREGG_LEAN_SEATS must be a positive integer\n' >&2; exit 64 ;; esac
mkdir -p "$seat_root" "$cycle_dir/build"
seat_root=$(cd "$seat_root" && pwd -P)
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

# Seats are taken per real Lean process by the wrapper below (make_lean_wrapper), not by this build:
# a build waits only while a compiler would exceed the host's seat count, and releases the seat the
# moment that compiler exits. A full set of seats is contention, not failure: the wrapper waits up to
# MINIDREGG_LEAN_SEAT_WAIT (MINIDREGG_LEAN_SEAT_WAIT=0 restores the immediate refusal, exit 75).
seat_wait=${MINIDREGG_LEAN_SEAT_WAIT:-7200}
case "$seat_wait" in ''|*[!0-9]*) printf 'MINIDREGG_LEAN_SEAT_WAIT must be a number of seconds\n' >&2; exit 64 ;; esac
seat_owners() {
  local d
  for d in "$seat_root"/lean-seat-*; do
    [[ -d "$d" ]] || continue
    printf '  %s: %s\n' "${d##*/}" "$(tr '\n' ' ' < "$d/owner.txt" 2>/dev/null)"
  done
}

start_epoch=$(date +%s)
printf 'start_utc=%s\nroot=%s\nlean_threads=%s\nlake_threads=%s\nnative_jobs=%s\nseat_root=%s\nlean_seats=%s\n' \
  "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$root" "$lean_threads" "$lake_threads" "$native_jobs" "$seat_root" "$lean_seats" \
  > "$output_dir/build.log"

# `transImports` is a nonbuildable Lake facet: it parses source headers and
# recursively combines module names.  Do not substitute `:deps`; that setup
# facet fetches import artifacts and can fan out compilers.
closure="$output_dir/transitive-imports.json"
env LEAN_NUM_THREADS="$lean_threads" \
  lake --reconfigure query "+$root_module:transImports" --json \
  > "$closure" 2> "$output_dir/transitive-imports.log"
jq -e 'type == "array" and length > 0' "$closure" >/dev/null

source_modules="$output_dir/source-modules.txt"
: > "$source_modules"
jq -r '.[]' "$closure" | while IFS= read -r module; do
  relative=${module//./\/}.lean
  [[ -f "$relative" ]] && printf '%s\n' "$module"
done > "$source_modules"
grep -qxF "$root_module" "$source_modules" || printf '%s\n' "$root_module" >> "$source_modules"

package_required="$output_dir/package-modules.txt"
jq -r '.[]' "$closure" | while IFS= read -r module; do
  relative=${module//./\/}.lean
  [[ -f "$relative" ]] || printf '%s\n' "$module"
done | sort -u > "$package_required"

build_modules="$output_dir/build-modules.txt"
if [[ "$build_umbrella" == 1 ]]; then
  umbrella_closure="$output_dir/umbrella-transitive-imports.json"
  umbrella_modules="$output_dir/umbrella-source-modules.txt"
  : > "$umbrella_modules"
  for target in "${umbrella_targets[@]}"; do
    env LEAN_NUM_THREADS="$lean_threads" \
      lake query "+$target:transImports" --json \
      > "$umbrella_closure" 2>> "$output_dir/umbrella-transitive-imports.log"
    jq -e 'type == "array" and length > 0' "$umbrella_closure" >/dev/null
    jq -r '.[]' "$umbrella_closure" | while IFS= read -r module; do
      relative=${module//./\/}.lean
      [[ -f "$relative" ]] && printf '%s\n' "$module"
    done >> "$umbrella_modules"
    grep -qxF "$target" "$umbrella_modules" || printf '%s\n' "$target" >> "$umbrella_modules"
  done
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

# A failed full build may have a useful compiled prefix. Capture the exact
# external Lean inputs before compiling, then checkpoint each successful
# module's source and generated artifacts. A later run may reuse only a
# consecutive, byte-verified prefix in this same independent snapshot.
module_checkpoint_paths() {
  local stem=$1 directory leaf required link parent
  leaf=${stem##*/}
  parent=""
  [[ "$stem" != */* ]] || parent=${stem%/*}
  for required in "$stem.lean" \
      ".lake/build/lib/lean/$stem.olean" \
      ".lake/build/lib/lean/$stem.ilean" \
      ".lake/build/ir/$stem.c"; do
    [[ -f "$required" && ! -L "$required" ]] || {
      printf 'build-native-host: missing or linked prefix artifact: %s\n' "$required" >&2
      return 66
    }
  done
  for directory in ".lake/build/lib/lean${parent:+/$parent}" \
      ".lake/build/ir${parent:+/$parent}"; do
    link=$(find "$directory" -maxdepth 1 -type l -name "$leaf.*" -print -quit)
    [[ -z "$link" ]] || {
      printf 'build-native-host: linked prefix artifact: %s\n' "$link" >&2
      return 65
    }
  done
  printf '%s\n' "$stem.lean"
  for directory in ".lake/build/lib/lean${parent:+/$parent}" \
      ".lake/build/ir${parent:+/$parent}"; do
    find "$directory" -maxdepth 1 -type f -name "$leaf.*" -print
  done | sort -u
}

# Return the longest common, byte-qualified prefix. A source change or a new
# module starts the recompiled suffix. Artifact drift under unchanged source
# is a refusal, not an excuse to trust a possibly stale imported OLean.
select_qualified_success_prefix() {
  local current_list=$1 baseline_list=$2 baseline_checkpoints=$3 evidence_dir=$4
  local current_module baseline_module stem checkpoint expected recorded index=0
  : > "$evidence_dir/success-prefix-artifact-check.log"
  exec 7< "$current_list"
  exec 8< "$baseline_list"
  while IFS= read -r current_module <&7 && IFS= read -r baseline_module <&8; do
    [[ "$current_module" == "$baseline_module" ]] || break
    stem=${current_module//./\/}
    [[ -f "$success_baseline_root/$stem.lean" && -f "$stem.lean" ]] || break
    cmp -s "$success_baseline_root/$stem.lean" "$stem.lean" || break
    index=$((index + 1))
    checkpoint="$baseline_checkpoints/$(printf '%04d' "$index")-${current_module//./_}.sha256"
    [[ -f "$checkpoint" ]] || {
      printf 'build-native-host: successful baseline lacks prefix checkpoint: %s\n' \
        "$checkpoint" >&2
      return 65
    }
    expected="$evidence_dir/success-prefix-expected-paths.txt"
    recorded="$evidence_dir/success-prefix-recorded-paths.txt"
    module_checkpoint_paths "$stem" > "$expected" || return 65
    sed -n 's/^[[:xdigit:]]\{64\}  //p' "$checkpoint" > "$recorded"
    cmp -s "$expected" "$recorded" || {
      printf 'build-native-host: successful prefix artifact set changed: %s\n' \
        "$current_module" >&2
      return 65
    }
    shasum -a 256 -c "$checkpoint" \
      >> "$evidence_dir/success-prefix-artifact-check.log" || {
      printf 'build-native-host: successful prefix artifact changed: %s\n' \
        "$current_module" >&2
      return 65
    }
  done
  exec 7<&-
  exec 8<&-
  printf '%s\n' "$index"
}

package_artifact_symlinks() {
  # Package documentation/benchmark symlinks are not compiler inputs. Roots
  # and every imported library or generated native-object ancestor must be
  # real so find/hash cannot silently skip a dereferenced artifact tree.
  local links link
  if [[ -L .lake || -L .lake/packages || ! -d .lake/packages ]]; then
    printf 'build-native-host: package root is linked or missing\n' >&2
    return 65
  fi
  links=$(find .lake/packages -type l -print) || {
    printf 'build-native-host: package symlink enumeration failed\n' >&2
    return 65
  }
  while IFS= read -r link; do
    if [[ "$link" =~ ^\.lake/packages/[^/]+(/\.lake(/build(/(lib|ir)(/.*)?)?)?)?$ ]]; then
      printf '%s\n' "$link"
    fi
  done <<< "$links"
}

resume_prefix=0
resume_checkpoint_dir="$output_dir/resume-checkpoints"
if [[ "$checkpoint_resume" == 1 ]]; then
  mkdir -p "$resume_checkpoint_dir"
  source_inputs="$output_dir/source-input-sha256.txt"
  while IFS= read -r module; do
    shasum -a 256 "${module//./\/}.lean"
  done < "$source_modules" > "$source_inputs"
  resume_inputs="$output_dir/resume-input-sha256.txt"
  toolchain=$(lake env lean --print-prefix)
  toolchain=$(cd "$toolchain" && pwd -P)
  package_links="$output_dir/package-symlinks-recursive.txt"
  package_artifact_symlinks > "$package_links" || exit 65
  if [[ -s "$package_links" ]]; then
    printf 'build-native-host: checkpoint mode refuses nested package symlinks; see %s\n' \
      "$package_links" >&2
    exit 65
  fi
  toolchain_links="$output_dir/toolchain-symlinks.txt"
  find "$toolchain" -type l -print | sort | while IFS= read -r link; do
    target=$(realpath "$link") || exit 65
    case "$target" in
      "$toolchain"/*) printf '%s -> %s\n' "$link" "$target" ;;
      *)
        printf 'build-native-host: toolchain symlink leaves pinned tree: %s\n' \
          "$link" >&2
        exit 65
        ;;
    esac
  done > "$toolchain_links"
  {
    for input in lake-manifest.json lakefile.lean lakefile.toml lean-toolchain \
        scripts/build-native-host.sh; do
      [[ -f "$input" ]] && shasum -a 256 "$input"
    done
    # Lean can load private/server OLeans, IR, compiled evaluators and native
    # libraries in addition to the public OLean. Pin the complete toolchain
    # and package Lean library trees rather than guessing an extension list.
    find "$toolchain" -type f -print0 \
      | sort -z | xargs -0 -n 50 shasum -a 256
    find .lake/packages -type f -path '*/.lake/build/lib/*' -print0 \
      | sort -z | xargs -0 -n 50 shasum -a 256
  } > "$resume_inputs"
  printf 'snapshot_root=%s\ntoolchain=%s\nmode=full-nonumbrella\n' "$root" "$toolchain" \
    > "$output_dir/resume-contract.txt"

  if [[ -n "$resume_complete_output" ]]; then
    resume_complete_output=$(cd "$resume_complete_output" && pwd -P)
    [[ "$resume_complete_output" != "$output_dir" &&
       -f "$resume_complete_output/resume-contract.txt" &&
       -f "$resume_complete_output/resume-input-sha256.txt" &&
       -f "$resume_complete_output/source-input-sha256.txt" &&
       -f "$resume_complete_output/build.log" &&
       -f "$resume_complete_output/compile-args.txt" &&
       ! -e "$resume_complete_output/manifest.txt" ]] || {
      printf 'build-native-host: post-Lean output lacks a failed resume contract\n' >&2
      exit 65
    }
    cmp -s "$resume_complete_output/resume-contract.txt" \
      "$output_dir/resume-contract.txt" || {
      printf 'build-native-host: post-Lean snapshot or toolchain changed\n' >&2
      exit 65
    }
    for list in source-modules.txt build-modules.txt transitive-imports.json; do
      cmp -s "$resume_complete_output/$list" "$output_dir/$list" || {
        printf 'build-native-host: post-Lean source closure changed: %s\n' "$list" >&2
        exit 65
      }
    done
    # The prior locale may have ordered punctuation differently. Compare the
    # package set, with duplicate rejection, rather than trusting either order.
    for side in prior current; do
      if [[ "$side" == prior ]]; then
        list="$resume_complete_output/package-modules.txt"
      else
        list="$output_dir/package-modules.txt"
      fi
      sort "$list" > "$output_dir/post-lean-$side-packages.txt"
      uniq -d "$output_dir/post-lean-$side-packages.txt" \
        > "$output_dir/post-lean-$side-package-duplicates.txt"
      [[ ! -s "$output_dir/post-lean-$side-package-duplicates.txt" ]] || {
        printf 'build-native-host: duplicate package in post-Lean closure\n' >&2
        exit 65
      }
    done
    cmp -s "$output_dir/post-lean-prior-packages.txt" \
      "$output_dir/post-lean-current-packages.txt" || {
      printf 'build-native-host: post-Lean package closure changed\n' >&2
      exit 65
    }
    cmp -s "$resume_complete_output/source-input-sha256.txt" \
      "$source_inputs" || {
      printf 'build-native-host: post-Lean source input manifest changed\n' >&2
      exit 65
    }
    (cd "$root" && shasum -a 256 -c "$source_inputs") \
      > "$output_dir/post-lean-source-check.log"
    # Exactly one reviewed builder revision may differ. All other toolchain,
    # package-library, and build inputs retain their predecessor digests.
    old_builder_line=$(grep -E '^[[:xdigit:]]{64}  scripts/build-native-host\.sh$' \
      "$resume_complete_output/resume-input-sha256.txt") || exit 65
    [[ "$old_builder_line" == "$resume_complete_builder_sha  scripts/build-native-host.sh" &&
       "$(grep -c '  scripts/build-native-host.sh$' \
          "$resume_complete_output/resume-input-sha256.txt")" == 1 ]] || {
      printf 'build-native-host: predecessor builder hash differs from declared pin\n' >&2
      exit 65
    }
    grep -v '  scripts/build-native-host.sh$' \
      "$resume_complete_output/resume-input-sha256.txt" \
      | sort -k2,2 > "$output_dir/post-lean-prior-external-sha256.txt"
    grep -v '  scripts/build-native-host.sh$' "$resume_inputs" \
      | sort -k2,2 > "$output_dir/post-lean-current-external-sha256.txt"
    for side in prior current; do
      awk '{ print $2 }' "$output_dir/post-lean-$side-external-sha256.txt" \
        | uniq -d > "$output_dir/post-lean-$side-external-duplicates.txt"
      [[ ! -s "$output_dir/post-lean-$side-external-duplicates.txt" ]] || {
        printf 'build-native-host: duplicate post-Lean external input path\n' >&2
        exit 65
      }
    done
    cmp -s "$output_dir/post-lean-prior-external-sha256.txt" \
      "$output_dir/post-lean-current-external-sha256.txt" || {
      printf 'build-native-host: post-Lean external input changed beyond builder\n' >&2
      exit 65
    }
    (cd "$root" && shasum -a 256 -c \
      "$output_dir/post-lean-prior-external-sha256.txt") \
      > "$output_dir/post-lean-external-check.log"
    for list in toolchain-symlinks.txt package-symlinks-recursive.txt; do
      sort "$resume_complete_output/$list" > "$output_dir/post-lean-prior-$list"
      sort "$output_dir/$list" > "$output_dir/post-lean-current-$list"
      cmp -s "$output_dir/post-lean-prior-$list" \
        "$output_dir/post-lean-current-$list" || {
        printf 'build-native-host: post-Lean symlink inventory changed: %s\n' "$list" >&2
        exit 65
      }
    done
    total=$(wc -l < "$build_modules" | tr -d ' ')
    checkpoint_count=$(find "$resume_complete_output/resume-checkpoints" \
      -maxdepth 1 -type f -name '*.sha256' | wc -l | tr -d ' ')
    [[ "$checkpoint_count" == "$total" ]] || {
      printf 'build-native-host: post-Lean checkpoint count is incomplete\n' >&2
      exit 65
    }
    prior_verified_prefix=0
    if [[ -f "$resume_complete_output/resume-validation.txt" ]]; then
      [[ "$(grep -c '^verified_prefix_modules=' \
          "$resume_complete_output/resume-validation.txt")" == 1 ]] || exit 65
      prior_verified_prefix=$(sed -n 's/^verified_prefix_modules=//p' \
        "$resume_complete_output/resume-validation.txt")
      [[ "$prior_verified_prefix" =~ ^[0-9]+$ &&
         "$prior_verified_prefix" -le "$total" ]] || exit 65
      grep -qxF "failed-build resume check PASS $prior_verified_prefix compiled prefix modules" \
        "$resume_complete_output/build.log" || {
        printf 'build-native-host: post-Lean predecessor prefix lacks PASS record\n' >&2
        exit 65
      }
    fi
    index=0
    while IFS= read -r module; do
      index=$((index + 1))
      if [[ "$index" -gt "$prior_verified_prefix" ]]; then
        awk -v want="lean[$index/$total] $module PASS " \
          'index($0, want) == 1 { found = 1 } END { exit !found }' \
          "$resume_complete_output/build.log" || {
          printf 'build-native-host: post-Lean module lacks PASS: %s\n' "$module" >&2
          exit 65
        }
      fi
      stem=${module//./\/}
      checkpoint="$resume_complete_output/resume-checkpoints/$(printf '%04d' "$index")-${module//./_}.sha256"
      [[ -f "$checkpoint" ]] || exit 65
      module_checkpoint_paths "$stem" | sed -E '/\.c\.o\.(export|native)$/d' \
        > "$output_dir/post-lean-expected-paths.txt"
      sed -n 's/^[[:xdigit:]]\{64\}  //p' "$checkpoint" \
        | sed -E '/\.c\.o\.(export|native)$/d' \
        > "$output_dir/post-lean-recorded-paths.txt"
      cmp -s "$output_dir/post-lean-expected-paths.txt" \
        "$output_dir/post-lean-recorded-paths.txt" || {
        printf 'build-native-host: post-Lean checkpoint path set changed: %s\n' "$module" >&2
        exit 65
      }
      grep -vE '^[[:xdigit:]]{64}  .*\.c\.o\.(export|native)$' "$checkpoint" \
        | (cd "$root" && shasum -a 256 -c) \
        >> "$output_dir/post-lean-prefix-check.log" || {
        printf 'build-native-host: post-Lean source/OLean/C changed: %s\n' "$module" >&2
        exit 65
      }
    done < "$build_modules"
    cp "$resume_complete_output"/resume-checkpoints/*.sha256 \
      "$resume_checkpoint_dir/"
    resume_prefix=$total
    printf 'post_lean_output=%s\nverified_modules=%s\nold_builder_sha256=%s\nnew_builder_sha256=%s\nproject_c_action=recompile_all\n' \
      "$resume_complete_output" "$total" "$resume_complete_builder_sha" \
      "$(shasum -a 256 scripts/build-native-host.sh | cut -d ' ' -f 1)" \
      > "$output_dir/post-lean-recovery.txt"
    printf 'post-Lean recovery check PASS %s source/OLean/C modules; recompile project C\n' \
      "$total" | tee -a "$output_dir/build.log"
  elif [[ -n "$resume_failed_output" ]]; then
    resume_failed_output=$(cd "$resume_failed_output" && pwd -P)
    [[ "$resume_failed_output" != "$output_dir" &&
       -f "$resume_failed_output/resume-contract.txt" &&
       -f "$resume_failed_output/resume-input-sha256.txt" &&
       -f "$resume_failed_output/build.log" &&
       ! -e "$resume_failed_output/manifest.txt" ]] || {
      printf 'build-native-host: failed output lacks a usable resume contract\n' >&2
      exit 65
    }
    cmp -s "$resume_failed_output/resume-contract.txt" \
      "$output_dir/resume-contract.txt" || {
      printf 'build-native-host: resume snapshot or mode changed\n' >&2
      exit 65
    }
    grep -q ' FAIL(' "$resume_failed_output/build.log" || {
      printf 'build-native-host: prior run has no recorded Lean failure\n' >&2
      exit 65
    }
    for list in source-modules.txt build-modules.txt package-modules.txt \
        transitive-imports.json resume-input-sha256.txt toolchain-symlinks.txt \
        package-symlinks-recursive.txt; do
      cmp -s "$resume_failed_output/$list" "$output_dir/$list" || {
        printf 'build-native-host: resume closure or external input changed: %s\n' \
          "$list" >&2
        exit 65
      }
    done
    (cd "$root" && shasum -a 256 -c "$resume_failed_output/resume-input-sha256.txt") \
      > "$output_dir/resume-input-check.log"
    index=0
    while IFS= read -r module; do
      index=$((index + 1))
      checkpoint="$resume_failed_output/resume-checkpoints/$(printf '%04d' "$index")-${module//./_}.sha256"
      [[ -f "$checkpoint" ]] || break
      stem=${module//./\/}
      expected="$output_dir/resume-expected-paths.txt"
      module_checkpoint_paths "$stem" > "$expected"
      sed -n 's/^[[:xdigit:]]\{64\}  //p' "$checkpoint" > "$output_dir/resume-checkpoint-paths.txt"
      cmp -s "$expected" "$output_dir/resume-checkpoint-paths.txt" || {
        printf 'build-native-host: malformed prefix checkpoint: %s\n' "$checkpoint" >&2
        exit 65
      }
      (cd "$root" && shasum -a 256 -c "$checkpoint") \
        >> "$output_dir/resume-prefix-check.log" || {
        printf 'build-native-host: compiled prefix changed: %s\n' "$checkpoint" >&2
        exit 65
      }
      resume_prefix=$index
    done < "$build_modules"
    checkpoint_count=$(find "$resume_failed_output/resume-checkpoints" \
      -maxdepth 1 -type f -name '*.sha256' | wc -l | tr -d ' ')
    [[ "$resume_prefix" -gt 0 && "$checkpoint_count" == "$resume_prefix" &&
       "$resume_prefix" -lt "$(wc -l < "$build_modules" | tr -d ' ')" ]] || {
      printf 'build-native-host: resume checkpoints are empty or nonconsecutive\n' >&2
      exit 65
    }
    cp "$resume_failed_output"/resume-checkpoints/*.sha256 "$resume_checkpoint_dir/"
    printf 'failed_output=%s\nverified_prefix_modules=%s\n' \
      "$resume_failed_output" "$resume_prefix" > "$output_dir/resume-validation.txt"
    printf 'failed-build resume check PASS %s compiled prefix modules\n' \
      "$resume_prefix" | tee -a "$output_dir/build.log"
  elif [[ -n "$success_baseline_root" ]]; then
    success_baseline_root=$(cd "$success_baseline_root" && pwd -P)
    success_baseline_output=$(cd "$success_baseline_output" && pwd -P)
    [[ "$success_baseline_root" != "$root" &&
       -f "$success_baseline_root/.minidregg-native-snapshot" ]] || {
      printf 'build-native-host: successful baseline must be another independent snapshot\n' >&2
      exit 73
    }
    for baseline_file in manifest.txt source-sha256.txt artifact-sha256.txt \
        reusable-artifact-sha256.txt source-modules.txt package-modules.txt \
        package-objects.txt resume-input-sha256.txt resume-contract.txt \
        toolchain-symlinks.txt package-symlinks-recursive.txt \
        source-input-sha256.txt success-checkpoint-sha256.txt; do
      [[ -f "$success_baseline_output/$baseline_file" ]] || {
        printf 'build-native-host: successful baseline lacks qualification: %s\n' \
          "$baseline_file" >&2
        exit 65
      }
    done
    grep -qxF 'usage_exit=1' "$success_baseline_output/manifest.txt"
    grep -qxF 'checkpointed_success=1' "$success_baseline_output/manifest.txt" || {
      printf 'build-native-host: baseline was not a checkpointed successful build\n' >&2
      exit 65
    }
    if ! grep -qxF "snapshot_root=$success_baseline_root" \
        "$success_baseline_output/resume-contract.txt" ||
        ! grep -qxF "toolchain=$toolchain" \
          "$success_baseline_output/resume-contract.txt" ||
        ! grep -qxF 'mode=full-nonumbrella' \
          "$success_baseline_output/resume-contract.txt"; then
      printf 'build-native-host: successful baseline contract does not match its snapshot or toolchain\n' >&2
      exit 65
    fi
    grep -qxF "native_target=$(uname -s):$(uname -m)" \
      "$success_baseline_output/manifest.txt"
    baseline_binary=$(sed -n 's/^binary=//p' "$success_baseline_output/manifest.txt")
    baseline_binary_hash=$(sed -n 's/^binary_sha256=//p' \
      "$success_baseline_output/manifest.txt")
    [[ -f "$baseline_binary" && -n "$baseline_binary_hash" &&
       "$(shasum -a 256 "$baseline_binary" | cut -d ' ' -f 1)" == "$baseline_binary_hash" ]] || {
      printf 'build-native-host: successful baseline executable identity changed\n' >&2
      exit 65
    }
    shasum -a 256 -c "$success_baseline_output/artifact-sha256.txt" \
      > "$output_dir/success-baseline-artifact-check.log"
    (cd "$success_baseline_root" &&
      shasum -a 256 -c "$success_baseline_output/source-sha256.txt") \
      > "$output_dir/success-baseline-source-check.log"
    (cd "$success_baseline_root" &&
      shasum -a 256 -c "$success_baseline_output/reusable-artifact-sha256.txt") \
      > "$output_dir/success-baseline-reusable-check.log"
    shasum -a 256 -c "$success_baseline_output/success-checkpoint-sha256.txt" \
      > "$output_dir/success-checkpoint-check.log"
    for list in resume-input-sha256.txt toolchain-symlinks.txt \
        package-symlinks-recursive.txt package-modules.txt; do
      cmp -s "$success_baseline_output/$list" "$output_dir/$list" || {
        printf 'build-native-host: successful baseline external input changed: %s\n' \
          "$list" >&2
        exit 65
      }
    done
    # The baseline and current external-input manifests have identical paths
    # and bytes, including package IR/private OLeans and toolchain libraries.
    (cd "$root" &&
      shasum -a 256 -c "$success_baseline_output/resume-input-sha256.txt") \
      > "$output_dir/success-external-input-check.log"
    while IFS= read -r object; do
      package_root=${object%%/.lake/build/ir/*}
      package_module=${object#"$package_root/.lake/build/ir/"}
      package_module=${package_module%.c.o.*}
      for path in "$object" "${object%.o.*}" \
          "$package_root/.lake/build/lib/lean/$package_module.olean"; do
        if [[ ! -f "$success_baseline_root/$path" || ! -f "$path" ]] ||
            ! cmp -s "$success_baseline_root/$path" "$path"; then
          printf 'build-native-host: successful baseline package artifact changed: %s\n' \
            "$path" >&2
          exit 65
        fi
      done
    done < "$success_baseline_output/package-objects.txt"
    # Reuse presumes that every project dependency precedes its importer in
    # Lake's current closure. Check that order explicitly before selecting a
    # prefix, including when a new import changed the topology.
    ordered_prefix="$output_dir/ordered-project-prefix.txt"
    : > "$ordered_prefix"
    # The inner grep reopens the immutable module list while the outer loop
    # reads it; neither command writes that list.
    # shellcheck disable=SC2094
    while IFS= read -r module; do
      source=${module//./\/}.lean
      while IFS= read -r imports; do
        read -r -a import_tokens <<< "$imports"
        for imported in "${import_tokens[@]}"; do
          [[ "$imported" == --* ]] && break
          [[ "$imported" == all ]] && continue
          [[ "$imported" =~ ^[A-Za-z_][A-Za-z0-9_.]*$ ]] || continue
          [[ -f "${imported//./\/}.lean" ]] || continue
          if grep -qxF "$imported" "$source_modules" &&
              ! grep -qxF "$imported" "$ordered_prefix"; then
            printf 'build-native-host: current project closure is not topological: %s imports %s\n' \
              "$module" "$imported" >&2
            exit 65
          fi
        done
      done < <(sed -nE \
        's/^[[:space:]]*((public|meta)[[:space:]]+)*import[[:space:]]+//p' \
        "$source")
      printf '%s\n' "$module" >> "$ordered_prefix"
    done < "$source_modules"
    resume_prefix=$(select_qualified_success_prefix "$source_modules" \
      "$success_baseline_output/source-modules.txt" \
      "$success_baseline_output/resume-checkpoints" "$output_dir")
    printf 'successful_baseline=%s\nverified_prefix_modules=%s\n' \
      "$success_baseline_output" "$resume_prefix" \
      > "$output_dir/success-prefix-validation.txt"
    printf 'successful-prefix reuse check PASS %s compiled prefix modules\n' \
      "$resume_prefix" | tee -a "$output_dir/build.log"
  fi
elif [[ -n "$resume_failed_output" ]]; then
  printf 'build-native-host: failed-build resume requires a full non-umbrella build\n' >&2
  exit 64
fi

if [[ -n "$incremental_baseline_root" ]]; then
  incremental_baseline_root=$(cd "$incremental_baseline_root" && pwd -P)
  incremental_baseline_output=$(cd "$incremental_baseline_output" && pwd -P)
  [[ "$incremental_baseline_root" != "$root" ]] || {
    printf 'build-native-host: incremental baseline must be a different snapshot\n' >&2
    exit 73
  }
  [[ -f "$incremental_baseline_root/.minidregg-native-snapshot" ]] || {
    printf 'build-native-host: incremental baseline is not an independent snapshot\n' >&2
    exit 73
  }
  baseline_manifest="$incremental_baseline_output/manifest.txt"
  baseline_sources="$incremental_baseline_output/source-sha256.txt"
  baseline_artifacts="$incremental_baseline_output/artifact-sha256.txt"
  baseline_reusable="$incremental_baseline_output/reusable-artifact-sha256.txt"
  baseline_packages="$incremental_baseline_output/package-objects.txt"
  for baseline_file in "$baseline_manifest" "$baseline_sources" \
      "$baseline_artifacts" "$baseline_reusable" "$baseline_packages" \
      "$incremental_baseline_output/source-modules.txt" \
      "$incremental_baseline_output/package-modules.txt" \
      "$incremental_baseline_output/compile-args.txt"; do
    [[ -f "$baseline_file" ]] || {
      printf 'build-native-host: missing baseline evidence: %s\n' "$baseline_file" >&2
      exit 66
    }
  done
  reusable_hash_anchored=0
  while read -r artifact_hash artifact_path; do
    [[ -f "$artifact_path" ]] || continue
    artifact_canonical=$(cd "$(dirname "$artifact_path")" && pwd -P)/$(basename "$artifact_path")
    if [[ "$artifact_canonical" == "$baseline_reusable" &&
          "$artifact_hash" == "$(shasum -a 256 "$baseline_reusable" | cut -d ' ' -f 1)" ]]; then
      reusable_hash_anchored=1
      break
    fi
  done < "$baseline_artifacts"
  [[ "$reusable_hash_anchored" == 1 ]] || {
    printf 'build-native-host: reusable artifact manifest has no baseline hash\n' >&2
    exit 65
  }
  grep -qxF 'usage_exit=1' "$baseline_manifest"
  grep -qxF "native_target=$(uname -s):$(uname -m)" "$baseline_manifest"
  baseline_binary=$(sed -n 's/^binary=//p' "$baseline_manifest")
  baseline_binary_hash=$(sed -n 's/^binary_sha256=//p' "$baseline_manifest")
  [[ -f "$baseline_binary" && -n "$baseline_binary_hash" &&
      "$(shasum -a 256 "$baseline_binary" | cut -d ' ' -f 1)" == "$baseline_binary_hash" ]] || {
    printf 'build-native-host: baseline executable identity changed\n' >&2
    exit 65
  }
  shasum -a 256 -c "$baseline_artifacts" > "$output_dir/baseline-artifact-check.log"
  (cd "$incremental_baseline_root" && shasum -a 256 -c "$baseline_sources") \
    > "$output_dir/baseline-source-check.log"
  (cd "$incremental_baseline_root" && shasum -a 256 -c "$baseline_reusable") \
    > "$output_dir/baseline-reusable-check.log"
  if [[ ${#inserted_modules[@]} == 0 ]]; then
    cmp -s "$source_modules" "$incremental_baseline_output/source-modules.txt" || {
      printf 'build-native-host: incremental import closure changed\n' >&2
      exit 65
    }
  else
    # Lake may reorder unchanged modules after a new import. The reusable
    # prefix must be identical in order; beyond the restart, the old closure
    # must survive as a set and every extra member must be declared. The whole
    # new suffix is compiled in its freshly computed topological order.
    baseline_sorted="$output_dir/baseline-source-modules-sorted.txt"
    current_sorted="$output_dir/current-source-modules-sorted.txt"
    sort "$incremental_baseline_output/source-modules.txt" > "$baseline_sorted"
    sort "$source_modules" > "$current_sorted"
    if [[ -n "$(uniq -d "$baseline_sorted")" || -n "$(uniq -d "$current_sorted")" ]]; then
      printf 'build-native-host: duplicate module in native source closure\n' >&2
      exit 65
    fi
    missing_baseline="$output_dir/missing-baseline-source-modules.txt"
    comm -23 "$baseline_sorted" "$current_sorted" > "$missing_baseline"
    if [[ -s "$missing_baseline" ]]; then
      printf 'build-native-host: inserted closure removed baseline modules; see %s\n' \
        "$missing_baseline" >&2
      exit 65
    fi
    inserted_seen="$output_dir/inserted-source-modules.txt"
    comm -13 "$baseline_sorted" "$current_sorted" > "$inserted_seen"
    declared_sorted="$output_dir/declared-inserted-modules-sorted.txt"
    printf '%s\n' "${inserted_modules[@]}" | sort > "$declared_sorted"
    if ! cmp -s "$inserted_seen" "$declared_sorted"; then
      printf 'build-native-host: inserted closure differs from declared modules\n' >&2
      exit 65
    fi
    current_prefix="$output_dir/current-reused-prefix.txt"
    baseline_prefix="$output_dir/baseline-reused-prefix.txt"
    awk -v restart="$incremental_changed_module" '$0 == restart { exit } { print }' \
      "$source_modules" > "$current_prefix"
    head -n "$(wc -l < "$current_prefix" | tr -d ' ')" \
      "$incremental_baseline_output/source-modules.txt" > "$baseline_prefix"
    cmp -s "$current_prefix" "$baseline_prefix" || {
      printf 'build-native-host: insertion or reorder precedes suffix restart\n' >&2
      exit 65
    }
    while IFS= read -r module; do
      stem=${module//./\/}
      if [[ -e "$incremental_baseline_root/$stem.lean" || ! -f "$stem.lean" ]]; then
        printf 'build-native-host: declared inserted source is not new: %s\n' \
          "$stem.lean" >&2
        exit 65
      fi
    done < "$inserted_seen"
    # A new local module may not silently pull new, unpinned package objects.
    cmp -s "$package_required" "$incremental_baseline_output/package-modules.txt" || {
      printf 'build-native-host: inserted closure changed package requirements\n' >&2
      exit 65
    }
  fi
  [[ -f lakefile.lean || -f lakefile.toml ]] || {
    printf 'build-native-host: neither Lake project file exists\n' >&2
    exit 65
  }
  for source_file in lake-manifest.json lean-toolchain lakefile.lean lakefile.toml; do
    if [[ ! -e "$incremental_baseline_root/$source_file" && ! -e "$source_file" ]]; then
      continue
    fi
    if [[ ! -f "$incremental_baseline_root/$source_file" || ! -f "$source_file" ]] || \
        ! cmp -s "$incremental_baseline_root/$source_file" "$source_file"; then
      printf 'build-native-host: incremental package/toolchain manifest changed: %s\n' \
        "$source_file" >&2
      exit 65
    fi
  done
  toolchain=$(lake env lean --print-prefix)
  grep -qxF "toolchain=$toolchain" "$baseline_manifest"
  grep -qxF "lean=$(lean --version | sed -n '1p')" "$baseline_manifest"
  changed_stem=${incremental_changed_module//./\/}
  changed_source="$changed_stem.lean"
  grep -qxF "$incremental_changed_module" "$source_modules" || {
    printf 'build-native-host: changed module is outside native source closure: %s\n' \
      "$incremental_changed_module" >&2
    exit 65
  }
  changed_is_inserted=0
  for inserted in "${inserted_modules[@]+"${inserted_modules[@]}"}"; do
    [[ "$inserted" == "$incremental_changed_module" ]] && changed_is_inserted=1
  done
  if [[ "$changed_is_inserted" == 1 ]]; then
    [[ -f "$changed_source" && ! -e "$incremental_baseline_root/$changed_source" ]] || {
      printf 'build-native-host: suffix start is not a new source: %s\n' \
        "$changed_source" >&2
      exit 65
    }
  else
    [[ -f "$changed_source" && -f "$incremental_baseline_root/$changed_source" &&
        ! "$changed_source" -ef "$incremental_baseline_root/$changed_source" ]] || {
      printf 'build-native-host: changed module must be in an independent copy: %s\n' \
        "$changed_source" >&2
      exit 73
    }
    if cmp -s "$incremental_baseline_root/$changed_source" "$changed_source"; then
      if [[ "$allow_unchanged_restart" != 1 ]]; then
        printf 'build-native-host: incremental source is unchanged: %s\n' \
          "$changed_source" >&2
        exit 65
      fi
      restart_source_unchanged=1
    else
      restart_source_unchanged=0
    fi
  fi
  shasum -a 256 "$changed_source" > "$output_dir/changed-source-sha256.txt"
  reused_paths="$output_dir/reused-artifact-paths.nul"
  : > "$reused_paths"
  validated_sources=0
  validated_tail_sources=0
  validated_additional_changes=0
  validated_insertions=$changed_is_inserted
  changed_seen=0
  while IFS= read -r module; do
    stem=${module//./\/}
    if [[ "$module" == "$incremental_changed_module" ]]; then
      changed_seen=1
      continue
    fi
    if [[ "$changed_seen" == 1 ]]; then
      allowed_change=0
      inserted_module=0
      for allowed in "${suffix_allowed_modules[@]+"${suffix_allowed_modules[@]}"}"; do
        if [[ "$allowed" == "$module" ]]; then
          allowed_change=1
          break
        fi
      done
      for inserted in "${inserted_modules[@]+"${inserted_modules[@]}"}"; do
        if [[ "$inserted" == "$module" ]]; then
          inserted_module=1
          break
        fi
      done
      if [[ "$inserted_module" == 1 ]]; then
        if [[ -e "$incremental_baseline_root/$stem.lean" || ! -f "$stem.lean" ]]; then
          printf 'build-native-host: declared inserted source is not new: %s\n' \
            "$stem.lean" >&2
          exit 65
        fi
        shasum -a 256 "$stem.lean" >> "$output_dir/changed-source-sha256.txt"
        validated_insertions=$((validated_insertions + 1))
        continue
      fi
      if [[ ! -f "$incremental_baseline_root/$stem.lean" ||
            ! -f "$stem.lean" ]]; then
        printf 'build-native-host: later source absent: %s\n' "$stem.lean" >&2
        exit 65
      fi
      if [[ "$allowed_change" == 1 ]]; then
        if cmp -s "$incremental_baseline_root/$stem.lean" "$stem.lean"; then
          printf 'build-native-host: declared suffix change is unchanged: %s\n' "$stem.lean" >&2
          exit 65
        fi
        shasum -a 256 "$stem.lean" >> "$output_dir/changed-source-sha256.txt"
        validated_additional_changes=$((validated_additional_changes + 1))
      else
        if ! cmp -s "$incremental_baseline_root/$stem.lean" "$stem.lean"; then
          printf 'build-native-host: undeclared later source changed: %s\n' "$stem.lean" >&2
          exit 65
        fi
        validated_tail_sources=$((validated_tail_sources + 1))
      fi
      continue
    fi
    for path in "$stem.lean" \
        ".lake/build/lib/lean/$stem.olean" \
        ".lake/build/lib/lean/$stem.ilean" \
        ".lake/build/ir/$stem.c"; do
      if [[ ! -f "$incremental_baseline_root/$path" || ! -f "$path" ]] || \
          ! cmp -s "$incremental_baseline_root/$path" "$path"; then
          printf 'build-native-host: imported source/artifact changed: %s\n' "$path" >&2
          exit 65
      fi
      printf '%s\0' "$path" >> "$reused_paths"
    done
    validated_sources=$((validated_sources + 1))
  done < "$source_modules"
  [[ "$changed_seen" == 1 ]] || {
    printf 'build-native-host: changed module was not reached in source closure\n' >&2
    exit 65
  }
  [[ "$validated_additional_changes" == "${#suffix_allowed_modules[@]}" ]] || {
    printf 'build-native-host: declared suffix change is absent or precedes %s\n' \
      "$incremental_changed_module" >&2
    exit 65
  }
  [[ "$validated_insertions" == "${#inserted_modules[@]}" ]] || {
    printf 'build-native-host: declared inserted module was not reached in suffix\n' >&2
    exit 65
  }
  validated_packages=0
  while IFS= read -r object; do
    package_root=${object%%/.lake/build/ir/*}
    package_module=${object#"$package_root/.lake/build/ir/"}
    package_module=${package_module%.c.o.*}
    for path in "$object" "${object%.o.*}" \
        "$package_root/.lake/build/lib/lean/$package_module.olean"; do
      if [[ ! -f "$incremental_baseline_root/$path" || ! -f "$path" ]] || \
          ! cmp -s "$incremental_baseline_root/$path" "$path"; then
          printf 'build-native-host: package artifact changed: %s\n' "$path" >&2
          exit 65
      fi
      printf '%s\0' "$path" >> "$reused_paths"
    done
    validated_packages=$((validated_packages + 1))
  done < "$baseline_packages"
  xargs -0 -n 50 shasum -a 256 < "$reused_paths" \
    > "$output_dir/reused-artifact-sha256.txt"
  {
    printf 'baseline_snapshot=%s\n' "$incremental_baseline_root"
    printf 'baseline_output=%s\n' "$incremental_baseline_output"
    printf 'baseline_binary_sha256=%s\n' "$baseline_binary_hash"
    printf 'changed_module=%s\n' "$incremental_changed_module"
    printf 'unchanged_imported_modules=%s\n' "$validated_sources"
    printf 'unchanged_later_sources=%s\n' "$validated_tail_sources"
    printf 'additional_changed_sources=%s\n' "$validated_additional_changes"
    printf 'inserted_source_modules=%s\n' "$validated_insertions"
    printf 'restart_source_unchanged=%s\n' "${restart_source_unchanged:-0}"
    printf 'changed_source_manifest=%s\n' "$output_dir/changed-source-sha256.txt"
    printf 'unchanged_package_objects=%s\n' "$validated_packages"
    printf 'changed_source_sha256=%s\n' \
      "$(shasum -a 256 "$changed_source" | cut -d ' ' -f 1)"
    if [[ "$incremental_changed_module" == Host.Main ]]; then
      printf 'changed_host_source_sha256=%s\n' \
        "$(shasum -a 256 "$changed_source" | cut -d ' ' -f 1)"
    fi
  } > "$output_dir/incremental-validation.txt"
  shasum -a 256 "$toolchain/bin/lean" "$toolchain/bin/clang" \
    "$toolchain/bin/leanc" > "$output_dir/toolchain-sha256.txt"
  printf 'incremental source/artifact check PASS %s earlier modules, %s declared later changes, %s inserted modules, %s unchanged later sources, %s package objects\n' \
    "$validated_sources" "$validated_additional_changes" "$validated_insertions" "$validated_tail_sources" "$validated_packages" | tee -a "$output_dir/build.log"
fi

# A companion executable reuses only what a successful build of this same
# snapshot compiled, byte for byte. Every module it names must still match
# that build's source and artifact manifests; drift refuses rather than
# recompiling a module whose importers were already checked against it.
companion_reused="$output_dir/companion-reused-modules.txt"
companion_compiled="$output_dir/companion-compiled-modules.txt"
: > "$companion_reused"
: > "$companion_compiled"
if [[ -n "$companion_output" ]]; then
  companion_output=$(cd "$companion_output" && pwd -P)
  for required in manifest.txt source-sha256.txt source-modules.txt reusable-artifact-sha256.txt; do
    [[ -f "$companion_output/$required" ]] || {
      printf 'build-native-host: companion build lacks %s\n' "$required" >&2
      exit 65
    }
  done
  grep -qxF "root=$root" "$companion_output/manifest.txt" || {
    printf 'build-native-host: companion build is not of this snapshot: %s\n' "$root" >&2
    exit 65
  }
  grep -qxF "lean=$(lean --version | sed -n '1p')" "$companion_output/manifest.txt" || {
    printf 'build-native-host: companion build used another Lean\n' >&2
    exit 65
  }
  companion_check="$output_dir/companion-expected-sha256.txt"
  : > "$companion_check"
  while IFS= read -r module; do
    stem=${module//./\/}
    # Reusable = the companion's own SOURCE closure (source-modules.txt: what reusable-artifact-sha256
    # covers). Not source-sha256.txt: under --umbrella that lists every umbrella module too, and a
    # module only the umbrella built has no reusable entry (the consent closure reaching
    # Theory.MaterializerCardinality, outside the Host closure, refused every consent build at c1df1f08).
    if grep -qxF "$module" "$companion_output/source-modules.txt"; then
      grep -E "^[[:xdigit:]]{64}  $stem\.lean\$" "$companion_output/source-sha256.txt" >> "$companion_check"
      for path in ".lake/build/lib/lean/$stem.olean" ".lake/build/lib/lean/$stem.ilean" \
          ".lake/build/ir/$stem.c" ".lake/build/ir/$stem.c.o.native"; do
        grep -E "^[[:xdigit:]]{64}  $path\$" "$companion_output/reusable-artifact-sha256.txt" \
          >> "$companion_check" || {
          printf 'build-native-host: companion manifest lacks %s\n' "$path" >&2
          exit 65
        }
      done
      printf '%s\n' "$module" >> "$companion_reused"
    else
      printf '%s\n' "$module" >> "$companion_compiled"
    fi
  done < "$source_modules"
  if ! shasum -a 256 -c "$companion_check" > "$output_dir/companion-check.log" 2>&1; then
    printf 'build-native-host: companion artifacts drifted; see %s\n' \
      "$output_dir/companion-check.log" >&2
    exit 65
  fi
  printf 'companion %s: %s reused modules, %s compiled here\n' "$companion_output" \
    "$(wc -l < "$companion_reused" | tr -d ' ')" "$(wc -l < "$companion_compiled" | tr -d ' ')" \
    | tee -a "$output_dir/build.log"
fi

# --- the seated Lean wrapper: every Lake build below runs through it --------------------------
# Lake has no jobs flag: each module job is a default-priority task on Lake's OWN Lean thread pool
# (Lake/Build/Job/Monad.lean, BaseIO.asTask), and the task blocks its worker while its `lean` runs. So
# Lake's LEAN_NUM_THREADS is the build's real compiler concurrency: it ran at the per-compiler 2 until
# 2026-10-31 (batch 3: exactly 2 compilers for 86% of a 2,356 s Lean wall on 12 seats). Lake now gets
# MINIDREGG_LAKE_THREADS workers (default 2 x seats, so seat waiters never starve ready modules) and
# each compiler gets MINIDREGG_LEAN_THREADS through MINIDREGG_LEAN_COMPILER_THREADS. Every Lake build of this script therefore runs with a fake sysroot whose
# bin/lean is a wrapper: it takes one of the host's MINIDREGG_LEAN_SEATS seats (an atomic mkdir under
# MINIDREGG_LEAN_SEAT_ROOT, shared by every build on the host), runs the real compiler with
# -j $MINIDREGG_LEAN_COMPILER_THREADS, logs START/END and releases the seat only after the compiler has exited.
# Lake runs the closure in parallel; the seats are the only bound on concurrent compilers. The fake
# sysroot points every library back at the real immutable toolchain (so the outputs and Lake's traces
# are the real compiler's: publish-artifacts' --umbrella step replays a tree plain Lake built).
toolchain=$(lake env lean --print-prefix)
# HOT-PATH 2d: every lean this build runs loads .lake/native/libmini_kernels_lean.so (the lakefile's
# --load-dynlib), so the kernel library exists BEFORE the first lake build, on every mode: the Rust
# kernels, the Lean shim and the seam closure's objects (scripts/build-mini-kernels.sh, two stages).
scripts/build-mini-kernels.sh > "$output_dir/mini-kernels.log" 2>&1 || {
  printf 'build-native-host: native/mini-kernels did not build; see %s\n' "$output_dir/mini-kernels.log" >&2
  exit 65
}
cp .lake/native/SHA256SUMS "$output_dir/mini-kernels-sha256.txt"
wrapper_root="$output_dir/seated-lean-toolchain"
mkdir -p "$wrapper_root/bin"
cp "$root/scripts/lean-seat-lock.sh" "$wrapper_root/lean-seat-lock.sh"
ln -s "$toolchain/include" "$wrapper_root/include"
ln -s "$toolchain/lib" "$wrapper_root/lib"
ln -s "$toolchain/src" "$wrapper_root/src"
while IFS= read -r executable; do
  name=${executable##*/}
  [[ "$name" == lean ]] || ln -s "$executable" "$wrapper_root/bin/$name"
done < <(find "$toolchain/bin" -maxdepth 1 -type f -print)
# The compiler's own resource use, measured by its parent: wait4(2) returns the child's rusage, whose
# ru_maxrss is the peak resident set (KiB on Linux, bytes on macOS; recorded in KiB). Signals the
# wrapper forwards reach the compiler through this runner; its exit status is the compiler's.
cat > "$wrapper_root/lean-rusage.py" <<'EOF'
import os, signal, subprocess, sys, time
out, argv = sys.argv[1], sys.argv[2:]
child = subprocess.Popen(argv)
for sig in (signal.SIGHUP, signal.SIGINT, signal.SIGTERM):
    signal.signal(sig, lambda n, _f: child.send_signal(n))
t0 = time.monotonic()
while True:
    try:
        _, status, usage = os.wait4(child.pid, 0)
        break
    except InterruptedError:
        continue
child.returncode = 0          # reaped here: keep Popen from waiting again
rss = usage.ru_maxrss // 1024 if sys.platform == "darwin" else usage.ru_maxrss
with open(out, "w") as f:
    f.write(f"{time.monotonic() - t0:.1f}\t{rss}\n")
sys.exit(os.waitstatus_to_exitcode(status) if os.WIFEXITED(status) else 128 + os.WTERMSIG(status))
EOF
cat > "$wrapper_root/bin/lean" <<'EOF'
#!/usr/bin/env bash
# build-native-host.sh's seated Lean: one real compiler per host-wide seat.
set -u
: "${MINIDREGG_REAL_LEAN:?}" "${MINIDREGG_LEAN_SEAT_ROOT:?}" "${MINIDREGG_LEAN_SEATS:?}"
: "${MINIDREGG_LEAN_SEAT_WAIT:?}" "${MINIDREGG_LEAN_WRAPPER_LOG:?}" "${MINIDREGG_LEAN_BUILD_ROOT:?}"
: "${MINIDREGG_LEAN_RUSAGE:?}"
source_file=-
for arg in "$@"; do case "$arg" in *.lean) source_file=$arg ;; esac; done
# Memory-weighted seats: this compiler takes WEIGHT of the host's MINIDREGG_LEAN_SEATS seats, read from
# MINIDREGG_LEAN_SEAT_WEIGHTS (module<TAB>weight, written by build-native-host from recorded peak RSS).
# A module with no row is heavy (all seats) until a build has measured it; a non-module invocation takes 1.
module=-
if [[ "$source_file" == *.lean ]]; then
  module=${source_file#"$MINIDREGG_LEAN_BUILD_ROOT"/}; module=${module#./}; module=${module%.lean}; module=${module//\//.}
fi
weight=1
if [[ "$module" != - ]]; then
  weight=$(awk -F '\t' -v m="$module" '$1 == m { print $2; exit }' "${MINIDREGG_LEAN_SEAT_WEIGHTS:-/dev/null}")
  [[ -n "$weight" ]] || weight=$MINIDREGG_LEAN_SEATS
fi
if (( weight > MINIDREGG_LEAN_SEATS )); then
  printf 'build-native-host: %s alone needs %s of %s Lean seats (its recorded peak RSS exceeds the memory cap): refusing\n' \
    "$module" "$weight" "$MINIDREGG_LEAN_SEATS" >&2
  exit 64
fi
# Acquisition is all-or-nothing under one lock (a mkdir), in ticket order: a waiter takes its WEIGHT seats
# iff (the weights of the live tickets ahead of it) + WEIGHT <= the free seats, so a heavy compiler is never
# starved by a stream of light ones and two half-seated compilers never deadlock.
seats=() locked=0
lockfile=$MINIDREGG_LEAN_SEAT_ROOT/alloc.lock
waiters=$MINIDREGG_LEAN_SEAT_ROOT/waiters
# the lock functions live in lean-seat-lock.sh (copied beside bin/), where scripts/test-lean-seat-lock.sh tests them
source "${BASH_SOURCE[0]%/*}/../lean-seat-lock.sh"
lock() { lean_seat_lock; }
unlock() { lean_seat_unlock; }
release() {
  local d
  for d in ${seats[@]+"${seats[@]}"}; do rm -f "$d/owner.txt"; rmdir "$d" 2>/dev/null || true; done
  seats=(); rm -f "$waiters/$$"; unlock
}
trap release EXIT
mkdir -p "$waiters"; echo "$weight" > "$waiters/$$"
waited=0
while :; do
  if lock; then
    ahead=0
    for f in $(ls -tr "$waiters" 2>/dev/null); do
      [[ "$f" == "$$" ]] && break
      if kill -0 "$f" 2>/dev/null; then ahead=$(( ahead + $(cat "$waiters/$f" 2>/dev/null || echo 0) )); else rm -f "$waiters/$f"; fi
    done
    free=()
    for number in $(seq 1 "$MINIDREGG_LEAN_SEATS"); do
      [[ -e "$MINIDREGG_LEAN_SEAT_ROOT/lean-seat-$number" ]] || free+=("$number")
    done
    if (( ahead + weight <= ${#free[@]} )); then
      for number in "${free[@]:0:$weight}"; do
        candidate="$MINIDREGG_LEAN_SEAT_ROOT/lean-seat-$number"
        # a wrapper from before the lock may take a seat between the count and here: give back and retry
        if mkdir "$candidate" 2>/dev/null; then
          seats+=("$candidate")
          printf 'pid=%s\nstarted_utc=%s\nroot=%s\nsource=%s\nweight=%s\n' "$$" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
            "$MINIDREGG_LEAN_BUILD_ROOT" "$source_file" "$weight" > "$candidate/owner.txt"
        else
          break
        fi
      done
      if (( ${#seats[@]} == weight )); then rm -f "$waiters/$$"; unlock; break; fi
      for d in ${seats[@]+"${seats[@]}"}; do rm -f "$d/owner.txt"; rmdir "$d" 2>/dev/null || true; done; seats=()
    fi
    unlock
  fi
  if (( waited >= MINIDREGG_LEAN_SEAT_WAIT )); then
    printf 'build-native-host: %s needs %s of %s Lean compiler seats under %s; not free after %s s (%s)\n' \
      "$module" "$weight" "$MINIDREGG_LEAN_SEATS" "$MINIDREGG_LEAN_SEAT_ROOT" "$waited" "$source_file" >&2
    exit 75
  fi
  sleep 1
  waited=$((waited + 1))
done
printf 'SEATS\t%s\t%s\t%s\n' "$$" "$weight" "$module" >> "$MINIDREGG_LEAN_WRAPPER_LOG"
child=""
forward_signal() { [[ -z "$child" ]] || kill -"$1" "$child" 2>/dev/null || true; }
trap 'forward_signal HUP' HUP
trap 'forward_signal INT' INT
trap 'forward_signal TERM' TERM
# Each log line is ONE write (O_APPEND): concurrent wrappers never interleave a line.
line=$(printf 'START\t%s\t%s\t' "$(date +%s)" "$$"; printf '%q ' "$@")
printf '%s\n' "$line" >> "$MINIDREGG_LEAN_WRAPPER_LOG"
usage_file=$(mktemp "${TMPDIR:-/tmp}/lean-rusage.XXXXXX")
LEAN_NUM_THREADS=$MINIDREGG_LEAN_COMPILER_THREADS \
  python3 "$MINIDREGG_LEAN_RUSAGE" "$usage_file" "$MINIDREGG_REAL_LEAN" -j "$MINIDREGG_LEAN_COMPILER_THREADS" "$@" &
child=$!
# A trapped signal returns `wait` early while the compiler still runs: keep the seat until it exits.
wait "$child"
code=$?
while kill -0 "$child" 2>/dev/null; do
  wait "$child"
  code=$?
done
# RSS<TAB>pid<TAB>source<TAB>wall_s<TAB>maxrss_kib<TAB>rc, then END (one write each).
usage=$(cat "$usage_file" 2>/dev/null || true)
rm -f "$usage_file"
printf 'RSS\t%s\t%s\t%s\t%s\n' "$$" "$source_file" "${usage:--	-}" "$code" >> "$MINIDREGG_LEAN_WRAPPER_LOG"
printf 'END\t%s\t%s\t%s\n' "$(date +%s)" "$$" "$code" >> "$MINIDREGG_LEAN_WRAPPER_LOG"
exit "$code"
EOF
chmod +x "$wrapper_root/bin/lean"
# --- memory-weighted seats: the cap the seats share, one seat's bytes, and each module's weight -------------
size_kib() {   # SIZE (bytes, or with K/M/G/T) -> KiB
  local v=$1 n u
  [[ "$v" =~ ^([0-9]+)([KkMmGgTt]?)$ ]] || return 1
  n=${BASH_REMATCH[1]} u=${BASH_REMATCH[2]}
  case "$u" in '') echo $(( n / 1024 )) ;; [Kk]) echo "$n" ;; [Mm]) echo $(( n * 1024 )) ;; [Gg]) echo $(( n * 1024 * 1024 )) ;; [Tt]) echo $(( n * 1024 * 1024 * 1024 )) ;; esac
}
mem_cap_kib=""
if [[ -n "${MINIDREGG_LEAN_MEM_CAP:-}" ]]; then
  mem_cap_kib=$(size_kib "$MINIDREGG_LEAN_MEM_CAP") || { printf 'MINIDREGG_LEAN_MEM_CAP must be a size (e.g. 48G)\n' >&2; exit 64; }
  mem_cap_from=MINIDREGG_LEAN_MEM_CAP
elif [[ -r /proc/self/cgroup ]] && cg=$(sed -n 's/^0:://p' /proc/self/cgroup) && [[ -n "$cg" ]]; then
  p=/sys/fs/cgroup${cg%/}
  while :; do
    m=$(cat "$p/memory.max" 2>/dev/null || true)
    if [[ "$m" =~ ^[0-9]+$ ]] && { [[ -z "$mem_cap_kib" ]] || (( m / 1024 < mem_cap_kib )); }; then mem_cap_kib=$(( m / 1024 )); mem_cap_from=$p/memory.max; fi
    [[ "$p" == /sys/fs/cgroup || "$p" != /sys/fs/cgroup/* ]] && break
    p=${p%/*}
  done
fi
if [[ -z "$mem_cap_kib" ]]; then mem_cap_kib=$(size_kib "${SWARM_MEM_MAX:-48G}") || { printf 'SWARM_MEM_MAX must be a size\n' >&2; exit 64; }; mem_cap_from="SWARM_MEM_MAX (${SWARM_MEM_MAX:-48G}; no cgroup cap)"; fi
seat_kib=$(( mem_cap_kib / lean_seats ))
seat_weights="$output_dir/lean-seat-weights.tsv"
rss_sources=()
if [[ -f "$root/scripts/pipeline/lean-module-rss.tsv" ]]; then rss_sources+=("$root/scripts/pipeline/lean-module-rss.tsv"); fi
IFS=: read -r -a extra_rss <<< "${MINIDREGG_LEAN_RSS_FROM:-}"
for f in ${extra_rss[@]+"${extra_rss[@]}"}; do [[ -z "$f" ]] && continue; [[ -f "$f" ]] || { printf 'MINIDREGG_LEAN_RSS_FROM: no table %s\n' "$f" >&2; exit 64; }; rss_sources+=("$f"); done
# module<TAB>weight<TAB>maxrss_kib: per module the max recorded peak over every table; weight = ceil(rss / seat)
awk -F '\t' -v seat="$seat_kib" '$0 !~ /^#/ && $3 ~ /^[0-9]+$/ { if ($3 > r[$1]) r[$1] = $3 }
  END { for (m in r) { w = int((r[m] + seat - 1) / seat); if (w < 1) w = 1; print m "\t" w "\t" r[m] } }' \
  ${rss_sources[@]+"${rss_sources[@]}"} /dev/null | LC_ALL=C sort > "$seat_weights"
over=$(awk -F '\t' -v cap="$mem_cap_kib" -v root="$root" '$3 > cap { f = $1; gsub(/\./, "/", f); if ((getline l < (root "/" f ".lean")) >= 0) print $1 " (" $3 " KiB)" }' "$seat_weights")
# A module whose recorded peak alone exceeds the cap gets a weight above the seats, and the wrapper refuses
# it by name (64) at the moment Lake asks to COMPILE it. It is not refused here: a replay or a cache fetch
# (a gated tree published under a small cap) never invokes the compiler for it, and must not be refused
# for a compile that does not happen. The list is printed so a refusal later is expected, not a surprise.
if [[ -n "$over" ]]; then
  printf 'build-native-host: over-cap modules (recorded peak RSS exceeds the %s KiB Lean memory cap, %s): each refuses by name if it must compile here:\n%s\n' \
    "$mem_cap_kib" "$mem_cap_from" "$over" | tee -a "$output_dir/build.log" >&2
fi
printf 'lean-seats memory-weighted: cap=%sKiB (%s) seats=%s seat=%sKiB; %s modules weighted from %s table(s), unrecorded modules take all %s seats\n' \
  "$mem_cap_kib" "$mem_cap_from" "$lean_seats" "$seat_kib" "$(wc -l < "$seat_weights" | tr -d ' ')" "${#rss_sources[@]}" "$lean_seats" | tee -a "$output_dir/build.log"
wrapper_log="$output_dir/lake-lean-wrapper.tsv"
: > "$wrapper_log"
lake_cc=${MINIDREGG_NATIVE_LAKE_CC:-$toolchain/bin/clang}
# seated_lake LOG TARGET...: `lake build TARGET...` through the seated wrapper, output to LOG.
seated_lake() {
  local log=$1
  shift
  env \
    LAKE_OVERRIDE_LEAN=true \
    LEAN_SYSROOT="$wrapper_root" \
    LEAN_CC="$lake_cc" \
    LEAN_AR="$toolchain/bin/llvm-ar" \
    LEAN_NUM_THREADS="$lake_threads" \
    MINIDREGG_LEAN_COMPILER_THREADS="$lean_threads" \
    MINIDREGG_REAL_LEAN="$toolchain/bin/lean" \
    MINIDREGG_LEAN_SEAT_ROOT="$seat_root" \
    MINIDREGG_LEAN_SEATS="$lean_seats" \
    MINIDREGG_LEAN_SEAT_WAIT="$seat_wait" \
    MINIDREGG_LEAN_WRAPPER_LOG="$wrapper_log" \
    MINIDREGG_LEAN_BUILD_ROOT="$root" \
    MINIDREGG_LEAN_RUSAGE="$wrapper_root/lean-rusage.py" \
    MINIDREGG_LEAN_SEAT_WEIGHTS="$seat_weights" \
    lake build "$@" > "$log" 2>&1
}

compiled_sources=0
# The modes that reuse a byte-checked PREFIX of the import order (--checkpoint-resume, --resume-failed,
# --resume-complete-lean, --reuse-success-prefix-from) or start at a named module of it
# (--incremental-host-from, --incremental-suffix-from) checkpoint and skip module by module, so they
# keep the ordered loop (still seated). Every other non-umbrella build is ONE parallel Lake build of
# the same per-module facet set the loop requested.
ordered_loop=0
if [[ "$checkpoint_resume" == 1 || -n "$incremental_baseline_root" ]]; then
  ordered_loop=1
fi
if [[ "$build_umbrella" == 0 && "$ordered_loop" == 1 ]]; then
  index=0
  incremental_started=0
  total=$(wc -l < "$build_modules" | tr -d ' ')
  while IFS= read -r module; do
    if [[ "$resume_prefix" -gt 0 && "$index" -lt "$resume_prefix" ]]; then
      index=$((index + 1))
      continue
    fi
    if [[ -n "$incremental_baseline_root" && "$incremental_started" == 0 ]]; then
      if [[ "$module" == "$incremental_changed_module" ]]; then
        incremental_started=1
      else
        index=$((index + 1))
        continue
      fi
    fi
    index=$((index + 1))
    compiled_sources=$((compiled_sources + 1))
    safe=${module//./_}
    log="$output_dir/lean/$(printf '%04d' "$index")-$safe.log"
    one_start=$(date +%s)
    printf 'lean[%s/%s] %s start\n' "$index" "$total" "$module" | tee -a "$output_dir/build.log"
    stem=${module//./\/}
    mkdir -p ".lake/build/lib/lean/$(dirname "$stem")" ".lake/build/ir/$(dirname "$stem")"
    # LAKE compiles the module (its leanArts facet: .olean, .ilean, .c), never a bare
    # `lake env lean -o -i -c`. Lake hands Lean the module's setup (package "minidregg"), and only
    # with it does the C name the package: `initialize_minidregg_<Module>`. The bare call emitted
    # `initialize_<Module>` (and a different .olean) into .lake/build under Lake's unchanged trace;
    # a later Lake build in that tree stored those files in the shared artifact cache, and every
    # lane that fetched them failed to link any lean_exe (79 poisoned .c on burst2-b, 10-07).
    # Lake also replaces its outputs instead of writing through a cache-restored hard link.
    if seated_lake "$log" "+$module:leanArts"; then
      printf 'lean[%s/%s] %s PASS %ss\n' \
        "$index" "$total" "$module" "$(( $(date +%s) - one_start ))" | tee -a "$output_dir/build.log"
      if [[ "$checkpoint_resume" == 1 ]]; then
        checkpoint="$resume_checkpoint_dir/$(printf '%04d' "$index")-${module//./_}.sha256"
        checkpoint_tmp="$checkpoint.tmp.$$"
        module_checkpoint_paths "$stem" | while IFS= read -r artifact; do
          shasum -a 256 "$artifact"
        done > "$checkpoint_tmp"
        mv "$checkpoint_tmp" "$checkpoint"
      fi
    else
      code=$?
      printf 'lean[%s/%s] %s FAIL(%s) log=%s\n' \
        "$index" "$total" "$module" "$code" "$log" | tee -a "$output_dir/build.log" >&2
      tail -100 "$log" >&2
      exit "$code"
    fi
  done < "$build_modules"
elif [[ "$build_umbrella" == 0 ]]; then
  # Every module's leanArts (.olean, .ilean, .c) in ONE Lake build: Lake compiles what is stale in
  # parallel (the seats bound it), replays the rest, and is still the only writer of its outputs (the
  # loop's poisoning guard above holds unchanged). A companion's reused modules are not requested;
  # Lake reads them as imports, and their bytes are checked again after the build.
  lake_targets="$output_dir/lake-leanarts-targets.txt"
  if [[ -n "$companion_output" ]]; then
    grep -vxF -f "$companion_reused" "$build_modules" > "$lake_targets.modules" || true
  else
    cp "$build_modules" "$lake_targets.modules"
  fi
  sed 's/^/+/; s/$/:leanArts/' "$lake_targets.modules" > "$lake_targets"
  rm -f "$lake_targets.modules"
  while IFS= read -r module; do
    stem=${module//./\/}
    mkdir -p ".lake/build/lib/lean/$(dirname "$stem")" ".lake/build/ir/$(dirname "$stem")"
  done < <(sed 's/^+//; s/:leanArts$//' "$lake_targets")
  if [[ -s "$lake_targets" ]]; then
    lake_target_args=()
    while IFS= read -r target; do lake_target_args+=("$target"); done < "$lake_targets"
    leanarts_log="$output_dir/lake-build-leanArts.log"
    printf 'lake build %s +MODULE:leanArts targets\n' "${#lake_target_args[@]}" \
      > "$output_dir/lake-build-leanArts.command.txt"
    one_start=$(date +%s)
    printf 'lean-closure %s modules start (seats=%s threads=%s)\n' \
      "${#lake_target_args[@]}" "$lean_seats" "$lean_threads" | tee -a "$output_dir/build.log"
    if seated_lake "$leanarts_log" "${lake_target_args[@]}"; then
      printf 'lean-closure %s modules PASS %ss\n' \
        "${#lake_target_args[@]}" "$(( $(date +%s) - one_start ))" | tee -a "$output_dir/build.log"
    else
      code=$?
      printf 'lean-closure FAIL(%s) log=%s\n' "$code" "$leanarts_log" | tee -a "$output_dir/build.log" >&2
      tail -100 "$leanarts_log" >&2
      exit "$code"
    fi
  fi
  if [[ -n "$companion_output" ]] &&
     ! shasum -a 256 -c "$companion_check" > "$output_dir/companion-recheck.log" 2>&1; then
    printf 'build-native-host: companion artifacts changed during the build; see %s\n' \
      "$output_dir/companion-recheck.log" >&2
    exit 65
  fi
  # Lake may reuse the entire warm closure; count actual source invocations.
  compiled_sources=$(awk -F '\t' '$1 == "START" && $4 ~ /\.lean( |$)/ { n++ } END { print n+0 }' "$wrapper_log")
fi

if [[ "$build_umbrella" == 1 ]]; then
  lake_gate_log="$output_dir/lake-build-$umbrella_tag.log"
  cat > "$output_dir/lake-build-$umbrella_tag.command.txt" <<EOF
LAKE_OVERRIDE_LEAN=true LEAN_SYSROOT=$wrapper_root LEAN_NUM_THREADS=$lake_threads MINIDREGG_LEAN_COMPILER_THREADS=$lean_threads MINIDREGG_LEAN_SEATS=$lean_seats lake build $umbrella_target
EOF
  gate_start=$(date +%s)
  printf 'lake-gate %s start\n' "$umbrella_target" | tee -a "$output_dir/build.log"
  if seated_lake "$lake_gate_log" "${umbrella_targets[@]}"; then
    printf 'lake-gate %s PASS %ss\n' "$umbrella_target" \
      "$(( $(date +%s) - gate_start ))" | tee -a "$output_dir/build.log"
    if [[ "$umbrella_only" == 1 ]]; then
      printf 'lake_gate=lake build %s\nlean_seats=%s\n' "$umbrella_target" "$lean_seats" > "$output_dir/manifest.txt"
      exit 0
    fi
  else
    code=$?
    printf 'lake-gate %s FAIL(%s) log=%s\n' "$umbrella_target" \
      "$code" "$lake_gate_log" | tee -a "$output_dir/build.log" >&2
    tail -100 "$lake_gate_log" >&2
    exit "$code"
  fi

  # `leanArts` invokes Lean with -o/-i/-c.  Build the executable's separate
  # Host library through the same wrapper after the literal umbrella gate; the
  # resulting C files feed the native link below without a duplicate source pass.
  host_gate_log="$output_dir/lake-build-Host.Main-leanArts.log"
  cat > "$output_dir/lake-build-Host.Main-leanArts.command.txt" <<EOF
LAKE_OVERRIDE_LEAN=true LEAN_SYSROOT=$wrapper_root LEAN_NUM_THREADS=$lake_threads MINIDREGG_LEAN_COMPILER_THREADS=$lean_threads MINIDREGG_LEAN_SEATS=$lean_seats lake build +Host.Main:leanArts
EOF
  gate_start=$(date +%s)
  printf 'lake-gate Host.Main:leanArts start\n' | tee -a "$output_dir/build.log"
  if seated_lake "$host_gate_log" +Host.Main:leanArts; then
    printf 'lake-gate Host.Main:leanArts PASS %ss\n' \
      "$(( $(date +%s) - gate_start ))" | tee -a "$output_dir/build.log"
  else
    code=$?
    printf 'lake-gate Host.Main:leanArts FAIL(%s) log=%s\n' \
      "$code" "$host_gate_log" | tee -a "$output_dir/build.log" >&2
    tail -100 "$host_gate_log" >&2
    exit "$code"
  fi
  # The umbrella gate must have run the wrapper at all (a Lake that bypassed the sysroot would compile
  # unseated and unlogged).
  grep -q '^START' "$wrapper_log" || {
    printf 'build-native-host: the umbrella gate never ran the seated Lean wrapper: %s\n' "$wrapper_log" >&2
    exit 70
  }
  # Lake may reuse the entire warm closure; count actual source invocations.
  compiled_sources=$(awk -F '\t' '$1 == "START" && $4 ~ /\.lean( |$)/ { n++ } END { print n+0 }' "$wrapper_log")
fi

# Every compiler the wrapper started has ended, each pid once, each with its SEATS line, and at no point did
# this build hold more seat WEIGHT than the host has seats (START is logged after a seat is taken, END before it is
# released, so the file order bounds the overlap).
if ! concurrency=$(awk -F '\t' -v seats="$lean_seats" '
    $1 == "SEATS" { w[$2] = $3 }
    $1 == "START" { if ($3 in open || !($3 in w)) bad = 1; open[$3] = 1; n++; if (n > m) m = n; held += w[$3]; if (held > mh) mh = held; starts++ }
    $1 == "END" { if (!($3 in open)) bad = 1; delete open[$3]; n--; held -= w[$3]; ends++ }
    END { if (bad || n != 0 || held != 0 || starts != ends || mh > seats) exit 1; print m + 0, mh + 0 }
  ' "$wrapper_log"); then
  printf 'build-native-host: seated Lean wrapper log is unbalanced or exceeds %s seats: %s\n' \
    "$lean_seats" "$wrapper_log" >&2
  exit 70
fi
read -r max_concurrent_lean max_seat_weight <<< "$concurrency"
# Per compiled module: wall and peak RSS, so seats and threads are sized from data (CYCLE-TIME F10).
# lean-module-rss.tsv: module<TAB>wall_s<TAB>maxrss_kib<TAB>rc, heaviest first; one line each into build.log.
rss_table="$output_dir/lean-module-rss.tsv"
awk -F '\t' -v root="$root/" '$1 == "RSS" && $3 ~ /\.lean$/ {
    m = $3; if (index(m, root) == 1) m = substr(m, length(root) + 1); sub(/^\.\//, "", m)
    sub(/\.lean$/, "", m); gsub(/\//, ".", m); print m "\t" $4 "\t" $5 "\t" $6 }' "$wrapper_log" \
  | sort -t "$(printf '\t')" -k3,3nr > "$rss_table"
awk -F '\t' '{ printf "lean-rss %s wall=%ss maxrss=%sKiB rc=%s\n", $1, $2, $3, $4 }' "$rss_table" >> "$output_dir/build.log"
rss_stats=$(awk -F '\t' '$3 ~ /^[0-9]+$/ { v[n++] = $3 } END {
    if (!n) { print "0 0 0"; exit }
    # sorted descending already: p50 and p95 by rank
    print v[int(n * 0.5)], v[int(n * 0.05)], v[0] }' "$rss_table")
read -r rss_p50 rss_p95 rss_max <<< "$rss_stats"
printf 'lean_seats=%s\nlean_mem_cap_kib=%s\nlean_seat_kib=%s\nmax_concurrent_real_lean=%s\nmax_concurrent_seat_weight=%s\nunrecorded_rss_modules=%s\nwrapper_invocations=%s\nlean_maxrss_kib_p50=%s\nlean_maxrss_kib_p95=%s\nlean_maxrss_kib_max=%s\n' \
  "$lean_seats" "$mem_cap_kib" "$seat_kib" "$max_concurrent_lean" "$max_seat_weight" \
  "$(awk -F '\t' 'NR == FNR { k[$1] = 1; next } $1 == "SEATS" && $4 != "-" && !($4 in k) { n++ } END { print n + 0 }' "$seat_weights" "$wrapper_log")" \
  "$(grep -c '^START' "$wrapper_log")" "$rss_p50" "$rss_p95" "$rss_max" \
  > "$output_dir/lake-wrapper-summary.txt"
printf 'lean-rss summary: %s compiled modules, maxrss p50=%sKiB p95=%sKiB max=%sKiB (%s)\n' \
  "$(wc -l < "$rss_table" | tr -d ' ')" "$rss_p50" "$rss_p95" "$rss_max" "$rss_table" | tee -a "$output_dir/build.log"

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
if [[ -n "$incremental_baseline_root" ]]; then
  cmp -s "$incremental_baseline_output/compile-args.txt" "$compile_args" || {
    printf 'build-native-host: incremental C compiler arguments changed\n' >&2
    exit 65
  }
  shasum -a 256 "$compile_args" >> "$output_dir/toolchain-sha256.txt"
fi
if [[ -n "$resume_complete_output" ]]; then
  cmp -s "$resume_complete_output/compile-args.txt" "$compile_args" || {
    printf 'build-native-host: post-Lean C compiler arguments changed\n' >&2
    exit 65
  }
fi

export toolchain output_dir
project_c_modules="$source_modules"
if [[ -n "$companion_output" ]]; then
  project_c_modules="$companion_compiled"
fi
if [[ -n "$success_baseline_root" ]]; then
  project_c_modules="$output_dir/project-c-recompiled-modules.txt"
  tail -n "+$((resume_prefix + 1))" "$source_modules" > "$project_c_modules"
fi
# One compile of one generated C file: cc-object.sh C_PATH OBJECT LOG. Every object this builder makes goes
# through it, with the one flag set below. MINIDREGG_NATIVE_OBJECT_CACHE=DIR (unset: no cache) reuses an object
# by CONTENT: the key is sha256 over (the toolchain's clang and include tree, the flags, the C file's path as
# given -- an ELF object names its source -- and the C file's bytes), so a hit is the object this compile would
# produce, and a set built with the cache is byte-identical to one built without it. Misses compile and are
# stored (tmp + rename, so a concurrent build never reads half an object). Hits/misses: object-cache.tsv.
cc_flags='-fstack-clash-protection -fdata-sections -ffunction-sections -fvisibility=hidden -Wno-unused-command-line-argument -O3 -DNDEBUG -DLEAN_EXPORTING'
object_cache=${MINIDREGG_NATIVE_OBJECT_CACHE:-}
toolchain_key=""
if [[ -n "$object_cache" ]]; then
  mkdir -p "$object_cache"
  toolchain_key=$( { shasum -a 256 "$toolchain/bin/clang"; (cd "$toolchain/include" && find . -type f -print0 | LC_ALL=C sort -z | xargs -0 shasum -a 256); } | shasum -a 256 | cut -d' ' -f1)
fi
cat > "$output_dir/cc-object.sh" <<CC
#!/usr/bin/env bash
set -euo pipefail
c_path=\$1 object=\$2 log=\$3
compile() {
  "$toolchain/bin/clang" -c -o "\$1" "\$c_path" -I "$toolchain/include" $cc_flags \\
    --sysroot "$toolchain" -nostdinc -isystem "$toolchain/include/clang" > "\$log" 2>&1
}
cache="$object_cache"
if [[ -z "\$cache" ]]; then compile "\$object"; exit 0; fi
key=\$( { printf '%s\n%s\n%s\n' "$toolchain_key" "$cc_flags" "\$c_path"; cat "\$c_path"; } | shasum -a 256 | cut -c1-64)
hit="\$cache/\${key:0:2}/\$key.o"
if [[ -f "\$hit" ]]; then
  cp "\$hit" "\$object"; touch "\$hit"; printf 'hit\t%s\n' "\$c_path" >> "$output_dir/object-cache.tsv"; : > "\$log"; exit 0
fi
compile "\$object"
mkdir -p "\$cache/\${key:0:2}"
tmp="\$cache/\${key:0:2}/.\$key.\$\$"
cp "\$object" "\$tmp" && mv -f "\$tmp" "\$hit"
printf 'miss\t%s\n' "\$c_path" >> "$output_dir/object-cache.tsv"
CC
chmod +x "$output_dir/cc-object.sh"
: > "$output_dir/object-cache.tsv"
# This single-quoted text is the child bash body, not parent interpolation.
# shellcheck disable=SC2016
if [[ -s "$project_c_modules" ]]; then
  xargs -P "$native_jobs" -n 1 bash -c '
  set -euo pipefail
  module=$1
  stem=${module//./\/}
  c_path=".lake/build/ir/$stem.c"
  object="$c_path.o.native"
  [[ -f "$c_path" ]] || { printf "missing generated C: %s\n" "$c_path" >&2; exit 66; }
  mkdir -p "$(dirname "$object")"
  "$output_dir/cc-object.sh" "$c_path" "$object" "$output_dir/c/${module//./_}.log"
' build-module < "$project_c_modules"
fi

# Objects THIS builder compiles are named *.c.o.native, never Lake's own *.c.o.export: Lake owns
# that name under its unchanged traces, and overwriting it (hidden visibility, other flags) made a
# later `lake build <exe>` in the same tree link these objects and fail on undefined lp_*/initialize_*
# symbols (merge keeper, b5 gate clone, 10-07). A package module's object is ours when we compiled
# one (*.c.o.native), else Lake's *.c.o.export, used read-only.
make_package_index() {
  find .lake/packages -type f \( -path '*/.lake/build/ir/*.c.o.export' -o -path '*/.lake/build/ir/*.c.o.native' \) -print | awk '
    {
      path=$0
      marker="/.lake/build/ir/"
      pos=index(path, marker)
      if (!pos) next
      rel=substr(path, pos + length(marker))
      native=(rel ~ /\.c\.o\.native$/)
      sub(/\.c\.o\.(export|native)$/, "", rel)
      dir=substr(path, 1, pos - 1)
      module=rel
      gsub(/\//, ".", module)
      key=dir "\t" module
      if (!(key in best) || native) best[key]=path
      mod[key]=module
    }
    END { for (k in best) print mod[k] "\t" best[k] }
  ' | sort -t $'\t' -k1,1 -k2,2
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
if [[ -s "$output_dir/missing-package-objects.txt" ]]; then
  # Index the package tree once. A per-module find walks the same large tree
  # thousands of times on a cold native build.
  package_c_index="$output_dir/package-c-index.tsv"
  find .lake/packages -type f -path '*/.lake/build/ir/*.c' -print | awk '
    {
      path=$0
      marker="/.lake/build/ir/"
      pos=index(path, marker)
      if (!pos) next
      rel=substr(path, pos + length(marker))
      sub(/\.c$/, "", rel)
      module=rel
      gsub(/\//, ".", module)
      print module "\t" path
    }
  ' | sort -t $'\t' -k1,1 -k2,2 > "$package_c_index"
  cut -f1 "$package_c_index" | sort -u > "$output_dir/package-c-modules.txt"
  comm -23 "$output_dir/missing-package-objects.txt" "$output_dir/package-c-modules.txt" \
    > "$output_dir/unresolved-package-c-modules.txt"
  comm -12 "$output_dir/missing-package-objects.txt" \
    <(cut -f1 "$package_c_index" | uniq -d) \
    > "$output_dir/ambiguous-package-c-modules.txt"
  if [[ -s "$output_dir/unresolved-package-c-modules.txt" ||
        -s "$output_dir/ambiguous-package-c-modules.txt" ]]; then
    printf 'build-native-host: missing or ambiguous package generated C; see %s and %s\n' \
      "$output_dir/unresolved-package-c-modules.txt" \
      "$output_dir/ambiguous-package-c-modules.txt" >&2
    exit 66
  fi
  join -t $'\t' -1 1 -2 1 "$output_dir/missing-package-objects.txt" \
    "$package_c_index" | cut -f2 | while IFS= read -r c_path; do
      printf '%s\0' "$c_path"
    done > "$missing_package_c"
fi
if [[ -s "$missing_package_c" ]]; then
  # The single-quoted child body expands task-specific variables in bash.
  # shellcheck disable=SC2016
  xargs -0 -P "$native_jobs" -n 1 bash -c '
    set -euo pipefail
    c_path=$1
    object="$c_path.o.native"
    module=${c_path#*/.lake/build/ir/}
    module=${module%.c}
    "$output_dir/cc-object.sh" "$c_path" "$object" "$output_dir/c/package-${module//\//_}.log"
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
  c_path=${object%.o.*}
  object="$c_path.o.native"
  [[ -f "$c_path" ]] || {
    printf 'build-native-host: wrong-architecture object has no generated C: %s\n' "$object" >&2
    exit 66
  }
  "$output_dir/cc-object.sh" "$c_path" "$object" "$output_dir/c/wrongarch-$(basename "$c_path").log"
done < "$output_dir/wrong-architecture-package-objects.txt"
if [[ -s "$output_dir/wrong-architecture-package-objects.txt" ]]; then
  # the recompiled objects are *.c.o.native beside Lake's: resolve the package objects again
  make_package_index > "$package_index"
  join -t $'\t' -1 1 -2 1 "$package_required" "$package_index" > "$package_objects_tsv"
  cut -f2 "$package_objects_tsv" > "$output_dir/package-objects.txt"
fi
file -f "$output_dir/package-objects.txt" > "$output_dir/package-object-types-final.txt"
if grep -vF "$native_object_description" "$output_dir/package-object-types-final.txt" \
    > "$output_dir/wrong-architecture-package-objects-final.txt"; then
  printf 'build-native-host: package objects remain incompatible after recompilation; see %s\n' \
    "$output_dir/wrong-architecture-package-objects-final.txt" >&2
  exit 66
fi

response="$output_dir/${binary##*/}.rsp"
: > "$response"
while IFS= read -r module; do
  stem=${module//./\/}
  printf '%s\n' ".lake/build/ir/$stem.c.o.native" >> "$response"
done < "$source_modules"
cat "$output_dir/package-objects.txt" >> "$response"
# HOT-PATH 2d: the Rust kernels the compiled hashes call through @[extern] (native/mini-kernels)
# are link inputs of every Lean executable (built above, before the Lean closure).
[[ -f .lake/native/link-inputs.txt ]] || {
  printf 'build-native-host: .lake/native/link-inputs.txt missing (scripts/build-mini-kernels.sh did not run)\n' >&2
  exit 65
}
cat .lake/native/link-inputs.txt >> "$response"

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
awk -v prefix="$usage_prefix" 'index($0, prefix) == 1 { found = 1 } END { exit !found }' \
    "$output_dir/usage.txt" || {
  printf 'build-native-host: linked binary did not print its usage contract\n' >&2
  exit 70
}

while IFS= read -r module; do
  source=${module//./\/}.lean
  shasum -a 256 "$source"
done < "$build_modules" > "$output_dir/source-sha256.txt"
reusable_paths="$output_dir/reusable-artifact-paths.nul"
: > "$reusable_paths"
while IFS= read -r module; do
  stem=${module//./\/}
  for path in ".lake/build/lib/lean/$stem.olean" \
      ".lake/build/lib/lean/$stem.ilean" \
      ".lake/build/ir/$stem.c" \
      ".lake/build/ir/$stem.c.o.native"; do
    [[ -f "$path" ]] || { printf 'missing reusable project artifact: %s\n' "$path" >&2; exit 66; }
    printf '%s\0' "$path" >> "$reusable_paths"
  done
done < "$source_modules"
while IFS= read -r object; do
  package_root=${object%%/.lake/build/ir/*}
  package_module=${object#"$package_root/.lake/build/ir/"}
  package_module=${package_module%.c.o.*}
  for path in "$object" "${object%.o.*}" \
      "$package_root/.lake/build/lib/lean/$package_module.olean"; do
    [[ -f "$path" ]] || { printf 'missing reusable package artifact: %s\n' "$path" >&2; exit 66; }
    printf '%s\0' "$path" >> "$reusable_paths"
  done
done < "$output_dir/package-objects.txt"
xargs -0 -n 50 shasum -a 256 < "$reusable_paths" \
  > "$output_dir/reusable-artifact-sha256.txt"
if [[ "$checkpoint_resume" == 1 ]]; then
  # Refresh checkpoints after C compilation: a warm copy may have carried
  # older objects when the Lean-only checkpoint was first written.
  index=0
  while IFS= read -r module; do
    index=$((index + 1))
    stem=${module//./\/}
    checkpoint="$resume_checkpoint_dir/$(printf '%04d' "$index")-${module//./_}.sha256"
    checkpoint_tmp="$checkpoint.tmp.$$"
    module_checkpoint_paths "$stem" | while IFS= read -r artifact; do
      shasum -a 256 "$artifact"
    done > "$checkpoint_tmp"
    mv "$checkpoint_tmp" "$checkpoint"
  done < "$source_modules"
  find "$resume_checkpoint_dir" -maxdepth 1 -type f -name '*.sha256' -print0 \
    | sort -z | xargs -0 -n 50 shasum -a 256 \
    > "$output_dir/success-checkpoint-sha256.txt"
  [[ "$(wc -l < "$output_dir/success-checkpoint-sha256.txt" | tr -d ' ')" == \
     "$(wc -l < "$source_modules" | tr -d ' ')" ]] || {
    printf 'build-native-host: successful checkpoint count differs from closure\n' >&2
    exit 65
  }
  (cd "$root" && shasum -a 256 -c "$resume_inputs") \
    > "$output_dir/success-external-input-check.log"
  (cd "$root" && shasum -a 256 -c "$source_inputs") \
    > "$output_dir/success-source-input-check.log"
fi
shasum -a 256 "$binary" "$response" "$closure" > "$output_dir/artifact-sha256.txt"
shasum -a 256 "$output_dir/reusable-artifact-sha256.txt" \
  >> "$output_dir/artifact-sha256.txt"
if [[ "$checkpoint_resume" == 1 ]]; then
  shasum -a 256 "$resume_inputs" "$output_dir/resume-contract.txt" \
    "$source_inputs" \
    "$output_dir/toolchain-symlinks.txt" \
    "$output_dir/package-symlinks-recursive.txt" \
    "$output_dir/success-checkpoint-sha256.txt" \
    >> "$output_dir/artifact-sha256.txt"
fi
if [[ "$build_umbrella" == 1 ]]; then
  shasum -a 256 "$umbrella_closure" >> "$output_dir/artifact-sha256.txt"
fi
if [[ "$source_git" == 1 ]]; then
  git status --short > "$output_dir/git-status.txt"
fi
{
  printf 'end_utc=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf 'elapsed_seconds=%s\n' "$(( $(date +%s) - start_epoch ))"
  if [[ "$source_git" == 1 ]]; then
    printf 'git_head=%s\n' "$(git rev-parse HEAD)"
  else
    printf 'git_head=none (source tree is not a git checkout)\n'
  fi
  printf 'root=%s\n' "$root"
  printf 'lean=%s\n' "$(lean --version | sed -n '1p')"
  printf 'toolchain=%s\n' "$toolchain"
  printf 'native_target=%s:%s\n' "$(uname -s)" "$(uname -m)"
  printf 'umbrella=%s\n' "$build_umbrella"
  printf 'root_module=%s\n' "$root_module"
  if [[ -n "$companion_output" ]]; then
    printf 'companion_of=%s\n' "$companion_output"
    printf 'companion_reused_modules=%s\n' "$(wc -l < "$companion_reused" | tr -d ' ')"
  fi
  if [[ -n "$incremental_baseline_root" ]]; then
    printf 'incremental_baseline=%s\n' "$incremental_baseline_output"
    printf 'incremental_changed_module=%s\n' "$incremental_changed_module"
    printf 'unchanged_imported_modules=%s\n' "$validated_sources"
    printf 'unchanged_later_sources=%s\n' "$validated_tail_sources"
    printf 'inserted_source_modules=%s\n' "$validated_insertions"
    printf 'restart_source_unchanged=%s\n' "${restart_source_unchanged:-0}"
    printf 'unchanged_package_objects=%s\n' "$validated_packages"
    printf 'reused_artifact_manifest=%s\n' "$output_dir/reused-artifact-sha256.txt"
  fi
  if [[ "$build_umbrella" == 1 ]]; then
    printf 'lake_gate=lake build %s\n' "$umbrella_target"
  fi
  printf 'lean_seats=%s\n' "$lean_seats"
  printf 'lean_threads=%s\n' "$lean_threads"
  printf 'max_concurrent_real_lean=%s\n' "$max_concurrent_lean"
  printf 'lean_maxrss_kib_p95=%s\n' "$rss_p95"
  printf 'lean_maxrss_kib_max=%s\n' "$rss_max"
  printf 'wrapper_invocations=%s\n' "$(grep -c '^START' "$wrapper_log")"
  if [[ -n "$incremental_baseline_root" ]]; then
    printf 'compiled_source_modules=%s\n' "$compiled_sources"
  else
    printf 'compiled_source_modules=%s\n' "$compiled_sources"
    printf 'resumed_prefix_modules=%s\n' "$resume_prefix"
  fi
  printf 'source_modules=%s\n' "$(wc -l < "$source_modules" | tr -d ' ')"
  printf 'package_modules=%s\n' "$(wc -l < "$package_required" | tr -d ' ')"
  printf 'response_objects=%s\n' "$(wc -l < "$response" | tr -d ' ')"
  printf 'reusable_artifact_manifest_sha256=%s\n' \
    "$(shasum -a 256 "$output_dir/reusable-artifact-sha256.txt" | cut -d ' ' -f 1)"
  if [[ "$checkpoint_resume" == 1 ]]; then
    printf 'checkpointed_success=1\n'
    if [[ -n "$resume_complete_output" ]]; then
      printf 'post_lean_recovery=%s\n' "$resume_complete_output"
      printf 'post_lean_prior_builder_sha256=%s\n' "$resume_complete_builder_sha"
      printf 'recompiled_project_c_modules=%s\n' \
        "$(wc -l < "$project_c_modules" | tr -d ' ')"
    fi
    if [[ -n "$success_baseline_root" ]]; then
      printf 'successful_baseline=%s\n' "$success_baseline_output"
      printf 'reused_success_prefix_modules=%s\n' "$resume_prefix"
      printf 'recompiled_project_c_modules=%s\n' \
        "$(wc -l < "$project_c_modules" | tr -d ' ')"
    fi
  fi
  printf 'usage_exit=%s\n' "$usage_exit"
  printf 'binary=%s\n' "$binary"
  printf 'binary_sha256=%s\n' "$(shasum -a 256 "$binary" | awk '{print $1}')"
} > "$output_dir/manifest.txt"
cat "$output_dir/manifest.txt" | tee -a "$output_dir/build.log"
