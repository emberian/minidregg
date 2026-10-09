# Shared helpers for the Mini candidate scripts. Source this file; it defines
# functions and no top-level side effects. See INTERFACES.md.

candidate_die() {
  printf '%s: %s\n' "${CANDIDATE_PROG:-candidate}" "$*" >&2
  exit 1
}

candidate_require() {
  for command in "$@"; do
    command -v "$command" >/dev/null 2>&1 || candidate_die "required command not found: $command"
  done
}

candidate_abs() {
  case "$1" in
    /*) printf '%s\n' "$1" ;;
    *) printf '%s/%s\n' "$(pwd -P)" "$1" ;;
  esac
}

candidate_sha256() {
  sha256sum "$1" | cut -d ' ' -f 1
}

# candidate_resolve MANIFEST
# MANIFEST is the journey-format manifest build.sh writes (see INTERFACES.md):
# absolute "host" "mini" "store" "verifier" "candidate" paths and a "sha256"
# map. Sets CANDIDATE_MANIFEST, CANDIDATE_DIR, CANDIDATE_PROVENANCE, HOST, MINI,
# STORE, VERIFIER, CONSENT after validating their manifest output entries.
# Call candidate_verify_outputs before launching any resolved binary.
candidate_resolve() {
  manifest=$(candidate_abs "$1")
  [ -f "$manifest" ] || candidate_die "manifest not found: $manifest"
  CANDIDATE_MANIFEST=$manifest
  CANDIDATE_DIR=$(CDPATH='' cd -- "$(dirname -- "$manifest")" && pwd -P)
  jq -e '.type == "minidregg-candidate-manifest-v2" and
    (.outputs | type == "object" and length > 0)' "$manifest" >/dev/null \
    || candidate_die "manifest must be minidregg-candidate-manifest-v2; repackage the candidate"
  CANDIDATE_PROVENANCE=$(jq -er '.candidate | select(type == "string" and startswith("/"))' "$manifest") \
    || candidate_die "manifest .candidate must be an absolute path"
  expected=$(jq -er '.sha256.candidate | select(test("^[0-9a-f]{64}$"))' "$manifest") \
    || candidate_die "manifest .sha256.candidate must be a SHA-256"
  [ -f "$CANDIDATE_PROVENANCE" ] || candidate_die "missing candidate provenance"
  [ "$(candidate_sha256 "$CANDIDATE_PROVENANCE")" = "$expected" ] \
    || candidate_die "candidate provenance sha256 mismatch"
  jq -e --slurpfile p "$CANDIDATE_PROVENANCE" '
    . as $m | $p[0] as $p |
    $p.type == "minidregg-candidate-provenance-v1" and
    .outputs == $p.outputs and
    (.outputs | to_entries | all(
      (.key | test("^bin/([A-Za-z0-9_-]+/)*[A-Za-z0-9_-]+$")) and
      (.value.sha256 | type == "string" and test("^[0-9a-f]{64}$")) and
      (.value.build.sourceTree == $p.source.tree) and
      (.value.build.sourceTree | type == "string" and test("^[0-9a-f]{40}$")) and
      (.value.build.rustcVerbose | type == "string" and contains("commit-hash:")) and
      (.value.build.leanToolchain | type == "string" and length > 0) and
      (.value.build.cargoLockSha256 | type == "object" and length > 0) and
      (.value.build.flags.rust | type == "object" and length > 0) and
      (.value.build.flags.native | type == "object" and length > 0))) and
    ($p.binaries | to_entries | all(
      . as $r | ($m.outputs | has($r.value.path)) and
      $m.outputs[$r.value.path].sha256 == $r.value.sha256 and
      $m.sha256[$r.key] == $r.value.sha256)) and
    (["host", "consent", "mini", "store", "verifier", "grainRuntime",
      "grainProviderBridge", "inferenceScheduler", "spkHost", "spkBrowserProxy",
      "spkBroker", "spkHostd", "discord", "payWatcher", "keys"] |
      all(. as $r | $p.binaries[$r].path | type == "string"))
    ' "$manifest" >/dev/null || candidate_die "manifest output identity is incomplete or differs from provenance"
  for role in host mini store verifier consent; do
    rel=$(jq -er --arg role "$role" '.binaries[$role].path' "$CANDIDATE_PROVENANCE")
    path=$CANDIDATE_DIR/$rel
    [ "$(jq -r --arg role "$role" '.[$role]' "$manifest")" = "$path" ] \
      || candidate_die "manifest .$role does not name its candidate output"
    case "$role" in
      host) HOST=$path ;;
      mini) MINI=$path ;;
      store) STORE=$path ;;
      verifier) VERIFIER=$path ;;
      consent) CONSENT=$path ;;
    esac
  done
}

# Each read happens in this shell (no pipeline that could hide a refusal).
candidate_verify_outputs() {
  jq -e '.outputs | type == "object" and length > 0' "$1" >/dev/null \
    || candidate_die "manifest .outputs must be a nonempty object"
  rows=$(jq -r '.outputs | to_entries[] | [.key, .value.sha256] | @tsv' "$1") \
    || candidate_die "cannot read manifest outputs"
  while read -r rel expected; do
    binary=$CANDIDATE_DIR/$rel
    [ -f "$binary" ] && [ -x "$binary" ] || candidate_die "binary $rel missing or not executable"
    actual=$(candidate_sha256 "$binary")
    [ "$actual" = "$expected" ] \
      || candidate_die "binary ${rel##*/} sha256 mismatch: manifest $expected, file $actual"
  done <<EOF_OUTPUTS
$rows
EOF_OUTPUTS
}

# candidate_state STATE_DIR
# Loads an initialized state directory written by `run.sh init`.
candidate_state() {
  STATE=$(CDPATH='' cd -- "$1" 2>/dev/null && pwd -P) || candidate_die "state directory not found: $1"
  [ -f "$STATE/state.json" ] || candidate_die "not an initialized state directory (no state.json): $STATE"
  jq -e '.type == "minidregg-candidate-state-v1"' "$STATE/state.json" >/dev/null \
    || candidate_die "state.json is not minidregg-candidate-state-v1"
  candidate_resolve "$(jq -er '.manifest' "$STATE/state.json")"
}

# Check state bindings only after run.sh has verified every candidate output.
candidate_state_bindings() {
  CONFIG=$STATE/deployment/pinned-config.json
  SOCKET=$STATE/public/mini.sock
  [ -s "$CONFIG" ] || candidate_die "missing pinned config: $CONFIG"
  pinned_host=$(jq -er '.hostSha256' "$STATE/state.json")
  [ "$pinned_host" = "$(candidate_sha256 "$HOST")" ] \
    || candidate_die "Host image differs from the one this state was bootstrapped with"
  [ "$(jq -r '.storageBinary' "$CONFIG")" = "$STORE" ] \
    || candidate_die "pinned config names a different Store helper than the manifest"
  [ "$(jq -r '.signatureBinary' "$CONFIG")" = "$VERIFIER" ] \
    || candidate_die "pinned config names a different signature verifier than the manifest"
}

# A foreground serve need not have server.pid. Check every process naming this
# configuration or socket, including a Host left alive by a departed supervisor.
# Operators must serialize start/stop/upgrade; this check is not a process lock.
candidate_require_stopped() {
  for candidate_proc in /proc/[0-9]*/cmdline; do
    [ -r "$candidate_proc" ] || continue
    candidate_cmdline=$(tr '\0' '\n' <"$candidate_proc" 2>/dev/null) || continue
    case "$candidate_cmdline" in
      *"$CONFIG"*|*"$SOCKET"*)
        candidate_die "upgrade requires a stopped Host (process ${candidate_proc#/proc/} names its config or socket)" ;;
    esac
  done
}

# candidate_build_root SRC
# Cargo hashes the absolute path of every path dependency that lies outside the building package's
# own directory (native/grain-runtime builds ../signed-api-path, ...; resource-client's `mini` has
# the same shape) into `-C metadata`, hence into every symbol hash and the binary's layout, and
# --remap-path-prefix does not reach it: one source built in two directories gives two binaries
# (cv 01a0f830-42e7: grain-runtime 7b8f929c vs e75bccf1 on 7961b345). So every cargo command of a
# candidate build runs through ONE fixed path: a symlink to SRC, which cargo follows lexically,
# in a 0700 directory owned by this account (MINI_CANDIDATE_BUILD_ROOT, default
# /tmp/minidregg-candidate-build), held under flock on fd 9 so two builds on one host take turns.
# Builds compared for reproducibility must share the build root; it is recorded in provenance.
# Sets CANDIDATE_BUILD_ROOT and CANDIDATE_BUILD_SRC (the path to hand cargo, and to remap).
# The same fixed path is what lets a shared sccache (scripts/pipeline/install-sccache) hit across
# lanes and tips. Release with candidate_build_root_release.
candidate_build_root() {
  CANDIDATE_BUILD_ROOT=${MINI_CANDIDATE_BUILD_ROOT:-/tmp/minidregg-candidate-build}
  mkdir -p -m 0700 "$CANDIDATE_BUILD_ROOT"
  [ -d "$CANDIDATE_BUILD_ROOT" ] && [ ! -L "$CANDIDATE_BUILD_ROOT" ] && [ -O "$CANDIDATE_BUILD_ROOT" ] \
    || candidate_die "build root $CANDIDATE_BUILD_ROOT is not a directory owned by this account (set MINI_CANDIDATE_BUILD_ROOT)"
  exec 9>"$CANDIDATE_BUILD_ROOT/lock"
  flock 9
  CANDIDATE_BUILD_SRC=$CANDIDATE_BUILD_ROOT/src
  rm -f "$CANDIDATE_BUILD_SRC"
  ln -s "$1" "$CANDIDATE_BUILD_SRC"
}

candidate_build_root_release() {
  [ -z "${CANDIDATE_BUILD_SRC:-}" ] || rm -f "$CANDIDATE_BUILD_SRC"
  exec 9>&-
}
