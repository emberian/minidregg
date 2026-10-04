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
# STORE, VERIFIER after checking every file against its pinned SHA-256.
candidate_resolve() {
  manifest=$(candidate_abs "$1")
  [ -f "$manifest" ] || candidate_die "manifest not found: $manifest"
  CANDIDATE_MANIFEST=$manifest
  CANDIDATE_DIR=$(CDPATH='' cd -- "$(dirname -- "$manifest")" && pwd -P)
  for role in host mini store verifier candidate; do
    path=$(jq -er --arg role "$role" '.[$role] | select(type == "string" and startswith("/"))' "$manifest") \
      || candidate_die "manifest .$role must be an absolute path"
    expected=$(jq -er --arg role "$role" '.sha256[$role] | select(type == "string" and test("^[0-9a-f]{64}$"))' "$manifest") \
      || candidate_die "manifest .sha256.$role must be a SHA-256"
    [ -f "$path" ] || candidate_die "not a file: $path"
    actual=$(candidate_sha256 "$path")
    [ "$actual" = "$expected" ] || candidate_die "SHA-256 mismatch for $role: $path is $actual, manifest pins $expected"
    case "$role" in
      host) HOST=$path ;;
      mini) MINI=$path ;;
      store) STORE=$path ;;
      verifier) VERIFIER=$path ;;
      candidate) CANDIDATE_PROVENANCE=$path ;;
    esac
  done
  for binary in "$HOST" "$MINI" "$STORE" "$VERIFIER"; do
    [ -x "$binary" ] || candidate_die "not executable: $binary"
  done
  jq -e '.type == "minidregg-candidate-provenance-v1"' "$CANDIDATE_PROVENANCE" >/dev/null \
    || candidate_die "manifest .candidate is not a minidregg-candidate-provenance-v1"
}

# candidate_state STATE_DIR
# Loads an initialized state directory written by `run.sh init`.
candidate_state() {
  STATE=$(CDPATH='' cd -- "$1" 2>/dev/null && pwd -P) || candidate_die "state directory not found: $1"
  [ -f "$STATE/state.json" ] || candidate_die "not an initialized state directory (no state.json): $STATE"
  jq -e '.type == "minidregg-candidate-state-v1"' "$STATE/state.json" >/dev/null \
    || candidate_die "state.json is not minidregg-candidate-state-v1"
  candidate_resolve "$(jq -er '.manifest' "$STATE/state.json")"
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
  mkdir -p -m 0700 "$CANDIDATE_BUILD_ROOT" 2>/dev/null || true
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
