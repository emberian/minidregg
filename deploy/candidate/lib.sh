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
# Sets CANDIDATE_DIR, HOST, MINI, STORE, VERIFIER to absolute paths after
# checking every binary against the SHA-256 recorded in the manifest.
candidate_resolve() {
  manifest=$(candidate_abs "$1")
  [ -f "$manifest" ] || candidate_die "manifest not found: $manifest"
  jq -e '.type == "minidregg-candidate-manifest-v1"' "$manifest" >/dev/null \
    || candidate_die "not a minidregg-candidate-manifest-v1: $manifest"
  CANDIDATE_MANIFEST=$manifest
  CANDIDATE_DIR=$(CDPATH='' cd -- "$(dirname -- "$manifest")" && pwd -P)
  for role in host mini store verifier; do
    relative=$(jq -er --arg role "$role" '.binaries[$role].path' "$manifest") \
      || candidate_die "manifest lacks binaries.$role.path"
    expected=$(jq -er --arg role "$role" '.binaries[$role].sha256' "$manifest") \
      || candidate_die "manifest lacks binaries.$role.sha256"
    case "$relative" in /*|*..*) candidate_die "binary path must be relative and inside the candidate: $relative" ;; esac
    binary="$CANDIDATE_DIR/$relative"
    [ -f "$binary" ] && [ -x "$binary" ] || candidate_die "not an executable file: $binary"
    actual=$(candidate_sha256 "$binary")
    [ "$actual" = "$expected" ] || candidate_die "SHA-256 mismatch for $role: $binary is $actual, manifest says $expected"
    case "$role" in
      host) HOST=$binary ;;
      mini) MINI=$binary ;;
      store) STORE=$binary ;;
      verifier) VERIFIER=$binary ;;
    esac
  done
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
