#!/bin/sh
# Relocate only the two exact pinned Mini helper executables into protected
# root-owned custody. This is a pure JSON preparation, not a Store operation.
set -eu
umask 077
[ "$#" -eq 5 ] || {
  echo "usage: $0 BASE.json CANDIDATE.json BASE_SHA CANDIDATE_SHA NEW_PRIVATE_DIR" >&2
  exit 2
}
BASE=$1 CANDIDATE=$2 BASE_SHA=$3 CANDIDATE_SHA=$4 OUTPUT=$5
STORE=/opt/minidregg-gitweb-r3-20260927/bin/minidregg-link-sqlite-store-9746c47
SIGNATURE=/opt/minidregg-gitweb-r3-20260927/bin/minidregg-credential-signature-verifier-9746c47
STORE_SHA=9a5054813d9ad358ece337b99121cb37a36ba82b4b92ad0e287dcc7e529190e0
SIGNATURE_SHA=e80a0949d0ce16b24bcf24f2ac1306f4e194887ba11d328121b4c3345f8dfa1a
absolute() {
  case "$1" in /*) ;; *) echo "path must be absolute" >&2; exit 2 ;; esac
  case "$1" in *'/../'*|*'/./'*|*'//'*|*'/..'|*'/.'|*'/')
    echo "path is not canonical" >&2; exit 2 ;; esac
}
protected_leaf() {
  path=$1 expected=$2
  absolute "$path"
  [ -f "$path" ] && [ ! -L "$path" ] && [ -x "$path" ] &&
    [ "$(stat -c '%u:%h' "$path")" = '0:1' ] || {
    echo "protected helper leaf invalid" >&2; exit 2;
  }
  mode=$(stat -c '%a' "$path")
  case "$mode" in ''|*[!0-7]*) exit 2 ;; esac
  [ $((0$mode & 022)) -eq 0 ] || exit 2
  ancestor=${path%/*}
  while :; do
    [ -d "$ancestor" ] && [ ! -L "$ancestor" ] &&
      [ "$(stat -c '%u' "$ancestor")" = 0 ] || exit 2
    mode=$(stat -c '%a' "$ancestor")
    case "$mode" in ''|*[!0-7]*) exit 2 ;; esac
    [ $((0$mode & 022)) -eq 0 ] || exit 2
    [ "$ancestor" = / ] && break
    ancestor=${ancestor%/*}; [ -n "$ancestor" ] || ancestor=/
  done
  [ "$(sha256sum "$path" | cut -d ' ' -f 1)" = "$expected" ] || exit 2
}
for path in "$BASE" "$CANDIDATE" "$OUTPUT"; do absolute "$path"; done
for value in "$BASE_SHA" "$CANDIDATE_SHA"; do
  case "$value" in ''|*[!0-9a-f]*) exit 2 ;; esac
  [ "${#value}" -eq 64 ] || exit 2
done
[ -f "$BASE" ] && [ ! -L "$BASE" ] &&
  [ -f "$CANDIDATE" ] && [ ! -L "$CANDIDATE" ] &&
  [ "$(sha256sum "$BASE" | cut -d ' ' -f 1)" = "$BASE_SHA" ] &&
  [ "$(sha256sum "$CANDIDATE" | cut -d ' ' -f 1)" = "$CANDIDATE_SHA" ] || exit 2
protected_leaf "$STORE" "$STORE_SHA"
protected_leaf "$SIGNATURE" "$SIGNATURE_SHA"
ORIGINAL_STORE=$(jq -er '.storageBinary | select(type == "string")' "$BASE")
ORIGINAL_SIGNATURE=$(jq -er '.signatureBinary | select(type == "string")' "$BASE")
absolute "$ORIGINAL_STORE"; absolute "$ORIGINAL_SIGNATURE"
[ "$(sha256sum "$ORIGINAL_STORE" | cut -d ' ' -f 1)" = "$STORE_SHA" ] &&
  [ "$(sha256sum "$ORIGINAL_SIGNATURE" | cut -d ' ' -f 1)" = "$SIGNATURE_SHA" ] &&
  [ "$(jq -er '.storageBinary' "$CANDIDATE")" = "$ORIGINAL_STORE" ] &&
  [ "$(jq -er '.signatureBinary' "$CANDIDATE")" = "$ORIGINAL_SIGNATURE" ] || {
  echo "candidate helper differs from original pinned helper" >&2; exit 2;
}
PARENT=${OUTPUT%/*}
[ -n "$PARENT" ] && [ -d "$PARENT" ] && [ ! -L "$PARENT" ] &&
  [ "$(stat -c '%u:%a' "$PARENT")" = "$(id -u):700" ] || {
  echo "output parent is not private operator custody" >&2; exit 2;
}
[ ! -e "$OUTPUT" ] && [ ! -L "$OUTPUT" ] || exit 2
mkdir -m 700 "$OUTPUT"
jq -cS --arg store "$STORE" --arg signature "$SIGNATURE" \
  '.storageBinary=$store | .signatureBinary=$signature' "$BASE" >"$OUTPUT/base-rebound.json"
jq -cS --arg store "$STORE" --arg signature "$SIGNATURE" \
  '.storageBinary=$store | .signatureBinary=$signature' "$CANDIDATE" >"$OUTPUT/cb55-rebound.json"
chmod 600 "$OUTPUT/base-rebound.json" "$OUTPUT/cb55-rebound.json"
sync -f "$OUTPUT/base-rebound.json"
sync -f "$OUTPUT/cb55-rebound.json"
sync -f "$OUTPUT"
sync -f "$PARENT"
printf 'base_rebound_sha256=%s\n' "$(sha256sum "$OUTPUT/base-rebound.json" | cut -d ' ' -f 1)"
printf 'candidate_rebound_sha256=%s\n' "$(sha256sum "$OUTPUT/cb55-rebound.json" | cut -d ' ' -f 1)"
