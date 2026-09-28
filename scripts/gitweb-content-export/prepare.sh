#!/bin/sh
# Select one explicitly approved public GitWeb file from an immutable commit.
# This only prepares bytes; it does not contact Mini or publish anything.
set -eu
umask 077

die() { echo "gitweb content export: $*" >&2; exit 2; }
if [ "$#" -ne 5 ]; then
  die "usage: prepare.sh GIT-REPOSITORY COMMIT-OID FILE-PATH public-demo-file NEW-DIRECTORY"
fi
repo=$1 commit=$2 path=$3 approval=$4 output=$5
[ "$approval" = public-demo-file ] || die "explicit public-demo-file approval required"
case "$commit" in *[!0-9a-f]*|'') die "commit must be a lowercase object ID" ;; esac
case ${#commit} in 40|64) ;; *) die "commit must be a full object ID" ;; esac
case "$path" in
  ''|/*|../*|*/../*|*/..|./*|*/./*|*/.|*'//'*) die "unsafe file path" ;;
  *[!A-Za-z0-9._/-]*) die "file path must be simple printable ASCII" ;;
esac
[ ! -e "$output" ] || die "output directory already exists"
command -v git >/dev/null 2>&1 || die "git is required"
command -v jq >/dev/null 2>&1 || die "jq is required"
command -v iconv >/dev/null 2>&1 || die "iconv is required"
repo=$(CDPATH='' cd -- "$repo" && pwd -P) || die "repository is unavailable"
actual=$(git -C "$repo" rev-parse --verify "$commit^{commit}") || die "commit is absent"
[ "$actual" = "$commit" ] || die "commit abbreviation or mismatch"
selection=$(git -C "$repo" ls-tree -r --full-tree "$commit" -- "$path") || die "tree lookup failed"
[ "$(printf '%s\n' "$selection" | wc -l | tr -d ' ')" = 1 ] || die "file path is absent or ambiguous"
tab=$(printf '\t')
case "$selection" in
  "100644 blob "*"$tab$path"|"100755 blob "*"$tab$path") ;;
  *) die "selected object is not an exact regular file" ;;
esac
blob=${selection#* blob }
blob=${blob%%"$tab"*}
case "$blob" in *[!0-9a-f]*|'') die "invalid Git blob ID" ;; esac
case ${#blob} in 40|64) ;; *) die "invalid Git blob ID length" ;; esac
mkdir -m 700 "$output"
output=$(CDPATH='' cd -- "$output" && pwd -P)
git -C "$repo" cat-file blob "$blob" >"$output/file.bin" || die "blob extraction failed"
[ "$(git -C "$repo" hash-object --no-filters "$output/file.bin")" = "$blob" ] ||
  die "extracted bytes differ from selected Git blob"
length=$(wc -c <"$output/file.bin" | tr -d ' ')
[ "$length" -gt 0 ] && [ "$length" -le 65536 ] || die "public demo file must contain 1..65536 bytes"
iconv -f UTF-8 -t UTF-8 <"$output/file.bin" >"$output/utf8-check.bin" || die "file is not UTF-8"
cmp -s "$output/file.bin" "$output/utf8-check.bin" || die "file is not exact UTF-8"
LC_ALL=C tr -d '\000' <"$output/file.bin" >"$output/utf8-check.bin"
cmp -s "$output/file.bin" "$output/utf8-check.bin" || die "file contains NUL"
rm "$output/utf8-check.bin"
sha=$(shasum -a 256 "$output/file.bin" | awk '{print $1}')
{
  printf 'DREGG/GITWEB-CONTENT-EXPORT/v1\n'
  printf 'commit %s\npath %s\nblob %s\nsha256 %s\nlength %s\n\n' \
    "$commit" "$path" "$blob" "$sha" "$length"
  cat "$output/file.bin"
} >"$output/atom-payload.bin"
jq -n --arg commit "$commit" --arg path "$path" --arg blob "$blob" \
  --arg fileSha256 "$sha" --arg fileBytes "$length" \
  --arg payloadSha256 "$(shasum -a 256 "$output/atom-payload.bin" | awk '{print $1}')" \
  '{type:"gitweb-public-file-export-v1",commit:$commit,path:$path,blob:$blob,
    fileSha256:$fileSha256,fileBytes:$fileBytes,payloadSha256:$payloadSha256}' \
  >"$output/selection.json"
(cd "$output" && shasum -a 256 file.bin atom-payload.bin selection.json >SHA256SUMS)
