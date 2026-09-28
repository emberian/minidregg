#!/bin/sh
set -eu
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
scratch=$(mktemp -d)
git -C "$scratch" init -q
git -C "$scratch" config user.name Test
git -C "$scratch" config user.email test@example.invalid
git -C "$scratch" config commit.gpgsign false
mkdir "$scratch/public"
printf 'A selected public demo file.\n' >"$scratch/public/demo.txt"
git -C "$scratch" add public/demo.txt
git -C "$scratch" commit -qm demo
commit=$(git -C "$scratch" rev-parse HEAD)
"$here/prepare.sh" "$scratch" "$commit" public/demo.txt public-demo-file "$scratch/export"
jq -e --arg commit "$commit" \
  '.commit == $commit and .path == "public/demo.txt" and .fileBytes == "29"' \
  "$scratch/export/selection.json" >/dev/null
if "$here/prepare.sh" "$scratch" "$commit" ../private.txt public-demo-file \
    "$scratch/reject-path" >/dev/null 2>&1; then
  echo "unsafe path was accepted" >&2; exit 1
fi
if "$here/prepare.sh" "$scratch" "$commit" public/demo.txt missing-approval \
    "$scratch/reject-approval" >/dev/null 2>&1; then
  echo "missing public approval was accepted" >&2; exit 1
fi
ln -s demo.txt "$scratch/public/link.txt"
git -C "$scratch" add public/link.txt
git -C "$scratch" commit -qm link
link_commit=$(git -C "$scratch" rev-parse HEAD)
if "$here/prepare.sh" "$scratch" "$link_commit" public/link.txt public-demo-file \
    "$scratch/reject-link" >/dev/null 2>&1; then
  echo "symlink was accepted" >&2; exit 1
fi
printf 'bad\000file\n' >"$scratch/public/nul.txt"
git -C "$scratch" add public/nul.txt
git -C "$scratch" commit -qm nul
nul_commit=$(git -C "$scratch" rev-parse HEAD)
if "$here/prepare.sh" "$scratch" "$nul_commit" public/nul.txt public-demo-file \
    "$scratch/reject-nul" >/dev/null 2>&1; then
  echo "NUL text was accepted" >&2; exit 1
fi
printf 'PASS: exact Git file selection, explicit approval and path refusals\n'
