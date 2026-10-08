#!/bin/sh
# Signed sntfy v2.28.0-sandstorm-18, measured in the 2026-09-27 app-selection
# and 2026-09-28 qualification records. SPK install still verifies its signature.
set -eu
umask 077
[ "$#" -le 1 ] || { echo "usage: $0 [CACHE_DIR_OUTSIDE_SRC]" >&2; exit 2; }
cache=${1:-/srv/lanes/prod-spk/cache}
package=bc424d5fd3cf60977cacdac328adfbee
sha=bc424d5fd3cf60977cacdac328adfbee4de94f88d57383ad38b3d472c0c24f2d
here=$(CDPATH='' cd -- "$(dirname "$0")" && pwd)
repo=$(CDPATH='' cd -- "$here/../.." && pwd)
case "$cache" in /*) ;; *) echo 'absolute cache directory required' >&2; exit 2;; esac
case "$cache/" in "$repo/"*) echo 'SPK cache must be outside src' >&2; exit 2;; esac
mkdir -p -m 700 "$cache"
[ ! -L "$cache" ] && [ "$(realpath "$cache")" = "$cache" ] || { echo 'SPK cache custody refused' >&2; exit 1; }
path=$cache/sntfy-$sha.spk
check() {
  [ -f "$1" ] && [ ! -L "$1" ] && [ "$(stat -c '%s' "$1")" = 17379772 ] &&
    [ "$(sha256sum "$1" | cut -d ' ' -f1)" = "$sha" ]
}
if [ -e "$path" ] || [ -L "$path" ]; then
  check "$path" || { echo 'test SPK pinned sha256 mismatch' >&2; exit 1; }
else
  temp=$(mktemp "$cache/.sntfy.XXXXXXXX")
  trap 'rm -f "$temp"' EXIT HUP INT TERM
  curl --fail --location --proto '=https' --tlsv1.2 --connect-timeout 20 --max-time 180 \
    "https://app-index.sandstorm.io/packages/$package" -o "$temp"
  check "$temp" || { echo 'test SPK pinned sha256 mismatch' >&2; exit 1; }
  chmod 400 "$temp"
  ln "$temp" "$path"
  rm "$temp"
  trap - EXIT HUP INT TERM
fi
printf '%s\n' "$path"
