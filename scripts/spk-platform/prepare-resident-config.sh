#!/bin/sh
# The native grain author is the sole emitter; it validates with the resident's
# own decoder before returning the path. This performs no START or CLAIM.
set -eu
[ "$#" -eq 3 ] || { echo "usage: $0 SPK_HOST PROFILE APP" >&2; exit 2; }
exec "$1" grain prepare-resident "$2" "$3"
