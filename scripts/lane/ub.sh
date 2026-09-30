#!/usr/bin/env bash
# usage: scripts/lane/ub.sh <log>
# The umbrella for THIS checkout: Minidregg + the minidregg-host exe + every
# Host.* module (Host.lean does not root them all).
set -u
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root" || exit 2
mods=$(ls Host/*.lean | sed "s|/|.|; s|\.lean$||")
exec "$root/scripts/lane/lb.sh" "$1" Minidregg minidregg-host $mods
