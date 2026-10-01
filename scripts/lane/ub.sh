#!/usr/bin/env bash
# usage: scripts/lane/ub.sh <log>
# The DEPLOYED umbrella for THIS checkout: `Deployed` (core, kernel, predicates,
# effects, every Host.* module) + the minidregg-host exe + AxiomCensus over it.
# The proof-system research (Selvage, proof-system Assurance) is
# scripts/lane/rb.sh.
set -u
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root" || exit 2
mods=$(ls Host/*.lean | sed "s|/|.|; s|\.lean$||")
exec "$root/scripts/lane/lb.sh" "$1" Deployed minidregg-host $mods AxiomCensus
