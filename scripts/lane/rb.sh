#!/usr/bin/env bash
# usage: scripts/lane/rb.sh <log>
# The RESEARCH umbrella for THIS checkout: `Minidregg` (the whole tree, Selvage
# and the proof-system Assurance included) + AxiomCensusResearch over it.
set -u
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root" || exit 2
exec "$root/scripts/lane/lb.sh" "$1" Minidregg AxiomCensusResearch
