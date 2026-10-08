#!/usr/bin/env bash
# Reintroduce the lost hostile Host load in check long in a temporary copy.
set -euo pipefail
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
exec bash "$here/plant-jserve-runner.sh" --plant long "$@"
