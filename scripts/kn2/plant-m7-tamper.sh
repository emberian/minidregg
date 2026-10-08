#!/usr/bin/env bash
# Re-runnable binary fault: mutation and exact named red line are asserted by M7's check.
set -euo pipefail
here=$(cd "$(dirname "$0")/../.." && pwd)
exec "$here/deploy/candidate/check-tamper.sh" "${1:?built candidate}" "${2:?new evidence directory}"
