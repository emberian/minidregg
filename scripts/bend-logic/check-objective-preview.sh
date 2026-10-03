#!/usr/bin/env bash
set -euo pipefail
# Exact warm-only qualification; source/tooling/capture configuration is caller-owned.
# Run under the assigned guardian resource envelope. No lake/dependency builds.
task_source_root=${1:?source root}
task_config=${2:?pinned tooling JSON}
task_request=${3:?preview request}
task_output=${4:?empty owned output directory}
export LEAN_NUM_THREADS=2
eval "$(python3 - "$task_config" <<'CONFIG'
import json,shlex,sys
c=json.load(open(sys.argv[1]))
for key,var in [('leanPath','task_lean'),('oleanRoot','LEAN_PATH'),('previewHostPath','task_host'),('bunPath','task_bun')]:
 print('export '+var+'='+shlex.quote(c[key]))
CONFIG
)"
"$task_lean" -j 2 "$task_host" -o "$LEAN_PATH/Host/ObjectiveBendPreview.olean"
"$task_bun" "$task_source_root/native/bend-source/objective-preview.ts" "$task_request" "$task_output" "$task_config"
