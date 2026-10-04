#!/bin/bash
# rooms-all.sh REPS: the room scenario REPS times, interleaved so each binary set sees the same
# box load: main binaries with the v1 room declaration; tip binaries with the v2 declaration
# (+ closure probes); tip binaries with the v1-shaped declaration (same code, old width: control).
set -uo pipefail
L=/home/ember/workbox/claude-lanes/schema-v2
V1="2-1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1011,1012,1010"
V2="1001,1002,1003,1004,1005,1006,1007,1008,1009,1011,1012,1010,2000-"
for r in $(seq 1 ${1:-3}); do
  uptime > $L/evidence/rooms-load-$r.txt
  $L/rooms-run.sh main-v1-$r $L/bin-main $L/mainwt "$V1" 2 0
  $L/rooms-run.sh tip-v2-$r $L/bin-tip $L/src "$V2" 2000 $([ $r = 1 ] && echo 1 || echo 0)
  $L/rooms-run.sh tip-v1shape-$r $L/bin-tip $L/src "$V1" 2 0
  uptime >> $L/evidence/rooms-load-$r.txt
done
echo done > $L/evidence/rooms-all.state
