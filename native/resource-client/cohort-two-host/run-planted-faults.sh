#!/usr/bin/env bash
# Planted faults: each run MUST end red (nonzero). A pass here is the failure.
set -uo pipefail
. "$(dirname "$0")/env.sh"
for plant in wrong-slot-key drop-cover; do
  rm -rf $L/evidence/planted-$plant
  python3 $RC/cohort-native-tcp.py --mini $MINI_NEW --fixture $LOOKUP --native-socket $SOCKET \
    --evidence $L/evidence/planted-$plant --epochs 16 --processing-slots 2 --native-workload single \
    --startup-s 40 --plant $plant > $L/logs/planted-$plant.log 2>&1
  rc=$?
  echo "plant $plant exit=$rc (0 would mean the plant was NOT detected)" | tee -a $L/logs/planted-faults.summary
done
