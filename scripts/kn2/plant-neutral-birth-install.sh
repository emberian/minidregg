#!/bin/bash
# KN2-NEUTRAL-BIRTHS cluster (4) plant, executed through the real Host install path: the
# install step drops its newborn slot (PolicyInstallController.project without
# newbornSlots), so the successor policy source is named by nothing; the probe's control
# installation must be refused `neutralBirthUnjudged <successor cell>`.  Then restores.
# Usage (tree root): scripts/kn2/plant-neutral-birth-install.sh VERIFIER SIGN-PROBE STORE LOGDIR
set -u
VERIFIER=$1; SIGN=$2; STORE=$3; LOGS=$4
TARGETS="Kernel.NativeHost Kernel.NativeHostGenesis Kernel.NativeHostLight"
probe() { lake env lean --run scripts/kn2/neutral-birth-install.lean "$VERIFIER" "$SIGN" "$STORE"; }
f=Kernel/PolicyInstallController.lean; cp $f "$LOGS/plant.orig"
python3 - $f <<'PLANT'
import sys
p=sys.argv[1]; s=open(p).read()
o=""") ++
      newbornSlots wanted.domain declaration }"""
assert s.count(o)==1, s.count(o); open(p,'w').write(s.replace(o,") }"))
PLANT
{ git diff -- $f; /srv/pipeline/scripts/lake-slot $TARGETS > "$LOGS/plant-install.build.log" 2>&1; echo "build rc=$?"; probe; echo "probe rc=$?"; } > "$LOGS/plant-install.log" 2>&1
cp "$LOGS/plant.orig" $f
if grep -q "neutralBirthUnjudged" "$LOGS/plant-install.log" && grep -q "probe rc=1" "$LOGS/plant-install.log"; then echo "RED as intended: install newborn slot dropped"; else echo "NOT RED: install plant"; fi
/srv/pipeline/scripts/lake-slot $TARGETS > "$LOGS/plant-install-restore.build.log" 2>&1; echo "restore build rc=$?"
probe > "$LOGS/plant-install-control-after.log" 2>&1; echo "control after restore rc=$?"; tail -2 "$LOGS/plant-install-control-after.log"
