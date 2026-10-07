#!/bin/bash
# KN2-NEUTRAL-BIRTHS cluster (2), executed through the real native Host: the grain-backed
# birth journey (scripts/grain-birth/native-acceptance.sh: a worker's composite birth under
# a reserved tool grain, an owner bare birth, a worker bare birth refused by the factory
# law) runs against this tree's `minidregg-host`.  Control: the journey passes.  Plant: the
# grain factory projection drops the newborn slots, so its step names no newborn; the
# composite birth must be refused `neutralBirthUnjudged` (the Host's operator log names it).
# Usage (tree root): scripts/kn2/plant-grain-neutral-birth.sh ARTIFACT-BIN-DIR LOGDIR
set -u
A=$1; LOGS=$2
HOST=$PWD/.lake/build/bin/minidregg-host
# JOURNEY: the journey script (default the tree's; a reviewed local copy when its source guard lags)
JOURNEY=${JOURNEY:-scripts/grain-birth/native-acceptance.sh}
run() {
  name=$1; out=$LOGS/grain-$name
  rm -rf "$out"
  MINI=$A/mini STORE_BINARY=$A/minidregg-link-sqlite-store \
    SIGNATURE_BINARY=$A/minidregg-credential-signature-verifier \
    sh "$JOURNEY" "$HOST" "$out" > "$LOGS/grain-$name.log" 2>&1
  echo "$name journey rc=$?"
}
/srv/pipeline/scripts/lake-slot minidregg-host > "$LOGS/grain-host-control.build.log" 2>&1 || { echo "control host build failed"; exit 1; }
run control
f=Kernel/GrainResourceBirthAdmission.lean; cp $f "$LOGS/plant.orig"
python3 - $f <<'PLANT'
import sys
p=sys.argv[1]; s=open(p).read()
o=""" ++
        ResourceBirthController.Concrete.newbornSlots source.birth⟩"""
assert s.count(o)==1, s.count(o); open(p,'w').write(s.replace(o,"⟩"))
PLANT
git diff -- $f > "$LOGS/grain-plant.diff"
/srv/pipeline/scripts/lake-slot minidregg-host > "$LOGS/grain-host-plant.build.log" 2>&1; echo "plant host build rc=$?"
run plant
cp "$LOGS/plant.orig" $f
grep -h "operator log" "$LOGS"/grain-plant/composite-session/stderr 2>/dev/null | head -3
if grep -q "neutralBirthUnjudged" "$LOGS"/grain-plant/composite-session/stderr 2>/dev/null; then echo "RED as intended: grain newborn slots dropped"; else echo "NOT RED: grain plant"; fi
/srv/pipeline/scripts/lake-slot minidregg-host > "$LOGS/grain-host-restore.build.log" 2>&1; echo "restore host build rc=$?"
