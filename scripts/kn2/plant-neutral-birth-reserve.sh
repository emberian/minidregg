#!/bin/bash
# KN2-NEUTRAL-BIRTHS cluster (5) plant, executed through the reserve factory method: the factory
# step leaves the auxiliary policy-source creates out of its newborn slots (newbornSlots over
# the births only); the reserve probe's control birth (scripts/kn2/neutral-birth-reserve.lean,
# real receiver, booted Store, owner consent) must be refused `neutralBirthUnjudged <aux cell>`.
# Usage (tree root): scripts/kn2/plant-neutral-birth-reserve.sh VERIFIER SIGN-PROBE STORE LOGDIR
set -u
VERIFIER=$1; SIGN=$2; STORE=$3; LOGS=$4
TARGETS="Kernel.NativeHost Kernel.NativeHostGenesis Kernel.ResourceBirthReceiver Kernel.NativeHostReserveBirth Verify.ResourceReserveBirthFixture"
probe() { lake env lean --run scripts/kn2/neutral-birth-reserve.lean "$VERIFIER" "$SIGN" "$STORE" control; }
f=Kernel/ResourceBirthController.lean; cp $f "$LOGS/plant.orig"
python3 - $f <<'PLANT'
import sys
p=sys.argv[1]; s=open(p).read()
o="""  (allocationWrites descriptor).map fun write =>
    (ReceivingLaw.birthSlot write.cellId.value, Int.ofNat write.exactPost.value)"""
n="""  (descriptor.births.map fun item => birthWrite item.create).map fun write =>
    (ReceivingLaw.birthSlot write.cellId.value, Int.ofNat write.exactPost.value)"""
assert s.count(o)==1, s.count(o); open(p,'w').write(s.replace(o,n))
PLANT
{ git diff -- $f; /srv/pipeline/scripts/lake-slot $TARGETS > "$LOGS/plant-reserve.build.log" 2>&1; echo "build rc=$?"; probe; echo "probe rc=$?"; } > "$LOGS/plant-reserve.log" 2>&1
cp "$LOGS/plant.orig" $f
if tr -d '\n ' < "$LOGS/plant-reserve.log" | grep -q "neutralBirthUnjudged" && grep -q "probe rc=1" "$LOGS/plant-reserve.log"; then echo "RED as intended: reserve aux create unnamed"; else echo "NOT RED: reserve plant"; fi
/srv/pipeline/scripts/lake-slot $TARGETS > "$LOGS/plant-reserve-restore.build.log" 2>&1; echo "restore build rc=$?"
probe > "$LOGS/plant-reserve-control-after.log" 2>&1; echo "control after restore rc=$?"; tail -2 "$LOGS/plant-reserve-control-after.log"
