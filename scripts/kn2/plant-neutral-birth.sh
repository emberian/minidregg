#!/bin/bash
# KN2-NEUTRAL-BIRTHS source plants, executed: each plants one fault, rebuilds the probe's
# imports, runs scripts/kn2/neutral-birth.lean in control mode (the real receiver path on a
# booted Store), and requires the control to go RED with the named refusal. Then restores.
# Usage (from the tree root): scripts/kn2/plant-neutral-birth.sh VERIFIER SIGN-PROBE STORE LOGDIR
set -u
VERIFIER=$1; SIGN=$2; STORE=$3; LOGS=$4
TARGETS="Kernel.NativeHost Kernel.NativeHostGenesis Kernel.ResourceBirthReceiver Verify.ResourceReserveBirthFixture"
build() { /srv/pipeline/scripts/lake-slot $TARGETS; }
probe() { lake env lean --run scripts/kn2/neutral-birth.lean "$VERIFIER" "$SIGN" "$STORE" control; }
plant() {
  name=$1; file=$2; old=$3; new=$4; expect=$5; log=$LOGS/plant-nb-$name.log
  cp "$file" "$LOGS/plant.orig"
  python3 - "$file" "$old" "$new" <<'PY'
import sys
p,o,n=sys.argv[1:4]; s=open(p).read()
assert s.count(o)==1, ('PLANT DID NOT APPLY', s.count(o)); open(p,'w').write(s.replace(o,n))
PY
  { echo "== PLANT $name in $file"; git diff -- "$file"; build > "$LOGS/plant-nb-$name.build.log" 2>&1; echo "build rc=$?";
    probe; echo "probe rc=$?"; } > "$log" 2>&1
  cp "$LOGS/plant.orig" "$file"
  if tr -d '\n ' < "$log" | grep -q "$(echo "$expect" | tr -d ' ')" && grep -q "probe rc=1" "$log"; then echo "RED as intended: $name"; else echo "NOT RED: $name (see $log)"; fi
}
plant aux-unnamed Kernel/ResourceBirthController.lean \
'  (allocationWrites descriptor).map fun write =>
    (ReceivingLaw.birthSlot write.cellId.value, Int.ofNat write.exactPost.value)' \
'  (descriptor.births.map fun item => birthWrite item.create).map fun write =>
    (ReceivingLaw.birthSlot write.cellId.value, Int.ofNat write.exactPost.value)' \
'neutralBirthUnjudged 3305979916'
# Static plant: an extra birth write appended to the receiver's committed intent cannot
# elaborate: intent_births_named (the committed writes are the named ones) goes red.
f=Kernel/ResourceBirthReceiver.lean; cp $f "$LOGS/plant.orig"
python3 - $f <<'PLANT'
import sys
p=sys.argv[1]; s=open(p).read()
o="""  transactionId := accepted.descriptor.transactionId
  writes := accepted.prepared.writes
  readGuards := readGuards accepted"""
n=o.replace("writes := accepted.prepared.writes", "writes := accepted.prepared.writes ++ ((accepted.descriptor.createRequests.take 1).map fun request => ResourceBirthController.birthWrite { request with cellId := request.cellId + 500 })")
assert s.count(o)==2, s.count(o); open(p,'w').write(s.replace(o,n))
PLANT
{ git diff -- $f; /srv/pipeline/scripts/lean-ask check $f --reload --timeout 5000; } > "$LOGS/plant-nb-static-intent.log" 2>&1
cp "$LOGS/plant.orig" $f
if grep -q "intent_births_named" "$LOGS/plant-nb-static-intent.log" && grep -q "error" "$LOGS/plant-nb-static-intent.log"; then echo "RED as intended: static-intent"; else echo "NOT RED: static-intent"; fi
build > "$LOGS/plant-nb-restore.build.log" 2>&1; echo "restore build rc=$?"
probe > "$LOGS/plant-nb-control-after.log" 2>&1; echo "control after restore rc=$?"; tail -2 "$LOGS/plant-nb-control-after.log"
