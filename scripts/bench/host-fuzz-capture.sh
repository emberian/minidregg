#!/bin/bash
cd /srv/lanes/bench-store; ulimit -s unlimited; umask 077
export TEE_REAL_HOST=/srv/lanes/bench-store/set/bin/minidregg-host
B=/srv/lanes/bench-store; T=$B/teebin; R=src/native/resource-client
cap() { n=$1; shift
  rm -rf tee2/$n run2/$n; mkdir -p tee2/$n
  TEE_DIR=$B/tee2/$n timeout 3400 "$@" > logs/capture2-$n.out 2> logs/capture2-$n.err
  echo "$n EXIT $?" >> logs/capture2-status.txt; }
: > logs/capture2-status.txt
for d in act:objective-activity-native-acceptance.py seat:objective-seat-native-acceptance.py call:objective-call-native-journey.py send:objective-send-native-journey.py domain:objective-domain-native-journey.py upgrade:objective-upgrade-native-journey.py bounty:objective-bounty-native-acceptance.py objrec:objectrecord-native-journey.py work:objective-work-account-journey.py; do
  n=${d%%:*}; f=${d#*:}; ( cap $n python3 $R/$f --bin teebin --root $B/run2/$n ) &
done
( cap quote python3 $R/objective-activity-quote-submit-journey.py --bin teebin --root $B/run2/quote --births 12 ) &
( cap charged python3 $R/objective-charged-failure-journey.py --bin teebin --root $B/run2/charged --repeat 2 ) &
( cap welcome bash $R/welcome-continuity-journey.sh $T/minidregg-host $T/mini $T/minidregg-link-sqlite-store $T/minidregg-credential-signature-verifier $B/run2/welcome ) &
( cap rooms env MINI_HOST_BIN=$T/minidregg-host MINI_BIN=$T/mini MINI_STORE_BIN=$T/minidregg-link-sqlite-store MINI_VERIFIER_BIN=$T/minidregg-credential-signature-verifier bash $R/rooms-e2e.sh $B/run2/rooms ) &
( cap journey env JOURNEY_STEPS="J0 J1 J2 J3 J4 J5 J6 J7 J8 JROT JPAY2 JRLANE" bash $R/journey.sh $T/manifest.json $B/run2/journey ) &
wait
echo ALLDONE >> logs/capture2-status.txt
