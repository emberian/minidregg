#!/usr/bin/env bash
# scripts/census/grow.sh WORLD [ROUNDS]: grow a seven-member scratch world to demo scale: ROUNDS
# (default 2,400) rounds over member-1..7, each a `say` in the shared room, and a `doc new` birth on
# 2 of every 9 rounds (~533 births at 2,400); a progress line per 100. Failures go to WORLD/grow.fail.
set -uo pipefail
W=$1; N=${2:-2400}; R=$W/root/var/lib/mini; M=$R/candidate/current/bin/mini
run() { local m=member-$1; HOME=$R/sessions/$m SSH_ORIGINAL_COMMAND="$2" $W/root/usr/local/lib/mini/mini-shell-ssh $M $R/candidate/current/bin/minidregg-host $R/store/node/deployment/pinned-config.json $R/store/node/public/mini.sock $R/sessions/$m/workspace $R/sessions/$m >/dev/null 2>>$W/grow.err || echo "rc=$? $m $2" >> $W/grow.fail; }
s=$(date +%s)
for i in $(seq 1 $N); do
  m=$(( 1 + i % 7 ))
  run $m "say census round $i from member-$m"
  case $(( i % 9 )) in 0|4) run $m "doc new g$i";; esac
  [ $(( i % 100 )) = 0 ] && echo "$i $(( $(date +%s)-s ))s $(sqlite3 $R/store/node/store/forward-link.sqlite3 'select count(*) from durable_log' 2>/dev/null)"
done
echo DONE
