#!/usr/bin/env bash
# scripts/census/run.sh WORLD [REPS] [OUT-DIR]: the member-command census, against the budget.
#
# WORLD is a scratch world (dregg-infra `jworld-scratch.sh up WORLD ... 7`: the sponsor and seven
# members), grown to demo scale by `grow.sh WORLD` (3,600 records, ~540 births). Every line below
# runs REPS times (default 8) as member-1, warm, through the ssh forced-command wrapper, with one
# fixed MINI_TRACE path per member (the member's line resident is keyed by its MINI_* variables, so
# a fresh path per run would measure a cold shell). Each run's wall time and every traced hop (Host
# op, codec frame, consent frame) is a row of OUT-DIR/census.jsonl; the summary prints every
# command and Host op against CENSUS_BUDGET_MS (default 10): over it is RED.
#
# Writes: three probe documents' pushes under member-1's requests/, and the census's own `say`,
# `react`, `topic`, `doc append`, `doc push` and `doc new` records in the world's Store.
set -euo pipefail
W=$1; N=${2:-8}; OUT=${3:-$W/census}; here=$(cd "$(dirname "$0")" && pwd)
M=$W/root/var/lib/mini/candidate/current/bin/mini; mkdir -p "$OUT"
mkdir -p $W/root/var/lib/mini/sessions/member-1/requests
for r in $(seq 0 $N); do printf 'census push %s\nsecond line %s\n' $r $RANDOM > $W/root/var/lib/mini/sessions/member-1/requests/push$r.txt; done
C="python3 $here/census.py $W $M"
export CENSUS_TRACE_DIR=$OUT
# warm both call slots and the consent resident first (not recorded)
$C 2 /dev/null "member-1|warm|credit" "member-1|warm|doc pull cdoc1" >/dev/null
J=$OUT/census-$(date +%Y%m%dT%H%M%S).jsonl
$C $N $J \
 "member-1|whoami|whoami" "member-1|home|home" "member-1|refs|refs" "member-1|history|history -n 20" \
 "member-1|inbox|inbox" "member-1|chat rooms|chat rooms" "member-1|room list|room list" \
 "member-1|credit|credit" "member-1|tariff|tariff feedback" "member-1|key-status|key-status" \
 "member-1|can|can feedback" "member-1|read|read feedback" "member-1|room members|room members feedback" \
 "member-1|room status|room status feedback" "member-1|tail|tail -n 20" \
 "member-1|doc show|doc show cdoc1" "member-1|doc outline|doc outline cdoc1" "member-1|doc pull|doc pull cdoc1" \
 "member-1|doc history|doc history cdoc1" "member-1|doc history (born ~1,500)|doc history g1512" \
 "member-1|doc show (born ~100)|doc show g63" \
 "member-1|story list|story list" "member-1|look|look" \
 "member-1|say|say census {n}" "member-1|react|react 1 +1" "member-1|topic|topic census {n}" \
 "member-1|doc append|doc append ap{n} cdoc1 appended-{n}" "member-1|doc push|doc push pu{n} cdoc1 @push{i}.txt" \
 "member-1|doc new|doc new cz{n}" >/dev/null
echo "load: $(cut -d' ' -f1-3 /proc/loadavg)   records: $(sqlite3 $W/root/var/lib/mini/store/node/store/forward-link.sqlite3 'select count(*) from durable_log' 2>/dev/null)   rows: $J"
python3 "$here/summ.py" "$J"
