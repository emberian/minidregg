#!/bin/bash
# usage: ticker.sh MINI RUNROOT STOPFILE COUNTS -- the deployment timers against a journey world:
# the clock subject ticks every TICK_S seconds (default 60; 0 = no tick) from W/clock, and the
# operator certifies every CERTIFY_S seconds (default 15) with --min-tail 64 (control = the
# genesis factory controller). Each confirmed installed acceptedCount is appended to COUNTS.
MINI=$1; R=$2; STOP=$3; C=$4; W=$R/world; L=$R/ticker.log
TICK_S=${TICK_S:-60}; CERTIFY_S=${CERTIFY_S:-15}
done_() { grep -q "^EXIT=" "$STOP" 2>/dev/null; }
count() { jq -r 'select(.confirmation == "installed") | .acceptedCount // empty' "$1" 2>/dev/null | head -1; }
while [ ! -f "$W/clock/workspace.json" ] || [ ! -S "$W/public/mini.sock" ] || [ ! -f "$W/genesis.json" ]; do
  done_ && exit 0; sleep 2; done
CONTROL=$(jq -r .factoryControllerCapability "$W/genesis.json")
next_tick=0; next_cert=0
while ! done_; do
  now=$(date +%s)
  if [ "$TICK_S" != 0 ] && [ "$now" -ge "$next_tick" ] && [ -S "$W/public/mini.sock" ]; then
    next_tick=$((now + TICK_S))
    "$MINI" clock --action tick --workspace "$W/clock" >"$R/ticker.last" 2>"$R/ticker.err"; rc=$?
    k=$(count "$R/ticker.last"); [ -n "$k" ] && echo "$k" >>"$C"
    echo "$(date +%s) tick rc=$rc count=$k" >>"$L"
  fi
  if [ "$now" -ge "$next_cert" ] && [ -S "$W/public/mini.sock" ]; then
    next_cert=$((now + CERTIFY_S))
    "$MINI" checkpoint --action certify --workspace "$W/sponsor" --control "$CONTROL" --min-tail 64 >"$R/certify.last" 2>"$R/certify.err"; rc=$?
    k=$(count "$R/certify.last"); [ -n "$k" ] && echo "$k" >>"$C"
    echo "$(date +%s) certify rc=$rc count=$k" >>"$L"
  fi
  sleep 0.5
done
