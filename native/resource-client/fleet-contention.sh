#!/bin/sh
# Fleet contention on one Store: K agents publish concurrently for R rounds.
# Uses the fixture and sponsor of a completed fleet-journey.sh run; joins K
# fresh agents, then records per turn: wall seconds, re-plans, result.
# The service started here is always stopped.
set -eu
umask 077

if [ "$#" -ne 5 ]; then
  echo "usage: $0 HOST MINI JOURNEY_ROOT AGENTS ROUNDS" >&2
  exit 2
fi
HOST=$1 MINI=$2 ROOT=$3 K=$4 R=$5
FIX="$ROOT/fixture"
CONFIG="$FIX/deployment/pinned-config.json"
SOCKET="$FIX/public/mini.sock"
OUT="$ROOT/evidence/contention-k$K-r$R"
[ -d "$FIX" ] || { echo 'journey fixture missing' >&2; exit 2; }
[ ! -e "$OUT" ] || { echo 'contention output already exists' >&2; exit 2; }
mkdir -m 700 "$OUT"

SERVER_PID=
stop_server() {
  if [ -n "$SERVER_PID" ] && kill -0 "$SERVER_PID" 2>/dev/null; then
    kill "$SERVER_PID" 2>/dev/null || true
    i=0
    while kill -0 "$SERVER_PID" 2>/dev/null && [ "$i" -lt 100 ]; do i=$((i + 1)); sleep 0.1; done
  fi
  SERVER_PID=
}
trap stop_server EXIT INT TERM
nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$OUT/serve.log" 2>&1 </dev/null &
SERVER_PID=$!
i=0
until grep -q '^mini: serving ' "$OUT/serve.log" 2>/dev/null; do
  kill -0 "$SERVER_PID" 2>/dev/null || { echo 'Mini server exited' >&2; exit 1; }
  i=$((i + 1)); [ "$i" -lt 1200 ] || { echo 'Mini server not ready' >&2; exit 1; }
  sleep 0.1
done

now() { date +%s.%N; }
span() { awk -v a="$1" -v b="$2" 'BEGIN { printf "%.3f", b - a }'; }

n=1
while [ "$n" -le "$K" ]; do
  name="load-$n"
  [ -d "$ROOT/$name" ] || {
    "$MINI" keygen --secret "$ROOT/$name.key" --public "$ROOT/$name.pub" >/dev/null
    "$MINI" fleet --action join --sponsor-workspace "$FIX/sponsor" --factory-ref factory \
      --name "$name" --new-key "$ROOT/$name.key" --enroll-dir "$ROOT/enroll/$name" \
      --dir "$ROOT/$name" --fund 1000 >/dev/null 2>"$OUT/join-$n.stderr"
  }
  n=$((n + 1))
done

printf 'round\tagent\tseconds\treplans\tresult\n' >"$OUT/turns.tsv"
printf 'round\tseconds\n' >"$OUT/rounds.tsv"
total0=$(now)
r=1
while [ "$r" -le "$R" ]; do
  r0=$(now)
  n=1
  while [ "$n" -le "$K" ]; do
    (
      t0=$(now)
      if "$MINI" fleet --action publish --dir "$ROOT/load-$n" --account account \
          --topic load --payload "round $r agent $n" \
          >"$OUT/r$r-a$n.json" 2>"$OUT/r$r-a$n.stderr"; then
        replans=$(jq -r .replans "$OUT/r$r-a$n.json")
        result=admitted
      else
        replans=-
        result=failed
      fi
      printf '%s\t%s\t%s\t%s\t%s\n' "$r" "$n" "$(span "$t0" "$(now)")" "$replans" "$result" \
        >>"$OUT/turns.tsv"
    ) &
    n=$((n + 1))
  done
  wait
  printf '%s\t%s\n' "$r" "$(span "$r0" "$(now)")" >>"$OUT/rounds.tsv"
  r=$((r + 1))
done
total=$(span "$total0" "$(now)")
stop_server

awk -F '\t' -v K="$K" -v R="$R" -v total="$total" 'NR > 1 {
    turns++; if ($5 == "admitted") { ok++; replans += $4; secs += $3; if ($3 > max) max = $3 }
  } END {
    printf "{\"agents\":%d,\"rounds\":%d,\"turns\":%d,\"admitted\":%d,\"replans\":%d,", K, R, turns, ok, replans
    printf "\"meanTurnSeconds\":%.3f,\"maxTurnSeconds\":%.3f,\"wallSeconds\":%.3f,", secs / (ok ? ok : 1), max, total
    printf "\"admittedPerSecond\":%.4f}\n", ok / total
  }' "$OUT/turns.tsv" >"$OUT/summary.json"
cat "$OUT/summary.json"
