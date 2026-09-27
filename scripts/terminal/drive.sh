#!/bin/sh
# Bounded, keyless test driver for one framed terminal attachment. Native
# receipts, journal state, and physical worker fencing must be checked by the
# separate task owner; this script only records the terminal presentation.
set -eu
umask 077

if [ "$#" -ne 6 ]; then
  echo "usage: $0 IMMUTABLE_RUNTIME ABSOLUTE_SOCKET hard|soft complete|detach PROMPT NEW_OUTPUT_DIR" >&2
  exit 2
fi
RUNTIME=$1 SOCKET=$2 MODE=$3 SCENARIO=$4 PROMPT=$5 OUT=$6
[ -x "$RUNTIME" ] || { echo "runtime is not executable" >&2; exit 2; }
case "$SOCKET" in /*) ;; *) echo "socket must be absolute" >&2; exit 2;; esac
[ -S "$SOCKET" ] || { echo "controller socket absent" >&2; exit 2; }
case "$MODE" in hard|soft) ;; *) echo "mode must be hard or soft" >&2; exit 2;; esac
case "$SCENARIO" in complete|detach) ;; *) echo "scenario must be complete or detach" >&2; exit 2;; esac
case "$PROMPT" in ''|*'
'*) echo "prompt must be a nonempty single line" >&2; exit 2;; esac
[ ! -e "$OUT" ] || { echo "output directory already exists" >&2; exit 2; }
command -v rg >/dev/null 2>&1 || { echo "rg is required" >&2; exit 2; }
WAIT=${TERMINAL_WAIT_SECONDS:-1500}
case "$WAIT" in ''|0*|*[!0-9]*) echo "invalid terminal wait budget" >&2; exit 2;; esac
[ "$WAIT" -le 1800 ] || { echo "terminal wait budget exceeds 1800 seconds" >&2; exit 2; }
if [ "$SCENARIO" = detach ]; then
  GATE=${TERMINAL_DETACH_GATE:?set TERMINAL_DETACH_GATE to a new physical observer marker path}
  [ ! -e "$GATE" ] || { echo "physical observer marker already exists" >&2; exit 2; }
fi
mkdir -m 700 "$OUT"
OUT=$(CDPATH='' cd -- "$OUT" && pwd)
mkfifo -m 600 "$OUT/input.fifo"
TERMINAL_PID=
cleanup() {
  exec 3>&- 2>/dev/null || :
  if [ -n "$TERMINAL_PID" ] && kill -0 "$TERMINAL_PID" 2>/dev/null; then
    kill "$TERMINAL_PID" 2>/dev/null || :
  fi
  if [ -n "$TERMINAL_PID" ]; then wait "$TERMINAL_PID" 2>/dev/null || :; fi
}
trap cleanup EXIT HUP INT TERM
"$RUNTIME" terminal "$SOCKET" "$MODE" <"$OUT/input.fifo" >"$OUT/terminal.stdout" 2>"$OUT/terminal.stderr" &
TERMINAL_PID=$!
# Linux FIFO O_RDWR opens without waiting for the child. Open only after
# spawning so the terminal child cannot inherit this writer and hide EOF.
exec 3<>"$OUT/input.fifo"

await_line() {
  pattern=$1
  deadline=$(($(date +%s) + WAIT))
  while ! rg -q "$pattern" "$OUT/terminal.stdout" 2>/dev/null; do
    kill -0 "$TERMINAL_PID" 2>/dev/null || {
      echo "terminal exited before expected event: $pattern" >&2; exit 1;
    }
    [ "$(date +%s)" -lt "$deadline" ] || {
      echo "terminal event deadline: $pattern" >&2; exit 1;
    }
    sleep 1
  done
}

# Only source-owned display lines match these anchors. Model text is always
# prefixed with a visible vertical bar by the terminal renderer.
await_line '^(mini> )?\[state\] ready$'
printf '%s\n' "$PROMPT" >&3
await_line '^(mini> )?\[busy\] Hermes prompt started; Mini will report completion or recovery state\.$'

if [ "$SCENARIO" = complete ]; then
  await_line '^\[prompt\] (completed|failed|review-needed)$'
  rg -q '^\[prompt\] completed$' "$OUT/terminal.stdout" || {
    echo "terminal did not report completed" >&2; exit 1;
  }
  printf '/quit\n' >&3
else
  # A separate physical observer creates this marker only after the scoped
  # worker is active. Closing before that would not test an in-flight detach.
  gate_deadline=$(($(date +%s) + WAIT))
  while [ ! -f "$GATE" ]; do
    kill -0 "$TERMINAL_PID" 2>/dev/null || exit 1
    [ "$(date +%s)" -lt "$gate_deadline" ] || {
      echo "physical worker gate deadline" >&2; exit 1;
    }
    sleep 1
  done
fi
exec 3>&-
close_deadline=$(($(date +%s) + 120))
while kill -0 "$TERMINAL_PID" 2>/dev/null; do
  [ "$(date +%s)" -lt "$close_deadline" ] || {
    echo "terminal did not close after hard/soft EOF" >&2; exit 1;
  }
  sleep 1
done
wait "$TERMINAL_PID"
trap - EXIT HUP INT TERM
rm "$OUT/input.fifo"
echo "terminal presentation recorded under $OUT"
