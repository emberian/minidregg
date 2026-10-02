#!/usr/bin/env bash
# Run only against a matched method/compute family with real activation.
# Uses normal member program/kind/instance commands; no custom evaluator.
set -euo pipefail
umask 077
WORKSPACE=${WORKSPACE:-${SPONSOR_WS:?}}
RUN_DIR=${RUN_DIR:-${JOURNEY_STEP_DIR:?}/jworld-prototype}
: "$MINI" "$HOST" "$CONFIG" "$SOCKET" "$WORKSPACE" "$RUN_DIR"
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
test ! -e "$RUN_DIR" || { echo "refusing existing RUN_DIR: $RUN_DIR" >&2; exit 2; }
mkdir -p "$RUN_DIR/home/requests" "$RUN_DIR/log"
N=0
say() {
  N=$((N+1))
  printf '%s\n' "$1" >"$RUN_DIR/log/$N.line"
  "$MINI" shell --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --workspace "$WORKSPACE" --home "$RUN_DIR/home" --line "$1" \
    >"$RUN_DIR/log/$N.out" 2>"$RUN_DIR/log/$N.err" || {
      cat "$RUN_DIR/log/$N.err" >&2; return 1;
    }
}
python3 "$HERE/jworld-prototype.py" --out "$RUN_DIR/home/requests"
say 'program create prototype-bundle @bundle-program.json open'
LIBRARY=$(jq -er '.programId' "$WORKSPACE/programs/prototype-bundle.json")
python3 "$HERE/jworld-prototype.py" --out "$RUN_DIR/home/requests" --library-id "$LIBRARY"
say 'program create prototype-base @base-program.json open'
say 'program create prototype-close @close-program.json open'
BASE=$(jq -er '.programId' "$WORKSPACE/programs/prototype-base.json")
CLOSE=$(jq -er '.programId' "$WORKSPACE/programs/prototype-close.json")
python3 "$HERE/jworld-prototype.py" --out "$RUN_DIR/home/requests" --library-id "$LIBRARY" \
  --base-program-id "$BASE" --close-program-id "$CLOSE"
say 'kind create prototype-poll @poll-kind.json open'
say 'create prototype-one --from prototype-poll open'
say 'instance show prototype-one'
say 'instance set prototype-vote-one prototype-one votes 7 1'
say 'submit prototype-vote-one'
say 'instance set prototype-vote-two prototype-one votes 8 1'
say 'submit prototype-vote-two'
TARGET=$(jq -er '.target' "$WORKSPACE/refs/prototype-one.json")
python3 "$HERE/jworld-prototype.py" --out "$RUN_DIR/home/requests" --library-id "$LIBRARY" \
  --base-program-id "$BASE" --close-program-id "$CLOSE" --instance-target "$TARGET"
say 'instance call prototype-base-call prototype-one base-close'
jq -e --slurpfile expected "$RUN_DIR/home/requests/expected-bytes.json" \
 '.purpose.draft.command.run.sample==$expected[0].sample and
  .purpose.draft.command.run.output==$expected[0].baseOutput' \
 "$WORKSPACE/proposals/prototype-base-call/intent.json" >/dev/null
say 'submit prototype-base-call'
say 'instance show prototype-one'
jq -e '(.value.entries|any(.field=="2" and .value=="0")) and
 (.value.entries|any(.field=="4" and .value=="2")) and
 (.value.entries|any(.field=="6" and .value=="1")) and
 (.value.entries|any(.field=="7" and .value=="0"))' "$RUN_DIR/log/$N.out" >/dev/null
cp "$RUN_DIR/log/$N.out" "$RUN_DIR/base-result.json"
say 'instance call prototype-close-call prototype-one close'
jq -e --slurpfile expected "$RUN_DIR/home/requests/expected-bytes.json" \
 '.purpose.draft.command.run.sample==$expected[0].sample and
  .purpose.draft.command.run.output==$expected[0].closeOutput' \
 "$WORKSPACE/proposals/prototype-close-call/intent.json" >/dev/null
say 'submit prototype-close-call'
say 'instance show prototype-one'
jq -e '(.value.entries|any(.field=="2" and .value=="0")) and
 (.value.entries|any(.field=="4" and .value=="2")) and
 (.value.entries|any(.field=="6" and .value=="1")) and
 (.value.entries|any(.field=="7" and .value=="1"))' "$RUN_DIR/log/$N.out" >/dev/null
cp "$RUN_DIR/log/$N.out" "$RUN_DIR/close-result.json"
# Same old run cannot execute again. Preserve its retained exact intent.
cp "$WORKSPACE/proposals/prototype-close-call/intent.bin" "$RUN_DIR/close-original.bin"
say 'instance call prototype-close-call prototype-one close'
cmp "$RUN_DIR/close-original.bin" "$WORKSPACE/proposals/prototype-close-call/intent.bin"
say 'retry prototype-close-call'
say 'instance show prototype-one'
jq -S '.value' "$RUN_DIR/close-result.json" >"$RUN_DIR/expected-state.json"
jq -S '.value' "$RUN_DIR/log/$N.out" >"$RUN_DIR/retry-state.json"
cmp "$RUN_DIR/expected-state.json" "$RUN_DIR/retry-state.json"
printf '%s\n' '{"selector":{"physicalKinds":["18"],"verbs":["2"]},"parents":[],"predicate":{"type":"any","predicates":[]}}' \
  >"$RUN_DIR/home/requests/sealed.json"
say 'law export prototype-seal prototype-poll @sealed.json'
say 'submit prototype-seal'
set +e
"$MINI" shell --host "$HOST" --config "$CONFIG" --socket "$SOCKET" --workspace "$WORKSPACE" --home "$RUN_DIR/home" --line 'instance call prototype-blocked prototype-one close' >"$RUN_DIR/refusal.out" 2>"$RUN_DIR/refusal.err"
RC=$?
if [ "$RC" = 0 ]; then
"$MINI" shell --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --workspace "$WORKSPACE" --home "$RUN_DIR/home" --line 'submit prototype-blocked' \
  >"$RUN_DIR/refusal.out" 2>"$RUN_DIR/refusal.err"
RC=$?
fi
set -e
test "$RC" = 3 && grep -q '^refused:' "$RUN_DIR/refusal.err"
printf 'shared self/super native fixture: PASS\n' >&2
printf '%s\n' "$RUN_DIR"
