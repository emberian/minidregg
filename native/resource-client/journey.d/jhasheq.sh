#!/usr/bin/env bash
# journey.d/jhasheq.sh — K-PRED-HASHEQ: a sealed bid on the kernel (PRIVACY §3.4, J-PRIV-4's
# sealed-bid rows), on the journey's fresh Store, after J4 (the newcomer B holds a workspace).
#
# Three cells under the sealed-bid law (deploy/shell/templates/market/sealed/law.json):
# field 2 = commit, 3 = value, 4 = blinder (field 1 is written at birth). While
# request/height <= D-1 a write must keep field 2 write-once and fields 3, 4 at 0; from height D
# a write must keep field 2 unchanged and satisfy hashEq(field 3, field 4, field 2): commit = cSHAKE256("DREGG.PRED.HASHEQ/v1";
# cell ‖ names ‖ value ‖ blinder). Commitments are computed here by an independent cSHAKE256
# (pycryptodome), not by the kernel's own function.
# Rows:
#   a-commit            A commits H(bid-a, bidA, rA) in bid-a                   -> installed
#   b-commit            B (delegated) commits H(bid-b, bidB, rB) in bid-b        -> installed
#   c-copy-commit       A copies A's commit value into bid-c                      -> installed
#   a-early-reveal      A writes its bid before D                                 -> refused
#   store-sealed        the Store holds neither bid in any encoding; it does hold A's commit
#   a-reveal            at height D, A reveals (bidA, rA) in bid-a                -> installed
#   b-wrong-reveal      B reveals (bidB+1, rB) in bid-b                           -> refused
#   b-wrong-blinder     B reveals (bidB, rB+1) in bid-b                           -> refused
#   c-replay            A's public opening (bidA, rA) written into bid-c          -> refused (context)
#   a-rereveal          A re-opens bid-a to another value                         -> refused
#   store-after         A's bid is now on the Store (the grep can see plaintext); B's still is not
#   image-unchanged     no refused attempt moved the world root or height
#   b-reveal            B reveals its true opening                                -> installed
# Exported by the journey: MINI SOCKET CONFIG SPONSOR_WS NEWCOMER_WS SPONSOR_SUBJECT
# NEWCOMER_SUBJECT JOURNEY_WORLD JOURNEY_STEP_DIR. Exit 0 = every row as expected. Last stdout
# line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
TEMPLATE=$HERE/../../../deploy/shell/templates/market/sealed/law.json
UV=${UV:-/snap/bin/uv}
mkdir -p "$D/req"
rows=$D/hasheq-rows.tsv
: >"$rows"
bad=0
REFUSAL_TAG=44524547472f4e41544956452d484f53542f4f5554434f4d45
G=$(jq -r .genesisHeight "$CONFIG")
LAST=0

nonce() { od -An -tu8 -N8 /dev/urandom | tr -d ' \n'; }
host_refused() { [ "$(cat "$D/$1.rc")" != 0 ] && grep -q "encoded refusal: $REFUSAL_TAG" "$D/$1.err"; }
refusal_text() {
  grep -o 'encoded refusal: [0-9a-f]*' "$D/$1.err" | tail -1 | cut -d' ' -f3 | xxd -r -p 2>/dev/null \
    | tr -c '[:print:]' ' ' | tr -s ' ' | sed 's/^ *DREGG\/NATIVE-HOST\/OUTCOME\/v1 *//' | cut -c1-160
}
note() { printf '%s\t%s\n' "$1" "$2" >>"$rows"; }
# The Host's signed outcome of a submitted attempt that it refused at admission (the policy gate):
# {"type":"refused","phase":hex,"detail":hex}. On this branch the law's failing clause is not
# named (P-LAW's LawLeaf adds that); the phase and detail are the Host's own words.
outcome_refused() {
  local dir out
  grep -q '^mini: host returned refused; exact outcome evidence was retained$' "$D/$1.err" || return 1
  dir=$(sed -n 's/^workspace attempt: //p' "$D/$1.err" | tail -1); out=$dir/outcome.json
  [ "$(jq -r .type "$out" 2>/dev/null)" = refused ] || return 1
  printf 'host outcome refused at %s: %s' "$(jq -r .phase "$out" | xxd -r -p)" "$(jq -r .detail "$out" | xxd -r -p)"
}
row() { # NAME EXPECT(installed|refused) [DETAIL]
  local name=$1 expect=$2 got detail
  if [ "$(cat "$D/$name.rc")" = 0 ]; then got=installed
  elif host_refused "$name"; then got=refused
  elif outcome_refused "$name" >/dev/null; then got=refused
  else got=client-error
  fi
  if [ "$got" = refused ]; then
    detail=$(outcome_refused "$name") || detail="$(grep -o 'host refused [a-z]*' "$D/$name.err" | tail -1): $(refusal_text "$name")"
    detail="h=$((G + LAST)) $detail${3:+ — $3}"
  else detail=${3:-$(tail -1 "$D/$name.err" | cut -c1-160)}
  fi
  printf '%s\texpect=%s\tgot=%s\t%s\n' "$name" "$expect" "$got" "$detail" >>"$rows"
  [ "$got" = "$expect" ] || bad=$((bad + 1))
}
# attempt NAME WORKSPACE REQUEST: propose then submit; NAME.rc/.err carry the deciding step.
attempt() {
  local name=$1 ws=$2 req=$3 pid
  pid="$1-$(nonce)"
  if ! "$MINI" workspace --action propose --dir "$ws" --request "$req" --proposal-id "$pid" \
      >"$D/$name.out" 2>"$D/$name.err"; then
    echo 1 >"$D/$name.rc"; return
  fi
  "$MINI" workspace --action submit --dir "$ws" --intent "$ws/proposals/$pid/intent.json" \
    --attempt "$ws/attempts/$pid" >"$D/$name.out" 2>"$D/$name.err"
  local rc=$?
  echo $rc >"$D/$name.rc"
  if [ $rc = 0 ]; then
    [ "$(jq -r .confirmation "$ws/attempts/$pid/outcome.json")" = installed ] || echo 9 >"$D/$name.rc"
    LAST=$(jq -r .acceptedCount "$ws/attempts/$pid/outcome.json")
  fi
}
must_ok() { [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -1 "$D/$1.err")" >&2; exit 1; }; }
next_height() { echo $((G + LAST)); }
image() { # NAME: world root and height through A's signed read of bid-a
  "$MINI" workspace --action read --dir "$SPONSOR_WS" --name bid-a >"$D/$1.json" 2>"$D/$1.rerr" \
    || { echo "read $1 failed: $(tail -1 "$D/$1.rerr")" >&2; exit 1; }
  local dir
  dir=$(sed -n 's/^workspace read attempt: //p' "$D/$1.rerr" | tail -1)
  jq -er '"\(.worldRoot) \(.height)"' "$dir/challenge.json" || { echo "no challenge for $1" >&2; exit 1; }
}
field_of() { jq -r --arg f "$2" '[.cell.entries[]? | select(.key.field == $f) | .value][0] // "absent"' "$1"; }

# --- the opening, computed outside the kernel -------------------------------------------------
commit_of() { # CELL VALUE BLINDER -> decimal commit
  "$UV" run --quiet --with pycryptodome python3 - "$@" <<'PY'
import sys
from Crypto.Hash import cSHAKE256
cell, value, blinder = (int(a) for a in sys.argv[1:4])
def name(s):
    b = s.encode()
    return len(b).to_bytes(4, "big") + b
pre = (cell.to_bytes(8, "big") + name("resource/field/3/after") + name("resource/field/4/after")
       + name("resource/field/2/after") + (value + 2**255).to_bytes(32, "big") + blinder.to_bytes(32, "big"))
h = cSHAKE256.new(data=pre, custom=b"DREGG.PRED.HASHEQ/v1").read(32)
print(int.from_bytes(h, "big"))
PY
}
blinder() { od -An -tx1 -N32 /dev/urandom | tr -d ' \n' | python3 -c 'import sys; print(int(sys.stdin.read(), 16))'; }
scan() { # LABEL VALUE... : byte-pattern hits for each value over the Store and operator files
  python3 - "$W" "$@" <<'PY'
import os, sys
root, label, values = sys.argv[1], sys.argv[2], [int(v) for v in sys.argv[3:]]
paths = [os.path.join(root, p) for p in ("store", "deployment", "operator.json", "genesis.json")]
files = []
for p in paths:
    if os.path.isfile(p): files.append(p)
    for d, _, fs in os.walk(p):
        files += [os.path.join(d, f) for f in fs]
blob = [open(f, "rb").read() for f in files]
def b255(n):
    out = []
    while n: out.append(n % 255); n //= 255
    return bytes(out) + b"\xff"
out = []
for v in values:
    z = 2 * v if v >= 0 else -2 * v - 1
    be = v.to_bytes((v.bit_length() + 7) // 8 or 1, "big")
    pats = {"ascii": str(v).encode(), "store-b255": b255(z), "be": be, "hex": be.hex().encode()}
    hits = {k: sum(b.count(p) for b in blob) for k, p in pats.items()}
    out.append(f"{v}:" + ",".join(f"{k}={n}" for k, n in hits.items()))
print(f"{label} files={len(files)} bytes={sum(map(len, blob))} " + " ".join(out))
PY
}
hits() { echo "$1" | tr ' ' '\n' | grep "^$2:" | tr ',' '\n' | grep -o '=[0-9]*' | tr -d = | awk '{s+=$1} END {print s+0}'; }

# --- the cells ---------------------------------------------------------------------------------
create() { # NAME LAW
  "$MINI" workspace --action create --dir "$SPONSOR_WS" --name "$1" --storage declared --predicate "$2" \
    >"$D/create-$1.out" 2>"$D/create-$1.err"; echo $? >"$D/create-$1.rc"; must_ok "create-$1"
  LAST=$(jq -r .acceptedCount "$SPONSOR_WS/attempts/create-$1/outcome.json")
}
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
create filler "$D/req/permit-all.json"
# Records before the reveal phase: 3 creates, 1 delegation, 3 commits = 7; D leaves 2 fillers.
CLOSE=$(( $(next_height) + 7 + 2 ))
sed -e "s/{FOUNDER}/$SPONSOR_SUBJECT/g" -e "s/{LAST_SEALED_HEIGHT}/$((CLOSE - 1))/g" "$TEMPLATE" >"$D/req/law.json"
jq -e . "$D/req/law.json" >/dev/null || { echo "law template did not render" >&2; exit 1; }
for c in bid-a bid-b bid-c; do create "$c" "$D/req/law.json"; done
A_CELL=$(jq -r .target "$SPONSOR_WS/refs/bid-a.json")
B_CELL=$(jq -r .target "$SPONSOR_WS/refs/bid-b.json")
C_CELL=$(jq -r .target "$SPONSOR_WS/refs/bid-c.json")
note law "D=$CLOSE (phase 1 while request/height <= $((CLOSE - 1))); G=$G; cells a=$A_CELL b=$B_CELL c=$C_CELL"

# B gets observe+mutate on bid-b.
jq -n --arg r "$NEWCOMER_SUBJECT" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"bid-b",
  recipient:$r,verbs:["observe","mutate"],maxCost:"50000"}' >"$D/req/delegate.json"
"$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/delegate.json" --proposal-id grant-bid-b \
  >"$D/dp.out" 2>"$D/dp.err" || { echo "delegate propose: $(tail -1 "$D/dp.err")" >&2; exit 1; }
"$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$SPONSOR_WS/proposals/grant-bid-b/intent.json" \
  --attempt "$SPONSOR_WS/attempts/grant-bid-b" >"$D/ds.out" 2>"$D/ds.err" || { echo "delegate submit: $(tail -1 "$D/ds.err")" >&2; exit 1; }
LAST=$(jq -r .acceptedCount "$SPONSOR_WS/attempts/grant-bid-b/outcome.json")
"$MINI" workspace --action publish-delegation --dir "$SPONSOR_WS" --proposal-id grant-bid-b \
  --attempt "$SPONSOR_WS/attempts/grant-bid-b" >"$D/pub.out" 2>"$D/pub.err" || { echo "publish: $(tail -1 "$D/pub.err")" >&2; exit 1; }
"$MINI" workspace --action import --dir "$NEWCOMER_WS" --name bid-b \
  --from-ref "$SPONSOR_WS/proposals/grant-bid-b/recipient-reference.json" >"$D/imp.out" 2>"$D/imp.err" \
  || { echo "B import: $(tail -1 "$D/imp.err")" >&2; exit 1; }

# --- phase 1: commit ---------------------------------------------------------------------------
BID_A=271828182845; BID_B=314159265358
R_A=$(blinder); R_B=$(blinder)
COMMIT_A=$(commit_of "$A_CELL" "$BID_A" "$R_A")
COMMIT_B=$(commit_of "$B_CELL" "$BID_B" "$R_B")
seal() { # NAME COMMIT -> sealed-phase create of fields 1, 2, 3
  jq -n --arg n "$1" --arg c "$2" '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:$n,
    payload:{type:"scalar",actions:[{type:"create",key:{type:"object",field:"2"},value:$c},
      {type:"create",key:{type:"object",field:"3"},value:"0"},{type:"create",key:{type:"object",field:"4"},value:"0"}]}}]}'
}
reveal() { # NAME VALUE BLINDER EXPECTED-VALUE EXPECTED-BLINDER
  jq -n --arg n "$1" --arg v "$2" --arg r "$3" --arg ev "$4" --arg er "$5" '{type:"minidregg-workspace-proposal-v1",
    action:"invoke",targets:[{name:$n,payload:{type:"scalar",actions:[
      {type:"write",key:{type:"object",field:"3"},value:$v,expected:$ev},
      {type:"write",key:{type:"object",field:"4"},value:$r,expected:$er}]}}]}'
}
seal bid-a "$COMMIT_A" >"$D/req/a-commit.json";  attempt a-commit "$SPONSOR_WS" "$D/req/a-commit.json";  row a-commit installed "h=$((G + LAST - 1)) commit=${COMMIT_A:0:20}…"
seal bid-b "$COMMIT_B" >"$D/req/b-commit.json";  attempt b-commit "$NEWCOMER_WS" "$D/req/b-commit.json"; row b-commit installed "h=$((G + LAST - 1)) by B (subject $NEWCOMER_SUBJECT)"
seal bid-c "$COMMIT_A" >"$D/req/c-commit.json";  attempt c-copy-commit "$SPONSOR_WS" "$D/req/c-commit.json"; row c-copy-commit installed "bid-c holds A's commit value"
reveal bid-a "$BID_A" "$R_A" 0 0 >"$D/req/a-reveal.json"
before=$(image img-0)
attempt a-early-reveal "$SPONSOR_WS" "$D/req/a-reveal.json"; row a-early-reveal refused "the request a-reveal admits at D, sent before D"
after=$(image img-1)
[ -n "$before" ] && [ "$after" = "$before" ] || { note image-unchanged "FAIL: a-early-reveal moved $before"; bad=$((bad + 1)); }

S0=$(scan sealed "$BID_A" "$BID_B" "$COMMIT_A")
note store-scan-before "$S0"
if [ "$(hits "$S0" "$BID_A")" = 0 ] && [ "$(hits "$S0" "$BID_B")" = 0 ] && [ "$(hits "$S0" "$COMMIT_A")" != 0 ]; then
  printf 'store-sealed\texpect=0-bid-hits\tgot=0-bid-hits\tneither bid in any encoding; A commit found (%s hits)\n' "$(hits "$S0" "$COMMIT_A")" >>"$rows"
else
  printf 'store-sealed\texpect=0-bid-hits\tgot=FAIL\t%s\n' "$S0" >>"$rows"; bad=$((bad + 1))
fi

# --- the deadline: filler records until the next request is at height D ------------------------
k=10
while [ "$(next_height)" -lt "$CLOSE" ]; do
  jq -n --arg f "$k" '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:"filler",
    payload:{type:"scalar",actions:[{type:"create",key:{type:"object",field:$f},value:"1"}]}}]}' >"$D/req/fill-$k.json"
  attempt "fill-$k" "$SPONSOR_WS" "$D/req/fill-$k.json"; must_ok "fill-$k"; k=$((k + 1))
done
note deadline "next request height $(next_height) = D"

# --- phase 2: reveal ---------------------------------------------------------------------------
attempt a-reveal "$SPONSOR_WS" "$D/req/a-reveal.json"; row a-reveal installed "h=$((G + LAST - 1)) (bidA, rA) opens bid-a's commit"
before=$(image img-2)
reveal bid-b "$((BID_B + 1))" "$R_B" 0 0 >"$D/req/b-wrong.json"
attempt b-wrong-reveal "$NEWCOMER_WS" "$D/req/b-wrong.json"; row b-wrong-reveal refused "differs from b-reveal (admitted below) only in the value"
reveal bid-b "$BID_B" "$(python3 -c "print($R_B ^ 1)")" 0 0 >"$D/req/b-wrong-r.json"
attempt b-wrong-blinder "$NEWCOMER_WS" "$D/req/b-wrong-r.json"; row b-wrong-blinder refused "differs from b-reveal only in the blinder"
reveal bid-c "$BID_A" "$R_A" 0 0 >"$D/req/c-replay.json"
attempt c-replay "$SPONSOR_WS" "$D/req/c-replay.json"; row c-replay refused "same opening and same commit value as a-reveal (admitted); only the cell differs"
reveal bid-a "$((BID_A - 1))" "$R_A" "$BID_A" "$R_A" >"$D/req/a-rereveal.json"
attempt a-rereveal "$SPONSOR_WS" "$D/req/a-rereveal.json"; row a-rereveal refused "bid-a re-opened to bidA-1"
after=$(image img-3)
if [ -n "$before" ] && [ "$after" = "$before" ]; then
  printf 'image-unchanged\texpect=same\tgot=same\t%s across 4 refused reveals (and a-early-reveal)\n' "$after" >>"$rows"
else
  printf 'image-unchanged\texpect=same\tgot=MOVED\t%s -> %s\n' "$before" "$after" >>"$rows"; bad=$((bad + 1))
fi
"$MINI" workspace --action read --dir "$SPONSOR_WS" --name bid-a >"$D/read-a.json" 2>"$D/read-a.err"
note bid-a-fields "commit=$(field_of "$D/read-a.json" 2 | cut -c1-20)… value=$(field_of "$D/read-a.json" 3) blinder-matches=$([ "$(field_of "$D/read-a.json" 4)" = "$R_A" ] && echo yes || echo no)"

S1=$(scan revealed "$BID_A" "$BID_B")
note store-scan-after "$S1"
if [ "$(hits "$S1" "$BID_A")" != 0 ] && [ "$(hits "$S1" "$BID_B")" = 0 ]; then
  printf 'store-after\texpect=A-visible,B-sealed\tgot=A-visible,B-sealed\tA bid %s hits after its reveal (the scan sees plaintext); B 0\n' "$(hits "$S1" "$BID_A")" >>"$rows"
else
  printf 'store-after\texpect=A-visible,B-sealed\tgot=FAIL\t%s\n' "$S1" >>"$rows"; bad=$((bad + 1))
fi

reveal bid-b "$BID_B" "$R_B" 0 0 >"$D/req/b-reveal.json"
attempt b-reveal "$NEWCOMER_WS" "$D/req/b-reveal.json"; row b-reveal installed "B's true opening"

total=$(grep -c 'expect=' "$rows")
echo "$((total - bad))/$total sealed-bid rows as expected" >&2
echo "$rows"
[ "$bad" = 0 ]
