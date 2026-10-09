#!/bin/sh
# deploy/candidate/params.sh -- the ONE place a genesis's clock is chosen. Every driver that makes
# a genesis calls it; none writes clock values by hand.
#
#   params.sh fill-genesis PARAMS.json   a minidregg-candidate-genesis-params-v1 file
#                                        (.clock.genesisNow, .clock.maxStepSeconds: JSON integers),
#                                        before `run.sh init` or `genesis.sh`
#   params.sh fill-source  SOURCE.json   a hand-written `mini bootstrap --source` file
#                                        (.clockGenesisNow, .clockMaxStepSeconds: decimal strings),
#                                        before `mini bootstrap`
#
# Fills the file IN PLACE, at genesis time. An UNFILLED value is absent or null (the shipped
# genesis-params.example.json carries null for both): genesisNow becomes the current Unix second
# ($GENESIS_NOW when set), maxStepSeconds becomes $MAX_STEP_SECONDS (default 300).
# Refuses (exit 2, file untouched):
#   - a present value that is not a positive integer below 2^53 -- 0 included. This helper never
#     repairs an explicit bad value; `run.sh init`, `genesis.sh` and the Host refuse it too;
#   - a present value other than the one this call would write. A genesis time is chosen once:
#     re-running on a filled file refuses unless GENESIS_NOW / MAX_STEP_SECONDS pin that value.
set -eu
usage() { sed -n '4,9p' "$0" >&2; exit 2; }
die() { echo "params.sh: $*" >&2; exit 2; }
[ "$#" -eq 2 ] || usage
verb=$1 file=$2
case "$verb" in
  fill-genesis) paths='[["clock","genesisNow"],["clock","maxStepSeconds"]]' type=number ;;
  fill-source) paths='[["clockGenesisNow"],["clockMaxStepSeconds"]]' type=string ;;
  *) usage ;;
esac
command -v jq >/dev/null || die "jq is required"
[ -f "$file" ] && [ ! -L "$file" ] || die "not a regular file: $file"
now=${GENESIS_NOW:-$(date +%s)}
step=${MAX_STEP_SECONDS:-300}
for pair in "GENESIS_NOW=$now" "MAX_STEP_SECONDS=$step"; do
  case "${pair#*=}" in ''|0*|*[!0-9]*) die "${pair%%=*} must be a positive integer: ${pair#*=}" ;; esac
done
# One jq program checks and fills both values; on `error` the file is left untouched.
tmp=$file.fill.$$
trap 'rm -f "$tmp" "$tmp.err"' EXIT
# shellcheck disable=SC2016
if ! jq --argjson paths "$paths" --argjson want "[$now, $step]" --arg type "$type" '
  def pos: (type == "number" and . > 0 and . == floor and . < 9007199254740992)
         or (type == "string" and test("^[1-9][0-9]*$") and (tonumber < 9007199254740992));
  def name($p): "." + ($p | join("."));
  def fill($p; $w):
    getpath($p) as $have
    | if $have == null then setpath($p; if $type == "number" then $w else ($w | tostring) end)
      elif ($have | type) != $type then error("\(name($p)) is \($have | tojson): must be a JSON \($type) here")
      elif ($have | pos | not) then error("\(name($p)) is \($have | tojson): not a positive integer (refused, not repaired)")
      elif ($have | tonumber) != $w then error("\(name($p)) is already \($have | tojson), not \($w): a genesis clock is filled once")
      else . end;
  if type != "object" then error("not a JSON object")
  elif $type == "number" and (.clock | type) != "object" then error(".clock is absent")
  else fill($paths[0]; $want[0]) | fill($paths[1]; $want[1]) end
' "$file" >"$tmp" 2>"$tmp.err"; then
  die "$file: $(sed 's/^jq: error ([^)]*): //' "$tmp.err")"
fi
chmod --reference="$file" "$tmp" 2>/dev/null || :
mv "$tmp" "$file"
