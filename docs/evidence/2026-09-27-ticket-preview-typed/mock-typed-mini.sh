#!/bin/sh
# Schema-only stand-in for the new read-only Mini op56 preview route.
set -eu
umask 077
command=$1
shift
[ "$command" = grain-share-issue-plan ] || exit 9
while [ "$#" -gt 0 ]; do
  case "$1" in
    --host) host=$2; shift 2 ;;
    --config) config=$2; shift 2 ;;
    --socket) socket=$2; shift 2 ;;
    --request) request=$2; shift 2 ;;
    --dir) dir=$2; shift 2 ;;
    *) exit 9 ;;
  esac
done
[ -n "${host:-}" ] && [ -n "${config:-}" ] && [ -n "${socket:-}" ] &&
  [ -n "${request:-}" ] && [ -n "${dir:-}" ] || exit 9
mkdir -m 700 "$dir"
cp "$request" "$dir/request.json"
cp "$config" "$dir/config.json"
"$host" "$config" author application-share-issue-grain-request \
  "$dir/request.json" "$dir/request.bin"
"$host" "$config" inspect application-share-issue-grain-request \
  "$dir/request.bin" "$dir/request-inspected.json"
"$host" "$config" application-grain-share-issue-plan \
  "$dir/request.bin" "$dir/plan.bin"
printf 'mock typed op56 frame\n' >"$dir/plan.frame"
"$host" "$config" inspect application-share-issue-grain-plan \
  "$dir/plan.bin" "$dir/plan-inspected.json"
sha() { sha256sum "$1" | cut -d ' ' -f1; }
jq -n --arg host "$host" --arg hostSha "$(sha "$host")" \
  --arg config "$config" --arg configSha "$(sha "$config")" \
  --arg socket "$socket" --arg request "$(sha "$dir/request.bin")" \
  --arg plan "$(sha "$dir/plan.bin")" '
  {format:"minidregg-grain-share-issue-plan-only-v1",host:$host,
   hostSha256:$hostSha,config:$config,configSha256:$configSha,
   operatorSocket:$socket,requestSha256:$request,planSha256:$plan}
  ' >"$dir/plan-pin.json"
if [ "${MOCK_BAD_PLAN_PIN:-}" = 1 ]; then
  jq '.planSha256="0000000000000000000000000000000000000000000000000000000000000000"' \
    "$dir/plan-pin.json" >"$dir/plan-pin-bad.json"
  mv "$dir/plan-pin-bad.json" "$dir/plan-pin.json"
fi
cat "$dir/plan-inspected.json"
