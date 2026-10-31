#!/bin/sh
# Append-only capability allocation for event28. This does not touch the Store.
set -eu
umask 077
[ "$#" -eq 2 ] || { echo "usage: $0 PREPARED_ROOT NEW_OVERLAY.json" >&2; exit 2; }
root=$1 output=$2
for path in "$root" "$output"; do
  case "$path" in /*) ;; *) exit 2 ;; esac
  case "$path" in *'/../'*|*'/./'*|*'//'*|*'/..'|*'/.'|*'/') exit 2 ;; esac
done
case "$root" in /var/lib/minidregg/spk/fixtures/*) ;; *) exit 2 ;; esac
case "$output" in "$root"/continuations/*) ;; *) exit 2 ;; esac
path=$root
while :; do
  [ -d "$path" ] && [ ! -L "$path" ] || exit 2
  owner=$(stat -c '%u' "$path"); mode=$(stat -c '%a' "$path")
  { [ "$owner" = 0 ] || [ "$owner" = "$(id -u)" ]; } || exit 2
  [ $((0$mode & 022)) -eq 0 ] || exit 2
  [ "$path" = / ] && break
  path=${path%/*}; [ -n "$path" ] || path=/
done
allocation=$root/source-stage/agent-allocation.json
[ -d "$root/source-stage" ] && [ ! -L "$root/source-stage" ] &&
  [ "$(stat -c '%u:%a' "$root/source-stage")" = "$(id -u):700" ] || exit 2
[ -f "$allocation" ] && [ ! -L "$allocation" ] &&
  [ "$(stat -c '%u:%a' "$allocation")" = "$(id -u):600" ] || exit 2
path=${output%/*}
while [ "$path" != "$root" ]; do
  [ -d "$path" ] && [ ! -L "$path" ] &&
    [ "$(stat -c '%u:%a' "$path")" = "$(id -u):700" ] || exit 2
  path=${path%/*}
done
[ ! -e "$output" ] && [ ! -L "$output" ] || exit 2
jq -e '
  .app == "8401" and .packageManifest == "8402" and
  ([.humans[] | [.route,.subject,.ticket,.plannedCaps.ticketOwner,.plannedCaps.ticketObserve]] ==
   [["alice-web","8","8500","171","173"],["bob-web","9","8501","181","183"],
    ["alice-api","8","8510","191","193"]]) and
  ([.agents[] | [.route,.controller.subject,.ticket,.plannedCaps.ticketOwner,
      .plannedCaps.ticketObserve,.plannedCaps.appObserve]] ==
   [["hermes-a","10","8520","271","273","274"],
    ["hermes-b","20","8521","371","373","374"]]) and
  ([.humans[] | select(.route == "bob-web") | .plannedCaps.appObserve] == ["184"]) and
  ([.. | objects | .[]? | strings | select(. == "185" or . == "275" or . == "375")] | length == 0)
' "$allocation" >/dev/null || { echo "allocation differs or manifest child ID collides" >&2; exit 2; }
allocation_sha=$(sha256sum "$allocation" | cut -d ' ' -f 1)
jq -n --arg allocation "$allocation" --arg allocationSha256 "$allocation_sha" '
  def grant($route;$kind;$resource;$parent;$child;$holder):
    {route:$route,kind:$kind,resource:$resource,parentCapability:$parent,
     childCapability:$child,parentSubject:"8",holder:$holder,verbs:["observe"]};
  {type:"mini-spk-enrollment-observe-overlay-v1",allocation:$allocation,
   allocationSha256:$allocationSha256,
   grants:[
     grant("alice-web";"ticket";"8500";"171";"173";"8"),
     grant("bob-web";"ticket";"8501";"181";"183";"9"),
     grant("alice-api";"ticket";"8510";"191";"193";"8"),
     grant("hermes-a";"ticket";"8520";"271";"273";"10"),
     grant("hermes-b";"ticket";"8521";"371";"373";"20"),
     grant("bob-web";"app";"8401";"141";"184";"9"),
     grant("hermes-a";"app";"8401";"141";"274";"10"),
     grant("hermes-b";"app";"8401";"141";"374";"20"),
     grant("bob-web";"manifest";"8402";"143";"185";"9"),
     grant("hermes-a";"manifest";"8402";"143";"275";"10"),
     grant("hermes-b";"manifest";"8402";"143";"375";"20")]} ' >"$output"
chmod 600 "$output"
echo "event28 observe allocation retained at $output"
