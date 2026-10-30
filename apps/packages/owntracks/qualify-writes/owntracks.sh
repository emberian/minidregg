# shellcheck shell=bash
# state, app, dir, body, out and req are supplied by featured-qualify.sh.
# shellcheck disable=SC2154
# POST /pub stores a location for the signed-in user (the recorder takes the identity from
# X-Sandstorm-Username, percent-decoded and reduced to its storage name); GET /api/0/last must
# return that exact report. A 200 [] POST is the friends list, not a receipt, so the readback
# requires this run's own timestamp. Then the installed descriptor must list api beside web.
write_OwnTracks() {
  local tst post got descriptor; tst=$(date +%s)
  post=$(req POST "/pub" -H 'Content-Type: application/json' \
    --data "{\"_type\":\"location\",\"lat\":52.5200,\"lon\":13.4050,\"tst\":$tst,\"tid\":\"fr\",\"acc\":10}")
  cp "$body" "$body.post"
  got=$(req GET '/api/0/last')
  if [[ $post =~ ^20 && $got == 200 ]] &&
      jq -e --argjson tst "$tst" 'any(.[]; .tst == $tst and .lat == 52.52 and .lon == 13.405)' "$body" >/dev/null 2>&1; then
    descriptor="$state/apps/$app/install/launch-descriptor/package-v1/descriptor-inspection.json"
    if [[ -f $descriptor ]] && jq -e '.interfaces | map(.kind) | (index("api") != null and index("web") != null)' "$descriptor" >/dev/null; then
      cp "$descriptor" "$out/owntracks-descriptor-inspection.json"
      echo "1 POST /pub $post; GET /api/0/last $got returns timestamp $tst; descriptor lists api and web"
    else
      echo "0 readback passed, but installed descriptor does not list both api and web: $descriptor"
    fi
  else
    echo "0 owntracks-readback-absent: POST /pub $post; GET /api/0/last $got; timestamp $tst absent [$(head -c 160 "$body" | tr '\r\n\t' '   ')]"
  fi
}
