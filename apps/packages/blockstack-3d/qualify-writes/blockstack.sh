# shellcheck shell=bash
# state, app, dir, body, out and req are supplied by featured-qualify.sh.
# shellcheck disable=SC2154
# The write runs through the package-pinned declaration (apps/interfaces/blockstack-3d.json): submit a score, read
# the member's best score back. Then the installed descriptor must list api beside web.
write_3DBlockstack() {
  local typed descriptor
  typed=$(typed_app_row blockstack-3d)
  [[ ${typed%% *} == 1 ]] || { echo "$typed"; return; }
  descriptor="$state/apps/$app/install/launch-descriptor/package-v1/descriptor-inspection.json"
  if [[ -f $descriptor ]] && jq -e '.interfaces | map(.kind) | (index("api") != null and index("web") != null)' "$descriptor" >/dev/null; then
    cp "$descriptor" "$out/blockstack-descriptor-inspection.json"
    echo "1 ${typed#* }; descriptor lists api and web (bridgeConfig.apiPath /)"
  else
    echo "0 typed write passed, but installed descriptor does not list both api and web: $descriptor"
  fi
}
