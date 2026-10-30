# shellcheck shell=bash
# state, app, dir, body, out and req are supplied by featured-qualify.sh.
# shellcheck disable=SC2154
# Mercurial 7.2.4 (apps/packages/mercurial/runner.py): hgwebdir serves a collection at / with the
# grain's first repo named from the grain title ("repo" when it has none). Three parts:
#  1. the package-pinned declaration (apps/interfaces/mercurial.json) reads the empty repository's
#     summary through json-summary (a typed call; the declaration is read-only because a push is the hg
#     wire protocol, a binary changegroup, and the typed qualify gate refuses a declaration without a
#     write, as for Datasette);
#  2. the write beneath the HTML: hg-push.py pushes a hand-built HG10UN changegroup to
#     /<repo>?cmd=unbundle (hgrc: push_ssl=False, allow_push=*) over the owner route, and the
#     changeset is read back through hgweb's own raw-file and rev;
#  3. the installed descriptor must list api beside web (bridgeConfig.apiPath /).
mw_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
write_Mercurial() {
  local null=0000000000000000000000000000000000000000 call_dir="$out/interface-mercurial-summary-$BASHPID-$RANDOM" typed
  "${APP_INTERFACE_PYTHON:-python3}" "$app_interface_driver" call mercurial --route "$dir" --package-id "$pkg" \
    --operation repo.summary --args '{"repo":"repo"}' --out "$call_dir" >"$call_dir.stdout" 2>"$out/interface-mercurial.err"
  jq -e --arg null "$null" '[.. | objects | select(.node? == $null)] | length > 0' "$call_dir/responses.json" >/dev/null 2>&1 \
    || { echo "0 typed repo.summary of the empty repository did not return the null node: $call_dir"; return; }
  typed="1 typed mercurial repo.summary read of the empty repository ($call_dir/responses.json)"
  local got; got=$(req GET /)
  [[ $got == 200 ]] || { echo "0 GET / $got: $(snip)"; return; }
  local repo; repo=$(grep -o 'href="/[A-Za-z0-9_.-][A-Za-z0-9_.-]*/\?"' "$body" | head -1 | cut -d'"' -f2 | sed 's|^/||; s|/$||')
  [[ -n $repo ]] || { echo "0 index at / lists no repository: $(snip)"; return; }
  local res; res=$(python3 -I "$mw_dir/hg-push.py" "$dir" featured.txt $'written by a resident\n' "$repo" 2>&1 | tail -1)
  [[ $res == *'"ok": true'* ]] || { echo "0 POST /$repo?cmd=unbundle: ${res:0:200}"; return; }
  local node; node=$(jq -r .node <<<"$res")
  local raw; raw=$(req GET "/$repo/raw-file/$node/featured.txt")
  local raw_ok=0; [[ $raw == 200 ]] && grep -q 'written by a resident' "$body" && raw_ok=1
  local rev; rev=$(req GET "/$repo/rev/$node")
  if [[ $raw_ok != 1 || $rev != 200 ]] || ! grep -q "${node:0:12}" "$body"; then
    echo "0 pushed ${node:0:12} but raw-file $raw (text ok $raw_ok), rev $rev"; return
  fi
  local descriptor="$state/apps/$app/install/launch-descriptor/package-v1/descriptor-inspection.json"
  if [[ -f $descriptor ]] && jq -e '.interfaces | map(.kind) | (index("api") != null and index("web") != null)' "$descriptor" >/dev/null; then
    cp "$descriptor" "$out/mercurial-descriptor-inspection.json"
    echo "1 ${typed#* }; POST /$repo unbundle pushed changeset ${node:0:12}; GET raw-file $raw holds the text; GET /rev $rev; descriptor lists api and web"
  else
    echo "0 push read back, but installed descriptor does not list both api and web: $descriptor"
  fi
}
