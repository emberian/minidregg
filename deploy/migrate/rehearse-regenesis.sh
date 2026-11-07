#!/usr/bin/env bash
# deploy/migrate/rehearse-regenesis.sh INCOMING — inside rehearse-hbox.sh's frame, as root, the Store stopped:
# ship.sh --regenesis's world steps for the copy, then the walk's members/reenroll steps:
#   b. checkpoint each database's WAL, MOVE the Store to store/retired-<ts> (kept, never deleted);
#   c. per session home, everything but keys/, consent/ and earlier retired-*/ moves to retired-<ts>/;
#   e. the door's per-world state moves aside, except an enrolled request whose account exists;
#   publish INCOMING as the current candidate (lib.sh prepare_candidate_manifest + publish_candidate);
#   `run.sh init` from /etc/mini/genesis-params.json (lib.sh genesis_params_for_init, the pay observer's files).
# What ship.sh does beyond these (units, the notice, the market's and controllers' per-world state, the roster)
# has no counterpart in the frame. After it: rehearse-hbox.sh store-start, then rehearse-hbox.sh ns
# rehearse-regenesis.sh --after (run.sh sponsor, mini-reenroll --all and the members step's house/sage/public).
set -euo pipefail
. "$MINI_ROOT/usr/local/lib/mini/infra/lib.sh"
if [ "${1:-}" = --after ]; then
  as_mini "$C/run.sh" sponsor --state "$NODE"
  # the walk's members step (public, house, sage) and reenroll step (--all), with the carry. mini-reenroll in
  # MINI_ROOT mode switches no account (its as_member runs the member's possess signature as the caller), so the
  # homes are root's for its length; rehearse-hbox.sh tenant gives each back to its member after.
  chown -R root:root "$S"/*/
  "$LIB/mini-reenroll" --all | tee "$VAR/migrate/reenroll.log" || echo "rehearse: mini-reenroll reported failures (above)" >&2
  exit 0
fi
inc=${1:?usage: rehearse-regenesis.sh INCOMING | --after}
[ ! -S "$NODE/operator/mini.sock" ] || ! fuser -s "$NODE/operator/mini.sock" 2>/dev/null || { echo "rehearse: the Store is serving; stop it first" >&2; exit 1; }
ts=$(date -u +%Y%m%dT%H%M%SZ)
while IFS= read -r -d '' db; do
  # ship.sh's `sqlite3 DB 'PRAGMA wal_checkpoint(TRUNCATE);' 'PRAGMA journal_mode=DELETE;'` (hbox has no sqlite3 CLI)
  python3 -I -c 'import sqlite3,sys; c=sqlite3.connect(sys.argv[1]); c.execute("PRAGMA wal_checkpoint(TRUNCATE)"); c.execute("PRAGMA journal_mode=DELETE"); c.close()' "$db"
  [ ! -s "$db-wal" ] || { echo "rehearse: $db still has a WAL; NOT moved" >&2; exit 1; }
done < <(find "$NODE" -name '*.sqlite3' -type f -print0)
retired=$STORE_DIR/retired-$ts
mv "$NODE" "$retired"; rm -f "$retired"/public/*.sock "$retired"/operator/*.sock
echo "rehearse: old Store -> $retired"
for d in "$S"/*/; do
  moved=()
  for p in "$d".[!.]* "$d"*; do
    [ -e "$p" ] || continue
    x=${p#"$d"}
    case $x in keys|consent|retired-*) continue ;; esac
    install -d -m 0700 "${d}retired-$ts"; mv "$p" "${d}retired-$ts/"; moved+=("$x")
  done
  [ ${#moved[@]} = 0 ] || echo "rehearse: session $(basename "$d"): ${#moved[@]} entries -> retired-$ts/"
done
enrolled_ids=$(for f in "$R"/var/lib/mini-door-process/requests/*.json; do
  [ -f "$f" ] || continue
  n=$(jq -r 'select(.phase == "enrolled") | .name' "$f"); [ -n "$n" ] || continue
  id "mini-s-$n" >/dev/null 2>&1 && jq -r .id "$f"
done 2>/dev/null)
for src in "$R"/var/lib/mini-door/queue "$R"/var/lib/mini-door-process/requests "$R"/var/lib/mini-door-status; do
  [ -d "$src" ] && [ -n "$(ls -A "$src" 2>/dev/null)" ] || continue
  install -d -m 0700 "$src.retired-$ts"; kept=0
  while IFS= read -r -d '' p; do
    base=${p##*/}; keep=""
    for rid in $enrolled_ids; do case $base in "$rid".json|"$rid"|"$rid"-*) keep=1;; esac; done
    if [ -n "$keep" ] && [ "$src" != "$R"/var/lib/mini-door/queue ]; then kept=$((kept + 1)); else mv -t "$src.retired-$ts/" "$p"; fi
  done < <(find "$src" -mindepth 1 -maxdepth 1 -print0)
  echo "rehearse: door $src -> $src.retired-$ts/ (kept $kept enrolled)"
done
id=$(basename "$inc" .incoming); dst=$CD/$id
prepare_candidate_manifest "$inc" "$C"
publish_candidate "$inc" "$dst"
ln -sfn "$id" "$CD/.current.new" && mv -T "$CD/.current.new" "$C"
echo "rehearse: current -> $id"
# the walk's prep step: the old world's apps config is set aside (apps-bootstrap writes the new world's; the
# frame has no apps worker, so mini-reenroll's app-market grants say "no apps world" and skip)
[ ! -f "$ETC/apps.json" ] || mv "$ETC/apps.json" "$VAR/migrate/apps.json.previous-world"
genesis_params_for_init "$ETC/genesis-params.json" "$ETC/genesis-params.genesis.json"
pay_init=() pay_env=()
if [ -f "$ETC/pay/genesis-observer.json" ] && [ -f "$ETC/pay/genesis-enrollments.json" ]; then
  pay_init=(--pay-observer "$ETC/pay/genesis-observer.json"); pay_env=("EXTRA_GENESIS_ENROLLMENTS=$ETC/pay/genesis-enrollments.json")
fi
as_mini env "${pay_env[@]}" "$C/run.sh" init --manifest "$C/manifest.json" --params "$ETC/genesis-params.genesis.json" --state "$NODE" "${pay_init[@]}"
chgrp "$TENANT_GROUP" "$STORE_DIR" "$NODE" "$NODE/deployment" "$NODE/public"; chmod 0710 "$STORE_DIR" "$NODE" "$NODE/deployment" "$NODE/public"
chmod 0644 "$NODE/deployment/pinned-config.json"
echo "rehearse: new genesis at $NODE ($(jq -r .hostSha256 "$NODE/state.json" | cut -c1-16))"
