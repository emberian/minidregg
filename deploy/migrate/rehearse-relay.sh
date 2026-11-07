#!/usr/bin/env bash
# deploy/migrate/rehearse-relay.sh — inside rehearse-hbox.sh's frame, as mini-core: edge/mini/public-ingress.sh
# (which needs the unit's own User=mini; here the same steps, for split tenancy, as the Store's account).
set -euo pipefail
. /usr/local/lib/mini/infra/lib.sh
ingress_topology_check
CANDIDATE_PROG=mini-public-ingress
candidate_serving_state
install -d -m 0700 "$NODE/tmp"
export TMPDIR="$NODE/tmp"
gid=$(getent group "$TENANT_GROUP" | cut -d: -f3)
install -d -m 0710 -g "$TENANT_GROUP" "$NODE/public"
chgrp "$TENANT_GROUP" "$NODE/public"; chmod 0710 "$NODE/public"
rm -f "$NODE/public/mini.sock"
exec "$MINI" serve-public-proxy --socket "$NODE/public/mini.sock" --upstream "$NODE/operator/mini.sock" --config "$CONFIG" --socket-gid "$gid"
