#!/usr/bin/env bash
# deploy/migrate/rehearse-consent.sh NAME STORE_USER MEMBER_USER — inside rehearse-hbox.sh's frame, as root:
# mini-consent@NAME as the box runs it (mini-consent@.socket + edge/mini/mini-consent-serve): root binds the
# one activated listener at HOME/consent/peer.sock, owned by the member's account, 0600; the worker runs as
# the Store's owner and serves that member's uid only.
set -euo pipefail
name=$1 store_user=$2 member_user=$3
C=/var/lib/mini/candidate/current N=/var/lib/mini/store/node
consent=$C/bin/minidregg-client-consent config=$N/deployment/pinned-config.json
consent_sha=$(sha256sum "$consent" | cut -d' ' -f1) config_sha=$(sha256sum "$config" | cut -d' ' -f1)
anchors=$N/consent-anchors-members/$name/${consent_sha:0:16}-${config_sha:0:16}
shared=$N/consent-shared/${consent_sha:0:16}-${config_sha:0:16}
setpriv --reuid="$store_user" --regid="$(id -gn "$store_user")" --init-groups -- \
  install -d -m 0700 "$N/consent-anchors-members" "$N/consent-anchors-members/$name" "$anchors" "$N/consent-shared" "$shared"
sock=/var/lib/mini/sessions/$name/consent/peer.sock
install -d -m 0700 -o "$member_user" -g "$(id -gn "$member_user")" "$(dirname "$sock")"
# the member's consent pins, as render-authorized-keys.sh renders them on every ship (a new genesis moves the config's)
printf '%s %s\n' "$consent_sha" "$config_sha" | install -m 0644 -o "$member_user" -g "$(id -gn "$member_user")" /dev/stdin "$(dirname "$sock")/peer.pins"
rm -f "$sock"
exec python3 -I "$(dirname "$0")/socket-activate.py" "$sock" "$(id -u "$member_user")" -- \
  setpriv --reuid="$store_user" --regid="$(id -gn "$store_user")" --init-groups -- \
  "$C/bin/mini" serve-controller-consent --socket "$sock" --consent "$consent" --config "$config" --anchors "$anchors" \
  --consent-sha256 "$consent_sha" --config-sha256 "$config_sha" --controller-uid "$(id -u "$member_user")" --resident-dir "$shared"
