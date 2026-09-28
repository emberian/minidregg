#!/usr/bin/env bash
# Fresh, private, format-8 fn preview node. Run once as hbox on hbox.
# Credentials remain under the 0700 preview root; none are printed.
set -euo pipefail
umask 077

root=/tank/dregg-preview/fn-gitweb-r3-20260927
image=/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d/fn-host
image_sha=432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505
openssl_prefix=/tank/fn/toolchains/openssl-3.5.8
port=11213
unit=mini-fn-gitweb-preview-r3

[[ $(id -un) == hbox ]] || { echo 'expected hbox service account' >&2; exit 1; }
[[ -d /tank/dregg-preview &&
   $(stat -c '%a:%U:%G' /tank/dregg-preview) == 700:hbox:hbox ]] || {
  echo 'operator must provision private /tank/dregg-preview parent' >&2; exit 1;
}
[[ ! -e $root && ! -L $root ]] || { echo 'preview root already exists; refusing' >&2; exit 1; }
[[ $(sha256sum "$image" | cut -d ' ' -f 1) == "$image_sha" ]] || {
  echo 'qualified format-8 image pin drift' >&2; exit 1;
}
[[ -x $image && -x /usr/bin/openssl ]] || {
  echo 'qualified runtime or OpenSSL unavailable' >&2; exit 1;
}
if ss -ltnH | awk '{print $4}' | grep -Eq "(^|:)${port}$"; then
  echo 'preview loopback port already occupied' >&2
  exit 1
fi
[[ $(systemctl --user show -P LoadState "$unit.service") == not-found ]] || {
  echo 'preview unit name already exists' >&2; exit 1;
}

install -d -m 700 "$root"
cat > "$root/fn.toml" <<EOF
[store]
path = "$root/store"
[listener]
host = "127.0.0.1"
port = $port
tls_cert = "$root/tls-cert.pem"
tls_key = "$root/tls-key.pem"
[control]
path = "$root/control.sock"
[auth]
required = true
protected_only = true
path = "$root/auth.toml"
EOF
chmod 600 "$root/fn.toml"

/usr/bin/openssl req -x509 -newkey rsa:2048 -sha256 -nodes \
  -days 2 -subj /CN=localhost \
  -addext subjectAltName=DNS:localhost,IP:127.0.0.1 \
  -keyout "$root/tls-key.pem" -out "$root/tls-cert.pem" \
  > "$root/cert.stdout" 2> "$root/cert.stderr"
chmod 600 "$root/tls-key.pem" "$root/tls-cert.pem"

FN_OPENSSL_PREFIX=$openssl_prefix "$image" --fn operator "$root/fn.toml" \
  init --max-article-octets 1048576 fn.test \
  > "$root/init.stdout" 2> "$root/init.stderr"

/usr/bin/openssl rand -hex 32 > "$root/posting-password"
chmod 600 "$root/posting-password"
{ cat "$root/posting-password"; cat "$root/posting-password"; } | \
  FN_OPENSSL_PREFIX=$openssl_prefix "$image" --fn operator "$root/fn.toml" \
    principal set-password selected-mini-publisher --posting \
    > "$root/principal.stdout" 2> "$root/principal.stderr"

FN_OPENSSL_PREFIX=$openssl_prefix "$image" --fn operator "$root/fn.toml" \
  status > "$root/prestart-status.txt" 2> "$root/prestart-status.stderr"

systemd-run --user --unit="$unit" --description='Isolated Mini GitWeb fn preview' \
  --property=MemoryMax=8G --property=CPUQuota=150% \
  --property=TasksMax=64 --property=Restart=no \
  --property=TimeoutStartSec=120s \
  --working-directory="$root" \
  /usr/bin/env "FN_OPENSSL_PREFIX=$openssl_prefix" "$image" \
    --fn operator "$root/fn.toml" run

for _ in {1..120}; do
  [[ $(systemctl --user show -P ActiveState "$unit.service") == active &&
     -S $root/control.sock ]] && break
  sleep 0.5
done
[[ $(systemctl --user show -P ActiveState "$unit.service") == active &&
   -S $root/control.sock ]] || { echo 'preview owner did not become ready' >&2; exit 1; }
[[ $(stat -c '%a:%U' "$root/control.sock") == 600:hbox ]] || {
  echo 'control socket mode/owner drift' >&2; exit 1;
}

FN_OPENSSL_PREFIX=$openssl_prefix "$image" --fn consumer bootstrap "$root/control.sock" \
  > "$root/bootstrap.stdout" 2> "$root/bootstrap.stderr"
FN_OPENSSL_PREFIX=$openssl_prefix "$image" --fn consumer register \
  "$root/control.sock" selected-mini-gateway fn.test "$root/registered.fncu" \
  > "$root/register.stdout" 2> "$root/register.stderr"
FN_OPENSSL_PREFIX=$openssl_prefix "$image" --fn consumer status \
  "$root/control.sock" selected-mini-gateway \
  > "$root/consumer-status.txt" 2> "$root/consumer-status.stderr"
FN_OPENSSL_PREFIX=$openssl_prefix "$image" --fn consumer position \
  "$root/control.sock" selected-mini-gateway "$root/position.fncu" \
  > "$root/position.stdout" 2> "$root/position.stderr"
cmp -- "$root/registered.fncu" "$root/position.fncu"
echo 'private fn preview ready; no article posted or ACKed'
