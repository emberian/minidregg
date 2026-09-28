#!/usr/bin/env bash
# Continue only the exact private config created by provision-hbox.sh after
# its initial certificate tool refused before any Store or credential write.
set -euo pipefail
umask 077
root=/tank/dregg-preview/fn-gitweb-r3-20260927
image=/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d/fn-host
image_sha=432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505
openssl_prefix=/tank/fn/toolchains/openssl-3.5.8
unit=mini-fn-gitweb-preview-r3

[[ $(id -un) == hbox && $(stat -c '%a:%U:%G' "$root") == 700:hbox:hbox ]] || exit 1
[[ $(sha256sum "$image" | cut -d ' ' -f 1) == "$image_sha" ]] || exit 1
[[ -f $root/fn.toml && ! -e $root/store && ! -e $root/auth.toml &&
   ! -e $root/posting-password && ! -e $root/tls-key.pem && ! -e $root/tls-cert.pem ]] || {
  echo 'partial state differs from exact certificate-tool refusal; no replay' >&2; exit 1;
}
[[ $(systemctl --user show -P LoadState "$unit.service") == not-found ]] || exit 1

/usr/bin/openssl req -x509 -newkey rsa:2048 -sha256 -nodes \
  -days 2 -subj /CN=localhost \
  -addext subjectAltName=DNS:localhost,IP:127.0.0.1 \
  -keyout "$root/tls-key.pem" -out "$root/tls-cert.pem" \
  > "$root/cert-system.stdout" 2> "$root/cert-system.stderr"
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
[[ $(stat -c '%a:%U' "$root/control.sock") == 600:hbox ]] || exit 1

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
