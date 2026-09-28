#!/usr/bin/env bash
# Keyless, read-only check of the isolated preview transport. No POST or ACK.
set -euo pipefail
root=/tank/dregg-preview/fn-gitweb-r3-20260927
image=/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d/fn-host
image_sha=432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505
unit=mini-fn-gitweb-preview-r3.service

[[ $(sha256sum "$image" | cut -d ' ' -f 1) == "$image_sha" ]]
[[ $(systemctl --user show -P ActiveState "$unit") == active ]]
[[ -S $root/control.sock && $(stat -c '%a:%U' "$root/control.sock") == 600:hbox ]]
[[ $(stat -c '%a:%U' "$root") == 700:hbox ]]
cmp -- "$root/registered.fncu" "$root/position.fncu"
[[ $(stat -c '%s' "$root/empty-poll.fnev") == 0 ]]

echo 'qualified image and private artifacts:'
sha256sum "$image" "$image.core" "$root/fn.toml" "$root/tls-cert.pem" \
  "$root/registered.fncu" "$root/position.fncu" "$root/empty-poll.fncu"
echo 'user unit:'
systemctl --user show "$unit" -p ActiveState -p SubState -p Result \
  -p InvocationID -p MainPID -p ControlGroup -p MemoryMax -p MemoryPeak -p TasksMax
echo 'listener:'
ss -ltnH | awk '$4 ~ /127[.]0[.]0[.]1:11213$/ {print $4}'

status=$(FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 \
  "$image" --fn operator "$root/fn.toml" status)
grep -F 'transactions=2 articles=0' <<< "$status"
grep -F 'profile format=8' <<< "$status" | grep -F 'max-article-octets=1048576'
cat "$root/consumer-status.txt"
FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 \
  "$image" --fn consumer-inspect "$root/registered.fncu"
FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 \
  "$image" --fn consumer-inspect "$root/empty-poll.fncu"

# The single-quoted program is intentionally expanded by the remote bash.
# shellcheck disable=SC2016
clear_reply=$(timeout 8 bash -c '
  exec 3<>/dev/tcp/127.0.0.1/11213
  IFS= read -r greeting <&3
  printf "AUTHINFO USER selected-mini-publisher\r\n" >&3
  IFS= read -r reply <&3
  printf "%s\n" "$reply"')
[[ $clear_reply == '483 '* ]]
echo "cleartext authentication gate: $clear_reply"

tls_reply=$(printf 'GROUP fn.test\r\nQUIT\r\n' | timeout 10 /usr/bin/openssl s_client \
  -starttls nntp -connect 127.0.0.1:11213 \
  -CAfile "$root/tls-cert.pem" -verify_hostname localhost \
  -verify_return_error -quiet 2>/dev/null)
grep -F '480 authentication required' <<< "$tls_reply"
echo 'TLS certificate verified and unauthenticated GROUP refused'
echo 'read-only preview verification passed; no POST or ACK'
