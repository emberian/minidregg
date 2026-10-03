#!/usr/bin/env bash
set -euo pipefail
cd /home/hbox/workbox/codex-homomorphic-bend-20261003/src/native/fhe-bend
export CARGO_NET_OFFLINE=true
bash scripts/build-scoped.sh
bash scripts/check-physical.sh /home/hbox/workbox/codex-bend-logic-20261003/natural-expression-artifact.json 866e18d809e531a0569877e8ee36c347717043f3669ddacd8a58cf5cee3ef58f /home/hbox/workbox/codex-homomorphic-bend-20261003/run-natural-01
bash scripts/check-physical.sh /home/hbox/workbox/codex-bend-logic-20261003/prelude-mux-artifact.json d158cff51aaf88f75f0ab1beb1a76dd1d59775f429f491fe8e92a490b12bd6a2 /home/hbox/workbox/codex-homomorphic-bend-20261003/run-prelude-mux-01
printf 'FHE NAT/PRELUDE-MUX ACTUAL PHYSICAL CONSUMER CHECK PASS\n'
