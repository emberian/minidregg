# HERMES-TARIFF evidence (2026-10-01, persvati, code commit 97644f8f)

Binaries: bin-SHA256SUMS (host, mini, grain-runtime, hermes-test-provider rebuilt
at 97644f8f; store, verifier, launch-gate from pay-braid prun/bin3).

| run | result | run dir (persvati) |
|---|---|---|
| J-PAY-6 (JPAY6_TASK_BASE=7110) | PASS 40/40 (jpay6-rows.tsv) | /home/ember/build/htr/j6-062652 |
| HERMES-KEYS evidence run.sh | 13/13, HERMES_KEYS_EVIDENCE_PASS, 0 fake-token hits (hermes-keys-table.tsv, hermes-keys-token-grep.tsv) | /home/ember/build/htr/hk-061125 |
| J-PAY-3 | PASS 24/24 (jpay3-rows.tsv) | /home/ember/build/htr/jpay3-055557 |
| J-PAY-2 | PASS 18/18 (jpay2-rows.tsv) | /home/ember/build/htr/jpay2-055557 |

The Host tariffs used: jpay6-operator.json (user 5; pool 7 + 20/40 per million;
homelab 3) and hermes-keys-provider-pins.json (user 1; pool 19 + 1/1; homelab 20).
