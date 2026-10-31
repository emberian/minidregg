# Reds (owned by the builder; rewritten whole each pass)

The builder is not running yet; until it is, seats add reds they find here and the build-loop seat owns the file.

| red | signature | reruns? | same place? | suspect | owner |
|---|---|---|---|---|---|
| j14-apps: Hermes final say refused (H1/H1b) | controller pays for the final say, never submits it | yes (b5, b6, b7) | open: check on the H1b overlay | 58f0bad2b overlay pending | apps-hermes |
| START: route socket path over SUN_LEN at 20-digit app ids | — | — | — | f7f23fb46 may cover it | apps-hermes |
| START: "agent reserve custody lacks confirmation" | worker enrollment lookup | — | — | — | apps-hermes |
| composed documents:protected (batch 8 dc61016cb, forge) | `owner: doc protect pd-paper`: "phase must remain inside participant workspace" (evidence composed:/ci/run/c-dc61-d1) | not rerun on a fix | same row as 837c3f457's message (7dd2f7eda read scratch vs `doc protect`'s phaseDirectory); 837c3f457 is NOT in dc61016cb | 7dd2f7eda | read-path |
| composed apps:sheet (batch 7 acc7cfa03, forge) | "same-Store app: command failed": enrollment Host outcome op83 no-record, "session enrollment plan no longer current"; frame retained, not retried (evidence composed:/ci/run/c-acc7-d1/inputs/evidence) | no: batch 8 dc61016cb passed apps on forge | different place from batch 5/6 reds (those were Hermes final say) | batch 7 delta (consent single read / attempt index) | apps-hermes |

