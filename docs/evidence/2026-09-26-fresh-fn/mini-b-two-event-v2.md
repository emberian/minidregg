# Real two-event Mini prefix export and independent verification

On 2026-09-26, the source-matched native Mini host
`/tmp/minidregg-overnight-20260926/minidregg-host-final-b-fast`
(SHA-256 `c2a1fd3699338f28eaf1d076b53cbd1bf27b4438b857b0482666205b334a394c`)
exported evidence for the **second accepted signed call** in the surviving B
Store at `/tmp/mini-fn-setup-probe-parent/distinct-run-1/mini-b/store`.
The call was `/tmp/mini-fn-setup-probe-parent/distinct-run-1/mini-b-attempt/call.bin`
(103,781 bytes, SHA-256
`ab3fd516172541ac2a13a94eb5fcb77e06bb56a896d569b0f0bfb9eac9c1c6d7`).

The fixture config encoded `fnGateway.policyAddress` as a JSON number. Current
`Host.Settings` requires its canonical decimal string; temporary B and verifier
config copies changed only that field. The original fixture configs and Store
were not modified. The verifier config had empty storage paths and retained B's
domain, genesis, and signature helper, so verification replayed the package
independently of B's Store.

The normalized [B config](mini-b-two-event-config.json) has SHA-256
`10ccd2aac6a604c83851ce4baa43e03a9379398e46904ac6def492bd72b8a174`;
the [independent pin](mini-b-two-event-independent-pin.json) has SHA-256
`3b992816ec02ade026892097d2c923a2ae833009bcaa7cdb64af583c0b0ee03e`.

Commands (both exit 0):

```sh
minidregg-host-final-b-fast B-config-current.json export-evidence call.bin mini-b-two-event-v2-package.bin
minidregg-host-final-b-fast B-independent-current.json verify-evidence mini-b-two-event-v2-package.bin mini-b-two-event-v2-receipt.json
```

The [package](mini-b-two-event-v2-package.bin) is **326,022 bytes**, SHA-256
`1b58fc62885e1c9e9da4efa706abba6fb57272b20f26c2fc9030b1d6aaf23245`.
The [independent receipt](mini-b-two-event-v2-receipt.json) has SHA-256
`1e02c2a104bf29e1e215bda94cff6658599230029e01ac5b152afb7ecd0d5f2c`
and reports `acceptedCount: "2"`, transaction ID
`38597618243160867309796552145820195279544051064490397259935699993518329756481`,
and `type: "verified-mini-native-prefix-v1"` (the receipt's existing label;
the enclosed package uses the new v2 envelope).

This verifies a real multi-event Mini correspondence. It does not by itself
show fn carriage or consumer poll of the larger article.
