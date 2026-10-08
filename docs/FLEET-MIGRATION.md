# Fleet migration: `dregg-client-sign` to `mini fleet-sign`

For Pug. Your harness (helm, `akapug/helm`) reaches Bread's signer in exactly two shapes, so
that is what this page is built around. The mapping of every verb is in
[`FLEET-SURFACE.md`](FLEET-SURFACE.md); this page is what you change.

## What your harness actually calls

Read in helm at `b9f0db0` (`helm/chat.py`, `helm/cell.py`); the full transcript, with each
line marked OBSERVED or INFERRED, is in the recorded run below.

| call | where | answer helm reads |
| --- | --- | --- |
| `join --profile SEAT --fund 0` | `chat.py:1350` (`HELM_CHAT_JOIN_FUND`, default 0) | last JSON line, `cell` |
| `send --profile SEAT --to OWNCELL --topic helm.chat\|helm.land PAYLOAD` | `chat.py:1412` | `sent`, `turn_hash`, `receipt_hash`, `chain_index` |
| `roster --json`, and `helm cell accept\|recv\|heartbeat\|roster` | `cell.py:881`, `:950` | legacy meld verbs; Bread's signer never had them |

helm never calls `transfer` or `receipt` through the signer; it reads receipts, cells and the
faucet over HTTP (`/api/receipts`, `/api/cell/ID`, `/api/faucet`). `transfer` and `receipt`
below are the Bread verbs your other tooling may call; they are marked INFERRED.

## What changes

- **Install.** Put `native/resource-client/dregg-client-sign` where seats already run that
  name (`~/.local/bin/dregg-client-sign`; `MINI_BIN` names the `mini` client). It is three lines
  that run `mini fleet-sign "$@"`; the verbs and flags are `mini`'s own.
- **Profile home.** `MINI_FLEET_HOME/profiles/NAME` (default `~/.mini-fleet`), not `~/.dregg/profiles`.
  `--profile` is as before; `DREGG_PROFILE` is not read.
- **A socket, not a URL.** The profile is pinned to its Host's socket. `--node-url http://...` is
  refused; `unix:/ABS/SOCKET` is accepted if it is the pinned one.
- **No bearer.** `--token`, `--token-file` are refused. Authority is the signature under the
  account's grant.
- **No faucet, no exempt class.** Every turn pays the pinned tariff from the profile's account.
  helm's `join --fund 0` makes an account that cannot pay for its first send. Fund at join
  (`HELM_CHAT_JOIN_FUND=N`) or by a `transfer` from a funded profile. `--fund` on send or transfer is refused.
- **`join` runs where the sponsor is.** The sponsor admits the key and funds the account
  (`MINI_FLEET_SPONSOR`). On a seat with no sponsor workspace a first `join` is refused by
  name; a profile that already joined answers its balance. So seats are admitted by the
  operator, and the seat then holds the profile. Moving a profile (its key) from the sponsor's
  machine to a seat's is a key-custody decision for the operator, not something this kit does.
- **Accounts are decimal.** The `cell` a join prints is a decimal account, not 64 hex. A cached
  Bread cell id is refused ("Bread cell id"). `send --to` is accepted only as the profile's own
  account (it means nothing more, as in the Bread tool helm was written against); any other
  account is refused: use `transfer`.
- **Ids.** `turn_hash` is Mini's transaction id as 64 hex, `chain_index` the accepted count,
  `finality` is `accepted` (one level; `--accept-tentative` is refused), and `receipt_hash` names
  Mini's four-field receipt (printed as `receipt`); see FLEET-SURFACE.md. A call repeated while an
  earlier one is unfinished answers that call's receipt (`replayed`) and commits nothing.
- **Ambient environment.** `DREGG_NODE_URL`, `DREGG_API_TOKEN(_FILE)`, `DREGG_NODE_PASSPHRASE`,
  `DREGG_COORDINATION_EXEMPT`, `DREGG_PROFILE` are exported by helm on every call. They are not
  read, and each one set is named on stderr.

### Rewrite table

| Bread | Mini |
| --- | --- |
| `DREGG_NODE_URL=http://H:8899`, `--node-url` | the pinned socket; `--node-url unix:/ABS/SOCKET` or omit |
| `DREGG_API_TOKEN`, `DREGG_API_TOKEN_FILE`, `--token-file`, `--token` | none |
| `DREGG_NODE_PASSPHRASE`, `DREGG_COORDINATION_EXEMPT` | none |
| `DREGG_PROFILE`, `~/.dregg/profiles/ACTIVE` | `--profile`, `MINI_PROFILE`, `MINI_FLEET_HOME/profiles/ACTIVE` |
| `join --fund N` (faucet) | `join --fund N` where the sponsor is (a Book posting) |
| `send ... --fund N`, `transfer ... --fund N` | refused; fund by `transfer` |
| `transfer --to HEX64` | `transfer --to DECIMAL_ACCOUNT` |
| `--accept-tentative` | refused (one level) |
| receipt by hash (HTTP) | `receipt --turn-hash TX`; head: `receipt --head` |
| the retry that re-signs | `retry --attempt DIR`: the exact retained bytes, answered `replayed` |

## Changes helm itself needs

These are in helm, not in Mini, and each was measured by running helm's real code against the
shim (the probe in the recorded run).

1. **The HTTP probes.** `_signed_row` asks `GET /api/receipts` (`node_head`) before it ever
   calls the signer, and `_sign_send` calls `_balance`, `_faucet` and `_revive` over HTTP. Mini has
   no HTTP ingress, so on a Mini-only seat these must be skipped.
2. **The fee.** helm sets `DREGG_COORDINATION_EXEMPT=1` and `LOW_WATER` from a faucet. Neither
   applies; fund the seat's account.

## Recorded run

The command transcript is [`native/resource-client/fleet-migration-replay.sh`](../native/resource-client/fleet-migration-replay.sh);
each call carries its provenance. **OBSERVED** means read in helm's code at `b9f0db0` (`file:line`);
**INFERRED** means taken from Bread's `dregg-client-sign` contract and Pug's commits to it
(`aeca5dea1` transfer, `b1854fbab` join/send), never seen invoked in helm.

- OBSERVED: `join --profile SEAT --fund 0`; `send --profile SEAT --to OWNCELL --topic helm.chat|helm.land PAYLOAD`
  (one argv word, the 73/78-byte blake2b digest); a second send as helm's retry; `roster --json`,
  `accept`, `recv`, `heartbeat`; the ambient `DREGG_*`/`MELD_*` environment on every call.
- INFERRED: `transfer`, `receipt`, send with payload words and no `--to`, `--node-url`, `--token`,
  `--token-file`, `--accept-tentative`, `--fund` on send/transfer.
- PLANTED: the verb `frobnicate`.

Run on burst2-b against a fresh one-sponsor Store (Host `1cc8edbd...`, built at the lane commit):
32 checks pass, each mapped call answered with one JSON object, each unmappable shape exits non-zero
with an empty stdout and its reason on stderr (`unknown verb 'roster'`, `Bread cell id`, `no HTTP
ingress`, `no bearer token`, `one commitment level`, `no faucet`, `has not joined`,
`another account`). Six planted wrong expectations (wrong filter, wrong sequence, wrong refusal
reason, accept expected of a refusal, refusal expected of an accept, an unknown verb expected to
send) each turn the checker red. Evidence:
[`docs/evidence/2026-10-06-fleet-migration/`](evidence/2026-10-06-fleet-migration/)
(`transcript.log` is the readable run, `results.tsv` the verdicts, `helm-probe.json` below).

Two defects the replay found in the client, both fixed (not principled differences):
`send --to OWNCELL` was refused, and a re-`join --fund 0` of a profile holding 0 answered an error
instead of balance 0.

**helm's own `_sign_send`, unmodified, against the shim** (`helm-probe.json`). Before cv
01a11476-1c59, helm reported `send_failed` ("sent:true response has invalid
turn_hash/receipt_hash/chain_index", twice) while **two turns committed**: fleet-sign printed no
`receipt_hash` and a decimal `turn_hash`, so helm re-sent. fleet-sign now answers both in helm's
64-hex shape, and the replay checks that helm concludes `sent` on its first attempt with exactly
one turn landed (rows Z2a, Z2). helm needs no change for this; the fix is Mini's.
