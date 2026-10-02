# Paid cold entry

The member keeps the Mini and SSH private keys on their own machine. A local,
source-matched Host supplies codecs and verifies the public deployment pin.
Before SSH admission, three typed HTTP routes provide public metadata, a
source-owned price breakdown, and exact enrollment status:

- `GET /mini/v1/metadata`
- `POST /mini/v1/quote` with `{miniKey,mode,weeks,starterCredit}`
- `GET /mini/v1/enrollment/KEY[?signature=HEX]`

The server is `mini enrollment-bootstrap --host HOST --config PUBLIC_CONFIG
--socket PUBLIC_SOCKET --listen 127.0.0.1:8794 --metadata PUBLIC_METADATA`.
`--check true` validates the same pins and public metadata without listening.
Only an explicitly configured `--trusted-proxy IP` may supply `X-Real-IP`.
The server has a four-worker/eight-waiter pool, two concurrent Host workflows,
4KiB bodies, 8KiB headers, and bounded reads/connects/writes. Quote requests are
limited to six per minute and four per ten seconds per address, with bounded
rate-limit state. No generic Host command or operator socket is exposed.

Metadata configuration has only `sshLogin`, `clientBundleUrl`,
`clientBundleSha256`, and optional `birthContextUrl`. The server derives the
source identity and Host digest. Neither the pinned config nor arbitrary files
are copied into HTTP responses. Status returns only the exact requested key
and, if requested, the exact transaction signature's journal decision. An
ambiguous multi-address journal signature refuses rather than selecting a row.

A fresh member can prepare payment without an SSH connection:

```
mini join --solana --host /absolute/Host --config public-config.json \
  --bootstrap-url https://node.dregg.net/mini/v1 --enrol enrol.json \
  --dir /absolute/my-membership --name friend
mini join --wait --host /absolute/Host --config public-config.json \
  --dir /absolute/my-membership --birth-context public-birth-context.json
```

The first command signs a memo and prints a Solana Pay link; it sends no
transaction. The second retains the bootstrap origin, reads exact status, and
constructs the member's own funded workspace. The generated SSH credential is
pinned in the workspace and recovery manifests and selected automatically by
Mini's proxy. The published SSH target is pinned; shared SSH configuration is
not edited. A provided `--remote` alias can select an existing SSH host config.

The quote comes from Host op121 and its exact receiver birth fee. `--weeks N`
and `--starter-credit N` select a duration and minimum spendable remainder;
`--starter-credit 0` identifies the bare entry minimum. With byte pricing off,
the source default covers the first room/document/application/session and one
hundred ordinary base-fee transactions. Provider tokens and compute have
separate prices. This is not a production DREGG conversion-rate recommendation.
Atomic rounding that buys an unwanted extra week or consumes the starter is
refused. For offline preparation, `--quote FILE --key EXISTING_MINI_KEY` replaces
the live request; the quote must match the exact key, duration, starter and pin.

The v1 memo does **not** reserve a quote or commit to a next key. Output and
metadata therefore say `priceReserved:false`; tariff changes before processing
can change the outcome. The v2 source and native paths below are a distinct after-core receiving
contract; those properties are not silently attributed to v1.

Qualification is layered: source quote boundary vectors/proofs, exact quote
binding/native recovery tests, HTTP framing/privacy/deadline/rate tests, and a
composed isolated Host journey. Deployment is separate: the infra bootstrap
unit, explicit public metadata, exact mesh proxy peer and reviewed Caddy route
must be installed together. Nothing in these commands deploys a public service.

## Quote-bound v2 entry and recovery

The after-core source adds `POST /mini/v2/status` and `/mini/v2/quote`, and
fixed binary POST routes `/mini/v2/claim/plan`, `/assemble`, `/submit`, `/lookup`.
The latter accept only closed source claim commands, not arbitrary Host
operations. Status uses the exact identity plus signature and original recipient;
it does not scan the journal. Rates, Host permits and deadlines are shared with
v1, rather than multiplied by the number of routes. Duplicate/unknown JSON
fields reach the source parser unchanged and are refused there.

`mini join --memo-version v2 --solana ... --bootstrap-url HTTPS/mini/v2`
requires an explicit `minidregg-enrol-pin-v2` containing the base58 recipient,
mint and token program, decimals, and Mini SSH login. Fresh entry creates a
local NEXT key, obtains source status and a source quote, presents the split,
and signs the exact 485-byte memo with both local keys. Explicit
`--starter-credit 0` selects bare entry; the normal fresh default asks the
source for the same useful starter allowance as v1. Byte-priced deployments
require an explicit starter budget. No command sends a Solana transaction.

The memo binds the stable deployment seed, asset and recipient, stable member
identity, current signing authority, exact pricing terms, requested weeks,
minimum spendable remainder, processing-chain expiry and NEXT commitment.
Every v2 deposit has an immutable origin and one atomic consumption. A valid
payment observed under stale terms remains a recoverable pending claim with
zero credit minted. It is not silently repriced, refunded, or paid a second
time. Expiry is the processing chain hour from authenticated observer evidence,
not the transaction timestamp. Processing after the deadline can therefore
produce a pending claim even when the transfer was sent before it.

Renewal signs a new memo using the current source owner and preserves the
original enrollment record. Registry `Some(0)` is a commitment, while a legacy
uncommitted member uses the distinct mode3 with no registry mutation. Pending
owner rotation retains stable identity and uses the precommitted successor.

Claim operations retain exact command, plan, possession signature, ingress,
original config/profile and expected receipt before their first submission.
Reopening a retained operation performs only exact lookup. Lost signing keys,
changed current authority, or later freshness/pricing changes cannot turn an
old admitted receipt into a fresh decision. An absent or uncertain reply is
not confirmation, and an incomplete record is never silently re-signed.


To choose current terms for one retained pending payment, first prepare an
unsigned command and inspect the printed source quote:

```
mini pay-claim --action quote --join-dir /absolute/my-membership \
  --host /absolute/Host --config /absolute/public-config.json \
  --weeks 1 --starter-credit 347 --expiry-hour CHAIN_HOUR --nonce NONCE \
  --output /absolute/claim.bin
mini pay-claim --action accept --join-dir /absolute/my-membership \
  --host /absolute/Host --config /absolute/public-config.json \
  --command /absolute/claim.bin --operation-record /absolute/claim-operation
mini pay-claim --action lookup --join-dir /absolute/my-membership \
  --host /absolute/Host --config /absolute/public-config.json \
  --operation-record /absolute/claim-operation
```

The starter amount above is illustrative service credit; use the source quote
and the original deposit's available amount. Quote expiry is an explicit
processing chain hour. Renewal claims select `--mode renew` and
`--payment-record /absolute/my-membership/payments/RECORD.json`; the first
entry defaults to its immutable `join.json`. The operation retains that exact
signed payment and its transaction locator before submission. Later renewals,
changes to `latest-payment.json`, and loss of the original signing key cannot
select another payment during receipt lookup. Fresh acceptance still requires
the current authorized key (`--key` may select it); pending-owner rotation uses
the precommitted successor and a source-authored rotation command.

An admitted member can instead use `--dir WORKSPACE` for fresh acceptance.
That path performs the normal workspace authority checks. Historical lookup
uses a closed retained transport context and checks the original operation's
profile, genesis, config, origin and expected receipt, without asking an old
key to prove present-day authority. Recovery across a source-profile carry
requires the dedicated retained claim adapter; ordinary SignedCall lookup
op153 does not accept these native claim ingress bytes.

New successful paid workspaces pin the common fresh-continuity contract before
atomic publication and complete the source-verified first account baseline
before acknowledging onboarding. Existing explicitly legacy setup records
remain legacy. Source-owned v2 Lean qualification and the composed runtime
journeys are still required before this after-core service is deployed;
synthetic native tests are not substitutes for that qualification.
