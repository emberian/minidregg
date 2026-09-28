# r3 local Bonsai A/B configuration staging

The read-only source config is r3
`base/workroom/deployment/pinned-config.json` (SHA-256
`c2c79aa69f66ecc7922f69f620a9dd9ca24cfea25cd94282fcb1a40c2b8296b8`).
A mode-0600 copy outside that fixture is staged at
`/tank/dregg-preview/mini-r3-bonsai-review-20260927/host-cb55-candidate.json`
(SHA-256 `0af8e9422f54dbe840d79f449829152d44c92653f4aa33bf8203b1217a021a2f`).
It changes only provider configuration: two `providerServices` entries for
7950 and 7951, both with tariff version 1, model `bonsai2-27b-ptq1`, and
zero input/output micro-units per million. Zero is allowed by the source
tariff contract and makes this a local preview with a real signed reserve and
usage quote; it does not remove the input/output token, wall, or task budgets.
The candidate names the same authoritative storage root. At the time of this
render it was only parsed read-only; a later idle operator start (invocation
`79bb`) used this candidate and then stopped after a protected helper-ancestry
guard refused the handoff. That attempt was not an A/B controller prompt or
provider settlement. The later INSTALL owner must verify current service and
Store state afresh.
The cb55 Host image
`/tank/dregg-build/minidregg-cb55b81-host/bin/minidregg-host-cb55b81-r1`
(SHA-256 `89973efe154b3f53bb279a931a93aed0b0a1d341d759dc776dca635dda01c354`)
read this exact candidate in `profile` mode: it projected only the two
`providerMeterings` IDs, the pinned model/version/zero rates, and one common
source tariff digest. That was config parsing only, with no Store open.
The builder separately exercised exact cb55 Host and Mini on a private copied
Store with retained fixture SSE bytes: strict v2 selectors 7204 and 7205 each
returned a quote for its selected provider (charge 3), and the copied Store
SHA inventory was unchanged. That is a read-only protocol check using fixture
model/usage bytes, not a Bonsai call or r3 acceptance.

`render-r3-bonsai-review.sh` consumed the exact r3 allocation, this Host
candidate, qualified Linux Mini/Host/launcher paths, and two distinct worker
runtime roots. It wrote only under the new review directory. The resulting A/B
configs are respectively
`/tank/dregg-preview/mini-r3-bonsai64k-review-20260927/a/controller-review.json`
(SHA-256 `836c5918735afdbe2d2e82b8b6bb598e1612196de1ac2da3262ec331470a89c1`)
and its `b/` sibling (SHA-256
`37c054f320d79527df36d53cea3ee719a87743858ffcb4eb7f85907edc802853`).
The private `artifact-sha256.txt` retains source config, allocation, qualified
executables, and rendered config hashes. Each controller
candidate pins its own parent, tool and provider signing-key **paths** from
the existing r3 provision. It selects parent 7920/7921, tool 7930/7931,
provider 7950/7951, and parent provider witness 205/305 respectively. The
provider uses `reserve:1`, metered `charge:0`, input ceiling 65024, output
ceiling 512, two Hermes iterations, 180-second per-request timeout, and
separate bridge ports 18762/18763. The scoped Hermes worker has a 600-second
wall ceiling and `--network none`. Its only upstream is the hbox-local
OpenAI-compatible endpoint at 127.0.0.1:18081; the model credential remains
outside the worker.
The [local-model qualification](../2026-09-27-hermes-context-64k/README.md)
reports one 65,536-token context slot with q4_0 K/V and flash attention. The
input and output ceilings add to 65,536; the installed
upstream Hermes profile advertises 65,024 as its context length, satisfying
Hermes's 64,000 minimum for a custom provider. The earlier 8k controller
candidates at `/tank/dregg-preview/mini-r3-bonsai-review-20260927/{a,b}`
are preserved but unstarted and known to fail Hermes session creation at that
minimum. The 8k server is inactive.
This hbox review stages both controllers under one operator UID. Separate
worker roots and workspaces make the two launch mounts distinct; they do not
replace the dedicated task-account isolation required for an external offer.

Each mode-0700 controller state directory now contains an owned mode-0600
copy of the known hbox-local model key. The renderer itself never reads or
copies the key; a separate private install compared the bytes without
displaying them. The existing `check-hosted-pair` preflight passed on both
rendered configs, including distinct paths and no secret under either worker
mount. These remain **review candidates**, not qualified controller
deployments. The r3 fixture writer has since released the Store to the
dedicated INSTALL owner; this note does not authorize starting either
controller or replacing that owner's service selection. The rendered configs
leave app API routes empty: accepted event22 tickets,
event27 grants, and exact issue indices/receipts are required before adding
`agentLifetimeDispatchServices` and controller lifetime route pins. A separate
dispatchTask must then pin the resident socket, distinct host UID, enrolled
payer signer, and private operator socket; copying a route JSON into these
provider-only candidates would not enable GitWeb. Signed
current parent/provider readbacks and parent witness capability checks must
precede a prompt. The retained post-birth signed owner views showed A parent
7920 and provider 7950 idle at generation 0 with remaining 100 and 50;
B parent 7921 and provider 7951 had the same states and allowances. Those
views predate later app work and cannot stand in for current reads. A single
cb55-qualified Host/socket and the INSTALL owner's current-state proof are
required before these controller configs can be selected. The committed
[lifetime service overlay](../../../scripts/spk-platform/prepare-lifetime-host-services.sh)
consumes both accepted event27 route handoffs and constructs exact A/B
`agentLifetimeDispatchServices` selectors. It re-inspects the original grant
ingresses with a pinned Host against the current Store before producing a new
private Host config. Native execution and validation of that post-issue
overlay remain pending; the provider-only candidate here does not admit
event26.
The 65,536-context Bonsai server passed authenticated direct nonstream chat and
streaming structured-tool protocol checks, including terminal usage and
`[DONE]`; these were direct server checks, not Mini provider calls. A no-send
capture of unforked Hermes with its 16 built-in tools produced a 35,808-byte
first request without `max_tokens`; the gateway would insert the authorized
512-token output ceiling. This capture lacks the full accepted GitWeb MCP
catalog. Before a real Mini prompt, a no-send capture must measure that actual
serialized catalog and request against the 65,024 input ceiling. The gateway's
wire-byte estimate is profile-specific and is not an independent exact
tokenizer count; the backend enforces its 65,536 context.

The cb55 resource client
`/tank/dregg-build/minidregg-resource-client-cb55b81/bin/mini` (SHA-256
`2f205b791bc4a2ae796af277afd6f574b5e15e592b4237075fc5122202403953`)
and grain-runtime
`/tank/dregg-build/minidregg-grain-runtime-cb55b81/bin/grain-runtime`
(SHA-256 `7cb370ec7292004842c4680b77736cee9bda408665085b09f75b61c04036e40c`)
are now source-qualified. The bridge SHA-256 is
`2877ef2a5293ee0b2a7c22d0c0216dab865d3174dd68b312889661cb4f90cfcb`.
Two physically distinct A/B worker runtime roots now carry these new images;
both passed separate no-network upstream ACP `--check` and initialize probes.
The review renderer pinned their member hashes, Mini, Host, launcher,
allocation and source config before writing either candidate.
No model request, Mini provider reserve, or same-Store A/B settlement has
occurred.
