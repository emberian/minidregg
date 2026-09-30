# Mini resource client

`mini` is the physical custody and evidence client for `minidregg-host`. The
Lean host remains the only author of semantic binary values and the only
receiver that decides admission. The Rust process generates and holds raw
Ed25519 keys, signs the host's exact inspected headers, and retains every byte
needed to recover from an uncertain response.

## Participant workspace

`mini workspace` gives one already enrolled subject a private address book and
retained attempts over the existing `author`, signed `query`, `submit`, and exact
`lookup` paths. Initialization pins the Host image path, configuration, key,
subject and optional socket. It does **not** enroll a new subject or grant any
authority. A reference is a discovery hint; every read checks the current
grant and every operation faces Lean admission under current law.

For a newcomer, `mini enroll --action plan --sponsor-workspace W --factory-ref
NAME --name REQUEST-LABEL --new-key KEY --dir ATTEMPT` uses a sponsor's signed
factory observation and control capability. Continue with `--action seal`,
`submit`, and `lookup` on that exact attempt. The request label identifies the
reservation attempt, not a permanent participant handle. Only a confirmed
admission writes private `ATTEMPT/enrollment.json`; it conveys a signing
identity, not a resource grant. Initialize the new workspace with
`--enrollment ATTEMPT/enrollment.json` instead of `--key` and `--subject`. The
client verifies the retained key matches the result's public key.

A principal whose key and subject number belong to another Store (the owner of a
selected release, for example) is enrolled as a *home identity*. Pass
`--new-public-key PUB --home-subject N` instead of `--new-key`. The principal
runs `mini enroll --action possess --dir ATTEMPT --key KEY --subject N --output SIG`
in its own process, and the sponsor seals with `--possession-signature SIG`.
The result records `keyPath: null`, so it does not initialize a workspace. See
[SELECTED-EXCHANGE.md](SELECTED-EXCHANGE.md#two-stores-with-independent-credentials).

```sh
mini workspace --action init --dir /private/alice/workspace \
  --host /absolute/minidregg-host --config /absolute/pinned-config.json \
  --key /private/alice.key --subject 7 --socket /private/host.sock \
  --birth-context /private/birth-context.json \
  --namespace-root /private/shared-operator-namespace
mini workspace --action import --dir /private/alice/workspace \
  --name notes --kind object --target 600 --observe-capability 61 \
  --operation-capability 61 --control-capability 62
mini workspace --action list --dir /private/alice/workspace
mini workspace --action describe --dir /private/alice/workspace --name notes
mini workspace --action read --dir /private/alice/workspace --name notes
```

`describe` is a signed current policy query; `read` is a signed current resource
query. The output includes the Host's typed view, and the private attempt is
retained under `workspace/attempts`. Imported numeric references are never
treated as proof that a grant exists. A source-owned operation can still be
submitted in the full typed Mini vocabulary:

```sh
mini workspace --action submit --dir /private/alice/workspace \
  --intent /private/operation.json --intent-kind intent \
  --attempt /private/alice/workspace/attempts/operation-1
mini workspace --action recover --dir /private/alice/workspace \
  --attempt /private/alice/workspace/attempts/operation-1
```

The optional `--attempt` is a new direct child of the workspace attempt
directory. A controller can retain that path before starting submission.
`recover` performs **lookup only** on the exact retained `call.bin`; it never
submits a fresh operation. `--prepare-only true` leaves a signed assembled
call without submitting it.

For a bounded agent proposal, `workspace --action propose --proposal-id ID
--request REQUEST.json --dir WORKSPACE` accepts a named `invoke` or
`install-policy` request, or a narrowed `delegate` request. An `invoke` request names 1–16 local references and
supplies supported typed actions; scalar create/write keys specify only their
local field, and content proposals support local creation actions. The client
fills resource IDs, capabilities, current roots, subject and nonces from
private references and signed current reads, then asks Lean to author the
resulting typed intent. The no-effect result is
`workspace/proposals/ID/proposal.json`, binding the retained `intent.json` by
SHA-256. The controller should pass only a proposal ID to a later submit step
and recheck that digest; proposal generation does not grant authority or
promise later admission. For example:

```json
{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[
  {"name":"notes","payload":{"type":"content","actions":[
    {"type":"createAtom","atom":"7001","kind":{"type":"text"},"payload":"6869"}
  ]}}
]}
```

A delegation request names one reference and the recipient's already admitted
subject. The client obtains signed resource, policy and typed parent-capability
views from the same image, checks the requested verbs and cost against the
parent, and durably reserves a fresh child capability ID. The requested grant
must include `observe` so the recipient can inspect its named reference;
operation-only delegation remains available through the lower-level typed
intent surface. The requested grant still faces current-law admission:

```json
{"type":"minidregg-workspace-proposal-v1","action":"delegate",
 "name":"notes","recipient":"8","verbs":["observe","mutate"],
 "maxCost":"50000"}
```

Submit its retained `proposals/ID/intent.json` through the usual workspace
`submit --attempt` path. After an admitted receipt, `workspace --action
publish-delegation --proposal-id ID --attempt ATTEMPT` performs exact
historical lookup and writes `proposals/ID/recipient-reference.json`. Transfer
that file to the recipient through an authorized channel; they can run
`workspace --action import --name LOCAL --from-ref RECEIVED.json`. The imported
name remains a hint; their key and current law determine every later use.

Generic native resource creation uses `workspace --action create --name NAME
--storage content|declared --predicate PREDICATE.json --dir WORKSPACE`. The
birth context pinned at initialization supplies deployment genesis, template,
factory/payer grants and funding, while the participant selects any supported
predicate tree. Its JSON shape is:

```json
{"type":"minidregg-participant-birth-context-v1",
 "genesis":{},"template":{},"sourceCapabilities":[],"funding":[],
 "feePayer":"7","grants":[]}
```

`genesis`, `template` and grants must be the real bootstrap values for the
enrolled subject; empty values above only show the fields. A shared private
namespace root durably reserves a target and owner/control capability IDs
for this exact request. The client retains the source and binds it to one
attempt **before** submit. A repeated create of the same name recovers that
attempt and never authors a replacement call. Only a confirmed birth becomes
a local reference. The namespace service currently coordinates controllers
running under one operator Unix account; separate Unix accounts need an
authenticated broker. Lean remains the final collision and authority checker.
Creation uses the loaded-current resource birth route. The client first
retains a signed factory resource observation, then asks Lean to derive the
current height and authority epochs and author a canonical binary intent.
The exact intent and signed observation are retained before binary submission.
An interrupted pre-submit authoring step can resume from those bytes; once an
attempt contains a call, recovery uses historical lookup without reauthoring.
This newer route requires a qualified current Host image and a persistent
socket. Do not treat the CLI's reservation as an admitted birth.

## Persistent local host session

Start one local Lean host with a Unix socket in a directory owned by your
account and inaccessible to other accounts. The service refuses an existing
live owner and a directory with group or world access:

```sh
mkdir -m 700 /private/path/mini-session
mini serve --host /absolute/path/minidregg-host \
  --config /absolute/path/deployment/pinned-config.json \
  --socket /private/path/mini-session/host.sock
```

The service holds an owner-private lock, preserves `host.config` across
restarts, and recovers a stale socket only after proving it is an owned Unix
socket with no listener. Restart with the same config bytes and socket path;
config drift refuses. A live owner always refuses a second service. To change
the operator config, stop the service and choose a new private socket path.

In another shell, add `--socket /private/path/mini-session/host.sock` to
`mini author`, `submit`, `query`, or `retry`. Evidence export, independent
verification and bootstrap still use direct Host/Main CLI commands. The socket
carries bounded length-framed
binary requests; the service passes them to one long-lived
`minidregg-host CONFIG.json stdio` process, one request at a time. Lean still
authors canonical bytes, inspects headers, assembles signed calls, checks
current authority and decides submissions. The service accepts no shell
command or client-supplied file path. It reads its fixed config at startup.
The daemon passes a private launch copy of that config to the host and
requires each client request to present identical config bytes. The local
socket rejects unknown operation codes. Fn poll accepts only an empty request;
fn ACK accepts only a canonical decimal Mini transaction ID, never paths.
Every current `mini` socket request also hashes its selected `--host`
executable and sends that image digest in the v2 envelope. A service running
different Host bytes refuses before forwarding the operation; the client does
not fall back to the legacy v1 envelope. Consumer workers additionally check
the selected image against their durable v2 worker pin. This is a local
owner-controlled executable identity check, not remote attestation.

The transport covers profile, description, author, inspect, signatures,
observation challenge/assembly, prepare, call assembly, submit, lookup, and
query. `submit` syncs the exact `ATTEMPT/call.bin` and its directory ancestry
before sending it; retry does the same before reuse. If a pipe or
socket closes during a request, the client reports **uncertain**; inspect the
retained attempt and use `mini retry --attempt ATTEMPT --mode lookup` to
recover the original receipt. A fresh service can use the same pinned config
and store after a restart. Attempt manifests record the socket path, and
`retry --socket NEW-SOCKET` may select a restarted endpoint. `retry --direct
true` uses the retained host and config paths when no socket is available.
The broker bounds a client frame to 10 seconds, a host request write to 30
seconds, and a host reply to 600 seconds. On a host pipe timeout it exits and
reaps the child; the caller still treats the request as uncertain.

Public `mini inspect` accepts the typed fn inbox summary and the source-owned
`application-permission-schema` presentation. The schema route bounds both
input and output to 1 MiB and requires Host's canonical bytes to equal the
exact supplied schema binary before writing the requested result. Host owns
the schema root, permission, role, and denial interpretation.

## Operator custody for application shares

Application share issue uses a separate operator service. Run it under the
operator OS account, with a new `0700` socket directory that participants
cannot access. `serve-operator` pins that socket's mode; an existing public
`serve` endpoint cannot restart as an operator endpoint. The public socket
refuses unsigned planning/assembly operations 32/33. The operator socket
accepts only share issue operations 28/29/32/33 and checks the peer UID.

```sh
mkdir -m 700 /operator/private/share-socket
mini serve-operator --host HOST --config PINNED-CONFIG.json \
  --socket /operator/private/share-socket/host.sock
```

The producer supplies `REQUEST.json`. It selects a ticket, payer, funding,
and source capabilities, but does not supply birth cells, policies, signing
headers, or authority. The operator first previews the source-owned canonical
Request and current Plan using the pinned Host, then writes a private approval
file. These commands perform no native issue:

```sh
mini author --host HOST --config PINNED-CONFIG.json \
  --kind application-share-issue-request --input REQUEST.json --output REQUEST.bin
HOST PINNED-CONFIG.json inspect application-share-issue-request \
  REQUEST.bin REQUEST-inspected.json
HOST PINNED-CONFIG.json application-share-issue-plan REQUEST.bin PLAN.bin
HOST PINNED-CONFIG.json inspect application-share-issue-plan PLAN.bin PLAN.json
```

The approval file and its parent directory must be owned by the operator and
inaccessible to group and world. Its `requestSha256` covers the **entire**
canonical Request, including payer, funding amounts and source capabilities;
`canonicalSpec` comes from `REQUEST-inspected.json`. The four readable
selectors help the custodian check issuer, participant and delegate scope.
Each ordered `signers` entry corresponds to a `PLAN.json` `slots` entry and
pins that slot's exact header digest and the expected enrolled key identity:

```json
{
  "type": "minidregg-application-share-issue-approval-v1",
  "requestSha256": "<lowercase SHA-256 of REQUEST.bin>",
  "canonicalSpec": "<REQUEST-inspected.json canonicalSpec>",
  "issuer": "7",
  "participantSubject": "8",
  "appDelegateCapability": "141",
  "ticketResource": "8500",
  "signers": [
    {
      "role": "<PLAN.json slots[0].role>",
      "index": "<PLAN.json slots[0].index>",
      "keyId": "<PLAN.json slots[0].signing.keyId>",
      "keyEpoch": "<PLAN.json slots[0].signing.keyEpoch>",
      "publicKey": "<64 lowercase hex digits from enrollment>",
      "headerSha256": "<lowercase SHA-256 of decoded slots[0].header>",
      "keyPath": "/operator/private/keys/signer-0.key"
    }
  ]
}
```

List every slot, including the final app `.delegateObject` slot; one key is
not assumed to authorize them all. The key files and their parent directories
must also be owner-private. `share-issue-prepare` reauthors Request, asks
operator op32 for a fresh Plan, requires exact canonical Request and Spec
equality, checks each approved slot/header/key, signs only the Host's header
bytes, lets Host encode the signature list and asks op33 to assemble ingress.
It retains all bytes in a new private directory. If a current root, signing
key or plan changes after preview, approval must be reviewed again.

```sh
mini share-issue-prepare --host HOST --config PINNED-CONFIG.json \
  --socket /operator/private/share-socket/host.sock \
  --request REQUEST.json --approval /operator/private/approval.json \
  --dir /operator/private/share-attempt
mini share-issue-submit --socket /operator/private/share-socket/host.sock \
  --attempt /operator/private/share-attempt
mini share-issue-lookup --socket /operator/private/share-socket/host.sock \
  --attempt /operator/private/share-attempt
```

Op28 is the sole submit attempt. The client writes and syncs its marker
before sending. If the reply is lost, repeat **lookup op29 only**; no
automatic resubmit occurs. The first confirmed exact outcome becomes a
durable four-field receipt anchor, reconstructed from a retained response
frame if a crash interrupted extraction. Later lookups must match its
transaction, event, accepted count and world root. Native receiving
rechecks current authority and installed policy; a signed Plan alone is not
an accepted share or a dispatch grant.

Event21's independent purse reserve has a separate operator custody path.
The controller allocates `reserveOperationId` and supplies a source JSON
request containing the full canonical HTTP bytes and its configured purse,
parent, ticket, and allowance selectors. The private Host checks those
selectors against its startup pin before op58 releases a current-image Plan.
The operator approval is an owner-private JSON object with type
`minidregg-agent-reserve-approval-v1`, the exact `requestSha256` and
`planSha256`, the complete `fixedSelectors` object from
`plan-inspected.json`, and ordered `signers`. Each signer pins the slot's
decimal `role`, `index`, `keyId`, `keyEpoch`, lowercase `publicKey`,
`headerSha256`, and absolute owner-private `keyPath`. The controller must
compare the source plan's context and intended request before issuing that
approval; the resident app never receives the purse key.

```sh
mini agent-reserve-plan --host HOST --config PINNED-CONFIG.json \
  --operator-socket /operator/private/host.sock \
  --public-socket /private/host.sock --request SOURCE.json \
  --dir /operator/private/reserve-attempt
mini agent-reserve-seal --attempt /operator/private/reserve-attempt \
  --approval /operator/private/reserve-approval.json
mini agent-reserve-submit --attempt /operator/private/reserve-attempt
mini agent-reserve-lookup --attempt /operator/private/reserve-attempt
```

The Plan and its inspection, source signature list, op59 frame, and exact
canonical op2/op3 `call.bin` live in that single private attempt directory.
The client signs only Host-selected headers matching the approval. It writes
and syncs `submit-marker.json` before its **one** public op2. On a lost or
refused reply, `agent-reserve-lookup` is the read-only exact op3 recovery;
the command never resubmits. A confirmed result retains the native four-field
receipt and decimal `reserveIndex = acceptedCount − 1` in `receipt.json`.
Event21 still rechecks that admitted reserve and the current purse before any
dispatch; this custody command grants no delivery permit.

For the later paid dispatch, the controller keeps the original reserve
attempt and its confirmed receipt. It obtains a current source Plan through
private op48, but the payer signer does not trust resident-supplied Plan
bytes or inspection JSON. The owner-private approval has type
`minidregg-agent-payer-approval-v1`, exact `planSha256` and
`compactSelectorRequestSha256`, the complete `fixedSelectors` and `context`
objects from the original reserve inspection, `canonicalHttpHex` for the
original full HTTP request, decimal `reserveIndex`, exact `reserveReceipt`
object from the original four-field receipt plus index, and ordered
`signers`. Each signer pins `role`, `index`, `keyId`, `keyEpoch`, lowercase
`publicKey`, and `headerSha256`; the controller supplies its private seed
separately. It must check the intended HTTP and route against its retained
request before issuing approval.

```sh
mini agent-payer-sign --host HOST --config PINNED-CONFIG.json \
  --operator-socket /operator/private/host.sock \
  --reserve-attempt /operator/private/reserve-attempt \
  --plan /operator/private/paid-plan.bin \
  --approval /operator/private/payer-approval.json \
  --key /operator/private/dispatch-seed.bin \
  --dir /operator/private/payer-sign-attempt
```

The helper re-inspects the exact original reserve Plan and a retained
confirmed native outcome. The pinned Host authors the expected paid request
from that original request, context and receipt index; private op48 must
reproduce the supplied paid Plan byte-for-byte at the current image. Source
inspection must then show the same full HTTP, context, fixed selectors and
reserve index. Only after those checks does the client sign the ordered
`payerSlots` headers into `payer-signatures.json`. `appSlots` belong to the
resident and are never signed here. The helper neither assembles op49 nor
submits op46, and a historical reserve receipt alone grants no dispatch.

Selected public release uses a distinct Lean-authored canonical ingress and
the same native receiver, through Host operations 20 and 21:

```sh
mini selected-release-sign --host SOURCE-HOST --config SOURCE-CONFIG.json \
  --preimage PREIMAGE.bin --key OWNER.key --output SIGNATURE.bin
mini selected-release-submit --host HOST --config CONFIG.json \
  --socket /private/path/mini-session/host.sock \
  --ingress INGRESS.bin --dir /private/path/attempt-1
mini selected-release-lookup --attempt /private/path/attempt-1
```

Signing first asks the source-owned Host to strictly decode and re-encode the
bounded public release preimage. The client compares those bytes to the exact
input, requires an owner-private regular key file, and signs only those bytes
with its existing Ed25519 custody implementation. It writes a new private
64-byte signature file; no release codec is implemented in Rust. This command
uses direct Host validation and does not accept `--socket`.
Canonical public-release validation does not establish current source
publication authority; outbound publication has a separate admission gate.

The attempt directory is created private (`0700`). It retains exact
`ingress.bin`, config bytes, Host image and input digests, and a durable
per-request marker before transmission. Each response frame is retained
before the Host decodes its `Outcome`; a lost or mismatched response is
uncertain even if the receiver may have committed. Lookup sends the same
ingress to the source-owned historical replay path and never submits missing
work. Only a retained latest lookup with `type: "absent"` permits an explicit
`mini selected-release-retry --attempt /private/path/attempt-1`, which sends
the exact retained ingress once; it does not author a new nonce or release.
At retry, the pinned Host re-decodes the exact retained lookup binary; cached
JSON cannot authorize submission. The latest lookup's ingress digest and
selected socket must match the retry request.
After any resubmit, another absent lookup is required before a further
resubmit. A historical confirmed lookup reports the original native receipt.
An optional `--socket NEW-SOCKET` on lookup or retry selects a restarted
endpoint while retaining the Host image/config/ingress pins.

The existing file-oriented fn consumer Host/Main commands are exposed by a
restricted direct bridge, for example:

```sh
mini host-command --host HOST --config CONFIG.json \
  --command consumer-export-reply --arg TRANSACTION-ID --arg REPLY.bin
```

`--arg` order is preserved. Only the fn consumer command allowlist in the
client source is accepted; Rust invokes Host/Main directly without a shell or a
second implementation of those semantics. The typed B and A poll/ACK routes
below use the framed session; other allowlisted file-oriented fn commands still
use a separate direct host process.

For a service configured with the host's `fnPoll` pin, the typed consumer
path uses one socket for the entire poll, Mini submission, and fn ACK:

```sh
mini consumer-poll --host HOST --config FN-POLL-CONFIG.json \
  --socket /private/path/mini-session/host.sock --dir attempts/fn-poll-1
mini submit --host HOST --config FN-POLL-CONFIG.json \
  --socket /private/path/mini-session/host.sock \
  --intent attempts/fn-poll-1/intent.bin --intent-kind binary \
  --key CONSUMER.key --dir attempts/fn-submit-1
mini consumer-ack --host HOST --config FN-POLL-CONFIG.json \
  --socket /private/path/mini-session/host.sock \
  --mini-transaction MINI-TRANSACTION-ID --dir attempts/fn-ack-1
```

The operator config pins the fn control socket, origin, scope, and policy;
the caller supplies no fn paths or policy. Each consumer attempt directory is
private (`0700`). Poll retains `reply.frame` before decoding, `decision.json`,
and a Lean-authored `intent.bin` when the decision proposes a Mini operation.
An accepted historical repeat or recorded conflict has no new intent. Polling does
not ACK fn or submit to Mini. Submit retains its exact signed `call.bin` before
publication. ACK retains `transaction-id.txt`, `reply.frame`, and `ack.json`;
only `fnAck: "durable-accepted"` reports success. An exact repeat of the
current article or skip cursor has passed native validation without a new fn
Store event. A missing, uncertain, or transport-fault ACK reply permits one
automatic exact transaction retry with a durable one-shot marker; a second
uncertainty holds. A refusal, malformed reply, or older cursor coverage holds
for operator review. An older cursor can instead return `covered-by-durable-frontier`, which proves scoped
cursor coverage but not the exact old ACK event. The worker does not retry an
old covered cursor. Coverage is retained and reported distinctly from exact
durable acceptance.

An empty fn page can return `status: "idle"` with no intent, or
`status: "skip-decision"`. A fresh skip decision includes a Lean-authored
`intent.bin` to submit before acknowledging; a repeated skip decision has no
new intent. An accepted skip ACK identifies itself as `kind:
"empty-page-skip"` in `ack.json`.

The A reply consumer uses the same custody sequence with its own operator
`fnReplyPoll` config and separate socket. Replace `consumer-poll` and
`consumer-ack` above with `reply-consumer-poll` and `reply-consumer-ack`;
submit A's returned `intent.bin` through that A socket. The A poll and ACK
attempts retain the same filenames. A historical repeat can return an
accepted decision without a new intent; in that case no Mini submit is due.
The A service also uses the `idle` and `skip-decision` empty-page statuses
described above.

For an A service configured with operator-owned `fnReplyCatalog`, the bounded
R carrier is the only client-supplied op16 payload:

```sh
mini origin-outbox-prepare --host HOST --config FN-REPLY-CATALOG-CONFIG.json \
  --socket /private/path/a-session/host.sock --carrier R.eml \
  --dir attempts/a-outbox-r-1
```

The client retains `carrier.bin` and the complete `reply.frame` before
decoding `decision.json`. A `prepared-decision`/`proposed-fresh` response
also retains the Lean-authored `intent.bin` for ordinary signed Mini submit.
A repeated decision has no new intent. A refusal retains its full frame and
decision. No carrier path, claim, pin, or operator path crosses the public
socket; the broker admits op16 only for a service whose pinned config has
`fnReplyCatalog`, and Host/Main re-verifies the carrier against that catalog.

The `origin-publish` entry is prepared for a durable A-origin publication:

```sh
mini origin-publish --host HOST --config FN-REPLY-CATALOG-CONFIG.json \
  --socket /private/path/a-session/host.sock --key A-ORIGIN.key \
  --carrier SIGNED-R.eml --state-dir /private/path/a-publisher \
  --post-config /private/path/fn-post.json
```

Its owner-private post config specifies the operator's localhost NNTP
endpoint and credentials, for example:

```json
{"type":"minidregg-fn-post-v1","port":1119,
 "certificatePath":"/private/path/fn-cert.pem",
 "username":"a-at-b","passwordFile":"/private/path/fn-password"}
```

The publisher retains the exact already-signed carrier, asks Host op16 to
prepare A's Mini outbox decision, submits that Lean-authored intent using the
normal signed Mini route, and requires Host op18 to read back the accepted
carrier from A's durable history before fn POST. It sends those exact bytes
over authenticated STARTTLS, with NNTP dot-stuffing only for wire framing.
`240 article received OK` means accepted now; the exact already-stored `441`
means the same carrier was accepted earlier; a different-article `441` is a
Message-ID conflict. A lost reply or fn's explicit `do not repost` outcome
never authorizes a new carrier. The durable state permits at most one exact
reconciliation POST after a recorded transport uncertainty; missing response
evidence holds for operator review. The post config and signed carrier are
pinned for restart, and the password is never placed on an argument vector.

The [September 26 workroom publisher run](../../docs/evidence/2026-09-26-workroom-content-publisher/README.md)
exercised `origin-publish` for an actual hosted Hermes content edit. Host
op18 returned the exact accepted carrier, fn accepted one POST, both private
fn peers retained the article, and restarting the publisher did not repost.
This establishes that operator-driven fixture's custody and transport path;
it does not authorize an agent to release the origin Store's entire history.
See the [disclosure boundary](../../docs/FN-PUBLICATION-DISCLOSURE.md) before
using this full-prefix carrier for a workroom.

`mini origin-outbox-export --host HOST --config FN-REPLY-CATALOG-CONFIG.json
--socket SOCKET --mini-transaction ID --dir NEW-ATTEMPT` is the read-only
historical tag-10 readback. It retains `transaction-id.txt`, complete
`reply.frame`, typed `export.json`, and the exact decoded `carrier.bin` for an
accepted A outbox transaction. A typed refusal remains in the attempt and
exits nonzero. It never POSTs to fn or mutates Mini.

For a provider reserve already confirmed by Mini, the read-only continuity
route keeps the original call and canonical confirmed outcome as its inputs:

```sh
mini continuity --host HOST --config PROVIDER-CONFIG.json \
  --socket /private/path/provider-session/host.sock \
  --call RESERVE/call.bin --outcome RESERVE/outcome.bin \
  --dir /private/path/continuity-check-1
```

The attempt retains exact `call.bin`, `outcome.bin`, and `reply.frame` before
decoding `continuity.json`. Host op17 uses the operator-pinned provider
resource, refreshes the verifier-minted session, and returns a typed current
confirmation or refusal. A refusal is retained and exits nonzero. The client
does not renew a reserve, change the accepted journal, or create a new call.
This observation is not an atomic lease across a later external send; the
runtime must compare its anchor and provider identity with the retained
reserve and check fresh parent/provider state. This v1 route requires the
persistent `--socket`; no direct one-shot Host fallback is inferred.

`meter` asks the operator-pinned Host for a read-only quote over exact retained
provider request and response bytes:

```sh
mini meter --host HOST --config CONFIG.json --socket SOCKET \
  --metadata META.json --request REQUEST.bin --response RESPONSE.bin \
  --dir /private/path/new-meter-attempt
```

`META.json` contains exactly `status`, `contentType`, and `reserve` as strings;
the status and reserve use canonical decimal spelling. The client retains the
exact metadata, request, response, and full Host `reply.frame` in a new private
directory before decoding `meter.json` or a refusal. The source Host, using the
configured provider resource and tariff, checks the provider-reported usage
and returns a typed quote with its provenance limitation. The quote is not a
Mini settlement, provider invoice attestation, or permission to release a
held reservation. The controller must bind it to its own retained request,
response, and confirmed reserve before constructing a separate signed settle
call. This route requires the persistent `--socket`.

`consumer-drain-once` runs one bounded B consumer wake through that same
socket. It holds a single private, owner-locked durable state directory:

```sh
mini consumer-drain-once --host HOST --config FN-POLL-CONFIG.json \
  --socket /private/path/mini-session/host.sock --key CONSUMER.key \
  --state-dir /private/path/b-consumer-worker --max-pages 16
```

The worker polls using Host/Main, stores the exact Lean-authored intent, and
uses `submit --prepare-only true` to retain and sync a signed `call.bin` before
any Mini submission. It persists `Ready`, then `Sending` before `retry --mode
submit`. A restart in `Sending` runs exact `lookup` first. Confirmed lookup
uses the original receipt; definitive absence permits one resubmission of the
same retained bytes under Mini's replay and current-authority checks. An
uncertain lookup or resubmission holds the call for reconciliation. Once Mini confirms, the worker
persists its transaction ID and the confirmed receipt before fn ACK. A durable
accepted ACK frame can finish archival after a crash. A missing, uncertain, or
transport-fault reply allows one automatic retry of the same ACK transaction;
another unresolved result holds. A typed refusal, cursor coverage, or malformed
reply holds for operator review. None of these paths creates a new intent or
submits another Mini call. The operator must keep the same host, config bytes, socket,
and signing key; a changed pin refuses. The worker archives successful
attempts by Mini transaction ID and removes idle poll attempts.

After diagnosing a Held typed fn-session refusal and correcting the
operator-controlled fn bridge, an operator can run one bounded retry of the
same transaction:

```sh
mini consumer-resume-ack --host HOST --config FN-POLL-CONFIG.json \
  --socket /private/path/mini-session/host.sock --key CONSUMER.key \
  --state-dir /private/path/b-consumer-worker
```

This requires the worker's v2 Host-image pin, an anchored confirmed receipt,
and an existing Held publication or neutral-page skip with a complete typed
fn-session refusal frame. A missing reply, exhausted automatic retry, or other
failure remains Held for operator diagnosis. The command preserves the prior ACK frame, checks the retained
signed call and confirmed receipt, performs a read-only lookup under the pinned
Host, and compares all four receipt fields before marking the one-shot retry
durable and sending the exact typed fn ACK. If the reply is lost again, the
worker stays Held; re-running the command cannot send a second ACK after the
one-shot marker. A retained exact durable ACK can still finish archival. This
command does not repair fn state or infer success from a transport error.

One wake stops after a publication, a short neutral page, an idle poll, or
the `--max-pages` cap. The fn ACK itself appends a Store event, so repeatedly
polling until idle would generate a new skip and ACK without external work.
`consumer-drain-once` remains an operator-controlled bounded wake; the
`consumer-worker` command below provides the unattended GROUP scheduler.

For unattended B consumption, `consumer-worker` uses a private operator wake
config alongside the same Host config, key, socket, and state directory:

```json
{
  "type": "minidregg-b-consumer-wake-v1",
  "port": 11942,
  "certificatePath": "/private/path/fn-server.crt",
  "username": "consumer-observer",
  "passwordFile": "/private/path/fn-observer.password",
  "group": "fn.test",
  "intervalSeconds": 10,
  "maxPages": 16
}
```

Create that file with mode `0600` and invoke:

```sh
mini consumer-worker --host HOST --config FN-POLL-CONFIG.json \
  --socket /private/path/mini-session/host.sock --key CONSUMER.key \
  --state-dir /private/path/b-consumer-worker \
  --worker-config /private/path/b-consumer-wake.json
```

The worker connects only to `127.0.0.1:port`, requires STARTTLS, verifies
the exact operator-pinned certificate bytes and its `localhost` name and
validity period, verifies the TLS handshake signature, and authenticates with the
private password file, and reads the exact NNTP `GROUP` count/first/last for
the group pinned by the Host's `fnPoll` scope. The certificate identity,
endpoint, auth principal, and custody paths are pinned in the private state;
the password itself is never copied there or placed on the command line.
The GROUP tuple is only a wake hint. On a fresh state directory the worker
drains unconditionally; after restart it resumes any pending attempt and
otherwise uses the last durably remembered tuple. It continues bounded rounds after a publication or
full page, checks GROUP again after an idle or short page, and remembers the
tuple only when it stayed stable through that round. Its owner lock covers
the whole process and excludes another worker or one-shot drain on the same
socket. A stable GROUP tuple lets it sleep without turning fn ACK journal
events into further Mini skip submissions. A changed group may contain an
unrelated article; Host/Main still verifies each poll before any Mini write.
The current fn fixture presents one self-signed `CN=localhost` certificate
with `CA:TRUE` and no SAN; this exact-leaf pin mode is deliberately narrower
than general public-PKI validation. Operators must rotate the private worker
state and Host service pin deliberately when the fn certificate, scope, or
incarnation changes. The worker pins the complete fn scope digest and refuses
local config drift, but an unchanged GROUP tuple alone cannot prove a remote
Store incarnation; the next typed Mini poll performs the source-owned check.

An A service using operator-owned `fnReplyCatalog` can use the same durable
prepare, exact-call lookup, and typed ACK lifecycle with a separate state
directory and route pin. The catalog pins the origin configuration, R and Q
signer manifests, scope, policy, and the absolute fn control socket path. The
control socket is an endpoint, so the worker does not read or hash it as a
manifest. The five input manifests are bounded regular files. An A worker
never accepts an existing B pin or B pending state as A state (or the reverse).

```sh
mini reply-consumer-drain-once --host HOST --config A-CATALOG-CONFIG.json \
  --socket SOCKET --key REPLY-CONSUMER.key \
  --state-dir /private/path/a-reply-worker --max-pages 16

mini reply-consumer-worker --host HOST --config A-CATALOG-CONFIG.json \
  --socket SOCKET --key REPLY-CONSUMER.key \
  --state-dir /private/path/a-reply-worker \
  --worker-config /private/path/a-reply-wake.json
```

The A wake file has the same `port`, `certificatePath`, `username`,
`passwordFile`, `group`, `intervalSeconds`, and `maxPages` fields shown above,
with `"type":"minidregg-a-reply-consumer-wake-v1"`. Its group must match the
catalog's pinned scope query. A first wake polls unconditionally; later wakes
use the protected NNTP `GROUP` tuple as a scheduling hint and recheck it after
a short page or idle poll. ACK journal events alone do not change article
count. A short neutral-page scan or own-R progress decision submits the exact
Host-authored tag9 intent and ACKs its selected Mini transaction. An own-R
decision continues the bounded wake because Q can already follow that R at
an unchanged GROUP count; only a short empty-page scan proves the tip. A Q
decision uses the same durable sequence, then ends that drain pass after
publication; the worker continues draining within its wake budget.
Historical repeated decisions without a fresh intent hold for operator
reconciliation. An uncertain ACK gets at most one automatic exact retry;
cursor coverage or a typed refusal holds.

After correcting a typed fn-session refusal, the A counterpart to the B
recovery command is:

```sh
mini reply-consumer-resume-ack --host HOST --config A-CATALOG-CONFIG.json \
  --socket SOCKET --key REPLY-CONSUMER.key \
  --state-dir /private/path/a-reply-worker
```

It requires the A v2 image pin and the retained exact-call confirmed receipt,
then performs the same read-only four-field lookup and one-shot ACK recovery.
The B `consumer-host-upgrade` command does not upgrade A state; an A image
change with pending work currently requires operator review.

For an already confirmed call stranded in the worker's `Sending` phase,
`consumer-host-upgrade` changes the executable pin explicitly:

```sh
mini consumer-host-upgrade \
  --old-host OLD-HOST --old-sha256 OLD-SHA256 \
  --new-host NEW-HOST --new-sha256 NEW-SHA256 \
  --config FN-POLL-CONFIG.json --socket SOCKET --key CONSUMER.key \
  --state-dir PRIVATE-WORKER-STATE \
  --known-outcome CONFIRMED.bin --known-sha256 OUTCOME-SHA256
```

Stop the service and worker first. The command takes their locks, checks the
existing pin and exact retained call/config snapshot, and asks the new Host
for a read-only lookup. All four receipt fields must match the retained
confirmed outcome. It saves the previous pin and migration evidence before
atomically replacing the pin; it neither submits the call nor ACKs fn.
Restart the service with the explicit new Host path and run the worker with
that same path. Its own lookup must match the migration receipt before ACK;
absence or disagreement retains the pending attempt for review. The old
attempt manifest and signed call remain unchanged. This command is scoped
to confirmed pending calls, not general deployment or config migration.

New and upgraded worker pins also record the Host executable digest and the
referenced fn manifest digests. Their socket requests use envelope v2: the
service checks the expected executable digest and exact config before
forwarding a request, including lookup and ACK. Use the matching new `mini
serve`; an older service refuses v2, and the worker does not fall back to v1.
Existing v1 worker pins retain their original behavior. The service hashes
its configured executable before spawning it, relying on the owner keeping
that path stable through launch. This is a local deployment check, not remote
attestation against a malicious service owner.

To render a retained signed resource query as a bounded fn inbox summary,
run `mini query --host HOST --config CONFIG.json --socket SOCKET --intent
INTENT.json --key KEY --view resource --presentation fn-inbox-resource --dir
ATTEMPT`. It retains the exact signed `view.bin` and writes the typed summary
directly to `view.json`, without a raw `view-resource` presentation step. For
an existing `view.bin`,
run `mini inspect --host HOST --config CONFIG.json --socket SOCKET --kind
fn-inbox-resource --input ATTEMPT/view.bin --output ATTEMPT/inbox.json`.
This admits only the `fn-inbox-resource` kind, refuses to replace an existing
output, and does not make a new query or mutation. Keep the signed query and
raw `view.bin`; the JSON is a source-rendered presentation of those bytes.

## Portable native prefix evidence

`mini export-evidence --host HOST --config PINNED.json --call CALL.bin --output PACKAGE.bin`
reads a previously accepted exact call from the local native history. The Lean
host checks the original signed call with its historical lookup and exports
the exact first accepted prefix, original receipt, claimed domain, semantics
profile and genesis identity. Rust only invokes Lean. An absent call or later
event refuses; export does not publish an event.

`mini verify-evidence --host HOST --config INDEPENDENT-PIN.json --package
PACKAGE.bin --output RESULT.json` verifies without opening or writing a local
store. The verifier's config must independently select the peer domain,
profile parameters, genesis identity and native signature helper. The package
pin is only a claim to compare with that config. Lean calls
`NativeHostReplay.verifyBytes` to re-admit the retained original signed ingress
from the pinned genesis, compares the reconstructed original receipt, and
requires exact historical lookup of the supplied call in that accepted prefix.
Successful output identifies a verified historical Mini operation. It does not
authorize a new local action, prove an external side effect, or replace fn's
authorship and retention decisions.

`DREGG/FN/NATIVE-PREFIX/v2` is the current canonical codec in
`Compiler/FnEvidenceCodec.lean`. Its portable limits are 1,048,576 bytes for
the complete package, 262,144 for the signed call, and 786,432 for the
retained accepted prefix; the original receipt must have a positive accepted
count within that prefix. The verifier also decodes historical v1 evidence
under its original 17,408-byte package, 6,144-byte call, 12,288-byte prefix,
and exactly one accepted event bounds. The host caps input before decoding,
and the codec checks the decoded shape before native re-admission. The
package contains public authority history and must not be exported from a
private live store.

## Local E1 consumer experiment

The [bounded E1 consumer contract](../../docs/FN-CONSUMER-E1.md) uses the
native host's `consumer-decide-test` command to verify a public origin package,
select a stable application/operation binding, and write a canonical Mini
observation intent. For a proposed operation or conflict, sign and submit the
intent through the ordinary receiver:

```sh
mini submit --host HOST --config CONSUMER-CONFIG.json \
  --intent INTENT.bin --intent-kind binary --key CONSUMER.key --dir ATTEMPT
```

For a deterministic stale-prestate test, append `--prepare-only true` to
retain `ATTEMPT/call.bin` before publication, then use `mini retry --attempt
ATTEMPT --mode submit`. The proposed decision is not an accepted Mini receipt;
the final `outcome.json` and historical lookup settle that distinction.

Build it with:

```sh
CARGO_BUILD_JOBS=2 cargo build --manifest-path native/resource-client/Cargo.toml
```

Generate a fresh signer. The secret file is created with mode `0600` on Unix
and existing files are never replaced:

```sh
mini keygen --secret alice.key --public alice.pub
```

The command prints the raw public key as lowercase hex for a source-authored
genesis enrollment. Bootstrap retains the exact source, canonical source
binary, genesis image, pinned config, profile, and post-bootstrap description:

```sh
mini bootstrap \
  --host .lake/build/bin/minidregg-host \
  --config operator.json \
  --source genesis.json \
  --dir deployment
```

`submit` accepts a source-owned observation intent whose purpose is `prepare`.
Its attempt directory contains the observation challenge, signatures, signed
observation, finalized signing plan, transaction signatures, exact signed call,
a retained pinned config, and decoded outcome:

```sh
mini submit --host .lake/build/bin/minidregg-host \
  --config deployment/pinned-config.json \
  --intent birth-intent.json --intent-kind birth-intent \
  --key alice.key --dir attempts/birth-1
```

For a standard birth, pass `--intent-kind birth-intent`. The Lean builder takes
the exact genesis source and native factory template, derives absent cell roots,
neutral declared/content cells, root owner and policy-control grants, policy
addresses, transaction identity, authority nullifier, and the quoted fee. A
resource entry chooses `"storage":"declared"` or `"storage":"content"`; content
birth is an empty canonical content page. Rust never calculates these fields.

Ordinary transaction intents use `purpose.draft.type = "invoke"`. Its command
has one shared `subject`, `expectedAuthorityRoot`, and `nonce`, plus a nonempty
`targets` array. Each target has `kind`, `target`, mutation `capability`,
nullable `observeCapability`, `schemaVersion`, `expectedTargetRoot`, and a
tagged payload:

```json
{
  "type": "content",
  "actions": [
    {"type": "createAtom", "atom": "7001", "kind": {"type": "text"}, "payload": "68656c6c6f"}
  ]
}
```

The sibling payload type `scalar` carries the existing create/write/move
actions. One command may mix scalar and content targets; Lean constructs the
single flat transaction and requires distinct physical target IDs. Every
target of a command with more than one target must name an actual current read
grant in `observeCapability`. The host obtains and checks those read signatures
again at submission before any resource policy can inspect another target. A
singleton uses `null` because it has no foreign participant to observe.

After a lost or uncertain response, this command reuses `call.bin` byte for
byte. Each response gets a new evidence filename and earlier evidence is kept:

```sh
mini retry --attempt attempts/birth-1 --mode submit
mini retry --attempt attempts/birth-1 --mode lookup
```

Authorized inspection follows the same challenge/sign/query path:

```sh
mini query --host .lake/build/bin/minidregg-host \
  --config deployment/pinned-config.json \
  --intent inspect-resource.json --key alice.key --view resource \
  --dir attempts/query-1
```

The implemented `mini author --kind` values are `predicate`, `grain-caveat`,
`policy`, `policy-install`, `policy-install-draft`, `delegation`,
`delegation-draft`, `revocation`, `revocation-draft`, `birth`, `birth-intent`,
`content`, `resource`, `joint`, `joint-draft`, `grain`, `draft`, `intent`, and
`genesis`. Rust passes each JSON source to Lean unchanged:

```sh
mini author --host .lake/build/bin/minidregg-host \
  --config deployment/pinned-config.json \
  --kind content --input content-operation.json --output content-operation.bin
```

The `*-draft` kinds return canonical `NativeHostCodec.Draft` bytes. They are
useful for inspecting or integrating with another transport; normal `submit`
accepts an `intent` JSON that embeds the corresponding friendly source form.
The friendly `purpose.draft` constructors are:

| `type` | Source fields |
| --- | --- |
| `invoke` | `command` with shared subject/root/nonce and typed targets |
| `install-source` | `subject`, `control`, and a policy `declaration` |
| `delegate-source` | source-owned delegation `command` |
| `revoke-source` | source-owned revocation `command` |

A policy declaration supplies `expectedPreRoot`, nullable current `expected`
head, `nonce`, and a full policy record. Delegation supplies `kind`, `domain`,
`semantics`, `subject`, `nonce`, `expectedTargetRoot`, the complete child
capability, `parentId`, `target`, and `expectedPreRoot`; Lean derives its
operation marker. Revocation supplies the actual target `kind`, `subject`,
`nonce`, `target`, `victimKind`, victim `capability`, `controlCapability`, and
both expected roots. Program control grants use distinct `installPolicy` and
`revokeCapability` verbs.

Content payload actions are `createDocument`, `createAtom`, `createRun`,
`editAtom`, and `link`. Byte payloads are lowercase or uppercase even-length
hex; identifiers and unbounded integers are canonical decimal strings. Atom
edits carry the complete observed old record, so the source receiver can reject
a stale replacement without trusting a Rust-side reconstruction.

The bounded local acceptance journey creates a new signer and deployment,
births content and declared objects, submits a typed singleton content mutation
with a deliberately lost outcome, recovers it from exact retained call bytes,
then submits a mixed content/scalar joint transaction with current read grants.
Authorized queries check both final states, and exact retries check receipt
identity. It requires `jq` plus the already-built native storage and signature
helpers, and refuses to reuse its evidence directory:

```sh
native/resource-client/acceptance.sh .lake/build/bin/minidregg-host /tmp/mini-acceptance
```

The directory retains the generated `birth-intent.json`, `content-intent.json`,
`joint-intent.json`, query sources, canonical binary artifacts, signatures,
receipts, and `acceptance.json`. These are concrete examples for the local
client. The Unix socket is local only; no network server or SSH interface is
provided yet.

The separate authority journey uses two fresh enrolled signers and the same
ordinary `mini` JSON interface. Alice installs a source-authored policy,
delegates a narrower observe/mutate grant to Bob, and later revokes it. Bob's
write is confirmed under his own key; policy and grant refusals are checked
against the current world root, and his retained call replays its original
receipt after revocation without a new event. Both the initial and installed
policy records are reconstructed from authorized `view-policy` JSON and
reauthored to the exact same canonical bytes:

```sh
native/resource-client/authority-acceptance.sh .lake/build/bin/minidregg-host /tmp/mini-authority-acceptance
```
