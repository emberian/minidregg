# Isolated two-Store E1/E2 exchange

This is the finite synthetic A→B→A trace selected in fn
`planning/experiments/e1-e2-agent-exchange.md` and `specs/consumer-progress.md`.
It composes native fn protected peering and local-owner consumer with Mini's
observed poll transaction and durable reply publication. It does not assert
general remote consumer semantics, BP transit, power-loss durability, or
exactly-once external side effects.

The fn owner fixture runs only on a fresh hbox gate scratch directory. It
initializes two independent fn Stores with separate control sockets, TLS
certificates and administration credentials; configures reciprocal pinned
STARTTLS+AUTHINFO peers; signs R's existing exact synthetic source with a new
A author keyset through native `hybrid-sign`/`hybrid-author`; enrolls A's
public keyset on B; observes B's protected peer receipt, exact source and
historical native verdict; and registers B's local consumer `worker`. Each
keyring snapshot contains one principal/keyset. B accepts R under generation
1 before A and B enroll Q's distinct author keyset at generation 2. B's
preview poll follows those enrollments, so Mini's later live poll sees the
same committed frontier. The fixture
atomically publishes `ready.json` and holds for Mini. These are isolated test
credentials, not the deployed node's keys.

The ready object has version 1; `image`, `a_control`, `b_control`, `a_port`,
`b_port`, `consumer_b`, `r_message_id`, `r_source`, `r_carrier_b`,
`r_principal`, `r_ed_public`, `r_ml_public`, `r_ml_public_raw`,
`b_registered_cursor`, `b_preview_cursor`, `b_preview_report`,
`q_principal`, `q_ed_public`, `q_ed_secret`, `q_ml_public`,
`q_ml_public_raw`, `q_ml_private`, `q_generation`, `b_login`,
`b_password_file` and `b_tls_cert`. Paths name files on hbox. Mini copies
only public inputs; private key paths remain there and are passed to native
signing in that test process. `protected_article.py` reads the observer
password file on hbox and sends it only over the pinned TLS session.

Mini's driver:

1. Verifies B's R carrier with fn native `hybrid-verify-source`, checks exact
   R source/keyset/identity, and uses ACL2 `consumer-project` to build a
   temporally registered scope pin. It then invokes `consumer-poll-decide`
   against B's live control socket and commits a new Mini operation with the
   ordinary signed native `mini submit`. A new Mini deployment with only its
   birth event is required. Its reopened event retains the exact cursor,
   report, carrier, provenance, operation index and immutable Q.
2. Calls Mini's `consumer-ack-poll` after that transaction. The bridge lets
   fn commit the *advancing* ACK, then deliberately loses its response. Mini
   must return `transport-fault`, and the driver reads native `consumer
   position` and compares the exact cursor before idempotently repeating the
   ACK. Neither a socket write nor the simulated loss is called accepted.
3. Reopens the accepted Mini transaction, installs absent-only prepared and
   signed SQLite slots for Q, and reopens the signed slot from a separate
   process with nonexistent signing keys. Fn native signs and verifies the
   exact source; the driver requires identical source, detached signatures,
   Message-ID, source identity and signed-slot readback on retry.
4. Sends the durable tuple to native B `hybrid-author`. The bridge loses its
   accepted response, then a separate protected NNTP ARTICLE lookup and fn
   native `hybrid-verify-source` establish exact presence, keyset and source
   identity before any retry. A definitive absence would require a separate
   same-tuple retry; the accepted trace never re-signs or invents a new ID.
5. Publishes `posted.source`, `posted.reply.bin` and atomic
   `mini-finished.json` only after that
   readback. The fn fixture then cold-reopens its Stores, observes protected
   B→A delivery, verifies the reopened carrier and historical verdict, and
   polls Q with A's original consumer. A's Q cursor stays unacknowledged:
   this fixture has no durable A-side Mini application result transaction.
   Its final consumer observation is a read and verification, not a claim
   that A completed application work.
   It atomically publishes `owner-finished.json` and retains A's carrier,
   native verified source/verifier tuple and poll cursor/event. Mini's driver
   independently calls the native verifier and `consumer-project` on A's
   artifacts, then runs `check_a_reply.lean` against its durable prepared
   and signed slots, canonical Q, R source/identity and A's verified source.

The A-side Mini reply consumer is implemented separately in
`Kernel/FnReplySource.lean`, `Kernel/FnReplyConsumption.lean` and
`Host/Main.lean`. `reply-consumer-poll-decide` independently re-admits R's
Mini origin package, calls A's actual local `consumer poll`, projects its
native historical verdict, verifies Q's exact carrier with fn native
`hybrid-verify-source`, and checks Q's application, operation, R source
identity, parent Message-ID and original Mini receipt. One atomic local
transaction creates the result and exact Q/poll inbox under an operation
marker independent of Q's source identity. A changed Q for that operation
records conflict evidence instead of creating a second result.
`reply-consumer-export-result` reopens the accepted event before exporting
the result and inbox. `reply-consumer-ack-poll` requires that reopened result
and exact native cursor/report before fn ACK. A lost ACK response must be
settled against native `consumer position`; the local result does not assert
exactly-once external execution.

The future fn owner must atomically publish `a-ready.json` after Q reaches
reopened A, with live A control, A's registered consumer scope and Q key pin,
then hold until Mini writes `a-mini-finished.json` after its accepted result
and ACK. The staged e160 owner currently polls A itself and exits. The A
Mini source has a pure negative test against the exact earlier B3 Q, but no
composed A runtime claim. Both B and A native polls require the receiver-side
kind-4 historical verdict missing from e160. A's Mini deployment must use
its own fresh configuration and admin/custody identity, separate from B.

The result distinguishes exact authored source from Path/Xref and other
mutable native projections. `mini-finished.json` reports an accepted B post
only after lookup settlement. The current driver does not yet invoke the new
A Mini result path; its final A observation remains a bounded native
read/verifier witness. A later qualified fn image and second live handoff
are needed for that composed trace.

The exact Mini executable for the first composed run is the clean B3
functional baseline built from source `1eb84a9a46e08aa423a99e39ad74a9be538b5385`,
SHA-256 `11f451f7c14d55efcb16ee16f99bfffc20f551a7ebf173d5090966e1434f68f9`.
The later policy-projection candidate `568bbbea...` has not repeated the
native B3 sign/post path and is excluded from this run. The qualified e160
production image passed reciprocal protected peering but its B peer ingress
produced only a raw `fn-r` poll record and no historical verified verdict;
it cannot complete this composed trace. A later qualified image must make
the B poll return a bound kind-4 composite with an acceptance-time verdict.
The driver requires that image's exact path and launcher/core hashes.
`fn_bridge.sh` transports commands and opaque files, not an independent
consumer, signing or Store model.

Once that native feature has a source-matched qualified image and the fn
owner fixture is launched separately at its atomic handoff, invoke on the
Mini host after filling in the image/gate placeholders:

```sh
FN_E1E2_HANDOFF=/tank/fn/gates/<qualified-fn-gate>/build/mini-e1e2-two-store-1 \
FN_E1E2_EXPECTED_FN_IMAGE=/tank/fn/gates/<qualified-fn-gate>/build/fn-host \
FN_E1E2_EXPECTED_FN_LAUNCHER_SHA256=<64-hex-launcher-sha256> \
FN_E1E2_EXPECTED_FN_CORE_SHA256=<64-hex-core-sha256> \
FN_E1E2_OUTPUT=/tmp/mini-fn-e1e2-two-store-20260924/run-1 \
FN_E1E2_MINI_HOST=/tmp/mini-b3-build-1eb84a9/build/minidregg-host-b3 \
FN_E1E2_MINI_CONFIG=/tmp/mini-fn-e1e2-two-store-20260924/mini-config.json \
FN_E1E2_MINI_CLIENT=/Users/ember/dev/minidregg-wt/fn-evidence/native/resource-client/target/debug/mini \
FN_E1E2_ORIGIN_PIN=/tmp/mini-fn-e2-native-20260923/fn/origin-pin.json \
FN_E1E2_CLAIM=/Users/ember/dev/fn/build/lanes/mini-p2-portable/tests/fixtures/dregg-e1/portable-p2/source-claim.json \
FN_E1E2_POLICY=/tmp/mini-fn-e2-native-20260923/policy.json \
FN_E1E2_CUSTODY_KEY=/tmp/mini-fn-portable-inbox-native-20260923/consumer.key \
python3 scripts/fn-e1e2/mini_driver.py
```

Before that run, `mini-config.json` must select a fresh storage root with
the pinned original deployment fields. Run the source-matched host's
`bootstrap GENESIS.bin`, then submit the retained `live-birth-attempt/intent.json`
with `mini submit --intent-kind birth-intent`; require `confirmed` with
`acceptedCount=1`. Do not clone an already processed Mini R/Q operation into
the experiment. The first run's isolated root and confirmed birth evidence
are retained at `/tmp/mini-fn-e1e2-two-store-20260924/`.

The exact first-run preparation was:

```sh
python3 - <<'PY'
import json
from pathlib import Path
root = Path('/tmp/mini-fn-e1e2-two-store-20260924')
root.mkdir(exist_ok=False)
source = Path('/tmp/mini-fn-e2-native-20260923/live-deployment/pinned-config.json')
config = json.loads(source.read_text())
config['storageRoot'] = str(root / 'mini-store')
(root / 'mini-config.json').write_text(json.dumps(config, sort_keys=True, indent=2) + '\n')
PY
/tmp/mini-b3-build-1eb84a9/build/minidregg-host-b3 \
  /tmp/mini-fn-e1e2-two-store-20260924/mini-config.json bootstrap \
  /tmp/mini-fn-e2-native-20260923/live-deployment/genesis.bin
/Users/ember/dev/minidregg-wt/fn-evidence/native/resource-client/target/debug/mini \
  submit --host /tmp/mini-b3-build-1eb84a9/build/minidregg-host-b3 \
  --config /tmp/mini-fn-e1e2-two-store-20260924/mini-config.json \
  --intent /tmp/mini-fn-e2-native-20260923/live-birth-attempt/intent.json \
  --intent-kind birth-intent \
  --key /tmp/mini-fn-portable-inbox-native-20260923/consumer.key \
  --dir /tmp/mini-fn-e1e2-two-store-20260924/birth-attempt-2
```

The first failed birth invocation omitted `--intent-kind birth-intent` and
was rejected before submission (`missing field purpose`). It left no accepted
event. The corrected attempt reported `confirmed`, `acceptedCount=1` and
transaction ID
`30574338302698088804635708227956052706316029374670952451210790093397252577964`.

## Fresh setup on current source (2026-09-26)

The historical paths above describe the 2026-09-24 preparation and are not
required inputs. `setup-mini.sh` creates a new private Mini deployment through
the native custody client and Lean host: two independently generated enrolled
keys (gateway subject 7 and ordinary subject 8 by default), a canonical genesis, one
confirmed content-resource birth at target 600 and one confirmed cap-63
delegation to the ordinary signer, a source-only origin pin for
the retained public R fixture, and the local `mini-e1` policy. It queries the
actual accepted policy source and writes a separate `gateway-config.json`
with the operator's `fnGateway` address/subject/target/capability pin; the
bootstrap-pinned config remains intact. The content
resource's birth predicate permits mutation only by the configured gateway
subject. The ordinary signer has a current target-600 mutation capability but
the resource law denies that signer.
Run this twice with distinct output directories and subject IDs to obtain
separate A and B Mini identities. Keep both directories private; they contain
custody keys. The ordinary signer can be used for the refusal probe.

```sh
MINI=/absolute/path/to/mini \
STORE_BINARY=/absolute/path/to/minidregg-link-sqlite-store \
SIGNATURE_BINARY=/absolute/path/to/minidregg-credential-signature-verifier \
FN_FIXTURES=/Users/ember/dev/fn/tests/fixtures/dregg-e1 \
scripts/fn-e1e2/setup-mini.sh /absolute/path/to/minidregg-host /private/scratch/mini-b
GATEWAY_SUBJECT=17 ORDINARY_SUBJECT=18 \
MINI=/absolute/path/to/mini \
scripts/fn-e1e2/setup-mini.sh /absolute/path/to/minidregg-host /private/scratch/mini-a
```

The script refuses an existing output directory and requires the birth
outcome to be `confirmed` and `installed` with `acceptedCount=1`. It does not
copy a prior Store or custody key. The local delegation is a second accepted
event; the fn two-Store harness replays only genesis and birth into fresh A/B
Stores, so its gateway resource starts at accepted count 1. Run
`check-ordinary-refusal.sh HOST SETUP_DIRECTORY` to verify the ordinary key's
direct cap-63 mutation is refused at observation with unchanged Store height
and target root. That CLI refusal does not itself establish the receiver's
signed-call policy rejection; the source-owned
`probe_gateway_direct_submit.sh SETUP_DIRECTORY` prepares and signs an exact
call against the scratch Store and requires receiver `policyRejected` with no
journal growth. Run it with a source-matched current host build after setup.
On the fresh subject-7/ordinary-8 fixture, that source-owned probe passed:
the signed ordinary subject-8 call used its valid cap 63, the native receiver
returned `policyRejected`, and accepted history stayed unchanged. The public
CLI probe separately refused at observation. The private probe log SHA-256 is
`bf6391ba46450533ef7a2e25dc000f1130604fec8f50f54611e3ac7e38b1be66`.
Its `origin-pin.json` refers to the
independently selected historical Mini source within R; it does not give R
authority over the new consumer deployment. The `policy.json` binds the
gateway's local subject (7 or 17 above), content target 600 and capability 61. Fn still
owns the historical article verdict, consumer cursor and acknowledgement.

Fn's completed `planning/evidence/two-store-join-1a9dd747-2026-09-24.md`
used its qualified `1a9dd747` image pair and the matching Mini `183cd37`
binary. Its five runs completed the protected R→B and Q→A exchange, including
the B and A Mini transactions and ACKs. The older e160 refusal and the
preparation status above remain historical observations. The fn harness at
`tools/runbooks/two_store_join.py` accepts one Mini config/genesis/birth/key
set and copies that identity into separate A and B Stores. Until it accepts
per-side inputs, a rerun with the fresh setup proves fresh custody and Store
state but does not prove independent Mini A/B administrator identities.

A first fresh-input rerun on 2026-09-26 with the exact `183cd37` Mini binary
and qualified fn `1a9dd747` pair reached B's protected accepted R, retained
receiver verdict after restart, and Mini `consumer-poll-decide` returning
`proposed-fresh`. Mini then refused `submit` during observation preparation
before any Mini consumer transaction. The encoded invocation was 102,872 bytes,
above that first deployment's `ownerBudget=100000`; the Lean observation
controller charges encoded intent length as grant cost. A separate authorized
query of target 600 succeeded because its cost was smaller. The setup now
selects `ownerBudget=300000` before bootstrap and birth, preserving the normal
grant check. This is an operator-selected capacity for the measured workload,
not a change to an already pinned deployment. With that bound, the same
fresh-input run accepted B's Mini transaction/export/ACK, Q publication and
Q→A signed peering. A's Mini reply decision then refused before transaction:
`Q source has invalid Message-ID fields`. The emitted Q Message-ID contained
68 hexadecimal digest characters while `FnReplySource.parse` in the pinned
Mini `183cd37` image accepts exactly 66. `FnReplyPublication.messageId`
encodes a digest with the variable-length `digestStream` Nat codec, so fresh
identities can expose this mismatch. The accepted B transaction and fn Q
transfer remain evidence; the run did not complete A's Mini result or ACK.

For independent A/B identities, `run-distinct-mini.sh` checks the original fn
test harness SHA-256, copies it into a private sibling of `LOCAL_OUT`, applies
`two_store_join_per_side.patch`, and passes each deployment's config, genesis,
birth intent, custody key and policy separately. It does not edit fn's shared
checkout or change the qualified fn executable pair. The patch changes only
the existing test harness's inputs. The source harness is pinned to SHA-256
`c88160cf459d3959928f6ae913f455ed9ff49971b89619518ab7b49c884c99e6`;
the adapted copy currently hashes to
`fa595de896891cf362c8f8af3a8000d6ab8298d59837f0c8634b6807faaf2015`.
Set `MINI_SHA256` to the exact rebuilt Mini
host hash when testing a source fix; absent that variable the wrapper pins the
older `183cd37` image.

```sh
scripts/fn-e1e2/run-distinct-mini.sh \
  /tank/fn/gates/qual-1a9dd747-20260924/build \
  /absolute/path/to/minidregg-host /absolute/path/to/mini \
  /Users/ember/dev/minidregg /private/scratch/mini-b /private/scratch/mini-a \
  /tank/fn/scratch/unique-run /private/scratch/unique-output
```

The first distinct A/B run on 2026-09-26 used gateway subjects 7 and 17 and
completed all 77 harness steps, both accepted Mini consumer transactions,
both fn ACKs and final two-article counts. Its summary SHA-256 is
`5425858da0674fb0ace6c759a997bd9985af5b922a74877d09c5d264c5f318a6`
under private `/tmp/mini-fn-setup-probe-parent/distinct-run-1/summary.json`.
Its first generated Q ID had the parser's accepted 66 hex digits; the
independent prior 68-digit refusal remains a source defect. The harness
reported `EXCHANGE COMPLETE`. An edit to the shell wrapper during the
long-running child caused a later outer-shell EOF error; the current wrapper
passes `sh -n`, and the retained harness summary and 77 step logs provide the
exchange verdict.

Set `FN_REVOKE_GATEWAY_BEFORE_B_ACK=1` for an opt-in historical recovery
check. The wrapper applies the separate `two_store_join_revoke_hook.patch` to
its private harness copy. After B's accepted consumer event and exact export,
the hook queries current roots, submits a native `revoke-source` for B gateway
mutation cap 61, requires a third accepted Mini event, then re-exports the
original B transaction's exact cursor/event before the normal fn B ACK. The
2026-09-26 native hook run completed all 80 harness steps on the old pinned
Mini image: B consumer accepted count 2, gateway cap-61 revocation confirmed
at accepted count 3, historical re-export returned the exact pre-revocation
cursor and event, and B's fn ACK was durable-accepted. A's result/ACK and
final article counts also passed. Its private summary is
`/tmp/mini-fn-setup-probe-parent/revoke-run-1/summary.json`, SHA-256
`278a6ae4dc40df4c3f86fcbc66c800e60863ca02768839ada25b727c9dc6cf2d`.
The hook leaves the baseline per-side patch and fn's shared harness intact.

All new harness modes also apply `two_store_join_creation_context.patch`.
Current Mini reply-plan authoring requires the operator's explicit Q creation
fields. This test profile fixes From `mini-e2@example.invalid`, newsgroup
`fn.test`, Message-ID domain `example.invalid`, and Date
`Wed, 23 Sep 2026 12:00:00 +0000` in the signer JSON before source planning.
That matches the historical synthetic Q profile while making the selection
explicit and source-bound for the current host. This adapter has passed patch
application and Python syntax checks; native validation awaits the new host.

Set `FN_PUBLIC_B_SESSION=1` for the separate public B transport trial. The
wrapper applies `two_store_join_socket_b.patch` to its private harness copy.
After the B fn pin and scope exist, it starts one `mini serve` process on a
private Unix socket with operator-fixed `fnPoll` origin, fn pin, scope, policy
and control paths. B then calls typed `mini consumer-poll` (op 12), signs and
submits the returned binary intent through that same socket, and calls typed
`mini consumer-ack` (op 13) with only the accepted Mini transaction ID. The
accepted export must match B's preview cursor, and fn position must match the
export after ACK. In B-only socket mode, A's Q reply decision and ACK still
use the existing native CLI; the full A socket mode is described below. The
public B overlay supports `--cut none` only and cannot be combined with the revoke
overlay. It is staged for the source-matched final host/client build; patch
application, Python syntax and CLI flag parsing passed, but no native public
B run is claimed yet.

Set `FN_PUBLIC_B_SESSION=1 FN_PUBLIC_A_SESSION=1` for the full public socket
trial. A second, separate `mini serve` process is started after A's R carrier,
R/Q pins, Q claim and scope are fixed in the operator `fnReplyPoll` manifest.
The A overlay calls typed `mini reply-consumer-poll` (op 14), signs and submits
its proposed intent on the A socket, and calls typed
`mini reply-consumer-ack` (op 15) with only the accepted A Mini transaction
ID. Both sockets are terminated by harness cleanup. The A overlay requires
the B overlay and `--cut none`. Its patch chain applies to the pinned fn
harness and Python compilation passes; it awaits a source-matched linked Mini
host for a native exchange. The frozen combined client is
`/tmp/minidregg-overnight-20260926/mini-client-ba-311ab01`, SHA-256
`0523c8d2a340da315c926b1c73d25f0bb6d5be647d3492841bfc2c589fff6014`.
