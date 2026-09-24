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
