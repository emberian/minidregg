# Selected public Mini content over fn

`mini selected-exchange` is the reusable client for one explicitly chosen Mini
content atom. Its `prepare` phase checks a current signed Mini resource view and
compares the selected atom with the caller's exact payload file. The pinned Lean
Host then authors the owner-signed public release and event14 source ingress.
`publish` admits event14 before posting the exact article to fn. `receive`
projects that article through the Host and submits event13 to an independently
authorized recipient Mini. Coverage event17 precedes fn cursor ACK. `verify`
requires a fresh signed recipient read showing the exact accepted packet.
Current fn NNTP POST stores a legacy `fn-r` article. For that route,
`receive-transport` makes an authenticated local consumer poll, has fn's ACL2
`consumer-article` decoder extract the exact stored article and Message-ID,
checks the stored article carries the complete selected source, then asks Mini
to admit event13 under its own current law. `verify-transport` makes the fresh
signed recipient read. This path records **transport only**: `fn-r` carries no
historical fn authorship verdict and neither phase claims event17 or fn ACK.
The stronger `receive`/`cover-plan`/`cover-advance`/`ack`/`verify` path remains
for a schema-1 `fn-e` accepted-article event; it refuses `fn-r`.

The command replaces the GitWeb-specific authority and phase join in
`scripts/fn-gitweb-preview/join.sh` for new selected content versions. GitWeb
may still create content and supply provenance, but the authority input here is
the Mini content atom and signed current read. The old script remains a dated
fixture. This profile is **public-peerable-v2**; there is no recipient-only
encryption or private-history export. Fn acceptance and ACK are transport and
progress facts, not Mini admission or app installation.

The private contract is a JSON object with `type` equal to
`minidregg-selected-exchange-v1` and `releaseProfile` equal to
`public-peerable-v2`. All paths are absolute. It contains:

| Field | Meaning |
| --- | --- |
| `host`, `sourceConfig`, `recipientConfig` | Source-matched Host and the two pinned Mini deployments. |
| `sourceSignedQuery`, `sourceAtom`, `selectedPayload`, `selectedPayloadSha256` | Exact signed current source observation, chosen content atom, complete atom payload bytes and SHA-256. |
| `ownerKey`, `sourceDelegateCapability` | Owner signing key and current source publication capability. |
| `destinationDomain`, `destinationSemantics`, `destinationTarget`, `group`, `messageId`, `policyRoot`, `keysetRoot`, `epoch`, `ownerSubject`, `ownerNonce`, `expiresAt`, `from`, `date`, `subject` | Exact public release request passed to Lean. The group is a routing label, not an access control list. |
| `privatePostConfig`, `fnBinary`, `fnRuntimeImage`, `fnScope`, `fnControl` | Protected fn POST custody and explicit fn consumer launcher, underlying executable/core image, scope and socket. Use a separately initialized test fn Store for experiments. |
| `recipientCapability`, `recipientAuthorityRoot`, `recipientTargetRoot`, `recipientSocket`, `recipientOperatorSocket`, `gatewayKey` | Recipient current admission and event17 coverage inputs. Roots must come from a fresh authorized recipient read. |
| `recipientQueryIntent`, `recipientQueryKey` | Separately authorized signed read of the exact recipient content resource after admission. |

Every numeric field is a canonical decimal string. The contract and source,
recipient, key, fn launcher/runtime image/scope and payload files, plus the
running Mini client image, are hashed into private state;
later phases refuse changes. The state path must be new for `prepare` and mode
0700. The Host image and client binary should be source-matched and pinned for
the run. A partial preparation is retained for inspection; start a new attempt
with a new state directory after correcting a refusal. All subsequent phases
reuse that state:

```sh
mini selected-exchange --phase prepare --contract /private/release.json --state-dir /private/exchange
mini selected-exchange --phase publish --contract /private/release.json --state-dir /private/exchange
mini selected-exchange --phase receive --contract /private/release.json --state-dir /private/exchange
mini selected-exchange --phase cover-plan --contract /private/release.json --state-dir /private/exchange
mini selected-exchange --phase cover-advance --contract /private/release.json --state-dir /private/exchange --approval /private/exact-frontier-approval.json
mini selected-exchange --phase ack --contract /private/release.json --state-dir /private/exchange
mini selected-exchange --phase verify --contract /private/release.json --state-dir /private/exchange
# For an NNTP-posted fn-r article, after prepare and publish:
mini selected-exchange --phase receive-transport --contract /private/release.json --state-dir /private/exchange
mini selected-exchange --phase verify-transport --contract /private/release.json --state-dir /private/exchange
```

Each phase holds a nonblocking owner-private lock over the exchange state, so
concurrent phase commands refuse. An interrupted preparation retains its files
without submitting to Mini or fn. `--phase status` checks the same pinned inputs
and reports which local evidence exists; it does not infer admission. If
`preparationComplete` is absent or false, keep that state for inspection and
start a new preparation in a new directory. No later phase can consume the
incomplete attempt.

`publish` uses the existing selected publisher's durable marker and never
blindly reposts after an uncertain fn response. Once a recipient attempt
directory exists, `receive` performs only exact op21 lookup; it does not create
a second event13. An absent or uncertain latest lookup prevents coverage and
ACK. Event17 uses the existing operator-private frontier plan and exact approval.
The fn ACK checks that event13 and event17 are admitted, and a subsequent signed
read checks the installed packet. Installing or executing an application version
from that packet requires a separate receiving authority and operation.
The `fn-r` transport path retains its raw cursor, report, stored article and
Host result. It never calls fn ACK. A retry after an event13 attempt uses only
exact op21 lookup. Its signed recipient read proves the selected packet was
installed; a fn `240` response or retrieved article alone does not.
