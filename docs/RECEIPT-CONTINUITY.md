# Client receipt continuity

A participant can retain an authenticated world head and refuse a server history
that fails to extend it. This complements the Store's operator-local head anchor.
Neither file can detect rollback when the attacker also rolls back every copy of
that file. Independent witnesses remain a separate layer.

## What is checked

Existing transaction receipt codecs are unchanged. Host operation 151 supplies a
hash-only extension between known `(acceptedCount, worldRoot)` endpoints:

- Identity pins domain, semantic profile, expected genesis seed and protocol
  `minidregg-continuity-v1`.
- Both endpoint log-chain values have system-slot membership openings under the
  exact named world roots. Each opening has 256 siblings.
- The ordered suffix contains the canonical accepted-record digests. Folding
  `WorldRoot.chainDigest` from the old chain must equal the new chain, and the
  digest count must exactly match the accepted-count difference.
- Equal heights require equal roots. Lower ordinary read heads are refused.
- Responses paginate after at most 4096 record digests. Every acknowledged hop
  has its own verified endpoint; partial failure cannot bless the final answer.

`Kernel.ReceiptContinuity.opens_sound` uses the authenticated-map path-binding
carrier: hashes must separate the compared inputs. Under that cryptographic
assumption, the verified system opening is the world's actual committed system
slot. This proves commitment continuity, not independent execution of every new
record or global agreement among disconnected clients. The initial endpoint is
explicitly trusted through the authenticated service connection.

There is no circular world-root hash. An accepted record commits its transaction,
cell writes, guards, nullifiers, charge, event and subject, not its resulting
world root. Its digest extends the log chain; `(height, chain)` becomes the system
leaf of that resulting world root.

Observation challenges use absolute admission height (`genesisHeight` plus
accepted count). The local source-owned `continuity-point` command checks the
challenge's domain and semantics and subtracts the pinned genesis height.
Transaction receipts already use accepted count. Clients must not conflate them.

## Receiving and client paths

`Host.ReceiptContinuity` produces openings from the receiver's loaded tree and
suffix digests from its accepted records. Historical fallback uses the canonical
prefix executor. Ordinary reads usually avoid replay: the client returns its
previously verified opening, and the Host keeps a bounded cache of 64 already
loaded observation heads so a clock tick between reading and obtaining a proof
does not force historical reconstruction.

The pure verifier is the same Lean implementation used by the Host. The client
runs it locally; Rust transports bytes and manages durable custody, rather than
reimplementing Lean hash/codec semantics:

```
HOST CONFIG continuity-point CHALLENGE.json POINT.json
HOST CONFIG continuity-verify REQUEST.json RESPONSE.json VERIFIED.json
```

Workspace continuity is explicitly initialized against a signed resource read:

```
mini workspace --action continuity-init --dir WORKSPACE --name RESOURCE --verifier HOST
```

The initialized workspace guards ordinary reads and shared signed-view consumers
before returning data. Accepted mutation receipts are checked and durably retained
before successful submit or recovery output. A failed continuity check after a
write does not mean the write was rejected: the client keeps its exact attempt
and asks for lookup recovery, never a newly signed replacement. Older workspaces remain identified as legacy
until initialized. An enabled workspace with missing or corrupt custody fails
closed; ordinary reads never silently create a new anchor.

A replacement local verifier requires an explicit `continuity-verifier` action.
The replacement must preserve the deployment identity and verify the retained
anchor; the anchor remains byte-for-byte unchanged. This supports local software
upgrades without silently trusting a new endpoint.

Historical retained challenges can be checked explicitly. Their proof runs from
the old receipt to the retained head and cannot move that head backwards. Exact
replayed transaction receipts use the same historical treatment; a newer replay
may advance custody after its extension is verified. A read
captures a baseline before transmission. If concurrent reads finish out of order,
an older completion may be proved a prefix of the newer retained head; a new
ordinary read below its own starting baseline is still refused.

Custody updates hold a process-shared lock, write a private temporary file, fsync
it, rename it and fsync the containing directory before acknowledging the answer.
Workspace enablement is retained separately from the anchor. This detects missing
anchor custody rather than falling back to first trust.

## Evidence

`Host.ReceiptContinuityCheck` executes genuine authenticated-map openings and
refutes changed/reordered/truncated suffixes, missing or extra siblings, incorrect
chains, roots, identities and completion flags, lower heads and same-height forks.
Rust continuity tests cover acknowledgment ordering, custody loss/corruption,
concurrent completions and real child-process termination at durability stages.
Those process crashes are not simulated power loss.

`native/resource-client/continuity-journey.sh` runs the actual Host/socket/workspace
path on a fresh private Store, including ordinary advancement, retained historical
reads, altered network proofs, custody-loss refusal and service restart. Its
execution result is separate from source compilation and the unit-test results.

The independent candidate based on `663a63fd` plus anchored-Store seam `62f110f2`
completed the receiving journey on 2026-10-02: **38/38 named steps passed**. This
included an actually accepted mutation whose altered extension prevented success
output and anchor advancement, followed by exact lookup recovery and durable
acknowledgment. Restarted ordinary and historical reads retained the same anchor.
The native Host build passed 6774 jobs; the Rust checks passed 16 continuity
cases, 19 workspace cases, and the retained-call retry case. The source verifier's
16 cryptographic cases passed separately. These are candidate results, not a claim
that later integrations or unrelated full-system suites were qualified.

Runtime evidence is retained on the build host under
`codex-receipt-continuity/journey-1/` (`rows.tsv`, `provenance.sha256`, retained
requests/proofs and private test workspaces). The fixture creates fresh credentials
and Store data; those files are deliberately not part of this repository.
