# Client custody across an authorized carry

A carry is an operator-authorized handoff between deployment identities. The
operator's native receiver audits private source state and the target semantics.
The client verifies the public detached EdgeSeal using an operator key it pinned
locally beforehand, authenticates the old receipt-to-cut prefix, and installs the
signed target endpoint. This does **not** make the client independently replay the
operator's private state or establish global consensus. Private Store images and
MAC keys are not part of the public client protocol.

## Local authority and source registry

While the workspace still uses its original trusted continuity verifier:

```
mini workspace --action continuity-carry-authority --dir WORKSPACE --operator-key HEX64
```

The command holds the receipt custody lock, checks the current verifier and
identity, and records the current authenticated anchor beside the explicit key.
It snapshots the local verifier, configured signature helper, exact config bytes,
and exact profile output into an owner-private capsule. The result reports
`sourceCapsulePath`. All files and directories are synced before success. No key
or executable is learned from an endpoint response. No Store/helper replay is
performed on the client; the copied signature helper is a pinned cryptographic
dependency of the source-owned public seal verifier.

If the original verifier lacks `carry-edge-verify`, upgrade it using the existing
same-identity `continuity-verifier` command. This keeps the registered capsule and
operator pin. The capsule retains the original local interpretation for historical
receipts; it is distinct from the operator's server-side semantic capsule.

Registry files are `verifier`, `signature-verifier`, `original-config.json`,
`profile.json`, and `pins.json`. The client-owned `sourceCapsulePins` object is:

```
{verifierSha256, configSha256, profileSha256, identity,
 signatureVerifierPath, signatureVerifierSha256}
```

Hashes and keys are lowercase 64-character hexadecimal strings. Identity uses the
existing `minidregg-continuity-v1` object. Signature helper paths must select the
registered private copy, and every retained file is rehashed before use.

## Adoption

```
mini workspace --action continuity-carry --dir WORKSPACE \
  --edge PUBLIC-MANIFEST.json --source-capsule REGISTERED-CAPSULE \
  --new-config TARGET-CONFIG.json --new-verifier TARGET-HOST
```

Under the custody lock, the client snapshots the explicit edge and configs. It
hashes the target binary without executing it, then invokes the **currently
trusted, checksum-pinned** verifier:

```
CURRENT-HOST OLD-CONFIG carry-edge-verify REQUEST.json RESULT.json
```

The request contains `oldIdentity`, the full current `oldAnchor`, locally pinned
`operatorPublicKey`, `edgeManifestPath`, `sourceCapsulePath`, `sourceCapsulePins`,
`newConfigPath`, and `newVerifierPath`. Full points use `height`, `worldRoot`,
`logChain`, and exactly 256 `systemSiblings`, all canonical decimal strings.

The accepted result uses algorithm `minidregg-carry-edge-v1`, `oldIdentity`,
`newIdentity`, full `oldCut` and `newStart`, `bodyDigest`, `originIndexDigest`,
`operatorPublicKey`, and `targetVerifierDigest`. The client independently binds
these fields to local custody and explicit target selections. The new height must
be exactly old cut height plus one. Only after the old verifier accepts that seal
and the client checks its bindings may the target binary's profile run. Its
identity must equal the signed new identity.

The old verifier checks ordinary paginated continuity from the pinned authority
anchor through the current anchor to the old cut. The target endpoint is expected
to be already serving: these op151 requests use the authorized **new** transport
config and image digest, while their payload names the **old** identity and local
proof verification uses the old config/verifier. This special proof-only request
does not change the process's ordinary socket pin.

## Durable transition and history

An immutable lineage record retains old settings, anchor, workspace manifest,
operator pin, edge verdict, exact proof request/response paths, capsule references,
and next settings/anchor/manifest. The write-ahead record is synced before any
active file changes. Recovery accepts each component only if it equals one of the
recorded old/new values, then completes forward, syncing settings, anchor,
workspace manifest, authority retirement, and completion phase. It never enrolls
a new endpoint or guesses a replacement. Missing custody or unrecorded changes
refuse recovery. The old operator pin is retired; another lineage requires a new
explicit pin. The `freshContinuity` first-enrollment marker remains unchanged.

Ordinary in-flight tickets from the old identity refuse after migration. Their
exact mutation bytes remain available for later lookup; a refused acknowledgment
must never trigger a newly signed resend.

For explicit historical reads and already obtained exact-replay receipts, accepted
counts select nonoverlapping archived lineage ranges. The client verifies the old
point to that lineage's old cut under its retained verifier/config, with current
server transport pins. Durable carry edges connect that cut to current custody.
Historical verification never replaces the new anchor. A missing or invalid
old-identity op151 response is a refusal, not a same-profile fallback.

Uncertain **old call lookup** is a separate native integration obligation. The
existing retry path still selects the original attempt's transport/codec, so a
fresh lookup after an identity carry requires a source-owned origin-aware lookup
operation. This client change preserves those bytes and refuses incompatible
transport; it does not silently reinterpret or resend old calls.

## Evidence and remaining integration

The Rust tests exercise physical private capsule snapshots, hash changes, wrong
result bindings, missing/unrecorded custody, real child-process exits after each
transition file sync, stale in-flight tickets, unchanged first-use metadata, and a
real Unix-socket receiving fixture with the server already on the target config.
That fixture checks the new transport envelope and old identity payload, imports
the exact signed target witness, and verifies a historical replay without anchor
downgrade. It also verifies that a refused source verdict never executes target
code. Its proof/signature verdicts are deliberately **injected test fixtures**.
These tests establish custody/control flow, not native cryptographic correctness.

Native EdgeSeal and old-identity history dispatch are owned by the carry receiver
implementation. An actual native end-to-end journey must use those components;
the prior `3b1f628a` Host does not implement `carry-edge-verify` and correctly
refuses adoption. Process-exit tests do not simulate hardware power loss.

Scoped Rust validation in the independent `codex-continuity-carry` checkout:
`cargo test --jobs 2 receipt_continuity` passed 28 filtered tests (including child
harness entrypoints), and `cargo test --jobs 2 workspace::tests` passed 19 tests.
Both ran on persvati, nice 10, CPUs 3–4, with an independent Cargo target directory.
The receiving fixture uses injected proof verdicts as described above; no native
carry end-to-end pass is claimed here.
