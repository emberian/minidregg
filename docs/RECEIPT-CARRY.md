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

If the original Host cannot verify carry edges, install the generic public carry
verifier explicitly, using its independently selected artifact hash:

```
mini workspace --action continuity-carry-verifier --dir WORKSPACE \
  --verifier /absolute/path/to/portable-carry-verifier --sha256 HEX64
```

The installer checks that hash **before executing** the artifact, holds current
custody and authority locked, and invokes:

```
PORTABLE REGISTERED-OLD-CONFIG carry-verifier-profile REQUEST.json RESULT.json
```

The request contains client-owned `oldIdentity`, `sourceCapsulePath`, and
`sourceCapsulePins`. The portable artifact validates those registered source
files, derives identity from the retained old profile, and returns exactly
`{algorithm:"minidregg-carry-verifier-v1",identity,sourceCapsulePins,
edgeAlgorithm:"minidregg-carry-edge-v1"}`. The client requires an exact match before
writing its independent private `carry-verifier.json` pin:

```
{type:"minidregg-carry-verifier-pin-v1",verifier,verifierSha256,
 identity,sourceCapsulePath,sourceCapsulePins}
```

Ordinary `Settings.verifier`, deployment identity, anchor bytes, authority record,
and registered source capsule remain unchanged. Only carry-edge verification uses
the new executable. The workspace's `receiptCarryVerifier` marker is synced before
the pin, so interruption disables carry until explicit reinstall. A missing,
changed, unmarked, or stale pin refuses; it never silently falls back to another
executable. A pin inherited by a different identity or capsule needs an explicit
new install. Neither an edge nor an endpoint selects this executable.

The existing same-identity `continuity-verifier` action still upgrades ordinary
proof interpretation when explicitly requested; it is not required to bootstrap
the independent carry verifier. The source capsule retains the original local
interpretation for historical receipts and is distinct from the operator's
server-side semantic capsule.

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
hashes the target binary without executing it, then invokes the separately
installed portable verifier if present, otherwise the already trusted source
Host. Both paths remain checksum-pinned:

```
PINNED-CARRY-VERIFIER OLD-CONFIG carry-edge-verify REQUEST.json RESULT.json
```

The request contains `oldIdentity`, the full current `oldAnchor`, locally pinned
`operatorPublicKey`, `edgeManifestPath`, `sourceCapsulePath`, `sourceCapsulePins`,
`newConfigPath`, and `newVerifierPath`. Full points use `height`, `worldRoot`,
`logChain`, and exactly 256 `systemSiblings`, all canonical decimal strings.

The accepted result uses algorithm `minidregg-carry-edge-v1`, `oldIdentity`,
`newIdentity`, full `oldCut` and `newStart`, `bodyDigest`, `originIndexDigest`,
`operatorPublicKey`, and `targetVerifierDigest`. The client independently binds
these fields to local custody and explicit target selections. The new height must
be exactly old cut height plus one. Only after the pinned carry verifier accepts that seal under the registered old
profile and the client checks its bindings may the target binary's profile run. Its
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

## Read-only recovery of old ordinary calls

`workspace --action recover --dir WORKSPACE --attempt RETAINED` routes an archived
ordinary SignedCall through public read-only op153 before the legacy attempt can
pin an obsolete Host image. The existing central `retry --mode lookup` path uses
the same adapter. It keeps the current socket/config/image pins, selects the origin
profile using the retained challenge and authenticated lineage range, and sends
exact retained `call.bin` bytes. It never executes the original Host path, mutates
those bytes, signs a replacement, or submits the call. Old direct execution and
`--mode submit` refuse. Specialized historical calls outside ordinary SignedCall
need a separate source-owned whitelist and refuse here.

The binary payload is a four-byte little-endian JSON header length, followed by
`{algorithm:"minidregg-carried-call-lookup-v1",originIdentity}`, followed by the raw
call bytes. The header is at most 1024 bytes. Every formerly supported raw call up
to 12,102,759 bytes still fits. Only op153's body allowance grows to 12,103,788 bytes
(including opcode); every other opcode retains 12,102,760. Config bytes remain
bounded to 65,536 and the v2 transport envelope has its separate fixed overhead.
Length prefixes exceeding the resulting frame bound fail before allocation.

The result has exactly `algorithm`, `originIdentity`, `callDigest` (SHA-256 of the
exact raw call), and `outcome`. The client accepts only these outcome shapes:

- Confirmed: `type`, `confirmation:"replayed"`, `transactionId`, `eventId`,
  `acceptedCount`, and `worldRoot`.
- Absent: `type:"absent"`.
- Refused: `type:"refused"`, and a fixed identifier `reason` from
  `origin-mismatch`, `malformed-call`, `capsule-unavailable`, `lookup-refused`, or
  `receipt-invalid`.

Unexpected fields, content, free-form explanations, wrong origin/digest, and
out-of-segment receipts refuse. Raw response and transport evidence are durably
retained under the retry number. A confirmed outcome is acknowledged only after
its old-profile historical continuity proof succeeds; missing or invalid proof
leaves the exact attempt available. Absent/refused is not authorization to resend.

Op153 exposes only original receipt/outcome metadata, like existing receipt
lookup; it remains useful after grant revocation. It grants no historical content
access. Content observations still need current authority. Native old-capsule
lookup must be read-only and sanitize its inspected outcome to these fields.

## Evidence and remaining integration

The Rust tests exercise physical private capsule snapshots, hash changes, wrong
result bindings, missing/unrecorded custody, real child-process exits after each
transition file sync, stale in-flight tickets, unchanged first-use metadata, and a
real Unix-socket receiving fixture with the server already on the target config.
That fixture checks the new transport envelope and old identity payload, imports
the exact signed target witness, verifies historical replay without anchor
downgrade, and exercises op153 against exact call bytes. It checks forged call
hashes/origins, unexpected content fields, absent outcomes, retry evidence, and
refusal of direct execution or resubmission. It also verifies that a refused source verdict never executes target
code. Its proof/signature verdicts are deliberately **injected test fixtures**.
These tests establish custody/control flow, not native cryptographic correctness.

Native EdgeSeal, portable source-profile validation, old-identity history dispatch,
and read-only old-capsule lookup are separate native integration obligations. An actual native end-to-end journey must use those components;
the prior `3b1f628a` Host does not implement `carry-edge-verify` and correctly
refuses adoption. Process-exit tests do not simulate hardware power loss.

Scoped Rust validation in the independent `codex-continuity-carry` checkout:
`cargo test --jobs 2 receipt_continuity` passed 29 filtered tests (including child
harness entrypoints), and `cargo test --jobs 2 workspace::tests` passed 19 tests.
Both ran on persvati, nice 10, CPUs 3–4, with an independent Cargo target directory.
The receiving fixture uses injected proof verdicts as described above; no native
carry end-to-end pass is claimed here.
The op153 follow-up also passed all 26 transport tests, including full old call
capacity with maximum header/config, new maximum plus one refusal, and unchanged
ordinary opcode bounds. The independent debug client build passed. Native
cryptographic and read-only capsule execution remain separate integration tests.

Portable bootstrap follow-up validation in the independent
`codex-carry-verifier-client` checkout: 33 receipt-continuity tests passed. The
receiving fixture additionally selects an explicitly installed portable verifier
while the old Host deliberately refuses carry-edge commands, and exercises both
portable approval and refusal. Hash mismatch executes no artifact; rejected
portable authorization executes no target. Fixture descriptions/verdicts are
injected and do not establish a native cryptographic end-to-end pass.
