# Native Mini host

The source-owned receiving process is `Host/Main.lean`, with Lake target
`minidregg-host`. It transports the actual kernel birth, invocation, policy
installation, and delegation receivers. It does not evaluate a second policy
language, accept raw durable intents, or supply native signature verdicts.

Implementation status and measured checks belong in the sprint evidence, not
this interface document. Adding a target does not establish that its linked
executable or complete user journey has passed.

## Building and exercising the native interface

In an independent snapshot, `scripts/build-native-host.sh --umbrella --output
BUILD-DIR --binary BUILD-DIR/minidregg-host` checks the full Lean umbrella and
links the host with bounded compiler concurrency. Its manifest records the source
and object closure. Give each build a fresh binary path so an earlier host remains
available to tests already running against it. Without `--binary`, the default is
`.lake/build/bin/minidregg-host`; the builder refuses to replace an existing binary.
Compile the public acceptance driver against that same closure:

```sh
scripts/build-native-acceptance-runner.sh \
  --host-response BUILD-DIR/minidregg-host.rsp --output RUNNER-DIR
RUNNER-DIR/native-acceptance-runner --new-world \
  BUILD-DIR/minidregg-host VERIFIER SQLITE-STORE OPENSSL ARTIFACT-DIRECTORY
RUNNER-DIR/native-acceptance-runner \
  BUILD-DIR/minidregg-host VERIFIER SQLITE-STORE OPENSSL
```

Use fresh output directories. The second invocation exercises the earlier
owner/delegation and history-integrity journey. The runner builder matches
Lake's package namespace to the host's actual objects. The large signing-plan
fixture exceeds the interpreted `lean --run` recursion depth; use the compiled
runner. Building or usage-smoking it is not an acceptance result.

Preparation requires a signed observation challenge covering its actual resource
read set. Internal preparation reads state, so exposing its success/errors
before authorization would be a balance or existence oracle. The public command
authorizes observation before planning on that same loaded image.

## Configuration and initialization

`Host.Settings` is the operator JSON manifest. It selects the deployment,
federation, complete factory grant template and tariff, initial logical height,
expected genesis seed identity, SQLite byte-store executable/path, and native
signature verifier executable. Configuration is loaded once per process;
operations cannot replace it. Native binaries, their byte transport, SQLite,
and the operating system remain trusted external execution dependencies.

The concrete profile is `Compiler.NativeHostProfile`: BabyBear with scalar
order difference width 29, and the proved `NoWrap` interval. The shared compiler
still checks every actual input range and full-view cast injectivity. Large
integers are never truncated or rescaled. This native checked execution profile
does not claim a deployed succinct STARK proof. Source-bound limbs and carries
remain necessary to support wider arithmetic in this compiler dialect.

The profile's receiver parameters commit the actual deployment, federation,
tariff, and genesis clock offset. The genesis commitment is separate, avoiding
a cycle through the genesis policy records' own semantics identity. Every open
checks the pinned genesis, canonical journal replay, native cell laws, complete
authority, and the semantics of every selected policy source. Reopening also
re-admits each retained original signed ingress at its original prefix and
logical height. Its source-derived intent must equal the complete stored
record; a physically consistent journal alone does not establish authority.

`profile` reports immutable configuration-derived protocol metadata before a
store exists. It reads no resource state, and renders full-width identifiers as
decimal strings. This lets an external initializer obtain the exact semantics
identity without reimplementing profile hashing.

Initialization is explicit:

```text
minidregg-host CONFIG.json profile
minidregg-host CONFIG.json author genesis SOURCE-CONFIG.json SOURCE-CONFIG.bin
minidregg-host CONFIG.json genesis SOURCE-CONFIG.bin GENESIS.bin PINNED-CONFIG.json
minidregg-host PINNED-CONFIG.json bootstrap GENESIS.bin
minidregg-host PINNED-CONFIG.json describe
```

`SOURCE-CONFIG.bin` uses `NativeHostGenesis.configCodec`. The source builder
accepts supplied public enrollment records and authored policies and derives the
actual initial authority, resources, and conserved internal Book. It contains
no private keys or fixture signer. These internal genesis balances do not
represent an external Solana deposit. The `genesis` command checks agreement
with the operator manifest, emits the zero-history image, and writes settings
with its exact seed identity. `bootstrap` validates that identity before an
absence-only installation and physical readback. Ordinary opening refuses a
missing store; it never bootstraps it.

## Source-owned JSON authoring

```text
minidregg-host CONFIG.json author KIND INPUT.json OUTPUT.bin
minidregg-host CONFIG.json inspect KIND INPUT.bin OUTPUT.json
minidregg-host CONFIG.json derive grain INPUT.json OUTPUT.json
minidregg-host CONFIG.json signatures SIGNATURES.json SIGNATURES.bin
```

`Host.Json` constructs the real source ASTs and uses their canonical codecs.
JSON is a notation for those values; it supplies no authority or replacement
policy evaluator. Integers are canonical decimal strings and bytes are hex.
The parser rejects duplicate keys; each authoring form rejects unknown fields.
`inspect` exposes the exact canonical header bytes for external signing and
presents returned views and outcomes. `signatures` transports an ordered JSON
array of detached 64-byte signatures. The receiving path still rechecks every
request, current rule and signature.

## Prepare, sign, submit, recover

The current construction epoch uses one finite transaction command for both
singleton and joint resource mutations. Each ordered target names its actual
kind, resource ID, mutation capability, expected root, command schema version,
and scalar or typed-content operations. The receiver computes the candidate
states and evaluates the installed laws against the same final tuple before
publishing one durable event. A caller cannot submit a proposed final page or
a policy verdict. Duplicate target IDs and physical write aliases refuse.

Typed content contains canonical document, element, atom, run and link records.
Atom edits compare the complete old record; payloads and provenance stay in
the canonical page. Source-anchored links require stored endpoints. Remote
link targets remain references, without an availability or rendering claim.
The content storage schema is version 2 with capacity 16; the independent
content action grammar is version 1. This construction epoch requires fresh
genesis rather than claiming migration of an existing deployment.

A joint command also supplies each target's `observeCapability`. Its signing
plan orders mutation headers, observation headers (role 8), then the shared
authority header. Submission rechecks the observation signatures, current
grants and current resource rules before evaluating policies that can inspect
other participants. Preparation authorization alone is insufficient. A
singleton keeps the blind-mutation path and needs no extra joint-read
envelopes. Policy inputs omit unrelated authority and account state.

Delegation and revocation use the same actual resource-role selection as
observation, including content resources. Revocation requires the distinct
`revokeCapability` management verb; `installPolicy` does not imply it. Rule
replacement preserves existing grants, whose uses check the new rule. A
resource can deliberately deny its own future management operations; there
is no owner repair bypass.

```text
minidregg-host CONFIG.json challenge INTENT.bin CHALLENGE.bin
minidregg-host CONFIG.json observe-assemble CHALLENGE.bin OBSERVE-SIGNATURES.bin SIGNED.bin
minidregg-host CONFIG.json prepare SIGNED.bin PLAN.bin
minidregg-host CONFIG.json assemble PLAN.bin SIGNATURES.bin CALL.bin
minidregg-host CONFIG.json submit CALL.bin OUTCOME.bin
minidregg-host CONFIG.json lookup CALL.bin OUTCOME.bin
```

`INTENT.bin` uses `NativeObservationCodec.intentCodec`. It names the subject,
nonce, preparation draft, and explicit observation capabilities for the actual
read set. The public challenge contains protocol metadata, exact image boundary
and canonical signing headers. Sign each header externally, then assemble the
detached signatures into `SIGNED.bin`. Current capability authority and compiled
resource policies must permit every required observation before preparation
returns a plan or state-dependent diagnostics.

Drafts use `NativeHostCodec.draftCodec`, carrying the existing controller's
canonical draft/command/declaration. Birth also selects the capabilities for
the ordered conserved debit legs. A prepared plan contains the finalized
source command, exact image boundary and logical height, and ordered canonical
signing headers. The headers contain the complete typed requests and selected
committed key information. Preparation is neither authority nor acceptance.

Custody signs each exact header outside the host. `SIGNATURES.bin` is the strict
canonical `StreamCodec.list bytesStream` encoding of the detached signatures
in plan order. `assemble` builds the existing signed ingress. `submit` derives
the requests again and invokes the actual native signature, capability,
compiled-policy, physical, and durable checks.

Logical height is `genesisHeight + loaded.image.accepted.length`. The same
loaded image supplies open checks, height, preparation, and the initial CAS.
A concurrent image change returns contention; the host cannot transplant an
old admission onto a newer journal. Replayed and refused operations do not
advance height. This clock counts accepted commits, not elapsed seconds or
Solana slots.

Outcomes preserve installed, recovered-after-uncertain-response, and replayed
confirmation distinctions. Sealed receipts include the original transaction
and event IDs and the exact historical accepted prefix boundary. A later tip
does not replace that boundary. After a lost response, retain and resubmit or
look up **the original signed call bytes**. Lookup is read-only exact-ingress
replay; an absent entry remains absent, and an occupied ID with different
canonical ingress is a conflict. A failed readback after an attempted commit
remains uncertainty.

All public fresh-submission refusals have the same phase and detail. A mutation
can be authorized without granting the caller read access (for example, a blind
write or recipient credit), so its internal preparation errors are private.
This output rule is not a timing noninterference claim.

## Authorized queries

An observation intent may instead select a resource query. Use the same
challenge, detached signing and `observe-assemble` steps, then run:

```text
minidregg-host CONFIG.json query SIGNED.bin VIEW.bin
```

Views are the selected resource and its own sparse account balances, its selected
policy, or the observation grant used to authorize that query. Whole Books and
unrelated capability records are not returned. Unauthorized and stale signed
observations return the same refusal. Historical cursor queries are not part of
this interface.

## Process transport

`stdio` reads length-framed binary requests: four little-endian length bytes,
then one operation byte and the canonical payload. The limit is 1 MiB per
frame. Operation bytes are `0` describe (empty payload), `1` authorized prepare,
`2` submit, `3` lookup, `4` observation challenge, and `5` authorized query.
Response bytes have the same operation byte; prepare/challenge/query refusal
uses `255` followed by a strict outcome. Describe returns UTF-8 JSON;
preparation returns `signingPlanCodec`; submit/lookup return `outcomeCodec`;
challenge returns `NativeObservationCodec.challengeCodec`; query returns the
selected source-owned view codec.
Truncated, oversized, or unsupported frames terminate the stream.

An SSH shell, supervisor, or Hermes adapter can carry these bytes. It must
preserve original calls, confirmation distinctions, and receipt identity.
Policy installation programs a stored predicate rule; it is not an imperative
VM program upload. Operating-system process control and wall-clock attachment
leases belong to the surrounding host and must not reinterpret the commit-count
clock as elapsed time.
