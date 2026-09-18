# Native Mini host

The source-owned receiving process is `Host/Main.lean`, with Lake target
`minidregg-host`. It transports the actual kernel birth, invocation, policy
installation, and delegation receivers. It does not evaluate a second policy
language, accept raw durable intents, or supply native signature verdicts.

Implementation status and measured checks belong in the sprint evidence, not
this interface document. Adding a target does not establish that its linked
executable or complete user journey has passed.

The unsigned public preparation route is deliberately closed while its actual
per-resource observation gate is being integrated. Internal preparation reads
state, so exposing its success/errors before authorization would be a balance
or existence oracle. The command shape below describes the receiving contract;
it does not bypass that gate.

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
authority, and the semantics of every selected policy source.

Initialization is explicit:

```text
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

## Prepare, sign, submit, recover

```text
minidregg-host CONFIG.json prepare DRAFT.bin PLAN.bin
minidregg-host CONFIG.json assemble PLAN.bin SIGNATURES.bin CALL.bin
minidregg-host CONFIG.json submit CALL.bin OUTCOME.bin
minidregg-host CONFIG.json lookup CALL.bin OUTCOME.bin
```

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

## Process transport

`stdio` reads length-framed binary requests: four little-endian length bytes,
then one operation byte and the canonical payload. The limit is 1 MiB per
frame. Operation bytes are `0` describe (empty payload), `1` prepare, `2`
submit, `3` lookup. Response bytes have the same operation byte; prepare refusal
uses `255` followed by a strict outcome. Describe returns UTF-8 JSON;
preparation returns `signingPlanCodec`; submit/lookup return `outcomeCodec`.
Truncated, oversized, or unsupported frames terminate the stream.

An SSH shell, supervisor, or Hermes adapter can carry these bytes. It must
preserve original calls, confirmation distinctions, and receipt identity.
Policy installation programs a stored predicate rule; it is not an imperative
VM program upload. Authorized resource queries and cursor-based history need
their own actual observe-authorized receiving surface and are not advertised
as callable endpoints here.
