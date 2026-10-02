# Credential write scopes and owner-key migration

`grain-runtime controller-write-scopes CONFIG` describes public credential paths
using the runtime's strict Config, provider-table selection and credential Owner
parser. It does not open the credential store, read a key, lock a namespace, make
a native request or increment usage. The provider table remains root-owned.

The JSON response has type `mini-controller-write-scopes-v1`, `configPath`, raw
`configSha256`, `bindingSha256`, `task`, `credentialsRoot`,
`providerTableSha256`, `provider`, `route`, and `credentialWriteDirectories`.
Only the selected member or pool leaf is writable. No provider means null
selection fields and no directories; a homelab row needs no credential writes.
The shared `credentials::namespace_path` is also used by CredentialStore itself.
No root renderer should reconstruct namespace paths from public keys or route
names independently.

For an existing same-subject owner-key migration, the root orchestrator stops the
resident and controller, retains desired service state, then runs:

```
grain-runtime controller-write-scopes preflight CONFIG REQUEST
```

Run this as the registered service UID outside the old controller mount namespace.
It holds the existing private controller flock, validates the exact migration
request/config/journal binding and permits only the existing owner-key transition.
It queries current native owner authority and the signed provider resource height,
then verifies the existing exact key-epoch/model/runner grant and sealed credential.
That verification may create/acquire the selected provider lock and retain signed
query evidence. It makes no provider request and consumes no usage allowance.
It does not publish a config or journal, and it is **not a closed checkpoint**.

The preflight JSON type is `mini-controller-scope-preflight-v1`, with
`requestPath`, raw `requestSha256`, `source` and `target` scope descriptions,
`sourceJournalSha256`, `changedFields`, `ownerEpoch`,
`ownerObservationSha256`, and `quiescenceRequired: true`. Both scope descriptions
use the eventual live CONFIG path for `configPath` and `bindingSha256`; the
request's target file is only staging input. Source/config/request/journal/table
bytes are rechecked after native observation. Unsupported or mixed changes refuse.

The root helper binds its retained plan to this exact request and result, stages
only the union of old and target selected directories, then starts the existing
canonical SYSTEM unit as a stopped migration oneshot. That receiver again checks
current authority and fresh signed/process/resident quiescence before publication.
Root unit edits stay outside the unprivileged runtime. A failed attempt retains
its staged plan and uncertainty; it does not start a fresh resident prompt.

After the same-unit receiver succeeds, consume the actual source publication:

```
grain-runtime controller-write-scopes receipt CONFIG REQUEST
```

This service-UID command holds the same controller lock and reads the immutable
migration archive/current pointer. It checks the exact request, source/target
transition, historical closed checkpoint, received configuration and current
journal binding. A prepared or partial publication refuses; recover that exact
migration first. A fully received published or activated migration yields type
`mini-controller-scope-receipt-v1`, `requestPath`, `requestSha256`, `archive`,
`transactionSha256`, `phase`, `operationId`, and `target` scopes. It is read-only;
a supplied success label is not accepted as a receipt.

The root helper compares this target and request against its retained preflight,
then narrows the drop-in to the target directories, restores the normal entrypoint,
and restarts to apply the mounts. Retry uses the identical private request and
retained stage. Neither a config-only parser nor a generic controller registration
may silently authorize an existing controller's owner drift.
