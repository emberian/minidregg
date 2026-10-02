# Typed controller configuration migration

Entry points:

```
grain-runtime config-migrate active ADMIN_SOCKET ABS_PRIVATE_REQUEST
grain-runtime config-migrate stopped ABS_CONTROLLER_CONFIG ABS_PRIVATE_REQUEST
```

The stopped entrypoint runs as the sole MainPID of the **same canonical**
`mini-grain-controller@TASK.service` unit with its existing source-owned unit
environment. It is a query/publication one-shot, never `serve`. It neither starts a
worker nor sends a provider request. An independently named service cannot borrow
this proof. The orchestrator must preserve and restore the exact unit/drop-in
configuration before normal restart; no change to the cgroup proof is included.

Request (owned regular mode 0600 file; all paths absolute):

```json
{
  "type": "mini-controller-config-migration-v1",
  "expectedConfigSha256": "EXACT_OLD_CONTROLLER_CONFIG_RAW_SHA256",
  "expectedBindingSha256": "SOURCE_QUIESCENCE_BINDING_SHA256",
  "targetConfig": "/private/upgrade/target-controller.json",
  "targetConfigSha256": "EXACT_TARGET_CONFIG_RAW_SHA256",
  "residentState": "/private/controller-state/resident",
  "compatibleAdmission": null
}
```

Use residentState null only when no room resident is configured. For a Host
transport transition, compatibleAdmission is `{ "path": "ROOT_ADMISSION_PATH",
"sha256": "EXACT_ROOT_ADMISSION_RAW_SHA256" }`. Root custody uses the shared
compatible-upgrade-custody validator and an exact unique captured `hermesProfiles`
entry binding old config path/raw hash, journal binding hash, and old Host config
hash. Operational-only changes must not attach an unrelated admission.

Initial supported operational differences are explicit providerTask.maxIterations
(1..6), contextWindowTokens (request ceilings fit, <=2097152), and maxRequestBytes
(1..1048576). Existing native grants, provider reserve, input/output ceilings,
model, route, credential identity and all other fields remain exact. Other fields
are **unsupported by this transition**, not declared universally impossible;
they require their appropriate typed compatibility/source authorization evidence.

Host changes are exactly source→target Host/config paths from the root admission,
plus optional exact admitted public→management socket. The Mini executable also
follows the exact admitted source/target `mini` manifest paths and target SHA,
with root image custody checked on activation. Matching room transport and
its delegated workspace are published together. Arbitrary Mini replacement, keys, stateDir,
workspace/home paths, grain identities and authority grants cannot be rebound.
Qualified feature Host image changes require separate qualification, not this
initial transport transition.

For a Mini client replacement with the Host stack unchanged, use `miniAdmission`
in the same request instead of `compatibleAdmission`. This narrower root artifact
does not claim kernel upgrade compatibility or require the existing unchanged
Host/config to be root-owned. The artifact and target Mini executable must have
root custody; its exact schema is:

```json
{
  "protocol": "mini-controller-client-upgrade-v1",
  "controllerConfig": "/private/controller.json",
  "controllerConfigSha256": "RAW_OLD_CONTROLLER_CONFIG_SHA256",
  "bindingSha256": "CANONICAL_SOURCE_JOURNAL_BINDING_SHA256",
  "sourceMini": {"path": "/private/bin/mini-old", "sha256": "SOURCE_MINI_SHA256"},
  "targetMini": {"path": "/var/lib/mini-images/new/bin/mini", "sha256": "TARGET_MINI_SHA256"},
  "host": {"path": "/private/bin/host", "sha256": "UNCHANGED_HOST_SHA256"},
  "hostConfig": {"path": "/private/host.json", "sha256": "UNCHANGED_HOST_CONFIG_SHA256"},
  "hostSocket": "/private/kernel.sock"
}
```

Set `miniAdmission` to `{ "path": "ROOT_ARTIFACT", "sha256": "RAW_ARTIFACT_SHA" }`
and `compatibleAdmission` to null. The target path must differ from the source;
preserve the source image through publication recovery. Fresh admission/recovery
checks exact source Mini, Host and Host config bytes plus root-pinned target Mini.
Historical archive checks do not require obsolete live images. Only `mini` and
matching `toolTask.room.mini`, together with the existing operational throttle
fields, can change. Changed Host/config/socket, authority, model, route or grain
fields refuse this category. Full transport changes still require the full
compatible admission. Both admissions together are refused. This is an explicit
root image admission, not a claim that the new Mini's feature behavior was tested.

The resident lock covers both `resident.json` and the strict `requests.json`
request queue. Queued requests, a selected request with `started` custody, and
`maintenancePending` are retained work even if `resident.pending` is absent. They
permit an unchanged restart retaining evidence, but block a closed checkpoint
and account/config reassignment. Resolve them through their source completion
or exact preadmission refusal paths before requesting publication.

A configured queue's exact bytes and digest are retained as
`resident-requests-before.json` / `residentRequestsSha256`. File absence is also
pinned: a newly appearing queue invalidates the locked snapshot. Startup refuses
changed queue custody before replacing any receiving member. This category
still does not authorize a new room account or assignment inbox.

The source retains config-before/after, journal-before/after, optional
workspace-before/after, resident-before, quiescence, transaction and previous
selection under `STATE/config-migrations/migration-OPERATION_ID`. `transaction.json`
and its referenced blobs are immutable. The only mutable selection is
`STATE/config-migration.json`. Every archive file is mode0600 and fsynced before
selection publication. A pre-publication failure can leave an unselected archive;
it does not change the selected config and is retained, not erased.

A successful stdout result is one JSON object:

```json
{
  "type": "mini-controller-config-migration-v1",
  "phase": "published",
  "archive": "/private/controller-state/config-migrations/migration-0000000000000042",
  "operationId": 42,
  "restartRequired": true,
  "fullResumeReady": false,
  "changedFields": ["/providerTask/maxIterations"]
}
```

The orchestrator may retain stdout at its own exact result path; the source
archive and selected manifest are authoritative if that reply is lost. Repeating
the **same request** through the stopped entrypoint performs ordinary locked
startup recovery of any exact old/new receiving vector, then returns the same
archive/operationId with phase activated, restartRequired false and
recoveredReceipt true. It does not allocate new query IDs or rebind again. An
unknown receiving byte, changed resident, missing archive, altered admission or
unrelated journal edit refuses and retains evidence.

Publication freezes every input/save in the old controller. Ordinary startup
holds controller and resident locks, recovers exact partial publication before
cross-file validation, re-reads effective config, validates exact journal binding,
and activates the selection before releasing the resident lock. Resident startup
also re-reads config under its own flock and refuses unactivated publication before
any room preparation or budget return. Normal future controller restarts update
the activated process marker without rewriting historical journals/archives.

Migration success is not a promise that an ACP session has loaded or that a useful
agent turn completed. The ordinary source session/load verification still gates
full resume. Pending resident/native/provider/room/external uncertainty blocks
migration; clearing them is a separate typed recovery operation.

Receiving checks included: operational bounds and authority refusal, unadmitted
transport refusal, all eight config/journal/workspace old/new interruption vectors,
unknown-member preflight refusal, exact-vs-altered crash temp recovery, and old
process/resident publication barrier. These are staged for the owner’s shared
Rust batch; no additional compiler was started by this lane.

## Existing member key rotation

This transition adopts a native key rotation that already happened; it does not
rotate the member key, install a credential, create a grant, or consume a provider
call. Prepare the new current key's credential and exact model/runner/epoch grant
through the normal native member entry first.

Use the existing `config-migrate active` or `config-migrate stopped` request with
both admission fields null. Only `providerTask.onBehalfOf.publicKey` may differ;
the owner subject, grain identities, capabilities, budgets, model, provider route,
request ceilings and every other field remain unchanged. Publish operational or
transport changes separately.

Under the controller lock, source code queries native current-owner status and a
fresh signed provider-task view, verifies the new key is current/not revoked,
uses the signed height to check the existing grant's expiry, and verifies the
exact model, runner, native epoch and an output-token grant sufficient for the
unchanged configured ceiling. These read-only observations finish before the
normal complete signed/process/resident quiescence gate. They do not increment
the grant's daily usage.

`owner-rotation.json` in the immutable migration archive retains the old/new key
coordinates, native owner response, signed-view coordinates/hash pins and grant
metadata. The manifest pins its bytes with `ownerRotationSha256`. Owner status is
honestly a native read-only observation, not a signed mutation receipt. Historical
archive validation never converts that record into a current-authority proof.

If publication was interrupted, stopped startup re-queries current owner/grant
before replacing any remaining old receiving member. It retains and fsyncs an
`owner-reobserved-NANOSECONDS.json` decision and reconfirms physical stop. A stale,
revoked, expired or missing grant refuses recovery without resetting the journal
or replaying a provider call. Supply a valid current grant through normal native
entry and retry the same migration. After activation, ordinary provider calls
continue their own current-owner/epoch checks; historical startup does not claim
that an old migration observation stays current indefinitely.
