# Existing-world SPK attachment and ordinary checkpoints

Construction contract, October 2. These scripts do not create a second Store or
replace existing apps. Qualification needs the joined manifest and actual service
journeys; unit/helper checks are not browser or backup/restore evidence.

## Existing Store and arbitrary members

Run `scripts/spk-platform/same-store-profile.py INPUT` once as the Store operator.
Its `mini-spk-same-store-profile-input-v1` input names the exact manifest/source
commit, existing Mini config/hash, private socket, grains root and explicit broker
socket, source runtime semantics, completion seed/public key, pinned bwrap, and
management `{subject,keyId,keyEpoch,seedPath,publicKeyPath}`. The existing config
must already contain matching lifecycle management and completion custody. It
performs native `grain init-store` against that exact config and broker, and
publishes the retained native profile/init results. It initializes no genesis,
account or socket service. Existing profiles are preserved rather than guessed.

Run `same-store-app.py INPUT` as that operator. Protocol
`mini-spk-same-store-attach-v1` requires:

- Fresh private evidence `root`; exact `manifest`, `expectedSourceCommit`,
  `miniConfig`, `miniConfigSha256`, `workspace`, `genesis`, `publicSocket`,
  `privateSocket`, `grainsRoot`, `brokerSocket`, `profileResult`, `initStoreResult`.
- `namespace: {domain,semantics}`, `room: {target,capability}`, signed package
  `spk`/`spkSha256`, and optional `sizeClass` (default S).
- `authority`: app `owner`, optional funding/birth `creator` (defaults to owner),
  `creatorAccountCapability` (legacy fixture default `ownerAccountCapability`),
  `factory: {target,capability}`, `tool` and `parent` each containing
  `{task,capability,observeCapability}`, source `template`
  `{issuer,ownerBudget,lifetime}` and `tariff: {base,perBirth}`.
- `application`: explicit `app`, `packageManifest`, `snapshotManifest` and six
  corresponding owner/control capability IDs. No resource arithmetic is required.
- `keys`: actual subject-keyed `{keyId,keyEpoch,seedPath,publicKeyPath}` custody.
  Include source-requested sponsor/issuer signers as well as participants. Secret
  seeds are referenced in protected workspaces rather than copied by this adapter.
- `delegates`: arbitrary member-keyed entries `{subject,session,descriptor,cap,
  sessionControlCapability,descriptorOwnerCapability,descriptorControlCapability,
  ticket,appObserve,pkgObserve,ticketOwner,ticketControl,ticketObserve,expectedHost}`.
  Resource and capability allocations must be distinct. The current resident
  route limit is explicitly 64; it is not a fixed two-person product.

For canonical workroom funding, creator/payer 8 can fund births and metered tasks
while room founder 7 owns the app. The owner performs app/ticket delegations and
share issuance; source signing slots select the exact issuer, payer and member
keys. Every query/birth/install/share/start/enrollment uses the same supplied
Mini config and socket pair. Signed namespace and room authority are observed
before any app write. The result retains `appId`, all actual subjects, profile,
resident config, generation, unit and routes as an inventory.

The joined harness hook is `python3 same-store-hook.py --request REQUEST
--result RESULT`. Set each app instance's `attach.inputPath` to the attach input.
Its delegate map must equal that room's scoped member-key-to-subject map and the
owner must equal the room founder. The hook writes from every member, reads from
an independent next member, and checks all retained markers after the harness's
controlled restart. It returns the actual generalized hook envelope and immutable
artifact hashes. Interactive browser inspection, revocation, uncertain effects
and backup receiving remain separate actual cases.

## Bounded request admission

Each resident admits at most 16 pending HTTP requests, with at most two per
principal across all their routes. Bounded readers run separately from the sole
physical receiver. Queued selection uses the principal's last served turn; listener
acceptance rotates. Unadmitted requests expire at 30 seconds and allocate no Mini
operation or Store record. Responses are `mini-spk-admission-v1`: `busy` permits a
new request; `uncertain` permits exact recovery only. A retained native/physical
marker prevents unrelated new authoring in that app generation. Different apps
have independent queues and fences. One physical call per generation and all
existing exact dispatch/replay rules remain mandatory.

## Unattended online checkpoint

A resident serves same-operator `checkpoint-control.sock` in its generation
journal. Frames are a little-endian 32-bit JSON length, maximum 4096 request bytes.
The closed request is:

```
{protocol:"mini-spk-checkpoint-control-v1", action:"pause"|"resume",
 nonceHex:64_lowercase_hex,
 binding:{app,generation,journalDir,residentConfig,residentConfigSha256,
          miniConfigSha256}}
```

Pause executes between serialized human and agent receiving callbacks. It
requires the exact live incarnation, no in-flight dispatch, no active physical or
native marker, no unresolved historical dispatch tombstone, and a certain RPC
driver. A durable app-level pause intent precedes lease revocation. Live streams
close; clients later reopen through ordinary current Mini admission. A bounded
failed drain leaves the pause fenced and supports the same exact retry. No
participant signature or new source authority is minted by transport resume.
Human requests receive typed busy; agent connections close before any frame is
read/admitted, so their clients must retain exact uncertainty rather than infer
absence. Route mutation is refused while paused.

The complete pause receipt binds the exact request and physical `record.json`
hash. A completed resume receipt is fsynced before removing the matching pause
marker. Repeated exact resume is idempotent; an old resume cannot clear another
pause. An interrupted pause fences startup of every generation of that app.
Atomic publication reuses the hostd temp/fsync/rename/parent-fsync helper under the
checkpoint lock. Broker copy and pause/resume use the same lock.

Static root-owned callback config `mini-spk-checkpoint-app-config-v1` contains
`app`, `stateRoot`, `profilePath`, `spkHost`, `spkHostSha256`. The service registers:

```
python3 /pinned/scripts/checkpoint-app.py capture CONFIG --checkpoint-id ID
python3 /pinned/scripts/checkpoint-app.py quiesce CONFIG --checkpoint-id ID
python3 /pinned/scripts/checkpoint-app.py resume CONFIG --checkpoint-id ID
```

Plans reside under `stateRoot/checkpoints/ID`. Each successful callback returns
`mini-service-app-checkpoint-result-v1` with the exact ID/action and `ready:true`.
Quiesce also returns the private `pauseInventory` path and `pausedUnits`. The
inventory protocol is `mini-spk-checkpoint-pause-inventory-v1`, with
`apps:[{store:<native Store tag>,request:<exact pause request>}]`.

Root uses the pinned source commands:

```
spk-host checkpoint-pause-check BROKER_CONFIG PAUSE_INVENTORY
spk-host checkpoint-backup BROKER_CONFIG OUTPUT_DIR PAUSE_INVENTORY
```

Pause-check verifies native private custody, complete intent/receipt identity,
resident/config/journal hashes, exact physical incarnation and every active app's
coverage. It returns `activePausedUnits` and `pausePins`. Backup repeats the checks
while holding the pause/resume locks and uses the existing filesystem freeze/copy/
thaw path. `checkpoint-grains-backup.json` explicitly labels live images
`paused-frozen-crash-consistent`; it does not claim app background workers stopped
or application-level transactional snapshots. The original backup manifest remains
its original honest state. Every other Store writer must be quiesced before Store
and custody copies. Keep these paused resident units running during the checkpoint.

Service order: capture all app plans; pause all apps and drain streams; quiesce
other Store writers; stop Store; check pauses and copy volumes/Store/custody;
restart the same Store owner; exact-resume all app plans; restore ingress. A failed
phase retains its plan and fence. Never substitute a new nonce or stop app units
without an actual recovery plan. Actual root receiving and failure-cut rehearsal
are required before scheduling this path.

## Disaster restore boundary

Online checkpoint resume preserves the running generation. Disaster restoration
is separate: the process and live streams do not survive, and the one-shot launch
journal must never be rearmed. Retain uncertain dispatch evidence. Recovery must
perform an authenticated source/physical STOP audit, retire only the exact stopped
checkpoint fence, START a new generation, and let returning members re-enroll with
their existing authority and retained role/ticket through an ordinary client flow.
The existing `session-reenroll` compatible-upgrade admission is not that ordinary
client flow. Its new same-source reconnect mode and audited stopped-fence retirement
are explicit remaining implementation/receiving work; automatic disaster restore
has not been delivered by these callbacks.

## Native Store transport visibility

A root-owned broker configuration may declare `residentHomeReadOnlyPaths`, a
bounded inventory of canonical protected regular files and operator socket
parent directories. When a native resident refers to transport configuration,
completion custody, or signing files below `/home` or `/root`, the broker
requires those exact paths before installing its unit. The socket directory
must contain the resident's actual operator-owned Unix endpoint. No additional
writable paths are granted.

The source renders a separate immutable unit drop-in with `ProtectHome=tmpfs`
and exact `BindReadOnlyPaths`. Selected file parents are empty read-only tmpfs
mounts with their original protected ownership and permissions; only the
listed files are mounted inside. This preserves signing custody checks without
revealing sibling files. The exact socket parent is bound read-only so its
private directory custody and Unix connection remain available. The base
unit, app bubblewrap root, and existing grain state/volume write limits remain
in force. The inventory gives filesystem visibility; current native authority
still decides every operation.

An initial unit failure before native BEGIN can retry the same generation only
with the ordinary source `never-begun` classification, current installed app
observation, and failed inactive unit incarnation. An admitted or uncertain
BEGIN is recovered through its exact retained attempt; visibility repair does
not authorize another physical invocation. The current receiving app531101 has
confirmed installation105/ticket112 and generation2 never-begun, with a
sandbox visibility failure. Browser and checkpoint receiving remain pending
until the source-rendered unit actually runs.
