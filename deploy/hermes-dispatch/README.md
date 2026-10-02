# Registered Hermes delivery

`mini hermes-handoff` verifies and delivers the shell producer's complete signed
handoff. The service pump runs it for arbitrary member home inventories; members
use ordinary `summon` and `dismiss` commands.

Fresh rooms declare the central `room_schema.rs` table: names1010, paid-open1011,
assignment1012. Native closed-field admission is unchanged. The roster reserves
499 historical non-founder subject slots. Leaving/kicking retains history;
re-inviting the same subject issues fresh authority and reuses its existing stream.
A new subject at the boundary receives an explicit refusal.

An operator registration is topology, not native authority. Its exact shape is:

```json
{"type":"mini-hermes-dispatch-registration-v1","task":"TASK","subject":"SUBJECT","roomCell":"CELL","encryptionKey":"64 hex digits","workspace":"/absolute/resident-workspace","inbox":"/absolute/private-inbox-root"}
```

Register distinct controller/workspace custody for unrelated room assignments.
`mini hermes-handoff --action registry --registrations DIR --socket SOCKET`
validates the loaded workspace subject, real encryption key and current native
signing key, then emits the public `mini-hermes-registry-v1` resident inventory.
The installer publishes it as `/etc/mini/hermes-residents.json`; a member's
`HOME/hermes/registry.json` can supply the same inventory. `HOME/hermes/node.json`
selects a default subject. Subject, task, room cell and encryption key are resolved
together before funding or granting, including explicit `--hermes SUBJECT`.

The producer reserves a nonzero assignment nonce and deterministic source operation
ID. It retains one exact request before submission and recovers its original call
on retry. State is `HOME/hermes/CELL.json`; outgoing custody is
`HOME/outbox/SUBJECT/room-CELL/assignment-NONCE/`. The manifest includes the exact
account alias/target. Controller provisioning must select that account and the
resulting assignment inbox before prompting.

Dispatch requires a fixed operator registration:

```
mini hermes-handoff --socket SOCKET --action dispatch --registration FILE --bundle FILE
```

The signed bundle binds world domain/seed, recipient, task, founder, room cell,
assignment, all manifest/grant/account bytes, and the accepted scalar transition.
Host authoring binds the retained command to its plan; Host assembly reconstructs
the exact call from retained plan/signatures; native historical lookup confirms
its accepted transaction. First publication requires the current founder signer.
Signed room/grant/program observations qualify setup, and a final relevant room
check detects replacement/dismissal without requiring unrelated world writes to
stop. Native admission remains the authority gate for every actual effect.

Files and `ready.json` are staged privately, fsynced, atomically renamed into
`registered-inbox/room-CELL/assignment-NONCE`, then the parent is fsynced. An
uncommitted partial stage is repaired from the verified bundle; a published inbox
must match immutable payload and file bytes. A retry publishes once. The retained
private gate continues across ordinary founder signing-key rotation; fresh
registrations still require current keys.

Before work, the resident invokes:

```
mini hermes-handoff --socket SOCKET --action check-delivery --dir WORKSPACE --task TASK --inbox ASSIGNMENT-INBOX
```

The ready result includes world, room cell, assignment, exact account, original
plan height, acceptedCount, and acceptedHeight in journal coordinates
(`genesisHeight + acceptedCount - 1`). Current source assignment/grants are
rechecked; later requests must lie strictly after acceptedHeight. A stale,
dismissed or replaced assignment refuses before new work.

Dismissal has its own signed bundle and accepted CAS clearing subject/account/
assignment from the exact prior values to zero. Dispatch publishes `dismissal.json`
inside the original assignment inbox. `check-dismissal` checks it against that
original ready payload and accepted call, returning the originally bound refund
account. This works after room grants are revoked; native account admission still
judges the return. Unsigned notices do not authorize refunds.

The system pump reads `/etc/mini/hermes-dispatch-service.json`:

```json
{"type":"mini-hermes-dispatch-service-v1","mini":"/absolute/mini","socket":"/absolute/mini.sock","registrationsDir":"/etc/mini/hermes-dispatch","memberHomes":["/absolute/member-home"]}
```

`mini-hermes-dispatch.py --config FILE [--once]` discovers one hint per member per
round, retaining advisory scan cursors. It visits at most128 hints per poll and
starts at most32 deliveries with four subprocess slots and60-second deadlines.
Malformed member hints are isolated. Retained assignment history is paged, not a
lifetime admission quota. Bounded advisory caches may evict; native origin and
recipient ready records preserve exact retry after eviction/restart. The current
config inventory bound is4096 member homes; this is an explicit service limit,
not fixed product population. SYSTEM unit installation and write-path inventory
belong to the service installer.

Scoped Rust tests cover source substitution, signatures, registered identity,
duplicate aliases, exact publication, partial staging recovery, precise256-bit
world binding and dismissal CAS. `test_dispatch.py` covers retained-history
pagination, inter-member progress and malformed/duplicate JSON hints. Native
receiving evidence must identify its exact Host/Store/CLI pins; a component pass
on an older unchanged core does not qualify the final joined runtime or provider.
