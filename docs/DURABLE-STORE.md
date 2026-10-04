# The durable Store: interfaces an operator depends on

One Mini Store is one directory (`storageRoot` in the operator configuration)
plus one key file and an independently retained sibling head anchor. This page lists what the Host and its store helper read,
write and refuse there. Anything not listed is not part of the contract.

## Files

| path | written by | mode | what |
| --- | --- | --- | --- |
| `DEPLOYMENT/checkpoint.key` | `mini bootstrap`, once | `0600` | 32 bytes from `/dev/urandom`: the Store's MAC key. Never printed, copied into another artifact, or committed. |
| `DEPLOYMENT/pinned-config.json` | the Host's `genesis` | `0600` (umask) | Operator configuration plus `expectedSeed` and `checkpointKey` (the key's absolute path). Optional `checkpointEvery` (default 64). |
| `STORE.head-anchor` | the store helper | `0600` | Independently retained exact genesis/deployment and head commitments; outside the Store directory. |
| `STORE.head-anchor.lock` | the store helper | `0600` | Serializes SQLite publication and anchor persistence; no history is stored here. |
| `STORE/forward-link.sqlite3` | the store helper | `0600` | SQLite, schema version 4. Tables: `durable_seed` (the genesis, once), `durable_log(height, record, tag)`, `durable_checkpoint(height, bytes)` (the latest two are kept), `archive_journal(seq, record, tag)` (the fn archive journal, `Kernel/FnArchiveJournal.lean`: signed articles before their first send, fn's acknowledgements and definite refusals, archive funding). |

`DEPLOYMENT` is the directory given to `mini bootstrap --dir`, and `STORE` is
the operator configuration's `storageRoot`.

## What the key means, and what it does not

The key authenticates exactly three things, all only for this Store.

- **Log tags.** Entry *h* carries `KMAC256(key, (keyId, h, chain_h))`, where
  `chain_h` is the log root. `chain_0 = logRoot0(domain, semantics, seed)`, and
  `chain_h = H(chain_{h-1} ‖ H(record_h))`.
- **Archive journal tags.** Journal entry *j* carries
  `KMAC256(key, (keyId, j, journal_j))` under its own customization
  (`DREGG/NATIVE-HOST/ARCHIVE-JOURNAL-TAG/v1`), where `journal_0` is derived
  from the deployment's domain and semantics and
  `journal_j = H(journal_{j-1} ‖ H(record_j))`.
- **Checkpoints.** A checkpoint carries
  `KMAC256(key, (keyId, height, worldRoot, H(body)))`. The body is the
  materialized state at that height together with the log root.

A valid MAC means that this Host executed and accepted this history. It does
not mean that every signed ingress was re-admitted. An attacker who can forge
the MAC can already forge this Host's receipts, so the key introduces no trust
that the receipt signatures do not already carry.

- **Loss of the key.** The Store refuses to open. The log and seed are intact,
  and nothing reinterprets them.
- **Rotation.** Stop the service. Replace `checkpoint.key` (mode `0600`). Then
  seal a checkpoint at the head under the new key (DATAMODEL §6 Q1).
  - The new checkpoint's log-root value vouches for every earlier entry.
  - Tags on later entries use the new key.
  - There is no rotation command yet. A Store opened under a key whose id
    differs from its latest checkpoint's refuses (`foreignKey`).

## Open, write, audit

- **Open.** Performed by `mini serve` and every Host command that reads state.
  1. Lock the sibling anchor; read the seed, latest checkpoint and entries in
     one SQLite transaction. Check the retained deployment/genesis identity and
     exact anchored prefix entry. A lower head, conflict or missing anchor refuses.
     A committed but unacknowledged extension may recover. Persist the current
     anchor before returning the read; the Lean checks below remain mandatory.
  2. Recompute the log root over every record.
  3. Open the checkpoint: its key id, recomputed world root, MAC, and log-root
     value at its height must all check.
  4. Verify every entry's tag against the chain at its height
     (`Compiler.DurableLogTags.verifyTags`); the first wrong one refuses by height.
  5. Materialize the checkpoint and replay only the records after it through
     the shared executor.

  No signed ingress is re-admitted. Every check refuses.
- **Write.** Each accepted operation appends one entry at `head + 1`; the
  helper refuses unless the head is still `head` and the anchor still matches.
  SQLite commits first; the helper then fsyncs a new anchor file, renames it and
  fsyncs its parent directory before returning success. The independent lock spans
  both publications. The Host reads that one entry
  back and confirms only on exact equality. Every `checkpointEvery` accepted
  records it seals a checkpoint. The served world root is a cached tree, so
  one write rehashes one path per written slot.
- **Audit.** `mini audit --host HOST --config PINNED.json` or
  `minidregg-host PINNED.json audit` runs the genesis re-admission.
  - Every retained signed ingress is re-admitted by its real receiver, at its
    original prefix height, with the signature helper, and compared record for
    record with the stored history.
  - The time grows with the whole history. It is an operator command, never
    the request path.
  - Run it after restoring a Store from backup, after key rotation, or on any
    doubt about the Host's past execution.

## What refuses to load

| condition | observable |
| --- | --- |
| missing anchor on a seeded Store | `durable head anchor refused: missing anchor; existing Stores require explicit audited enrollment` |
| Store truncated below retained head | `durable head anchor refused: Store is behind retained head` |
| deployment/genesis or same-height retained entry differs | `durable head anchor refused: genesis or retained head conflicts` |
| Store holds the retired whole-image record (`DREGG.DURABLE.IMAGE`, pre-C2) | helper exit 5, `store holds a retired whole-image record; re-genesis (no migration)` |
| key file missing or not exactly 32 bytes | `checkpoint MAC key unavailable` / `must be exactly 32 bytes` |
| checkpoint sealed under another key | `checkpoint refused: foreignKey` |
| checkpoint world root does not recompute | `checkpoint refused: rootMismatch` |
| checkpoint MAC wrong | `checkpoint refused: badMac` |
| checkpoint log-root value differs from the recomputed log root | `checkpoint does not match the log chain` |
| the stored entry count differs from the head | `durable log head does not match its entries` |
| any entry's tag wrong (an entry written or altered without the key) | `durable log entry tag refused at height H` |
| a record after the checkpoint no longer replays | `durable log suffix does not replay through the canonical executor` |
| log not rooted at this deployment's genesis log root | `log chain not rooted at this deployment's genesis` |
| a live session sees the log shrink | `durable log shrank beneath the session` (session poisoned) |
| the incremental world-root cache disagrees with a full rebuild | `world root cache disagrees with a full rebuild` (session poisoned) |

The helper never resets or rewrites anything implicitly. A forged or corrupt
entry stays visible to the operator.

## Store helper commands (opaque bytes; Lean owns all meaning)

```
minidregg-link-sqlite-store durable-init ROOT SEED                 # Installed | AlreadyPresent | exit 4
minidregg-link-sqlite-store durable-read ROOT FROM 0|1 OUTPUT      # exit 3: not initialized
minidregg-link-sqlite-store durable-append ROOT HEIGHT RECORD TAG  # Installed | AlreadyPresent | exit 4
minidregg-link-sqlite-store durable-checkpoint ROOT HEIGHT INPUT
minidregg-link-sqlite-store journal-read ROOT FROM OUTPUT          # exit 3: not initialized
minidregg-link-sqlite-store journal-append ROOT SEQ RECORD TAG     # Installed | AlreadyPresent | exit 4
```

`durable-append-crash … after-begin|after-insert|after-commit` is a lifecycle
test hook. The probe `scripts/probe-durable-receiver.sh` exercises every
command, both MAC poles, crash recovery and checkpoint resume.


## Independent head continuity and upgrade

The helper's `--anchor-identity ID` prefix binds its opaque anchor to the Host's
canonical `domain:D;semantics:S;seed:G` string. `D` and `S` come from
`minidregg-host PINNED.json profile`; `G` is `expectedSeed` in the pinned config.
`NativeHost.Config.transport` supplies this automatically. Generic byte-store
probes use the empty identity; this is not an alternate production identity.
Changing domain, semantics or genesis requires explicit lineage/re-enrollment,
not silently deleting the previous anchor.

The fixed 120-byte anchor contains `MINIANC2`, SHA256 of length-delimited opaque
identity and seed bytes with a domain separator, the big-endian u64 height, and
SHA256 of the exact height/length-delimited record/tag with a separate domain
separator, then the same pair for the head of the archive journal (u64 seq and
SHA256 of the seq/length-delimited record/tag under its own separator). At
height or seq zero the commitment names the empty entry. One anchor binds both
logs: a Store whose journal is behind its retained journal head, or holds a
different entry at that seq, refuses every read and write, the durable log's
included. A `MINIANC1` (80-byte, durable-log-only) anchor refuses by name:
`retired MINIANC1 anchor (durable log only); re-genesis (no migration)`. Rust does
not parse or re-admit these bytes. Lean's existing domain/genesis-rooted chain,
KMAC tags, checkpoint and replay checks continue to establish their meaning.
No extra full replay occurs on the normal path: only the retained and current
head entries are read for physical continuity.

A new genesis writes its initial anchor before committing the seed. An
interruption may retry exactly the same seed and identity. Existing seeded
Stores never auto-enroll, including height-zero Stores. Before upgrading an
existing service, stop all writers, preserve its database and key, audit with
the previously qualified Host/helper, compare any retained client evidence,
and deliberately enroll the observed head using the new helper:

```
minidregg-link-sqlite-store --anchor-identity 'domain:D;semantics:S;seed:G' durable-anchor-enroll STORE
```

Use the actual source-derived decimal identities, not the literal placeholders.
This command establishes trust in the operator-selected existing history; it
cannot prove freshness on its own. It refuses to overwrite a conflicting retained
anchor. Run the updated Host's audit before exposing the upgraded service.

If the process dies after SQLite commit but before anchor publication, the old
anchor must still match a prefix of the database. A read or exact retry retains
the committed head durably and succeeds. If it dies after rename but before the
directory fsync, a retry syncs the existing file and directory before returning.
An error after commit is still an uncertain result, never permission to submit
a different operation. Test hooks cover `after-begin`, `after-insert`,
`after-commit`, `after-anchor-prepare`, `after-anchor-rename`, and `after-anchor`.

For backups, stop the service and copy both the SQLite Store and its sibling
anchor. When moving the restored Store, put the copied anchor at the sibling
path of its resolved destination. Preserve any newer live anchor separately;
never overwrite it merely to make a historic backup open. A copied old database
with the newer anchor correctly refuses. Restoring an old database **and its old
anchor** cannot detect their joint rollback. Independent client receipt memory
and ultimately external witnesses address that stronger threat; a local file
is not a witness. Loss of the anchor needs explicit recovery evidence and an
operator enrollment decision. New storage paths and re-enrollment must not
silently reset clients' history.

Physical tests run real helper subprocesses killed at the publication boundaries,
then reopen/read/retry and replace the database with an older copy. They also
exercise row truncation above a checkpoint, same-height conflicts, foreign
genesis/domain, missing/replaced anchors, and concurrent appenders. This tests
process failure and exact-byte continuity; it does not prove filesystem/media
behavior during power loss or provide protection from an operator controlling
both the Store and retained anchor.
