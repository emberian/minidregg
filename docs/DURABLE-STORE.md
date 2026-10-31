# The durable Store: interfaces an operator depends on

Present-state contract for `native/hyperdocument-link-sqlite-store` (schema 5,
`src/lib.rs:603`). One Mini Store is one
directory (`storageRoot` in the operator configuration), one MAC key file, and
an independently retained **sibling head anchor** that lives *outside* the
Store directory. Back up the anchor with the Store or a restore refuses (see
"Backup and restore"). Anything not listed here is not part of the contract.

## Files

| path | written by | mode | what |
| --- | --- | --- | --- |
| `DEPLOYMENT/checkpoint.key` | `mini bootstrap`, once | `0600` | 32 bytes from `/dev/urandom`: the Store's MAC key. Never printed, copied into another artifact, or committed. |
| `DEPLOYMENT/pinned-config.json` | the Host's `genesis` | `0600` (umask) | Operator configuration plus `expectedSeed` and `checkpointKey` (the key's absolute path). Optional `checkpointEvery` (default 64). |
| `STORE/forward-link.sqlite3` | the store helper | `0600` | SQLite, **schema version 5** (`PRAGMA user_version`), write-ahead log (`journal_mode=WAL`, `synchronous=OFF`). Tables below. |
| `STORE/forward-link.sqlite3-wal` | the store helper | `0600` | The write-ahead log: committed transactions not yet checkpointed into the database file. **Part of the database.** Kept after the last connection closes (persistent WAL), truncated to empty whenever it is reset. |
| `STORE/forward-link.sqlite3-shm` | the store helper | `0600` | The WAL index (shared memory). Rebuilt from the `-wal` when needed; every process that opens the Store must be able to write it, so all of them run as the Store's account. |
| `STORE.head-anchor` | the store helper | `0600` | The 120-byte `MINIANC2` anchor: exact deployment/genesis identity and the heads of both logs. In the Store's **parent** directory. |
| `STORE.head-anchor.lock` | the store helper | `0600` | `flock` that serializes SQLite publication and anchor persistence; holds no history. |
| `STORE.head-anchor.PID.N.tmp` | the store helper | `0600` | A crash between create and rename leaves one; it is inert and may be removed with the service stopped. |

The anchor's directory (the Store's parent) must be owned by the Store's
account or root and writable by no other account (or sticky); the anchor file
must be the Store account's with no group or other bits. A systemd
`StateDirectory=` parent (root `0755`) satisfies this.

### Schema 5

| table | shape | mutability |
| --- | --- | --- |
| `durable_seed` | `slot=1 → bytes` (≤ 64 MiB) | the genesis, written once |
| `durable_log` | `height → (record, tag)` | append-only at `head + 1` |
| `durable_node` | `(space, key, height) → value` (key, value ≤ 4096 bytes) | the history accumulator nodes (`Compiler.DurableHistory`), written in the same transaction as their entry, never rewritten |
| `durable_checkpoint` | `height → bytes` (≤ 64 MiB) | **every checkpoint is kept**; re-sealing at an existing height (a key rotation) replaces that row only |
| `archive_journal` | `seq → (record, tag)` | the fn archive journal (`Kernel/FnArchiveJournal.lean`), append-only at `head + 1` |
| `opaque_record` | `slot=1 → bytes` | the legacy one-slot link record (`cas`, `read-to`) |

### Durability contract

The helper publishes the anchor (rename) before it answers. A committed record may live only in
`-wal` until the next checkpoint folds it into the database file, so **the
database is the database file together with its `-wal`** (and `-shm`, which is
rebuildable). A process killed right after `COMMIT` leaves the record in
`-wal`; the next open recovers it exactly
(`native/hyperdocument-link-sqlite-store/tests/durable_anchor.rs::a_crash_after_commit_keeps_the_record_in_the_wal`).

A Store written by an older helper (rollback journal) enters WAL mode on its
first open; that open needs a writable disk once.

Opening schema 0 upgrades it in one transaction (the legacy BLOB is kept); an
unseeded v2–v4 Store gains the durable tables; a **seeded v2–v4 Store refuses**
(`RetiredSchema`, exit 5: re-genesis, no migration). Opening a current Store
takes no write lock and writes nothing.

Checkpoints: the Host opens from the latest one; `durable-checkpoint-at H`
reads the latest at or below `H` (history views). Nothing prunes them (the
only write is the upsert by height at `native/hyperdocument-link-sqlite-store/src/lib.rs:1386`, and no
code path deletes a `durable_checkpoint` row), so the table grows by one row per `checkpointEvery` records.

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
  seal a checkpoint at the head under the new key (the trust it rests on: `docs/NATIVE-HOST.md:64`).
  - The new checkpoint's log-root value vouches for every earlier entry.
  - Tags on later entries use the new key.
  - There is no rotation command yet. A Store opened under a key whose id
    differs from its latest checkpoint's refuses (`foreignKey`).

## Open, write, audit

- **Open.** Performed by `mini serve` and every Host command that reads state.
  1. Lock the sibling anchor; read the seed, latest checkpoint and entries in
     one SQLite transaction. Check the retained deployment/genesis identity and
     the exact anchored entry of each log. A lower head, a conflict or a
     missing anchor refuses. A committed but unacknowledged extension recovers.
     The read then brings the anchor up to the head it read; on a full or
     read-only disk it answers anyway (the anchor it verified is never ahead of
     the head, so a lagging anchor loses nothing and the next write repairs it).
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
  SQLite commits first; the helper then renames a new anchor file into place
  before returning success. The lock spans both
  publications. The Host reads that one entry back and confirms only on exact
  equality. Every `checkpointEvery` accepted records it seals a checkpoint.
- **Audit.** `mini audit --host HOST --config PINNED.json` or
  `minidregg-host PINNED.json audit` runs the genesis re-admission: every
  retained signed ingress is re-admitted by its real receiver at its original
  prefix height and compared record for record. Its time grows with the whole
  history; it is an operator command, never the request path. Run it after a
  restore, after key rotation, or on any doubt about the Host's past execution.

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

The helper never resets or rewrites anything implicitly. A forged or corrupt
entry stays visible to the operator.

## Store helper commands (opaque bytes; Lean owns all meaning)

`minidregg-link-sqlite-store [--anchor-identity ID] VERB ...`, one-shot or as
frames to its `serve` coprocess (`Compiler.NativeCoprocess`; reply tag
`MDCOPRC1`). The production binary has only these verbs:

```
durable-init ROOT SEED                       # Installed | AlreadyPresent
durable-read ROOT FROM 0|1|2 OUTPUT          # 2: the open's read (base + entries from the checkpoint)
durable-history ROOT REQUEST OUTPUT
durable-seed ROOT OUTPUT
durable-append ROOT HEIGHT RECORD TAG NODES  # Installed | AlreadyPresent
durable-checkpoint ROOT HEIGHT INPUT
durable-checkpoint-at ROOT HEIGHT OUTPUT
durable-anchor-enroll ROOT                   # operator only, see below
journal-read ROOT FROM OUTPUT
journal-append ROOT SEQ RECORD TAG           # Installed | AlreadyPresent
read ROOT | read-to ROOT OUTPUT | publish ROOT INPUT | cas ROOT EXPECTED|- INPUT   # legacy one-slot record
database-path ROOT                           # tamper probes
serve
```

| exit | meaning | the Host reads it as |
| --- | --- | --- |
| 0 | success (stdout `Installed` / `AlreadyPresent` for writes) | success |
| 2 | usage (an unknown verb, wrong arity) | uncertain |
| 3 | absent (not initialized, no record) | absent |
| 4 | **CAS conflict** only: the head moved, or a different entry is at that height | conflict: reload and recompute |
| 5 | retired image or schema (re-genesis) | uncertain |
| 6 | **bound violation**: height or seq 0, a tag, node key or node value over 4096 bytes, more than 4096 nodes, duplicate node keys. The same bytes never succeed | uncertain today (`DurableReceiverCore.parseCasOutput`); Lean ask: a distinct refused outcome |
| 7 | **disk refused a write**: full (`ENOSPC`, `EDQUOT`, `SQLITE_FULL`) or read-only (`EROFS`, `SQLITE_READONLY`) | uncertain today; Lean ask: report it as such, never as absent |
| 1 | anything else (opaque SQLite or filesystem failure, anchor refusal) | uncertain |

Exit 4 is reserved for a real CAS conflict, so a codec that produces an
over-long tag does not reload and retry (`tests/durable_anchor.rs`,
`an_append_over_a_bound_exits_six_not_conflict`). The crash and hold fixtures
are not verbs of this binary: they live in `tests/support` and run from the
crate's test binaries, and as a process in the separate
`minidregg-link-sqlite-store-fixtures` binary, built only with
`--features fixtures` for the Lean probe `scripts/durable-receiver.lean`
(`Cargo.toml`, `src/bin/fixtures.rs`); never ship that binary.
`Compiler/DurableReceiverCore.lean`'s `append … crashAt` parameter
(`:234-261`) drives only the fixtures binary; production passes `none`.

## Independent head continuity and upgrade

The helper's `--anchor-identity ID` prefix binds its opaque anchor to the Host's
canonical `domain:D;semantics:S;seed:G` string. `D` and `S` come from
`minidregg-host PINNED.json profile`; `G` is `expectedSeed` in the pinned config.
`NativeHost.Config.transport` supplies this automatically. Generic byte-store
probes use the empty identity; this is not an alternate production identity.
Changing domain, semantics or genesis requires explicit lineage/re-enrollment,
not silently deleting the previous anchor.

The fixed 120-byte anchor contains `MINIANC2`, SHA-256 of length-delimited
opaque identity and seed bytes with a domain separator, the big-endian u64 log
height and SHA-256 of the exact height/length-delimited record/tag under its own
separator, then the same pair for the archive journal's head. At height or seq
zero the commitment names the empty entry. One anchor binds both logs: a Store
whose journal is behind its retained journal head, or holds a different entry
at that seq, refuses every read and write. A `MINIANC1` (80-byte) anchor refuses
by name (re-genesis). The digests are unkeyed: custody of the file is the only
protection, which is why the custody checks above are enforced. Rust does not
parse or re-admit the records; Lean's chain, KMAC tags, checkpoint and replay
checks establish their meaning.

A new genesis writes its initial anchor before committing the seed. An
interruption may retry exactly the same seed and identity. A seed commit that
fails for a non-crash reason (a full disk) leaves an anchor naming a genesis
the database lacks: reads report absent while the anchor exists, and recovery
is the operator's (remove the anchor with the service stopped, or enroll).
Existing seeded Stores never auto-enroll. To adopt an existing Store under a
new helper (or after losing the anchor), stop all writers, preserve the
database and key, audit with a qualified Host, and deliberately enroll the
observed head:

```
minidregg-link-sqlite-store --anchor-identity 'domain:D;semantics:S;seed:G' durable-anchor-enroll STORE
```

Use the actual decimal identities, not the placeholders. Enrollment trusts the
operator-selected history; it cannot prove freshness. It refuses to overwrite
a conflicting retained anchor. Run the Host's audit before serving.

If the process dies after the SQLite commit but before anchor publication, the
old anchor still matches a prefix of the database; a read or exact retry
retains the committed head and succeeds. An error after commit is an uncertain result, never permission to
submit a different operation.

## Backup and restore

- **Online (the service running): SQLite's online backup API**, which reads
  through the WAL, so the snapshot holds every committed transaction and is one
  self-contained file (run it as the Store's account so any `-wal`/`-shm` it
  creates belongs to that account). Never `cp` the database file of a live
  Store: it can miss the committed transactions still in `-wal`. The helper
  takes no backups. `mini-backup` and `mini-restore-check` belong to
  dregg-infra, not to this repository (named at `deploy/shell/OPERATOR.md:80-81`
  and `deploy/door/infra/dregg-infra.patch:213`; the script is not in the
  tree). The commit that moved the Store to WAL (`43ede087`) records a hand
  check, against the system sqlite3, that the online `.backup` captures a
  record present only in `-wal`; no repository test covers the backup path.
  The demo box pushes to an Object Lock bucket and runs the restore check
  (`docs/DEMO-PREFIX-2026-10-26.md:77`, a recorded run, not a property of this
  crate).
- **A Store restored or moved to another root is another Store to the grain
  platform.** `storeTag` is the tag of the Store identity
  (`Config.storeIdentity`, `Kernel/NativeHostStoreIdentity.lean`: the genesis
  seed at `storageRoot`), so a copy opened from a different `storageRoot` names
  fresh resident units, volumes and a fresh grain world and adopts none of the
  original's residue, by construction, with no nonce to mint. A world template
  restored under a new root therefore needs nothing beyond the path rewrite.
- **Cold (the service stopped): copy the database file, its `-wal` and its
  `-shm` together** (or first run `PRAGMA wal_checkpoint(TRUNCATE)` as the
  Store's account, after which the database file alone is whole). A cold copy
  without `-wal` can restore to an older state silently.
- **Either way, copy the sibling `STORE.head-anchor` with it.** The anchor is
  outside `STORE/` on purpose (a directory-only copy of the Store would
  otherwise carry its own anchor), so a backup of `STORE/` alone restores to a
  Store that refuses: `missing anchor; existing Stores require explicit audited
  enrollment`. A snapshot of the database taken while the service runs is at
  or ahead of an anchor copied before it, never behind; copy the anchor first
  or stop the service.
- Back up `checkpoint.key` separately; without it the Store refuses to open.
- When restoring to a new path, put the copied anchor at the sibling path of
  the resolved destination, and do not carry a stale `-wal` or `-shm` from
  another copy into it. Preserve any newer live anchor separately; never
  overwrite it to make a historic backup open. An old database with the newer
  anchor correctly refuses.
- Freezing a retired Store (`ship.sh --regenesis`, `deploy/shell/OPERATOR.md:63`):
  checkpoint with `TRUNCATE` (`wal_checkpoint`, `src/lib.rs:547`) and set
  `journal_mode=DELETE` before making it read-only, so no `-wal` remains and
  it can be read `immutable=1`. `ship.sh` is dregg-infra's.
- Restoring an old database **and its old anchor** together cannot detect the
  joint rollback. Client receipt memory and external witnesses address that;
  a local file is not a witness.

## Guarantees and what backs them

"exists" means code with a crate or Lean test; "proved" means a Lean theorem
(not a statement about SQLite, the filesystem or media); "journeyed" means a
recorded run, none of which is claimed here unless named.

| guarantee | backing | word |
| --- | --- | --- |
| an acknowledged write survives a kill at every publication boundary | `killed_publisher_recovers_before_and_after_commit_and_anchor`, `crash_after_commit_reopens_exact_and_retry_is_idempotent` | exists (process kills, not power loss) |
| a record committed only to `-wal` is recovered | `a_crash_after_commit_keeps_the_record_in_the_wal` | exists |
| concurrent appenders cannot fork the log or anchor | `concurrent_publishers_serialize_anchor_with_commit`, `concurrent_cas_writers_cannot_both_replace_the_same_preimage` | exists |
| a rolled-back or foreign database refuses | `genesis or retained head conflicts` and missing-anchor cases in `tests/durable_anchor.rs` | exists |
| bound violations exit 6, a read needs no writable disk, a refused write is typed (7) | `an_append_over_a_bound_exits_six_not_conflict`, `a_read_needs_no_writable_disk_and_a_refused_write_is_typed` | exists |
| the production binary has no crash or hold verb | `serve_answers_in_process_and_the_production_binary_has_no_crash_verbs` | exists |
| the first wrong log tag is named; a valid chain verifies | `Compiler/DurableLogTags.lean`: `verifyTags_ok_iff`, `verifyTags_refuses_at`, `verifyTags_refuses_head` | proved |
| history accumulator entries verify against their frontier | `Compiler/DurableHistory.lean`: `verifyAt_sound`, `verifyAt_refuses` | proved |
| cold reopen, MAC chain, checkpoints and replay together | `scripts/durable-receiver.lean` | exists (a probe; no recorded journey cited here) |
| the anchor detects a joint rollback of database and anchor | none | not provided |

## Dependencies and tests

The helper links the system `libsqlite3` through a hand-written FFI (no
rusqlite) and depends on `sha2` (anchor digests) and `libc` (`flock`,
`geteuid`, `O_NOFOLLOW`). `build.rs` creates a private linker alias when only
`libsqlite3.so.0` is present (x86_64 and aarch64 Debian paths).

The tests run real helper processes killed at every publication boundary
(`after-begin`, `after-insert`, `after-commit`, `after-anchor-prepare`,
`after-anchor-rename`, `after-anchor`), then reopen, read, retry and replace
the database with an older copy; they cover truncation above a checkpoint,
same-height conflicts, foreign genesis, missing and replaced anchors,
concurrent appenders, bound violations (exit 6) and a read with an unwritable
Store directory, and a record committed only to the WAL surviving a kill
after `COMMIT`. They test process failure and exact-byte continuity, not
filesystem or media behaviour under power loss, and not an operator who
controls both the Store and its anchor.
