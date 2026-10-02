# The durable Store: interfaces an operator depends on

One Mini Store is one directory (`storageRoot` in the operator configuration)
plus one key file. This page lists what the Host and its store helper read,
write and refuse there. Anything not listed is not part of the contract.

## Files

| path | written by | mode | what |
| --- | --- | --- | --- |
| `DEPLOYMENT/checkpoint.key` | `mini bootstrap`, once | `0600` | 32 bytes from `/dev/urandom`: the Store's MAC key. Never printed, copied into another artifact, or committed. |
| `DEPLOYMENT/pinned-config.json` | the Host's `genesis` | `0600` (umask) | Operator configuration plus `expectedSeed` and `checkpointKey` (the key's absolute path). Optional `checkpointEvery` (default 64). |
| `STORE/forward-link.sqlite3` | the store helper | `0600` | SQLite, schema version 3. Tables: `durable_seed` (the genesis, once), `durable_log(height, record, tag)`, `durable_checkpoint(height, bytes)` (the latest two are kept). |

`DEPLOYMENT` is the directory given to `mini bootstrap --dir`, and `STORE` is
the operator configuration's `storageRoot`.

## What the key means, and what it does not

The key authenticates exactly two things, both only for this Store.

- **Log tags.** Entry *h* carries `KMAC256(key, (keyId, h, chain_h))`, where
  `chain_h` is the log root. `chain_0 = logRoot0(domain, semantics, seed)`, and
  `chain_h = H(chain_{h-1} ‖ H(record_h))`.
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
  1. Read the seed, the latest checkpoint and every log entry in one SQLite
     transaction.
  2. Recompute the log root over every record.
  3. Open the checkpoint: its key id, recomputed world root, MAC, and log-root
     value at its height must all check.
  4. Verify every entry's tag against the chain at its height
     (`Compiler.DurableLogTags.verifyTags`); the first wrong one refuses by height.
  5. Materialize the checkpoint and replay only the records after it through
     the shared executor.

  No signed ingress is re-admitted. Every check refuses.
- **Write.** Each accepted operation appends one entry at `head + 1`; the
  helper refuses unless the head is still `head`. The Host reads that one entry
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
```

`durable-append-crash … after-begin|after-insert|after-commit` is a lifecycle
test hook. The probe `scripts/probe-durable-receiver.sh` exercises every
command, both MAC poles, crash recovery and checkpoint resume.
