# Portable continuation and archive repair

Mini's portable home is the existing multiuser source world plus its actual
service/custody obligations. It is not a restored app counter. Workshop, shared
worlds, continuing residents, SPK services and Bend computations are consumers.

Lean owns the source binding and continuity decision. The native archive only
retains, compares, reconstructs and repairs exact bytes. It does not install a
world, select authority, replace a provider, export secret shares, or prune logs.

## Additive source and current consumers

- `Kernel/PortableContinuationManifest.lean`: complete source identity/prefix,
  exact durable image and opaque physical inventory; participant pin and public
  ACK continuity; nonregression/chain-binding laws; typed one-generation-ahead
  reconciliation; explicit source/private/fence successor obligations.
- `Compiler/PortableContinuationManifestCodec.lean`: canonical framed codec,
  exact complete-image binding using `DurableReceiverCodec`, public ACK frame.
- `Compiler/PortableContinuationArchiveIO.lean`: same chunk mechanics for every
  source-selected physical artifact and the private manifest. All artifacts and
  the whole canonical manifest are read back before opaque custody can accompany
  participant ACK signature verification. Helper runs from a SHA-pinned private
  executable snapshot. Public ACK discloses no source cells or holder inventory.
- `Host/PortableContinuationInspection.lean`: actual
  `NativeHostSession.startWalked` captures the whole admitted image; restored
  independent Store must re-admit under the original source configuration and
  match the entire canonical image and endpoint.
- `native/portable-archive`: private 64KiB chunks, exact position/length/hash,
  untrusted-provider repair and bounded ranges; new-output-only reconstruction;
  streaming stable-lock CAS with file+directory fsync and uncertain-reply replay.
  Agreement's owner is adding a storage-only helper selector, retaining the
  independent crypto/network helper and its physical frame limit.

## Source-owned inventory and current-authority joins still required

The caller cannot decide completeness by supplying a convenient empty inventory.
Service must derive its capture from the existing settled pause/driver lock and
full inventory: exact SPK/package/config/runtime/profile, physical journals and
volumes, resident request/notices/start/maintenance state, pending provider holds,
completion and delivery records. The complete native image already retains all
logical modules/currentrefs/notes/cells/nullifiers/charges/admitted events.

Joint receiver must derive still-owed control frame/reservation/decision/repair
outbox and historical roster/configuration/seed retention from CURRENT source
state. `Preserves required` checks exact inventories, but `required` must come
from that native source closure. No unproved ACK flag authorizes overwrite.

Private backend must carry complete old Generation, exact descriptor,
WAL/event/outbox prefix, immutable pool-row identity and independent monotonic
spent anchors. A signed stale snapshot is not freshness. No share-generation
mixing, tombstone reset, private-world export or proactive erase/rekey proof is
provided by byte custody. Its actual Qualified adapter remains a required join.

Successor activation additionally needs actual current-source governed decision,
private-generation qualification where applicable, and an old physical worker
fence. The generic ReadySuccessor proof fields explicitly state these separate
obligations; no concrete current-source constructor is yet supplied here.
Uncertain external calls carry exact original custody and remain uncertain until
the existing provider/completion/delivery receiver resolves them. Restoration
cannot rerun them merely because it starts in a new directory.

## Meaning of evidence

General named laws and native crash/repair tests are separate from live service
qualification. Lean modules remain QUEUED UNCOMPILED. Native exact source r1 passed all five
release nextest tests (zero skipped, 0.174 seconds) and release helper build on
Persvati under 8GiB/no swap/CPU200% supervised lease. Source tar SHA256
`32af5f3be155dfb9cca7f3505db2e73ac95777041c6eb2e3659295bf528f877a`;
helper SHA256 `fe36b0d716190761291d7248572e549346c8d33be50a10e6d7ddd4399beb1567`.
These are physical component cases, not a qualified whole-home transfer. The
agreement owner is joining the actual source Storage consumer next.
Registration/common receiving is owned by the kernel captain. No activation,
actual cross-provider replacement, asset operation or private secret export is
inferred from this source.

Tests are source-authored to exercise >16MiB exact storage at the last byte,
lost durable reply followed by exact reopen/retry conflict, stale/symlink
refusal, unavailable chunk repair, wrong-position/forged chunk refusal,
bounded cross-chunk retrieval and refusal to overwrite an existing source.
These do not establish full SPK home transfer or malicious private portability.

## Lifetime boundary

The agreement journal keeps its exact canonical meaning; streaming physical CAS
removes the accidental network-frame cap on whole storage. Lean storage.read and
journal replay still materialize the whole journal, and logical BFT messages may
carry full ancestry. Bounded logical transfer/MAC processing and streaming replay
remain agreement-consumer joins. Safe checkpoints must retain all old-view and
outstanding obligations under actual proofs. This module grants no pruning.
