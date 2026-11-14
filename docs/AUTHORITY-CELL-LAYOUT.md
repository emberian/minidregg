# The authority cell's physical layout: a design, not built

The ordered append grows with the number of births (docs/GENERIC-SIMPLEX-NATIVE.md, "Still
growing with the history"). The cause is the credential authority cell: one physical cell
that holds every stored capability and is rewritten whole by every birth. This is the design
of the fix. Nothing of it is built. It was written from a partial reading (below) and must
be checked against the unread files before a line is built.

## What is there (read)

- `CredentialAuthorityDomain.Cell` (= `CredentialAuthorityCell.Cell`) is a keyed store
  (`cell.logical.keys`, addresses such as `⟨.capability kind, identifier⟩`,
  `readCapability cell kind identifier`) serialised as one physical cell:
  `cellBytes cell = LifecycleImage.bytes registry (.live (packedCell cell))` at
  `cellIdOf deployment = ⟨deployment.authorityCellId⟩`
  (Compiler/CredentialAuthorityDomainReceiver.lean, lines 61 to 77).
- A record's `DataWrite.canonicalPostBytes` is the whole post cell.
- `issuedOf domain cell = cell.logical.keys.filterMap (issuedEntry domain cell)` hashes every
  stored capability. `Snapshot.issued` is a thunk rebuilt for each changed cell. Its one
  reader is `issuerCheck`: `snapshot.issued.get.contains (issuer, epoch, commitment)`
  (Compiler/CredentialAuthorityPolicyRegistry.lean, line 284).
- Measured (200 births, four Stores, hbox, two runs): the record is 5,116 bytes at height 1
  and 36,989 at 200; its largest write is to cell 12, the fixture's `authorityCellId`, and
  is 1,324 bytes at height 1 and 33,185 at 200 (160 bytes per birth); the ingress stays
  about 2,450 bytes. The application hand-off was 57, 100 and 531 ms at heights 1, 40 and
  200 in one run and 117, 104 and 213 ms in the other (a shared box).

## Not read

- Compiler/CredentialAuthorityCell.lean (the cell itself).
- The patch and `Prepared` proofs in Compiler/CredentialAuthorityDomain.lean (579 lines).
- Compiler/CredentialAuthorityDomainReceiver.lean beyond the lines cited (1,125 lines).
- Compiler/CredentialAuthorityServed.lean.
- Every family that writes the cell: birth, delegation, revocation, policy install, key
  rotation.

## Design: one physical cell per store address

Delta writes are ruled out: a record that carries a write as a delta makes a cell's bytes a
function of history, which breaks `DataSnapshot.canonicalBytes`, exact readback and the root
cache's one-path-per-written-cell update, all of which assume a write carries the cell.

1. Physical layout. The authority store keeps its logical type and every logical theorem.
   Its physical image becomes a head cell at `authorityCellId` holding only the bounded
   fields (roots, epochs, revision), and one physical cell per store address, at
   `CellId = cSHAKE("DREGG.AUTHORITY.ADDRESS/v1", domain ‖ authorityCellId ‖ address bytes)`,
   holding that address's value under a new lifecycle role (say `.authorityEntry`). A
   capability, a revocation mark and a policy row each live in their own cell.
2. Writes. A patch over the logical store compiles to one `DataWrite` per touched address,
   plus the head when a bounded field moves. A birth that issues two capabilities writes the
   born cell, two entry cells, and whatever head field it advances.
3. Reads. `readCapability` and the other key-by-key readers become
   `snapshot.canonicalBytes (addressCell address)` decoded on demand. `LoadedDirectory` and
   `Loaded` hold the head and decode entries lazily. Nothing enumerates the store on a
   request.
4. `issuedOf` is deleted, not maintained. `issuerCheck` asks whether a triple
   (issuer, epoch, commitment) is the triple of some stored capability; with per-address
   cells that needs the capability's address. Either the evidence already names the
   capability id (then it is one cell read and one hash), or it does not and an index cell
   keyed by the commitment is written beside each capability (one more constant write per
   issue).
5. What moves. The record bytes of every family that writes authority state (the write list
   changes). The world root at every height including genesis (the seed's cells change: one
   authority cell becomes a head and entries), hence `expectedSeed`, the log start, the
   consensus anchor and every checkpoint: a re-genesis. `Image.cellIds` grows by one id per
   address ever written, which is the existing shape for born cells.
6. The bound, the keystone to state before proof work (the names are proposals):
   `BirthWritesBounded`: for every opened state and every admitted birth descriptor `d`,
   `(recordFrame.encode (IntentRecord.ofIntent intent)).length ≤ B d` and
   `intent.writes.length ≤ W d`, where `B` and `W` are functions of the descriptor alone
   (its born items and grants), with no term in the store's key count.
   - Satisfiable: the fixture's birth at height 1 and at height 200 produce records of equal
     length (executed, exact equality of the two lengths).
   - Teeth: the present encoding, where the two lengths differ by 160 bytes per birth (the
     falsifying instance of the same statement on the old layout).
   - Premise inhabitation: the fixture's genesis and its admitted birth.
   The work half is not a theorem about time. It is the gate: `append-flatness`
   (`minidregg-four-source-fixture`, row `four-source-flat` of
   scripts/gates/check-generic-simplex) judged on raw hand-off time, the last window at most
   twice the first over 200 heights. Today the row judges time per KB of appended record,
   because a raw-time bound is red on the present layout.
7. Order of work: read the unread files; settle the first open question; write the
   address-cell codec and the `Prop`; port `Loaded`, `LoadedDirectory` and
   `validateLoadedStep` (already per written cell, which is why it ports); port each writing
   family; re-genesis the fixtures; make the flatness row a raw-time bound.

## Open questions

1. Does `issuerCheck`'s evidence name the capability id? It decides between one cell read
   and an index cell keyed by the commitment (point 4). Read
   Compiler/CredentialAuthorityPolicyRegistry.lean first.
2. The lawful role for entry cells. The cell law (`cellsLawful`) and policy sourcing
   (`policiesSourced`, `holdsNoPolicySource`) walk `LoadedDirectory`. Both are already
   incremental over written cells, but each new entry cell needs a lawful role, and the
   source-holding predicate must keep seeing policy rows once they are cells of their own.

## A second, smaller cost on the same path

`ExactReadback.ofAppended` (Kernel/NativeHostReplay.lean) runs `Loaded.prepare` and
`Loaded.extend` again on the image the receiver already extended
(`DurableReceiverIO.Appended.next`), so every byte of the record is encoded and hashed
twice. Reusing the receiver's extended image needs `Appended` to carry that it is the
`extend` of the prepared `Ready` (it may also have been rebased by a due checkpoint). Not
done.
