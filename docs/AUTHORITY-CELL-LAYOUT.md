# The authority store's physical layout

State on `lane/authority-cells`: the layout, its lowering and its refinement are defined and
proved in `Compiler/CredentialAuthorityLayout.lean`. **No writer is migrated and the registry's
`.authority` payload has not flipped**: every record still carries the whole authority cell. The
measured growth below is therefore unchanged. The sections "Migrated", "Not migrated" and "Next
step" are exact.

## The problem (measured, four-replica fixture, 200 births)

Every record that writes authority state carries the whole authority cell. Its largest write is
1,324 B at height 1, 7,568 at 40, 20,377 at 120 and 33,185 at 200, inside records of 5,116,
11,366, 24,169 and 36,989 B; the ingress stays about 2,450 B.

The cause is the physical image only. The logical root is already a kept authenticated trie
(`CredentialAuthorityCell.materializer = PrivateCellRoot.materializer`, one path walk per write).
The physical write is `LifecycleImage.bytes (.live ⟨.authority, cell⟩)`: the canonical encoding of
the whole store (`ServedBasis.Ground.authorityWrite`, `CredentialAuthorityDomainReceiver.Loaded.write`).

## The layout

The logical authority `Store` over `CredentialAuthorityState.layout`, its patches and its logical
root are kept. Its physical image is:

| cell  | identifier                                              | payload                         |
|-------|---------------------------------------------------------|---------------------------------|
| HEAD  | `deployment.authorityCellId`                            | `head`, `[]`, the logical root  |
| ENTRY | `2^256 + cSHAKE256("DREGG.AUTHORITY.ADDRESS/v1", domain ‖ plane tag ‖ key bytes)` | `entry plane`, key bytes, value bytes |

Both are the registry's one `.authority` kind, whose payload is a `Kernel.ProtectedCell` cell (the
construction seat and activity cells already use) with `Role = head | entry plane`. There is no
new `Kind`: the law class (`kernelOnly authorityWriters`), `UserShape = False` and the observation
protocol's refusal of the authority role as a target cover the head and every entry by
construction.

A logical update lowers to `lowerAuthority`: the head write carrying the post logical root, then
one write per touched address carrying that address's post value, each guarded at its cell's
current root. The serving Host keeps its cached logical `Store` and applies the existing logical
patch to it; only this lowering is new. Semantic readers are not turned into IO.

## The six questions

1. **Which maps stay per-address?** All of them. Issuer epochs, policy epochs, subject-key epochs,
   policy revisions and addresses, capabilities, revocations, registrations, key records and parent
   rows are each one entry cell per key. The head holds the logical root and nothing else. The
   authority clock and the spent markers were never in the cell (durable height, durable consumed
   set) and stay out of the head.
2. **How is the head consistent with the entries?** `RealizesAuthority`: the head cell decodes to
   `rootOf logical`, and for every address `logical address = valueAt physical address`. Every
   content-changing patch writes the head. `lower_realizes` proves the lowering preserves it.
   `RealizesAuthority.unique`: the logical store is a function of the physical state.
3. **Logical free against physical retirement.** A logical `free` writes the entry cell with no
   payload. The cell stays live and the identifier is never retired, so a later lawful allocation
   at the same address writes the same cell (policy install's superseded address is the case).
4. **Collisions, placement, squatting.** An entry's payload carries its plane and key bytes;
   `valueAt` returns a value only when the payload names the address read (`Names`, injective:
   `Names.unique`). A touched address must be `Vacant` (its cell never used, or an authority cell
   whose payload, if any, names it); otherwise the update is refused by name,
   `LowerReject.coordinateOccupied` (`checkVacant`, `collision_refused`). Two addresses with equal
   coordinates are a cSHAKE256 collision on the `ADDRESS/v1` preimages, the one cryptographic
   assumption of the placement: a collision is a loss of liveness for that one address and no loss
   of safety. Every entry coordinate is at or above `ProtectedCell.reservedBase = 2^256` and every
   identifier a birth may choose is below it (`CanonicalCellRegistry.UserInitial`), so no user
   birth squats one. Placement of a loaded entry cell at its coordinate belongs in the registry's
   `LogicalLaw .authority` (owed with the flip).
5. **The complete read footprint.** A command that reads any authority address carries one read
   guard, on the head (`headReadGuard`). The head's root moves whenever the logical root moves, so
   a stale read of any entry is refused (`stale_authority_read_refused`); a guard that still
   matches pins the logical root (`head_guard_pins_root`, with the physical root's binding of the
   head's bytes as its one named premise). Authority writes stay serialised against authority
   readers exactly as under the one-cell layout: no regression and no new concurrency. Finer
   guards would be a separate change.
6. **"On demand" for a concrete `Store`.** Nothing is on demand in this change. The Host holds the
   logical `Store`; an open rebuilds it from the entry cells of the directory; a step applies the
   written entry cells to the held store. An IO-backed reader is a separate change.

## Statements (all in `Compiler/CredentialAuthorityLayout.lean`)

Proved (single-file check on hbox, no `sorry`, standard axioms only):

- `lower_realizes`: over a state that realises `logical`, an intent whose writes are
  `other ++ lowerAuthority …` at distinct cells, every touched address vacant, `post` equal to
  `logical` outside the touched set, and `Foreign other` (each other write is over a non-authority
  cell and leaves one), installs a state that realises `post`.
- `lower_frame`: addresses outside the touched set read the same from the physical state.
- `birthAuthorityWriteCount`: the birth's lowering has at most
  `1 + 3·|initialPolicies| + 2·|grants| + |parentRows|` writes.
- `birthAuthorityRealized`: the realisation and frame clauses at the birth's batch, under
  `ResourceBirthAuthority.BatchEvidence` (the authority part of every admitted birth).
- Teeth, over every state: `omitted_entry_refused`, `wrong_head_refused`, `false_value_refused`
  (false absence), `occupied_not_vacant`, `foreign_not_vacant`, `collision_refused`. A stale guard
  is the existing preflight (`stale_read_guard_rejected`, and each write's `expectedPre`).

Stated, proof owed:

- `BirthAuthorityWriteBytes`: the encoded bytes of the birth's lowered writes are at most
  `authorityBirthBudget.maxEncodedBytes`, a closed function of the envelope's constant, the head
  identifier and the descriptor's entries through the codecs (`authorityBirthBudget_userPart`: the
  kernel's auxiliary allocations do not enter it). It counts write framing, both roots of each
  write and the head write as constants. It needs the base-255 natural codec's length to be
  monotone, digests below `2^256`, and the cell codec's length.
- `BirthAuthorityWritesBounded` is the conjunction of the three clauses.

Owed and not claimed:

- The tie of `other ++ lowerBirth …` to `ResourceBirthReceiver.intent` (the birth's migration).
- Non-vacuity as a construction: for every k, a reachable state with at least k unrelated
  entries and an admitted birth of a fixed descriptor shape meeting the same budget. Its executed
  instance is the migrated 200-birth fixture (heights 1, 40, 120, 200).
- An executed collision witness under a toy coordinate (the coordinate is not yet a parameter).
- **The complete-record bound is not claimed and is false today: the Book and the factory cell are
  written whole by every birth, so a birth's record still grows with unrelated Book entries.**

## Where the code differs from the review and the brief

- Sixteen families write authority, not five: `CanonicalCellRegistry.authorityWriters`. They reach
  the write through two functions, `ServedBasis.Ground.authorityWrites` and
  `CredentialAuthorityDomainReceiver.Loaded.writes`. Those two are the migration points.
- The review proposed a new entry role in every kind table; one kind with a role inside its
  payload needs no table row and cannot leave a table out.

## Migrated

Nothing.

## Not migrated

- The registry: `layout`, `materializer`, `wire?`, `privateWire?`, `schemaRef` and
  `LogicalLaw` of `.authority` (payload becomes `ProtectedCell.layout spec`; the law becomes head
  at the pinned id, entry at its coordinate with a decodable key and value).
- The `Envelope` instance (`LifecycleImage.bytes registry (.live ⟨.authority, cell⟩)` and its
  decode), replacing `cellBytes`, `decodeCell`, `cellRoot`, `packedCell`.
- `Loaded` (`observed` becomes `RealizesAuthority`), `loadDeployment` (an open folds the
  directory's entry cells into a store and checks the head), `loadDeploymentFromAt` and
  `ServedAuthority.adopt` (a step clears each written cell's old address and sets its new one in
  the held store, then checks the head), `HeldCell`.
- `Ground.authorityWrites` and `Loaded.writes` (take the touched addresses and return
  `lowerAuthority`), `authorityReadGuard` (the head), and all sixteen families' proofs about the
  one write (`writes_single`, `installed_authority`, the candidate layouts' one authority leg).
- The issuer locator (`issuerCheck`, `issuedOf`, `Snapshot.issued`), `policiesSourced` and
  `sourcesUnwritten`, `ReceivingLaw.birthRoom`.
- Fixtures, seeds, the `append-flatness` row.

## What moves when the registry flips (a re-genesis)

- Cell payload of kind tag 3: from the `minidregg/credential-authority/v6` store frame to the
  frame `minidregg/credential-authority-cell/v7`, wire version 7; `schemaRef .authority` from
  `⟨91003, 8⟩` to `⟨91003, 9⟩`.
- New cSHAKE customizations: `DREGG.AUTHORITY.ADDRESS/v1` (coordinate),
  `DREGG.AUTHORITY.CELL.ROOT/v1` (cell root).
- `logicalLawVersion` (`registry_loaded_and_final_store_cells_v17`) to v18.
- Every seed's cells (one authority cell becomes a head and one entry per address), hence the
  world root at every height, the log start, the consensus anchor and every checkpoint.
- A store of the old layout is refused by name: the v6 store frame at the head identifier does
  not decode as a v7 cell (owed: the theorem, in the pattern of
  `retired_capability_v2_frame_refused`).

## Next step

1. Prove `BirthAuthorityWriteBytes`.
2. Flip the registry's `.authority` payload and instantiate `Envelope`; rewrite `Loaded` and the
   two write functions over `lowerAuthority`. From that commit the tree is red until all sixteen
   families compile, so it is one change: birth first (`ResourceBirthController.planWrites`,
   `PreparedPostAuthority`), then the thirteen other `Ground.authorityWrites` callers, then the
   `Loaded.writes` callers.
3. Issuer locator; `policiesSourced` by changed policy coordinates; `birthRoom` reads the
   parent-address post.
4. Re-genesis; whole build; the tour; `append-flatness` as a raw bound with the four numbers.
