# The authority store's physical layout

State on `lane/authority-cells`: the registry's `.authority` kind is the cell layout and every
writer family and reader is ported to it. **The whole build is not yet green on this head**: the
section "Build state" names what is verified and what is not. Nothing here is landable until
that section says the whole build, the Host and the gates pass.

## The problem (measured before the change, four-replica fixture, 200 births)

Every record that wrote authority state carried the whole authority cell. Its largest write was
1,324 B at height 1, 7,568 at 40, 20,377 at 120 and 33,185 at 200, inside records of 5,116,
11,366, 24,169 and 36,989 B; the ingress stayed about 2,450 B. The other writes of those records
summed to about 3,800 B at every height.

The cause was the physical image only. The logical root was already a kept authenticated trie
(`CredentialAuthorityCell.materializer = PrivateCellRoot.materializer`, one path walk per write).
The physical write was the canonical encoding of the whole store.

## The layout

The logical authority `Store` over `CredentialAuthorityState.layout`, its patches and its logical
root are kept. Its physical image is:

| cell  | identifier                                             | payload                         |
|-------|--------------------------------------------------------|---------------------------------|
| HEAD  | `deployment.authorityCellId`                           | `head`, `[]`, the logical root  |
| ENTRY | `2^257 + ofDigits 256 (plane tag :: key bytes ++ [1])` | `entry plane`, key, value bytes |

Both are the registry's one `.authority` kind (`Compiler.CredentialAuthorityEntry`), whose payload
has the shape of a `Kernel.ProtectedCell` cell. There is no new `Kind`: the law class
(`kernelOnly authorityWriters`), `UserShape = False` and the observation protocol's refusal of the
authority role as a target cover the head and every entry by construction.

A logical update lowers to `CredentialAuthorityLayout.lowerAuthority`: the head write carrying the
post logical root, then one write per touched address carrying that address's post value, each
guarded at its cell's current root. The serving Host keeps its logical `Store` and applies the
existing logical patch to it; only this lowering is new.

## The six questions

1. **Which maps stay per-address?** All of them. Issuer epochs, policy epochs, subject-key epochs,
   policy revisions and addresses, capabilities, revocations, registrations, key records and parent
   rows are each one entry cell per key. The head holds the logical root and nothing else. The
   authority clock and the spent markers were never in the cell and stay out of the head.
2. **How is the head consistent with the entries?** `RealizesAuthority`: the head, below the
   authority space, holds `rootOf logical`, and for every address `logical address = valueAt bytes
   address`. Every update writes the head. `lower_realizes` proves the lowering installs it from a
   pre state that only HOLDS its store (`HoldsAuthority`: the same without the root comparison).
   The store is a function of the bytes (`HoldsAuthority.unique`).
3. **Logical free against physical retirement.** A logical `free` writes the entry cell with no
   payload. The cell stays live and the identifier is never retired, so a later allocation at the
   same address writes the same cell. Entry cells are never retired.
4. **Collisions, placement, squatting.** The coordinate is injective, not hashed
   (`entryCellId_injective`): no two addresses share a cell, so there is no collision to refuse,
   no vacancy check, no cSHAKE assumption and no hash per entry. The kind's law
   (`CredentialAuthorityEntry.PhysicalLaw`) places a head at the pinned identifier and an entry at
   the coordinate of its own plane and key (`CanonicalCellRegistry.authority_entry_is_placed`).
   Squatting: entries are at or above `ProtectedCell.authorityBase = 2^257`; a user birth is below
   `2^256` (`AuthoritySpaceGate.userInitial_below_authority_space`); the object kernel's protected
   range is `[2^256, 2^257)` (`ObjectiveActivityGate.Protected`, narrowed from "at or above
   `2^256`"; every activity and seat coordinate is still inside it,
   `AuthoritySpaceGate.coordinate_still_protected`). The gate `Kernel.AuthoritySpaceGate.gate` runs
   in `NativeHost.Config.sourceGate` for every facet, the object kernel's included, and refuses by
   name (`RejectReason.authoritySpaceWrite`) any write at or above `2^257` that is not a live cell
   of the authority kind (`admitted_space_write_is_authority`, `foreign_write_refused`, executed
   poles `forged_empty_refused`, `forged_other_kind_refused`, `ordinary_admitted`,
   `last_protected_cell`). Two components enforce the two halves. The GATE knows the kind and
   not the family: at or above `2^257`, only a live authority-kind cell. The RECEIVER's
   `lawFault` knows the family: a write of the authority kind by a family outside
   `authorityWriters` is refused `kernelOnlyForeignWriter`
   (`space_write_by_authority_writer` over `ReceivingLaw.kernelOnly_writers`; executed pole
   `ReceivingLawFixture.foreign_authority_writer_refused`). The second half holds for intents the
   Receiver judges.
   Entry identifiers are as long as their keys: `entryCellId address < 2^257 + 256^(key bytes + 2)`
   (`entryCellId_lt`). Every key type is built from naturals and digests; a natural in a key (a
   policy, capability, subject or cell identifier, a revision) is unbounded in type and bounded at
   admission by the size of the signed ingress that names it.
5. **The read footprint for guards.** A command that reads any authority address carries one
   read guard, on the head (`Ground.authorityReadGuard`, `Loaded.readGuard`). Every update writes
   the head, so a stale read of any entry is refused (`stale_authority_read_refused`), and a guard
   that still matches pins the logical root (`head_guard_pins_root`, whose one premise is the
   physical root's binding of the head's bytes). Authority writes stay serialised against authority
   readers exactly as before: no new concurrency. Entry cells carry no read guard; each entry
   write carries a write guard at its cell's root.
6. **What "on demand" means for a concrete `Store`.** The Host holds the logical store. At an
   open it reads every enumerable cell of the authority space once (`loadStore`, exact by
   `loadStore_exact`; cells below `2^257` are skipped without reading their bytes) and compares the
   head's root (`loadCell`). After a step it follows the held cell along the cells the step wrote
   (`stepCell`: one decode and one trie path per written entry) and compares the head's root with
   the followed cell's. Both are proved equal to the open (`loadServedAuthorityStep_eq`,
   `loadDeploymentStepAt_eq`). A receiver handed a durable image its Host validated READS it
   (`readDeployment`: the same store, no root computed, `loadDeployment_read`). A reader with no
   held store (the `at height` read) reads each address it needs at its own entry cell
   (`valueAt`, `NativeObservationController.standingAt`).

## Statements (`Compiler/CredentialAuthorityLayout.lean` unless named)

- `lower_realizes`, `lower_frame`: over a state that holds `logical`, an intent whose writes are
  the lowering of `post` (equal to `logical` outside `touched`) and writes outside the authority
  kind, at distinct cells, installs a state that realises `post`; untouched addresses read the
  same. No vacancy premise.
- `Update`: a post cell, its touched addresses and its frame. `Ground.authorityWrites` and
  `Loaded.writes` take an `Update`, so an omitted entry write does not compile. `Update.realizes`.
- `BirthAuthorityWritesBounded` (`birthAuthorityWritesBounded`): count at most
  `1 + 3·|initialPolicies| + 2·|grants| + |parentRows|`; encoded bytes at most
  `authorityBirthBudget.maxEncodedBytes`, a closed function of the pinned head identifier and the
  descriptor's entries through the codecs (each entry's own cell identifier, its key and value
  lengths; write framing, both roots and the head as constants); realisation and frame under
  `ResourceBirthAuthority.BatchEvidence`. It bounds the authority writes only: **the complete
  record is not bounded by the descriptor while the Book and the factory cell are written whole by
  every birth**, and no complete-record bound is claimed.
- The tie to the receiver: `ResourceBirthReceiver.installed_authority` (the installed image of an
  admitted birth realises the batch's post store; its other writes are proved outside the
  authority kind) and `ResourceBirthReceiver.authority_writes_bounded` (the count and byte clauses
  of the intent's own authority writes). The same installed theorem for delegation, revocation
  and policy install (`installed_authority_cell` in each receiver).
- Teeth, as theorems over every state: `omitted_entry_refused`, `wrong_head_refused`,
  `false_value_refused`, `entry_elsewhere_holds_nothing`, `stale_authority_read_refused`,
  `old_layout_refused`, `old_layout_unrealized`; executed: the gate's four poles.
- `ReceivingLaw.birthRoom` reads the newborn's parent address at its own entry write
  (`birthRoom_some`, `birthRoom_none_of_unwritten`).
- Issuer evidence is one point read: `Portal.verifyIssuer` is handed the capability,
  `CredentialAuthorityPolicyRegistry.issuerCheck` reads the capability stored at its kind and
  identifier (existence, issuer, stored epoch, full commitment, current issuer epoch:
  `issuerCheck_sound`, `issuerCheck_complete`, `issuerCheck_absent`, `issuerCheck_stale`).
  `issuedOf` and `Snapshot.issued` are deleted.
- Policy sourcing is maintained by the step: `NativeHostContext.policiesSourced_step` over
  `changedAddresses` and `HoldsAuthority.framed` (the frame of the patch read off the written
  cells). Only policies with a moved head coordinate or a written source cell are rechecked.
  `sourcesUnwritten` and its "head unwritten" inference are deleted.
- `at height`: `NativeObservationController.standingAt`, `atCovered_sound`, `atCovered_realized`,
  `atCovered_fold`: a fixed number of point reads at the past cells and the target's parent chain
  (`parentageAt`, bounded by the enumeration with no cell read).

## Owed, not claimed

- The for-every-k reachable-state construction with an admitted birth as a theorem. Its executed
  instance is the `append-flatness` run (200 births on one growing world).
- The complete-record bound (false today, as above).
- `Loaded.pastBytes` scans the accepted records from the asked height back for each cell it
  reads, so an `at height` read costs a fixed number of such scans. That scan is the history
  index's, not this layout's.
- The serving Host follows the written cells itself after its own write (`stepCell`) instead of
  taking the family's post cell: one more trie path per written entry than before (`HeldCell` is
  deleted). Measure before optimising.

## Non-Lean consumers of cell identifiers (checked, none sees an entry id)

`native/resource-client` (`market.rs`, `receipt_continuity.rs`, `hiding.rs`, `chat.rs`, `can.rs`),
`native/grain-runtime`, `native/private-backend`, `native/discord-entrance` parse cell
identifiers as `u64` or strings. Each of those is an identifier the client itself names: a room,
a document, a keys cell, an object cell. Authority cells are never an observation target (the
observation protocol refuses the role), no client names one, and no native crate parses the
record, checkpoint or Store codecs (`native/hyperdocument-link-sqlite-store`, `mini-kernels`,
`mini-streams`, `mini-sdk`, `mini-sdk-ts`, `pay-watcher`, `portable-archive`,
`oracle-appliance`: no cell-identifier column or field). There is no `web/` tree; `website/` is
static. The world-root index keys a cell by cSHAKE256 of its identifier's bytes and every Lean
codec encodes an identifier as a variable-length natural.

## What moved (a re-genesis)

- Cell payload of kind tag 3: from the `minidregg/credential-authority/v6` store frame holding
  the whole store to the frame `minidregg/credential-authority-cell/v7`, wire version 7, holding
  one head or one entry; `schemaRef .authority` from `⟨91003, 8⟩` to `⟨91003, 9⟩`.
- The cell root customization `DREGG.AUTHORITY.CELL.ROOT/v1` is new. No coordinate customization
  exists (the coordinate is not hashed).
- The law label `DREGG.REGISTRY.LOADED-AND-FINAL.STORE-CELLS` from `/v18` to `/v19`.
- `DurableDataIntent.RejectReason` gains `authoritySpaceWrite`.
- Every seed's cells (the one authority cell becomes a head and one entry per address), hence
  the world root at every height, the log start, the consensus anchor and every checkpoint.
- A store of the old layout is refused by name: `old_layout_refused`, `old_layout_unrealized`.
- The legacy Store2 carry (`NeutralPolicyCarry`) converts the source's one authority cell whole
  and lowers it to a head and one entry per address.

## Build state

See the lane's last report for the current list. This file is rewritten at each boundary.
