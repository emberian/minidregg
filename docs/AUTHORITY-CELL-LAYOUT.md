# The authority store's physical layout

State on `lane/authority-cells`: the registry's `.authority` kind is the cell layout and every
writer family and reader is ported to it. The whole build is green, a native Host built from the
lane passes the tour, and the Simplex gate passes with the appended record flat over 200 births.
The section "Validation" says exactly what ran on which commit and what is still owed.

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
- **A kind with a real class tag still pays the shared-prefix chain.** `PrivateCellRoot.paths`
  under a tag that leads (`kindTag`, for a kind whose addresses carry fields) puts every entry of
  one class under one 260-bit prefix, and `AuthTrie.tree` hashes a branch at every level where two
  or more entries remain, so each `set` rehashes about 260 + log2 n nodes. Measured with
  `store-bench trie 1000 class-leads` (the authority wire under a leading constant tag, 1,000
  entries of one class): 455 us per `set`, against 77 us with the hashed bits first. The fix is a
  compressed tree (a single-child chain hashed as one node) or short enumerated class tags; it
  rewrites `Theory/AuthTrie*` and the view openings and is its own change. Not done here.
- **One `set` is above the 50 us target.** After both halves below it is 58 to 77 us on stores of
  10 and 1,000 and 107 to 152 us on 100,000 (hbox, one run each). Of that, `paths` is 16 us and
  runs twice per insert (once for the walk, once inside the leaf's digest), the rest is the
  packed path, the content digest and about log2 n node hashes at 1 to 2 us. Computing the path
  once per insert and packing it without the bit list is the next cut; not done.
- **The hand-off time is not flat, and the record is.** In the 200-birth `append-flatness` run the
  median application hand-off is 41 to 54 ms over the first 8 births and 67 to 89 ms over the
  last 8 (three runs), inside the row's bound of 2. Attributed by phase (`MINI_APPLY_PHASES`,
  microseconds, one replica, heights 1 / 40 / 120 / 200): journal and decode 349 / 347 / 335 /
  329; certificate 1,658 / 2,215 / 1,994 / 1,867; acknowledge 4,368 / 4,979 / 5,232 / 5,627;
  **receive 31,061 / 42,355 / 66,052 / 108,596**. Inside the receive (`MINI_APPEND_TIMING`): order
  453 / 458 / 464 / 493, readback 2,669 / 2,959 / 3,534 / 3,538, reader 57 / 56 / 60 / 62;
  **derive 13,961 / 15,209 / 20,720 / 31,271** (`deriveVerified`, the source admission) and
  **store 13,181 / 23,214 / 44,135 / 73,478** (`DurableReceiverIO.receiveLoadedDetailed`, the
  durable append). So two things grow linearly with history, the append at about 0.3 ms per
  height and the admission at about 0.09 ms per height, neither through the record's size. Not
  attributed below that and not fixed: it is outside the authority layout (the first places to
  read are the per-append work over the image's cell list and the Book and factory cells, which
  are still rewritten whole).
- **The byte paths are still lists.** `scripts/check-bytes-repr.sh` counts 5031 against 4961 on
  main. The rise is the binder `CellId → List UInt8` (the type of `DataSnapshot.canonicalBytes`
  and `Loaded.pastBytes`) on the layout's definitions and theorems, and the list signatures of
  `encodeCell`, `decodeCell`, `natOfBytes` and `entryId` over the lifecycle list codec. No path
  executes more list bytes than before and each record carries fewer. The real fix is its own
  change: `DataSnapshot.canonicalBytes`, `DataWrite.canonicalPostBytes` and the lifecycle codec as
  `ByteArray`, after which these binders convert with no work here.

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
- The private root of every `untagged` kind (the authority store, the policy registry's root
  bytes, hyperdocument event logs): the key path is the 256 hashed address bits FOLLOWED BY the
  260-bit class tag, where it was the tag first (`PrivateCellRoot.KeyTag.leads`, `paths`,
  `paths_eq_iff`). No customization string moved. The logical authority root committed in the
  head therefore differs from the one the same store had before, and so does the world root.
  Checked by reading: every trie opening over a private root is in `Kernel/PrivateCellView.lean`
  (`revealVerify` over `keyBits`, the tag first) and `Kernel/PrivateCellOpening.lean`
  (`revealVerify pathDig` over `paths wire (kindTag kind)`), both at `kindTag`, which still leads;
  those two modules and `PrivateCellReceiver`, `PrivateCellMaterializer` are imported only by
  `Kernel.lean`. No light reader, range reader or view opens a path of an `untagged` root: the
  authority readers are point reads of entry cells against the head, the other two kinds are read
  by root equality.
- An old-order private root cannot be presented under the new layout by a store that existed:
  the path order and the cell layout move in one change, so every store whose roots are of the
  old order holds the one whole authority cell and is refused by name below. A head forged to
  carry an old-order root over new entry cells fails the head check (`HoldsAuthority`: the
  loaded store's root is not the head's), as any wrong root does.
- A store of the old layout is refused by name: `old_layout_refused`, `old_layout_unrealized`.
- The legacy Store2 carry (`NeutralPolicyCarry`) converts the source's one authority cell whole
  and lowers it to a head and one entry per address.

## Validation

Head `lane/authority-cells` rebased onto `origin/main` at `e837e5735` (after `76c7a9798`, the
empty-digest and midstate change, and `f08fe6e5c`, the `append` binding). Everything below ran
on that head on hbox unless it says otherwise.

- **Whole build**: `swarm-build lake build Minidregg minidregg-host` with the two native
  fixtures, the four Simplex gate executables and the modules outside the umbrella that import
  the layout (`Host.ClientConsentSession`, `Host.ClientConsentSpecializedSession`,
  `Host.WorldSim`, `Host.TurnLogFollower`, `Host.CarryVerifierMain`, `Host.Kn2StoreBench`,
  `Verify.ResourceReserveBirthFixture`, `Fixtures.BirthPlanPoles`, `Kernel.NativeThinConsent`,
  `Host.ThinBirthConsent`, `Host.ClientConsentCore`): rc 0, 13,086 jobs.
- **Static checks**: `check-import-boundary.sh` OK; `check-bytes-repr.sh` 5032 against the ceiling
  4961 (main itself counts 4962 since `76c7a9798`: the node hash's list binders).
- **Native Host**: `native-loop` overlay candidate `a7d7e48a9eb6`.
- **Journeys** (through `scripts/pipeline/lane-journey`): J0 to J8, THIN, JROT 34/34 and K10C 184
  rows pass. JROT and K10C had four rows expecting the constructor name where the client prints
  the rendered clause (`not-precommitted`, `not-prerotated`, `not-holder`, `already-revoked`);
  the rows are corrected in their own commit.
- **One `set` of the kept private index** (`store-bench trie <n>`; microseconds; the built index
  still held / a second batch / one entry on a held index; one run each):

  | store | main before `76c7a9798` | empty digest once, midstate | hashed bits first |
  |---|---|---|---|
  | 10 | 846 | 454 / 622 / 773 | 58 / 68 / 58 |
  | 1,000 | 818 / 885 / 926 | 475 / 461 / 512 | 77 / 74 / 64 |
  | 100,000 | 1,364 / 1,050 / 1,882 | 1,111 / 797 / 1,672 | 152 / 127 / 108 |

  Building 100,000 entries by `set`: 110.5 s, 58.3 s, 16.1 s. The cause was the class tag leading
  the path: every entry of an `untagged` store shared 260 bits, the trie carried a 260-level
  single-child chain, and each level hashed its branch and its empty sibling again.
- **The served step** (`store-bench`, ten repetitions, three runs each, matched worlds made by J0
  to J2 for the birth and J0 to J3 for the delegation; the bench uses one state as both sides,
  so each written entry is freed and set again, twice a real step's trie work):

  | last record | lane | main (`cc727d09d`) |
  |---|---|---|
  | birth | 1.0 / 1.0 / 1.0 ms over 12 written cells, of which `stepCell` 0.7 | 0.6 / 0.5 / 0.5 ms over 5 |
  | delegation | 0.5 / 0.5 / 0.5 ms over 3 written cells, of which `stepCell` 0.3 to 0.4 | 0.5 / 0.5 / 0.5 ms over 1 |

  Before the two trie changes the lane's birth step was 14.8 to 18.5 ms. The Host still walks
  each written entry's path a second time (the family walks it first); at this cost the checked
  hand-off of the family's post cell is not needed and was not built.
- **Authority-writing families on this head** (candidate `a7d7e48a9eb6`, each journey in its own
  root after J0 to J5, through `lane-journey`): JPAY2 18/18, JPAY3 24/24, JPAY4 26/26, JPAYE2
  38/38, JPAYE3 27/27, JJOBM 39/39, J17 212 rows, JROTL 10/10, JROT 34/34, K10C 184 rows, KW
  20/20, J12 139 rows, J12W 81 rows (213 content actions), K12T 28/28, KCH 12/12, JSLK 23/23.
  All pass. JROT reaches commitment adoption (its precommitment rows). Which journeys reach
  factory provisioning, share issue and the lifetime grant was not traced.
- **Earlier runs, on older bases, not repeated on this head**: J12X, JSERVE, G (1000 writes), K4,
  KT, JJ, K10, KF pass.
- **Rows failing identically on the base candidate** (control runs of the same row): KBW
  (`stale-birth` expects `birthStale`, the birth is installed); KC (K-CLOCK 31 of 33); K11
  (`create-gift` exits 3 where a refusal is expected, `same-2` accepted where a refusal is
  expected); KCH (its Lean probe needs `supportInterpreter`); KH (`scalar: undeclared-field 3` at
  prepare).
- **First writes**: `Kernel.FirstWriteCoverage.first_write_covered`,
  `authority_space_never_unnamed`, `unnamed_below_refused` (theorems over every step and patch).
  Executed: `ReceivingLawFixture.neutral_unauthorized_refused` and `neutral_smuggled_refused` run a
  whole receive whose patch has an unnamed first write of cell 8, below the authority space, and
  are refused `neutralBirthUnjudged 8`; `AuthoritySpaceGate.forged_other_kind_refused` refuses a
  cell of another kind at an entry coordinate; every birth of the tour is admitted with its entry
  cells unnamed. The fixture's family is its own (`bypass`), not the birth family: a pole through
  `ResourceBirthReceiver` itself is not written.
- **Fixtures**: `scripts/native-accepted-fixture/rerecord.sh` re-recorded both native fixtures
  from candidate `a7d7e48a9eb6`; their projections equal the hand-written authorities.
- **Simplex gate**: `scripts/gates/check-generic-simplex .lake/build/bin` with 200 heights, three
  runs: 19 rows pass, 10 plants red as recorded. `append-flatness` over 200 births, by ordinal:

  | ordinal | record before | record now | largest write before | largest write now | authority now |
  |---|---|---|---|---|---|
  | 1 | 5,116 | 5,123 | 1,324 | 107 | 615 B in 8 writes |
  | 40 | 11,366 | 5,110 | 7,568 | 107 | 615 B in 8 writes |
  | 120 | 24,169 | 5,125 | 20,377 | 107 | 616 B in 8 writes |
  | 200 | 36,989 | 5,128 | 33,185 | 107 | 615 B in 8 writes |

  The row is two raw bounds (hand-off at most 2 times, record at most one eighth above the first
  window) and prints these as its `WRITES` line. `GENERIC_SIMPLEX_ROW_LOGS=DIR` keeps each row's
  whole output.
- **Executed poles** (compiled in the umbrella): `AuthoritySpaceGate.forged_empty_refused`,
  `forged_other_kind_refused`, `ordinary_admitted`, `last_protected_cell`;
  `ReceivingLawFixture.foreign_authority_writer_refused`.
- **Not run**: `lane-check` as a script (the Lake targets above replace it); the composed, enrol
  and j14 gate phases; any writer family the tour does not reach on a native Host (key rotation,
  renounce, the pay and application share families: they compile and are untested natively).

## Next (in this order; none of it is done)

1. The hand-off growth: read `DurableReceiverIO.receiveLoadedDetailed` and `deriveVerified` for
   the work that scales with height (numbers under "Owed"), fix it at the cause, and tighten the
   flatness row's hand-off bound from 2 toward 1.
2. `paths` once per insert and the packed path without the bit list, to bring one `set` under
   50 us.
3. The compressed tree for kinds with a real class tag (its own lane).
4. A birth-family pole for the unnamed first write, and tracing which journeys reach factory
   provisioning, share issue and the lifetime grant.
