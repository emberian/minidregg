# What an append costs as history grows

State on `lane/append-growth`. Fixed: the allocation check, the journal index's compiled half,
the index rows read back on every append, the Store's node insert, the NODES file, the holder's
hand-over. Measured, attributed to the code that does it and not fixed: the rest ("Measured, not
fixed"); "Next" at the end is the order of work. The store phase of a birth off a checkpoint
height is 4.1 ms at the first birth and 7.1 ms at the two hundredth (the target, under 4 ms and
flat, is not met). Numbers are from hbox, a shared box, one replica of the four-source fixture
unless a line says otherwise; times are microseconds.

## How to measure

- `MINI_STORE_PHASES=1` (environment of the receiving process) prints to stderr, per record:
  `store judge` (the executor and the gates, run once more to be timed), `store index` (the two
  steps of the journal index apply, with key counts), `store prepare` (index root, index rows,
  `Loaded.extend`, entry; record bytes and node rows), `store confirm` (read-back, checkpoint),
  `birth admit` (the parts of the native birth admission) and `birth prepare` (the parts of
  `prepareBirth`, run once more to be timed: a run with this flag pays the preparation twice, so
  its hand-off times are not the row's). Also `store extend` (the parts of `Loaded.extend`,
  with the root cache's advance), `store turn` (the World's turn: derivation, charge, pins,
  admission), `store entry` (leaf digest, tag, node rows, NODES file), `store append` (the
  Store's append call alone) and `store hold` (the holder's hand-over). Every part is run once
  more to be timed, so `ordered append ... store` under this flag is about 3 ms above the sum of
  the parts.
- hbox has co-tenants: compare runs only when `ordered append ... derive` (the signature
  verification, constant work) agrees between them. The tables below take, per field, the minimum
  over the four replicas and three neighbouring heights.
- `MINI_APPEND_TIMING=1` prints the ordered receiver's five phases; `MINI_APPLY_PHASES=1` the
  hand-off's.
- `scripts/gates/check-generic-simplex BIN` with `GENERIC_SIMPLEX_FLAT_HEIGHTS=200` and
  `GENERIC_SIMPLEX_ROW_LOGS=DIR` keeps the flat row's whole output in `DIR/four-source-flat.log`.
  The fixture seals a checkpoint every 8 records (the product every 64).
- `MINI_FLAT_BORN=account` makes every birth of the flat row register an account, so the Book
  gains one per birth.
- `minidregg-host CONFIG store-bench index N` times the journal index's row operations on a trie
  of N keys; `store-bench trie N` one `set` of the private index.
- `scripts/perf/flatness-bench.py --bin CANDIDATE/bin --root NEW --src TREE --n 100 --lo 10` is
  the product's row (100 appends to one document through the client). `MINI_TRACE=/abs/file`
  makes the client write one line per exchange.

## Where the time went before any fix (main at `74d653514`)

Heights 40, 120 and 200 are checkpoint heights in the fixture; 41, 121 and 199 are not.

| part of `receiveLoadedDetailed` | 1 | 40 | 120 | 200 | 41 | 121 | 199 |
|---|---|---|---|---|---|---|---|
| executor (`Loaded.prepare`) | 13 | 22 | 28 | 20 | | | |
| gates (`Loaded.judge`) | 50 | 47 | 56 | 54 | | | |
| index root (head tag MAC) | 1 | 79 | 86 | 79 | | | |
| journal index rows (`applyIndex`) | 11,505 | 14,424 | 18,271 | 18,597 | 15,677 | 20,380 | 16,232 |
| `Loaded.extend` and the World's turn | 1,976 | 2,523 | 3,137 | 3,138 | 2,759 | 3,191 | 2,883 |
| leaf, frontier, tag MAC | 256 | 614 | 801 | 818 | | | |
| the Store's append call | 357 | 1,147 | 1,724 | 1,818 | | | |
| read-back | 96 | 102 | 163 | 106 | | | |
| checkpoint seal and put | 0 | 5,870 | 24,373 | 55,007 | 1 | 2 | 2 |
| whole store phase | 14,489 | 25,209 | 49,278 | 80,517 | 21,288 | 26,999 | 22,045 |
| node rows written | 35 | 117 | 146 | 154 | | | |
| `deriveVerified` | 14,601 | 17,283 | 24,378 | 37,880 | 17,735 | 32,361 | 31,962 |

`deriveVerified` for a birth: the credential bundle (the signature verifier) is 12,300 to 13,500
at every height; `prepareBirth` was 1,010 at the first birth and 16,400 to 20,700 at the two
hundredth. Inside it `preparePreAuthority` 31, the grant batch 49, the candidate law 500 and the
authority writes 85 are level; `preparePostAuthority` was 72 / 622 / 2,638 / 11,510 / 17,380 at
births 1 / 34 / 78 / 167 / 200: quadratic.

## Fixed: the allocation check (`Directory.used`)

`Theory.CellRegistry.Directory.used` was a `Finset CellId`. `Directory.insert` computed
`before.used ∪ {cellId}`, which is `List.union` (every old identifier re-inserted by a scan), once
per create request, and `CellRegistry.create` and `LifecycleImage.view` decided `cellId ∈ used` by
a linear scan. `used` is now the set's characteristic function `CellId → Bool`, as `slots`
already is a function: an insertion adds one case, the directory of held images answers from the
image (`everUsed`, one map lookup), and `HeldImages.used`, `usedExact` and
`CompiledListOps.usedSet` are deleted. Statements are rephrased pointwise
(`allocate_success_used : ∀ cellId, after.used cellId = (before.used cellId || decide (cellId ∈
requests.map cellId))`, `allocate_success_fresh`, `create_success_iff`, `view_used`,
`view_fresh_iff`). No statement needed the set to be finite: the whole build is green without it.

After it `preparePostAuthority` is 61 to 75 at every height and `deriveVerified` is 14,693 at
height 1 and 15,799 at height 200. The flat row's median hand-off is 40,911 over the first 8
births and 52,707 over the last 8 (before: 41 to 54 ms and 67 to 89 ms). The trie bench was not
rerun after the path-once change.

With it, `PrivateCellRoot.indexStep` is compiled as `indexStepOnce` (`indexStep_eq_once`): an
insert evaluates the address's path once, for the walk and for the leaf digest.

## Fixed: the journal index's compiled half

No statement, row, root or interface moved. What compiled code runs is replaced by `@[csimp]`
equalities, each proved for all inputs (nothing is executed-only): `dig = digFast` (the
customization absorbed once, the node written into a byte array, the empty digest and its
spelling constants), `IndexKey.bytes = bytesFast`, `bitsOf = bitsOfFast`, `verify = verifyFast`
(in `Compiler/DurableIndex.lean`, at the definitions, so every reader compiled after them gets
them); `set = setFast` (one walk, the bits once, `split`'s first differing bit in one pass, a
sibling's row read only under an empty subtree), `IndexRows.insert = insertFast` (one walk and
one verification per key), `setAll` and `IndexRows.apply` over one hash map of the rows written
and one hash set of the prefixes written (`foldMap_agrees`: the same root, the same rows, the
same order) in `Compiler/DurableIndexFast.lean`.

`store-bench index`, microseconds, before / after, at 1,000 keys (20,000 in brackets):

| | before | after |
|---|---|---|
| `bitsOf` (with the bench's key hash, 2.5) | 16.6 (24.1) | 7.3 (6.8) |
| digest of a leaf | 10.4 | 4.5 (4.7) |
| digest of a branch | 5.4 | 3.6 (3.8) |
| `lookupRows` | 161.7 (227.8) | 76 (104) |
| `set`, a new key | 564.5 (1,149.1) | 144 (183) |
| `set`, over a held key | 326.8 (454.0) | 143 (181) |
| `setAll`, twelve new keys, per key | 911 (1,530) | 155 (210) |

The target of 100 for a new key at 20,000 is not met. What remains is hashing, and two choices
of the ROOT that this change may not move:
- **The base-255 spelling of a digest.** A branch's digest costs 3.6: 2.7 to spell its two
  children base 255 into the node's bytes (1.3 each, `nodeArray of a branch`), 0.2 for the
  permutation, 0.7 to read the output as a number. One level of one `set` is two such hashes
  (the verification's and the rebuild's): 5.4 of its 7.2 is the spelling.
- **The family byte leads every path.** A trie of 1,000 keys of one family has 2,436 rows and a
  key about 19 levels, where 11 would hold it: the family's eight bits are a chain of branches
  with an empty sibling, hashed twice per key. (The empty sibling's spelling is a constant now.)
A re-genesis that moves the index root (the checkpoint design does) can fix both: digests as
fixed 32 octets in a node's bytes, and the family in three bits or after the hashed bits where
no reader reveals by family.
`rebuildLazy (siblings given)` reads 272 at 20,000 keys against 68 at 1,000 while a whole `set`
is 183: a bench artifact, not explained.

In the product (`flatness-bench.py`, 100 appends to one document, `MINI_STORE_PHASES=1`) the
index apply is 283 / 376 / 1,091 (minimum, median, maximum) over 103 appends; it was 1,400 to
2,400. On the four-source fixture's births (14 keys) it is 5,331 / 7,336 / 7,912 / 8,409 at
heights 1 / 40 / 120 / 200 (11,505 / 14,424 / 18,271 / 18,597 before), and that is NOT the trie:

## Fixed: the receiving loop read its index rows from the Store on every append

`store index ... held true` only says a holder exists after the read. In `receiveCandidateWithFresh`
nothing handed the appended rows to the holder (`DurableServed.receiveServed` does), so the holder
was one height behind and every append read its keys' prefixes from the Store (about 1,350 row
keys for a birth); and `DurableNodeCache.decoded` was one slot per process, so the fixture's four
Stores evicted one another. Now `PreparedAppend.indexWrites` carries the decoded rows,
`publishAfter` hands them over when the Store installed the entry from this call, and the holder
is kept per Store root, as a persistent binary trie over the bit prefixes (`DurableNodeCache.Held`:
a lookup or an insert follows the bits and compares no key; `Held.get?_insert`). The fixture's index apply is 1,423 / 2,038 / 2,521 / 2,533 at heights
2 / 41 / 121 / 200 (5,331 to 8,409 before).

The holder's step is the pure `DurableNodeCache.Decoded.hold`, and its invariant is stated and
proved there. The Store's index rows are modelled by height, an installed append being
`DurableIndex.overlay` of its rows (the form `SetPreserves` and `maintained_apply` use):
- `Decoded.Faithful store held`: every row held is the Store's row at the held height. The
  holder is a part of the Store's rows (rows read join it), never more.
- `Decoded.hold_appended`: handing over the rows of an append the Store installed at `h + 1`
  keeps it (moved from `h`, or started fresh). `Decoded.hold_read`: so do rows read at a height.
- `lookupRows_eq_of_faithful`: a verified lookup through a faithful holder that lacks no row on
  the key's walk (`walkMisses = false`) IS the lookup through the Store's rows.
- `faithful_inhabited` (a holder that holds a row, faithful); `Decoded.hold_unconfirmed_wrong`
  (teeth: a holder handed the rows of an append the Store did not install is not faithful, and
  its walk claims the key present where the Store's finds nothing).
Among handed rows the first of a prefix wins, as in `overlay`; no proof that `IndexRows.apply`
writes a prefix once is needed. Not proved in Lean: that the Store's helper installs exactly the
node rows it is given (the transport's contract, Rust). `DurableServed.receiveServed` (the
Host's path, not touched here) hands over on any confirmed read-back, also one the Store held
already; its premise then rests on every writer of the Store computing its rows by
`IndexRows.apply`. Every use of held rows stays verified against the authenticated root.

### The red row was the gate's, not the hand-over's

`four-source-serve` failed with "partial source completion" (or "partial completion retained"
when replica 0 was the late one). `scripts/gates/check-generic-simplex`'s `serve` awaited a
quorum of three receipts and then stopped all four replicas, and the lookup after it requires
the record in all four Stores. The fourth replica is 10 to 100 ms behind the third (it is still
validating when the others append); when the client's 200 ms poll fell in that window the row
stopped it before its append. Measured on hbox by running the row alone with its replica logs
kept: 5 of 30 with the hand-over, 2 of 30 with a fixture built before it (`d597a8582`), none
of 12 when the stop waits 3 s. The late replica's log never reaches `store index`: no changed
code ran in it. `serve` now waits for all four (`await-call --all`, as `serve_down` does) before
it stops them. The plant `quorum-lookup` keeps the lookup's teeth: replica 3 stopped, a birth
answered by three, the replicas stopped, and the lookup of all four must refuse.

## Fixed: the Store's append call, the NODES file, the holder's hand-over

- The Store helper prepared `INSERT INTO durable_node` once per node row (62 rows at the first
  birth, 150 at the two hundredth); it prepares it once per append and resets it per row.
- `NativeConfig.append` built the NODES file as a list of octets; `encodeNodesArray` writes it
  into one byte array (`encodeNodesArray_data`: its octets are `encodeNodes`).
- The holder's ordered map of bit lists made the hand-over grow with the rows held; the prefix
  trie above does not.

The store phase by part, before (`5e4a89d6d`) and after (`31271d5d4`), same box state (derive
about 15,000 in both). Heights 40, 120 and 200 seal a checkpoint.

| part | | 2 | 40 | 41 | 120 | 199 | 200 |
|---|---|---|---|---|---|---|---|
| index rows (`applyIndex`) | before | 1,373 | 2,096 | 2,045 | 2,510 | 2,459 | 2,480 |
| | after | 1,376 | 2,021 | 1,897 | 2,180 | 2,286 | 2,306 |
| `Loaded.extend` | before | 1,855 | 2,375 | 2,288 | 2,811 | 2,761 | 2,741 |
| | after | 1,878 | 2,296 | 2,295 | 2,621 | 2,809 | 2,759 |
| entry (leaf, frontier, tag, node rows) | before | 335 | 586 | 535 | 737 | 709 | 687 |
| | after | 325 | 599 | 515 | 653 | 675 | 679 |
| the Store's append call | before | 647 | 1,053 | 1,097 | 1,632 | 1,579 | 1,661 |
| | after | 245 | 624 | 639 | 780 | 1,002 | 1,731 |
| read-back and hand-over | before | 111 | 334 | 376 | 550 | 572 | 502 |
| | after | 94 | 180 | 142 | 169 | 178 | 230 |
| of it the hand-over | before | 31 | 199 | 228 | 385 | 430 | 410 |
| | after | 14 | 38 | 38 | 54 | 67 | 71 |
| checkpoint seal and put | before | 0 | 4,917 | 1 | 23,424 | 1 | 52,510 |
| | after | 0 | 4,673 | 0 | 21,694 | 1 | 51,550 |
| sum of the parts, with judge 80, index root 60, counts 55 | before | 4,509 | | 6,537 | | 8,277 | |
| | after | 4,106 | | 5,679 | | 7,148 | |

(The 1,731 at height 200 is one height's sample; 199 and its neighbours read 1,002.)

## Measured, not fixed

- **The index rows are 2.3 ms of the 7.1.** 14 keys at about 165 each. Per the bench above a
  `set` is two digests a level (the verification's and the rebuild's) and a digest is mostly the
  base-255 spelling of its children. Twelve of the fourteen keys are last-write keys of one
  family: each walks, verifies and rebuilds the family's eight one-sided levels and the shared
  levels under them again (about 530 digests an append where the union of the paths is about
  220). A batched `setAll` (keys sorted, each touched node verified and rebuilt once) needs its
  equality to the sequential definition proved; it is the largest single step left.
- **`Loaded.extend` is 2.8 ms**, split at height 199: the root cache's advance 1,092 (13 slots,
  each one path of the kept trie: `worldDig` still hashes a node from a list, the index's `dig`
  does not); the World's turn 860 (`Turn.ofIntent` 348, charge 20, pins 55, `admitPinned` 437),
  level; engine install, presence, links, ids and transaction index 150, growing slowly; the
  rest, about 650, is the record encoded and hashed again (next bullet).
- **One append encodes and hashes its record several times.** `Loaded.extend` computes
  `chainStep` (the record's turn digest) and, for the frontier, `leafDigest` over
  `recordFrame.encode record`; `prepareAppend` computes `loaded.chainAfterIntent`, the record's
  bytes, the leaf digest, `Frontier.push` and `completedNodes` (the frontier's node digests a
  third time) again. Each is O(record), about 5 KB; none grows with history.
- **`Turn.ofIntent` derives the writes' deltas five times** (`createsOf`, `legsOf`, `retiresOf`,
  and the first two again for the charge), each a decode of every written cell's post bytes.
- **The entry is its node rows**: 263 at the first birth, 616 at the two hundredth, for 60 to
  150 index rows encoded as lists (`appendNodes`: `rowKey`, `rowStream.encode`, two digests
  spelled base 255 each). `NodeWrite` holds its key and value as lists, and the node cache packs
  them again.
- **The Store's append call still grows**, 245 to 1,002: the rows (62 to 150) and the row
  table's B-tree, where an append's rows land on as many pages. The row keys are the bit prefixes,
  so they scatter by construction.
- **The fixture forks to sign.** By `perf`, 29 % of the fixture process's samples are in `execve`:
  `Verify/NativeJointSourceFixture.lean` runs the test signer by `IO.Process.output`, five times a
  birth, and each fork copies the page tables of a growing process. It is in the row's wall time
  and not in the hand-off the row judges.
- **The flat row is a ratio of wall times in one run.** A co-tenant's 19-core job starting in the
  middle of a run fails it (one of four gate runs at `31271d5d4`: derive 14,656 at height 2 and
  34,624 at height 199 in that run, every phase 2.3 times its usual).

- **The checkpoint seals the whole state.** `storeCheckpoint` encodes and MACs the whole `State`
  and the World's system store (`DurableCheckpointCodec.sealedBytesAt`) at every height that is
  a multiple of `checkpointEvery`: 5,870 / 24,373 / 55,007 at heights 40 / 120 / 200, about 0.27
  ms per birth of state. The system store (`Kernel.World.sysLayout`) has six namespaces; `journal`
  (one entry per record) and `spent` (one per nullifier) only grow, so the seal is O(history), not
  only O(state). The accepted direction: the checkpoint becomes a small sealed head and the cells
  are rows the append writes in its own transaction. The design message for it is owed before
  any of it is built (the keystone, what an open costs before and after, how a past height reads,
  what retires old cell versions, which formats move).
- **The Book is written whole.** With `MINI_FLAT_BORN=account` the record is 5,144 / 5,260 /
  5,502 / 5,747 bytes at births 1 / 40 / 120 / 200 and its largest write, the Book, 108 / 196 /
  436 / 676: three bytes per account. The bound on a birth's complete record is false.
- **`ExactReadback.ofAppended` prepares and extends a second time**: 2.6 to 3.9 ms, level.

## The product's flat row: another path, attributed, for its own lane

`flatness-bench.py` appends to one document; it
makes no birth, and the allocation fix does not move it: the median propose and submit wall
times over operations 1 to 10, 46 to 55 and 91 to 100 are 9.9 / 30.3 / 48.3 and 23.5 / 48.0 /
54.7 ms on main and 10.8 / 33.3 / 49.2 and 31.9 / 67.4 / 59.2 ms on the lane (one run each).
By the client's exchange trace over 80 operations, comparing operations 9 to 16 with the last
8: Host operation 5 answers 9,426 bytes early and 66,950 late (2.5 to 8.3 ms); the client then
makes five codec exchanges of operation 8 over that answer (1.6 to 4.7 ms each); Host
operation 2, whose request is 2,415 bytes throughout, takes 19.1 ms early and 43.4 late; Host
operation 1 is level at 9 ms. So the client reads something that grows by about 720 bytes per
append and recodes it five times per proposal, and the Host's handling of operation 2 grows by
0.3 ms per append of history. Neither is read in the code yet; the serving Host's append does
not go through `prepareAppend` (only its index apply printed, 1.4 to 2.4 ms, level).

Not fixed here and not this lane's: the row's owners are host-execution and store-retained.

## What ran for the allocation fix (`5e05cf4fc`)

Whole `swarm-build lake build Minidregg minidregg-host` with the fixture and the gate
executables, rc 0, 13,062 jobs. The modules outside the umbrella that import the directory
(`Host.ClientConsentCore`, `Host.ClientConsentSession`, `Host.ClientConsentSpecializedSession`,
`Host.WorldSim`, `Host.TurnLogFollower`, `Host.CarryVerifierMain`, `Host.Kn2StoreBench`,
`Verify.ResourceReserveBirthFixture`, `Fixtures.BirthPlanPoles`, `Kernel.NativeThinConsent`,
`Host.ThinBirthConsent`) build, rc 0; `Host.Json`, `Host.SourceAgreementJson` and `Host.Main` are
in the Host executable's build. `check-import-boundary.sh` OK. `check-bytes-repr.sh` 5033 against
the ceiling 5032: the one new occurrence is `digWithPath`'s node argument, `NodeIn (Address L)
(List UInt8) Inner`, the private index's existing node type. Native Host: overlay candidate
`d2eb8f7d8c4f` over the builder's `74d653514`. `scripts/pipeline/lane-journey-selftest` passes
on hbox. The Simplex gate at 200 heights with the phase prints: every row passes. Through
`lane-journey` on that candidate: J0 to J8 and THIN pass; KW 20/20, J12 139 rows, JPAY4 26/26 and
JROT 34/34 pass in one world, and K10C passes 184 rows in its own world. (In one world after KW,
K10C finds the world's socket closed and fails 147 rows at its first `enroll`: an order of steps
the earlier runs never made, not read further.) JPAY4's two Hosts and two residents, which live
in the run's short socket directory, were stopped by PID file by the runner.

## What ran for the holder and the append call (`5e4a89d6d`, `31271d5d4`)

At each head, on hbox: `swarm-build lake build Minidregg Host.Main Host.ClientConsentCore
Host.ClientConsentSession Host.ClientConsentSpecializedSession minidregg-host` with the fixture
and the three gate executables, rc 0, 13,075 jobs; `check-import-boundary.sh` OK;
`check-bytes-repr.sh` 5056, the ceiling (nothing added). The Simplex gate at 200 heights:
at `5e4a89d6d` three runs, at `31271d5d4` four, every row passing and all eleven plants red in
each but the second at `31271d5d4`, whose flat row failed under the co-tenant's load described
above. Native candidates over the builder's `9ac0425a6` (`d799cecc1ba3`, then `c53118cb30eb`);
through `lane-journey`: J0 to J8 and THIN pass, KW 20/20, J12 139 rows in its own world. (J12 run
after KW in one world fails at its first `enroll`, "cannot connect to world.sock": the same order
of steps that failed K10C after KW before.) The candidate's Store helper is the base
candidate's (`native-loop` overlays the Host and the consent provider only): the changed helper
ran in the gate, built from the tree, and in its unit test
`durable_nodes_are_written_with_their_entry_and_read_by_version`.

## Next, in this order

1. Written and not built (a patch over `31271d5d4`, not on the branch:
   `/private/tmp/claude-501/-Users-ember-dev-minidregg/25283063-688e-44a8-aca1-3f12f82237f5/scratchpad/append-growth/next-worlddig-turnof.patch`;
   `Kernel/WorldRoot.lean` and `Kernel/TurnOfIntent.lean` each pass `lake env lean` alone, the
   tree was not built under them): `worldDig` compiled as the index's
   `dig` is (`Kernel/WorldRoot.lean`: `worldDigFast`, `worldDig_eq_fast`, with `digestOfArray`
   moved there from `Compiler/DurableIndex.lean`), expected to take 350 to 400 off the root
   cache's 1,092; `turnOf` deriving the deltas once (`Kernel/TurnOfIntent.lean`: `turnOfOnce`,
   `turnOf_eq_once`), expected to take about 200 off `Turn.ofIntent`'s 348. Both are `@[csimp]`
   equalities for every input; the whole tree rebuilds under them.
2. The batched index apply (the first bullet of "Measured, not fixed"): about 1.2 ms.
3. The record encoded and hashed once per append (thread the bytes, the chain and the leaf from
   `prepareAppend` into the extension); `NodeWrite` with packed key and value and the rows encoded
   into byte arrays. About 0.6 ms together, and the bytes ratchet falls.
4. The read-back's second preparation (`ExactReadback.ofAppended`, 2.6 to 3.6 ms, outside the
   store phase).
5. The checkpoint as rows, stage A then stage B: with the owner. The design and the coordinator's
   five conditions are in the session's messages (no periodic seal; the tag is the head; cells as
   node rows; the system store as index families; `journal` and `spent` are already the index's
   transaction and nullifier families). Before its first commit: read `DurableFastForwardSpec`
   whole, the fn archive journal's anchoring, and list every place an index root leaves the Host;
   name what each reader that starts from a checkpoint starts from instead; the migration as a
   command with a test on a tour-built world; the retention Prop and refusal name; Store bytes per
   record before and after; the cold open at 1,000 and 10,000 records. Move the two root choices
   above (digests as fixed octets, the family's place in the path) in the same re-genesis: they
   are what bounds a digest at 3.6 and with it items 1 and 2.
6. The Book split, the same move.

## Left on hbox for the successor

Tree `t2`, leased as `append-growth`, with its own package copy, built at `31271d5d4`. One
candidate, `/home/hbox/pool/lanes/append-growth/candidates/c53118cb30eb`.
`/ci/lane-appendgrowth/flat-fix1`: a product bench world whose
`w/deployment/operator-config.json` is the configuration `store-bench index N` runs with. Logs in
`/home/hbox/lanes/append-growth-scratch`: `before-5e4a89d6d-flat.log` and `h2-1-flat.log` are the
flat rows the table above is read from (`scratchpad/append-growth/phase-table.sh FILE`).
