# PLACE: rooms, streams, documents, laws and runners friends share

This is the present-state description of the place: what friends do on a Mini node beyond
single cells. The Lean modules and the Rust client are the authority; this document says what
they do and where they are. Section numbers are kept from the design of 2026-09-30 so that the
`PLACE §N` citations in `Kernel/`, `Assurance/`, `Compiler/`, `native/grain-runtime`,
`native/resource-client` and its journeys resolve here. Item numbers (`PLACE item N`,
`§5 row N`) are the lanes in §5. Journey names (J11 … J17) are the rows in
`native/resource-client/journey.sh`.

Each section is marked **shipped** (in `main`, with the module named), **changed** (shipped,
but not as first designed: the difference is stated) or **design** (not built).

## 0. Summary

A room is a cell `R`. A capability whose target set is `under R` covers `R` and every cell whose
parent chain reaches `R` (`Theory/TypedAuthorization.lean`, `TargetSet.under`, `Parentage`;
`Theory/RoomAuthorization.lean`, `room_confidentiality`, `room_admission_traces_to_root`).
A cell is born into a room with `--in R`; the birth gate admits it only under a grant that
covers `R` and makes the creator its owner (`Kernel/RoomBirthGate.lean`,
`birth_under_room_requires_grant`, `room_birth_owner_is_creator`). Inside a room, friends
compose a few cell shapes: per-author streams (§2.3), hyperdocuments (§2.4), declared cells
under laws (§2.2, §2.6, §2.8), and runners that act under grants and pay for their turns
(§2.7, §2.10). The kernel admits or refuses every turn; nothing in the client decides.

Changed from the design: `under R` is transitive (a room under an area under a realm is
under the realm) and includes `R` itself; the design had one level and excluded `R`.

## 2. The constructs

### 2.1 Room. **Shipped, changed.**

The room, the birth gate and the confidentiality theorems are in §0. The shell verbs are
`room new`, `room invite` (one delegation `under R`, with narrowed verbs and fields),
`room welcome`, `room list`, `room members` and `room kick`. J10 is three journeys:
`journey.d/j10-kernel.sh` (kernel rows: a member's invite covers the room cell and every cell
born in it; a third key is refused), `journey.d/j10c.sh` (the same through `mini shell`, and
the kick of §2.2) and `journey.d/j10-index.sh` (the presence index of §2.5 and a read at a
past height, §4.5).

### 2.2 Workroom: documents, a board, and a kick. **Shipped.**

A workroom is a room holding content documents, a board and member streams
(`native/resource-client/templates/room/workroom/template.shell`, §4.9).

The board is a declared cell under a law the shell writes (`native/resource-client/src/shell.rs`,
`board_law`): task `n` has its state in field `2n+2` (0 todo, 1 doing, 2 done) and its owner
in field `2n+3`; a state never goes backwards and an owner, once taken, is never replaced.
The law covers tasks 0 and 1, and `board new` declares exactly fields 2–5, so the Host refuses
any other field by name.

A kick ends a member's authority in the room, including over the cells that member created
there (`Kernel/RoomKick.lean`). The owner and control grants of a cell born in a room carry the
creator's placing capability and its ancestors (`Kernel/ResourceBirthPolicyController.lean`,
`Concrete.BornLineage`), so revoking the creator's room grant refuses them and everything
attenuated from them (`kick_revokes_room_born_authority`, `kick_revokes_born_descendants`).
The founder's own room grant is outside that lineage and keeps every cell
(`founder_keeps_room_after_kick`). Covered scope: grants born through the room birth gate;
a root birth names no placing capability and its grants carry no ancestors.

J12 (`journey.d/j12.sh`) runs this through `mini shell`: two friends append, edit with the read
line as guard, link, list backlinks, move board tasks and revoke; a stale edit, a third key, a
reviewer's write, an append-only edit, a backwards task and a revoked read are refused with
their reason.

### 2.3 Social space: per-author streams. **Shipped, changed.**

A member speaks by appending to their own stream, a `stream` cell born `--in R`
(`Kernel/StreamResource.lean`, `Compiler/StreamCell`). The timeline is the merge of the
roster's streams; `tail` orders entries by (height, author, cell, sequence)
(`native/resource-client/src/chat.rs`). Topics, pins, unpins and reactions are typed entries in
the speaker's own stream, never writes to another member's stream. Because each author writes
only their own stream, appends by different authors never stale each other
(`append_admits_disjoint_authors`); and an append is computed at the head it meets, never at
its planned root (`append_planned_root_irrelevant`), so parallel appends to one stream all land,
in admission order.

(a) Who may write a stream is a law installed at birth (`StreamResource.authorLaw`): every
`mutate` or `append` must be signed by the author (`authorLaw_refuses_other_writer`,
`authorLaw_admits_author`). The room founder births each member's stream
(`templates/room/social/member.shell`); the founder pays for it and owns it, and its law
refuses the founder's writes like anyone else's. `create --owner SUBJECT` can instead birth it
owned by the member. The member speaks with the room grant (`observe` + `append` under `R`), so
a kick ends that too.

(b) Field-scoped grants (K-FIELDS, §5 item 10) exist but streams do not use them.

Changed from the design: a stream is a head cell plus one fresh cell per entry, not one
`eventHistory` cell; the room roster lives in the room cell's fields (founder in field 2,
member `k` in fields `2k+1` and `2k+2`). J11 is `journey.d/j11-kernel.sh` (kernel rows) and
`journey.d/jchat.sh` (client rows); `journey.d/jfeedback.sh` uses the same room shape for a
member's private feedback room.

### 2.4 Hyperdocument. **Shipped, changed.**

A document is a content cell (`Kernel/ContentResource.lean`, `Command`) born under a room.
The shell's `doc` verbs author its actions: `createDocument`, `createAtom`, `editAtom` (the
expected prior record is the guard; a moved line is refused `staleAtom`), `link`, `annotate`,
`transclude`, `mark`, `editElement` and the rest. Backlinks are a fold over the accepted log
(`Kernel/LinkIndex.lean`), not stored state. A past version is a signed `at` read (§4.5).

A transclusion is made by a subject holding observe on the source and mutate on the host;
disclosure is decided at transclusion time, under the transcluder's own observe grant
(`Kernel/DeclaredResourceController.lean`, `transclude_requires_source_coverage`;
`Kernel/ContentResource.lean`, `transclude_uncovered_refused`). A snapshot transclusion shows
the pinned bytes or says `moved`, never other bytes (`transclusion_pinned`).

Changed from the design: a reader without a grant on the source sees a placeholder and no
byte of the source (`journey.d/jdocuverse.sh`, J19), where the design let any reader of the
host see the quoted bytes. The docuverse verbs are described in `docs/DEOS.md`.

### 2.5 Presence and history. **Shipped, changed.**

`Kernel/PresenceIndex.lean` keeps two maps that are functions of the accepted log:
`lastSeen : (cell, subject) ↦ height`, the greatest height at which a record signed by that
subject wrote that cell, and `touched : cell ↦ height`, the greatest height at which any
record wrote it. `lastSeen_exact` and `touched_exact` state that the index agrees with the
fold, so a tampered index is refutable.

The Host serves them as signed queries (`Compiler/NativeObservationCodec.lean`, `QueryView.who`,
`QueryView.since`; `Kernel/NativeObservationController.lean`): `who R` lists the members with
their greatest height over cells under `R` the reader's grant covers, and `since R H` lists
the log entries above `H` that wrote such cells, with those cells alone.

Changed from the design: the index is cached on the loaded image
(`DurableReceiverIO.Loaded.index`), not kept in the system cell or carried in the checkpoint;
`touched` holds one greatest height per cell, not a per-height journal. The shell verb is
`since`, not `history ROOM`.

### 2.6 Laws with teeth. **Shipped.**

The shell's one-line law grammar (`native/resource-client/src/shell/law.rs`) renders to the
Host's `Pred` JSON and adds no semantics: clauses joined by `;`, `any [ … ]`, `all [ … ]`,
`not ( … )`, `sealed` (`any []`), `open` (`all []`), `field N monotone`, `field N writeOnce`,
slot comparisons against a value or a set, and slot-to-slot comparisons (`eqSlots`, `leSlots`).
Slots are `field N` with `before`, `after` or `delta`, `pair A,B delta`, `subject`, `verb`,
`cost`, or any projected slot by name. A refusal by a law names the clause that failed (§4.6).

J13 (`journey.d/j13.sh` → `law-leaf-journey.sh`) installs a board law in that grammar; B's
forward move is admitted (its grant survives the law change); B's backward move and
out-of-range move are refused with the failing clause named; A seals the board and A's own
repair is refused.

### 2.7 Computation: Hermes as a runner in a room. **Shipped.**

A runner is an enrolled subject with grants under a room and a Book account it pays its turns
from. The kernel never runs the program; it admits the runner's turns like anyone's.

`summon ROOM as ROLE [--budget N]` (`native/resource-client/src/hermes.rs`) is the founder's
verb. It births the room's till if absent, births Hermes's budget account funded with `N`,
adds Hermes to the roster with its own stream, births and delegates the role's documents, and
writes the program document into the room. The roles are the files under
`native/resource-client/templates/hermes/` (`librarian`, `runner`); they differ only in grants
and program text. `ask` is an entry in the asker's stream addressed to Hermes; `dismiss`
revokes Hermes's grants.

Hermes's controller for one room is `native/grain-runtime/src/hermes_room.rs`. Its tools
(`native/grain-runtime/src/resource_tools.rs`, `room_tool_specs`) are lines of the pinned
`mini` client's shell run under Hermes's own workspace, so no tool holds authority the
workspace lacks. Every write is preceded by one fleet turn paying the room's `hermes/turn`
price into the till; an account that cannot cover it is refused at plan (`bookRefused`) and
the write is not attempted. J14 (`journey.d/j14.sh`) runs the librarian with the deterministic
provider (`native/hermes-test-provider`, `--room-librarian`).

What is trusted: the kernel guarantees Hermes cannot spend more than its account holds and
cannot write what it holds no grant on. That each write follows its payment is the
controller's discipline, shown in its journal (K-BOOK-SLOTS, §4.8, would make it a law).

### 2.8 Interactive story. **Shipped, changed.**

A story is a transition table a friend writes as a document in the story's room, then seals
(`native/resource-client/src/story.rs`). After the seal, the client installs one law on every
player's cell, generated from the table (`Kernel/StoryLaw.lean`, `law`): only the player moves;
the turn counter goes up by one; the scene stays or follows an edge of the table; a conditional
edge needs its item; an item is taken only in its scene, goes from 0 to 1 and never back. The
law's management clause admits only reads and writes, so nobody, the author included, can
install another law, delegate or revoke on the cell.

`Assurance/StoryLaw.lean` proves what that law admits for every table: `scene_step`,
`sealed_story_scene_monotone`, `no_rewind`, `sealed_story_never_relawed`, with both poles on
the example story (`legal_step_admitted`, `rewind_refused`, `take_twice_refused`,
`install_refused`). The example's law is the client's output, embedded by
`scripts/gen-storylaw.py` and equal to `law taleTable` by `rfl`.

Changed from the design: the law is on each player's cell, not on one shared `R/state` cell.
J15 is `journey.d/j15.sh`.

### 2.10 Credit, membership, budgets. **Shipped, changed.**

A room's tariff is declared fields on the room cell itself (`native/resource-client/src/room_schema.rs`,
`TARIFF_FIELDS`: `week`, `birth`, `hermes/turn`, `till`, `period`, …), written only by a holder
of `mutate` on `R`. Paying for a week is one fleet turn moving credit from the payer's account
to the room's till and publishing `renew` (`native/resource-client/src/credit.rs`). The till's
incoming ledger is a signed Host read of the accepted journal (Host op 180,
`Kernel/NativeHost.lean`, `FleetIncomingEntry`).

The room's concierge (`native/grain-runtime/src/concierge.rs`) is a deterministic runner
holding `delegate` under `R`. It reads the ledger, reads the tariff at the height the payer
quoted, and for a payment that covers the week delegates `member` under `R` with
`notAfter = max(entry height, current notAfter) + period`; any other payment is refunded from
the till. The kernel enforces the window (`Admissible.validUntil`, refusal `outside-validity`).
When `week = 0` the room is free and the concierge issues on request. A Hermes turn's payment
is the same fleet turn with topic `hermes` (`credit --action turn`).

What is trusted: the concierge. The kernel checks that its delegations are admitted under the
founder's grant and that windows expire; it does not check that a delegation followed a
payment (§4.8). The concierge's journal names the ledger entry each decision acted on.

Changed from the design: the tariff is on `R`, not a separate `R/tariff` cell; payments the
concierge does not honour are refunded. J17 is `journey.d/j17.sh`.

## 4. Kernel and host changes

### 4.4 K-STREAM. **Shipped, changed.**

`Kernel/ResourceTransaction.lean` has `Payload.append (request : StreamCell.Append)` beside
scalar and content payloads. The target's patch is one guarded write of the stream head
(`StreamResource.append_footprint`) and the record is one fresh entry cell at the next
sequence (`append_entry_at_next`). `Verb.appendObject` (`Theory/TypedAuthorization.lean`) is
covered by itself or by `mutateObject`. An `append` naming a fleet topic head is refused
`wrongRole` (`room_append_refuses_topic_head`).

Changed from the design: one cell per entry, not an allocation in one `eventHistory` cell.

### 4.5 K-HISTORY-READ. **Shipped.**

`QueryView.atHeight` (`Compiler/NativeObservationCodec.lean`) returns a cell's canonical bytes
as of a height, admitted by the same observation check as a current read
(`Kernel/NativeObservationController.lean`). `doc show --at H` and `doc diff` use it.

### 4.6 K-LAW-LEAF. **Shipped.**

`Pred/Leaf.lean`: `firstFailingLeaf` walks `eval`'s own recursion and returns the path to the
first false clause. `firstFailingLeaf_none_iff_eval` says it reports nothing exactly when `eval`
accepts; `firstFailingLeaf_some_leaf` says the named subterm is a leaf `eval` rejects on the
same step. `Compiler/RefusalReason.lean` carries the leaf in the `lawDenied` refusal. The walk
descends only through conjunctions, so a guarded disjunction is named whole.

### 4.8 K-BOOK-SLOTS. **Design.**

Not built. The design projects a command's Book postings into law slots
(`joint/target/{book}/balance/{account}/{asset}/{before,after,delta}`), so a law could join a
write or a delegation to the posting that paid for it in one transaction. Until it exists, the
concierge (§2.10), Hermes's payment-before-write (§2.7) and the MUD sheet's cure law
(`templates/mud/sheet/law.sheet-cure-lawful`) rely on the runner's journal, not the kernel.

### 4.9 Room templates. **Shipped.**

A room template is a file of shell lines, exactly what a friend could type
(`native/resource-client/src/shell/template.rs`). `room new NAME --template T` binds `$ROOM`
and `$ME` and runs the lines as the founder; `room welcome NAME SUBJECT --template T` runs the
member lines with `$MEMBER` bound. Every line is one ordinary verb the Host judges. The
built-in templates are `native/resource-client/templates/room/` (`workroom`, `social`, `story`,
`chat`, `private`), compiled into `mini`; `room template show T` prints the file.

## 5. Items

The lanes the code names, with their state. Each exit is a journey row in `journey.sh`.

| item | name | state | where |
|---|---|---|---|
| 1 | P-SHELL-DOCS: `doc` and `board` verbs | shipped | `shell.rs`; J12 |
| 4 | K-STREAM: append payload, per-author law, `say`/`tail` | shipped (§4.4) | `Kernel/StreamResource.lean`, `chat.rs`; J11, JCHAT |
| 6 | P-CREDIT and the concierge | shipped (§2.10) | `credit.rs`, `concierge.rs`; J17 |
| 7 | P-HERMES-ROOM: room tools, roles, `summon`/`ask`/`dismiss` | shipped (§2.7) | `hermes.rs`, `hermes_room.rs`, `resource_tools.rs`; J14 |
| 8 | P-STORY | shipped (§2.8) | `story.rs`, `Kernel/StoryLaw.lean`, `Assurance/StoryLaw.lean`; J15 |
| 10 | K-FIELDS: `Scope.fields`, `maxDelta` | shipped | `Theory/TypedAuthorization.lean`; `journey.d/jfields.sh` (J12d: a reviewer granted `fields = {annotations}` annotates and is refused a body edit) |
