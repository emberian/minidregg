# Native Generic Simplex agreement

Generic Simplex is Mini's domain-log agreement engine. Its core (`Kernel/GenericSimplex`,
`…Quorum`, `…Local`, `…Structure`, `Compiler/GenericSimplexIO`, `…Codec`, `…SourceAnchor`) is in
the `Host.Main` closure. The safety proofs build in the `SimplexQualification` library. The
controller, participant, serve and native modules build through the executables `generic-simplex-harness`,
`generic-simplex-log-reopen`, `generic-simplex-load` and `minidregg-four-source-fixture`
(`lakefile.toml`). The transferable COMMIT witness (`Compiler/GenericSimplexTransferability`)
and reconfiguration (`Kernel/GenericSimplexReconfig`) build only in the opt-in `ResearchWip`
library.

The model is a fixed committee of n = 3f + 1 with at most f cumulatively Byzantine
members, authenticated reliable delivery and partial synchrony. The configured
timeout must cover the paper's timing bound and actual source validation. Fair
polling alone does not make missing historical source inputs available. Changing
membership, mobile faults and perpetual storage compaction are separate work.

## Durable decisions

The native journal is the running replica's (`Replica.step`, blocks relative to its
committed height). It replays exact entries and releases newly enabled messages only after
compare-and-append plus exact readback. A peer cannot supply a source checked event.

A certificate is a quorum of distinct ML-DSA-65 signatures on one COMMIT statement. It does
not require each signer to have locally output a commitment. A Byzantine sender can supply
the final COMMIT only to one honest replica; that replica passes the original signed COMMITs
on to a member that asks (`Replica.owed`), without obtaining a new quorum of local output
attestations.

A COMMIT packet carries its signer's transferable signature, covered by the pairwise MAC of
whoever sends it. The recipient verifies both, then retains the signature and the counted
delivery in one journal transaction. The statement binds the exact committee context, the
view, and the chain as its length and running digest, with the COMMIT-SEND v4 domain
separator.

The journal and wire schema are not an implicit migration path from an older profile.
Reconfiguration must preserve existing liabilities; a fresh file or epoch number is not
proof that old certificates cannot complete.

## Departure from the paper: the view timer (fix C)

**The paper.** One fixed view timer: a replica that enters a view sets its
deadline to `now + timeout`, and the liveness argument needs `timeout ≥ 7Δ` for
the delay bound Δ that holds after GST (the profile's stated premise). An
underestimated Δ is never repaired: every view can time out forever.

**Here, exactly.** `enterView` sets the deadline to `now + viewTimeout c s number`
(Kernel/GenericSimplex.lean), where

    viewTimeout c s number = timeout · 2^min(number − (lastCommittedView s + 1), backoffCap)

with truncated subtraction, and `lastCommittedView s` the highest view this
replica has locally committed (`doCommit`), 0 if none. Since the commit floor (below) the
kernel reads the maintained field `s.lastCommitted` instead of that fold. So the exponent counts the
views strictly between this replica's latest local commit and the view being
entered, capped at `backoffCap`. That is the whole delta from the paper:

- `backoffCap = 0` is the paper's timer exactly (`viewTimeout_fixed_of_cap_zero`).
- For every cap, `timeout ≤ viewTimeout ≤ timeout · 2^backoffCap`
  (`viewTimeout_bounds`), and the view right after a local commit runs on the
  fixed timer again (`viewTimeout_after_commit`). All three are theorems in
  Kernel/GenericSimplexEngineSafety.lean with pinned axioms.
- The exponent is LOCAL: replicas that committed different latest views run
  different deadlines in the same view. A late certificate for an older view
  does not reset the exponent unless that view is the highest committed one.
- The deadline is read only by the `tick` branch of `step`, to decide when this
  replica sends CANDIDATE(⊥) for its current view. No VOTE, COMMIT, prepare,
  disable or safe-parent rule reads it. The safety theorems
  (GenericSimplexEngineSafety, SimplexQualification) quantify over the
  executable `start`/`step` with this `enterView`; they were rebuilt against it
  with their statements and axiom pins unchanged.
- Liveness is NOT a theorem here, for either timer. The intended argument
  (INFERRED, not formalised): after finitely many uncommitted views the timer
  reaches `timeout · 2^backoffCap`; if that is at least 7Δ the paper's argument
  applies from then on. A Δ above `timeout · 2^backoffCap / 7` is still not
  survived.
- The cost: after a stall, a view whose leader has crashed costs up to
  `timeout · 2^backoffCap` before CANDIDATE(⊥), until some view commits.

`backoffCap` is the fifth `Config` field, so it is part of the agreed `Context`
and every replica of one instance runs the same policy. The four-source fixture
uses `backoffCap = 3` (a view timer of 100 s growing to 800 s).

**What broke.** Contexts carry five `Config` fields; a four-field `context.bin`
does not decode. The journal magic is `MINI-SIMPLEX-LOG` version 2 (3 since the quiescent leader below); an older
journal refuses at the magic instead of being reinterpreted. COMMIT signatures
cover the encoded context, so no old certificate verifies. A mesh moves to fix C
by re-genesis (`init` a new context), not by conversion.

**The test.** `Verify.GenericSimplexHarness` (exe `generic-simplex-harness`)
replays the recorded 00f711 stall in the pure kernel: in views 1 and 2 the
VOTEs to replicas 0 and 1 arrive after their deadlines, so under both timers
those views end with COMMITs from exactly replicas 2 and 3, CANDIDATE(⊥) from 0
and 1, and no certificate. From view 3 every message takes 1.5·timeout (ten
times the timeout/7 premise). The backoff timer (`backoffCap = 3`) then commits
the pending block in view 3 at all four replicas, with no resubmission and
prefix-consistent deliveries; the fixed timer under the same schedule commits
nothing, which the harness asserts, so the check fails without fix C (removing
the backoff from `viewTimeout` turns it red: "backoff: pending block never
committed").

## Departure: the quiescent leader

**Before.** The leader of every view proposed on entering it: its best parent
extended by a checked offer, or by an empty block when it had none. An idle
domain therefore committed an empty block every view, so the number of views
and the length of every block (exact ancestry) grew without bound, and each
replica's per-input cost grew with them (measured on a copy of the 00f711
evidence: CPU per appended input 0.57 s rising to 1.68 s over 45 minutes idle).

**Now, exactly** (Kernel/GenericSimplex.lean, `hasWork`, `propose`,
`progressOuter`):

- `propose` acts only if `hasWork s`: some offer `b` has `validBlock s
  (bestParent s ++ [b])`, or the best parent was prepared at least two views
  back (`bestParentView s + 1 < s.current`) and is not a prefix of the local
  `committedTip`. Otherwise it returns the state unchanged.
- A leader may propose late: each `progressOuter` call lets the leader of the
  current view propose if that view has no recorded proposal and the leader has
  not requested its disable. The recorded proposal makes it at most once per
  view; the existing rules are unchanged.
- A parent prepared in the immediately preceding view is not work, because that
  view's own COMMITs normally commit it. If they never come (the 00f711 shape:
  two COMMITs), the next view ends by CANDIDATE(⊥) and the leader of the view
  after it extends the parent with an empty block, which commits it.
- Safety: the theorems quantify over this executable `step`. The nine
  invariant files' `progressOuter` lemmas gained the `propose` case (the
  existing `propose_*` lemmas); no statement changed. The witness executions
  (GenericSimplexWitnesses) begin with checked offers, since a leader with
  no offer no longer proposes; they still exhibit a committing honest run and
  the f+1-fault conflicting commits.
- Consequences: an idle domain proposes nothing, and since log format 7 its
  view does not end either (the idle timer, below). An operation arriving
  mid-view is proposed by the current leader at once. A stuck prepared parent
  costs one extra view. Liveness is not a theorem here.
- Journals record inputs, and replaying them under a different `step` would
  reinterpret them, so this is log format version 3; older logs refuse at the
  magic.
- Test: `Verify.GenericSimplexHarness` "idle quiescence": one operation, one
  proposal over t = 20000, no CANDIDATE(⊥) and no view ended after it, and a
  late offer committed within 50 time units of being checked.

## Journal checkpoints (log format 4)

A replica's journal is its input log, and reopening used to replay every input
since genesis (97 s per replica on the 00f711 evidence copy). Now:

- A base frame may carry `snapshot : Option State`. Replay starts from it when
  present (which must be this replica's own, non-failed state), else from
  `start` (GenericSimplexIO.replayLog).
- `checkpointRestored` builds the checkpoint of an in-memory image: one base
  frame whose snapshot is the replayed state, with every retained COMMIT
  witness, no events and no deltas. `restoreLog_checkpoint` proves the new
  image restores to the same state, so the in-memory image is installed without
  replaying anything (pinned axioms).
- The writer helper's OP_REPLACE swaps the file atomically, length-checked
  under the writer lock (staged file, rename), and keeps
  the replaced image as `agreement.log.upto-<length>` (a hard link). A standing
  replica checkpoints every 1024 deltas (`checkpointEvery`), and a writable open
  that had to replay at least as many checkpoints at once.
- What reopen no longer does: re-derive the state from genesis. It decodes the
  snapshot the same replica wrote, under the same trust as the input log it
  replaced (private, single-writer storage). The whole input history is kept as
  the segment chain, and `minidregg-four-source-fixture audit-journal ROOT N`
  (`auditSegments`) replays it from genesis, requiring every segment to open
  with exactly the state the previous one replays to.
- BREAKS: log magic version 4; version-3 logs refuse by name. The legacy
  whole-image `agreement.bin` path (`restore`, `convert-journal`) is deleted:
  since fix C no pre-epoch mesh can be converted, only re-genesised.

## Commit floor and erasure (log format 6)

**What it is** (Kernel/GenericSimplex.lean):

- `State.lastCommitted` is the commit floor: the highest locally committed view, raised by
  `commitAt` (`doCommit` then `raiseFloor`). It is the fold `lastCommittedView`
  (`Kernel/GenericSimplexFloor.lean`, `lastCommitted_spec`).
- A view at or below the floor has one behaviour, refusal: `valueRules` and `argumentRules`
  do nothing there, `pass` walks only the views above the floor, and `ingest` takes no
  message for it. No rule reads a view below the floor; the floor view is read only as a
  parent (`isSafe`, `bestParent` range over `parentViews`: the floor and the views above it).
- `floorJump`, first in every pass: a replica at or below its floor enters the view after it,
  on the base timer (`viewTimeout_after_commit`).
- `forget` drops the views below the floor and the audit. `liveStep` is `step` then `forget`:
  the transition a running replica executes. `step` keeps everything and is what the safety
  theorems are about.
- Erasure (`Kernel/GenericSimplexErasure.lean`, kernel-only, proved):
  `step_erase : forget (step c s i) = forget (step c (forget s) i)`, hence
  `liveStep_run`: a replica running `liveStep` is, input for input, the `forget` image of the
  same replica running `step`. Every theorem about a `step` replica's sends, commits,
  delivered blocks, failure, view and floor is a theorem about the running one. The pump's
  fixpoint test compares `forget` images for this reason.
- Rebase (issue #2): two states with the same `forget` image send, commit, deliver and fail
  identically on every input sequence (`rebase_observational`). That equation is the whole
  condition on a restart-rebase; forgetting the floor itself breaks it and halts the replica
  (`Verify/GenericSimplexJumpStarvation.lean`, `forgotten_floor_halts`).
- Commit evidence: raising the floor records the COMMIT messages that committed it
  (`floorEvidence`). A replica still in a view a whole timeout after asking to leave it
  repeats its CANDIDATE(⊥); a peer whose floor has passed that view queues its evidence for
  the asker in `relay` (`serveFloor`, once per peer per floor); the driver forwards and
  drains it (`drainRelay`). The receiver commits by the ordinary COMMIT rule, so the evidence
  needs no new trust. Executed: `stranding_ends_with_floor_evidence` (stuck on a network
  that never forwards `relay`; three more commits on one that does, with no input from
  outside the kernel's own outputs).

**Not proved** (stated in `Verify/GenericSimplexJumpReach.lean`): `SettledBelowFrontier`,
`EventualCommit`. Not stated as theorems: that every send is above the floor (executed:
`floor_refuses_executed`), and that received evidence installs the floor (executed above).

## The retained engine (log format 7)

**Checked set and offers** (`Kernel/GenericSimplexChecked.lean`, proved). The measured
cost under load was not the view walk: time per operation rose with the fourth power of
the chain length, because `hasWork` rescanned every offer ever made and each `validBlock`
searched the whole `checked` list once per prefix. Now:

- `State.checked` keeps the maximal checked source histories (`addChecked`). The native
  checker replays a history from the pinned genesis, which replays every prefix of it, so
  validity is prefix-closed (`validBlock_prefix`) and one growing chain is one entry
  (`addChecked_chain`); no kept history is a prefix of another (`addChecked_antichain`);
  checking a block makes valid exactly the prefixes of its history (`addChecked_exact`).
- `validBlock` walks the block once per kept history.
- A committed payload leaves `offers` (`doCommit_offers`) and is not offered again
  (`addOffer`): the offers are the pending work.
- Bound: one input costs O(L · (m + k) + p), with L the payload count of the longest live
  block, m the messages kept in the views above the floor, k the kept histories (1 for one
  chain; one per checked fork) and p the pending offers. In the specification L is the
  whole chain, because a block there is its exact ancestry (interpreter, four replicas:
  15 ms per operation at 40 operations, 83 ms at 160; before, 3,009 ms at 40). In the
  running replica L is the payloads above its committed height (next section).

**Idle timer** (`wantsOut`). A view's timer runs only while this replica has a reason to
leave it: a checked offer on its best parent, a prepared parent not yet in its committed
tip, a proposal in the view, its own earlier request to leave, CANDIDATE(⊥) from
`faults + 1` members, or `faults + 1` members ahead of it. Otherwise each tick moves the
deadline one whole timeout ahead. An idle domain therefore stays in its view, sends
nothing and keeps a constant state; work that arrives gets the whole timeout. This was
chosen over summarising runs of disabled views because the idle views were also traffic
and journal appends, and because no safety rule reads the deadline, so no safety theorem
moved. What still grows: a stretch with work pending and no commit possible adds one view
per `timeout · 2^backoffCap`.

**View window** (`Kernel/GenericSimplexWindow.lean`, proved). `ingest` keeps a record only
for views up to `horizon` = `Config.window` (two leader rotations) above the current view.
A message above it leaves only an `ahead` note, one per member (`ingest_beyond`,
`noteAhead_unique`); a message within it that the replica has not received is registered
exactly as before (`ingest_within`, `ingest_within_propose`). Recovery of what was
dropped: `faults + 1` members ahead is a reason to leave the view; a replica still in a
view a timeout after asking repeats its CANDIDATE(⊥); a peer that has left that view
answers the repeat with its own messages for it and the following `window` views
(`serveViews`, through `relay`). Executed (`Verify/GenericSimplexWindow.lean`): 3,000
far-future messages create no record; a replica twelve views behind with everything above
its horizon dropped reaches the others' view, and stays behind when `relay` is not
forwarded. A COMMIT is the one kind `ingest` takes above the horizon: a quorum of them
moves the floor, and a replica that dropped them could never learn it is behind a commit.
The specification does not bound them; the running replica does (next section).

## The running replica: relative blocks (`Kernel/GenericSimplexRelative.lean`)

`Replica.step` is `liveStep` between a codec and a delivery policy. It adds no rule.

**Codec.** A block is the payloads above the replica's committed height, in memory and on
the wire. A `WireMessage` carries its sender's height and that suffix. A receiver at the
same or a greater height drops the part it has committed (`decode`); one at a lower
height cannot read the block and keeps only that the sender is ahead. After a commit the
replica moves its origin (`rebase`): the height rises, every kept block loses the
committed payloads, the floor view keeps only the parent it offers, and a received message
whose block does not extend the commit is dropped. If something the replica itself sent,
prepared or proposed does not extend the commit, it halts (`failed`): the safety theorem
excludes that state under at most f faults. The checker reports source records the same
way, relative to an application height (`WireInput.checked`).

**Delivery policy.** Holding, dropping and reordering deliveries is what the
specification's network may always do, so the policy carries no safety argument.
- A COMMIT the replica cannot read yet, or for a view above its horizon, is held: one per
  member (`holdFar_unique`), the one for that member's highest view. The engine gets held
  COMMITs when they are readable and within the horizon, or when a quorum of members holds
  the same view and block and no record above the horizon is already waiting (`release`).
- The cap on a member's messages of one kind in one view record is not policy: it is the
  specification's (`Config.cap` = `parties + 1`, `overCap` in `ingest`; proved:
  `GenericSimplexWindow.ingest_over_cap`). A correct member sends at most `2 * faults + 2`.
- The hold of far COMMITs is still policy here, and the specification still takes any
  number of COMMITs above its horizon. Moving it means `State` holds messages that are
  authentic but not yet received, and `step` receives them later on its own: every
  invariant of the proof closure that speaks of received messages (`backed`, the receive
  provenance and scope families) has to carry that set. Not done.
- `addOffer`'s refusal of a payload already committed sees only the payloads above the
  height (none between inputs). Not offering a committed operation again is the driver's.

**Recovery.** A replica keeps the COMMIT evidence of its last `Config.window` commits,
each relative to the height before that commit. A peer that asks to leave a view from a
lower height is sent, each time it asks, every kept commit from its height on, in order.
A replica further behind than its peers keep needs the earlier certificates in order from
a durable record: that transfer is the driver's, and `CommitTransfer` in `EventualCommit`
must be read as in-order for it.

**Bound.** One input costs O(u · (m + k) + p + n²): u the payloads of the longest
uncommitted block, m ≤ (window + 2) · 4 · n · (n + 1) kept messages, k kept checked
histories, p pending offers, n held COMMITs. None depends on the committed height.
Interpreter, four replicas, 640 operations: 13 ms per operation at 10, 15 ms at 160,
10 ms at 640; every kept block is empty between operations.

**Agreement.** The safety theorem of this engine is proved on an abstract model: a trace
of sends, prepares, disables and commits that meets the local obligations `LocalFaithful`
(`Kernel/GenericSimplexVAInvariant.lean`) has prefix-comparable commits. The model reads
no proposal, timer, offer, cap or validity check. The statement for the running replicas
is therefore `RelativeFaithful` (`Verify/GenericSimplexRelativeReach.lean`): every
reachable network of running replicas has a trace of that model which is its own
(`Faithful`: the trace's sends by correct members are exactly the durable record read as
whole chains, and each correct replica's chain is a commit of it).

- Proved: `relative_agreement_of_faithful` (with it, agreement of the running replicas);
  the codec reads the chain the sender meant when the receiver's committed chain is a
  strict prefix of it (`above_denotes`); moving the origin keeps what a block denotes and
  drops exactly the blocks that do not strictly extend the commit (`strip_denotes`,
  `strip_conflict`).
- Proved, the two facts the induction rests on (`Kernel/GenericSimplexSupportExtends.lean`,
  on the model and on the specification's reachable networks):
  `support_extends_commit` / `reachable_support_extends` (a VOTE, CANDIDATE, READY or
  COMMIT a correct member sends for a block in a view above a committed view is for a
  strict extension of the committed block) and `reachable_counted_extends` /
  `conflicting_count_small` (a block that does not strictly extend the commit is counted
  for at most `faults` members above it, below every threshold a rule reads). PROPOSE is
  not covered and need not be: no obligation of the model reads a proposal.
- Proved, the local half. The trace is the run's own and lives on the proof side: no
  replica field and no byte moves.
  - `Kernel/GenericSimplexTrail.lean`. `Good` is what a list of whole-chain events must
    meet, each event against the strict prefix before it, to be a trace of the model
    (`good_faithful`: it gives `LocalFaithful`). `Ghost` is one correct replica's side: a
    specification state `G` with its audit retained whose `forget` is the replica's state;
    every event of its audit and every message it holds is in the trail read as
    `chain ++ block`, and every VOTE, CANDIDATE and COMMIT of the member in the trail above
    its floor is one of its audit. `ghost_step`: one `step` on `G` appends its new events to
    the trail, and `Good` and `Ghost` hold again; each event meets its obligation from the
    specification's own lemmas applied to `G` (`step_invariant`, `step_causal`,
    `step_origin`, `step_positive`). It also gives what the durable record needs: every new
    SEND is in the outbox, every outbox message is a SEND of the trail.
  - `Kernel/GenericSimplexFresh.lean`, three facts about `step` on any state that the above
    needs because the replica forgets views below its floor: `step_fresh` (a step's new
    events are for views above the floor it started from; new SENDs and the outbox
    coincide), `step_relay` (what it adds to `relay` is floor evidence or its own received
    messages above the floor), `step_evident` (the floor evidence changes only when the
    floor rises, to received messages of the new floor view).
  - `Kernel/GenericSimplexRebaseGhost.lean`. `ghost_rebase`: when the origin moves, the
    `Ghost` over `chain` becomes one over `chain ++ tip`. Its audit is the old one with every
    event above the floor read from the new origin (`rebaseEvent`). The trail gains the
    floor view's parent and one SEND per `tombstone`, each a faulty member's. `Rebased`
    states what `rebase` did to the views, by view number, and is a premise.
- Proved, the induction on the run (`Verify/GenericSimplexRelativeSide.lean`,
  `Verify/GenericSimplexRelativeFaithful.lean`): `relative_faithful`, `relative_agreement`:
  `RelativeFaithful` and `RelativeAgreement` hold if the initial network is tracked
  (`TrackedInitial`). The invariant is `Tracked net trail`: the trail is `Good`, each correct
  replica has its `Side` of it, and each COMMIT a correct replica holds was delivered to it
  and is authentic. `Side` is the replica's `Ghost` (its forgotten image is the replica's
  state), `FloorInvariant`, `Tipped`, and its wire side `Wire`: every message it has written,
  read through `denote`, is a SEND of the trail, and a COMMIT states its chain's length and
  digest; every SEND of the member in the trail is recorded or queued; kept evidence is
  written from a prefix of the chain.
  - `rebased_meets` (`Kernel/GenericSimplexRebaseMeets.lean`): when the map over the kept
    views in `rebase` succeeds, the state it leaves is `Rebased`. That the floor view's
    block is the tip is what the map checks; that the floor view is there is `tipped_floor`
    (`Kernel/GenericSimplexTip.lean`). When the map fails the replica halts as it was, and
    its side still holds: the proof does not need `rebase` to succeed.
  - `read_covered`, the reading lemma: what a replica decodes from an authentic message and
    `ingest` can record (`Readable`: not a PROPOSE, a view above the floor, a block for a
    VOTE or COMMIT) is a SEND of the trail at the reader's chain, by
    `support_extends_commit` for a block and `commit_reads_signed_chain` under
    `CollisionFreeOn (Occurs …)` for a COMMIT. A faulty member's message is added to the
    trail.
  - `side_finish`, `side_deliver`, `side_release`, `tracked_advance`: one input. A run of
    specification steps before one drain is `Ran` (`ran_step`); it loses no SEND because no
    rule removes a message from the outbox (`Kernel/GenericSimplexOutbox.lean`).
- Stated, not proved: `TrackedInitial`, the base case: the initial network is tracked. Its
  trail is the correct members' start audits one after another, each member's `Ghost` is
  `ghost_start`. It needs of `GenericSimplex.start` that nothing is committed and nothing is
  owed (`relInitial` starts every chain empty and records only the start's broadcasts), and
  `Good` and `Ghost` across the concatenation. Until it is proved, agreement of the running
  replicas rests on `TrackedInitial` in place of `RelativeFaithful`.
- Executed: `relNet_faithful` (the conclusion on a reachable network whose correct
  replicas have committed; the trace is the specification's run of the same operation and
  the two engines' sends coincide exactly), `twoNet_run` and the witnesses on it for the
  two facts (`support_extends_needs_above`: the view must be above the commit;
  `conflicting_count_tight`: the bound `faults` is met).

`RelativeRefines` is withdrawn. It asked for a reachable network of the specification's
`step` in which each correct replica stands in the same view at the same floor. The
running replica is not an image of `step`, in three places, none of which the model reads:
- A message whose block it cannot read (its sender has committed more) leaves a note that
  the sender is ahead (`deliver`). `step` notes a member ahead only for a view above the
  horizon. The note feeds `wantsOut`, so the replica can ask to leave a view where `step`
  on the same messages would not.
- `rebase` drops received messages that do not extend the commit (a VOTE leaves one
  `tombstone` per member). The member then has room under `Config.cap` again; in `step`
  its share of the record would still be full.
- After `rebase` the committed payloads are gone from the engine's state, so `addOffer`
  takes an offer of a payload the replica has already committed; `step` refuses it.

Executed (`Verify/GenericSimplexRelative.lean`): the same eight operations through both
engines end in the same views, floors and chains; a replica four commits behind is served
and catches up; one twelve behind stays behind until the COMMITs are replayed in order;
4,000 far COMMITs from one member leave one held message; fifty VOTEs leave five.

**READY once.** `argumentRules` sends READY for one argument once, by whichever of its two
rules (`2f+1` CANDIDATEs, `f+1` READYs) is enabled first; it used to send it once per
rule. The F1 schedule did not depend on the duplicate: its facts hold unchanged.

**The signed statement (version 4).** A COMMIT signature is over

    commitStatementBytes context view length digest =
      "MINI-SIMPLEX-COMMIT-SEND" ‖ 4 ‖ contextStream context ‖ nat view ‖ nat length ‖ bytesStream digest

(`Compiler/GenericSimplexCodec.lean`). Version 2 signed the whole chain, so two correct
signers at different heights could not write one chain the same way; version 3 signed the
32-byte chain half of the digest alone.

- `length`: the number of payloads of the chain the COMMIT is for, empty protocol payloads
  included (consensus ancestry, not the application height).
- `digest`: 64 bytes, two running cSHAKE256 digests of that chain side by side
  (`chainDigest context`). The chain half, over every payload: the empty chain's is
  `cSHAKE256(contextStream context, S = "minidregg/simplex/chain")`, and a payload extends
  `d` to `cSHAKE256(d ‖ bytesStream payload, S)`. The history half, over the nonempty
  payloads only (`historyDigest context`, `S = "minidregg/simplex/history"`): an empty
  protocol payload leaves it unchanged. `bytesStream` is the length-prefixed encoding the
  journal uses, so the chain's split into payloads is bound; both origins bind the context,
  so one domain's digest is not another's.
- Proved: `chainDigest_history` (the history half of a chain's digest is `historyDigest` of
  its application history). A holder of the source records alone can therefore check which
  records a signed statement orders, with no knowledge of where the empty payloads fell.
- `commitmentBytes context view block` is that statement for a whole chain: a specification
  function. Nothing that runs calls it.
- In the running replica (`Kernel/GenericSimplexRelative.lean`): a `Replica` keeps the
  digest of its committed chain and `rebase` extends it over the payloads it commits. A
  wire COMMIT carries its statement `(length, digest)` beside the relative block; `encode`
  computes it from the writer's digest and the block, so a peer that passes a COMMIT on
  from another height writes the same statement, and `decode` reads a COMMIT only when the
  block it reads has the stated length and digest. Cost is the block, never the chain.
- Proved: `commit_reads_signed_chain` (the block a replica reads under a statement is the
  signed chain, wherever it was written from, when the digest has no collision between those
  two chains); `commitmentBytes_binds_config` (equal signed bytes have equal context, view,
  length and digest) and `commitmentBytes_binds_block` (equal chains, under the same premise).
- The collision premise is `ChainDigest.CollisionFreeOn h occurs`: no two chains among those
  that occur have one digest. In `RelativeAgreement` and `RelativeFaithful` the set is
  `Occurs` of the network: the chains its correct members signed a COMMIT for, and the
  chains a correct replica reads from a COMMIT delivered to it at any committed height it
  has had. That is a finite set fixed by the run, so the premise says the run exhibits no
  collision, which is what cSHAKE256 can be assumed to give. Before, the premise was
  `∀ a b, h.of a = h.of b → a = b`, which no function into 64 bytes satisfies, so every
  theorem taking it was about the plain digest only. `ChainDigest.CollisionFree` keeps that
  strong form as the inhabitation witness (`plain_collisionFree`,
  `ChainDigest.collisionFree_on`). Teeth: `collision_breaks_agreement` (on a digest that is
  the same for every chain, two correct replicas commit `[[7]]` and `[[8]]` in a reachable
  network).
- `RelAuthentic` no longer has a clause for a relayed COMMIT: a COMMIT is authentic as its
  sender, view and statement, and its height and block are whatever the forwarder wrote.
- Executed: `forged_statement_refused` (three COMMITs with another chain's statement
  commit nothing). Gate plant `forged-digest`: on a digest that is the same for every
  chain the same three COMMITs are read, and the harness goes red.

**The native layer runs the running replica** (`Compiler/GenericSimplexIO.lean` and the
modules above it).

- Journal. An event is an encoded `Entry`: an input of `Replica.step` (`WireInput`, blocks
  relative to the replica's committed height), `flush sends owed` (the driver handed that
  many broadcasts and owed messages to its transport) or `consume count` (the application
  took that many committed payloads). `replayEvents` applies them with the domain's
  `chainDigest`; the snapshot of a checkpoint is the `Replica`, so a checkpoint is bounded
  by live state. A replayed replica is the journal's own member and has not failed:
  `replayEvents_kept` and `replayLog_kept` (proved, from
  `GenericSimplexRelativeSelf.step_self` and `start_self`). Neither a replay nor an append
  compares an identity while it runs; the one check left is on a decoded checkpoint
  snapshot, which is input. `Restored.deltas` counts the delta frames since the last
  checkpoint and is kept by the append, so no caller walks them.
- Outputs. An acknowledged entry leaves the replica's outputs in the journalled state
  (`sends`, `owed`, `committed`): durable before anything is sent. The participant seals and
  returns them, and acknowledges exactly what it returned at its next slice (`flush` with the
  counts), so a crash between the two sends them again. There is no outbox cursor and no
  retry round: a member that missed a message repeats its CANDIDATE(⊥) and is answered by
  the kernel (`serveFloor`, `serveViews`, the kept commit evidence).
- Duplicates. `settled` skips a delivery the replica already accounts for (received, a
  proposal for a view that has one, at or below the floor, unreadable from a sender that is
  not ahead, a COMMIT already held). CANDIDATE(⊥) is never settled
  (`candidate_bottom_never_settled`): the repeat is what the kernel answers.
- The tick. The participant journals a tick whenever the view's deadline is due, also after
  the replica asked to leave the view: that is the input on which the kernel repeats its
  CANDIDATE(⊥). An idle replica moves its deadline one timeout ahead per tick, and is
  ticked only when that deadline is due, so the deadline it holds may be about to pass. The
  participant therefore ticks an idle replica before handing it a packet or an offer
  (`wake`): work that arrives gets the whole timeout before the replica asks to leave. Without
  it a proposal arriving just before a stale deadline loses its view (with the fixture's
  100 s timeout, a 100 s stall). This is argued from the kernel's `tick`, not shown by a
  before-and-after run.
- COMMIT witnesses. A kept witness is `(view, length, digest, attestation)`: the statement
  and its signer's signature, no payload. The signature is checked against
  `commitStatementBytes` before the block is read; the kernel's `decode` then checks the
  block the delivery carries against the same statement. A packet names the member whose MAC
  covers it (`origin`); a COMMIT may be passed on by any member with its signer's signature,
  every other kind must be its origin's own. This replica signs a COMMIT only when the
  message is in its own undrained output (`ownCommit`), which replaces `exportable`'s read of
  old views and the audit. A checkpoint keeps the witnesses the replica can still use
  (`retains`: a view above the floor, or a commit whose evidence it still serves).
- Certificates. A `Certificate` is `(context, view, length, digest, signers)`; verifying it
  costs the signatures and nothing else. `recoverCommitment` builds the certificate of the
  newest commit from `Replica.evidence` and the kept witnesses. It is not shipped between
  replicas any more: peers get the COMMITs themselves, relayed.
- The application. `VerifiedCommit.Reads history` says a history's `historyDigest` is the
  history half of the signed digest. The participant keeps the running digest of its source's
  records beside the source (`JointReceiver.History`: computed once when the source is
  opened or reread, extended by each append through `Applied.history`).
  `JointReceiver.order` extends it by the record and the committed records after it (the
  replica's `committed` queue) and compares with the newest certificate: it hashes nothing
  below the record, and its token names the history without building it. `applyNext` hands
  the application one committed payload per slice and journals `consume` only after the
  source holds the record, so a restart hands it over again.
- Validation. Work is `(height, records)`: source records from an application height. One
  record directly on the verified source tip (every proposal while the application keeps up
  with the commits) is admitted there once (`JointSourcePrefixValidation.validateNext`, the
  same fresh derivation the ordered receiver runs before its append); its cost does not
  depend on the height. Any other work (records above committed ones the source has not
  taken yet, or a record the tip does not grant) is replayed as a whole prefix from the
  genesis in a scratch Store (`validate`), linear in the history; that path alone tells an
  invalid prefix from an unavailable dependency.
- Discovery. Each acknowledged delivery contributes the blocks it carries. A held COMMIT
  the replica reads later (`release`) enters its views under an input that carried no
  block, so whenever the held set (`Replica.far`) has changed the participant rediscovers
  over everything the replica holds. Without this a replica that rejoined behind the others
  never validated the block of the commits it had held, and stayed behind until restarted.
- The request spool. A client places `ID.call` or `ID.watch` in a replica's `requests`
  directory and reads `ID.receipt` from `receipts`. A served request is removed, so a slice
  reads only pending requests; a pending request is read once and searches only the source
  records appended since its last search. The receipt file holds the native receipt (which
  carries the accepted count and world root at the call's height) and no longer the source
  prefix through the call.
- Bytes. Packets are `ByteArray` from the transport to the codec and back (`encodeBytes`,
  `decodeBytes`); a journal append is a `ByteArray` frame. Kernel values (`Bytes`, `Block`)
  are still lists, as are the in-memory `Log` and the image read at open.

Executed (`Verify/GenericSimplexNativeRun.lean`, run by `generic-simplex-harness`): four
native replicas over in-memory journals and a stand-in helper session (signatures and MACs
are cSHAKE256 of the signer or pair and the bytes: not cryptography) commit one operation
through `sealPacket`, `authenticate`, `receiveCommit`, `receiveDelivery` and `flush`. A
COMMIT with another member's signature on the same statement is refused, a packet with a
broken MAC is refused, a VOTE passed on by a member that is not its sender is refused; a
COMMIT passed on with its signer's kept signature is counted; a counted COMMIT is journalled
with its signature; every journal and every checkpoint reopens to the same replica; the
certificate of the commit is a quorum on the statement and reads `[[7]]` and not `[[8]]`.
Executed end to end (`minidregg-four-source-fixture`, rows of
`scripts/gates/check-generic-simplex`): four participants over four native source Stores
with the Rust agreement helper (ML-DSA-65 signatures, pair MACs, the journal file), the
signature verifier and the Store helper. `probe-key` and `author-birth` make the call: one
ordinary content birth by subject 7, planned by `NativeHost.prepareLoaded` on the opened
Store and signed by the test signer (`sign-probe`, a public seed).

- `run`: admission at the proposer, validation at each verified tip, a certificate of three
  signatures on the statement, `JointReceiver.order` against the running history digest,
  the ordered append and readback on all four; then every helper is stopped, every journal
  and Store reread, and the original receipt is there with exactly one append.
- `lookup-all-call`: fresh processes read the same receipt and prefix from the four Stores.
- `serve-replica` ×4 and `await-call`: a second birth through four standing processes over
  TCP and the request spool.
- Plant `foreign-history`: every participant's running digest is another domain's, and the
  certified record is never ordered or appended.

Run by hand and not a gate row (20 s and more, timing dependent): six to forty calls on
standing replicas with a 2 s view timeout; one replica stopped for two calls and restarted.
The three live replicas commit after one view timeout (the stopped replica's leader turn);
the restarted one catches up through the kept commit evidence, one timeout per step.
`await-call` waits for all four receipts, so a call made while a replica is down is
uncertain to its client until that replica returns. A replica that restarts into an idle
domain is not told it is behind until the next operation.

Measured (`generic-simplex-load 640 10`, compiled, hbox, four replicas, instant delivery,
each input journalled through `appendRestored` under the deployed digest, outputs flushed,
committed payloads consumed, a checkpoint every 1024 deltas; no signatures, MACs or disk),
µs per operation at 10, 160 and 640 operations, three runs: 359 / 473 / 491, 577 / 890 / 904 and 571 / 813 / 634. Between checkpoints the
per-window series is flat (360 to 500 µs in the first run); a window that holds a
checkpoint is 650 to 800 µs. About 54 inputs and
2.4 to 2.5 KB of journal per operation; a checkpoint is 8,951 bytes at height 10 and 8,992
at height 640. The box is shared and the runs differ by more than the heights do. For
scale, the kernel alone on whole chains (`liveStep`, no journal, the harness before the
native adoption) took 420 µs per operation at 10, 1,731 at 160 and 7,660 at 640.

Measured end to end (forty sequential births on four standing replicas, 20 ms service
tick, hbox; client wall time includes starting the client and its 200 ms poll): 440 to
600 ms per call at every height. Before tip validation and the pending-only spool the same
run took 0.5 s at the first call and 4.8 s at the fortieth: each validation replayed the
prefix from genesis (68 ms at height 0, about 2 s at height 23), each receipt wrote the
whole prefix, and each slice reread every request ever placed. A slice now spends about
22 ms in validation and 22 ms in a proposal at every height.

Still growing with the history: the ordered append (`JointOrderedSourceReceiver.apply`:
derivation, the Store's compare-and-append, readback, the verified extension) took 48 ms at
height 1 and 75 to 95 ms at height 40, about 0.7 ms per record; it is on the source side
and was not profiled. The first search of a request for its ingress walks the accepted
records once (there is no index by ingress). `validate` (the whole-prefix replay) remains
for work that is not one record on the tip. `PortableHomeTransferReceiver.order` still
builds and hashes its whole history.

In `GenericSimplexReceiverSafety` the two consumer theorems name the chain each
certificate's honest signers sent (`leftBlock`, `rightBlock`) and take as a premise that
each token's history is that chain's application history (for the native digest:
`chainDigest_history` plus collision-freedom of the history digest between the two). Before,
the certificate carried the chain and the premise was implicit in its shape.
`exportable_has_durable_send` and `reachable_exportable_sent` are gone with `exportable`;
that a COMMIT in a replica's own output is a send of the model's trace is part of
`RelativeFaithful`.

**BREAKS: log magic version 11; signed COMMIT statement version 4; packet format.** Version 7: the step
changed (`validBlock`, `checked`, `offers`, the tick guard, the `ingest` horizon and repeat
answer) and the snapshot carries `ahead`. Version 8: `ingest` takes a COMMIT above the
horizon and READY is sent once. Version 9: `ingest` caps a member's share of a view
record. Version 10: the COMMIT witnesses a journal keeps are signed over the version-3
statement. Version 11: the journal is the running replica's (entries of `Replica.step`,
relative blocks, drains as entries, a `Replica` snapshot, witnesses as statements); the
signed statement is version 4 (64-byte digest); a packet is `(origin, recipient, WireMessage,
signature)` under a one-octet frame tag (0 protocol, 2 application candidate; the
certificate frame 1 is gone) and the candidate MAC frame is version 2 (it carries an
application height). Each changes what a journal replays to or exports. Older logs refuse
(`GenericSimplexIO.v10_log_refused`); an older signature does not verify. A mesh moves
by re-genesis.

## Native source consumer

GenericSimplexParticipant calls the real admission, historical replay and ordered
append receiver:

1. Ordinary ingress is admitted at the verified source tip to derive the complete
   canonical source record. It becomes an offer, with no source append.
2. Proposals and received evidence create pending historical-prefix validation
   work. Only the opaque native validation result creates checked.
3. A verified full certificate orders source records. The next source record is
   freshly derived from its original ingress and compared with the certified
   prefix before the existing physical append/readback operation.
4. Lost replies reload the actual source and reverify historical admission.
   Completion polling returns the source's verified receipt for the exact record.

The client artifact boundary is the existing canonical
`NativeHostCodec.SignedCall` in `call.bin`. `proposeCall` and the fixture's
`runCall` decode that exact frame; an invocation retains its existing signed
command and receives only the deployment's fixed domain/profile encoding.
Birth, install and capability calls retain their original inner ingress bytes.
The adapter first checks the existing native decoder for the outer call family.
A birth/install/capability wrapper cannot smuggle signed invocation bytes into
generic historical replay and bypass the live invocation budget. The adapter
performs no signing and does not grant admission. New invocations
retain the existing local synchronous step bound; historical replay and receipt
lookup use the original admission rather than applying today's local bound.
Internal refusal details are operator diagnostics. A shared Host submit hook
must preserve the existing public disclosure policy when mapping those results.

The four-store harness checks distinct configured source and agreement paths
and restores each journal to check its signer index. Its fixture must actually
create those independent stores under one exact consensus-profile genesis.
Changing a previous consensus-free world's configuration does not create that
genesis. After a completed append, the harness discards volatile participant
state, reloads all four stores, replays original admission and locates the exact
retained signed ingress receipt with only one new source record. This is a
software reopen within the driver, not an OS process-kill claim.

An inert empty protocol block changes BFT ancestry but not source history.
Validation may reuse equality of filtered source histories; certificate checks
and the BFT safe-parent rule still use the exact unfiltered block.

A descendant certificate can recover several missing source records one at a
time. The receiver checks that its current source prefix plus the exact next
record is a prefix of that full certificate. It never invents signatures on a
truncated block.

## Service and remaining joins

A service slice makes a bounded number of validation attempts, sends the replica's
whole undrained output and hands the application at most one committed payload.
Scheduling state may reset after restart because the journal retains the undrained
output and the payloads the application has not taken. This physical service API does not create source
funding, private custody qualification or permission to release a reservation.

The optional streaming CAS helper separates journal-file capacity from the
network frame bound. The Lean journal still loads into memory, and complete
logical ancestry still needs a bounded chunk/reassembly transport before it
exceeds a single protocol frame. No pruning or finite-lifetime guarantee follows
from the storage adapter.

Current source consumer compilation passed against the frozen receiver cohort.
The four-node signed source action is executed by the gate (above). Still required for
integrated qualification: the shared Host propose/await hook, the final native-consumer binding to the
reachable-engine proof, source funding and private recovery joins, and justified
checkpoint/reconfiguration liability retention. VerifiedCommit verifies real signatures at an IO boundary;
it is not itself a proof of cryptographic unforgeability or executable refinement.


## Ordinary operator bridge

`Verify.GenericSimplexOperatorBridge.submit` accepts the original native
SignedCall and actual opened replicas. If any native verified source already
contains that ingress, it drives the other participants to the exact retained
record using recovered certificates. It does not propose the mutation again.
It returns a confirmation only after all four have the same exact source prefix
through that call and exact receipt. Later agreed records may have reached only
some participants without blocking lookup of the earlier completed call. An exception during possible progress produces a uniform uncertain
outcome and refreshes actual sources; it is never reported as a rollback.

`testing/generic-simplex-operator.py` speaks the existing four-byte little-endian
length plus opcode/payload protocol and its exact 12,102,760-byte Host body
bound (distinct from the crypto helper frame limit). The owner supplies
`MINI_AGREEMENT_BRIDGE_CONFIG`, whose JSON has:

- `readerCommand`: explicit argv for the matching native Host on source store 0.
- `submitCommand`: explicit argv prefix for the real fixture's `submit-call`;
  the bridge appends original-call path, native-outcome path, and service fuel.
- `clientArguments`: exact client launch argv accepted by this wrapper.
- `attempts`: existing owner-private directory for retained exact signed calls.
- `fuel` and `timeoutSeconds`: finite positive operator service bounds.

Only opcode 2 takes the agreement route. Opcodes 0, 1, 3 through 11, 91 and 144 use the
matching Host's existing read, lookup, preparation and authoring handlers.
Opcode91 retains the signed current factory-observation birth gate; opcode144
performs the actual current signing-key status check. Every
other opcode fails closed; it cannot fall through to another mutation family.
The matched Host must use the actual same consensus-profile genesis and source
store. This wrapper does not authorize changing an existing world's profile.

The bridge retains the original call before invoking the native
consumer. It takes response bytes only from that consumer's bounded private
outcome file. A process timeout closes the client connection and retains the call;
there is no automatic second semantic dispatch. Exact lookup/retry uses the
existing source receipt and agreement evidence.

Current qualification: seven Python framing/file/process-boundary checks pass,
including an actual child timeout with no redispatch. The Lean operator bridge, exact-prefix completion refinement and native
call-family guard compile against the passing source consumer and frozen receiver
cohort. The matched standalone reader and operator have run against the actual four
source stores: profile/seed agreement, wrong-pin rejection, refusal of direct
reader submission and both enrolled current signing keys passed.

A development mesh of four replicas in one process on one host has since committed two
application records and then stalled on the third (scout R2-3, 2026-10-03; recorded
outside this repository; the kernel schedule is reproduced in `Verify.GenericSimplexHarness`). Its diagnosis: two replicas reached
their view timeout before collecting a quorum of VOTEs, because one drive iteration took
15-27 s against a timeout that needs Delta below timeout/7, and the engine ran only while
a client request was open. That is lawful behaviour of the engine, not a safety fault.
The liveness fixes are standing replicas, a cheaper iteration and the adaptive timeout
above. Liveness is still not established as a theorem; the safety theorems are over the
Lean engine model.
This local four-participant driver does not claim four independent processes or
failure domains. Operator service fuel is not a source-funded recovery grant.

The native call-family guard and general mismatch-refusal theorem passed their
scoped check before the first source action. The earlier compiled adapter lacked
this outer/inner family equality; no source mutation was run through it.
