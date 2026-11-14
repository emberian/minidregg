# Native Generic Simplex agreement

Generic Simplex is Mini's domain-log agreement engine. Its core (`Kernel/GenericSimplex`,
`…Quorum`, `…Local`, `…Structure`, `Compiler/GenericSimplexIO`, `…Codec`, `…SourceAnchor`) is in
the `Host.Main` closure. The safety proofs build in the `SimplexQualification` library. The
controller, participant, serve and native modules build through the executables `generic-simplex-harness`,
`generic-simplex-log-reopen`, `generic-simplex-load` and `minidregg-four-source-fixture`
(`lakefile.toml`). The transferable COMMIT witness (`Compiler/GenericSimplexTransferability`)
and reconfiguration (`Kernel/GenericSimplexReconfig`) build only in the opt-in `ResearchWip`
library; `Verify/GenericSimplexNativeHarness.lean` is in no library.

The model is a fixed committee of n = 3f + 1 with at most f cumulatively Byzantine
members, authenticated reliable delivery and partial synchrony. The configured
timeout must cover the paper's timing bound and actual source validation. Fair
polling alone does not make missing historical source inputs available. Changing
membership, mobile faults and perpetual storage compaction are separate work.

## Durable decisions

GenericSimplex retains old views and ordered audit events. The native journal
replays exact inputs and releases newly enabled messages only after compare-and-
append plus exact readback. A peer cannot supply a source checked event.

A certificate contains distinct ML-DSA-65 signatures on durable COMMIT sends.
It does not require each signer to have locally output a commitment. A Byzantine
sender can supply the final COMMIT only to one honest replica. That replica must
transfer the original quorum evidence without obtaining a new quorum of local
output attestations.

The native COMMIT packet carries a transferable signature covered by its pairwise
MAC. The recipient verifies both, then retains the signature and the counted
delivery in one journal transaction. A recovered certificate imports those same
original COMMIT messages. The statement binds the exact committee context, view
and the chain as its length and running digest, with the COMMIT-SEND v3 domain separator.

The changed journal and wire schema are not an implicit migration path from the
old local-output profile. Reconfiguration must preserve existing liabilities; a
fresh file or epoch number is not proof that old certificates cannot complete.

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
- Stated, not proved: `RelativeFaithful`. Until it is proved, agreement of the running
  replicas rests on that statement. What remains is the local half, one `liveStep` at a
  time: each event the step emits on relative blocks, read through `denote`, meets its
  `LocalFaithful` obligation from the messages the replica holds. The specification's own
  proof of this (`step_emission` and the invariants under it) is about whole chains and a
  retained audit; it has to be transported across `forget` and `rebase`, or redone.
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

**The signed statement (version 3).** A COMMIT signature is over

    commitStatementBytes context view length digest =
      "MINI-SIMPLEX-COMMIT-SEND" ‖ 3 ‖ contextStream context ‖ nat view ‖ nat length ‖ bytesStream digest

(`Compiler/GenericSimplexCodec.lean`). Version 2 signed the whole chain, so two correct
signers at different heights could not write one chain the same way.

- `length`: the number of payloads of the chain the COMMIT is for, empty protocol payloads
  included (consensus ancestry, not the application height).
- `digest`: 32 bytes, the running digest of that chain (`chainDigest context`):
  the empty chain's is `cSHAKE256(contextStream context, S = "minidregg/simplex/chain")`,
  and a payload extends `d` to `cSHAKE256(d ‖ bytesStream payload, S)`. `bytesStream` is the
  length-prefixed encoding the journal uses, so the chain's split into payloads is bound;
  the origin binds the context, so one domain's digest is not another's.
- `commitmentBytes context view block` is that statement for a whole chain. The
  certificate and the COMMIT witness still carry the whole chain, and their verifiers
  recompute the digest from the origin: linear in the chain until the native layer adopts
  the running replica.
- In the running replica (`Kernel/GenericSimplexRelative.lean`): a `Replica` keeps the
  digest of its committed chain and `rebase` extends it over the payloads it commits. A
  wire COMMIT carries its statement `(length, digest)` beside the relative block; `encode`
  computes it from the writer's digest and the block, so a peer that passes a COMMIT on
  from another height writes the same statement, and `decode` reads a COMMIT only when the
  block it reads has the stated length and digest. Cost is the block, never the chain.
- Proved: `commit_reads_signed_chain` (for a digest with no collisions, the block a
  replica reads under a statement is the signed chain, wherever it was written from);
  `commitmentBytes_binds_config` (equal signed bytes have equal context, view, length and
  digest) and `commitmentBytes_binds_block` (equal chains, for a digest with no
  collisions). `ChainDigest.CollisionFree` is a named premise, inhabited by
  `Verify.GenericSimplexRelative.plain_collisionFree`; cSHAKE256 meets it only as an
  assumption about the chains that occur.
- `RelAuthentic` no longer has a clause for a relayed COMMIT: a COMMIT is authentic as its
  sender, view and statement, and its height and block are whatever the forwarder wrote.
- Executed: `forged_statement_refused` (three COMMITs with another chain's statement
  commit nothing). Gate plant `forged-digest`: on a digest that is the same for every
  chain the same three COMMITs are read, and the harness goes red.

**Not adopted by the native layer.** `Compiler/GenericSimplexIO.lean` still replays with
`step` on whole chains and checkpoints the whole state; `exportable` and
`certificateCandidates` read old views and the audit; the participant reads `outbox` by a
cursor into a list that only grows and never drains it; nothing forwards `relay`;
`receivedBefore` answers a repeated CANDIDATE(⊥) as a duplicate without giving it to the
kernel, so neither floor evidence nor `serveViews` can be triggered natively. The wire and
the journal therefore still carry whole chains. The kernel harness and the witnesses run
the new rules.

The adoption is one change across `GenericSimplexIO`, `GenericSimplexNative`,
`GenericSimplexParticipant`, `GenericSimplexServe`, `GenericSimplexController`,
`GenericSimplexTransferability` and the harnesses; the three gaps above cannot be closed
one at a time on `step` (letting a repeated CANDIDATE(⊥) through without a driver that
forwards and drains `relay` only grows `relay`). Its parts, in dependency order:
1. Codecs for `WireMessage`, `WireInput` and `Replica` (`stateStream` already encodes the
   core). An event is an encoded `WireInput`; the snapshot is a `Replica`.
2. `replayEvents` runs `Replica.step c (chainDigest context)`; `Journal.snapshot` is the
   replica, so a checkpoint is bounded by live state. `replayEvents_self` needs
   `Replica.step` to keep `core.self` (through `finish`, `rebase`, `release`).
3. The driver takes `Replica.drain` after every acknowledged input: `sends` to every peer,
   `owed` to the named peer, `committed` to the application. The output of an input is
   durable before it is sent, as today; the outbox cursors go away.
4. `receiveAuthenticated` keeps its duplicate test for everything but CANDIDATE(⊥).
5. A COMMIT witness is `(view, height, run, length, digest, attestation)`: the signature is
   checked against `commitStatementBytes` before the block is read, and the kernel's
   `decode` checks the block against the statement. `exportable` and the certificate answer
   from the kept evidence (`Replica.evidence`) and the durable witnesses: a certificate is
   `(context, view, length, digest, signers)` and its verifier needs the chain only above a
   height it already holds.
6. `logMagic` and the packet format move once, with this change.

**BREAKS: log magic version 10; signed COMMIT statement version 3.** Version 7: the step
changed (`validBlock`, `checked`, `offers`, the tick guard, the `ingest` horizon and repeat
answer) and the snapshot carries `ahead`. Version 8: `ingest` takes a COMMIT above the
horizon and READY is sent once. Version 9: `ingest` caps a member's share of a view
record. Version 10: the COMMIT witnesses a journal keeps are signed over the version-3
statement. Each changes what a journal replays to or exports. Older logs refuse
(`GenericSimplexIO.v9_log_refused`); a version-2 signature does not verify. A mesh moves
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

Fresh traffic, retries, validation and certificate work have separate finite
service opportunities. A retry round fixes its end so a growing outbox cannot
starve older messages. Scheduling cursors may reset after restart because the
journal retains obligations. This physical service API does not create source
funding, private custody qualification or permission to release a reservation.

The optional streaming CAS helper separates journal-file capacity from the
network frame bound. The Lean journal still loads into memory, and complete
logical ancestry still needs a bounded chunk/reassembly transport before it
exceeds a single protocol frame. No pruning or finite-lifetime guarantee follows
from the storage adapter.

Current source consumer compilation passed against the frozen receiver cohort.
Still required for integrated qualification: the actual four-node signed source
action, shared Host propose/await hook, the final native-consumer binding to the
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
