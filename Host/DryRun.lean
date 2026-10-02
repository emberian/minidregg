/-
# Dry run (op 130): the submission program, handed a Store writer that never writes

`can NAME` (P-AFFORDANCES) asks, per verb a subject holds, whether the kernel
would admit the smallest command for it *now*, without committing it. The
signing-plan op (op 1) answers only half of that: it authorizes the requester's
reads and evaluates the target's law (P-LAW's `invokeLawLeaf`), but it never
consults the capability that would authorize the write, the signer's standing,
or the nullifier. Those are decided at submission.

So the dry run is the submission itself: `NativeHost.submitLoadedVia`, the very
function the served path runs (`submitLoadedWith` is `submitLoadedVia
config.transport`), handed `dryTransport`, whose `append` records that it was
reached and answers `conflict`, and which never checkpoints or seeds.

* **Disclosure.** A blind submission names no reason (`publicSubmissionOutcome`).
  The dry run discloses the submission's reason, so it is gated exactly like the
  signing plan: the input is the requester's signed observation (the same frame
  op 1 takes) and the detached signatures over the plan op 1 derives from it.
  The Host re-derives the plan, assembles the call itself, and dry-submits that
  call — so the call judged is the one the observation authorized, never one the
  client supplies.
* **Verdict.** `admitted plan` iff the submission reached the Store writer;
  otherwise the outcome the submission produced (a refusal names its reason, a
  law refusal at plan time names its clause).
-/
import Kernel.NativeHost
import Theory.AssertAxioms

namespace Minidregg.Host.DryRun

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel
open Minidregg.Kernel.DurableCheckpoint

/-- The Store writer of a dry run: reads pass through; the one append records
that admission reached it and reports `conflict`; no checkpoint, no seed. -/
def dryTransport (t : DurableReceiverIO.Transport) (reached : IO.Ref Bool) :
    DurableReceiverIO.Transport where
  read := t.read
  append := fun _ _ => do reached.set true; pure .conflict
  putCheckpoint := fun _ _ => pure (.error "dry run writes no checkpoint")
  initializeSeed := fun _ => pure .conflict
  key := t.key
  checkpointEvery := t.checkpointEvery
  logStart := t.logStart
  systemCell := t.systemCell

/-- The dry run's writer does not depend on the Store's writers at all: any two
transports that read alike give the same dry transport. -/
theorem dryTransport_writers_irrelevant (t : DurableReceiverIO.Transport)
    (append : Nat → DurableReceiverIO.Entry → IO DurableReceiverIO.CasObservation)
    (putCheckpoint : Nat → List UInt8 → IO (Except String Unit))
    (initializeSeed : List UInt8 → IO DurableReceiverIO.CasObservation) :
    dryTransport { t with append, putCheckpoint, initializeSeed } = dryTransport t := rfl

@[simp] theorem dryTransport_key (t : DurableReceiverIO.Transport) (reached : IO.Ref Bool) :
    (dryTransport t reached).key = t.key := rfl

@[simp] theorem dryTransport_append (t : DurableReceiverIO.Transport) (reached : IO.Ref Bool)
    (height : Nat) (entry : DurableReceiverIO.Entry) :
    (dryTransport t reached).append height entry = (do reached.set true; pure .conflict) := rfl

inductive Verdict where
  /-- The submission reached the Store writer: every admission check passed. -/
  | admitted (plan : SigningPlan)
  /-- The submission (or the plan it derives from) stopped here. -/
  | stopped (outcome : Outcome)

/-- The replay branch's confirmation, read from the already-opened image. -/
def dryConfirm (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (kind : DurableReceiverIO.Confirmation)
    (transactionId eventId : Minidregg.Theory.TypedAuthorization.Digest) : IO Outcome :=
  pure <| match NativeHost.historicalReceipt config opened.durable transactionId eventId with
    | some receipt => .confirmed kind receipt
    | none => .uncertain "original receipt prefix unavailable".toUTF8.toList

/-- Op 130 over the Store reader `t`: plan exactly as op 1, assemble exactly as
op 11, submit exactly as op 2 — with the writer swapped. -/
def dryRunVia (t : DurableReceiverIO.Transport) (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (observation : List UInt8)
    (signatures : List (List UInt8)) : IO Verdict := do
  match ← NativeHost.prepareAuthorizedLoaded config opened observation with
  | .error refusal => return .stopped (NativeHost.refusalOutcome "prepare" refusal)
  | .ok plan =>
      match NativeHost.assemble plan signatures with
      | .error detail =>
          return .stopped (.refused .malformed "assemble".toUTF8.toList detail.toUTF8.toList)
      | .ok call =>
          let reached ← IO.mkRef false
          let outcome ← NativeHost.submitLoadedVia (dryTransport t reached) config opened call
            (dryConfirm config opened)
          if ← reached.get then return .admitted plan else return .stopped outcome

def dryRunLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (observation : List UInt8) (signatures : List (List UInt8)) : IO Verdict :=
  dryRunVia config.transport config opened observation signatures

/-- **Commits nothing.** Every Store mutation goes through the transport's
`append`, `putCheckpoint` or `initializeSeed`. The dry run is the same program
whatever those three are, so it cannot invoke the Store's: the Store's root and
log after a dry run are the ones before it. -/
theorem dryRun_commits_nothing (t : DurableReceiverIO.Transport)
    (append : Nat → DurableReceiverIO.Entry → IO DurableReceiverIO.CasObservation)
    (putCheckpoint : Nat → List UInt8 → IO (Except String Unit))
    (initializeSeed : List UInt8 → IO DurableReceiverIO.CasObservation)
    (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (observation : List UInt8) (signatures : List (List UInt8)) :
    dryRunVia { t with append, putCheckpoint, initializeSeed } config opened observation
      signatures = dryRunVia t config opened observation signatures := rfl

/-- **The submission half never names the Store's writers through its config.**
`submitLoadedVia` — the half of the dry run that could write — gives the same
program under any `storage` (the Store's paths, and with them every writer
`Config.transport` would build): it reaches the Store only through the
transport it is handed. With `dryRun_commits_nothing`, no Store writer is
reachable from the dry run's submission. (The plan half, op 1's
`prepareAuthorizedLoaded`, takes no transport and is the existing read-only
path; the same statement for it does not close by `rfl` — see the report.) -/
theorem submit_storage_irrelevant (t : DurableReceiverIO.Transport)
    (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (storage : DurableReceiverIO.NativeConfig) (call : SignedCall)
    (confirm : DurableReceiverIO.Confirmation → Minidregg.Theory.TypedAuthorization.Digest →
      Minidregg.Theory.TypedAuthorization.Digest → IO Outcome) :
    NativeHost.submitLoadedVia t { config with storage } (opened.restorage storage) call confirm =
      NativeHost.submitLoadedVia t config opened call confirm := rfl

/-- **The served submission and the dry run are one program.** Op 2 runs
`submitLoadedWith`, which is `submitLoadedVia` over the Store's transport; the dry
run runs `submitLoadedVia` over `dryTransport` of the same reader. -/
theorem submit_is_via_store_transport (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (call : SignedCall)
    (confirm : DurableReceiverIO.Confirmation → Minidregg.Theory.TypedAuthorization.Digest →
      Minidregg.Theory.TypedAuthorization.Digest → IO Outcome) :
    NativeHost.submitLoadedWith config opened call confirm =
      NativeHost.submitLoadedVia config.transport config opened call confirm := rfl

/-- **At the Store writer, the dry run agrees with submission on every refusal.**
Every receiver ends in `DurableReceiverIO.receiveLoaded`. Wherever the durable
admission (`DurableCheckpoint.prepare`) refuses or replays, the receiver's answer
does not touch the transport, so the dry transport and the Store's give the same
answer — and the dry run's `reached` flag is never set. -/
theorem dryReceive_refusal_agrees (t : DurableReceiverIO.Transport) (reached : IO.Ref Bool)
    (rootBytes : List UInt8 → Minidregg.Theory.TypedAuthorization.Digest)
    (loaded : DurableReceiverIO.Loaded rootBytes) (intent : DurableDataIntent.DataIntent rootBytes)
    (refused : ∀ ready, prepare loaded.image loaded.baseHeight loaded.base loaded.snapshot
      loaded.withinLog loaded.resumed intent ≠ .inl ready) :
    DurableReceiverIO.receiveLoadedDetailedWithFresh (dryTransport t reached) rootBytes loaded intent =
      DurableReceiverIO.receiveLoadedDetailedWithFresh t rootBytes loaded intent := by
  unfold DurableReceiverIO.receiveLoadedDetailedWithFresh
  split <;> first | rfl | (rename_i h; exact absurd h (refused _))

/-- The dry transport names the Store's system cell, so the tail law
(`Loaded.judge`, C14) judges a dry run exactly as it judges the submission. -/
@[simp] theorem dryTransport_judge (t : DurableReceiverIO.Transport) (reached : IO.Ref Bool)
    {rootBytes : List UInt8 → Minidregg.Theory.TypedAuthorization.Digest}
    (loaded : DurableReceiverIO.Loaded rootBytes) (intent : DurableDataIntent.DataIntent rootBytes) :
    loaded.judge (dryTransport t reached) intent = loaded.judge t intent := rfl

/-- **At the Store writer, the dry run agrees with submission on a tail-bound
refusal.** Where the durable admission accepts but the tail law refuses, neither
path reaches the transport's writers, and both answer the same refusal. -/
theorem dryReceive_tail_refusal_agrees (t : DurableReceiverIO.Transport) (reached : IO.Ref Bool)
    (rootBytes : List UInt8 → Minidregg.Theory.TypedAuthorization.Digest)
    (loaded : DurableReceiverIO.Loaded rootBytes) (intent : DurableDataIntent.DataIntent rootBytes)
    (ready) (admitted : prepare loaded.image loaded.baseHeight loaded.base loaded.snapshot
      loaded.withinLog loaded.resumed intent = .inl ready)
    (reason) (bounded : loaded.judge t intent = .error reason) :
    DurableReceiverIO.receiveLoadedDetailedWithFresh (dryTransport t reached) rootBytes loaded intent =
      DurableReceiverIO.receiveLoadedDetailedWithFresh t rootBytes loaded intent := by
  unfold DurableReceiverIO.receiveLoadedDetailedWithFresh
  simp only [admitted, dryTransport_judge, bounded]

/-- **At the Store writer, admission is exactly reaching the writer.** Where the
durable admission accepts and the tail law admits, the real path appends; the
dry run instead marks `reached` (after the same MAC-key read) and reports
contention. -/
theorem dryReceive_admission_reaches_append (t : DurableReceiverIO.Transport)
    (reached : IO.Ref Bool) (rootBytes : List UInt8 → Minidregg.Theory.TypedAuthorization.Digest)
    (loaded : DurableReceiverIO.Loaded rootBytes) (intent : DurableDataIntent.DataIntent rootBytes)
    (ready) (admitted : prepare loaded.image loaded.baseHeight loaded.base loaded.snapshot
      loaded.withinLog loaded.resumed intent = .inl ready)
    (judged : loaded.judge t intent = .ok ()) :
    DurableReceiverIO.receiveLoadedDetailedWithFresh (dryTransport t reached) rootBytes loaded intent =
      (do
        let .ok _ ← t.key
          | return (false, .ordinary (.unavailable "checkpoint MAC key unavailable"))
        reached.set true
        return (false, .ordinary .contention)) := by
  unfold DurableReceiverIO.receiveLoadedDetailedWithFresh
  simp only [admitted, dryTransport_judge, judged, dryTransport_key, dryTransport_append]
  rfl

#assert_axioms dryTransport_writers_irrelevant
#assert_axioms dryTransport_judge
#assert_axioms dryReceive_tail_refusal_agrees
#assert_axioms dryRun_commits_nothing
#assert_axioms submit_storage_irrelevant
#assert_axioms submit_is_via_store_transport
#assert_axioms dryReceive_refusal_agrees
#assert_axioms dryReceive_admission_reaches_append

end Minidregg.Host.DryRun
