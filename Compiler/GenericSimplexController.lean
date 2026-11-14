module

public import Compiler.GenericSimplexNative
public import Compiler.GenericSimplexPending
public import Kernel.JointSourcePrefixValidation

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Init.System.ST
import all Init.System.IO

@[expose] public section

namespace Minidregg.Compiler.GenericSimplexController
open Minidregg.Kernel.GenericSimplex
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Compiler.GenericSimplexNative
open Minidregg.Kernel.NativeHost
set_option autoImplicit false

/-- The sole validation grant used by this controller consumes the native
historical source replay capability, indexed by the exact committee and prefix.
No network-supplied Boolean or present-tip policy check is accepted here. The replica is
told the validated history as its records from application height `height`; it reads the
part above what it has committed (`GenericSimplexRelative.above`). -/
def checkedInput {config : Minidregg.Kernel.NativeHost.Config} {expected : Context} {block : Block}
    (_validated : Minidregg.Kernel.JointSourcePrefixValidation.Validated config expected block)
    (height : Nat) : Entry :=
  .input (.checked height ((Minidregg.Kernel.JointSourcePrefixValidation.sourceRecords block).drop height))

/-- The grant for one record admitted at the verified tip: the replica is told that record
at the tip's height. -/
def checkedNext {config : Minidregg.Kernel.NativeHost.Config} {expected : Context}
    {target : Minidregg.Kernel.NativeHost.Durable}
    {tip : Minidregg.Kernel.NativeHostReplay.Verified config target} {record : Bytes}
    (_validated : Minidregg.Kernel.JointSourcePrefixValidation.ValidatedNext config expected tip record) :
    Entry :=
  .input (.checked tip.opened.durable.height [record])

inductive Outcome where
  | idle
  | accepted (block : Block)
  | rejected (block : Block) (detail : String)
  | retry (block : Block) (detail : String)
  | conflict
  | uncertain
  | invalidJournal
  deriving Repr

/-- One bounded validation attempt. Discovery is reconstructed from durable
authenticated arrivals, including proposals not yet locally valid. Every
transient refusal rotates to the end of the FIFO; unrelated new proposals do
not jump ahead of already pending work. The trusted origin fixes the genesis;
`committed` is the caller's committed source history, and the history checked is its first
`work.height` records followed by the work's own.

One record directly on the verified source tip `tip` (every proposal while the application
keeps up with the commits) is admitted there once (`validateNext`): no history is rebuilt
and the cost does not depend on the height. Any other work (records above committed ones
the source has not taken yet, or a record the tip does not grant) is replayed as a complete
prefix from the genesis (`validate`), which is linear in the history.

This function performs read-only checking and the local protocol journal CAS.
It does not allocate private custody, issue semantic repair requests, charge a
source meter, or assert that finite operator capacity guarantees liveness. -/
def attempt (runtime : Runtime) (config : Minidregg.Kernel.NativeHost.Config) (origin : Opened config)
    {target : Minidregg.Kernel.NativeHost.Durable}
    (tip : Minidregg.Kernel.NativeHostReplay.Verified config target)
    (committed : Unit → Block)
    (queue : Minidregg.Compiler.GenericSimplexPending.Queue) : IO (Minidregg.Compiler.GenericSimplexPending.Queue × Outcome) := do
  let some prior ← runtime.current | return (queue,.invalidJournal)
  let replica := prior.state
  let some (work,rest) := Minidregg.Compiler.GenericSimplexPending.take replica queue
    | return (Minidregg.Compiler.GenericSimplexPending.discoverFrom replica [] queue,.idle)
  let recorded (entry : Entry) : IO (Minidregg.Compiler.GenericSimplexPending.Queue × Outcome) := do
    match ← persist (storage runtime.native) runtime.context entry with
    | .durable _ => return (rest,.accepted work.records)
    | .conflict => return (Minidregg.Compiler.GenericSimplexPending.retry rest work,.conflict)
    | .uncertain => return (Minidregg.Compiler.GenericSimplexPending.retry rest work,.uncertain)
    | .invalid => return (Minidregg.Compiler.GenericSimplexPending.retry rest work,.invalidJournal)
  if let [record] := work.records then
    if work.height == tip.opened.durable.height then
      if let some validated ← Minidregg.Kernel.JointSourcePrefixValidation.validateNext
          config tip runtime.context record then
        return ← recorded (checkedNext validated)
  let history := committed ()
  if history.length < work.height then
    return (Minidregg.Compiler.GenericSimplexPending.retry rest work,
      .retry work.records "the committed source history does not reach this work's height yet")
  let block := history.take work.height ++ work.records
  match ← Minidregg.Kernel.JointSourcePrefixValidation.validate config origin runtime.context block with
  | .accepted validated => recorded (checkedInput validated work.height)
  | .rejected detail => return (Minidregg.Compiler.GenericSimplexPending.reject rest work,.rejected work.records detail)
  | .retry failure => return (Minidregg.Compiler.GenericSimplexPending.retry rest work,.retry work.records failure.detail)

/-- A scheduler supplies a finite service slice from its reserved control
capacity. Zero attempts provide no progress; fair repeated positive slices and
eventual replay/dependency availability are explicit liveness premises. -/
def service (runtime : Runtime) (config : Minidregg.Kernel.NativeHost.Config) (origin : Opened config)
    {target : Minidregg.Kernel.NativeHost.Durable}
    (tip : Minidregg.Kernel.NativeHostReplay.Verified config target)
    (committed : Unit → Block) :
    Nat → Minidregg.Compiler.GenericSimplexPending.Queue → IO (Minidregg.Compiler.GenericSimplexPending.Queue × List Outcome)
  | 0,queue => pure (queue,[])
  | attempts+1,queue => do
    let (queue,outcome) ← attempt runtime config origin tip committed queue
    match outcome with
    | .idle | .invalidJournal | .uncertain => return (queue,[outcome])
    | _ =>
      let (queue,later) ← service runtime config origin tip committed attempts queue
      return (queue,outcome::later)

end Minidregg.Compiler.GenericSimplexController
