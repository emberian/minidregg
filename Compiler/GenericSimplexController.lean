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
`committed` is the caller's committed source history.

What an attempt costs, by the shape of the work:

* While the application has not taken every record this replica has committed (the verified
  source tip `tip` is below `Replica.records`), nothing is validated: the work waits, at no
  cost, for `applyNext` to bring the tip level. It used to be replayed from the genesis.
* One record above the tip (every proposal on a committed parent) is admitted there once
  (`validateNext`): the same fresh native derivation the ordered receiver runs before its
  append. No history is rebuilt and the cost does not depend on the height. A record that
  can never be this source's on this tip (`NextResult.invalid`) is rejected for good; one the
  tip's admission does not grant now is retried later at the same constant cost (the old
  replay retried those too, from the genesis each time).
* Two or more records above the tip (a proposal that extends a prepared parent this replica
  has not committed with another record) are replayed as a complete prefix from the genesis
  in a scratch Store (`validate`), linear in the history. This is the one remaining use: the
  second record has to be admitted at a source state that exists in no Store.

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
  let later (detail : String) : IO (Minidregg.Compiler.GenericSimplexPending.Queue × Outcome) :=
    return (Minidregg.Compiler.GenericSimplexPending.retry rest work,.retry work.records detail)
  let height := tip.opened.durable.height
  if height < replica.records then
    return ← later "the application has not taken every committed record yet"
  match Minidregg.Kernel.GenericSimplexRelative.above work.height height work.records with
  | none => later "this work does not reach above the committed records"
  | some [record] =>
    match ← Minidregg.Kernel.JointSourcePrefixValidation.validateNext config tip runtime.context record with
    | .granted validated => recorded (checkedNext validated)
    | .invalid detail =>
      return (Minidregg.Compiler.GenericSimplexPending.reject rest work,.rejected work.records detail)
    | .refused detail => later detail
  | some run =>
    let block := (committed ()).take height ++ run
    match ← Minidregg.Kernel.JointSourcePrefixValidation.validate config origin runtime.context block with
    | .accepted validated => recorded (checkedInput validated height)
    | .rejected detail => return (Minidregg.Compiler.GenericSimplexPending.reject rest work,.rejected work.records detail)
    | .retry failure => later failure.detail

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
