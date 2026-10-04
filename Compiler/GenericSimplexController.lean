import Compiler.GenericSimplexNative
import Compiler.GenericSimplexPending
import Kernel.JointSourcePrefixValidation

namespace Minidregg.Compiler.GenericSimplexController
open Minidregg.Kernel.GenericSimplex
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Compiler.GenericSimplexNative
open Minidregg.Kernel.NativeHost
set_option autoImplicit false

/-- The sole validation grant used by this controller consumes the native
historical source replay capability, indexed by the exact committee and prefix.
No network-supplied Boolean or present-tip policy check is accepted here. -/
def checkedInput {config : Minidregg.Kernel.NativeHost.Config} {expected : Context} {block : Block}
    (_validated : Minidregg.Kernel.JointSourcePrefixValidation.Validated config expected block) : Input := .checked block

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
the validator replays each complete exact ancestor prefix afresh.

This function performs read-only checking and the local protocol journal CAS.
It does not allocate private custody, issue semantic repair requests, charge a
source meter, or assert that finite operator capacity guarantees liveness. -/
def attempt (runtime : Runtime) (config : Minidregg.Kernel.NativeHost.Config) (origin : Opened config)
    (queue : Minidregg.Compiler.GenericSimplexPending.Queue) : IO (Minidregg.Compiler.GenericSimplexPending.Queue × Outcome) := do
  let some prior ← runtime.current | return (queue,.invalidJournal)
  let state := prior.state
  let some (block,rest) := Minidregg.Compiler.GenericSimplexPending.take state queue
    | return (Minidregg.Compiler.GenericSimplexPending.discoverFrom state [] queue,.idle)
  match ← Minidregg.Kernel.JointSourcePrefixValidation.validate config origin runtime.context block with
  | .accepted validated =>
    match ← persist (storage runtime.native) runtime.context (checkedInput validated) with
    | .durable _ => return (rest,.accepted block)
    | .conflict => return (Minidregg.Compiler.GenericSimplexPending.retry rest block,.conflict)
    | .uncertain => return (Minidregg.Compiler.GenericSimplexPending.retry rest block,.uncertain)
    | .invalid => return (Minidregg.Compiler.GenericSimplexPending.retry rest block,.invalidJournal)
  | .rejected detail => return (Minidregg.Compiler.GenericSimplexPending.reject rest block,.rejected block detail)
  | .retry failure => return (Minidregg.Compiler.GenericSimplexPending.retry rest block,.retry block failure.detail)

/-- Packet ingress first authenticates and durably journals the original
protocol message; discovering validation work cannot turn it into a grant. -/
def receiveAndDiscover (runtime : Runtime) (queue : Minidregg.Compiler.GenericSimplexPending.Queue) (packet : Bytes) :
    IO (Minidregg.Compiler.GenericSimplexPending.Queue × GenericSimplexIO.Result) := do
  let result ← GenericSimplexNative.receive runtime packet
  match result with
  | .durable state => return (Minidregg.Compiler.GenericSimplexPending.discover state queue,result)
  | _ => return (queue,result)

/-- A scheduler supplies a finite service slice from its reserved control
capacity. Zero attempts provide no progress; fair repeated positive slices and
eventual replay/dependency availability are explicit liveness premises. -/
def service (runtime : Runtime) (config : Minidregg.Kernel.NativeHost.Config) (origin : Opened config) :
    Nat → Minidregg.Compiler.GenericSimplexPending.Queue → IO (Minidregg.Compiler.GenericSimplexPending.Queue × List Outcome)
  | 0,queue => pure (queue,[])
  | attempts+1,queue => do
    let (queue,outcome) ← attempt runtime config origin queue
    match outcome with
    | .idle | .invalidJournal | .uncertain => return (queue,[outcome])
    | _ =>
      let (queue,later) ← service runtime config origin attempts queue
      return (queue,outcome::later)

theorem checkedInput_exact {config : Minidregg.Kernel.NativeHost.Config} {expected : Context} {block : Block}
    (validated : Minidregg.Kernel.JointSourcePrefixValidation.Validated config expected block) :
    checkedInput validated = .checked block := rfl

end Minidregg.Compiler.GenericSimplexController
