/- Hosted custody lifecycle as an actual Revival effect declaration.
The physical adapter interprets ONLY the emitted descriptor; acknowledgments
are separate effects, so an unknown reply cannot restore a live channel. -/
module
public import Effects.Revival.Engine
@[expose] public section
namespace Minidregg.Effects.Revival.HostedLifecycle
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization

structure Rule where
  name : String
  (code initial pending settled : Nat)
  isolated : Bool
  deriving DecidableEq
structure Operation where
  (phase command : Nat)
  (id binding preimage : List UInt8)
  deriving DecidableEq
structure Receipt where
  (id bytes : List UInt8)
  deriving DecidableEq
structure State where
  status : Nat := 0
  ended : Bool := false
  binding : List UInt8 := []
  pending : Option Operation := none
  emitted : Option Operation := none
  receipt : Option Receipt := none
  spent : List (List UInt8) := []
  deriving DecidableEq
structure Context where
  (current retained budget acknowledged ended : Bool)
  response : List UInt8
inductive Refusal where
  | unknown | current | preimage | budget | isolation | state | uncertain | intent | replay
  deriving DecidableEq
inductive Primitive where
  | terminate
  | claim (expected pending : Nat) (operation : Operation)
  | emit (operation : Operation)
  | settle (expected settled : Nat) (operation : Operation) (receipt : List UInt8)
  deriving DecidableEq

def operationStream : StreamCodec Operation :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product bytesStream (StreamCodec.product bytesStream bytesStream))))
    (fun op => (op.phase,op.command,op.id,op.binding,op.preimage))
    (fun (phase,command,id,binding,preimage) => ⟨phase,command,id,binding,preimage⟩)
    (by intro op; cases op; rfl)

def step (primitive : Primitive) (state : State) : Option State :=
  match primitive with
  | .terminate => some {state with status := 2, ended := true, emitted := none}
  | .claim expected pending op =>
    if state.status = expected ∧ state.ended = false ∧ state.pending = none ∧ op.id ∉ state.spent then
      some { state with
        status := pending, binding := op.binding, pending := some op,
        emitted := none, spent := op.id :: state.spent }
    else none
  | .emit op =>
    if state.pending = some op then some {state with emitted := some op} else none
  | .settle expected settled op receipt =>
    if state.status = expected ∧ state.pending = some {op with phase := 0} then
      some {state with status := if state.ended then 2 else settled, pending := none, receipt := some ⟨op.id,receipt⟩}
    else none

def substrate : Substrate where
  State := State
  Prim := Primitive
  step := step
  Loc := Unit
  Obs := fun _ => State
  read := fun state _ => state
  writes := fun _ => {()}

def lower (rules : List Rule) (ctx : Context) (op : Operation) (state : State) :
    Except Refusal (List Primitive) := do
  let some rule := rules.find? (fun rule => rule.code == op.command) | throw .unknown
  if op.phase = 0 then
    if !ctx.current then throw .current
    if !ctx.retained then throw .preimage
    if !ctx.budget then throw .budget
    if state.status != rule.initial || state.ended || state.pending.isSome then throw .state
    if rule.isolated && state.binding != op.binding then throw .isolation
    if state.spent.contains op.id then throw .replay
    return [.claim rule.initial rule.pending op, .emit op]
  else if op.phase = 1 then
    if !ctx.acknowledged then throw .uncertain
    if state.status != rule.pending || state.pending != some {op with phase := 0} then throw .intent
    return [.settle rule.pending rule.settled op ctx.response]
  else if op.phase = 2 then
    if !ctx.ended then throw .state
    return [.terminate]
  else throw .unknown

def refusalName : Refusal → String
  | .unknown => "unknown" | .current => "currentAuthority" | .preimage => "exactPreimage"
  | .budget => "budget" | .isolation => "bindingIsolation" | .state => "channelState"
  | .uncertain => "uncertainCompletion" | .intent => "originalIntent" | .replay => "noReplay"

def spec (rules : List Rule) : EffectSpec Context substrate Operation Refusal where
  opStream := operationStream
  refusalName := refusalName
  accepts := fun kind => kind == .object
  version := 1
  sem := lower rules
  rotate := fun _ _ => []
  rotated := fun _ => false
  field := fun _ => .slot 0
  amount := fun _ _ => 0
  frame := fun _ => {.slot 0}
  verb := fun kind _ => match kind with
    | .object => .mutateObject | .account => .transfer | .program => .installProgram
  view := fun op before after => [("phase",Int.ofNat op.phase), ("before",Int.ofNat before.status), ("after",Int.ofNat after.status)]

def handler (rules : List Rule) : Handler Context State where
  S := substrate
  O := Operation
  R := Refusal
  spec := spec rules
  header := fun _ _ => .ok ()
  select := some
  pack := id

def registry (rules : List Rule) : Registry Context State := [(0,handler rules)]

def receive (rules : List Rule) (ctx : Context) (op : Operation) (state : State) :=
  dispatch (registry rules) 0 (operationStream.encode op) ctx state
end Minidregg.Effects.Revival.HostedLifecycle
