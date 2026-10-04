/- Objective Bend demand machine → C: the code ROM, the canonical State codec,
and the C table emitter.

The C backend (native/objective-emit/runtime.c) is a defunctionalized copy of
`ObjectiveBendDemandMachine.stepRaw`: the State is C structs, the heap an
arena, `stepRaw` a switch over Term constructors and frames. What it executes
is a per-program ROM computed HERE, in Lean:

* every term the machine can ever hold in control, a cell or a frame is a ROM
  node: the closure of the program under subterms and under the two places
  where `stepRaw` itself manufactures code (`fix` allocates
  `app (app spec↑ (bound 0)) inherited↑`; `mix` continues with `mixBody`);
* those derived bodies are read off `stepRaw` by running it on a probe state
  (`fixBody`, `mixTarget`), so the C never re-implements `Term.rename` or
  `mixBody` — it follows a precomputed pointer;
* the ROM is audited (`Rom.audit`): every node decodes back to exactly its
  key term, and every derived pointer names exactly the probed body.

The one runtime term outside the ROM is the cached predecessor literal that
an `ifZero` successor step allocates (`.nat n` for a runtime `n`); the codec
encodes a term by ROM index when it is in the ROM and as a literal otherwise.

Refinement status: NONE PROVED. The obligation is "the emitted C's trace is
`stepRaw`'s trace"; the evidence today is a differential harness
(native/objective-emit/differential.sh) comparing canonical State bytes,
outcome, tick count and a per-tick fingerprint against `runBounded`. -/
import Std.Data.HashMap
import Theory.ObjectiveBendDemandMachine

namespace Minidregg.Compiler.ObjectiveBendEmitC
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
set_option autoImplicit false

deriving instance Hashable for Primitive
deriving instance BEq, Hashable for Term

/-! ## Code that `stepRaw` manufactures, read off `stepRaw` itself -/

/-- The body a `fix` allocates, obtained by running the machine's own
transition on a probe state. -/
def fixBody (spec inherited : Term) : Option Term :=
  match (stepRaw (initial (.fix spec inherited))).heap[0]? with
  | some (Cell.suspended origin) => some origin.term
  | _ => none

/-- The term a `mix` continues with, obtained the same way. -/
def mixTarget (lower upper : Term) : Option Term :=
  match (stepRaw (initial (.mix lower upper))).control with
  | .evaluate term _ => some term
  | _ => none

/-- The probe recovers exactly the `fix` rewrite (no premise). -/
theorem fixBody_exact (spec inherited : Term) :
    fixBody spec inherited =
      some (.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ)) := by
  first | rfl | simp [fixBody, stepRaw, initial]

/-- The probe recovers exactly `mixBody` (no premise). -/
theorem mixTarget_exact (lower upper : Term) :
    mixTarget lower upper = some (mixBody lower upper) := by
  first | rfl | simp [mixTarget, stepRaw, initial]

/-- A `case` frame allocates the payload alias `bound 0` over `[payload]`;
this is why the ROM always interns `bound 0`. -/
theorem case_allocates_bound_zero (tag : String) (body : Term) (payload : Address)
    (environment : Environment) :
    (stepRaw ⟨#[], .returned (.variant tag payload), [.case [(tag, body)] environment]⟩).heap[0]? =
      some (.suspended ⟨.bound 0, [payload]⟩) := by
  simp [stepRaw]

/-! ## The ROM -/

/-- One ROM node: a Term constructor whose children are ROM indices and whose
labels are label-table indices. `fix`/`mix` carry the index of the code that
`stepRaw` continues with. -/
inductive Node where
  | bound (index : Nat)
  | lam (body : Nat)
  | app (function argument : Nat)
  | mix (lower upper derived : Nat)
  | fix (specification inherited derived : Nat)
  | specification (metadata extension : Nat)
  | prototype (specification target : Nat)
  | reflect (target : Nat)
  | metadata (target : Nat)
  | project (target : Nat)
  | nat (value : Nat)
  | boolean (value : Bool)
  | label (name : Nat)
  | binary (primitive : Primitive) (left right : Nat)
  | extend (inherited : Nat) (fields : List (Nat × Nat))
  | record (fields : List (Nat × Nat))
  | get (target name : Nat)
  | ifZero (value whenZero successor : Nat)
  | inject (name payload : Nat)
  | case (scrutinee : Nat) (arms : List (Nat × Nat))
  | ifBool (condition whenTrue whenFalse : Nat)
  deriving Repr, Inhabited

structure Rom where
  terms : Array Term := #[]
  nodes : Array Node := #[]
  index : Std.HashMap Term Nat := {}
  labels : Array String := #[]
  labelIndex : Std.HashMap String Nat := {}

abbrev Build := StateT Rom (Except String)

def internLabel (name : String) : Build Nat := do
  let rom ← get
  match rom.labelIndex.get? name with
  | some index => pure index
  | none =>
    set {rom with labels := rom.labels.push name,
                  labelIndex := rom.labelIndex.insert name rom.labels.size}
    pure rom.labels.size

def place (capacity : Nat) (term : Term) (node : Node) : Build Nat := do
  let rom ← get
  match rom.index.get? term with
  | some index => pure index
  | none =>
    if rom.nodes.size ≥ capacity then throw "ROM node capacity"
    set {rom with terms := rom.terms.push term, nodes := rom.nodes.push node,
                  index := rom.index.insert term rom.nodes.size}
    pure rom.nodes.size

mutual
  /-- Post-order interning: children receive smaller indices than parents. The
  derived `fix`/`mix` pointers are patched afterwards by `deriveAll`. -/
  def intern (capacity : Nat) : Nat → Term → Build Nat
    | 0, _ => throw "ROM term depth capacity"
    | fuel+1, term => do
      if let some index := (← get).index.get? term then return index
      let node : Node ← match term with
        | .bound index => pure (Node.bound index)
        | .lam body => pure (.lam (← intern capacity fuel body))
        | .app function argument =>
          pure (.app (← intern capacity fuel function) (← intern capacity fuel argument))
        | .mix lower upper =>
          pure (.mix (← intern capacity fuel lower) (← intern capacity fuel upper) 0)
        | .fix spec inherited =>
          pure (.fix (← intern capacity fuel spec) (← intern capacity fuel inherited) 0)
        | .specification metadata extension =>
          pure (.specification (← intern capacity fuel metadata) (← intern capacity fuel extension))
        | .prototype spec target =>
          pure (.prototype (← intern capacity fuel spec) (← intern capacity fuel target))
        | .reflect target => pure (.reflect (← intern capacity fuel target))
        | .metadata target => pure (.metadata (← intern capacity fuel target))
        | .project target => pure (.project (← intern capacity fuel target))
        | .nat value => pure (.nat value)
        | .boolean value => pure (.boolean value)
        | .label name => pure (.label (← internLabel name))
        | .binary primitive left right =>
          pure (.binary primitive (← intern capacity fuel left) (← intern capacity fuel right))
        | .extend inherited fields =>
          pure (.extend (← intern capacity fuel inherited) (← internFields capacity fuel fields))
        | .record fields => pure (.record (← internFields capacity fuel fields))
        | .get target name => pure (.get (← intern capacity fuel target) (← internLabel name))
        | .ifZero value zero successor =>
          pure (.ifZero (← intern capacity fuel value) (← intern capacity fuel zero)
            (← intern capacity fuel successor))
        | .inject name payload => pure (.inject (← internLabel name) (← intern capacity fuel payload))
        | .case scrutinee arms =>
          pure (.case (← intern capacity fuel scrutinee) (← internFields capacity fuel arms))
        | .ifBool condition whenTrue whenFalse =>
          pure (.ifBool (← intern capacity fuel condition) (← intern capacity fuel whenTrue)
            (← intern capacity fuel whenFalse))
      place capacity term node

  def internFields (capacity : Nat) : Nat → List (String × Term) → Build (List (Nat × Nat))
    | _, [] => pure []
    | 0, _ :: _ => throw "ROM field-list capacity"
    | fuel+1, (name, term) :: rest => do
      let label ← internLabel name
      let code ← intern capacity fuel term
      let tail ← internFields capacity fuel rest
      pure ((label, code) :: tail)
end

/-- Close the ROM under the code `stepRaw` manufactures. Every node index is
visited once, including nodes appended while visiting; `budget` bounds the walk. -/
def deriveAll (capacity fuel : Nat) : Nat → Nat → Build Unit
  | 0, _ => throw "ROM derivation budget"
  | budget+1, position => do
    let rom ← get
    if position < rom.nodes.size then
      match rom.nodes[position]?, rom.terms[position]? with
      | some (.fix spec inherited _), some (.fix specTerm inheritedTerm) =>
        let some body := fixBody specTerm inheritedTerm | throw "fix probe refused"
        let derived ← intern capacity fuel body
        modify fun r => {r with nodes := r.nodes.set! position (.fix spec inherited derived)}
      | some (.mix lower upper _), some (.mix lowerTerm upperTerm) =>
        let some body := mixTarget lowerTerm upperTerm | throw "mix probe refused"
        let derived ← intern capacity fuel body
        modify fun r => {r with nodes := r.nodes.set! position (.mix lower upper derived)}
      | _, _ => pure ()
      deriveAll capacity fuel budget (position + 1)
    else pure ()

structure Compiled where
  rom : Rom
  entry : Nat
  boundZero : Nat

/-- Build the ROM of one closed program. Index 0 is always `bound 0`. -/
def buildAll (capacity fuel : Nat) (entry : Term) : Build (Nat × Nat) := do
  let boundZero ← intern capacity fuel (.bound 0)
  let entryIndex ← intern capacity fuel entry
  deriveAll capacity fuel (capacity + 1) 0
  pure (boundZero, entryIndex)

def compile (capacity fuel : Nat) (entry : Term) : Except String Compiled := do
  let ((boundZero, entryIndex), rom) ← (buildAll capacity fuel entry).run {}
  pure ⟨rom, entryIndex, boundZero⟩

/-! ## Audit: the ROM decodes to its keys, the derived pointers to the probes -/

mutual
  def Rom.decode (rom : Rom) : Nat → Nat → Option Term
    | 0, _ => none
    | fuel+1, position => do
      let label := fun (index : Nat) => rom.labels[index]?
      match ← rom.nodes[position]? with
      | .bound index => pure (.bound index)
      | .lam body => pure (.lam (← rom.decode fuel body))
      | .app f a => pure (.app (← rom.decode fuel f) (← rom.decode fuel a))
      | .mix l u _ => pure (.mix (← rom.decode fuel l) (← rom.decode fuel u))
      | .fix s i _ => pure (.fix (← rom.decode fuel s) (← rom.decode fuel i))
      | .specification m e => pure (.specification (← rom.decode fuel m) (← rom.decode fuel e))
      | .prototype s t => pure (.prototype (← rom.decode fuel s) (← rom.decode fuel t))
      | .reflect t => pure (.reflect (← rom.decode fuel t))
      | .metadata t => pure (.metadata (← rom.decode fuel t))
      | .project t => pure (.project (← rom.decode fuel t))
      | .nat value => pure (.nat value)
      | .boolean value => pure (.boolean value)
      | .label name => pure (.label (← label name))
      | .binary p l r => pure (.binary p (← rom.decode fuel l) (← rom.decode fuel r))
      | .extend i fs => pure (.extend (← rom.decode fuel i) (← rom.decodeFields fuel fs))
      | .record fs => pure (.record (← rom.decodeFields fuel fs))
      | .get t name => pure (.get (← rom.decode fuel t) (← label name))
      | .ifZero v z s => pure (.ifZero (← rom.decode fuel v) (← rom.decode fuel z) (← rom.decode fuel s))
      | .inject name p => pure (.inject (← label name) (← rom.decode fuel p))
      | .case s arms => pure (.case (← rom.decode fuel s) (← rom.decodeFields fuel arms))
      | .ifBool c t f => pure (.ifBool (← rom.decode fuel c) (← rom.decode fuel t) (← rom.decode fuel f))

  def Rom.decodeFields (rom : Rom) : Nat → List (Nat × Nat) → Option (List (String × Term))
    | _, [] => some []
    | 0, _ :: _ => none
    | fuel+1, (name, position) :: rest => do
      pure ((← rom.labels[name]?, ← rom.decode fuel position) :: (← rom.decodeFields fuel rest))
end

def Rom.audit (rom : Rom) (fuel : Nat) : Except String Unit := do
  if rom.labelIndex.size != rom.labels.size then throw "label table not injective"
  for position in [0:rom.nodes.size] do
    let some key := rom.terms[position]? | throw "ROM key missing"
    if rom.decode fuel position != some key then
      throw s!"ROM node {position} does not decode to its key term"
    if rom.index.get? key != some position then throw s!"ROM index disagrees at {position}"
    match rom.nodes[position]?, key with
    | some (.fix _ _ derived), .fix s i =>
      if rom.terms[derived]? != fixBody s i then throw s!"fix pointer {position} is not the probed body"
    | some (.mix _ _ derived), .mix l u =>
      if rom.terms[derived]? != mixTarget l u then throw s!"mix pointer {position} is not the probed body"
    | _, _ => pure ()

/-! ## Canonical State codec `objective-state.v1`

Little-endian. u8/u32/u64 fixed width; a natural is u32 byte-length + minimal
little-endian bytes; a string is u32 length + UTF-8; an environment and every
list is u64 length + items, in list order (the stack top first). A term is
`1, u32 ROM index` when it is a ROM node, else `0, natural` for a `.nat`
literal; any other non-ROM term is a codec refusal (it would mean the ROM is
not closed under the machine). -/

def putU8 (out : ByteArray) (value : Nat) : ByteArray := out.push value.toUInt8
def putU32 (out : ByteArray) (value : Nat) : ByteArray :=
  (List.range 4).foldl (fun acc k => acc.push ((value >>> (8 * k)) % 256).toUInt8) out
def putU64 (out : ByteArray) (value : Nat) : ByteArray :=
  (List.range 8).foldl (fun acc k => acc.push ((value >>> (8 * k)) % 256).toUInt8) out

def naturalBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel+1, n => if n = 0 then [] else (n % 256).toUInt8 :: naturalBytes fuel (n / 256)

def putNatural (out : ByteArray) (n : Nat) : ByteArray :=
  let bytes := naturalBytes (n.log2 + 2) n
  bytes.foldl ByteArray.push (putU32 out bytes.length)

def putString (out : ByteArray) (s : String) : ByteArray :=
  let bytes := s.toUTF8
  (putU32 out bytes.size).append bytes

def putEnvironment (out : ByteArray) (env : Environment) : ByteArray :=
  env.foldl putU64 (putU64 out env.length)

def putTerm (rom : Rom) (out : ByteArray) (t : Term) : Except String ByteArray :=
  match rom.index.get? t with
  | some position => pure (putU32 (putU8 out 1) position)
  | none => match t with
    | .nat n => pure (putNatural (putU8 out 0) n)
    | _ => throw "state holds a term outside the ROM"

def primitiveCode : Primitive → Nat
  | .add => 0 | .multiply => 1 | .equal => 2 | .conjunction => 3 | .labelEqual => 4

def refusalCode : Refusal → Nat
  | .unbound => 0 | .missingCell => 1 | .missingField => 2 | .wrongValue => 3
  | .invalidUpdate => 4 | .capacity => 5 | .missingArm => 6

def refusalName : Refusal → String
  | .unbound => "unbound" | .missingCell => "missingCell" | .missingField => "missingField"
  | .wrongValue => "wrongValue" | .invalidUpdate => "invalidUpdate"
  | .capacity => "capacity" | .missingArm => "missingArm"

def putAddressFields (out : ByteArray) (fields : List (String × Address)) : ByteArray :=
  fields.foldl (fun acc field => putU64 (putString acc field.1) field.2) (putU64 out fields.length)

def putTermFields (rom : Rom) (out : ByteArray) (fields : List (String × Term)) :
    Except String ByteArray :=
  fields.foldlM (fun acc field => putTerm rom (putString acc field.1) field.2) (putU64 out fields.length)

def putValue (rom : Rom) (out : ByteArray) : RuntimeValue → Except String ByteArray
  | .closure body env => do pure (putEnvironment (← putTerm rom (putU8 out 0) body) env)
  | .natural n => pure (putNatural (putU8 out 1) n)
  | .boolean b => pure (putU8 (putU8 out 2) (if b then 1 else 0))
  | .label s => pure (putString (putU8 out 3) s)
  | .record fields => pure (putAddressFields (putU8 out 4) fields)
  | .specification m e => pure (putU64 (putU64 (putU8 out 5) m) e)
  | .prototype s t => pure (putU64 (putU64 (putU8 out 6) s) t)
  | .variant s p => pure (putU64 (putString (putU8 out 7) s) p)

def putClosure (rom : Rom) (out : ByteArray) (c : Closure) : Except String ByteArray := do
  pure (putEnvironment (← putTerm rom out c.term) c.environment)

def putCell (rom : Rom) (out : ByteArray) : Cell → Except String ByteArray
  | .suspended origin => putClosure rom (putU8 out 0) origin
  | .evaluating origin => putClosure rom (putU8 out 1) origin
  | .cached origin v => do putValue rom (← putClosure rom (putU8 out 2) origin) v

def putFrame (rom : Rom) (out : ByteArray) : Frame → Except String ByteArray
  | .argument t env => do pure (putEnvironment (← putTerm rom (putU8 out 0) t) env)
  | .update address => pure (putU64 (putU8 out 1) address)
  | .field name => pure (putString (putU8 out 2) name)
  | .reflect => pure (putU8 out 3)
  | .metadata => pure (putU8 out 4)
  | .project => pure (putU8 out 5)
  | .extend fields env => do pure (putEnvironment (← putTermFields rom (putU8 out 6) fields) env)
  | .condition z s env => do
    pure (putEnvironment (← putTerm rom (← putTerm rom (putU8 out 7) z) s) env)
  | .binaryLeft p r env => do
    pure (putEnvironment (← putTerm rom (putU8 (putU8 out 8) (primitiveCode p)) r) env)
  | .binaryRight p l => putValue rom (putU8 (putU8 out 9) (primitiveCode p)) l
  | .case arms env => do pure (putEnvironment (← putTermFields rom (putU8 out 10) arms) env)
  | .ifBool t f env => do pure (putEnvironment (← putTerm rom (← putTerm rom (putU8 out 11) t) f) env)

def putControl (rom : Rom) (out : ByteArray) : Control → Except String ByteArray
  | .evaluate t env => do pure (putEnvironment (← putTerm rom (putU8 out 0) t) env)
  | .enter address => pure (putU64 (putU8 out 1) address)
  | .blackhole address => pure (putU64 (putU8 out 2) address)
  | .returned v => putValue rom (putU8 out 3) v
  | .complete v => putValue rom (putU8 out 4) v
  | .refused r => pure (putU8 (putU8 out 5) (refusalCode r))

def stateMagic : ByteArray := "OBS1".toUTF8

def encodeState (rom : Rom) (state : State) : Except String ByteArray := do
  let mut out := putU64 stateMagic state.heap.size
  for c in state.heap do out ← putCell rom out c
  out ← putControl rom out state.control
  out := putU64 out state.stack.length
  for f in state.stack do out ← putFrame rom out f
  pure out

/-! ## Per-tick fingerprint (FNV-1a 64 over control tag, heap size, stack length) -/

def controlTag : Control → Nat
  | .evaluate .. => 0 | .enter _ => 1 | .blackhole _ => 2
  | .returned _ => 3 | .complete _ => 4 | .refused _ => 5

def fnvPrime : UInt64 := 0x100000001b3
def fnvOffset : UInt64 := 0xcbf29ce484222325

def fingerprint (hash : UInt64) (state : State) : UInt64 :=
  let bytes := putU64 (putU64 (putU8 ByteArray.empty (controlTag state.control)) state.heap.size)
    state.stack.length
  bytes.foldl (fun h b => (h ^^^ b.toUInt64) * fnvPrime) hash

/-- The same tick loop as `runBounded`, counting accepted ticks and folding the
fingerprint of every post-tick state. Its final state is checked against
`runBounded`'s by the driver, byte for byte. -/
def traceRun (limits : Limits) : Nat → State → Nat → UInt64 → State × Nat × UInt64
  | 0, state, used, hash => (state, used, hash)
  | ticks+1, state, used, hash => match step limits state with
    | .suspended .ticks next => traceRun limits ticks next (used + 1) (fingerprint hash next)
    | _ => (state, used, hash)

/-! ## C table emission -/

def nodeTag : Node → Nat
  | .bound .. => 0 | .lam .. => 1 | .app .. => 2 | .mix .. => 3 | .fix .. => 4
  | .specification .. => 5 | .prototype .. => 6 | .reflect .. => 7 | .metadata .. => 8
  | .project .. => 9 | .nat .. => 10 | .boolean .. => 11 | .label .. => 12
  | .binary .. => 13 | .extend .. => 14 | .record .. => 15 | .get .. => 16
  | .ifZero .. => 17 | .inject .. => 18 | .case .. => 19 | .ifBool .. => 20

/-- (a, b, c, d, pairs) for one node; see runtime.c's table contract. -/
def nodeSlots : Node → Nat × Nat × Nat × Nat × List (Nat × Nat)
  | .bound i => (i, 0, 0, 0, [])
  | .lam b => (b, 0, 0, 0, [])
  | .app f a => (f, a, 0, 0, [])
  | .mix l u d => (l, u, 0, d, [])
  | .fix s i d => (s, i, 0, d, [])
  | .specification m e => (m, e, 0, 0, [])
  | .prototype s t => (s, t, 0, 0, [])
  | .reflect t | .metadata t | .project t => (t, 0, 0, 0, [])
  | .nat _ => (0, 0, 0, 0, [])
  | .boolean b => (if b then 1 else 0, 0, 0, 0, [])
  | .label n => (n, 0, 0, 0, [])
  | .binary p l r => (primitiveCode p, l, r, 0, [])
  | .extend i fs => (i, 0, 0, 0, fs)
  | .record fs => (0, 0, 0, 0, fs)
  | .get t n => (t, n, 0, 0, [])
  | .ifZero v z s => (v, z, s, 0, [])
  | .inject n p => (n, p, 0, 0, [])
  | .case s arms => (s, 0, 0, 0, arms)
  | .ifBool c t f => (c, t, f, 0, [])

def limbs : Nat → Nat → List Nat
  | 0, _ => []
  | fuel+1, n => if n = 0 then [] else (n % 2^32) :: limbs fuel (n / 2^32)

def cArray (type name : String) (items : Array Nat) : String :=
  let body := if items.isEmpty then "0" else ",".intercalate (items.toList.map toString)
  s!"const {type} {name}[] = \{{body}};\n"

def emitC (compiled : Compiled) : Except String String := do
  let rom := compiled.rom
  let mut tags : Array Nat := #[]; let mut as : Array Nat := #[]; let mut bs : Array Nat := #[]
  let mut cs : Array Nat := #[]; let mut ds : Array Nat := #[]
  let mut pairOffsets : Array Nat := #[]; let mut pairLengths : Array Nat := #[]
  let mut pairs : Array Nat := #[]
  let mut natOffsets : Array Nat := #[]; let mut natLengths : Array Nat := #[]
  let mut limbPool : Array Nat := #[]
  for node in rom.nodes do
    let (a, b, c, d, ps) := nodeSlots node
    if a ≥ 2^32 || b ≥ 2^32 || c ≥ 2^32 || d ≥ 2^32 then throw "ROM slot exceeds u32"
    tags := tags.push (nodeTag node); as := as.push a; bs := bs.push b; cs := cs.push c; ds := ds.push d
    pairOffsets := pairOffsets.push (pairs.size / 2); pairLengths := pairLengths.push ps.length
    for (label, code) in ps do pairs := (pairs.push label).push code
    let ls := match node with | .nat n => limbs (n.log2 + 2) n | _ => []
    natOffsets := natOffsets.push limbPool.size; natLengths := natLengths.push ls.length
    for l in ls do limbPool := limbPool.push l
  let mut labelOffsets : Array Nat := #[]; let mut labelLengths : Array Nat := #[]
  let mut labelBytes : Array Nat := #[]
  for name in rom.labels do
    labelOffsets := labelOffsets.push labelBytes.size
    labelLengths := labelLengths.push name.toUTF8.size
    for byte in name.toUTF8 do labelBytes := labelBytes.push byte.toNat
  pure <| String.join [
    "/* Generated by Compiler/ObjectiveBendEmitC.lean: the code ROM of one closed\n",
    "   Objective Bend program for native/objective-emit/runtime.c. Do not edit. */\n",
    "#include <stdint.h>\n",
    s!"const uint32_t ob_node_count = {rom.nodes.size};\n",
    s!"const uint32_t ob_label_count = {rom.labels.size};\n",
    s!"const uint32_t ob_entry = {compiled.entry};\n",
    s!"const uint32_t ob_bound_zero = {compiled.boundZero};\n",
    cArray "uint8_t" "ob_tag" tags, cArray "uint32_t" "ob_a" as, cArray "uint32_t" "ob_b" bs,
    cArray "uint32_t" "ob_c" cs, cArray "uint32_t" "ob_d" ds,
    cArray "uint32_t" "ob_pair_off" pairOffsets, cArray "uint32_t" "ob_pair_len" pairLengths,
    cArray "uint32_t" "ob_pairs" pairs,
    cArray "uint32_t" "ob_nat_off" natOffsets, cArray "uint32_t" "ob_nat_len" natLengths,
    cArray "uint32_t" "ob_limbs" limbPool,
    cArray "uint32_t" "ob_label_off" labelOffsets, cArray "uint32_t" "ob_label_len" labelLengths,
    cArray "uint8_t" "ob_label_bytes" labelBytes]

/-- info: 'Minidregg.Compiler.ObjectiveBendEmitC.fixBody_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fixBody_exact
/-- info: 'Minidregg.Compiler.ObjectiveBendEmitC.mixTarget_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mixTarget_exact
/--
info: 'Minidregg.Compiler.ObjectiveBendEmitC.case_allocates_bound_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms case_allocates_bound_zero

end Minidregg.Compiler.ObjectiveBendEmitC
