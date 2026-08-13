/-
# `Compiler/ZkmlTraceCheck.lean` — the trace wire format, and a CHECKED reader

**Substrate, said out loud: this is Lean-authored arithmetization.** The Rust
tracer is a stager. It records ops, shapes, wire ids and branch decisions; it
authors no constraint, and everything that decides what a trace MEANS lives in
`Theory/ZkmlTensorOps.lean`.

## What a "checked reader" is here

The reader's output type is `Trace tOut Γ` — the **intrinsically typed** trace of
`Theory/ZkmlTensorOps`. A trace that mentions a wire out of scope, at the wrong
dtype, with a mismatched matmul contraction, or with a `reshape` that changes the
element count, is not a term of that type. So "the reader returned `.ok`" is not a
claim to be audited: it is the construction of an object whose existence is the
well-typedness. There is no separate validator to fall out of sync with.

The reader is also the FIRST place the trace format gets a refusal. `checkTrace`
returns `Except String`, never a default and never a repair.

## The wire format is v1, not catgrad's v0 — and greenfield doctrine applies

`phase0/mnist-trace.json` is `catgrad-trace/v0`, which is the shape catgrad's
`Backend` trait happened to have. Inheriting it would inherit its gaps. Each
change below is a fact v0 does not carry; `phase0/v0_to_v1.py` performs the
conversion and PRINTS every place it had to invent one.

1. **Constants are not ops.** v0 emits weights, the inference input and program
   literals alike as a `const` op carrying an FNV digest. Here they are entries of
   the initial context with a mandatory `role` (`input` / `param` / `literal`) and
   a mandatory `path`. Two reasons, and they are independent: the vocabulary
   forbids data payloads (`[N3-converse]`), and a trace that cannot say WHICH
   weight entered a wire cannot be checked against any weight commitment at all.
   The converter assigns roles by tensor RANK, which is a guess, and says so — the
   tracer must supply them.
2. **The output is declared.** v0 declares neither the output wire nor its type;
   "the last op" is a convention. `outWire` and `outTy` are required, and the
   checker refuses a trace whose declared output type does not match the wire.
3. **No per-op `dtype` field.** v0 carries one, with no statement of whether it is
   the operand or the result dtype — and for `cast` the two differ by definition.
   Operand dtypes come from the operand wires and the result dtype is derived, so
   they cannot disagree.
4. **Rank-2 matmul only.** v0 gives a `contract` attribute and says nothing about
   what a rank>2 operand means. The checker REFUSES rank≠2 rather than picking a
   reading. Batched matmul enters as a constructor when it is needed, with a
   denotation.
5. **Row-major, pinned.** v0's `reshape` gives a target shape and no memory order;
   the two readings compute different functions. The order is fixed once, at
   `Theory/ZkmlTensorOps.idxEquiv`.

`FNV is still FNV.` The `path` field makes the *identity* of a constant
expressible; binding it needs a collision-resistant commitment, which this file
does not provide and does not pretend to. That is memo item v1-2 and is open.

## What this file establishes about the measured MNIST trace

Every number below is computed by the Lean kernel from the checked, intrinsically
typed trace — not read off the tracer's own report:

* it **checks**: 7 context entries, 19 ops, output `f32[2,10]`;
* **158 800 multiply-accumulates** — independently reproducing the tracer's
  measured figure through a completely different route;
* **3 548 elementwise output elements** (the memo's 3 552 counts the four scalar
  constants, which are context entries here, not ops);
* **4 gadget ops**, and `gadgetCount_eq_zero_iff` makes that count a certificate:
  MNIST is NOT in the arithmetic fragment, and the four are exactly the sigmoid's
  two `pow` and two `div`. Everything else in a two-layer MLP — including both
  matmuls — is carried by the ring structure.
-/
import Compiler.EmitSerialize
import Theory.ZkmlTensorOps
import Lean.Data.Json

namespace Minidregg.Compiler

open Minidregg.Theory.ZkmlTensorOps
open Lean (Json toJson)

/-! ## §1. The v1 raw trace — first-order, exactly the JSON. -/

/-- What an initial wire IS. The three have different commitment obligations: an
`input` is public and per-turn, a `param` is committed once and referenced across
turns, a `literal` is fixed by the program. v0 cannot tell them apart. -/
inductive WireRole
  | input | param | literal
  deriving DecidableEq, Repr

/-- A declared initial wire. `path` is mandatory: a trace that cannot name the
weight it read cannot be checked against a weight commitment. -/
structure RawInput where
  role : WireRole
  ty : TyT
  path : String
  deriving DecidableEq, Repr

/-- A raw op: a constructor tag plus wire LEVELS (0 = first declared). Levels, not
de Bruijn indices — the tracer counts forwards. -/
inductive RawOp
  | un (k : Un1) (a : ℕ)
  | bin (k : Bin2) (a b : ℕ)
  | cmp (k : Cmp2) (a b : ℕ)
  | select (s a b : ℕ)
  | fma (a b c : ℕ)
  | map (f : FnId) (a : ℕ)
  | cast (a : ℕ) (d : Dtype)
  | matmul (a b : ℕ)
  | reduce (k : Bin2) (init a : ℕ)
  | gather (tbl i : ℕ)
  | reshape (a : ℕ) (s : List ℕ)
  | broadcast (a : ℕ) (s : List ℕ)
  | transpose (a : ℕ)
  deriving DecidableEq, Repr

/-- The v1 trace. -/
structure RawTrace where
  version : String
  inputs : List RawInput
  ops : List RawOp
  outWire : ℕ
  outTy : TyT
  deriving DecidableEq, Repr

/-- The accepted wire-format version. A trace stamped otherwise is REFUSED, not
reinterpreted. -/
def zkmlTraceVersion : String := "zkml-trace/v1"

/-! ## §2. The checker — its RESULT TYPE is the theorem. -/

/-- A checked trace: an intrinsically typed program over the declared context. -/
structure CheckedTrace where
  ctx : Ctx
  tOut : TyT
  prog : Trace tOut ctx

/-- Look a de Bruijn INDEX up in a context, recovering its type. -/
def varAtIdx : (Γ : Ctx) → ℕ → Option ((t : TyT) × Var Γ t)
  | [], _ => none
  | t :: _, 0 => some ⟨t, Var.here⟩
  | _ :: Γ, n + 1 => (varAtIdx Γ n).map fun p => ⟨p.1, Var.there p.2⟩

/-- Look a wire LEVEL up (0 = first declared), converting to a de Bruijn index. -/
def varOfLevel (Γ : Ctx) (l : ℕ) : Option ((t : TyT) × Var Γ t) :=
  if l < Γ.length then varAtIdx Γ (Γ.length - 1 - l) else none

/-- The type on a wire, or a refusal. -/
def wireTy (Γ : Ctx) (l : ℕ) : Except String TyT :=
  match varOfLevel Γ l with
  | none => .error s!"wire {l} is not in scope"
  | some p => .ok p.1

/-- A wire AT AN EXPECTED TYPE, or a refusal. This is the only way a `Var` is ever
built from raw data, so every operand in a checked trace has been type-checked. -/
def varTyped (Γ : Ctx) (l : ℕ) (t : TyT) : Except String (Var Γ t) :=
  match varOfLevel Γ l with
  | none => .error s!"wire {l} is not in scope"
  | some ⟨t', v⟩ => if h : t' = t then .ok (h ▸ v) else .error s!"wire {l}: type mismatch"

/-- Check one raw op against a context. Every shape law of the vocabulary is
discharged here, at runtime, with a refusal on failure — and the result carries the
discharged law in its type. -/
def checkOp (Γ : Ctx) : RawOp → Except String (TOp Γ)
  | .un k a => do
      let t ← wireTy Γ a
      return TOp.un k t (← varTyped Γ a t)
  | .bin k a b => do
      let t ← wireTy Γ a
      return TOp.bin k t (← varTyped Γ a t) (← varTyped Γ b t)
  | .cmp k a b => do
      let t ← wireTy Γ a
      return TOp.cmp k t (← varTyped Γ a t) (← varTyped Γ b t)
  | .select s a b => do
      let t ← wireTy Γ a
      return TOp.select t (← varTyped Γ s t.pred) (← varTyped Γ a t) (← varTyped Γ b t)
  | .fma a b c => do
      let t ← wireTy Γ a
      return TOp.fma t (← varTyped Γ a t) (← varTyped Γ b t) (← varTyped Γ c t)
  | .map f a => do
      let t ← wireTy Γ a
      return TOp.map f t (← varTyped Γ a t)
  | .cast a d => do
      let t ← wireTy Γ a
      return TOp.cast t (← varTyped Γ a t) d
  | .matmul a b => do
      let ta ← wireTy Γ a
      let tb ← wireTy Γ b
      match ta.shape, tb.shape with
      | [m, k], [_, n] =>
          return TOp.matmul ta.dtype m k n (← varTyped Γ a ⟨ta.dtype, [m, k]⟩)
            (← varTyped Γ b ⟨ta.dtype, [k, n]⟩)
      | _, _ => .error "matmul: both operands must be rank 2"
  | .reduce k init a => do
      let ta ← wireTy Γ a
      match ta.shape with
      | [r, c] =>
          return TOp.reduce k ta.dtype r c (← varTyped Γ init ⟨ta.dtype, [r]⟩)
            (← varTyped Γ a ⟨ta.dtype, [r, c]⟩)
      | _ => .error "reduce: operand must be rank 2"
  | .gather tbl i => do
      let tt ← wireTy Γ tbl
      let ti ← wireTy Γ i
      match tt.shape, ti.shape with
      | [n], [m] =>
          return TOp.gather tt.dtype n m (← varTyped Γ tbl ⟨tt.dtype, [n]⟩)
            (← varTyped Γ i ⟨Dtype.idx, [m]⟩)
      | _, _ => .error "gather: table and index must be rank 1"
  | .reshape a s => do
      let t ← wireTy Γ a
      let va ← varTyped Γ a t
      if h : size s = size t.shape then return TOp.reshape t va s h
      else .error "reshape: element count differs"
  | .broadcast a s => do
      let t ← wireTy Γ a
      let va ← varTyped Γ a t
      if h : size t.shape = 1 then return TOp.broadcast t va h s
      else .error "broadcast: source must be a scalar (general broadcast is not in v1)"
  | .transpose a => do
      let t ← wireTy Γ a
      match t.shape with
      | [m, n] => return TOp.transpose t.dtype m n (← varTyped Γ a ⟨t.dtype, [m, n]⟩)
      | _ => .error "transpose: operand must be rank 2"

/-- Check an op list, threading the growing context. The declared output wire is
checked at the END against the declared output type. -/
def checkOps (tOut : TyT) (out : ℕ) : (Γ : Ctx) → List RawOp → Except String (Trace tOut Γ)
  | Γ, [] => do return Trace.ret (← varTyped Γ out tOut)
  | Γ, o :: rest => do
      let op ← checkOp Γ o
      return Trace.op op (← checkOps tOut out (op.outTy :: Γ) rest)

/-- **The checked reader.** Refuses an unknown version; otherwise returns an
intrinsically typed trace over the declared initial context. -/
def checkTrace (r : RawTrace) : Except String CheckedTrace := do
  unless r.version = zkmlTraceVersion do
    throw s!"unsupported trace version {r.version} (expected {zkmlTraceVersion})"
  let g : Ctx := (r.inputs.map (·.ty)).reverse
  return ⟨g, r.outTy, ← checkOps r.outTy r.outWire g r.ops⟩

/-- The census of a checked trace. -/
def checkedCensus (r : RawTrace) : Except String Census :=
  (checkTrace r).map fun c => census c.prog

/-- The gadget count of a checked trace — by `gadgetCount_eq_zero_iff`, a
certificate for arithmetic-fragment membership rather than a statistic. -/
def checkedGadgets (r : RawTrace) : Except String ℕ :=
  (checkTrace r).map fun c => gadgetCount c.prog

/-- Whether a raw trace checks at all. -/
def checksOk (r : RawTrace) : Bool := (checkTrace r).toOption.isSome

/-! ## §3. The JSON codec — Lean is the AUTHOR of the wire format.

Writer and reader over the v1 schema, with the round trip checked at build time on
the real MNIST trace. The reader is strict: an unknown op tag, an unknown dtype or
a missing field is a refusal, never a default. -/

/-- Serialize a dtype. `f8` keeps catgrad's spelling so the two formats can be
diffed by eye. -/
def dtypeToJson : Dtype → Json
  | .bf16 => Json.str "bf16"
  | .f32 => Json.str "f32"
  | .fp8 => Json.str "f8"
  | .pred => Json.str "pred"
  | .idx => Json.str "idx"

def dtypeFromJson? (j : Json) : Except String Dtype := do
  match ← j.getStr? with
  | "bf16" => pure .bf16
  | "f32" => pure .f32
  | "f8" => pure .fp8
  | "pred" => pure .pred
  | "idx" => pure .idx
  | s => throw s!"unknown dtype: {s}"

def shapeToJson (s : List ℕ) : Json := Json.arr (s.map toJson).toArray

def shapeFromJson? (j : Json) : Except String (List ℕ) := do
  (← j.getArr?).toList.mapM (·.getNat?)

def tyToJson (t : TyT) : Json :=
  Json.mkObj [("dtype", dtypeToJson t.dtype), ("shape", shapeToJson t.shape)]

def tyFromJson? (j : Json) : Except String TyT := do
  pure ⟨← dtypeFromJson? (← j.getObjVal? "dtype"), ← shapeFromJson? (← j.getObjVal? "shape")⟩

def roleToJson : WireRole → Json
  | .input => Json.str "input"
  | .param => Json.str "param"
  | .literal => Json.str "literal"

def roleFromJson? (j : Json) : Except String WireRole := do
  match ← j.getStr? with
  | "input" => pure .input
  | "param" => pure .param
  | "literal" => pure .literal
  | s => throw s!"unknown wire role: {s}"

def inputToJson (i : RawInput) : Json :=
  Json.mkObj [("role", roleToJson i.role), ("dtype", dtypeToJson i.ty.dtype),
    ("shape", shapeToJson i.ty.shape), ("path", Json.str i.path)]

def inputFromJson? (j : Json) : Except String RawInput := do
  pure { role := ← roleFromJson? (← j.getObjVal? "role")
         ty := ⟨← dtypeFromJson? (← j.getObjVal? "dtype"),
                ← shapeFromJson? (← j.getObjVal? "shape")⟩
         path := ← (← j.getObjVal? "path").getStr? }

def un1ToJson : Un1 → Json | .neg => Json.str "neg"

def un1FromJson? (j : Json) : Except String Un1 := do
  match ← j.getStr? with
  | "neg" => pure .neg
  | s => throw s!"unknown unary kind: {s}"

def bin2ToJson : Bin2 → Json
  | .add => Json.str "add" | .sub => Json.str "sub" | .mul => Json.str "mul"
  | .div => Json.str "div" | .pow => Json.str "pow"

def bin2FromJson? (j : Json) : Except String Bin2 := do
  match ← j.getStr? with
  | "add" => pure .add | "sub" => pure .sub | "mul" => pure .mul
  | "div" => pure .div | "pow" => pure .pow
  | s => throw s!"unknown binary kind: {s}"

def cmp2ToJson : Cmp2 → Json
  | .lt => Json.str "lt" | .le => Json.str "le" | .eq => Json.str "eq"

def cmp2FromJson? (j : Json) : Except String Cmp2 := do
  match ← j.getStr? with
  | "lt" => pure .lt | "le" => pure .le | "eq" => pure .eq
  | s => throw s!"unknown comparison kind: {s}"

def rawOpToJson : RawOp → Json
  | .un k a => Json.mkObj [("op", Json.str "un"), ("kind", un1ToJson k),
      ("ins", shapeToJson [a])]
  | .bin k a b => Json.mkObj [("op", Json.str "bin"), ("kind", bin2ToJson k),
      ("ins", shapeToJson [a, b])]
  | .cmp k a b => Json.mkObj [("op", Json.str "cmp"), ("kind", cmp2ToJson k),
      ("ins", shapeToJson [a, b])]
  | .select s a b => Json.mkObj [("op", Json.str "select"), ("ins", shapeToJson [s, a, b])]
  | .fma a b c => Json.mkObj [("op", Json.str "fma"), ("ins", shapeToJson [a, b, c])]
  | .map f a => Json.mkObj [("op", Json.str "map"), ("fn", toJson f),
      ("ins", shapeToJson [a])]
  | .cast a d => Json.mkObj [("op", Json.str "cast"), ("dtype", dtypeToJson d),
      ("ins", shapeToJson [a])]
  | .matmul a b => Json.mkObj [("op", Json.str "matmul"), ("ins", shapeToJson [a, b])]
  | .reduce k i a => Json.mkObj [("op", Json.str "reduce"), ("kind", bin2ToJson k),
      ("ins", shapeToJson [i, a])]
  | .gather t i => Json.mkObj [("op", Json.str "gather"), ("ins", shapeToJson [t, i])]
  | .reshape a s => Json.mkObj [("op", Json.str "reshape"), ("ins", shapeToJson [a]),
      ("shape", shapeToJson s)]
  | .broadcast a s => Json.mkObj [("op", Json.str "broadcast"), ("ins", shapeToJson [a]),
      ("shape", shapeToJson s)]
  | .transpose a => Json.mkObj [("op", Json.str "transpose"), ("ins", shapeToJson [a])]

/-- Read `n` operand levels, refusing the wrong arity — an op record with two
operands where three were expected is a parse error, not a silent truncation. -/
def insN (j : Json) (n : ℕ) : Except String (List ℕ) := do
  let l ← shapeFromJson? (← j.getObjVal? "ins")
  if l.length = n then pure l else throw s!"expected {n} operands, got {l.length}"

def rawOpFromJson? (j : Json) : Except String RawOp := do
  let tag ← (← j.getObjVal? "op").getStr?
  match tag with
  | "un" => match ← insN j 1 with
      | [a] => pure (.un (← un1FromJson? (← j.getObjVal? "kind")) a)
      | _ => throw "un: arity"
  | "bin" => match ← insN j 2 with
      | [a, b] => pure (.bin (← bin2FromJson? (← j.getObjVal? "kind")) a b)
      | _ => throw "bin: arity"
  | "cmp" => match ← insN j 2 with
      | [a, b] => pure (.cmp (← cmp2FromJson? (← j.getObjVal? "kind")) a b)
      | _ => throw "cmp: arity"
  | "select" => match ← insN j 3 with
      | [s, a, b] => pure (.select s a b)
      | _ => throw "select: arity"
  | "fma" => match ← insN j 3 with
      | [a, b, c] => pure (.fma a b c)
      | _ => throw "fma: arity"
  | "map" => match ← insN j 1 with
      | [a] => pure (.map (← (← j.getObjVal? "fn").getNat?) a)
      | _ => throw "map: arity"
  | "cast" => match ← insN j 1 with
      | [a] => pure (.cast a (← dtypeFromJson? (← j.getObjVal? "dtype")))
      | _ => throw "cast: arity"
  | "matmul" => match ← insN j 2 with
      | [a, b] => pure (.matmul a b)
      | _ => throw "matmul: arity"
  | "reduce" => match ← insN j 2 with
      | [i, a] => pure (.reduce (← bin2FromJson? (← j.getObjVal? "kind")) i a)
      | _ => throw "reduce: arity"
  | "gather" => match ← insN j 2 with
      | [t, i] => pure (.gather t i)
      | _ => throw "gather: arity"
  | "reshape" => match ← insN j 1 with
      | [a] => pure (.reshape a (← shapeFromJson? (← j.getObjVal? "shape")))
      | _ => throw "reshape: arity"
  | "broadcast" => match ← insN j 1 with
      | [a] => pure (.broadcast a (← shapeFromJson? (← j.getObjVal? "shape")))
      | _ => throw "broadcast: arity"
  | "transpose" => match ← insN j 1 with
      | [a] => pure (.transpose a)
      | _ => throw "transpose: arity"
  | s => throw s!"unknown op tag: {s}"

/-- **The trace writer.** -/
def rawTraceToJson (r : RawTrace) : Json :=
  Json.mkObj
    [ ("version", Json.str r.version),
      ("inputs", Json.arr (r.inputs.map inputToJson).toArray),
      ("ops", Json.arr (r.ops.map rawOpToJson).toArray),
      ("out", toJson r.outWire),
      ("out_ty", tyToJson r.outTy) ]

/-- **The trace reader**, JSON to raw trace. Composed with `checkTrace` this is the
whole path from a file on disk to an intrinsically typed `Trace`. -/
def rawTraceFromJson? (j : Json) : Except String RawTrace := do
  pure { version := ← (← j.getObjVal? "version").getStr?
         inputs := ← (← (← j.getObjVal? "inputs").getArr?).toList.mapM inputFromJson?
         ops := ← (← (← j.getObjVal? "ops").getArr?).toList.mapM rawOpFromJson?
         outWire := ← (← j.getObjVal? "out").getNat?
         outTy := ← tyFromJson? (← j.getObjVal? "out_ty") }

/-- Read a trace from a file and check it in one step. -/
def loadCheckedTrace (path : System.FilePath) : IO CheckedTrace := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error e => throw <| IO.userError s!"{path}: not JSON: {e}"
  | .ok j =>
    match rawTraceFromJson? j >>= checkTrace with
    | .error e => throw <| IO.userError s!"{path}: {e}"
    | .ok c => pure c

def writeTraceJson (path : System.FilePath) (r : RawTrace) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path ((rawTraceToJson r).pretty ++ "\n")

/-! ## §4. The measured MNIST trace, in v1.

Converted from `phase0/mnist-trace.json` by `phase0/v0_to_v1.py`, which prints
every fact it had to invent (§0, items 1–5). `SimpleMNISTModel`, batch 2,
784 → 100 → 10, sigmoid. -/

def mnistRaw : RawTrace where
  version := "zkml-trace/v1"
  inputs := [
    ⟨WireRole.param, ⟨Dtype.f32, [784, 100]⟩, "weight/b399b1f5a6354f02"⟩,
    ⟨WireRole.param, ⟨Dtype.f32, [100, 10]⟩, "weight/56d3cfe223499d49"⟩,
    ⟨WireRole.input, ⟨Dtype.f32, [2, 28, 28]⟩, "input/0"⟩,
    ⟨WireRole.literal, ⟨Dtype.f32, []⟩, "lit/c1216a7f9c5c2f98"⟩,
    ⟨WireRole.literal, ⟨Dtype.f32, []⟩, "lit/0f15fcfdf6fc7fcc"⟩,
    ⟨WireRole.literal, ⟨Dtype.f32, []⟩, "lit/c1216a7f9c5c2f98"⟩,
    ⟨WireRole.literal, ⟨Dtype.f32, []⟩, "lit/0f15fcfdf6fc7fcc"⟩
  ]
  ops := [
    RawOp.reshape 2 [2, 784],
    RawOp.matmul 7 0,
    RawOp.un Un1.neg 8,
    RawOp.broadcast 3 [2, 100],
    RawOp.cast 10 Dtype.f32,
    RawOp.broadcast 4 [2, 100],
    RawOp.cast 12 Dtype.f32,
    RawOp.bin Bin2.pow 13 9,
    RawOp.bin Bin2.add 11 14,
    RawOp.bin Bin2.div 11 15,
    RawOp.matmul 16 1,
    RawOp.un Un1.neg 17,
    RawOp.broadcast 5 [2, 10],
    RawOp.cast 19 Dtype.f32,
    RawOp.broadcast 6 [2, 10],
    RawOp.cast 21 Dtype.f32,
    RawOp.bin Bin2.pow 22 18,
    RawOp.bin Bin2.add 20 23,
    RawOp.bin Bin2.div 20 24
  ]
  outWire := 25
  outTy := ⟨Dtype.f32, [2, 10]⟩

/-! ## §5. What the kernel computes from it. -/

/-- **It checks.** The measured MNIST trace is a well-typed term of the vocabulary:
every wire in scope at the right dtype and shape, both matmul contractions
agreeing, the `reshape` element-count-preserving, both broadcasts from genuine
scalars, and the declared output wire at the declared type. -/
theorem mnistRaw_checks : checksOk mnistRaw = true := by rfl

/-- **The census, kernel-computed from the typed trace.** 19 ops; **158 800**
multiply-accumulates — independently reproducing the tracer's own measured figure
by a completely different route; 3 548 elementwise output elements. (The memo's
3 552 counts the four scalar constants, which are context entries here rather than
ops — a definitional difference, stated so nobody has to rediscover it.) -/
theorem mnistRaw_census : checkedCensus mnistRaw = .ok ⟨19, 158800, 3548⟩ := by rfl

/-- **The gadget bill of a two-layer MLP is FOUR ops.** By
`gadgetCount_eq_zero_iff` this is a certificate, not a statistic: MNIST is not in
the arithmetic fragment, and the four ops responsible are the sigmoid's two `pow`
and two `div`. Everything else — both matmuls, both negations, the four identity
casts, the four broadcasts, the reshape and both adds — is carried by the ring
structure and needs no gadget at all. -/
theorem mnistRaw_gadgets : checkedGadgets mnistRaw = .ok 4 := by rfl

/-! ### §5.1 The checker refuses — three teeth, each built CONSTRUCTIVELY.

A reader that cannot go red is not a reader. Each mutation below is built by
`List.set` on the real trace and each is proved to be a real change before its
refusal is read, so a mutation that silently became a no-op would fail loudly
rather than leave a green test asserting nothing. -/

/-- Repoint the first matmul's right operand from the 784×100 weight to the 100×10
one: the contraction no longer agrees. -/
def mnistForgedContraction : RawTrace :=
  { mnistRaw with ops := mnistRaw.ops.set 1 (RawOp.matmul 7 1) }

/-- The mutation is real. -/
theorem mnistForgedContraction_changed : mnistForgedContraction.ops ≠ mnistRaw.ops := by
  decide

/-- *Tooth 1*: a mismatched matmul contraction is REFUSED. -/
theorem mnistForgedContraction_refused : checksOk mnistForgedContraction = false := by rfl

/-- Reshape `[2,28,28]` (1568 elements) to `[2,783]` (1566). -/
def mnistForgedReshape : RawTrace :=
  { mnistRaw with ops := mnistRaw.ops.set 0 (RawOp.reshape 2 [2, 783]) }

theorem mnistForgedReshape_changed : mnistForgedReshape.ops ≠ mnistRaw.ops := by decide

/-- *Tooth 2*: an element-count-changing `reshape` is REFUSED. The vocabulary
carries the size-preservation law as a proof field, so this cannot be admitted. -/
theorem mnistForgedReshape_refused : checksOk mnistForgedReshape = false := by rfl

/-- Declare the output at `f32[2,11]` instead of `f32[2,10]`. -/
def mnistForgedOutTy : RawTrace :=
  { mnistRaw with outTy := ⟨Dtype.f32, [2, 11]⟩ }

theorem mnistForgedOutTy_changed : mnistForgedOutTy.outTy ≠ mnistRaw.outTy := by decide

/-- *Tooth 3*: a declared output type that does not match the output wire is
REFUSED — the fact v0 could not state at all, since it declares no output. -/
theorem mnistForgedOutTy_refused : checksOk mnistForgedOutTy = false := by rfl

/-- *Tooth 4*: a trace stamped with another wire-format version is REFUSED rather
than reinterpreted. Greenfield doctrine: the old shape must fail to load. -/
theorem mnistForgedVersion_refused :
    checksOk { mnistRaw with version := "catgrad-trace/v0" } = false := by rfl

/-! ## §6. The artifacts.

Lean is the author of the v1 JSON; `phase0/v0_to_v1.py` produces the same object
from the v0 trace and the two are compared outside the build. The round trip is
checked here, on the real trace, at build time. -/

/-- Round-trip the MNIST trace through the JSON codec; elaboration fails on
mismatch. -/
def roundTripMnist : IO Unit := do
  let txt := (rawTraceToJson mnistRaw).pretty
  match Json.parse txt with
  | .error e => throw <| IO.userError s!"v1 trace text does not re-parse: {e}"
  | .ok j =>
    match rawTraceFromJson? j with
    | .error e => throw <| IO.userError s!"v1 trace does not round-trip: {e}"
    | .ok r =>
      unless r = mnistRaw do throw <| IO.userError "v1 trace round-trip mismatch"
      IO.println s!"v1 round-trip OK: {r.inputs.length} inputs, {r.ops.length} ops"

#eval roundTripMnist

-- The Lean-authored v1 trace, for the tracer and the prover side to read.
#eval writeTraceJson "prover/testdata/zkml_mnist_trace_v1.json" mnistRaw

/-! ## §7. Axiom accounting. -/

/-- info: 'Minidregg.Compiler.mnistRaw_census' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms mnistRaw_census

/-- info: 'Minidregg.Compiler.mnistRaw_gadgets' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms mnistRaw_gadgets

/-- info: 'Minidregg.Compiler.mnistForgedContraction_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms mnistForgedContraction_refused

end Minidregg.Compiler
