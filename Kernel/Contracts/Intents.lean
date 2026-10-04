/-
# Kernel.Contracts.Intents — the typed intent over the six cuts, its canonical bytes, its name

This module is the SOURCE OF TRUTH for the bytes the Mini SDK (`native/mini-sdk`,
`native/mini-sdk-ts`) hashes into an `InvocationId` and binds into a confirmation. The SDK
carries one client-side encoder (Rust; the TypeScript SDK reaches it through wasm) and is
checked byte-for-byte against the vectors this module's emitter prints
(`Kernel/Contracts/IntentVectors.lean` → `native/mini-sdk/golden/lean-intents.json`).

An `Intent` is one semantic request by one actor: a 16-byte salt chosen once at creation (so two
deliberate identical requests are two requests and a retry of one is never a second), the
actor, and one `Cut`. The cuts are the SDK's pre-lowering form of `Kernel.Contracts.Cuts`
(`Observe`, `Invoke`, `Reserve`, `Install`, `Release`, `Retire`): identifiers are native
naturals, a kind is the declared kind string the native author reads, an artifact is exact
digest + length + format. Nothing here is a second `ObjectRef`: `Kernel.Contracts.Identities`
names the world coordinates a request is DECIDED against; this names the request itself.

Canonical bytes: `framed intentFrame intentStream` — the repo's one stream nucleus
(`Tower256ConcreteBackend.StreamCodec`: base-255 naturals, count-prefixed lists, tagged
options, nested prefix-free sums, a string is its scalar values), under the frame
`DREGG/CONTRACT/INTENT/v1`. The `InvocationId` preimage is `DREGG/CONTRACT/INTENT-ID/v1 ‖
bytes`, hashed with SHA-256 by the client (the digest is not defined here).

Facts proved here: decoding is a left inverse of encoding (`intent_roundtrip`), encoding is
injective (`intent_encode_injective`, hence two distinct requests never share an
`InvocationId` preimage: `intentIdPreimage_injective`), an intent's bytes never decode as any
`Kernel.Contracts.Identities` frame (`intent_frame_separates_identities`), and the layout is
pinned by a named worked example (`retire_example_bytes`).

The text entry (`parseIntent`, `encodeSpelling`) reads the SDK's JSON spelling and is strict:
exactly the fields of the cut, canonical decimals, lowercase hex, known routes, integers of
magnitude at most 2^53 in payloads. `@[export]`: `minidregg_intent_encode`,
`minidregg_intent_id_preimage` (one status byte, then the bytes or a UTF-8 refusal).
-/
import Compiler.NockProgramCodec
import Kernel.Contracts.Identities
import Lean.Data.Json
import Theory.AssertAxioms

namespace Minidregg.Kernel.Contracts.Intents

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.NockProgramCodec (framed framedDecode)
open Minidregg.Compiler.PolicyRecordCodec (stringStream)
open Minidregg.Theory.IndexedProgram (LawfulCodec)

set_option autoImplicit false

/-! ## Types -/

/-- Native identity, governing domain, declared kind (the string the native author reads). -/
structure Object where
  id : Nat
  domain : Nat
  kind : String
  deriving DecidableEq, Repr

/-- An exact root of an object; never latest-by-name. -/
structure Revision where
  object : Object
  root : Nat
  deriving DecidableEq, Repr

/-- Exact bytes: digest, length, format. A content address confers no permission. -/
structure Artifact where
  sha256 : List UInt8
  length : Nat
  format : String
  deriving DecidableEq, Repr

/-- The native invocation routes the signed command may carry. -/
inductive Route where
  | ordinary
  | objectiveMethod
  | activityDispatch
  | roomRelease
  | roomPublish
  deriving DecidableEq, Repr

structure Family where
  route : Route
  context : List UInt8
  deriving DecidableEq, Repr

/-- One invoke target. `payload` is CANONICAL JSON text (`canonText`): the only producer in this
module is the spelling parser, which canonicalises. -/
structure Target where
  revision : Revision
  capability : Nat
  observeCapability : Nat
  schemaVersion : Nat
  payload : String
  deriving DecidableEq, Repr

inductive Cut where
  | observe (resource : Revision) (projection : String) (capability : Nat)
  | invoke (targets : List Target) (family : Option Family)
  | reserve (candidate : Artifact) (footprint : List Object) (law obligation : Artifact)
  | install (candidate : Artifact) (preimage : Revision) (effects obligation : Artifact)
  | release (result : Artifact) (audience : List Nat) (law : Artifact)
  | retire (obligation evidence : Artifact)
  deriving DecidableEq, Repr

structure Intent where
  /-- Chosen once, at creation; 16 bytes. -/
  salt : List UInt8
  actor : Nat
  cut : Cut
  deriving DecidableEq, Repr

/-! ## Stream bodies -/

def unitStream : StreamCodec Unit where
  encode _ := []
  decodePrefix bytes := some ((), bytes)
  decodePrefix_encode := by intro _ _; rfl

def objectStream : StreamCodec Object :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat stringStream))
    (fun v => (v.id, v.domain, v.kind)) (fun w => ⟨w.1, w.2.1, w.2.2⟩)
    (by intro v; cases v; rfl)

def revisionStream : StreamCodec Revision :=
  StreamCodec.xmap (StreamCodec.product objectStream StreamCodec.nat)
    (fun v => (v.object, v.root)) (fun w => ⟨w.1, w.2⟩)
    (by intro v; cases v; rfl)

def artifactStream : StreamCodec Artifact :=
  StreamCodec.xmap (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat stringStream))
    (fun v => (v.sha256, v.length, v.format)) (fun w => ⟨w.1, w.2.1, w.2.2⟩)
    (by intro v; cases v; rfl)

def routeStream : StreamCodec Route :=
  StreamCodec.xmap
    (StreamCodec.sum unitStream (StreamCodec.sum unitStream (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream unitStream))))
    (fun v => match v with
      | .ordinary => .inl ()
      | .objectiveMethod => .inr (.inl ())
      | .activityDispatch => .inr (.inr (.inl ()))
      | .roomRelease => .inr (.inr (.inr (.inl ())))
      | .roomPublish => .inr (.inr (.inr (.inr ()))))
    (fun w => match w with
      | .inl _ => .ordinary
      | .inr (.inl _) => .objectiveMethod
      | .inr (.inr (.inl _)) => .activityDispatch
      | .inr (.inr (.inr (.inl _))) => .roomRelease
      | .inr (.inr (.inr (.inr _))) => .roomPublish)
    (by intro v; cases v <;> rfl)

def familyStream : StreamCodec Family :=
  StreamCodec.xmap (StreamCodec.product routeStream bytesStream)
    (fun v => (v.route, v.context)) (fun w => ⟨w.1, w.2⟩)
    (by intro v; cases v; rfl)

def targetStream : StreamCodec Target :=
  StreamCodec.xmap
    (StreamCodec.product revisionStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat stringStream))))
    (fun v => (v.revision, v.capability, v.observeCapability, v.schemaVersion, v.payload))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2⟩)
    (by intro v; cases v; rfl)

/-- The six cuts as a nested prefix-free sum, in declaration order: observe `0`, invoke `1 0`,
reserve `1 1 0`, install `1 1 1 0`, release `1 1 1 1 0`, retire `1 1 1 1 1`. -/
abbrev CutWire :=
  (Revision × String × Nat) ⊕
  ((List Target × Option Family) ⊕
  ((Artifact × List Object × Artifact × Artifact) ⊕
  ((Artifact × Revision × Artifact × Artifact) ⊕
  ((Artifact × List Nat × Artifact) ⊕
  (Artifact × Artifact)))))

def cutStream : StreamCodec Cut :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.product revisionStream (StreamCodec.product stringStream StreamCodec.nat))
      (StreamCodec.sum (StreamCodec.product (StreamCodec.list targetStream) (StreamCodec.option familyStream))
        (StreamCodec.sum (StreamCodec.product artifactStream (StreamCodec.product
              (StreamCodec.list objectStream) (StreamCodec.product artifactStream artifactStream)))
          (StreamCodec.sum (StreamCodec.product artifactStream (StreamCodec.product revisionStream
                (StreamCodec.product artifactStream artifactStream)))
            (StreamCodec.sum (StreamCodec.product artifactStream (StreamCodec.product
                  (StreamCodec.list StreamCodec.nat) artifactStream))
              (StreamCodec.product artifactStream artifactStream))))))
    (fun (v : Cut) => (match v with
      | .observe r p c => .inl (r, p, c)
      | .invoke ts f => .inr (.inl (ts, f))
      | .reserve c fp l o => .inr (.inr (.inl (c, fp, l, o)))
      | .install c p e o => .inr (.inr (.inr (.inl (c, p, e, o))))
      | .release r a l => .inr (.inr (.inr (.inr (.inl (r, a, l)))))
      | .retire o e => .inr (.inr (.inr (.inr (.inr (o, e))))) : CutWire))
    (fun (w : CutWire) => match w with
      | .inl (r, p, c) => .observe r p c
      | .inr (.inl (ts, f)) => .invoke ts f
      | .inr (.inr (.inl (c, fp, l, o))) => .reserve c fp l o
      | .inr (.inr (.inr (.inl (c, p, e, o)))) => .install c p e o
      | .inr (.inr (.inr (.inr (.inl (r, a, l))))) => .release r a l
      | .inr (.inr (.inr (.inr (.inr (o, e))))) => .retire o e)
    (by intro v; cases v <;> rfl)

def intentStream : StreamCodec Intent :=
  StreamCodec.xmap (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat cutStream))
    (fun v => (v.salt, v.actor, v.cut)) (fun w => ⟨w.1, w.2.1, w.2.2⟩)
    (by intro v; cases v; rfl)

/-! ## Frames and codec -/

/-- `DREGG/CONTRACT/INTENT/v1` -/
def intentFrame : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 67, 79, 78, 84, 82, 65, 67, 84, 47, 73, 78, 84, 69, 78, 84, 47, 118, 49]
/-- `DREGG/CONTRACT/INTENT-ID/v1`: prefixes the bytes the client hashes into an `InvocationId`. -/
def intentIdFrame : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 67, 79, 78, 84, 82, 65, 67, 84, 47, 73, 78, 84, 69, 78, 84, 45, 73, 68, 47, 118, 49]

theorem intent_frames_spell :
    intentFrame = "DREGG/CONTRACT/INTENT/v1".toUTF8.toList ∧
    intentIdFrame = "DREGG/CONTRACT/INTENT-ID/v1".toUTF8.toList := by
  decide +kernel

def intentCodec : LawfulCodec Intent := framed intentFrame intentStream

/-- The bytes the client hashes (SHA-256) into the `InvocationId` of this request. -/
def intentIdPreimage (i : Intent) : List UInt8 := intentIdFrame ++ intentCodec.encode i

theorem intent_roundtrip (i : Intent) : intentCodec.decode (intentCodec.encode i) = some i :=
  intentCodec.decode_encode i

theorem intent_encode_injective : Function.Injective intentCodec.encode :=
  Minidregg.Kernel.Contracts.framed_encode_injective intentFrame intentStream

/-- Two distinct requests never share an `InvocationId` preimage. -/
theorem intentIdPreimage_injective : Function.Injective intentIdPreimage := by
  intro a b same
  exact intent_encode_injective (List.append_cancel_left same)

/-- A small concrete intent, for the layout pin and the non-vacuity check below. -/
def retireExample : Intent :=
  ⟨List.replicate 16 0, 7, .retire ⟨List.replicate 32 1, 3, "x"⟩ ⟨List.replicate 32 2, 4, "y"⟩⟩

/-- Non-vacuity of `intentIdPreimage_injective`: changing the salt or the actor changes the
preimage. -/
theorem salt_and_actor_change_the_name :
    intentIdPreimage retireExample ≠ intentIdPreimage { retireExample with salt := 1 :: List.replicate 15 0 } ∧
    intentIdPreimage retireExample ≠ intentIdPreimage { retireExample with actor := 8 } := by
  constructor <;> intro h <;> have := intentIdPreimage_injective h <;> cases this

/-- The layout, pinned: frame, salt (`16` then `255`), actor (`7` `255`), cut tag `1 1 1 1 1`,
then two artifacts (digest as a count-prefixed byte string, length, format as a scalar list). -/
theorem retire_example_bytes :
    intentCodec.encode retireExample =
      intentFrame ++
      [16, 255] ++ List.replicate 16 0 ++ [7, 255] ++ [1, 1, 1, 1, 1] ++
      ([32, 255] ++ List.replicate 32 1 ++ [3, 255] ++ [1, 255, 120, 255]) ++
      ([32, 255] ++ List.replicate 32 2 ++ [4, 255] ++ [1, 255, 121, 255]) := by
  decide +kernel

/-- An intent's bytes never decode under any identity frame of `Kernel.Contracts.Identities`:
the first 18 bytes already separate them. -/
theorem intent_frame_separates_identities (i : Intent) :
    framedDecode Minidregg.Kernel.Contracts.objectRefFrame Minidregg.Kernel.Contracts.objectRefStream
      (intentCodec.encode i) = none ∧
    framedDecode Minidregg.Kernel.Contracts.revisionRefFrame Minidregg.Kernel.Contracts.revisionRefStream
      (intentCodec.encode i) = none ∧
    framedDecode Minidregg.Kernel.Contracts.invocationFrame Minidregg.Kernel.Contracts.invocationIdStream
      (intentCodec.encode i) = none ∧
    framedDecode Minidregg.Kernel.Contracts.artifactRefFrame Minidregg.Kernel.Contracts.artifactRefStream
      (intentCodec.encode i) = none := by
  have enc : intentCodec.encode i = intentFrame ++ intentStream.encode i := rfl
  rw [enc]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    exact Minidregg.Kernel.Contracts.framedDecode_refuses_other_frame _ intentFrame _ _ 18
      (by decide) (by decide) (by decide)

/-! ## Canonical JSON (the payload) -/

open Lean (Json JsonNumber)

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Escapes exactly as `serde_json` and `JSON.stringify`: `"` `\` and the controls below 0x20
(`\b \f \n \r \t` short, the rest `\u00xx` lowercase); everything else raw UTF-8. -/
def escapeChar (c : Char) : String :=
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if c.toNat = 8 then "\\b"
  else if c.toNat = 12 then "\\f"
  else if c.toNat = 10 then "\\n"
  else if c.toNat = 13 then "\\r"
  else if c.toNat = 9 then "\\t"
  else if c.toNat < 32 then "\\u00" ++ (hexDigit (c.toNat / 16)).toString ++ (hexDigit (c.toNat % 16)).toString
  else c.toString

def quote (s : String) : String := "\"" ++ String.join (s.toList.map escapeChar) ++ "\""

/-- The exact integer a JSON number denotes, if it denotes one of magnitude at most `2^53`:
`mantissa / 10^exponent` when that division is exact. The SPELLING does not matter (`100`, `100.0`,
`1e2` are the same number), the VALUE does; a fraction is refused, never rounded. The exponent is
bounded by the mantissa's digit count before any power is formed, so a hostile `1e-99999999999`
costs nothing. (`-0` is `0`.) -/
def integerValue? (n : JsonNumber) : Option Int :=
  if n.mantissa = 0 then some 0
  else if n.exponent > (toString n.mantissa.natAbs).length then none
  else
    let scale : Int := (10 : Int) ^ n.exponent
    if n.mantissa % scale = 0 ∧ (n.mantissa / scale).natAbs ≤ 2 ^ 53 then some (n.mantissa / scale) else none

/-- The number rule on worked cases: the spelling is irrelevant, the value decides, a fraction is
refused, the 2^53 bound is exact, and a zero mantissa is `0` whatever its sign or scale. -/
theorem integerValue_cases :
    integerValue? ⟨100, 0⟩ = some 100 ∧ integerValue? ⟨1000, 1⟩ = some 100 ∧
    integerValue? ⟨15, 1⟩ = none ∧ integerValue? ⟨-50, 0⟩ = some (-50) ∧
    integerValue? ⟨0, 7⟩ = some 0 ∧ integerValue? ⟨1, 400000⟩ = none ∧
    integerValue? ⟨9007199254740992, 0⟩ = some 9007199254740992 ∧
    integerValue? ⟨9007199254740993, 0⟩ = none ∧
    integerValue? ⟨900719925474099200, 2⟩ = some 9007199254740992 := by
  decide

/-- Sorted keys (code-point order, which is UTF-8 byte order), no whitespace, integers of
magnitude at most 2^53 only, written as plain integers. -/
partial def canonText : Json → Except String String
  | .null => pure "null"
  | .bool b => pure (toString b)
  | .num n =>
      match integerValue? n with
      | some v => pure (toString v)
      | none => throw "canonical JSON admits only integers of magnitude ≤ 2^53; use a decimal string"
  | .str s => pure (quote s)
  | .arr a => do
      let parts ← a.toList.mapM canonText
      pure ("[" ++ ",".intercalate parts ++ "]")
  | .obj o => do
      let kvs := o.toList
      let parts ← kvs.mapM fun (kv : String × Json) => do
        pure (quote kv.1 ++ ":" ++ (← canonText kv.2))
      pure ("{" ++ ",".intercalate parts ++ "}")

/-! ## The spelling: strict JSON in, intent out -/

/-- A canonical decimal natural: ASCII digits, no leading zero except `0` itself. -/
def isDecimal (s : String) : Bool :=
  !s.isEmpty && s.all Char.isDigit && (s.length == 1 || s.front != '0')

private def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else none

private def unhexChars : List Char → Except String (List UInt8)
  | a :: b :: rest =>
      match hexVal? a, hexVal? b with
      | some x, some y => do pure (UInt8.ofNat (x * 16 + y) :: (← unhexChars rest))
      | _, _ => throw "hex must be canonical lowercase"
  | [] => pure []
  | [_] => throw "hex has odd length"

def unhex (s : String) : Except String (List UInt8) := unhexChars s.toList

def hexOf (bytes : List UInt8) : String :=
  String.join (bytes.map fun b => (hexDigit (b.toNat / 16)).toString ++ (hexDigit (b.toNat % 16)).toString)

private def str (j : Json) : Except String String := j.getStr?

private def dec (j : Json) : Except String Nat := do
  let s ← str j
  if isDecimal s then
    match s.toNat? with
    | some n => pure n
    | none => throw s!"{s.quote} is not a canonical decimal"
  else throw s!"{s.quote} is not a canonical decimal"

private def fixedHex (j : Json) (n : Nat) (what : String) : Except String (List UInt8) := do
  let b ← unhex (← str j)
  if b.length = n then pure b else throw s!"{what} must be {n} bytes"

/-- The value has exactly these fields. -/
private def exact (j : Json) (keys : List String) : Except String Unit := do
  let o ← j.getObj?
  if o.size = keys.length ∧ keys.all (fun k => o.contains k) then pure ()
  else throw s!"expected exactly the fields {keys}"

private def get (j : Json) (k : String) : Except String Json := j.getObjVal? k

private def list {α : Type} (j : Json) (f : Json → Except String α) : Except String (List α) := do
  (← j.getArr?).toList.mapM f

private def parseObject (j : Json) : Except String Object := do
  exact j ["id", "domain", "kind"]
  pure ⟨← dec (← get j "id"), ← dec (← get j "domain"), ← str (← get j "kind")⟩

private def parseRevision (j : Json) : Except String Revision := do
  exact j ["object", "root"]
  pure ⟨← parseObject (← get j "object"), ← dec (← get j "root")⟩

private def parseArtifact (j : Json) : Except String Artifact := do
  exact j ["sha256", "length", "format"]
  let length ← match ← get j "length" with
    | .num n =>
        match integerValue? n with
        | some v => if 0 ≤ v then pure v.toNat else throw "length must be a natural number"
        | none => throw "length must be an integer ≤ 2^53"
    | _ => throw "length must be a number"
  pure ⟨← fixedHex (← get j "sha256") 32 "sha256", length, ← str (← get j "format")⟩

private def parseRoute (s : String) : Except String Route :=
  match s with
  | "ordinary" => pure .ordinary
  | "objectiveMethod" => pure .objectiveMethod
  | "activityDispatch" => pure .activityDispatch
  | "roomRelease" => pure .roomRelease
  | "roomPublish" => pure .roomPublish
  | _ => throw s!"unknown invocation family route {s.quote}"

private def parseFamily (j : Json) : Except String (Option Family) :=
  match j with
  | .null => pure none
  | f => do
      exact f ["route", "context"]
      pure (some ⟨← parseRoute (← str (← get f "route")), ← unhex (← str (← get f "context"))⟩)

private def parseTarget (j : Json) : Except String Target := do
  exact j ["revision", "capability", "observeCapability", "schemaVersion", "payload"]
  pure ⟨← parseRevision (← get j "revision"), ← dec (← get j "capability"),
    ← dec (← get j "observeCapability"), ← dec (← get j "schemaVersion"),
    ← canonText (← get j "payload")⟩

def parseIntent (j : Json) : Except String Intent := do
  let cut ← str (← get j "cut")
  let fields : List String ←
    match cut with
    | "observe" => pure ["actor", "salt", "cut", "resource", "projection", "capability"]
    | "invoke" => pure ["actor", "salt", "cut", "targets", "family"]
    | "reserve" => pure ["actor", "salt", "cut", "candidate", "footprint", "law", "obligation"]
    | "install" => pure ["actor", "salt", "cut", "candidate", "preimage", "effects", "obligation"]
    | "release" => pure ["actor", "salt", "cut", "result", "audience", "law"]
    | "retire" => pure ["actor", "salt", "cut", "obligation", "evidence"]
    | _ => throw s!"unknown cut {cut.quote}"
  exact j fields
  let salt ← fixedHex (← get j "salt") 16 "salt"
  let actor ← dec (← get j "actor")
  let body : Cut ←
    match cut with
    | "observe" => pure (.observe (← parseRevision (← get j "resource")) (← str (← get j "projection"))
        (← dec (← get j "capability")))
    | "invoke" => do
        let targets ← list (← get j "targets") parseTarget
        if targets.isEmpty then throw "an invocation names at least one target"
        pure (.invoke targets (← parseFamily (← get j "family")))
    | "reserve" => pure (.reserve (← parseArtifact (← get j "candidate"))
        (← list (← get j "footprint") parseObject) (← parseArtifact (← get j "law"))
        (← parseArtifact (← get j "obligation")))
    | "install" => pure (.install (← parseArtifact (← get j "candidate"))
        (← parseRevision (← get j "preimage")) (← parseArtifact (← get j "effects"))
        (← parseArtifact (← get j "obligation")))
    | "release" => pure (.release (← parseArtifact (← get j "result"))
        (← list (← get j "audience") dec) (← parseArtifact (← get j "law")))
    | _ => pure (.retire (← parseArtifact (← get j "obligation")) (← parseArtifact (← get j "evidence")))
  pure ⟨salt, actor, body⟩

/-- Spelling text → canonical bytes, or the named refusal. -/
def encodeSpelling (text : String) : Except String (List UInt8) := do
  let j ← Json.parse text
  pure (intentCodec.encode (← parseIntent j))

def idPreimageSpelling (text : String) : Except String (List UInt8) := do
  let j ← Json.parse text
  pure (intentIdPreimage (← parseIntent j))

/-! ## Byte entry points (`@[export]`)

Reply: one status byte — `1` then the bytes, or `0` then a UTF-8 refusal. A reply is never empty,
so a refusal cannot be mistaken for an empty encoding. -/

def tagged : Except String (List UInt8) → ByteArray
  | .ok b => ⟨(1 :: b).toArray⟩
  | .error e => ⟨(0 :: e.toUTF8.toList).toArray⟩

def viaSpelling (f : String → Except String (List UInt8)) (spelling : ByteArray) : ByteArray :=
  match String.fromUTF8? spelling with
  | some s => tagged (f s)
  | none => tagged (.error "intent spelling is not UTF-8")

/-- Intent spelling (JSON, UTF-8) → `1 ‖ intentCodec.encode`, or `0 ‖ refusal`. -/
@[export minidregg_intent_encode]
def intentEncodeBytes (spelling : ByteArray) : ByteArray := viaSpelling encodeSpelling spelling

/-- Intent spelling (JSON, UTF-8) → `1 ‖ intentIdPreimage`, or `0 ‖ refusal`. -/
@[export minidregg_intent_id_preimage]
def intentIdPreimageBytes (spelling : ByteArray) : ByteArray := viaSpelling idPreimageSpelling spelling

#assert_axioms intent_frames_spell
#assert_axioms intent_roundtrip
#assert_axioms intent_encode_injective
#assert_axioms intentIdPreimage_injective
#assert_axioms salt_and_actor_change_the_name
#assert_axioms retire_example_bytes
#assert_axioms integerValue_cases
#assert_axioms intent_frame_separates_identities

end Minidregg.Kernel.Contracts.Intents
