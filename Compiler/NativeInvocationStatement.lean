/- Common explicit signed invocation statement, edition 1. All routes bind the
same canonical domain/semantics/route/context/body tuple. BODY is the complete
unsigned invocation body, excluding this framing and its signatures; signatures
must bind these statement bytes through the actual authorization request.
This codec does not itself change a legacy profile or grant any admission.
-/
import Compiler.Tower256ConcreteBackend
import Compiler.ResourceBirthCodec

namespace Minidregg.Compiler.NativeInvocationStatement
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler.Tower256ConcreteBackend
set_option autoImplicit false

inductive Route
  | ordinary
  | objectiveMethod
  | activityDispatch
  deriving DecidableEq, BEq, Repr

def routeStream : StreamCodec Route where
  encode
    | .ordinary => [0]
    | .objectiveMethod => [1]
    | .activityDispatch => [2]
  decodePrefix
    | 0 :: rest => some (.ordinary,rest)
    | 1 :: rest => some (.objectiveMethod,rest)
    | 2 :: rest => some (.activityDispatch,rest)
    | _ => none
  decodePrefix_encode := by intro route suffix; cases route <;> rfl

structure Statement where
  domain : Digest
  semantics : Digest
  route : Route
  contextBytes : List UInt8
  bodyBytes : List UInt8
  deriving DecidableEq

def stream : StreamCodec Statement :=
  StreamCodec.xmap (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product routeStream (StreamCodec.product bytesStream bytesStream))))
    (fun statement => (statement.domain,statement.semantics,statement.route,
      statement.contextBytes,statement.bodyBytes))
    (fun (d,s,r,c,b) => ⟨d,s,r,c,b⟩) (by intro statement; cases statement; rfl)

/-- The version is part of the exact signed bytes, never an ambient hint. -/
def version : Nat := 1
def frame : List UInt8 := "DREGG/NATIVE/INVOCATION-STATEMENT".toUTF8.toList ++ [1]

def rawCodec : LawfulCodec Statement where
  encode statement := frame ++ stream.encode statement
  decode bytes := if bytes.take frame.length = frame then
    stream.toLawful.decode (bytes.drop frame.length) else none
  decode_encode := by
    intro statement
    have exact := stream.toLawful.decode_encode statement
    change stream.toLawful.decode (stream.encode statement) = some statement at exact
    simp [exact]

/-- Full consumption and exact re-encoding refuse alternate wire spellings. -/
def codec : LawfulCodec Statement := ResourceBirthCodec.strictCodec rawCodec
abbrev encode := codec.encode
abbrev decode := codec.decode

@[simp] theorem decode_encode (statement : Statement) :
    decode (encode statement) = some statement := codec.decode_encode statement

theorem encode_injective {left right : Statement} (same : encode left = encode right) :
    left = right := by
  have decoded := congrArg decode same
  simpa only [decode_encode,Option.some.injEq] using decoded

theorem decoded_canonical {bytes : List UInt8} {statement : Statement}
    (accepted : decode bytes = some statement) : encode statement = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCodec accepted

/-- Every route, the whole context and the whole unsigned body are bound by
canonical encoding; no digest collision claim is substituted for this fact. -/
theorem same_bytes_bind_all {left right : Statement} (same : encode left = encode right) :
    left.domain = right.domain ∧ left.semantics = right.semantics ∧
    left.route = right.route ∧ left.contextBytes = right.contextBytes ∧
    left.bodyBytes = right.bodyBytes := by
  cases encode_injective same
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem dispatch_not_ordinary (domain semantics : Digest) (context body : List UInt8)
    (other : Statement) (ordinary : other.route = .ordinary) :
    encode ⟨domain,semantics,.activityDispatch,context,body⟩ ≠ encode other := by
  intro same
  have route := (same_bytes_bind_all same).2.2.1
  rw [ordinary] at route
  cases route

#assert_axioms decode_encode
#assert_axioms encode_injective
#assert_axioms decoded_canonical
#assert_axioms same_bytes_bind_all
#assert_axioms dispatch_not_ordinary
end Minidregg.Compiler.NativeInvocationStatement
