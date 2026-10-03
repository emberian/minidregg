/- Shared clear-reference invocation data below native transaction modules.
Only independently selected current observations may populate this vector.
The wire is canonical native bytes; the source receives two Data byte lists,
(authored arguments, current admitted observation vector), as an affine pair.
No host map, file lookup, foreign IO or ambient authority is available. -/
import Compiler.BendRunCore

namespace Minidregg.Compiler.BendNativeInput
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

structure Observation where
  resource : Nat
  root : Digest
  physicalKind : Nat
  resourceBytes : List UInt8
  accountBytes : List UInt8
  deriving DecidableEq, Repr

def observationStream : StreamCodec Observation :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product bytesStream bytesStream))))
    (fun o => (o.resource,o.root,o.physicalKind,o.resourceBytes,o.accountBytes))
    (fun o => ⟨o.1,o.2.1,o.2.2.1,o.2.2.2.1,o.2.2.2.2⟩) (by intro o; cases o; rfl)

def observationFrame : List UInt8 := "DREGG/BEND/CURRENT-OBSERVATIONS/v1".toUTF8.toList
def encodeObservations (observations : List Observation) : List UInt8 :=
  observationFrame ++ (StreamCodec.list observationStream).encode observations

def codecId : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.NATIVE-INPUT-PAIR/v1".toUTF8.toList
    "affine-pair(authored-byte-list,current-observation-byte-list);strict-native-canonical-wire;scope-narrowed;original-roots".toUTF8.toList).digest

/-- The schema/source-library is public. No secret argument is compiled into
public code ROM; this is the clear reference invocation term only. Private
backends must inject qualified input into a fixed public template instead. -/
def term (arguments : List UInt8) (observations : List Observation) : BendTT.Term :=
  .Tup .Q1 (BendSourceRepresentation.bytesTerm arguments)
    (BendSourceRepresentation.bytesTerm (encodeObservations observations))

/-- Host-derived invocation actor and replay coordinate. These are canonical
binary Data; a source author cannot replace them with a declared actor argument. -/
structure Context where
  subject : SubjectId
  nonce : Nat
  deriving DecidableEq, Repr

def contextFrame : List UInt8 := "DREGG/BEND/CURRENT-CONTEXT/v2".toUTF8.toList
def contextStream : StreamCodec (Context × List Observation) :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.list observationStream)))
    (fun value => (value.1.subject,value.1.nonce,value.2))
    (fun value => (⟨value.1,value.2.1⟩,value.2.2))
    (by rintro ⟨⟨subject,nonce⟩,observations⟩; rfl)
def encodeContext (context : Context) (observations : List Observation) : List UInt8 :=
  contextFrame ++ contextStream.encode (context,observations)
def codecV2 : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.NATIVE-INPUT-PAIR/v2".toUTF8.toList
    "affine-pair(authored-byte-list,current-context-byte-list);native-subject-and-nonce;scope-narrowed-observations;original-roots;binary-identities".toUTF8.toList).digest
def contextTerm (context : Context) (arguments : List UInt8)
    (observations : List Observation) : BendTT.Term :=
  .Tup .Q1 (BendSourceRepresentation.bytesTerm arguments)
    (BendSourceRepresentation.bytesTerm (encodeContext context observations))

end Minidregg.Compiler.BendNativeInput
