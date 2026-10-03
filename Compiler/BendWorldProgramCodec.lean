/- Language-neutral executable-record/source-provenance join. Existing program
identities and RunClaims are retained verbatim. This additive artifact pins the
semantics, resource policy and source closure needed by a future Bend evaluator;
it does not register an evaluator or certify compiler refinement. -/
import Compiler.BendWorldSource

namespace Minidregg.Compiler.BendWorldProgramCodec
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

structure Profile where
  upstream : String
  /-- Checker, elaborator, kernel, compiler and base bytes, in that exact order. -/
  components : List Digest
  evaluator : Digest
  semantics : String
  arithmetic : String
  /-- Canonical charge semantics; physical backend instruction count is not gas. -/
  charge : Digest
  inputCodec : Digest
  outputCodec : Digest
  effectAbi : Digest
  /-- Public/private schema, audience/release policy and hiding bounds. -/
  disclosure : Digest
  /-- Code, Book, labels, data, heap, environment, frames, steps, output bytes. -/
  bounds : List Nat
  deriving DecidableEq, Repr

structure Artifact where
  source : BendWorldSource.Package
  profile : Profile
  /-- Exact elaborated Book bytes, not a Boolean saying "checked". -/
  book : List UInt8
  /-- Actual emitted/parsed core entry name, distinct from surface source names. -/
  entry : String
  /-- Bound operation DAG/grades, including key/release custody and proof joins.
  This is separate from semantic identity; no exclusive backend mode is chosen. -/
  plan : Digest
  backend : String
  /-- The current evaluator-generic immutable program record. -/
  program : NockProgramCodec.Program
  deriving DecidableEq, Repr

def profileStream : StreamCodec Profile :=
  StreamCodec.xmap
    (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product (StreamCodec.list digestStream)
    (StreamCodec.product digestStream
    (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product digestStream
    (StreamCodec.product digestStream
    (StreamCodec.product digestStream
    (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.list StreamCodec.nat)))))))))))
    (fun p => (p.upstream, p.components, p.evaluator, p.semantics, p.arithmetic,
      p.charge, p.inputCodec, p.outputCodec, p.effectAbi, p.disclosure, p.bounds))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1,
      p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2⟩)
    (by intro p; cases p; rfl)

def artifactStream : StreamCodec Artifact :=
  StreamCodec.xmap (StreamCodec.product BendWorldSource.packageStream
    (StreamCodec.product profileStream (StreamCodec.product bytesStream
      (StreamCodec.product PolicyRecordCodec.stringStream
        (StreamCodec.product digestStream
          (StreamCodec.product PolicyRecordCodec.stringStream NockProgramCodec.programStream))))))
    (fun a => (a.source, a.profile, a.book, a.entry, a.plan, a.backend, a.program))
    (fun a => ⟨a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1,
      a.2.2.2.2.2.1, a.2.2.2.2.2.2⟩)
    (by intro a; cases a; rfl)

def frame : List UInt8 := "DREGG/BEND/ARTIFACT/v1".toUTF8.toList
def encode (a : Artifact) : List UInt8 := frame ++ artifactStream.encode a
def decode (bytes : List UInt8) : Option Artifact :=
  NockProgramCodec.framedDecode frame artifactStream bytes

def profileId (p : Profile) : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.PROFILE/v1".toUTF8.toList
    (profileStream.encode p)).digest

def artifactId (a : Artifact) : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.ARTIFACT/v1".toUTF8.toList (encode a)).digest

/-- Exact checked core/entry and canonical ABI/numeric/charge meaning, independent
of an implementation plan. Refinement and actual Book.check are not implied by
computing this identifier. Effect/reveal authority is never minted by this ID. -/
def semanticId (a : Artifact) : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.SEMANTIC/v1".toUTF8.toList
    ((StreamCodec.product bytesStream
      (StreamCodec.product PolicyRecordCodec.stringStream
        (StreamCodec.product PolicyRecordCodec.stringStream
          (StreamCodec.product PolicyRecordCodec.stringStream
            (StreamCodec.list digestStream))))).encode
      (a.book, a.entry, a.profile.semantics, a.profile.arithmetic,
        [a.profile.evaluator, a.profile.charge, a.profile.inputCodec, a.profile.outputCodec,
          a.profile.effectAbi]))).digest

/-- The ID existing method tables, receipt provenance and RunClaims already name.
Adding source inspection must never silently reidentify historical programs. -/
def executionProgramId (a : Artifact) : Digest := NockProgramCodec.programId a.program

/-- Structural validation only. Exact source parsing, Book.check, backend
refinement and receiving authority are independent checks, not manifest flags. -/
def wellFormed (a : Artifact) : Bool :=
  BendWorldSource.wellFormed a.source &&
  decide (a.profile.upstream = BendWorldSource.upstreamPin ∧
    a.profile.components.length = 5 ∧ a.profile.bounds.length = 9 ∧
    a.program.evaluator = a.profile.evaluator) &&
  BendWorldSource.nameValid a.profile.semantics &&
  BendWorldSource.nameValid a.profile.arithmetic &&
  BendWorldSource.nameValid a.entry &&
  BendWorldSource.nameValid a.backend &&
  a.profile.bounds.all (fun n => decide (0 < n)) &&
  match a.profile.bounds[7]? with
  | none => false
  | some steps => decide (a.program.abi.fuel ≤ steps)

theorem decode_canonical {bytes : List UInt8} {a : Artifact}
    (h : decode bytes = some a) : encode a = bytes :=
  NockProgramCodec.framedDecode_canonical h

theorem roundtrip (a : Artifact) : decode (encode a) = some a :=
  NockProgramCodec.framedDecode_encode frame artifactStream a

theorem legacy_program_identity (a : Artifact) :
    executionProgramId a = NockProgramCodec.programId a.program := rfl

/-- Changing source/backend provenance cannot rewrite an existing run's program ID. -/
theorem source_update_preserves_program_id (a : Artifact)
    (source : BendWorldSource.Package) (backend : String) :
    executionProgramId { a with source := source, backend := backend } =
      executionProgramId a := rfl

theorem plan_update_preserves_semantics (a : Artifact) (plan : Digest) (backend : String) :
    semanticId { a with plan := plan, backend := backend } = semanticId a := rfl

end Minidregg.Compiler.BendWorldProgramCodec
