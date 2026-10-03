/- Exact selected immutable source to pure reference run, below transaction
and Plan modules. Current observations supplied here must be independently
constructed by the native receiver; this module is not an authority token.
Native policy/effect admission additionally consumes the complete result via
its pinned typed output decoder and exact current signed capacity envelope. -/
import Kernel.BendArtifactSource
import Compiler.BendExecutionClaim
import Compiler.BendNativeInput

namespace Minidregg.Kernel.BendNativeRun
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.BendTT
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

def evaluatorId : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.CHECKED-SOURCE-EVALUATOR/v1".toUTF8.toList
    "exact-pinned-book;actual-typed-closed-live-input;Eval-Walk-reference;capacity-refusal;complete-typed-output;no-ambient-IO;no-private-fallback".toUTF8.toList).digest

/-- Source mathematics and evaluation are independent of physical BFV/JS/C arithmetic.
Only a separately checked refinement may realize this exact source family. -/
def sourceSemantics : String := "bendtt-eval-walk-947db722-v1"
def sourceArithmetic : String := "bendtt-structural-nat-exact-v1"

def chargeId : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.CHARGE/v1".toUTF8.toList
    (BendPrivateCapacity.contract ++ "reference-source-work;exact-complete-native-write-and-dependency-usage".toUTF8.toList)).digest

def methodId (a : BendWorldProgramCodec.Artifact) : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.METHOD/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product PolicyRecordCodec.stringStream
      (StreamCodec.product PolicyRecordCodec.stringStream digestStream)))).encode
      (BendWorldSource.packageId a.source,a.source.entryModule,a.source.entryDefinition,a.entry,a.plan))).digest

structure Checked (artifact : BendWorldProgramCodec.Artifact)
    (claim : BendExecutionClaim.Claim) (observations : List BendNativeInput.Observation) where
  private mk ::
  core : BendCoreAdmission.Checked
  coreBytes : core.bytes = artifact.book
  entry : BendCoreAdmission.Entry core
  entryName : entry.name = artifact.entry
  quantity : Quan
  inputType : BendTT.Term
  outputBody : BendTT.Term
  interfaceExact : entry.definition.T = .All quantity inputType outputBody
  input : BendTT.Term
  inputExact : input = BendNativeInput.term claim.arguments observations
  limits : BendRunCore.Limits
  source : BendRunCore.Checked core (.App quantity (.Ref entry.name) input)
    (Term.inst outputBody input) limits

inductive Refusal where
  | artifactIdentity | methodIdentity | evaluator | inputCodec | outputCodec | core | entry | interface
  | charge | semantics | arithmetic | bounds | source (reason : BendRunCore.Refusal)
  deriving DecidableEq, Repr

/-- Bounds are selected from the accepted artifact profile, never supplied as a
new faster profile on failure. Full declaration/input/effect/charge authority
and codec registration remain native receiving checks. -/
def check (artifact : BendWorldProgramCodec.Artifact) (claim : BendExecutionClaim.Claim)
    (observations : List BendNativeInput.Observation) :
    Except Refusal (Checked artifact claim observations) := do
  if claim.artifact != BendWorldProgramCodec.artifactId artifact then throw .artifactIdentity
  if claim.method != methodId artifact then throw .methodIdentity
  if artifact.profile.evaluator != evaluatorId then throw .evaluator
  if artifact.profile.charge != chargeId then throw .charge
  if artifact.profile.semantics != sourceSemantics then throw .semantics
  if artifact.profile.arithmetic != sourceArithmetic then throw .arithmetic
  if claim.argumentCodec != artifact.profile.inputCodec ||
      claim.argumentCodec != BendNativeInput.codecId then throw .inputCodec
  if claim.outputCodec != artifact.profile.outputCodec then throw .outputCodec
  let core ← (BendCoreAdmission.admit artifact.book).mapError (fun _ => Refusal.core)
  let entry ← (BendCoreAdmission.entry core artifact.entry).mapError (fun _ => Refusal.entry)
  let .All quantity inputType outputBody := entry.definition.T | throw .interface
  let some sourceSteps := artifact.profile.bounds[7]? | throw .bounds
  let some outputSize := artifact.profile.bounds[3]? | throw .bounds
  let limits : BendRunCore.Limits := ⟨BendTT.FUEL, outputSize + 1, sourceSteps, outputSize⟩
  let input := BendNativeInput.term claim.arguments observations
  let source ← (BendRunCore.check core (.App quantity (.Ref entry.name) input)
    (Term.inst outputBody input) limits).mapError Refusal.source
  -- Exact interface/entry/book equalities are retained by a proof-producing
  -- checked constructor. The equations are checked, not inferred from strings.
  if bytes : core.bytes = artifact.book then
    if named : entry.name = artifact.entry then
      if shape : entry.definition.T = .All quantity inputType outputBody then
        pure ⟨core,bytes,entry,named,quantity,inputType,outputBody,shape,input,rfl,limits,source⟩
      else throw .interface
    else throw .entry
  else throw .core

/-- V2 native receiving binds actor/nonce from the signed command, without
changing the preserved V1 pure reference API or falling back between codecs. -/
structure ContextChecked (artifact : BendWorldProgramCodec.Artifact)
    (claim : BendExecutionClaim.Claim) (context : BendNativeInput.Context) (observations : List BendNativeInput.Observation) where
  private mk ::
  core : BendCoreAdmission.Checked
  coreBytes : core.bytes = artifact.book
  entry : BendCoreAdmission.Entry core
  entryName : entry.name = artifact.entry
  quantity : Quan
  inputType : BendTT.Term
  outputBody : BendTT.Term
  interfaceExact : entry.definition.T = .All quantity inputType outputBody
  input : BendTT.Term
  inputExact : input = BendNativeInput.contextTerm context claim.arguments observations
  limits : BendRunCore.Limits
  source : BendRunCore.Checked core (.App quantity (.Ref entry.name) input)
    (Term.inst outputBody input) limits


def checkContext (artifact : BendWorldProgramCodec.Artifact) (claim : BendExecutionClaim.Claim)
    (context : BendNativeInput.Context) (observations : List BendNativeInput.Observation) :
    Except Refusal (ContextChecked artifact claim context observations) := do
  if claim.artifact != BendWorldProgramCodec.artifactId artifact then throw .artifactIdentity
  if claim.method != methodId artifact then throw .methodIdentity
  if artifact.profile.evaluator != evaluatorId then throw .evaluator
  if artifact.profile.charge != chargeId then throw .charge
  if artifact.profile.semantics != sourceSemantics then throw .semantics
  if artifact.profile.arithmetic != sourceArithmetic then throw .arithmetic
  if claim.argumentCodec != artifact.profile.inputCodec ||
      claim.argumentCodec != BendNativeInput.codecV2 then throw .inputCodec
  if claim.outputCodec != artifact.profile.outputCodec then throw .outputCodec
  let core ← (BendCoreAdmission.admit artifact.book).mapError (fun _ => Refusal.core)
  let entry ← (BendCoreAdmission.entry core artifact.entry).mapError (fun _ => Refusal.entry)
  let .All quantity inputType outputBody := entry.definition.T | throw .interface
  let some sourceSteps := artifact.profile.bounds[7]? | throw .bounds
  let some outputSize := artifact.profile.bounds[3]? | throw .bounds
  let limits : BendRunCore.Limits := ⟨BendTT.FUEL, outputSize + 1, sourceSteps, outputSize⟩
  let input := BendNativeInput.contextTerm context claim.arguments observations
  let source ← (BendRunCore.check core (.App quantity (.Ref entry.name) input)
    (Term.inst outputBody input) limits).mapError Refusal.source
  -- Exact interface/entry/book equalities are retained by a proof-producing
  -- checked constructor. The equations are checked, not inferred from strings.
  if bytes : core.bytes = artifact.book then
    if named : entry.name = artifact.entry then
      if shape : entry.definition.T = .All quantity inputType outputBody then
        pure ⟨core,bytes,entry,named,quantity,inputType,outputBody,shape,input,rfl,limits,source⟩
      else throw .interface
    else throw .entry
  else throw .core

end Minidregg.Kernel.BendNativeRun
