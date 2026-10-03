import Compiler.GenericSimplexIO
import Compiler.PrivateSuccessorCustodyCodec
import Kernel.JointReservation
namespace Minidregg.Kernel.JointSimplexBinding
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Kernel.JointInvocationCandidate
open Minidregg.Kernel.JointDecisionRecovery
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false
abbrev Custody := PrivateSuccessorCustody.Descriptor
abbrev PrivatePlan := Plan Custody
def exactCandidate (plan : PrivatePlan) : List UInt8 :=
  (candidateStream PrivateSuccessorCustodyCodec.descriptorStream).encode plan.candidate
def slotInstance (plan : PrivatePlan) (index : Nat) : List UInt8 :=
  (StreamCodec.product bytesStream StreamCodec.nat).encode (exactCandidate plan,index)
/-- Context roster is source deployment data, never chosen from the certificate. -/
def slotContext (plan : PrivatePlan) (i : Fin plan.candidate.participants.length)
    (config : GenericSimplex.Config) (publicKeys : List (List UInt8)) : Context :=
  ⟨digestStream.encode plan.candidate.participants[i].domain,
    plan.candidate.participants[i].epoch,slotInstance plan i.val,config,publicKeys⟩
def decisionBytes (plan : PrivatePlan) (index : Nat) (yes : Bool) : List UInt8 :=
  (StreamCodec.product bytesStream StreamCodec.bool).encode (slotInstance plan index,yes)
/-- A slot can have only one nonempty application payload. Inert later blocks
allow old-view continuation without reopening the already-decided slot. -/
def slotBlockValid (plan : PrivatePlan) (index : Nat) (block : GenericSimplex.Block) : Bool :=
  let payloads := block.filter (fun b => !b.isEmpty)
  payloads.length == 1 &&
    (payloads.head? == some (decisionBytes plan index true) ||
     payloads.head? == some (decisionBytes plan index false))
/-- A checked prefix is granted only after the actual existing receiver's
CurrentAdmission and reservation compatibility/budget checks. The caller must
persist the returned table and engine input in ONE source image transaction.
This does not manufacture source authority to reserve. -/
def prepareYes {F : Type} [Field F] [DecidableEq F]
    {plan : PrivatePlan} (joint : JointDecisionRecovery.State plan)
    (table : JointReservation.Table) (i : Fin plan.candidate.participants.length)
    (parent : GenericSimplex.Block)
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {command : Command} {signed : SignedCommand}
    (admission : CurrentAdmission deployment profile ambient durable command signed
      plan.candidate.participants[i])
    (corrupt : Nat → Bool) (privateRecovery : Custody → Prop)
    (_qualified : PrivateSuccessorCustody.Qualified plan.candidate.participants[i].custody corrupt privateRecovery) :
    Option (JointReservation.Table × GenericSimplex.Input) := do
  let p := plan.candidate.participants[i]
  if p.custody.key.invocation != p.intent.transactionId ||
      p.custody.key.commandBytes != plan.candidate.commandBytes ||
      p.custody.key.attempt != plan.candidate.attempt ||
      p.custody.key.generation != p.generation ||
      DurableReceiverCodec.intentStream.encode p.custody.exactSuccessor !=
        DurableReceiverCodec.intentStream.encode p.intent then none else
  if i = plan.last ∧ ¬ LastReady joint then none else
  -- Changing the protocol parent must not charge/reserve the same native
  -- promise again. Reuse ONLY its complete existing candidate/projection.
  let proposal ← proposeLocalYes PrivateSuccessorCustodyCodec.descriptorStream i admission
  let existing := table.any fun held =>
    held.domain == p.domain && held.candidateBytes == proposal.candidateBytes &&
      held.lineage == plan.candidate.lineage && held.generation == p.generation &&
      DurableReceiverCodec.intentStream.encode held.intent ==
        DurableReceiverCodec.intentStream.encode p.intent
  let table ← if existing then some table else do
    let (next,_) ← JointReservation.reserve PrivateSuccessorCustodyCodec.descriptorStream table i admission
    pure next
  let block := parent ++ [decisionBytes plan i.val true]
  if slotBlockValid plan i.val block then some (table,.checked block) else none
/-- A source-applied promise is a DIFFERENT signature statement from an
engine COMMIT. The native source controller may sign it only after confirming
the agreed reservation/decision transition in the authoritative source log. -/
structure SourceCertificate where
  context : Context
  decision : List UInt8
  signers : List Attestation
def sourceCertificateStream : StreamCodec SourceCertificate :=
  StreamCodec.xmap
    (StreamCodec.product contextStream (StreamCodec.product bytesStream
      (StreamCodec.list attestationStream)))
    (fun c => (c.context,c.decision,c.signers))
    (fun (c,d,s) => ⟨c,d,s⟩) (by intro c; cases c; rfl)
def sourceAppliedBytes (context : Context) (decision : List UInt8) : List UInt8 :=
  [77,73,78,73,45,83,79,85,82,67,69,45,65,80,80,76,73,69,68,1] ++
    (StreamCodec.product contextStream bytesStream).encode (context,decision)
/-- GenericSimplexIO.exportCommitment cannot manufacture this certificate:
its signed domain separator differs. Source-applied exporter is intentionally
owned by the native atomic reservation controller, still an integration join. -/
def importDecision (crypto : Crypto) {plan : PrivatePlan}
    (joint : JointDecisionRecovery.State plan) (i : Fin plan.candidate.participants.length)
    (config : GenericSimplex.Config) (keys : List (List UInt8))
    (cert : SourceCertificate) : IO (Option (JointDecisionRecovery.State plan)) := do
  let context := slotContext plan i config keys
  if cert.context != context then return none
  if cert.decision != decisionBytes plan i.val true &&
      cert.decision != decisionBytes plan i.val false then return none
  if !(← verifyAttestations crypto context (sourceAppliedBytes context cert.decision) cert.signers) then return none
  let yes := cert.decision == decisionBytes plan i.val true
  return decideVote joint i (if yes then .yes else .no) (sourceCertificateStream.encode cert)
/-- Exact candidate identity includes the complete coherent-custody descriptor,
not just its generation key or command bytes. -/
theorem exactCandidate_injective (a b : PrivatePlan)
    (same : exactCandidate a = exactCandidate b) : a.candidate = b.candidate :=
  candidate_encode_injective PrivateSuccessorCustodyCodec.descriptorStream same
end Minidregg.Kernel.JointSimplexBinding
