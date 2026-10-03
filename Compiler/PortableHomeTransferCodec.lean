/- Canonical private governed-transfer source payload. No receipt string or
phase flag creates an authority, fencing or private successor capability. -/
import Kernel.PortableHomeTransfer
import Compiler.PortableContinuationManifestCodec
namespace Minidregg.Compiler.PortableHomeTransferCodec
open Minidregg.Kernel.PortableHomeTransfer
open Minidregg.Kernel.PortableContinuationManifest
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.PortableContinuationManifestCodec
set_option autoImplicit false

def principalStream : StreamCodec Principal :=
  StreamCodec.xmap (StreamCodec.product DurableReceiverCodec.subjectStream bytesStream)
    (fun value => (value.subject, value.publicKey))
    (fun (subject, publicKey) => ⟨subject, publicKey⟩) (by intro value; cases value; rfl)

private def statusTag : CallStatus → Nat × Bytes
  | .retained => (0,[])
  | .dispatchedUncertain => (1,[])
  | .reconciled outcome => (2,outcome)
private def tagStatus : Nat × Bytes → CallStatus
  | (1,_) => .dispatchedUncertain
  | (2,outcome) => .reconciled outcome
  | _ => .retained

def statusStream : StreamCodec CallStatus :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat bytesStream)
    statusTag tagStatus (by intro status; cases status <;> rfl)

def liabilityStream : StreamCodec Liability :=
  StreamCodec.xmap (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product artifactStream statusStream))))
    (fun value => (value.identity, value.originalContext, value.request, value.providerCustody, value.status))
    (fun (identity, originalContext, request, providerCustody, status) => ⟨identity, originalContext, request, providerCustody, status⟩) (by intro value; cases value; rfl)

def participantPinStream : StreamCodec ParticipantPin :=
  StreamCodec.xmap (StreamCodec.product DurableReceiverCodec.subjectStream (StreamCodec.product bytesStream (StreamCodec.product identityStream pointStream)))
    (fun value => (value.participant, value.publicKey, value.identity, value.acknowledged))
    (fun (participant, publicKey, identity, acknowledged) => ⟨participant, publicKey, identity, acknowledged⟩) (by intro value; cases value; rfl)

def cutReferenceStream : StreamCodec CutReference :=
  StreamCodec.xmap
    (StreamCodec.product identityStream (StreamCodec.product pointStream
      (StreamCodec.product artifactStream (StreamCodec.product artifactStream
        (StreamCodec.product StreamCodec.nat (StreamCodec.list artifactStream))))))
    (fun cut => (cut.identity,cut.point,cut.manifest,cut.control,cut.custodyGeneration,cut.required))
    (fun (i,p,m,c,g,r) => ⟨i,p,m,c,g,r⟩) (by intro cut; cases cut; rfl)

def planStream : StreamCodec Plan :=
  StreamCodec.xmap (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product principalStream (StreamCodec.product principalStream (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat (StreamCodec.product participantPinStream (StreamCodec.product cutReferenceStream (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream (StreamCodec.product (StreamCodec.list artifactStream) (StreamCodec.list liabilityStream)))))))))))))))))
    (fun value => (value.transfer, value.home, value.owner, value.renter, value.oldHostInstance, value.destination, value.destinationCredential, value.baseEpoch, value.acknowledged, value.source, value.sourceControlRoot, value.oldPrivateGeneration, value.oldPrivateDescriptor, value.successorPrivateGeneration, value.successorPrivateDescriptor, value.required, value.liabilities))
    (fun (transfer, home, owner, renter, oldHostInstance, destination, destinationCredential, baseEpoch, acknowledged, source, sourceControlRoot, oldPrivateGeneration, oldPrivateDescriptor, successorPrivateGeneration, successorPrivateDescriptor, required, liabilities) => ⟨transfer, home, owner, renter, oldHostInstance, destination, destinationCredential, baseEpoch, acknowledged, source, sourceControlRoot, oldPrivateGeneration, oldPrivateDescriptor, successorPrivateGeneration, successorPrivateDescriptor, required, liabilities⟩) (by intro value; cases value; rfl)

private def phaseTag : Phase → Nat
  | .serving => 0
  | .prepared => 1
  | .quiesced => 2
  | .successorCustodied => 3
  | .oldHostFenced => 4
  | .destinationActive => 5
  | .released => 6
  | .aborted => 7
  | .recoveryRequired => 8
private def tagPhase : Nat → Phase
  | 0 => .serving
  | 1 => .prepared
  | 2 => .quiesced
  | 3 => .successorCustodied
  | 4 => .oldHostFenced
  | 5 => .destinationActive
  | 6 => .released
  | 7 => .aborted
  | _ => .recoveryRequired
def phaseStream : StreamCodec Phase :=
  StreamCodec.xmap StreamCodec.nat phaseTag tagPhase (by intro phase; cases phase <;> rfl)

def stateStream : StreamCodec State :=
  StreamCodec.xmap (StreamCodec.product bytesStream (StreamCodec.product principalStream (StreamCodec.product principalStream (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat (StreamCodec.product phaseStream (StreamCodec.product (StreamCodec.option planStream) (StreamCodec.product (StreamCodec.option cutReferenceStream) (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product (StreamCodec.list liabilityStream) (StreamCodec.product (StreamCodec.list artifactStream) (StreamCodec.product DurableReceiverCodec.chargeStream (StreamCodec.list StreamCodec.nat))))))))))))))))))
    (fun value => (value.home, value.owner, value.renter, value.currentHost, value.currentCredential, value.privateGeneration, value.privateDescriptor, value.epoch, value.phase, value.plan, value.cut, value.successorCustody, value.oldFence, value.destinationReceipt, value.liabilities, value.required, value.maintenanceReserve, value.governedCells))
    (fun (home, owner, renter, currentHost, currentCredential, privateGeneration, privateDescriptor, epoch, phase, plan, cut, successorCustody, oldFence, destinationReceipt, liabilities, required, maintenanceReserve, governedCells) => ⟨home, owner, renter, currentHost, currentCredential, privateGeneration, privateDescriptor, epoch, phase, plan, cut, successorCustody, oldFence, destinationReceipt, liabilities, required, maintenanceReserve, governedCells⟩) (by intro value; cases value; rfl)

def frame : Bytes := "DREGG.PORTABLE.HOME-CONTROL/v1".toUTF8.toList
def encode (state : State) : Bytes := frame ++ stateStream.encode state
def decode (bytes : Bytes) : Option State := do
  let state ← stateStream.toLawful.decode (bytes.drop frame.length)
  if encode state = bytes then some state else none

@[simp] theorem decode_encode (state : State) : decode (encode state) = some state := by
  have roundtrip := stateStream.toLawful.decode_encode state
  change stateStream.toLawful.decode (stateStream.encode state) = some state at roundtrip
  simp [decode,encode,List.drop_left,roundtrip]

/-- Exact source statement signed by both independently current-admitted
owner/renter ordinary invocations. Evidence signatures are not semantic identity. -/
def proposalBytes (plan : Plan) : Bytes :=
  "DREGG.PORTABLE.HOME-TRANSFER-PROPOSAL/v1".toUTF8.toList ++ planStream.encode plan

#assert_axioms decode_encode
end Minidregg.Compiler.PortableHomeTransferCodec
