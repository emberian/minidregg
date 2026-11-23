/- Share issue selection and signed dispatch admission under one authenticated Store head. -/
module
public import Kernel.NativeHostLight
public import Kernel.NativeHistorySelection
public import Kernel.ApplicationDispatchHistoricalCore

@[expose] public section
namespace Minidregg.Kernel.ApplicationDispatchLight
open Minidregg.Compiler Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure IndexedIssue (config : Config) (light : NativeHostLight.Light config) (index : Nat) where
  private mk ::
  candidate : NativeHistorySelection.Candidate config light.opening.head index
  evidence : ApplicationDispatchHistoricalCore.IssuedEvidence config
  exactRecord : evidence.record = candidate.record

/-- Select the historical issue at its own prefix. Both the legacy and grain issue must
reproduce the complete authenticated record before their source can be used for planning. -/
def selectIssue (config : Config) (light : NativeHostLight.Light config) (index : Nat) :
    ExceptT String IO (IndexedIssue config light index) := do
  let reader := light.opening.reader config.transport ResourceBirthCodec.rootBytes
  let read ← ExceptT.mk ((·.mapError (·.message)) <$> reader.atHeight (index + 1))
  let candidate ← ExceptT.mk (NativeHistorySelection.select config reader reader.head.height index
    ⟨[read.record.transactionId], read.record.nullifiers⟩)
  let bytes := candidate.record.event.canonicalBytes
  let height := config.genesisHeight + candidate.ground.height
  let pins := candidate.pins
  match candidate.record.event.codecVersion with
  | 15 =>
    let ⟨ingress, accepted⟩ ← ExceptT.mk (ApplicationShareIssueAdmission.admitNative config.profile
      config pins config.signature candidate.ground height bytes)
    let matched ← NativeHistorySelection.matchIntent candidate (ApplicationShareIssueReceiver.intent accepted)
    return ⟨candidate, .fromAccepted config pins candidate.ground height ingress accepted candidate.record matched.candidateRecord, rfl⟩
  | 22 =>
    let ⟨ingress, accepted⟩ ← ExceptT.mk (ApplicationShareIssueGrainAdmission.admitNative config.profile
      config pins config.signature candidate.ground ⟨config.federation, height⟩ bytes)
    let matched ← NativeHistorySelection.matchIntent candidate (ApplicationShareIssueGrainReceiver.intent accepted)
    return ⟨candidate, .fromGrainAccepted config pins candidate.ground ⟨config.federation, height⟩ ingress
      accepted candidate.record matched.candidateRecord, rfl⟩
  | _ => throw "admitted share issue index unavailable"

/-- The original transaction selector is taken from the nested signed birth. -/
private def issueTransaction (source : List UInt8) : Option Minidregg.Theory.TypedAuthorization.Digest :=
  (do
    let issue ← ApplicationShareIssueSource.ingressCodec.decode source
    let birth ← ResourceBirthPolicyController.Concrete.decodeIngress issue.birthIngress
    pure birth.descriptor.transactionId) <|> (do
    let issue ← ApplicationShareIssueGrainSource.codec.decode source
    let grain ← issue.decodeGrain
    pure grain.source.birth.transactionId)

def selectSignedIssue (config : Config) (light : NativeHostLight.Light config)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) :
    ExceptT String IO ((index : Nat) × IndexedIssue config light index) := do
  let some issueTx := issueTransaction ingress.issueIngressBytes | throw "noncanonical issue source"
  let reader := light.opening.reader config.transport ResourceBirthCodec.rootBytes
  let .present found ← ExceptT.mk ((·.mapError (·.message)) <$> reader.byTx issueTx)
    | throw "original issue unavailable"
  return ⟨found.height - 1, ← selectIssue config light (found.height - 1)⟩

/-- The app command and payer command are checked on the same state, with the authenticated
answers for both invocations. The payer's signed command is checked again by each family's admission. -/
def paidBasis (config : Config) (light : NativeHostLight.Light config)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) (payer : DeclaredResourceController.SignedCommand) :
    ExceptT String IO (ServedBasis.Basis config.deployment light.opening.store) := do
  let some selected := ApplicationDispatchAdmission.selectCommand ingress | throw "dispatch selection unavailable"
  let some command := DeclaredResourceController.commandCodec.decode payer.commandBytes | throw "payer command malformed"
  let keys := DeclaredResourceController.invocationKeys config.deployment.domain config.profile.semantics
  let app := keys (ApplicationDispatchCommand.command ingress.dispatch selected ingress.parent)
  let pay := keys command
  ExceptT.mk (light.basis ⟨app.transactions ++ pay.transactions, app.nullifiers ++ pay.nullifiers⟩)

structure Admitted (config : Config) (light : NativeHostLight.Light config)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) where
  private mk ::
  index : Nat
  issue : IndexedIssue config light index
  basis : ServedBasis.Basis config.deployment light.opening.store
  atHead : basis.head = light.opening.head
  checked : ApplicationDispatchHistoricalCore.CheckedCandidate config (.ofBasis basis) ingress issue.evidence

def admit (config : Config) (light : NativeHostLight.Light config)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) : ExceptT String IO (Admitted config light ingress) := do
  let ⟨_, issue⟩ ← selectSignedIssue config light ingress
  let reader := light.opening.reader config.transport ResourceBirthCodec.rootBytes
  let some selection := ApplicationDispatchAdmission.selectCommand ingress | throw "dispatch selection unavailable"
  let command := ApplicationDispatchCommand.command ingress.dispatch selection ingress.parent
  let keys := DeclaredResourceController.invocationKeys config.deployment.domain config.profile.semantics command
  let footprint ← ExceptT.mk ((·.mapError (·.message)) <$> reader.footprint keys)
  have below : light.opened.served.height ≤ light.opening.head.height := by
    rw [light.same, light.opening.heightExact]
  let basis := light.opened.basis light.opening.head below footprint
  let checked ← ExceptT.mk (ApplicationDispatchHistoricalCore.checkCurrent config (.ofBasis basis) ingress issue.evidence)
  return ⟨_, issue, basis, rfl, checked⟩

end Minidregg.Kernel.ApplicationDispatchLight
