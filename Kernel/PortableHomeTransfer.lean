/- Governed home transfer source state. The existing source cell/authority and
one ordinary DurableReceiver CAS own every phase. Physical receipts remain
private evidence to separately qualified native receivers, never booleans that
mint authority. No phase authorizes export of old secret holder material.
-/
import Kernel.PortableContinuationManifest
import Theory.ResourceCost
namespace Minidregg.Kernel.PortableHomeTransfer
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.PortableContinuationManifest
set_option autoImplicit false

structure Principal where
  subject : SubjectId
  /-- Independently current-enrolled credential, not archive-learned. -/
  publicKey : Bytes
  deriving DecidableEq, Repr

inductive CallStatus where
  | retained
  | dispatchedUncertain
  | reconciled (authoritativeOutcome : Bytes)
  deriving DecidableEq, Repr

/-- Entire original prepared Activity context and dispatch identity remain
immutable across transfer. An uncertain dispatch cannot become a fresh retry. -/
structure Liability where
  identity : Bytes
  originalContext : Bytes
  request : Bytes
  providerCustody : Artifact
  status : CallStatus
  deriving DecidableEq, Repr

/-- Compact source commitment to the private full custody manifest. The full
image/history/control bytes stay in the verified immutable archive rather than
recursively embedding old journal ancestry inside its own next control cell.
Actual exact readback and cryptographic hash separation/retrieval are required;
this reference is not a proof that bytes are available or a portable permit. -/
structure CutReference where
  identity : Identity
  point : Minidregg.Kernel.ReceiptContinuity.Point
  manifest : Artifact
  control : Artifact
  custodyGeneration : Nat
  required : List Artifact
  deriving DecidableEq, Repr

structure Plan where
  transfer : Bytes
  home : Bytes
  owner : Principal
  renter : Principal
  oldHostInstance : Bytes
  destination : Bytes
  destinationCredential : Bytes
  baseEpoch : Nat
  acknowledged : ParticipantPin
  source : CutReference
  /-- Exact complete source ResourceCell control wrapper at preparation. -/
  sourceControlRoot : Digest
  oldPrivateGeneration : Nat
  oldPrivateDescriptor : Bytes
  successorPrivateGeneration : Nat
  successorPrivateDescriptor : Bytes
  /-- Full source-selected physical custody closure, including private WAL,
  spent anchors, agreement replay/old-view liabilities and service archives. -/
  required : List Artifact
  liabilities : List Liability
  deriving DecidableEq, Repr

inductive Phase where
  | serving | prepared | quiesced | successorCustodied | oldHostFenced
  | destinationActive | released | aborted | recoveryRequired | activationPending
  deriving DecidableEq, Repr

structure State where
  home : Bytes
  owner : Principal
  renter : Principal
  currentHost : Bytes
  currentCredential : Bytes
  privateGeneration : Nat
  privateDescriptor : Bytes
  epoch : Nat
  phase : Phase
  plan : Option Plan
  cut : Option CutReference
  successorCustody : Bytes
  oldFence : Bytes
  destinationReceipt : Bytes
  /-- Authority-retained uncertainty survives cancellation/repair/restart. -/
  liabilities : List Liability
  /-- Maintenance remains source-funded, not an unfunded priority bit. -/
  required : List Artifact
  maintenanceReserve : Minidregg.Theory.ResourceCost.Charge
  /-- Exact current source home membership. Never supplied by an export request. -/
  governedCells : List Nat
  /-- Persisted source-selected external activation identity before dispatch. -/
  activationRequest : Bytes

/-- Same full identity, preparation, request and provider custody. Only a
current-source authoritative reconciliation may change status. -/
def SameCall (new old : Liability) : Prop :=
  new.identity = old.identity ∧ new.originalContext = old.originalContext ∧
  new.request = old.request ∧ new.providerCustody = old.providerCustody

def CallsRetained (new old : List Liability) : Prop :=
  ∀ liability ∈ old, ∃ next ∈ new, SameCall next liability

/-- Public-source law does not establish these physical/private propositions.
Actual adapters must construct evidence from current ordinary consent,
quiesced archive readback, qualified malicious private recovery/resharing,
old generation source revocation + native STOP and destination sealed custody.
There is deliberately no executable bool/callback-to-proof conversion. -/
structure Receivers where
  CurrentConsent : State → Plan → Prop
  QuiescedCut : Plan → CutReference → Prop
  SuccessorPrivateCustody : Plan → CutReference → Bytes → Prop
  OldHostFenced : Plan → Bytes → Prop
  DestinationActivated : Plan → Bytes → Bytes → Prop
  DestinationAcknowledged : Plan → CutReference → Bytes → Prop
  AuthoritativeOutcome : Plan → Liability → Bytes → Prop
  RecoveryClassified : State → Bytes → Prop
  OldHostResumed : Plan → Bytes → Prop
  DestinationRecovered : Plan → Bytes → Bytes → Prop
  ActivationCurrentPermit : State → Plan → Bytes → Prop

/-- Preparation freezes ONE exact successor, consent, history, old/full private
identity and destination. A different plan requires a fresh source transition. -/
def Binds (state : State) (plan : Plan) : Prop :=
  plan.home = state.home ∧ plan.owner = state.owner ∧ plan.renter = state.renter ∧
  plan.oldHostInstance = state.currentHost ∧ plan.baseEpoch = state.epoch ∧
  plan.oldPrivateGeneration = state.privateGeneration ∧
  plan.oldPrivateDescriptor = state.privateDescriptor ∧
  plan.successorPrivateGeneration = plan.oldPrivateGeneration + 1 ∧
  plan.acknowledged.identity = plan.source.identity ∧
  plan.acknowledged.participant = plan.renter.subject ∧
  plan.acknowledged.publicKey = plan.renter.publicKey ∧
  plan.required = state.required ∧
  (∀ liability ∈ state.liabilities, liability.providerCustody ∈ plan.required) ∧
  plan.liabilities = state.liabilities

def Settled (liability : Liability) : Prop :=
  match liability.status with
  | .reconciled _ => True
  | _ => False
instance (liability : Liability) : Decidable (Settled liability) := by
  unfold Settled; split <;> infer_instance

def AllSettled (liabilities : List Liability) : Prop := ∀ call ∈ liabilities, Settled call
instance (liabilities : List Liability) : Decidable (AllSettled liabilities) := by
  unfold AllSettled; infer_instance

/-- A released home may transfer again without discarding historical outcomes.
Old uncertain calls must be reconciled first; a released phase alone cannot
reset pending identities or bootstrap a fresh destination/holder generation. -/
def CanPrepare (state : State) : Prop :=
  state.phase = .serving ∨ (state.phase = .released ∧ AllSettled state.liabilities)
instance (state : State) : Decidable (CanPrepare state) := by
  unfold CanPrepare; infer_instance

/-- Exact source phase transitions. Source admission and physical CAS are
constructed in the separate receiver. Every transition increments epoch;
copying/replaying a phase receipt cannot acquire the next source epoch. -/
inductive Step (receivers : Receivers) : State → State → Prop where
  | prepare (old : State) (plan : Plan) (ready : CanPrepare old)
      (binding : Binds old plan) (consent : receivers.CurrentConsent old plan) :
      Step receivers old { old with
        epoch := old.epoch + 1, phase := .prepared,
        plan := some plan, cut := none, successorCustody := [], oldFence := [],
        destinationReceipt := [], liabilities := plan.liabilities,activationRequest := []}
  | cut (old : State) (plan : Plan) (manifest : CutReference)
      (phase : old.phase = .prepared) (selected : old.plan = some plan)
      (quiesced : receivers.QuiescedCut plan manifest)
      (identity : manifest.identity = plan.source.identity)
      (history : plan.source.point.height ≤ manifest.point.height)
      (retention : ∀ artifact ∈ plan.required, artifact ∈ manifest.required) :
      Step receivers old { old with
        epoch := old.epoch + 1, phase := .quiesced, cut := some manifest}
  | successor (old : State) (plan : Plan) (manifest : CutReference) (receipt : Bytes)
      (phase : old.phase = .quiesced) (selected : old.plan = some plan)
      (cut : old.cut = some manifest)
      (qualified : receivers.SuccessorPrivateCustody plan manifest receipt) :
      Step receivers old { old with
        epoch := old.epoch + 1, phase := .successorCustodied,
        successorCustody := receipt}
  | fence (old : State) (plan : Plan) (receipt : Bytes)
      (phase : old.phase = .successorCustodied) (selected : old.plan = some plan)
      (actual : receivers.OldHostFenced plan receipt) :
      Step receivers old { old with
        epoch := old.epoch + 1, phase := .oldHostFenced, oldFence := receipt}
  | beginActivation (old : State) (plan : Plan) (request : Bytes)
      (nonempty : request ≠ [])
      (phase : old.phase = .oldHostFenced) (selected : old.plan = some plan)
      (retry : old.activationRequest = [] ∨ old.activationRequest = request)
      (permit : receivers.ActivationCurrentPermit old plan request) :
      Step receivers old { old with
        epoch := old.epoch + 1, phase := .activationPending,activationRequest := request }
  | activate (old : State) (plan : Plan) (receipt : Bytes)
      (phase : old.phase = .activationPending) (selected : old.plan = some plan)
      (fenced : receivers.OldHostFenced plan old.oldFence)
      (actual : receivers.DestinationActivated plan old.oldFence receipt) :
      Step receivers old { old with
        epoch := old.epoch + 1, phase := .destinationActive,
        currentHost := plan.destination, currentCredential := plan.destinationCredential,
        privateGeneration := plan.successorPrivateGeneration,
        privateDescriptor := plan.successorPrivateDescriptor, destinationReceipt := receipt}
  | acknowledge (old : State) (plan : Plan) (manifest : CutReference) (receipt : Bytes)
      (phase : old.phase = .destinationActive) (selected : old.plan = some plan)
      (cut : old.cut = some manifest)
      (actual : receivers.DestinationAcknowledged plan manifest receipt) :
      Step receivers old { old with
        epoch := old.epoch + 1, phase := .released,
        destinationReceipt := old.destinationReceipt ++ receipt}
  | abortBeforeFence (old : State) (before : old.phase = .prepared ∨ old.phase = .quiesced)
      (classification : receivers.RecoveryClassified old []) :
      Step receivers old { old with
        epoch := old.epoch + 1, phase := .aborted}
  | resumeOld (old : State) (plan : Plan) (receipt : Bytes)
      (phase : old.phase = .aborted) (selected : old.plan = some plan)
      (host : old.currentHost = plan.oldHostInstance)
      (generation : old.privateGeneration = plan.oldPrivateGeneration)
      (descriptor : old.privateDescriptor = plan.oldPrivateDescriptor)
      (settled : AllSettled old.liabilities)
      (actual : receivers.OldHostResumed plan receipt) :
      Step receivers old { old with
        epoch := old.epoch + 1, phase := .serving }
  | quarantine (old : State) (reason : Bytes)
      (classification : receivers.RecoveryClassified old reason) :
      Step receivers old { old with
        epoch := old.epoch + 1, phase := .recoveryRequired}
  | recoverFenced (old : State) (plan : Plan) (manifest : CutReference)
      (phase : old.phase = .recoveryRequired) (selected : old.plan = some plan)
      (cut : old.cut = some manifest) (host : old.currentHost = plan.oldHostInstance)
      (generation : old.privateGeneration = plan.oldPrivateGeneration)
      (descriptor : old.privateDescriptor = plan.oldPrivateDescriptor)
      (custodied : receivers.SuccessorPrivateCustody plan manifest old.successorCustody)
      (fenced : receivers.OldHostFenced plan old.oldFence)
      (classified : receivers.RecoveryClassified old old.oldFence) :
      Step receivers old { old with
        epoch := old.epoch + 1, phase := .oldHostFenced }
  | recoverActive (old : State) (plan : Plan)
      (phase : old.phase = .recoveryRequired) (selected : old.plan = some plan)
      (host : old.currentHost = plan.destination)
      (credential : old.currentCredential = plan.destinationCredential)
      (generation : old.privateGeneration = plan.successorPrivateGeneration)
      (descriptor : old.privateDescriptor = plan.successorPrivateDescriptor)
      (actual : receivers.DestinationRecovered plan old.oldFence old.destinationReceipt)
      (classified : receivers.RecoveryClassified old old.destinationReceipt) :
      Step receivers old { old with
        epoch := old.epoch + 1, phase := .destinationActive }
  | reconcile (old : State) (plan : Plan) (liability : Liability) (outcome : Bytes)
      (selected : old.plan = some plan) (member : liability ∈ old.liabilities)
      (unsettled : liability.status = .retained ∨ liability.status = .dispatchedUncertain)
      (actual : receivers.AuthoritativeOutcome plan liability outcome) :
      Step receivers old { old with
        epoch := old.epoch + 1,
        liabilities := old.liabilities.map fun call =>
          if call = liability then {call with status := .reconciled outcome} else call}

/-- Fresh work requires the destination source phase AND authoritative outcome
classification for every old call. A checkpoint Ready flag cannot supply this. -/
def FreshWork (state : State) : Prop :=
  (state.phase = .destinationActive ∨ state.phase = .released) ∧
  AllSettled state.liabilities

theorem step_epoch {receivers : Receivers} {old next : State}
    (step : Step receivers old next) : next.epoch = old.epoch + 1 := by
  cases step <;> rfl

theorem step_home {receivers : Receivers} {old next : State}
    (step : Step receivers old next) : next.home = old.home := by cases step <;> rfl

/-- Every transition retains the old exact request/context/custody, including
abort and uncertain recovery; reconciliation changes only authoritative status. -/
theorem step_calls {receivers : Receivers} {old next : State}
    (step : Step receivers old next) : CallsRetained next.liabilities old.liabilities := by
  cases step with
  | prepare plan _ binding _ =>
      rcases binding with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,calls⟩
      rw [calls]
      intro call present; exact ⟨call,present,rfl,rfl,rfl,rfl⟩
  | reconcile plan liability outcome selected member unsettled actual =>
      intro call present
      let f := fun (entry : Liability) =>
        if entry = liability then {entry with status := .reconciled outcome} else entry
      refine ⟨f call,List.mem_map.mpr ⟨call,present,rfl⟩,?_⟩
      dsimp [f]
      split <;> exact ⟨rfl,rfl,rfl,rfl⟩
  | _ => intro call present; exact ⟨call,present,rfl,rfl,rfl,rfl⟩

/-- Authoritatively reconciled old outcomes survive abort, recovery, activation
and later consented transfers byte-for-byte. No retry can reset a settled call
or substitute another outcome by reusing its original dispatch identity. -/
theorem settled_outcomes_retained {receivers : Receivers} {old next : State}
    (step : Step receivers old next) (call : Liability)
    (present : call ∈ old.liabilities) (settled : Settled call) :
    call ∈ next.liabilities := by
  cases step with
  | prepare plan _ binding _ =>
      rcases binding with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,calls⟩
      rw [calls]
      exact present
  | reconcile plan liability outcome selected member unsettled actual =>
      have different : call ≠ liability := by
        intro same
        rw [same] at settled
        rcases unsettled with retained | uncertain
        · simp [Settled,retained] at settled
        · simp [Settled,uncertain] at settled
      exact List.mem_map.mpr ⟨call,present,if_neg different⟩
  | _ => exact present

theorem step_governed_cells {receivers : Receivers} {old next : State}
    (step : Step receivers old next) : next.governedCells = old.governedCells := by
  cases step <;> rfl

/-- Within one source-selected phase, destination activation can only follow
actual old-host fencing evidence. This does not prove a malicious host erased
old shares or that two independently forked Stores share source authority. -/
theorem activates_only_after_fence {receivers : Receivers} {old next : State}
    (step : Step receivers old next) (activated : old.currentHost ≠ next.currentHost) :
    old.phase = .activationPending ∧ ∃ plan, old.plan = some plan ∧
      next.currentHost = plan.destination ∧ receivers.OldHostFenced plan old.oldFence := by
  cases step with
  | activate plan receipt phase selected fenced actual => exact ⟨phase,plan,selected,rfl,fenced⟩
  | _ => exact False.elim (activated rfl)

/-- One exact current source phase selects one successor. Physical duplication
of an old Store is not included in this premise; the agreed source/CAS consumer
must keep that common current authority and cannot infer it from archive ACK. -/
theorem one_successor {receivers : Receivers} {old left right : State}
    (leftStep : Step receivers old left) (rightStep : Step receivers old right)
    (leftChanged : old.currentHost ≠ left.currentHost)
    (rightChanged : old.currentHost ≠ right.currentHost) : left.currentHost = right.currentHost := by
  rcases activates_only_after_fence leftStep leftChanged with ⟨_,lp,ls,lh,_⟩
  rcases activates_only_after_fence rightStep rightChanged with ⟨_,rp,rs,rh,_⟩
  have same : lp = rp := Option.some.inj (ls.symm.trans rs)
  exact lh.trans ((congrArg Plan.destination same).trans rh.symm)

theorem generation_changes_only_after_fence {receivers : Receivers} {old next : State}
    (step : Step receivers old next) (changed : old.privateGeneration ≠ next.privateGeneration) :
    old.phase = .activationPending ∧
      ∃ plan, old.plan = some plan ∧ receivers.OldHostFenced plan old.oldFence := by
  cases step with
  | activate plan receipt phase selected fenced actual => exact ⟨phase,plan,selected,fenced⟩
  | _ => exact False.elim (changed rfl)

/-- A lost destination reply cannot choose a fresh activation identity during
recovery. Only another ordinary consented preparation after completed release
may clear the old attempt; all intermediate phases and retries retain it. -/
theorem activation_attempt_retained {receivers : Receivers} {old next : State}
    (step : Step receivers old next) (present : old.activationRequest ≠ [])
    (notPreparing : ¬ CanPrepare old) : next.activationRequest = old.activationRequest := by
  cases step with
  | prepare plan ready binding consent => exact False.elim (notPreparing ready)
  | beginActivation plan request nonempty phase selected retry permit =>
      rcases retry with empty | same
      · exact False.elim (present empty)
      · exact same.symm
  | _ => rfl

#assert_axioms activation_attempt_retained
#assert_axioms one_successor
#assert_axioms generation_changes_only_after_fence
#assert_axioms step_epoch
#assert_axioms step_home
#assert_axioms step_governed_cells
#assert_axioms step_calls
#assert_axioms settled_outcomes_retained
#assert_axioms activates_only_after_fence
end Minidregg.Kernel.PortableHomeTransfer
