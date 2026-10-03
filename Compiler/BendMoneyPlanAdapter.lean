/- Exact structural bridge from authored WorldPlanMoney Data to the ordinary
native Plan. The checked source trace and complete ABI definitions are retained.
Money operations come from the source result; the actual receiver supplies the
same-snapshot financial token and current account consent legs. No output table
can authenticate source inputs. Qualification of this additive leaf is separate
from its source-first publication. -/
import Compiler.BendScalarPlanBytesAdapter
import Compiler.BendSurfaceLowering
import Kernel.ResourceMoneyReceiver

namespace Minidregg.Compiler.BendMoneyPlanAdapter
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.BendSourceRepresentation
open Minidregg.Theory
open Minidregg.Theory.BendTT
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel
set_option autoImplicit false

abbrev Ref := BendScalarPlanAdapter.Ref
abbrev Scalar := BendScalarPlanAdapter.Scalar
abbrev constructor := BendSurfaceLowering.constructor
abbrev decodeConstructor := BendSurfaceLowering.decodeConstructor
abbrev listTerm := @BendScalarPlanAdapter.listTerm
abbrev decodeList := @BendScalarPlanAdapter.decodeList
abbrev identityCodec := BendScalarPlanBytesAdapter.identityCodec
abbrev rootCodec := BendScalarPlanBytesAdapter.rootCodec
def subjectCodec : LawfulCodec SubjectId :=
  ResourceBirthCodec.strictCodec TypedAuthorizationRequestCodec.subjectIdStream.toLawful

structure Transfer where
  source : Nat
  destination : Nat
  asset : Nat
  amount : Nat
  deriving DecidableEq, Repr

def Transfer.operation (transfer : Transfer) : CanonicalResourceKernel.Operation :=
  .transfer transfer.source transfer.destination transfer.asset transfer.amount

structure NativePlan where
  book : Ref
  operations : List Transfer
  reads : List Ref
  effects : List Scalar
  returns : List BendWorldPlan.ReturnSlot
  deriving DecidableEq, Repr

inductive PlanResult where
  | refused (reason : Nat)
  | planned (plan : NativePlan)
  deriving DecidableEq, Repr

def identityTerm (value : Nat) : BTerm := bytesTerm (identityCodec.encode value)
def decodeIdentity (term : BTerm) : Option Nat := do
  identityCodec.decode (← decodeBytes term)

def transferTerm (transfer : Transfer) : BTerm :=
  constructor "WorldPlanMoney.Transfer" [identityTerm transfer.source,
    identityTerm transfer.destination, identityTerm transfer.asset, natTerm transfer.amount]
def decodeTransfer (term : BTerm) : Option Transfer := do
  let [source, destination, asset, amount] ← decodeConstructor "WorldPlanMoney.Transfer" term
    | none
  pure ⟨← decodeIdentity source, ← decodeIdentity destination,
    ← decodeIdentity asset, ← decodeNat amount⟩

def returnTerm (slot : BendWorldPlan.ReturnSlot) : BTerm :=
  constructor "WorldPlanMoney.ReturnSlot" [
    bytesTerm slot.name.toUTF8.toList, bytesTerm (rootCodec.encode slot.valueSchema),
    bytesTerm (rootCodec.encode slot.encoding), bytesTerm (subjectCodec.encode slot.recipient),
    bytesTerm (rootCodec.encode slot.keyEpoch), bytesTerm (rootCodec.encode slot.audience),
    natTerm slot.generation, bytesTerm slot.bytes]
def decodeRoot (term : BTerm) : Option Digest := do
  rootCodec.decode (← decodeBytes term)
def decodeSubject (term : BTerm) : Option SubjectId := do
  subjectCodec.decode (← decodeBytes term)
def decodeReturn (term : BTerm) : Option BendWorldPlan.ReturnSlot := do
  let [name, schema, encoding, recipient, epoch, audience, generation, payload] ←
    decodeConstructor "WorldPlanMoney.ReturnSlot" term | none
  let bytes ← decodeBytes name
  let name ← String.fromUTF8? ⟨bytes.toArray⟩
  if name.toUTF8.toList = bytes then
    pure ⟨name, ← decodeRoot schema, ← decodeRoot encoding, ← decodeSubject recipient,
      ← decodeRoot epoch, ← decodeRoot audience, ← decodeNat generation, ← decodeBytes payload⟩
  else none

def planTerm (plan : NativePlan) : BTerm :=
  constructor "WorldPlanMoney.NativePlan" [
    BendScalarPlanBytesAdapter.refTerm plan.book, listTerm transferTerm plan.operations,
    listTerm BendScalarPlanBytesAdapter.refTerm plan.reads,
    listTerm BendScalarPlanBytesAdapter.scalarTerm plan.effects, listTerm returnTerm plan.returns]
def decodePlan (term : BTerm) : Option NativePlan := do
  let [book, operations, reads, effects, returns] ←
    decodeConstructor "WorldPlanMoney.NativePlan" term | none
  pure ⟨← BendScalarPlanBytesAdapter.decodeRef book, ← decodeList decodeTransfer operations,
    ← decodeList BendScalarPlanBytesAdapter.decodeRef reads,
    ← decodeList BendScalarPlanBytesAdapter.decodeScalar effects,
    ← decodeList decodeReturn returns⟩
def resultTerm : PlanResult → BTerm
  | .refused reason => constructor "WorldPlanMoney.Refused" [natTerm reason]
  | .planned plan => constructor "WorldPlanMoney.Planned" [planTerm plan]
def decodeResult (term : BTerm) : Option PlanResult :=
  match decodeConstructor "WorldPlanMoney.Refused" term with
  | some [reason] => (decodeNat reason).map PlanResult.refused
  | _ => do
    let [plan] ← decodeConstructor "WorldPlanMoney.Planned" term | none
    (decodePlan plan).map PlanResult.planned

@[simp] theorem decode_identityTerm (value : Nat) :
    decodeIdentity (identityTerm value) = some value := by
  simp [decodeIdentity, identityTerm, decode_bytesTerm, identityCodec.decode_encode]
@[simp] theorem decode_transferTerm (transfer : Transfer) :
    decodeTransfer (transferTerm transfer) = some transfer := by
  cases transfer
  simp [decodeTransfer, transferTerm, BendSurfaceLowering.decode_constructor, decode_natTerm]

abbrev listType := BendScalarPlanAdapter.listType
abbrev fieldsType := BendScalarPlanAdapter.fieldsType
abbrev singleArmsDef := BendScalarPlanAdapter.singleArmsDef
abbrev singleTypeDef := BendScalarPlanAdapter.singleTypeDef
def abiDefinitions : List Def :=
  [singleArmsDef "WorldPlanMoney.Transfer"
      [listType "Nat", listType "Nat", listType "Nat", .Ref "Nat"],
   singleTypeDef "WorldPlanMoney.Transfer",
   singleArmsDef "WorldPlanMoney.ReturnSlot"
      [listType "Nat", listType "Nat", listType "Nat", listType "Nat",
       listType "Nat", listType "Nat", .Ref "Nat", listType "Nat"],
   singleTypeDef "WorldPlanMoney.ReturnSlot",
   singleArmsDef "WorldPlanMoney.NativePlan"
      [.Ref "WorldPlanScalarBytes.Ref", listType "WorldPlanMoney.Transfer",
       listType "WorldPlanScalarBytes.Ref", listType "WorldPlanScalarBytes.ScalarEffect",
       listType "WorldPlanMoney.ReturnSlot"],
   singleTypeDef "WorldPlanMoney.NativePlan",
   ⟨"WorldPlanMoney.PlanResult.arms",
     .All .Q1 (.Enu ["WorldPlanMoney.Refused", "WorldPlanMoney.Planned"]) (.Typ .Q2),
     .Mat "WorldPlanMoney.Refused" (fieldsType [.Ref "Nat"])
       (.Mat "WorldPlanMoney.Planned" (fieldsType [.Ref "WorldPlanMoney.NativePlan"]) .Efq), false⟩,
   ⟨"WorldPlanMoney.PlanResult", .Typ .Q2,
     .Sig .Q1 (.Enu ["WorldPlanMoney.Refused", "WorldPlanMoney.Planned"])
       (.App .Q1 (.Ref "WorldPlanMoney.PlanResult.arms") (.Var 0)), false⟩]

structure ABIBinding (book : Book) where
  scalar : BendScalarPlanBytesAdapter.ABIBinding book
  exactDefinitions : ∀ definition ∈ abiDefinitions, Book.get book definition.k = some definition
def bindABI (core : BendCoreAdmission.Checked) : Option (ABIBinding core.book) := do
  let scalar ← BendScalarPlanBytesAdapter.bindABI core
  if exactDefinitions : ∀ definition ∈ abiDefinitions,
      Book.get core.book definition.k = some definition then
    some ⟨scalar, exactDefinitions⟩
  else none

def batch (source : NativePlan) : ResourceMoneyWire.ApplicationBatch :=
  ⟨source.book.root, source.operations.map Transfer.operation⟩
def moneyEffect (index : Nat) (source : NativePlan) : BendWorldPlan.Effect :=
  ⟨index, .moneyConsent ⟨some (batch source), [], none⟩⟩
abbrev entriesOf := moneyEntries
def carriers (command : Command) : List (Fin command.targets.length) :=
  (List.finRange command.targets.length).filter fun index =>
    match command.targets[index].payload with
    | .moneyConsent consent => consent.batch.isSome
    | _ => false

/-- The batch and object phases are one atomic application. Carrier location is
native layout, not a source identity or authority: funded carrier may be last.
Scalar effect order is preserved; exact command comparison still rejects every
missing, extra or reordered application effect. -/
def insertMoney (index : Nat) (source : NativePlan) :
    List BendWorldPlan.Effect → List BendWorldPlan.Effect
  | [] => [moneyEffect index source]
  | effect :: rest =>
    if effect.target < index then effect :: insertMoney index source rest
    else moneyEffect index source :: effect :: rest

theorem insertMoney_length (index : Nat) (source : NativePlan)
    (effects : List BendWorldPlan.Effect) :
    (insertMoney index source effects).length = effects.length + 1 := by
  induction effects with
  | nil => rfl
  | cons effect rest ih =>
    simp only [insertMoney]
    split <;> simp_all

/-- Same durable snapshot for financial preparation and scalar phase binding.
The full native account-position/funding consent remains in command and money;
only its application projection is normalized in the Plan effect. -/
structure BoundPlan {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (entries : List ResourceMoneyWire.Entry)
    (money : ResourceMoneyReceiver.Prepared deployment durable.snapshot entries)
    (source : NativePlan) where
  private mk ::
  plan : BendWorldPlan.Plan
  carrier : Fin command.targets.length
  carrierUnique : carriers command = [carrier]
  entriesExact : entriesOf command = entries
  bookExact : source.book.resourceID = deployment.resourceBookId
  batchExact : batch source = money.batch
  commandDistinct : (command.targets.map Target.target).Nodup
  effectsDistinct : (source.effects.map fun effect => effect.ref.resourceID).Nodup
  scalarEffects : List BendWorldPlan.Effect
  ordered : BendScalarPlanAdapter.Ordered deployment loaded command source.effects scalarEffects
  effectsExact : plan.effects = insertMoney carrier.val source scalarEffects
  scalarReads : List Minidregg.Kernel.DurableDataIntent.ReadGuard
  orderedReads : BendScalarPlanAdapter.OrderedReads loaded source.reads scalarReads
  readsExact : plan.reads = money.readGuards ++ scalarReads
  returnsExact : plan.returns = source.returns
  nativeExact : BendWorldPlan.matchesCommand plan command = true

def bindPlan {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (entries : List ResourceMoneyWire.Entry)
    (money : ResourceMoneyReceiver.Prepared deployment durable.snapshot entries)
    (source : NativePlan) : Option (BoundPlan deployment loaded command entries money source) := do
  match carrierUnique : carriers command with
  | [carrier] =>
    if entriesExact : entriesOf command = entries then
      if bookExact : source.book.resourceID = deployment.resourceBookId then
        if batchExact : batch source = money.batch then
          if commandDistinct : (command.targets.map Target.target).Nodup then
            if effectsDistinct : (source.effects.map fun effect => effect.ref.resourceID).Nodup then
              let scalars ← BendScalarPlanAdapter.bindOrdered deployment loaded command source.effects
              let reads ← BendScalarPlanAdapter.bindReads loaded source.reads
              let plan : BendWorldPlan.Plan :=
                ⟨insertMoney carrier.val source scalars.1, source.returns,
                  money.readGuards ++ reads.1⟩
              if nativeExact : BendWorldPlan.matchesCommand plan command = true then
                some ⟨plan, carrier, carrierUnique, entriesExact, bookExact, batchExact,
                  commandDistinct, effectsDistinct, scalars.1, scalars.2, rfl,
                  reads.1, reads.2, rfl, rfl, nativeExact⟩
              else none
            else none
          else none
        else none
      else none
    else none
  | _ => none

structure Evaluated (core : BendCoreAdmission.Checked) (initial : BTerm) where
  result : BTerm
  count : Nat
  trace : BendLiveMachine.Trace core.book count initial result
  value : Value core.book result
  output : PlanResult
  abi : ABIBinding core.book
  decoded : decodeResult result = some output
def execute (core : BendCoreAdmission.Checked) (abi : ABIBinding core.book)
    (classificationTicks steps : Nat) (initial : BTerm) : Option (Evaluated core initial) :=
  match BendLiveMachine.executeChecked core.book classificationTicks steps initial with
  | .refused _ _ _ _ => none
  | .complete result count trace value =>
    match decoded : decodeResult result with
    | none => none
    | some output => some ⟨result, count, trace, value, output, abi, decoded⟩

/-- Constructor decoding never substitutes for actual completed source execution. -/
def lowerEvaluated {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (entries : List ResourceMoneyWire.Entry)
    (money : ResourceMoneyReceiver.Prepared deployment durable.snapshot entries)
    {core : BendCoreAdmission.Checked} {initial : BTerm}
    (evaluated : Evaluated core initial) :
    Option (Sigma fun source => BoundPlan deployment loaded command entries money source) :=
  match evaluated.output with
  | .refused _ => none
  | .planned source => do
      let bound ← bindPlan deployment loaded command entries money source
      pure ⟨source, bound⟩

theorem operations_exact {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {deployment : CanonicalCellRegistry.Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {command : Command} {entries : List ResourceMoneyWire.Entry}
    {money : ResourceMoneyReceiver.Prepared deployment durable.snapshot entries}
    {source : NativePlan} (bound : BoundPlan deployment loaded command entries money source) :
    source.operations.map Transfer.operation = money.batch.operations :=
  congrArg ResourceMoneyWire.ApplicationBatch.operations bound.batchExact

theorem returns_exact {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {deployment : CanonicalCellRegistry.Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {command : Command} {entries : List ResourceMoneyWire.Entry}
    {money : ResourceMoneyReceiver.Prepared deployment durable.snapshot entries}
    {source : NativePlan} (bound : BoundPlan deployment loaded command entries money source) :
    bound.plan.returns = source.returns := bound.returnsExact

theorem no_missing_phase_effects {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {deployment : CanonicalCellRegistry.Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {command : Command} {entries : List ResourceMoneyWire.Entry}
    {money : ResourceMoneyReceiver.Prepared deployment durable.snapshot entries}
    {source : NativePlan} (bound : BoundPlan deployment loaded command entries money source) :
    bound.plan.effects.length = source.effects.length + 1 := by
  rw [bound.effectsExact]
  rw [insertMoney_length, BendScalarPlanAdapter.ordered_length bound.ordered]

#assert_axioms decode_identityTerm
#assert_axioms decode_transferTerm
#assert_axioms insertMoney_length
#assert_axioms operations_exact
#assert_axioms returns_exact
#assert_axioms no_missing_phase_effects

theorem original_book_root_exact {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {deployment : CanonicalCellRegistry.Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {command : Command} {entries : List ResourceMoneyWire.Entry}
    {money : ResourceMoneyReceiver.Prepared deployment durable.snapshot entries}
    {source : NativePlan} (bound : BoundPlan deployment loaded command entries money source) :
    source.book.root = durable.snapshot.model.roots (RunComputeBudgetDomain.bookId deployment) :=
  (congrArg ResourceMoneyWire.ApplicationBatch.expectedBookRoot bound.batchExact).trans
    money.financial.rootExact

theorem source_refusal_inert {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (entries : List ResourceMoneyWire.Entry)
    (money : ResourceMoneyReceiver.Prepared deployment durable.snapshot entries)
    {core : BendCoreAdmission.Checked} {initial : BTerm}
    (evaluated : Evaluated core initial) (reason : Nat)
    (refused : evaluated.output = .refused reason) :
    lowerEvaluated deployment loaded command entries money evaluated = none := by
  simp [lowerEvaluated, refused]

#assert_axioms original_book_root_exact
#assert_axioms source_refusal_inert

end Minidregg.Compiler.BendMoneyPlanAdapter
