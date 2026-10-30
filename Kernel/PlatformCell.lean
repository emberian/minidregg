/-
# Kernel.PlatformCell -- STATEMENTS FIRST: the platform cell (GENESIS-COUPLING L1) and the
seed-meter refill (M2), restated after the adversarial audit
(`docs/review/2026-10-27-platform-cell-statements/AUDIT.md`).

Every one of `grainBirthTariff`, `completionCustodianKey`, the `CreationTariff` and the
factory template's `{ownerBudget, lifetime}` sits in `Config.runtimeParameters` or in
`encode template`, hence in the semantics digest every signed request pins: a world born
without one of them cannot acquire it (GENESIS-COUPLING §A, §C L1). The genesis
`meterAllowance` is a lifetime meter every admitted record debits
(`DurableCommitProtocol.preflight`, `insufficientBudget`) and nothing replenishes.

This module holds the statements of both repairs (ATLAS §6 law 2): each keystone is a
`def … : Prop`; beside it stand its satisfiable pole, its teeth and the inhabitation of
its premises, and those poles are proved here because they test the statement, not the
receiver. The keystones themselves are the proof phase's.

Realizer slots (law 1):
* Signatures are read exactly as the deployed verifier answers them: a verdict recorded in
  the deployment's `CredentialSignatureIO.Transcript` (the native verifier's answers, each
  re-verified by `scripts/NativeTranscripts.lean`) under the subject's current enrolled key
  (`Deployment.keyOf`, the authority snapshot). Unforgeability itself is the verifier's, not
  a Lean theorem: the statements are relative to the transcript, and no transcript entry is
  ever invented here.
* `Deployment.holdsInstall` is `capabilityEvidenceChecked` in capability mode
  under the factory's current law (PayBookReceiver's authority).
* The controller is the deployment's `factoryController`; the genesis record is
  `genesisRecord` of the deployment's `NativeHost.Config`, not any valid record.
* `Context.encode current i` is the exact byte string the controller's signature covers
  for an install on `current` (at the receiver: the signed header's frame,
  `SignedEnvelope.frame`, with the command inside it by digest). Those bytes pin
  `Context.source` through a cSHAKE256 digest (`Context.pins`), and `source` covers the
  whole record (`Context.sourceCovers`); so two installs under one signature agree on the
  record, subject and capability or form a `PinCollision` of the two compared source byte
  strings (`Context.binds`). A relay cannot swap a field under a valid signature short of
  that collision.
* Births read the platform record of the image they commit against at the deployed receiver
  (`ResourceBirthReceiver.ReceiverReadsCurrent`); the client quote is
  `ResourceBirth.Descriptor.quotedFee` over that record's creation tariff (`Json.birthCurrent`).
* The meter is `DurableCommitProtocol.Snapshot.available` under the extended install
  (`Snapshot.install` adds `Intent.credit`, default zero, which only the refill family sets;
  `protocol_install_matches`); `Meter.consumed` is `Snapshot.consumed`, and every nullifier carries
  its family tag.
* The meter is unbounded by design: every persisted form of it is ten unbounded naturals
  (`DurableReceiverCodec.chargeStream`), so no fit bound applies to a refill. A future
  fixed-width emitter of `available` carries its own bound at that emitter (audit pass 21).

Known boundaries (recorded by the third audit pass, not closed here):
* the controller may name its OWN key as the first custodian (`CustodianStep none _`), so
  custodian separation begins with the first key a separate party holds;
* `Deployment.host` and `Deployment.genesis` carry no consistency premise between them;
* the install encoding carries no deployment or domain tag: cross-world replay rests on
  `expectedSemantics` in the signed request (`Host/Json.lean:2322`).

Out of this lane: the issuance-cap half of M2 (`wellFloorAmend` on the credit asset's issuer
well, `RealmWellReceiver`): a law-judged cell family, not the commit protocol's meter.
-/
module

public import Kernel.NativeHostGenesis
public import Kernel.NativeHostContext
public import Kernel.DurableCommitProtocol
public import Theory.AxiomPin

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Kernel.PlatformCell

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.IndexedProgram (LawfulCodec)
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHostGenesis (Config FactoryController)
open Minidregg.Kernel.PlatformCellLayout (Platform.valid)

set_option autoImplicit false

theorem lawful_injective {α : Type} (codec : LawfulCodec α) {a b : α}
    (same : codec.encode a = codec.encode b) : a = b := by
  have := congrArg codec.decode same
  rw [codec.decode_encode, codec.decode_encode] at this
  exact Option.some.inj this

/-! ## The deployment -/

structure Deployment where
  host : NativeHost.Config
  genesis : Config
  keyOf : SubjectId → Option (List UInt8)
  holdsInstall : SubjectId → CapabilityId → Bool
  transcript : CredentialSignatureIO.Transcript

def Deployment.controller (d : Deployment) : SubjectId := d.genesis.factoryController.subject

/-- The envelope verifies under `subject`'s current enrolled key over `bytes`: the deployed
verifier recorded that verdict. -/
def Deployment.verifies (d : Deployment) (subject : SubjectId) (bytes envelope : List UInt8) : Bool :=
  match d.keyOf subject with
  | some key => decide ((key, bytes, envelope) ∈ d.transcript.verified)
  | none => false

/-- A raw signature under a public key (the custodian is a key, not an enrolled subject). -/
def Deployment.verifiesKey (d : Deployment) (key bytes signature : List UInt8) : Bool :=
  decide ((key, bytes, signature) ∈ d.transcript.verified)

/-! ## L1: the platform record -/

/-- The record is the platform cell's (`Kernel.PlatformCellLayout.Platform`, with its
`valid`): the spec and the cell carry one type. -/
abbrev Platform := PlatformCellLayout.Platform

/-- The deployment's genesis record: what today's runtime parameters pin. -/
def genesisRecord (host : NativeHost.Config) : Platform :=
  ⟨0, host.tariff, host.grainBirthTariff, host.completionCustodianKey,
    host.template.ownerBudget, host.template.lifetime⟩

structure History where
  genesis : Platform
  installs : List Platform

def History.records (h : History) : List Platform := h.genesis :: h.installs

def History.current (h : History) : Platform := h.records.getLast (List.cons_ne_nil _ _)

def History.push (h : History) (p : Platform) : History := ⟨h.genesis, h.installs ++ [p]⟩

def Sorted (h : History) : Prop := h.records.IsChain (fun a b => a.version < b.version)

/-- An install carries no nonce: replay is refused by the version clause. -/
structure Install where
  next : Platform
  subject : SubjectId
  capability : CapabilityId
  envelope : List UInt8
  /-- The current custodian's signature over the same bytes, when the key rotates. -/
  custodianCosign : Option (List UInt8)
  /-- The last admission height the controller's signature names (signed, the signer's
  choice; the receiver's header `validUntil`). -/
  validUntil : Nat

/-- The digest a signed frame pins its command bytes by. -/
def pinDigest (customization bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash customization bytes).digest

/-- A context: a deployment, the exact bytes its controller signs for an install on a
current record, and the command bytes those signed bytes pin by digest. -/
structure Context where
  deployment : Deployment
  /-- The logical admission height the signed `validUntil` is checked against. -/
  height : Nat
  /-- The bytes the controller's signature (and a custodian's cosignature) covers. -/
  encode : Platform → Install → List UInt8
  /-- The command bytes the signed bytes pin through `pinDigest customization`. -/
  source : Platform → Install → List UInt8
  customization : List UInt8
  pins : ∀ p i j, encode p i = encode p j →
    pinDigest customization (source p i) = pinDigest customization (source p j)
  sourceCovers : ∀ p i j, source p i = source p j →
    i.next = j.next ∧ i.subject = j.subject ∧ i.capability = j.capability

/-- The compared-pair collision event: two different source byte strings under one pin
digest. A fixed-width digest cannot be injective on all byte strings, so binding is stated
with this disjunct over exactly the two strings compared. -/
structure PinCollision (ctx : Context) (p : Platform) (i j : Install) : Prop where
  sourcesDifferent : ctx.source p i ≠ ctx.source p j
  digestsEqual : pinDigest ctx.customization (ctx.source p i) =
    pinDigest ctx.customization (ctx.source p j)

/-- **Binding.** Two installs on one current record that share signed bytes agree on the
record, subject and capability, or their two source strings collide under the pin digest. -/
theorem Context.binds (ctx : Context) (p : Platform) (i j : Install)
    (same : ctx.encode p i = ctx.encode p j) :
    (i.next = j.next ∧ i.subject = j.subject ∧ i.capability = j.capability) ∨
      PinCollision ctx p i j := by
  by_cases sources : ctx.source p i = ctx.source p j
  · exact Or.inl (ctx.sourceCovers p i j sources)
  · exact Or.inr ⟨sources, ctx.pins p i j same⟩

/-- **Custodian separation.** The controller alone may name a first key; rotating a key
needs the CURRENT custodian's signature over the install bytes; dropping a key is refused. -/
def CustodianStep (verifiesKey : List UInt8 → List UInt8 → List UInt8 → Bool)
    (bytes : List UInt8) (cosign : Option (List UInt8)) :
    Option (List UInt8) → Option (List UInt8) → Prop
  | none, _ => True
  | some _, none => False
  | some old, some new => old = new ∨ ∃ s, cosign = some s ∧ verifiesKey old bytes s = true

/-- The admission the platform receiver must decide. -/
def Admits (ctx : Context) (h : History) (i : Install) : Prop :=
  i.subject = ctx.deployment.controller ∧
    ctx.deployment.verifies ctx.deployment.controller (ctx.encode h.current i) i.envelope = true ∧
    ctx.deployment.holdsInstall ctx.deployment.controller i.capability = true ∧
    h.current.version < i.next.version ∧
    i.next.valid = true ∧
    CustodianStep ctx.deployment.verifiesKey (ctx.encode h.current i) i.custodianCosign
      h.current.completionCustodianKey i.next.completionCustodianKey ∧
    ctx.height ≤ i.validUntil

/-- The cell's reachable histories: the deployment's genesis record, then admitted installs. -/
inductive Reachable (ctx : Context) : History → Prop
  | genesis (valid : (genesisRecord ctx.deployment.host).valid = true) :
      Reachable ctx ⟨genesisRecord ctx.deployment.host, []⟩
  | install (h : History) (i : Install) (prior : Reachable ctx h) (admitted : Admits ctx h i) :
      Reachable ctx (h.push i.next)

/-! ### Keystones (proof phase) -/

/-- **L1-a, the invariant:** admitting an install keeps the history sorted. -/
def StaysSorted (ctx : Context) : Prop :=
  ∀ h i, Sorted h → Admits ctx h i → Sorted (h.push i.next)

/-- **L1-a, the consequence:** every reachable history is sorted, and an admitted install is
above EVERY earlier record (so a replayed install is refused). -/
def VersionMonotone (ctx : Context) : Prop :=
  (∀ h, Reachable ctx h → Sorted h) ∧
    ∀ h i, Reachable ctx h → Admits ctx h i → ∀ p ∈ h.records, p.version < i.next.version

/-- **L1-b:** every record of a reachable history is valid. -/
def RecordsValid (ctx : Context) : Prop :=
  ∀ h, Reachable ctx h → ∀ p ∈ h.records, p.valid = true

/-- **L1-c, at the receiver:** `decide` decides exactly `Admits`; whatever it admits was
signed by the controller's key and presented the held capability. -/
def Decides (ctx : Context) (decide : History → Install → Bool) : Prop :=
  ∀ h i, decide h i = true ↔ Admits ctx h i

def ReceiverAuthenticated (ctx : Context) (decide : History → Install → Bool) : Prop :=
  ∀ h i, decide h i = true →
    ctx.deployment.verifies ctx.deployment.controller (ctx.encode h.current i) i.envelope = true ∧
      ctx.deployment.holdsInstall ctx.deployment.controller i.capability = true

/-! ### Proofs of L1-a, L1-b, L1-c -/

theorem records_push (h : History) (p : Platform) : (h.push p).records = h.records ++ [p] := by
  simp [History.push, History.records]

theorem current_push (h : History) (p : Platform) : (h.push p).current = p := by
  simp [History.current, records_push]

/-- Every record of a sorted list is at or below its last. -/
theorem chain_le_last : ∀ (l : List Platform) (ne : l ≠ []),
    l.IsChain (fun a b => a.version < b.version) → ∀ p ∈ l, p.version ≤ (l.getLast ne).version
  | [], ne, _, _, _ => absurd rfl ne
  | [a], _, _, p, mem => by
      simp at mem
      subst mem
      simp
  | a :: b :: t, _, chain, p, mem => by
      have ih := chain_le_last (b :: t) (List.cons_ne_nil _ _) (List.isChain_of_isChain_cons chain)
      rw [List.getLast_cons_cons]
      rcases List.mem_cons.mp mem with same | rest
      · subst same
        exact Nat.le_of_lt (Nat.lt_of_lt_of_le (List.rel_of_isChain_cons_cons (R := fun a b : Platform => a.version < b.version) chain) (ih b (by simp)))
      · exact ih p rest

theorem staysSorted (ctx : Context) : StaysSorted ctx := by
  intro h i sorted admitted
  unfold Sorted at *
  rw [records_push, List.isChain_append]
  refine ⟨sorted, List.isChain_singleton _, ?_⟩
  intro x last y first
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at first
  subst first
  rw [show h.records.getLast? = some h.current from
    List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil _ _)] at last
  simp only [Option.mem_def, Option.some.injEq] at last
  subst last
  exact admitted.2.2.2.1

theorem reachable_sorted (ctx : Context) (h : History) (reachable : Reachable ctx h) : Sorted h := by
  induction reachable with
  | genesis _ => exact List.isChain_singleton _
  | install h i _ admitted ih => exact staysSorted ctx h i ih admitted

theorem versionMonotone (ctx : Context) : VersionMonotone ctx := by
  refine ⟨reachable_sorted ctx, ?_⟩
  intro h i reachable admitted p member
  exact Nat.lt_of_le_of_lt (chain_le_last h.records (List.cons_ne_nil _ _)
    (reachable_sorted ctx h reachable) p member) admitted.2.2.2.1

theorem recordsValid (ctx : Context) : RecordsValid ctx := by
  intro h reachable
  induction reachable with
  | genesis valid =>
      intro p member
      simp [History.records] at member
      subst member
      exact valid
  | install h i _ admitted ih =>
      intro p member
      rw [records_push, List.mem_append] at member
      rcases member with old | new
      · exact ih p old
      · simp at new
        subst new
        exact admitted.2.2.2.2.1

/-- The custodian rule as the receiver checks it. -/
def custodianCheck (verifiesKey : List UInt8 → List UInt8 → List UInt8 → Bool)
    (bytes : List UInt8) (cosign : Option (List UInt8)) :
    Option (List UInt8) → Option (List UInt8) → Bool
  | none, _ => true
  | some _, none => false
  | some old, some new => decide (old = new) ||
      (match cosign with | some s => verifiesKey old bytes s | none => false)

theorem custodianCheck_iff (verifiesKey : List UInt8 → List UInt8 → List UInt8 → Bool)
    (bytes : List UInt8) (cosign : Option (List UInt8)) (old new : Option (List UInt8)) :
    custodianCheck verifiesKey bytes cosign old new = true ↔
      CustodianStep verifiesKey bytes cosign old new := by
  rcases old with _ | o <;> rcases new with _ | n <;>
    simp only [custodianCheck, CustodianStep, Bool.or_eq_true, decide_eq_true_eq] <;>
    try simp
  rcases cosign with _ | c <;> simp

/-- The reference admission the platform receiver runs. -/
def decideInstall (ctx : Context) (h : History) (i : Install) : Bool :=
  decide (i.subject = ctx.deployment.controller) &&
    ctx.deployment.verifies ctx.deployment.controller (ctx.encode h.current i) i.envelope &&
    ctx.deployment.holdsInstall ctx.deployment.controller i.capability &&
    decide (h.current.version < i.next.version) &&
    i.next.valid &&
    custodianCheck ctx.deployment.verifiesKey (ctx.encode h.current i) i.custodianCosign
      h.current.completionCustodianKey i.next.completionCustodianKey &&
    decide (ctx.height ≤ i.validUntil)

/-- **L1-c proved for the reference receiver.** -/
theorem decideInstall_decides (ctx : Context) : Decides ctx (decideInstall ctx) := by
  intro h i
  simp only [decideInstall, Bool.and_eq_true, decide_eq_true_eq, custodianCheck_iff, Admits,
    and_assoc]

theorem decides_authenticated (ctx : Context) (decide : History → Install → Bool)
    (decides : Decides ctx decide) : ReceiverAuthenticated ctx decide := by
  intro h i admitted
  have := (decides h i).mp admitted
  exact ⟨this.2.1, this.2.2.1⟩

/-! ### L1-d and L1-e: births read the platform of the store they commit against

Stated at the deployed receiver, where the birth is admitted:
`ResourceBirthReceiver.ReceiverReadsCurrent` (the record of the committed image prices the
birth, bounds its fee, binds its owner budget and lifetime, and is read-guarded), with
`unpriced_empty` and `stale_unadmitted`. A store-only `terms` function here would hold by
`rfl` and constrain no deployed reader, so none is stated. -/

/-! ### Poles of L1 -/

abbrev InstallWire :=
  Nat × (Nat × Nat × Nat × Nat × Nat × Nat) × Option (Nat × Nat) × Option (List UInt8) ×
    Nat × Nat × Nat × Nat

def installStream : StreamCodec InstallWire :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))
      (StreamCodec.product (StreamCodec.option (StreamCodec.product StreamCodec.nat StreamCodec.nat))
        (StreamCodec.product (StreamCodec.option bytesStream)
          (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
            (StreamCodec.product StreamCodec.nat StreamCodec.nat))))))

def installWire (i : Install) : InstallWire :=
  (i.next.version, (i.next.creation.base, i.next.creation.perBirth, i.next.creation.perGrant,
    i.next.creation.perInitialPayloadByte, i.next.creation.collector, i.next.creation.asset),
    i.next.grainBirth.map (fun g => (g.base, g.perBirth)), i.next.completionCustodianKey,
    i.next.ownerBudget, i.next.lifetime, i.subject.value, i.capability.value)

theorem installWire_covers (i j : Install) (same : installWire i = installWire j) :
    i.next = j.next ∧ i.subject = j.subject ∧ i.capability = j.capability := by
  rcases i with ⟨⟨v, ⟨a, b, c, d, e, f⟩, g, k, o, l⟩, ⟨s⟩, ⟨cap⟩, _, _, _⟩
  rcases j with ⟨⟨v', ⟨a', b', c', d', e', f'⟩, g', k', o', l'⟩, ⟨s'⟩, ⟨cap'⟩, _, _, _⟩
  rcases g with _ | ⟨gb, gp⟩ <;> rcases g' with _ | ⟨gb', gp'⟩ <;>
    simp_all [installWire]

/-- A codec that covers the whole record: the canonical stream of every field. -/
def wireEncode (i : Install) : List UInt8 := (StreamCodec.toLawful installStream).encode (installWire i)

theorem wireEncode_covers (i j : Install) (same : wireEncode i = wireEncode j) :
    i.next = j.next ∧ i.subject = j.subject ∧ i.capability = j.capability :=
  installWire_covers i j (lawful_injective _ same)

/-- A deployment for the poles: the controller's key is `key`, it holds every capability,
and the transcript records exactly the listed verdicts. -/
def toyDeployment (host : NativeHost.Config) (genesis : Config) (key : List UInt8)
    (verified : List (List UInt8 × List UInt8 × List UInt8)) : Deployment where
  host := host
  genesis := genesis
  keyOf s := if s = genesis.factoryController.subject then some key else none
  holdsInstall s _ := decide (s = genesis.factoryController.subject)
  transcript := ⟨verified⟩

def toyContext (d : Deployment) : Context where
  deployment := d
  height := 0
  encode _ := wireEncode
  source _ := wireEncode
  customization := []
  pins _ _ _ same := congrArg (pinDigest []) same
  sourceCovers _ := wireEncode_covers

/-- The controller's install of `next`, with envelope `env`. -/
def installOf (genesis : Config) (next : Platform) (env : List UInt8) : Install :=
  ⟨next, genesis.factoryController.subject, ⟨0⟩, env, none, 0⟩

/-- The verdict a signed install needs in the transcript. -/
def verdictFor (key : List UInt8) (genesis : Config) (next : Platform) (env : List UInt8) :
    List UInt8 × List UInt8 × List UInt8 := (key, wireEncode (installOf genesis next env), env)

theorem toy_admits (host : NativeHost.Config) (genesis : Config) (key env : List UInt8)
    (verified : List (List UInt8 × List UInt8 × List UInt8)) (h : History)
    (recorded : verdictFor key genesis { h.current with version := h.current.version + 1 } env ∈ verified)
    (valid : h.current.valid = true) :
    Admits (toyContext (toyDeployment host genesis key verified)) h
      (installOf genesis { h.current with version := h.current.version + 1 } env) := by
  refine ⟨rfl, ?_, ?_, by simp [installOf], ?_, ?_, by simp [toyContext, installOf]⟩
  · simp only [toyContext, Deployment.verifies, Deployment.controller, toyDeployment, if_pos rfl]
    exact decide_eq_true recorded
  · simp [toyContext, toyDeployment, Deployment.controller]
  · exact valid
  · simp only [installOf]
    cases h.current.completionCustodianKey with
    | none => trivial
    | some k => exact Or.inl rfl

/-- Premise inhabitation: for every deployment whose genesis record is valid, a reachable
two-record history with an admitted install on it exists. -/
theorem premises_inhabited (host : NativeHost.Config) (genesis : Config) (key : List UInt8)
    (valid : (genesisRecord host).valid = true) :
    ∃ verified h i, Reachable (toyContext (toyDeployment host genesis key verified)) h ∧
      2 ≤ h.records.length ∧ Admits (toyContext (toyDeployment host genesis key verified)) h i := by
  let g := genesisRecord host
  let r1 : Platform := { g with version := g.version + 1 }
  let h1 : History := ⟨g, [r1]⟩
  have cur1 : h1.current = r1 := rfl
  let r2 : Platform := { h1.current with version := h1.current.version + 1 }
  let verified := [verdictFor key genesis r1 [1], verdictFor key genesis r2 [2]]
  have g0 : Reachable (toyContext (toyDeployment host genesis key verified)) ⟨g, []⟩ :=
    .genesis valid
  have first := toy_admits host genesis key [1] verified ⟨g, []⟩ (by simp [verified, r1, History.current, History.records]) valid
  refine ⟨verified, h1, installOf genesis r2 [2], .install _ _ g0 first, by simp [h1, History.records], ?_⟩
  exact toy_admits host genesis key [2] verified h1 (by simp [verified, r2])
    (by rw [cur1]; simpa [r1, Platform.valid] using valid)

/-- Teeth: a request whose envelope the verifier did not record under the controller's key
is refused, whatever its subject field says. -/
theorem forged_refused (ctx : Context) (h : History) (i : Install)
    (forged : ctx.deployment.verifies ctx.deployment.controller (ctx.encode h.current i) i.envelope = false) :
    ¬ Admits ctx h i := by
  rintro ⟨-, verified, -⟩
  simp [forged] at verified

/-- Teeth (relay swap): with the codec covering the record, a relay that keeps the
controller's envelope and changes any field of the record is refused, because the verdict
was recorded for the original bytes only. -/
theorem relay_swap_refused (host : NativeHost.Config) (genesis : Config) (key env : List UInt8)
    (h : History) (next swapped : Platform) (differs : swapped ≠ next) :
    ¬ Admits (toyContext (toyDeployment host genesis key [verdictFor key genesis next env])) h
      (installOf genesis swapped env) := by
  apply forged_refused
  have ne : wireEncode (installOf genesis swapped env) ≠ wireEncode (installOf genesis next env) :=
    fun same => differs (wireEncode_covers _ _ same).1
  simp [toyContext, Deployment.verifies, Deployment.controller, toyDeployment, verdictFor, ne]

/-- Teeth: a receiver that trusts the subject field (no signature check) does not decide
`Admits`. -/
def trustsSubjectField (ctx : Context) (h : History) (i : Install) : Bool :=
  decide (i.subject = ctx.deployment.controller) &&
    decide (h.current.version < i.next.version) && i.next.valid

theorem trustsSubjectField_not_decides (host : NativeHost.Config) (genesis : Config)
    (key : List UInt8) (valid : (genesisRecord host).valid = true) :
    ¬ Decides (toyContext (toyDeployment host genesis key []))
      (trustsSubjectField (toyContext (toyDeployment host genesis key []))) := by
  intro decides
  let h : History := ⟨genesisRecord host, []⟩
  let i := installOf genesis { h.current with version := h.current.version + 1 } []
  have admitted := (decides h i).mp (by
    simp only [trustsSubjectField, i, installOf, toyContext, Deployment.controller,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨rfl, Nat.lt_succ_self _⟩, by
      exact valid⟩)
  exact forged_refused _ _ _ (by
    simp [toyContext, Deployment.verifies, Deployment.controller, toyDeployment]) admitted

/-- Teeth: a signature past its `validUntil` at the admission height is refused (the envelope
controller's expiry, `CredentialSignedEnvelopeController.prepare`). -/
theorem expired_refused (ctx : Context) (h : History) (i : Install)
    (expired : i.validUntil < ctx.height) : ¬ Admits ctx h i :=
  fun admitted => absurd admitted.2.2.2.2.2.2 (Nat.not_le.mpr expired)

theorem stale_version_refused (ctx : Context) (h : History) (i : Install)
    (stale : i.next.version ≤ h.current.version) : ¬ Admits ctx h i :=
  fun admitted => absurd admitted.2.2.2.1 (Nat.not_lt.mpr stale)

theorem invalid_refused (ctx : Context) (h : History) (i : Install) (invalid : i.next.valid = false) :
    ¬ Admits ctx h i := by
  rintro ⟨-, -, -, -, valid, -⟩
  simp [invalid] at valid

theorem zero_lifetime_invalid (p : Platform) (zero : p.lifetime = 0) : p.valid = false := by
  simp [Platform.valid, zero]

/-- Teeth: a named custodian key is never dropped. -/
theorem custodian_drop_refused (ctx : Context) (h : History) (i : Install) (key : List UInt8)
    (named : h.current.completionCustodianKey = some key)
    (dropped : i.next.completionCustodianKey = none) : ¬ Admits ctx h i := by
  rintro ⟨-, -, -, -, -, step, -⟩
  rw [named, dropped] at step
  exact step

/-- Teeth: a rotation (`some a → some b`, `a ≠ b`) without the custodian's cosignature is
refused. -/
theorem uncosigned_rotation_refused (ctx : Context) (h : History) (i : Install) (a b : List UInt8)
    (named : h.current.completionCustodianKey = some a)
    (rotated : i.next.completionCustodianKey = some b) (differs : a ≠ b)
    (uncosigned : i.custodianCosign = none) : ¬ Admits ctx h i := by
  rintro ⟨-, -, -, -, -, step, -⟩
  rw [named, rotated] at step
  rcases step with same | ⟨s, cosigned, -⟩
  · exact differs same
  · rw [uncosigned] at cosigned; cases cosigned

/-- Satisfiable: a rotation cosigned by the current custodian is admitted. -/
theorem cosigned_rotation_admitted (host : NativeHost.Config) (genesis : Config)
    (key env old new cosig : List UInt8) (h : History) (next : Platform)
    (named : h.current.completionCustodianKey = some old)
    (nextKey : next.completionCustodianKey = some new)
    (above : h.current.version < next.version) (valid : next.valid = true) :
    Admits (toyContext (toyDeployment host genesis key
      [(key, wireEncode ⟨next, genesis.factoryController.subject, ⟨0⟩, env, some cosig, 0⟩, env),
       (old, wireEncode ⟨next, genesis.factoryController.subject, ⟨0⟩, env, some cosig, 0⟩, cosig)]))
      h ⟨next, genesis.factoryController.subject, ⟨0⟩, env, some cosig, 0⟩ := by
  refine ⟨rfl, ?_, ?_, above, valid, ?_, by simp [toyContext]⟩
  · simp [toyContext, Deployment.verifies, Deployment.controller, toyDeployment]
  · simp [toyContext, toyDeployment, Deployment.controller]
  · simp only [toyContext, named, nextKey]
    exact Or.inr ⟨cosig, rfl, by simp [Deployment.verifiesKey, toyDeployment]⟩

/-- Teeth: `Sorted` is load-bearing. On the unsorted record list `[5, 1]` an install at 2
is admitted although it is not above 5, so `VersionMonotone` needs reachability. -/
theorem sorted_load_bearing (host : NativeHost.Config) (genesis : Config) (key : List UInt8)
    (base : Platform) (valid : base.valid = true) :
    let h : History := ⟨{ base with version := 5 }, [{ base with version := 1 }]⟩
    let next : Platform := { h.current with version := h.current.version + 1 }
    Admits (toyContext (toyDeployment host genesis key [verdictFor key genesis next []])) h
        (installOf genesis next []) ∧
      ¬ ∀ p ∈ h.records, p.version < next.version := by
  intro h next
  refine ⟨toy_admits host genesis key [] _ h (by simp [next]) (by simpa [h, History.current,
    History.records, Platform.valid] using valid), ?_⟩
  intro above
  have := above { base with version := 5 } (by simp [h, History.records])
  simp [next, h, History.current, History.records] at this

/-! ## M2: the seed-meter refill

The meter is the commit protocol's `Snapshot.available`, not a cell. `install` sets
`available := available - exactCharge + credit` with `Intent.credit` (default zero), and
`installAvailable` below is that install's meter as a spec.
Only the refill family sets a nonzero credit; its exact charge is zero (a nullifier-only
intent, which `preflight` admits), so it is admitted at an exhausted meter.

The keystones are the deployed ones (audit pass 21 addendum): M2-c is
`MeterRefillReceiver.AcceptedRefill.sound` with `intent_install_refilled`, M2-b is
`NativeHostReplay.NativeAdmission.credit_confined`, M2-d is `protocol_install_matches`
below. This section keeps the meter's shape (`Refill`, `refilled`, `installAvailable`) that
they are read against. -/

inductive Family
  | meterRefill
  | platformInstall
  | other (tag : Nat)
  deriving DecidableEq, Repr

/-- Durable nullifiers carry their family, so families never collide. -/
structure Nullifier where
  family : Family
  subject : SubjectId
  nonce : Nat
  deriving DecidableEq, Repr

/-- What the meter reads of a commit-protocol intent, with the proof phase's credit. -/
structure MeterIntent where
  family : Family
  exactCharge : ResourceCost.Charge
  credit : ResourceCost.Charge
  nullifiers : List Nullifier

/-- The extended install's meter. -/
def installAvailable (available : ResourceCost.Charge) (intent : MeterIntent) : ResourceCost.Charge :=
  fun lane => available lane - intent.exactCharge lane + intent.credit lane

/-- **M2-a, conservation with credit** (the extended `install_exact_debit`): a funded
install debits the charge and adds the credit, exactly. -/
theorem install_conserves_with_credit (available : ResourceCost.Charge) (intent : MeterIntent)
    (funded : intent.exactCharge ≤ available) :
    intent.exactCharge + installAvailable available intent = available + intent.credit := by
  funext lane
  change intent.exactCharge lane + (available lane - intent.exactCharge lane + intent.credit lane) =
    available lane + intent.credit lane
  have := (ResourceCost.Charge.le_iff _ _).mp funded lane
  omega

/-- Teeth: today's install (credit ignored) does not conserve a positive credit. -/
def installToday (available : ResourceCost.Charge) (intent : MeterIntent) : ResourceCost.Charge :=
  fun lane => available lane - intent.exactCharge lane

theorem installToday_loses_credit (available : ResourceCost.Charge) (intent : MeterIntent)
    (funded : intent.exactCharge ≤ available)
    (lane : ResourceCost.Lane) (positive : 0 < intent.credit lane) :
    intent.exactCharge + installToday available intent ≠ available + intent.credit := by
  intro same
  have := congrFun same lane
  change intent.exactCharge lane + (available lane - intent.exactCharge lane) =
    available lane + intent.credit lane at this
  have := (ResourceCost.Charge.le_iff _ _).mp funded lane
  omega

structure Refill where
  subject : SubjectId
  capability : CapabilityId
  nonce : Nat
  envelope : List UInt8
  amount : ResourceCost.Charge

def Refill.nullifier (r : Refill) : Nullifier := ⟨.meterRefill, r.subject, r.nonce⟩

/-- The refill's intent: no charge, the posting as credit, one tagged nullifier. -/
def Refill.intent (r : Refill) : MeterIntent := ⟨.meterRefill, 0, r.amount, [r.nullifier]⟩

def raised (remaining amount : ResourceCost.Charge) : ResourceCost.Charge :=
  fun lane => remaining lane + amount lane

theorem installAvailable_refill (remaining : ResourceCost.Charge) (r : Refill) :
    installAvailable remaining r.intent = raised remaining r.amount := by
  funext lane
  simp [installAvailable, Refill.intent, raised]

/-- The meter as the commit protocol holds it. -/
structure Meter where
  remaining : ResourceCost.Charge
  consumed : Nullifier → Bool

/-- The post-state of an admitted refill: the extended install of its intent. -/
def refilled (m : Meter) (r : Refill) : Meter :=
  ⟨installAvailable m.remaining r.intent, fun n => decide (n = r.nullifier) || m.consumed n⟩

/-- Liveness: the refill's zero charge is funded by an exhausted meter. -/
theorem refill_funded_at_exhaustion (r : Refill) :
    ResourceCost.Charge.fundedCheck r.intent.exactCharge 0 = true := by
  simp [Refill.intent]

/-- Teeth of the exemption: charged like an ordinary record, a refill is refused at the
exhausted meter. -/
theorem charged_refill_refused_at_exhaustion (c : ResourceCost.Charge)
    (positive : 0 < c .turnBytes) : ResourceCost.Charge.fundedCheck c 0 = false := by
  cases h : ResourceCost.Charge.fundedCheck c 0 with
  | false => rfl
  | true =>
      have := ((ResourceCost.Charge.fundedCheck_eq_true_iff c 0).mp h) .turnBytes
      simp at this; omega

/-- The family tag separates: another family's nullifier on the same subject and nonce is
not the refill's. -/
theorem family_tag_separates (r : Refill) (family : Family) (other : family ≠ .meterRefill) :
    r.nullifier ≠ ⟨family, r.subject, r.nonce⟩ := by
  intro same
  exact other (congrArg Nullifier.family same).symm

/-! ## M2: the copy is the protocol's install

`installAvailable`, `Meter` and the tagged `Nullifier` are the SPEC; the protocol is
`DurableCommitProtocol.Snapshot.install`, instantiated at the tagged `Nullifier`, which
carries `Intent.credit`. The protocol's install equals the spec at every credit
(`protocol_install_matches`, keystone M2-d), and then a refill's meter IS the protocol's
post-state (`refilled_is_protocol_install`). -/

def meterIntentOf {TxId CellId Event : Type} (family : Family) (credit : ResourceCost.Charge)
    (intent : DurableCommitProtocol.Intent TxId CellId Nullifier Event) : MeterIntent :=
  ⟨family, intent.exactCharge, credit, intent.nullifiers⟩

def meterOf {TxId CellId Event : Type}
    (snapshot : DurableCommitProtocol.Snapshot TxId CellId Nullifier Event) : Meter :=
  ⟨snapshot.available, snapshot.consumed⟩

theorem protocol_install_consumed {TxId CellId Event : Type} [DecidableEq CellId]
    (before : DurableCommitProtocol.Snapshot TxId CellId Nullifier Event)
    (intent : DurableCommitProtocol.Intent TxId CellId Nullifier Event) :
    (DurableCommitProtocol.Snapshot.install before intent).consumed =
      fun n => decide (n ∈ intent.nullifiers) || before.consumed n := by
  funext n
  by_cases member : n ∈ intent.nullifiers <;>
    simp [DurableCommitProtocol.Snapshot.install, member]

/-- **M2-d, the proof phase's install is the spec.** `installed` is a protocol meter,
`creditOf` the credit it reads off an intent. -/
def ProtocolInstallMatches {TxId CellId Event : Type}
    (installed : DurableCommitProtocol.Snapshot TxId CellId Nullifier Event →
      DurableCommitProtocol.Intent TxId CellId Nullifier Event → ResourceCost.Charge)
    (creditOf : DurableCommitProtocol.Intent TxId CellId Nullifier Event → ResourceCost.Charge) :
    Prop :=
  ∀ before intent family,
    installed before intent = installAvailable before.available (meterIntentOf family (creditOf intent) intent)

/-- **Keystone M2-d, discharged.** The deployed install, `Snapshot.install`, is the spec's
extended install at the intent's own `credit`. -/
theorem protocol_install_matches {TxId CellId Event : Type} [DecidableEq CellId] :
    ProtocolInstallMatches (TxId := TxId) (CellId := CellId) (Event := Event)
      (fun before intent => (DurableCommitProtocol.Snapshot.install before intent).available)
      (·.credit) := by
  intro before intent family
  funext lane
  simp [DurableCommitProtocol.Snapshot.install, installAvailable, meterIntentOf]

/-- The install before M2 (no credit): the teeth's reference. -/
def installUncredited {TxId CellId Event : Type}
    (before : DurableCommitProtocol.Snapshot TxId CellId Nullifier Event)
    (intent : DurableCommitProtocol.Intent TxId CellId Nullifier Event) : ResourceCost.Charge :=
  fun lane => before.available lane - intent.exactCharge lane

/-- Satisfiable: the uncredited install matches the spec when no intent carries credit. -/
theorem uncredited_install_matches_zero {TxId CellId Event : Type} :
    ProtocolInstallMatches (TxId := TxId) (CellId := CellId) (Event := Event)
      installUncredited (fun _ => 0) := by
  intro before intent family
  funext lane
  simp [installUncredited, installAvailable, meterIntentOf]

/-- Teeth: the uncredited install does not match once any funded intent carries a credit,
so the refill needs the protocol extension, not a second meter. -/
theorem uncredited_install_mismatch_with_credit {TxId CellId Event : Type}
    (creditOf : DurableCommitProtocol.Intent TxId CellId Nullifier Event → ResourceCost.Charge)
    (before : DurableCommitProtocol.Snapshot TxId CellId Nullifier Event)
    (intent : DurableCommitProtocol.Intent TxId CellId Nullifier Event)
    (lane : ResourceCost.Lane) (positive : 0 < creditOf intent lane)
    (funded : intent.exactCharge ≤ before.available) :
    ¬ ProtocolInstallMatches installUncredited creditOf := by
  intro agrees
  have := congrFun (agrees before intent .meterRefill) lane
  have le := (ResourceCost.Charge.le_iff _ _).mp funded lane
  simp [installUncredited, installAvailable, meterIntentOf] at this
  omega

/-- The link: under a matching install, a refill's protocol intent (no charge, the posting
as credit, its one tagged nullifier) leaves exactly `refilled`. -/
theorem refilled_is_protocol_install {TxId CellId Event : Type} [DecidableEq CellId]
    (installed : DurableCommitProtocol.Snapshot TxId CellId Nullifier Event →
      DurableCommitProtocol.Intent TxId CellId Nullifier Event → ResourceCost.Charge)
    (creditOf : DurableCommitProtocol.Intent TxId CellId Nullifier Event → ResourceCost.Charge)
    (agrees : ProtocolInstallMatches installed creditOf)
    (before : DurableCommitProtocol.Snapshot TxId CellId Nullifier Event)
    (intent : DurableCommitProtocol.Intent TxId CellId Nullifier Event) (r : Refill)
    (free : intent.exactCharge = 0) (credited : creditOf intent = r.amount)
    (single : intent.nullifiers = [r.nullifier]) :
    (⟨installed before intent, (DurableCommitProtocol.Snapshot.install before intent).consumed⟩ : Meter) =
      refilled (meterOf before) r := by
  have available := agrees before intent .meterRefill
  have consumed := protocol_install_consumed before intent
  simp only [refilled, meterOf, available, consumed, single]
  congr 1
  · funext lane
    simp [installAvailable, meterIntentOf, free, credited, Refill.intent]
  · funext n
    simp

/-- The deployed instance of the link: the protocol's own install of a refill's intent is
`refilled`. -/
theorem refilled_is_deployed_install {TxId CellId Event : Type} [DecidableEq CellId]
    (before : DurableCommitProtocol.Snapshot TxId CellId Nullifier Event)
    (intent : DurableCommitProtocol.Intent TxId CellId Nullifier Event) (r : Refill)
    (free : intent.exactCharge = 0) (credited : intent.credit = r.amount)
    (single : intent.nullifiers = [r.nullifier]) :
    meterOf (DurableCommitProtocol.Snapshot.install before intent) = refilled (meterOf before) r :=
  refilled_is_protocol_install _ _ protocol_install_matches before intent r free credited single

#assert_axioms expired_refused
#assert_axioms lawful_injective installWire_covers wireEncode_covers toy_admits premises_inhabited
  forged_refused relay_swap_refused trustsSubjectField_not_decides stale_version_refused
  invalid_refused zero_lifetime_invalid custodian_drop_refused uncosigned_rotation_refused
  cosigned_rotation_admitted sorted_load_bearing
  install_conserves_with_credit installToday_loses_credit
  installAvailable_refill refill_funded_at_exhaustion
  charged_refill_refused_at_exhaustion family_tag_separates
  protocol_install_consumed protocol_install_matches uncredited_install_matches_zero
  uncredited_install_mismatch_with_credit refilled_is_protocol_install refilled_is_deployed_install
  records_push current_push chain_le_last staysSorted reachable_sorted versionMonotone recordsValid
  custodianCheck_iff decideInstall_decides decides_authenticated

end Minidregg.Kernel.PlatformCell
