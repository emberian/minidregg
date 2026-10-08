# Clock v2 objective contract review

Source: 0ea31db53c; definitions changed by 93e18aac. Draft j480136033 passed all manifest/self-tests. The 7466 redefinitions propagate the clock v2 namespace/codec, bound-aware receiver and explicit genesis configuration. No removed rows or axiom-set changes.

load_exact domain approval requires missing/non-positive bounds be refused by the named receiving check: Kernel.ClockCellDomain.load matches maxStepOf; none returns none; some bound is admitted only by `if positive : 0 < bound`, otherwise none. The private Loaded witness carries boundExact and boundPositive.

## All 24 restated rows: verbatim elaborated old/new text and disposition

There are eight theorem rows (Prepared.decided is a proof projection), sixteen definition/constructor rows. All belong to 93e18aac; no new axioms.

theorem Minidregg.Kernel.ClockCell.genesis_clock
  old statement: Minidregg.Kernel.ClockCell.clockOf Minidregg.Kernel.ClockCell.genesisStore = Option.some Minidregg.Kernel.ClockCell.genesisClock
  new statement: ∀ (genesisNow maxStepSeconds : ℕ), Minidregg.Kernel.ClockCell.clockOf (Minidregg.Kernel.ClockCell.genesisStore genesisNow maxStepSeconds) = Option.some { now := genesisNow, slot := 0 }
OK stronger/generalized: arbitrary genesis time/bound; time=0 recovers old clock projection, bound entry does not change clock slot.

theorem Minidregg.Kernel.ClockCell.genesis_law
  old statement: Minidregg.Kernel.ClockCell.Law Minidregg.Kernel.ClockCell.genesisStore
  new statement: ∀ (genesisNow maxStepSeconds : ℕ), Minidregg.Kernel.ClockCell.Law (Minidregg.Kernel.ClockCell.genesisStore genesisNow maxStepSeconds)
OK stronger/generalized: Law for all genesis inputs, including previous zero-clock case.

theorem Minidregg.Kernel.ClockCellDomain.load_exact
  old statement: ∀ (deployment : Minidregg.Compiler.CanonicalCellRegistry.Deployment) (physical : Minidregg.Kernel.ClockCellDomain.PhysicalSnapshot) (cell : Minidregg.Kernel.ClockCell.Cell) (clock : Minidregg.Kernel.ClockCell.Clock), physical.canonicalBytes (Minidregg.Kernel.ClockCellDomain.cellIdOf deployment) = Minidregg.Kernel.ClockCellDomain.cellBytes cell → Minidregg.Kernel.ClockCell.clockOf cell.logical = Option.some clock → ∃ loaded, Minidregg.Kernel.ClockCellDomain.load deployment physical = Option.some loaded ∧ loaded.cell = cell ∧ loaded.clock = clock
  new statement: ∀ (deployment : Minidregg.Compiler.CanonicalCellRegistry.Deployment) (physical : Minidregg.Kernel.ClockCellDomain.PhysicalSnapshot) (cell : Minidregg.Kernel.ClockCell.Cell) (clock : Minidregg.Kernel.ClockCell.Clock), physical.canonicalBytes (Minidregg.Kernel.ClockCellDomain.cellIdOf deployment) = Minidregg.Kernel.ClockCellDomain.cellBytes cell → Minidregg.Kernel.ClockCell.clockOf cell.logical = Option.some clock → ∀ (bound : ℕ), Minidregg.Kernel.ClockCell.maxStepOf cell.logical = Option.some bound → 0 < bound → ∃ loaded, Minidregg.Kernel.ClockCellDomain.load deployment physical = Option.some loaded ∧ loaded.cell = cell ∧ loaded.clock = clock ∧ loaded.maxStepSeconds = bound
OK under deputy a122 v2 flag day: load rejects maxStepOf=none or non-positive bound; new premises are exactly required of every loadable cell; old exact cell/clock conclusions retained and bound exactness added.

theorem Minidregg.Kernel.ClockTickReceiver.Prepared.decided
  old statement: ∀ {F : Type} [inst : Field F] {deployment : Minidregg.Kernel.ClockTickReceiver.Deployment} {profile : Minidregg.Compiler.CanonicalRuntimeProfile.Profile F} {ambient : Minidregg.Kernel.ClockTickReceiver.Ambient} {durable : Minidregg.Kernel.ClockTickReceiver.Durable} {command : Minidregg.Kernel.ClockTickReceiver.Command} (self : Minidregg.Kernel.ClockTickReceiver.Prepared deployment profile ambient durable command), Minidregg.Kernel.ClockTickReceiver.decideTick self.clock.clock command.tick = Except.ok self.plan
  new statement: ∀ {F : Type} [inst : Field F] {deployment : Minidregg.Kernel.ClockTickReceiver.Deployment} {profile : Minidregg.Compiler.CanonicalRuntimeProfile.Profile F} {ambient : Minidregg.Kernel.ClockTickReceiver.Ambient} {durable : Minidregg.Kernel.ClockTickReceiver.Durable} {command : Minidregg.Kernel.ClockTickReceiver.Command} (self : Minidregg.Kernel.ClockTickReceiver.Prepared deployment profile ambient durable command), Minidregg.Kernel.ClockTickReceiver.decideTick self.clock.maxStepSeconds self.clock.clock command.tick = Except.ok self.plan
OK stronger: prepared witness certifies bound-aware decision at the exact loaded cell bound; advancement requirement preserved.

theorem Minidregg.Kernel.ClockTickReceiver.clock_monotone
  old statement: ∀ {F : Type} [inst : Field F] {deployment : Minidregg.Kernel.ClockTickReceiver.Deployment} {profile : Minidregg.Compiler.CanonicalRuntimeProfile.Profile F} {ambient : Minidregg.Kernel.ClockTickReceiver.Ambient} {durable : Minidregg.Kernel.ClockTickReceiver.Durable} {command : Minidregg.Kernel.ClockTickReceiver.Command} (prepared : Minidregg.Kernel.ClockTickReceiver.Prepared deployment profile ambient durable command), Minidregg.Kernel.ClockCell.clockOf prepared.clockPost.logical = Option.some command.tick ∧ prepared.clock.clock.now < command.now ∧ prepared.clock.clock.slot ≤ command.slot
  new statement: ∀ {F : Type} [inst : Field F] {deployment : Minidregg.Kernel.ClockTickReceiver.Deployment} {profile : Minidregg.Compiler.CanonicalRuntimeProfile.Profile F} {ambient : Minidregg.Kernel.ClockTickReceiver.Ambient} {durable : Minidregg.Kernel.ClockTickReceiver.Durable} {command : Minidregg.Kernel.ClockTickReceiver.Command} (prepared : Minidregg.Kernel.ClockTickReceiver.Prepared deployment profile ambient durable command), Minidregg.Kernel.ClockCell.clockOf prepared.clockPost.logical = Option.some command.tick ∧ prepared.clock.clock.now < command.now ∧ prepared.clock.clock.slot ≤ command.slot ∧ command.now ≤ prepared.clock.clock.now + prepared.clock.maxStepSeconds
OK stronger: all three previous conjuncts retained plus command.now <= loaded.now + loaded.maxStepSeconds.

theorem Minidregg.Kernel.ClockTickReceiver.decideTick_ok
  old statement: ∀ {current next : Minidregg.Kernel.ClockCell.Clock} {plan : Minidregg.Kernel.ClockTickReceiver.Plan}, Minidregg.Kernel.ClockTickReceiver.decideTick current next = Except.ok plan → plan = { current := current, next := next } ∧ current.now < next.now ∧ current.slot ≤ next.slot
  new statement: ∀ {bound : ℕ} {current next : Minidregg.Kernel.ClockCell.Clock} {plan : Minidregg.Kernel.ClockTickReceiver.Plan}, Minidregg.Kernel.ClockTickReceiver.decideTick bound current next = Except.ok plan → plan = { current := current, next := next } ∧ current.now < next.now ∧ current.slot ≤ next.slot ∧ next.now ≤ current.now + bound
OK stronger for bound-aware admission: old plan/advancement/slot conclusions retained plus upper bound.

theorem Minidregg.Kernel.ClockTickReceiver.slot_back_refused
  old statement: ∀ (current next : Minidregg.Kernel.ClockCell.Clock), next.slot < current.slot → Minidregg.Kernel.ClockTickReceiver.decideTick current next = Except.error Minidregg.Kernel.ClockTickReceiver.Reject.clockNotAdvancing
  new statement: ∀ (bound : ℕ) (current next : Minidregg.Kernel.ClockCell.Clock), next.slot < current.slot → Minidregg.Kernel.ClockTickReceiver.decideTick bound current next = Except.error Minidregg.Kernel.ClockTickReceiver.Reject.clockNotAdvancing
OK equal/generalized: same premise and named refusal, uniformly for every bound.

theorem Minidregg.Kernel.ClockTickReceiver.tick_behind_refused
  old statement: ∀ (current next : Minidregg.Kernel.ClockCell.Clock), next.now ≤ current.now → Minidregg.Kernel.ClockTickReceiver.decideTick current next = Except.error Minidregg.Kernel.ClockTickReceiver.Reject.clockNotAdvancing
  new statement: ∀ (bound : ℕ) (current next : Minidregg.Kernel.ClockCell.Clock), next.now ≤ current.now → Minidregg.Kernel.ClockTickReceiver.decideTick bound current next = Except.error Minidregg.Kernel.ClockTickReceiver.Reject.clockNotAdvancing
OK equal/generalized: same premise and named refusal, uniformly for every bound.

def Minidregg.Kernel.ClockCell.genesisStore
  old statement: Minidregg.Kernel.ClockCell.ClockStore
  new statement: ℕ → ℕ → Minidregg.Kernel.ClockCell.ClockStore
OK structural API flag day: explicit time and bound replace constant genesis; old zero-clock projection remains available.

ctor Minidregg.Kernel.ClockCellDomain.View.mk
  old statement: Minidregg.Theory.TypedAuthorization.Digest → Minidregg.Theory.TypedAuthorization.Digest → Minidregg.Kernel.ClockCell.Clock → Minidregg.Kernel.ClockCellDomain.View
  new statement: Minidregg.Theory.TypedAuthorization.Digest → Minidregg.Theory.TypedAuthorization.Digest → Minidregg.Kernel.ClockCell.Clock → ℕ → Minidregg.Kernel.ClockCellDomain.View
OK structural extension: old root/authority/clock fields retained, bound added.

def Minidregg.Kernel.ClockTickReceiver.Reject.capabilityRejected.elim
  old statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 11 → motive Minidregg.Kernel.ClockTickReceiver.Reject.capabilityRejected → motive t
  new statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 12 → motive Minidregg.Kernel.ClockTickReceiver.Reject.capabilityRejected → motive t
OK equal under constructor identity: autogenerated eliminator index shifts by one after new clockStepExceeded constructor; same motive and named constructor, no weakened proposition.

def Minidregg.Kernel.ClockTickReceiver.Reject.physicalPreparation.elim
  old statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 9 → motive Minidregg.Kernel.ClockTickReceiver.Reject.physicalPreparation → motive t
  new statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 10 → motive Minidregg.Kernel.ClockTickReceiver.Reject.physicalPreparation → motive t
OK equal under constructor identity: autogenerated eliminator index shifts by one after new clockStepExceeded constructor; same motive and named constructor, no weakened proposition.

def Minidregg.Kernel.ClockTickReceiver.Reject.policyCastAlias.elim
  old statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 14 → motive Minidregg.Kernel.ClockTickReceiver.Reject.policyCastAlias → motive t
  new statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 15 → motive Minidregg.Kernel.ClockTickReceiver.Reject.policyCastAlias → motive t
OK equal under constructor identity: autogenerated eliminator index shifts by one after new clockStepExceeded constructor; same motive and named constructor, no weakened proposition.

def Minidregg.Kernel.ClockTickReceiver.Reject.policyInputRange.elim
  old statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 13 → motive Minidregg.Kernel.ClockTickReceiver.Reject.policyInputRange → motive t
  new statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 14 → motive Minidregg.Kernel.ClockTickReceiver.Reject.policyInputRange → motive t
OK equal under constructor identity: autogenerated eliminator index shifts by one after new clockStepExceeded constructor; same motive and named constructor, no weakened proposition.

def Minidregg.Kernel.ClockTickReceiver.Reject.policyRejected.elim
  old statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 12 → motive Minidregg.Kernel.ClockTickReceiver.Reject.policyRejected → motive t
  new statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 13 → motive Minidregg.Kernel.ClockTickReceiver.Reject.policyRejected → motive t
OK equal under constructor identity: autogenerated eliminator index shifts by one after new clockStepExceeded constructor; same motive and named constructor, no weakened proposition.

def Minidregg.Kernel.ClockTickReceiver.Reject.policyUnavailable.elim
  old statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 10 → motive Minidregg.Kernel.ClockTickReceiver.Reject.policyUnavailable → motive t
  new statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 11 → motive Minidregg.Kernel.ClockTickReceiver.Reject.policyUnavailable → motive t
OK equal under constructor identity: autogenerated eliminator index shifts by one after new clockStepExceeded constructor; same motive and named constructor, no weakened proposition.

def Minidregg.Kernel.ClockTickReceiver.Reject.replayedMarker.elim
  old statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 7 → motive Minidregg.Kernel.ClockTickReceiver.Reject.replayedMarker → motive t
  new statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 8 → motive Minidregg.Kernel.ClockTickReceiver.Reject.replayedMarker → motive t
OK equal under constructor identity: autogenerated eliminator index shifts by one after new clockStepExceeded constructor; same motive and named constructor, no weakened proposition.

def Minidregg.Kernel.ClockTickReceiver.Reject.signature.elim
  old statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 15 → ((reason : Minidregg.Compiler.CredentialSignatureAdmission.Reject) → motive (Minidregg.Kernel.ClockTickReceiver.Reject.signature reason)) → motive t
  new statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 16 → ((reason : Minidregg.Compiler.CredentialSignatureAdmission.Reject) → motive (Minidregg.Kernel.ClockTickReceiver.Reject.signature reason)) → motive t
OK equal under constructor identity: autogenerated eliminator index shifts by one after new clockStepExceeded constructor; same motive and named constructor, no weakened proposition.

def Minidregg.Kernel.ClockTickReceiver.Reject.validation.elim
  old statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 8 → motive Minidregg.Kernel.ClockTickReceiver.Reject.validation → motive t
  new statement: {motive : Minidregg.Kernel.ClockTickReceiver.Reject → Sort u} → (t : Minidregg.Kernel.ClockTickReceiver.Reject) → t.ctorIdx = 9 → motive Minidregg.Kernel.ClockTickReceiver.Reject.validation → motive t
OK equal under constructor identity: autogenerated eliminator index shifts by one after new clockStepExceeded constructor; same motive and named constructor, no weakened proposition.

def Minidregg.Kernel.ClockTickReceiver.decideTick
  old statement: Minidregg.Kernel.ClockCell.Clock → Minidregg.Kernel.ClockCell.Clock → Except Minidregg.Kernel.ClockTickReceiver.Reject Minidregg.Kernel.ClockTickReceiver.Plan
  new statement: ℕ → Minidregg.Kernel.ClockCell.Clock → Minidregg.Kernel.ClockCell.Clock → Except Minidregg.Kernel.ClockTickReceiver.Reject Minidregg.Kernel.ClockTickReceiver.Plan
OK stronger admission API: bound added, old monotonicity necessary, excessive advancement now refused.

ctor Minidregg.Kernel.NativeHostGenesis.Config.mk
  old statement: Minidregg.Compiler.CanonicalCellRegistry.Deployment → Minidregg.Theory.TypedAuthorization.FederationId → Minidregg.Theory.ResourceBirth.CreationTariff → Minidregg.Theory.TypedAuthorization.Digest → Minidregg.Theory.TypedAuthorization.Epoch → Minidregg.Theory.TypedAuthorization.Height → Minidregg.Pred.Pred → List Minidregg.Kernel.NativeHostGenesis.Enrollment → Minidregg.Kernel.NativeHostGenesis.FactoryController → Minidregg.Theory.ResourceCost.Charge → Option Minidregg.Kernel.NativeHostGenesis.PayObserver → List Minidregg.Kernel.NativeHostGenesis.ClockTicker → ℕ → Minidregg.Kernel.NativeHostGenesis.Config
  new statement: Minidregg.Compiler.CanonicalCellRegistry.Deployment → Minidregg.Theory.TypedAuthorization.FederationId → Minidregg.Theory.ResourceBirth.CreationTariff → Minidregg.Theory.TypedAuthorization.Digest → Minidregg.Theory.TypedAuthorization.Epoch → Minidregg.Theory.TypedAuthorization.Height → Minidregg.Pred.Pred → List Minidregg.Kernel.NativeHostGenesis.Enrollment → Minidregg.Kernel.NativeHostGenesis.FactoryController → Minidregg.Theory.ResourceCost.Charge → Option Minidregg.Kernel.NativeHostGenesis.PayObserver → List Minidregg.Kernel.NativeHostGenesis.ClockTicker → ℕ → ℕ → ℕ → Minidregg.Kernel.NativeHostGenesis.Config
OK structural extension: explicit genesis time/step bound added, old config fields retained; Config.Valid requires positive bound.

def Minidregg.Kernel.NativeHostGenesis.clockCell
  old statement: Minidregg.Theory.CellRegistry.PackedCell Minidregg.Compiler.CanonicalCellRegistry.registry
  new statement: Minidregg.Kernel.NativeHostGenesis.Config → Minidregg.Theory.CellRegistry.PackedCell Minidregg.Compiler.CanonicalCellRegistry.registry
OK structural generalization: takes Config and materializes its explicit time/bound in v2 layout.

ctor private Minidregg.Kernel.ClockCellDomain.Loaded.mk @Kernel.ClockCellDomain
  old statement: {deployment : Minidregg.Compiler.CanonicalCellRegistry.Deployment} → {physical : Minidregg.Kernel.ClockCellDomain.PhysicalSnapshot} → (cell : Minidregg.Kernel.ClockCell.Cell) → (clock : Minidregg.Kernel.ClockCell.Clock) → physical.canonicalBytes (Minidregg.Kernel.ClockCellDomain.cellIdOf deployment) = Minidregg.Kernel.ClockCellDomain.cellBytes cell → Minidregg.Kernel.ClockCell.clockOf cell.logical = Option.some clock → Minidregg.Kernel.ClockCellDomain.Loaded deployment physical
  new statement: {deployment : Minidregg.Compiler.CanonicalCellRegistry.Deployment} → {physical : Minidregg.Kernel.ClockCellDomain.PhysicalSnapshot} → (cell : Minidregg.Kernel.ClockCell.Cell) → (clock : Minidregg.Kernel.ClockCell.Clock) → (maxStepSeconds : ℕ) → Minidregg.Kernel.ClockCell.maxStepOf cell.logical = Option.some maxStepSeconds → 0 < maxStepSeconds → physical.canonicalBytes (Minidregg.Kernel.ClockCellDomain.cellIdOf deployment) = Minidregg.Kernel.ClockCellDomain.cellBytes cell → Minidregg.Kernel.ClockCell.clockOf cell.logical = Option.some clock → Minidregg.Kernel.ClockCellDomain.Loaded deployment physical
OK stronger custody witness: all old exactness fields retained, requires exact positive bound as loader enforces.

ctor private Minidregg.Kernel.ClockTickReceiver.Prepared.mk @Kernel.ClockTickReceiver
  old statement: {F : Type} → [inst : Field F] → {deployment : Minidregg.Kernel.ClockTickReceiver.Deployment} → {profile : Minidregg.Compiler.CanonicalRuntimeProfile.Profile F} → {ambient : Minidregg.Kernel.ClockTickReceiver.Ambient} → {durable : Minidregg.Kernel.ClockTickReceiver.Durable} → {command : Minidregg.Kernel.ClockTickReceiver.Command} → (directory : Minidregg.Compiler.CredentialAuthorityDomainReceiver.LoadedDirectory durable) → (authority : Minidregg.Compiler.CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot) → (clock : Minidregg.Kernel.ClockCellDomain.Loaded deployment durable.snapshot) → (plan : Minidregg.Kernel.ClockTickReceiver.Plan) → Minidregg.Kernel.ClockTickReceiver.decideTick clock.clock command.tick = Except.ok plan → Minidregg.Theory.PolicyInstall.Candidate (Minidregg.Kernel.ClockTickReceiver.family deployment authority.snapshot clock.cell profile.semantics ambient command) clock.cell (Minidregg.Kernel.ClockTickReceiver.declaration authority.snapshot.domain profile.semantics command plan) () → Minidregg.Compiler.CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory (authority.snapshot.authState.policyAddress { value := Minidregg.Kernel.ClockTickReceiver.clockTarget deployment } (authority.snapshot.authState.policyRevision { value := Minidregg.Kernel.ClockTickReceiver.clockTarget deployment })) → Minidregg.Kernel.ClockTickReceiver.Prepared deployment profile ambient durable command
  new statement: {F : Type} → [inst : Field F] → {deployment : Minidregg.Kernel.ClockTickReceiver.Deployment} → {profile : Minidregg.Compiler.CanonicalRuntimeProfile.Profile F} → {ambient : Minidregg.Kernel.ClockTickReceiver.Ambient} → {durable : Minidregg.Kernel.ClockTickReceiver.Durable} → {command : Minidregg.Kernel.ClockTickReceiver.Command} → (directory : Minidregg.Compiler.CredentialAuthorityDomainReceiver.LoadedDirectory durable) → (authority : Minidregg.Compiler.CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot) → (clock : Minidregg.Kernel.ClockCellDomain.Loaded deployment durable.snapshot) → (plan : Minidregg.Kernel.ClockTickReceiver.Plan) → Minidregg.Kernel.ClockTickReceiver.decideTick clock.maxStepSeconds clock.clock command.tick = Except.ok plan → Minidregg.Theory.PolicyInstall.Candidate (Minidregg.Kernel.ClockTickReceiver.family deployment authority.snapshot clock.cell profile.semantics ambient command) clock.cell (Minidregg.Kernel.ClockTickReceiver.declaration authority.snapshot.domain profile.semantics command plan) () → Minidregg.Compiler.CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory (authority.snapshot.authState.policyAddress { value := Minidregg.Kernel.ClockTickReceiver.clockTarget deployment } (authority.snapshot.authState.policyRevision { value := Minidregg.Kernel.ClockTickReceiver.clockTarget deployment })) → Minidregg.Kernel.ClockTickReceiver.Prepared deployment profile ambient durable command
OK stronger prepared witness: old source/candidate/authority witnesses retained, decision uses exact loaded bound.

Reviewed all 24 statements before ledger admission or pin. Root groups exactly:
## redefined: 7466 rows, 24 root groups
7349	Minidregg.Kernel.ClockCell.Namespace, Minidregg.Kernel.ClockCell.Namespace.Key, Minidregg.Kernel.ClockCell.Namespace.Value ...	93e18aac
46	Minidregg.Kernel.NativeHostGenesis.Config.mk	93e18aac
40	Minidregg.Kernel.ClockTickReceiver.Reject, Minidregg.Kernel.ClockTickReceiver.Reject.capabilityRejected, Minidregg.Kernel.ClockTickReceiver.Reject.physicalPreparation ...	93e18aac
5	Minidregg.Kernel.NativeHostGenesis.Config.mk, Minidregg.Kernel.NativeHostGenesis.Config.ofWire, Minidregg.Kernel.NativeHostGenesis.Config.toWire ...	93e18aac
4	Minidregg.Kernel.ClockCellDomain.View.mk	93e18aac
2	Minidregg.Kernel.ClockCell.Namespace	93e18aac
2	Minidregg.Kernel.ClockCell.Namespace, Minidregg.Kernel.ClockCell.Namespace.ofNat	93e18aac
2	Minidregg.Kernel.NativeHostGenesis.Config.Valid, Minidregg.Kernel.NativeHostGenesis.Config.mk	93e18aac
1	Minidregg.Kernel.ClockCell.Namespace, Minidregg.Kernel.ClockCell.Namespace.Key	93e18aac
1	Minidregg.Kernel.ClockCell.Namespace, Minidregg.Kernel.ClockCell.Namespace.Value	93e18aac
1	Minidregg.Kernel.ClockCell.Namespace, Minidregg.Kernel.ClockCell.Namespace.discipline	93e18aac
1	Minidregg.Kernel.ClockCell.Namespace, Minidregg.Kernel.ClockCell.Namespace.Key, Minidregg.Kernel.ClockCell.Namespace.keyDecEq	93e18aac
1	Minidregg.Kernel.ClockCell.Namespace, Minidregg.Kernel.ClockCell.Namespace.Value, Minidregg.Kernel.ClockCell.Namespace.valueDecEq	93e18aac
1	Minidregg.Kernel.ClockCell.Namespace, Minidregg.Kernel.ClockCell.Namespace.Key, Minidregg.Kernel.ClockCell.keyStream	93e18aac
1	Minidregg.Kernel.ClockCell.Namespace, Minidregg.Kernel.ClockCell.namespaceStream	93e18aac
1	Minidregg.Kernel.ClockCell.Namespace, Minidregg.Kernel.ClockCell.Namespace.Value, Minidregg.Kernel.ClockCell.valueStream	93e18aac
1	Minidregg.Kernel.ClockCell.wireName	93e18aac
1	Minidregg.Kernel.ClockCellDomain.View.mk, Minidregg.Kernel.ClockTickReceiver.viewCodec, Minidregg.Kernel.ClockTickReceiver.viewStream	93e18aac
1	Minidregg.Kernel.ClockCellDomain.View.mk, Minidregg.Kernel.ClockTickReceiver.viewStream	93e18aac
1	Minidregg.Kernel.NativeHostGenesis.Config.mk, Minidregg.Kernel.NativeHostGenesis.Config.ofWire	93e18aac
1	Minidregg.Kernel.NativeHostGenesis.Config.mk, Minidregg.Kernel.NativeHostGenesis.Config.ofWire, Minidregg.Kernel.NativeHostGenesis.Config.toWire	93e18aac
1	Minidregg.Kernel.NativeHostGenesis.Config.mk, Minidregg.Kernel.NativeHostGenesis.Config.toWire	93e18aac
1	Minidregg.Kernel.NativeHostGenesis.configFrame	93e18aac
1	Minidregg.Kernel.NativeHostGenesis.Config.Valid, Minidregg.Kernel.NativeHostGenesis.Config.mk, Minidregg.Kernel.NativeHostGenesis.configValidDecidable	93e18aac
