/- KN2-NEUTRAL-BIRTHS executed probe: a newborn is committed only when the step the
factory law admitted names it (`birth/<id>` ↦ its exact post root).

One source-built genesis image (a creator, subject 7, with a real Ed25519 key from the
fixture signer), booted into a native Store.  A descriptor of one NEUTRAL content birth
(no room, no kind export) with its initial policy (an auxiliary policy-source create) is
authored by `NativeHost.prepareLoaded`, signed slot by slot, assembled, and submitted to
the real receiver `ResourceBirthReceiver.receiveLoaded` against the Store.

 control      the birth commits (`.confirmed .installed`);
 law-sees     a factory law `birth/<id> = <exact post root>` admits it, and the same law
              with the root plus one refuses it `policyRejected`: the slot is in the
              JUDGED state, read by the deployed factory law;
 substituted  the old atomic-birth substitution (a post other than the judged one) applied
              to the admitted birth's committed writes is refused by the receiver's own
              check, `neutralBirthUnjudged <id>`;
 extra        an extra fresh birth write appended to the committed writes is refused the
              same way, naming the extra cell.
Source plants (the same probe run on a planted tree, see plant-neutral-birth.sh) turn the
control red by name: an extra write in `planWrites`, an auxiliary create left out of
`newbornSlots`.

Usage: lake env lean --run scripts/kn2/neutral-birth.lean VERIFIER SIGN-PROBE STORE-BINARY [MODE]
  MODE = all (default) | control (control only: the plant runs) -/
import Kernel.NativeHostGenesis
import Kernel.NativeHost
import Kernel.ResourceBirthReceiver
import Verify.ResourceReserveBirthFixture

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent

namespace NeutralBirthProbe

def require (label : String) (yes : Bool) : IO Unit :=
  unless yes do throw (IO.userError s!"FAIL neutral birth: {label}")

def sign (binary : System.FilePath) (seed : Nat) (frame : List UInt8) :
    IO (List UInt8 × List UInt8) :=
  IO.FS.withTempDir fun directory => do
    let framePath := directory / "frame.bin"
    let keyPath := directory / "public.bin"
    let sigPath := directory / "signature.bin"
    IO.FS.writeBinFile framePath frame.toByteArray
    let output ← IO.Process.output
      { cmd := binary.toString
        args := #[toString seed, framePath.toString, keyPath.toString, sigPath.toString] }
    require s!"fixture signer: {output.stderr}" (output.exitCode == 0)
    pure ((← IO.FS.readBinFile keyPath).toList, (← IO.FS.readBinFile sigPath).toList)

def tariff : CreationTariff := ⟨0, 0, 0, 0, 99, 0⟩

def hostTemplate : NativeHost.Config where
  deployment := ⟨⟨8500⟩, 10, 11, 12⟩
  federation := ⟨9⟩
  template := ⟨⟨5⟩, 100000, 10000, 64⟩
  tariff := tariff
  genesisHeight := 10
  expectedSeed := ⟨0⟩
  storage := { binary := "unused", root := "unused", key := "unused", checkpointEvery := 16 }
  signature := ⟨"unused"⟩

def profile := hostTemplate.profile

def genesis (creatorKey : List UInt8) (factory : Minidregg.Pred.Pred) : NativeHostGenesis.Config where
  deployment := hostTemplate.deployment
  federation := hostTemplate.federation
  tariff := tariff
  expectedSemantics := profile.semantics
  issuerEpoch := 2
  genesisHeight := 10
  factoryPredicate := factory
  enrollments :=
    [⟨⟨7007, 2, 1, 7, creatorKey, 0, 100, none⟩, 7,
      ⟨41⟩, ⟨44⟩, ⟨46⟩, 100, .all []⟩]
  factoryController := ⟨⟨7⟩, ⟨43⟩⟩
  meterAllowance := fun _ => 10000000
  clockTickers := []
  tailBound := 1000
  clockGenesisNow := 0
  clockMaxStepSeconds := 300

/-- The newborn: one empty content cell at 7001, owner 7; neutral (no room, no kind). -/
def born : Minidregg.Verify.ResourceReserveBirthFixture.Born :=
  Minidregg.Verify.ResourceReserveBirthFixture.content 7001 ⟨7⟩ ⟨1001⟩ ⟨1101⟩

/-- The exact post root the factory step names the newborn by. -/
def bornRoot : Nat := (ResourceBirthController.birthWrite born.item.create).exactPost.value

inductive Verdict where
  | committed
  | refused (reason : String)

def describe : ResourceBirthReceiver.Result → String
  | .confirmed _ _ => "committed"
  | .rejected (.admission reason) => s!"refused admission {repr reason}"
  | .rejected .malformedIngress => "refused malformedIngress"
  | .rejected .transactionConflict => "refused transactionConflict"
  | .rejected (.durable reason) => s!"refused durable {repr reason}"
  | .contention => "contention"
  | .unavailable detail => s!"unavailable {detail}"
  | .uncertain detail => s!"uncertain {detail}"

/-- Boot a fresh Store from the genesis whose factory law is `factory`, author, sign and
submit the one-birth descriptor through the real receiver; `inspect` sees the admitted
birth (fresh admission on the same loaded image) before the durable submission. -/
def submit (verifier signer storeBinary : System.FilePath) (factory : Minidregg.Pred.Pred)
    (inspect : {pins : FactoryPins} → {durable : ResourceBirthController.Concrete.Durable} →
      {height : Height} →
      ResourceBirthPolicyController.Concrete.AcceptedBirth profile hostTemplate.deployment pins
        durable height → IO Unit) :
    IO String := do
  let (creatorPublic, _) ← sign signer 7 []
  let cfg := genesis creatorPublic factory
  let built ← match NativeHostGenesis.build profile cfg with
    | .error reason => throw (IO.userError s!"genesis build: {repr reason}")
    | .ok value => pure value
  IO.FS.withTempDir fun directory => do
    IO.FS.writeBinFile (directory / "key") ((List.range 32).map (fun i => UInt8.ofNat (i * 7 + 3))).toByteArray
    let storage : DurableReceiverIO.NativeConfig :=
      { binary := storeBinary, root := directory / "store", key := directory / "key", checkpointEvery := 16 }
    let host : NativeHost.Config :=
      { hostTemplate with
        expectedSeed := NativeHost.seedIdentity built.seed
        storage := storage
        signature := ⟨verifier⟩ }
    let transport := host.transport
    match ← DurableReceiverIO.bootstrap transport ResourceBirthCodec.rootBytes built.seed with
    | .error reason => throw (IO.userError s!"native bootstrap: {reason}")
    | .ok () => pure ()
    let opened ← match ← NativeHost.openExisting host with
      | .error reason => throw (IO.userError s!"native host open: {reason}")
      | .ok value => pure value
    let descriptor := Minidregg.Verify.ResourceReserveBirthFixture.ordinaryDescriptor host cfg opened ⟨7⟩ 71 7 [born]
    let plan ← match NativeHost.prepareLoaded host opened
        (.birth (CanonicalCellRegistry.sourceEncoding.codec.encode descriptor)
          (List.replicate descriptor.resourceBatch.operations.length ⟨41⟩)) with
      | .error reason => throw (IO.userError s!"birth plan: {reason}")
      | .ok value => pure value
    let signatures ← plan.slots.mapM fun slot => do
      let (_, signature) ← sign signer 7 slot.header
      pure signature
    let call ← match NativeHost.assemble plan signatures with
      | .error reason => throw (IO.userError s!"assemble: {reason}")
      | .ok value => pure value
    let .birth bytes := call | throw (IO.userError "assembled call is not a birth")
    let height := NativeHost.logicalHeight host opened.durable
    let some ingress := ResourceBirthPolicyController.Concrete.decodeIngress bytes
      | throw (IO.userError "assembled birth ingress does not decode")
    match ← ResourceBirthPolicyController.Concrete.admitDecodedNative profile host.deployment
        opened.pins host.signature opened.durable height ingress with
    | .ok accepted => inspect accepted
    | .error _ => pure ()
    let result ← ResourceBirthReceiver.receiveLoaded profile host.deployment opened.pins
      host.signature transport opened.durable height bytes
    pure (describe result)

/-- The receiver's naming check over a patch, by name. -/
def named (step : CanonicalPolicyAdmission.PolicyStepContext) (writes : List DataWrite) : String :=
  match ResourceBirthController.Concrete.checkNamed step writes with
  | .ok _ => "named"
  | .error cell => s!"neutralBirthUnjudged {cell}"

def run (verifier signer storeBinary : System.FilePath) (mode : String) : IO Unit := do
  let control ← submit verifier signer storeBinary (.all []) fun accepted => do
    let writes := accepted.prepared.writes
    let births := writes.filter ResourceBirthController.Concrete.bornIn
    IO.println s!"control: {births.length} birth writes {births.map (·.cellId.value)}, named: {named accepted.factoryStep writes}"
    if mode == "all" then
      -- the old atomic substitution: the newborn's post replaced after admission
      let original := ResourceBirthController.birthWrite born.item.create
      let page := NativeHostGenesis.declaredPacked 7001 false .open
      let substituted := ResourceBirthController.birthWrite { born.item.create with cell := page }
      let replaced := writes.map fun write => if write.cellId = original.cellId then substituted else write
      let verdict := named accepted.factoryStep replaced
      IO.println s!"substituted post at 7001: {verdict}"
      require "substituted post refused by name" (verdict == "neutralBirthUnjudged 7001")
      let extra := ResourceBirthController.birthWrite { born.item.create with cellId := 7501 }
      let verdict := named accepted.factoryStep (writes ++ [extra])
      IO.println s!"extra birth write at 7501: {verdict}"
      require "extra birth refused by name" (verdict == "neutralBirthUnjudged 7501")
  IO.println s!"control submission: {control}"
  require s!"control commits (got {control})" (control == "committed")
  if mode == "all" then
    let slot := ReceivingLaw.birthSlot 7001
    let sees ← submit verifier signer storeBinary (.eq slot (Int.ofNat bornRoot)) fun _ => pure ()
    IO.println s!"factory law birth/7001 = exact root: {sees}"
    require "a factory law reading birth/7001 = exact root admits" (sees == "committed")
    let refuses ← submit verifier signer storeBinary (.eq slot (Int.ofNat bornRoot + 1)) fun _ => pure ()
    IO.println s!"factory law birth/7001 = root + 1: {refuses}"
    require "a factory law reading birth/7001 = another root refuses"
      (refuses == "refused admission Minidregg.Kernel.ResourceBirthPolicyController.Reject.policyRejected")
  IO.println s!"PASS neutral birth ({mode})"

end NeutralBirthProbe

def main (args : List String) : IO Unit := do
  match args with
  | [verifier, signer, store] => NeutralBirthProbe.run verifier signer store "all"
  | [verifier, signer, store, mode] => NeutralBirthProbe.run verifier signer store mode
  | _ => throw (IO.userError "usage: neutral-birth VERIFIER SIGN-PROBE STORE-BINARY [all|control]")
