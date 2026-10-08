/- KN2-NEUTRAL-BIRTHS executed probe, cluster (5): the RESERVE factory method
(`NativeHostReserveBirth`, independently signed owner consent) commits its newborns only
when the step the factory law admitted names them (`birth/<id>` ↦ exact post root).
Two owners (subjects 7 and 8, real Ed25519 keys) each own one declared newborn
(`ResourceReserveBirthFixture.twoOwnerPlan`); the plan is signed source-side by the creator
and owner-side by each owner, assembled by `NativeHostReserveBirth.assemble`, and submitted
to the real receiver `ResourceBirthReceiver.receiveLoaded` against a booted native Store.
 control      the reserve birth commits;
 substituted  a newborn's post substituted on the admitted writes: `neutralBirthUnjudged <id>`;
 plant        (plant-neutral-birth.sh's aux-unnamed, run with MODE reserve) the control goes red.

The ordinary-method header below is shared with scripts/kn2/neutral-birth.lean.

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

Usage: lake env lean --run scripts/kn2/neutral-birth-reserve.lean VERIFIER SIGN-PROBE STORE-BINARY [MODE]
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

namespace NeutralBirthReserveProbe

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

def genesis (creatorKey ownerKey : List UInt8) (factory : Minidregg.Pred.Pred) : NativeHostGenesis.Config where
  deployment := hostTemplate.deployment
  federation := hostTemplate.federation
  tariff := tariff
  expectedSemantics := profile.semantics
  issuerEpoch := 2
  genesisHeight := 10
  factoryPredicate := factory
  enrollments :=
    [⟨⟨7007, 2, 1, 7, creatorKey, 0, 100, none⟩, 7,
      ⟨41⟩, ⟨44⟩, ⟨46⟩, 100, .all []⟩,
     ⟨⟨7008, 2, 1, 8, ownerKey, 0, 100, none⟩, 8,
      ⟨51⟩, ⟨54⟩, ⟨56⟩, 100, .all []⟩]
  factoryController := ⟨⟨7⟩, ⟨43⟩⟩
  meterAllowance := fun _ => 10000000
  clockTickers := []
  tailBound := 1000
  clockGenesisNow := 0
  clockMaxStepSeconds := 300


def describe : ResourceBirthReceiver.Result → String
  | .confirmed _ _ => "committed"
  | .rejected (.admission reason) => s!"refused admission {repr reason}"
  | .rejected .malformedIngress => "refused malformedIngress"
  | .rejected .transactionConflict => "refused transactionConflict"
  | .rejected (.durable reason) => s!"refused durable {repr reason}"
  | .contention => "contention"
  | .unavailable detail => s!"unavailable {detail}"
  | .uncertain detail => s!"uncertain {detail}"

def named (step : CanonicalPolicyAdmission.PolicyStepContext) (writes : List DataWrite) : String :=
  match ResourceBirthController.Concrete.checkNamed step writes with
  | .ok _ => "named"
  | .error cell => s!"neutralBirthUnjudged {cell}"

def run (verifier signer storeBinary : System.FilePath) (mode : String) : IO Unit := do
  let (creatorPublic, _) ← sign signer 7 []
  let (ownerPublic, _) ← sign signer 8 []
  let cfg := genesis creatorPublic ownerPublic (.all [])
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
    let plan ← match Minidregg.Verify.ResourceReserveBirthFixture.twoOwnerPlan host cfg opened ⟨7⟩ ⟨8⟩ 71 7 ⟨41⟩ with
      | .error reason => throw (IO.userError s!"reserve plan: {reason}")
      | .ok value => pure value
    let sources ← plan.base.slots.mapM fun slot => do
      let (_, signature) ← sign signer 7 slot.header
      pure signature
    -- owner consent: the first newborn (100) is subject 8's, the second (101) the creator's
    let owners ← (plan.owners.zip [8, 7]).mapM fun (slot, seed) => do
      let (_, signature) ← sign signer seed slot.header
      pure signature
    let call ← match NativeHostReserveBirth.assemble plan sources owners with
      | .error reason => throw (IO.userError s!"assemble: {reason}")
      | .ok value => pure value
    let .birth bytes := call | throw (IO.userError "assembled call is not a birth")
    let height := NativeHost.logicalHeight host opened.durable
    let some ingress := ResourceBirthPolicyController.Concrete.decodeIngress bytes
      | throw (IO.userError "assembled reserve ingress does not decode")
    require "the reserve factory method" (ingress.method == .reserve)
    match ← ResourceBirthPolicyController.Concrete.admitDecodedNative profile host.deployment
        opened.pins host.signature opened.durable height ingress with
    | .error reason => IO.println s!"admission: refused {repr reason}"
    | .ok accepted =>
        let writes := accepted.prepared.writes
        let births := writes.filter ResourceBirthController.Concrete.bornIn
        IO.println s!"reserve control: {births.length} birth writes, named: {named accepted.factoryStep writes}"
        if mode == "all" then
          let some first := births.head? | throw (IO.userError "no birth write")
          let substituted := { first with
            exactPost := ResourceBirthCodec.rootBytes ([0] ++ first.canonicalPostBytes)
            canonicalPostBytes := [0] ++ first.canonicalPostBytes }
          let replaced := writes.map fun write => if write.cellId = first.cellId then substituted else write
          let verdict := named accepted.factoryStep replaced
          IO.println s!"substituted post at {first.cellId.value}: {verdict}"
          require "substituted post refused by name" (verdict == s!"neutralBirthUnjudged {first.cellId.value}")
    let result ← ResourceBirthReceiver.receiveLoaded profile host.deployment opened.pins
      host.signature transport opened.durable height bytes
    let verdict := describe result
    IO.println s!"reserve submission: {verdict}"
    require s!"reserve birth commits (got {verdict})" (verdict == "committed")
    IO.println s!"PASS neutral birth reserve ({mode})"

end NeutralBirthReserveProbe

def main (args : List String) : IO Unit := do
  match args with
  | [verifier, signer, store] => NeutralBirthReserveProbe.run verifier signer store "all"
  | [verifier, signer, store, mode] => NeutralBirthReserveProbe.run verifier signer store mode
  | _ => throw (IO.userError "usage: neutral-birth-reserve VERIFIER SIGN-PROBE STORE-BINARY [all|control]")
