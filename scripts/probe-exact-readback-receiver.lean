import Compiler.DurableReceiverIO

open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Compiler
open Minidregg.Compiler.DurableReceiverIO

set_option autoImplicit false

def original : Loaded Witness.lengthRoot :=
  ⟨DurableReceiverCodec.encode Witness.image, Witness.image,
    Witness.seed.snapshot Witness.lengthRoot, rfl, Witness.seed_represents⟩

def candidate : List UInt8 :=
  DurableReceiverCodec.encode (Witness.image.append Witness.intent)

/-- A distinct harmless accepted turn after the candidate. This models a
concurrent later append observed by the original receiver's post-CAS read. -/
def laterWrite : DataWrite :=
  { cellId := Witness.writeCell
    expectedPre := ⟨4⟩
    exactPost := ⟨5⟩
    canonicalPostBytes := [10, 11, 12, 13, 14] }

def later : DataIntent Witness.lengthRoot where
  transactionId := ⟨92⟩
  writes := [laterWrite]
  readGuards := []
  nullifiers := []
  exactCharge := fun _ => 1
  event := { Witness.event with eventId := ⟨83⟩ }
  postRootsBound := by simp [laterWrite, Witness.lengthRoot]
  guardsReadOnly := by simp

def laterCandidate : List UInt8 :=
  DurableReceiverCodec.encode ((Witness.image.append Witness.intent).append later)

def transport (readback : Except String (Option (List UInt8)))
    (casResult : CasObservation) : Transport :=
  { read := pure readback, cas := fun _ _ => pure casResult }

def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL {label}")

def main : IO Unit := do
  let (freshInstalled, freshResult) ← receiveLoadedDetailedWithFresh
      (transport (.ok (some candidate)) .installed)
      Witness.lengthRoot original Witness.intent
  require "CAS winner marked fresh" freshInstalled
  match freshResult with
  | .exact .installed _ _ _ _ => pure ()
  | _ => throw (IO.userError "FAIL fresh CAS winner lost exact readback")
  let (alreadyFresh, alreadyResult) ← receiveLoadedDetailedWithFresh
      (transport (.ok (some candidate)) .alreadyPresent)
      Witness.lengthRoot original Witness.intent
  require "already-present exact readback is not fresh" (!alreadyFresh)
  match alreadyResult with
  | .exact .installed _ _ _ _ => pure ()
  | _ => throw (IO.userError "FAIL already-present readback changed legacy result")
  let (uncertainFresh, uncertainResult) ← receiveLoadedDetailedWithFresh
      (transport (.ok (some candidate)) (.uncertain "lost CAS reply"))
      Witness.lengthRoot original Witness.intent
  require "uncertain CAS readback is not fresh" (!uncertainFresh)
  match uncertainResult with
  | .exact .recoveredAfterUncertainResponse _ _ _ _ => pure ()
  | _ => throw (IO.userError "FAIL uncertain readback changed legacy result")
  match ← receiveLoadedDetailed (transport (.ok (some candidate)) .installed)
      Witness.lengthRoot original Witness.intent with
  | .exact .installed _ _ readback _ =>
      require "exact installed physical bytes" (readback.toByteArray == candidate.toByteArray)
      require "exact evidence candidate" (decide (readback = candidate))
  | _ => throw (IO.userError "FAIL installed candidate omitted exact witness")
  match ← receiveLoadedDetailed
      (transport (.ok (some candidate)) (.uncertain "lost CAS reply"))
      Witness.lengthRoot original Witness.intent with
  | .exact .recoveredAfterUncertainResponse _ _ _ _ => pure ()
  | _ => throw (IO.userError "FAIL lost reply exact readback not recovered")
  match ← receiveLoadedDetailed
      (transport (.error "read failed") .installed)
      Witness.lengthRoot original Witness.intent with
  | .ordinary (.uncertain _) => pure ()
  | _ => throw (IO.userError "FAIL absent readback yielded confirmation")
  match ← receiveLoadedDetailed
      (transport (.ok none) (.uncertain "lost CAS reply"))
      Witness.lengthRoot original Witness.intent with
  | .ordinary (.uncertain _) => pure ()
  | _ => throw (IO.userError "FAIL missing readback after lost reply yielded confirmation")
  match ← receiveLoadedDetailed
      (transport (.ok (some candidate)) .conflict)
      Witness.lengthRoot original Witness.intent with
  | .ordinary .contention => pure ()
  | _ => throw (IO.userError "FAIL CAS conflict gained exact witness")
  match ← receiveLoadedDetailed
      (transport (.ok (some [0])) .installed)
      Witness.lengthRoot original Witness.intent with
  | .ordinary (.uncertain _) => pure ()
  | _ => throw (IO.userError "FAIL malformed readback yielded confirmation")
  let _ ← match loadBytes Witness.lengthRoot laterCandidate with
    | .ok loaded => pure loaded
    | .error detail => throw (IO.userError s!"FAIL canonical later append: {detail}")
  match ← receiveLoadedDetailed
      (transport (.ok (some laterCandidate)) .installed)
      Witness.lengthRoot original Witness.intent with
  | .ordinary (.confirmed .installed _) => pure ()
  | _ => throw (IO.userError "FAIL later append gained exact-candidate witness")
  let reopened ← match loadBytes Witness.lengthRoot candidate with
    | .ok loaded => pure loaded
    | .error detail => throw (IO.userError s!"FAIL candidate reopen: {detail}")
  match ← receiveLoadedDetailed (transport (.ok (some candidate)) .installed)
      Witness.lengthRoot reopened Witness.intent with
  | .ordinary (.confirmed .replayed _) => pure ()
  | _ => throw (IO.userError "FAIL prior replay gained new exact witness")
  IO.println "PASS exact readback, CAS-winner distinction, lost response, unavailable/missing/malformed readback, contention, later append, prior replay"
