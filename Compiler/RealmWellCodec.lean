/-
# Compiler.RealmWellCodec — the wire of a realm-well command (K-WELL)

A realm well is an account born in a realm (a room) whose cell id names an
asset (`CanonicalResourceKernel`: an asset is named by its issuer-well
account). One signed command mints from, or burns into, one well:

* `mint`: `Operation.mint well account amount` — the request targets the WELL
  (verb `mintAsset`) and is admitted under the well's law;
* `burn`: `Operation.burn account well amount` — the request targets the
  debited ACCOUNT (verb `burnAsset`) and is admitted under that account's law.

Frames: `DREGG/WELL/COMMAND/v1`, `DREGG/WELL/SIGNED/v1` (command bytes and the
canonical signed envelope) and `DREGG/WELL/PLAN/v1` (the signing plan the Host
returns: the exact header the subject signs). The command carries no expected
roots: the signed request quotes the Book's pre-root and the plan's authority
footprint, so a plan against a moved Book refuses at signature admission.
-/
import Compiler.NativeHostCodec

namespace Minidregg.Compiler.RealmWellCodec

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

inductive WellOp where
  | mint
  | burn
  deriving DecidableEq, Repr

def WellOp.isMint : WellOp → Bool
  | .mint => true
  | .burn => false

def WellOp.ofIsMint (isMint : Bool) : WellOp := if isMint then .mint else .burn

def wellOpStream : StreamCodec WellOp :=
  StreamCodec.xmap StreamCodec.bool WellOp.isMint WellOp.ofIsMint
    (by intro op; cases op <;> rfl)

/-- `subject` signs, presenting stored capability `capability`; `well` is the
asset (its issuer-well account); `account` is the credited (mint) or debited
(burn) holder. -/
structure Command where
  subject : SubjectId
  capability : CapabilityId
  well : Nat
  op : WellOp
  account : Nat
  amount : Nat
  nonce : Nat
  deriving DecidableEq, Repr

/-- The resource the request targets: the well for a mint, the debited account
for a burn. -/
def Command.target (command : Command) : Nat :=
  match command.op with
  | .mint => command.well
  | .burn => command.account

def Command.verb (command : Command) : Verb .account :=
  match command.op with
  | .mint => .mintAsset
  | .burn => .burnAsset

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product capabilityIdStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product wellOpStream
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product StreamCodec.nat StreamCodec.nat))))))
    (fun c => (c.subject, c.capability, c.well, c.op, c.account, c.amount, c.nonce))
    (fun (subject, capability, well, op, account, amount, nonce) =>
      ⟨subject, capability, well, op, account, amount, nonce⟩)
    (by intro c; cases c; rfl)

def commandFrame : List UInt8 := "DREGG/WELL/COMMAND/v1".toUTF8.toList

def commandCodec : LawfulCodec Command := NativeHostCodec.framed commandFrame commandStream

theorem command_roundtrip (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command :=
  commandCodec.decode_encode command

theorem command_canonical {bytes : List UInt8} {command : Command}
    (accepted : commandCodec.decode bytes = some command) : commandCodec.encode command = bytes :=
  NativeHostCodec.framed_canonical commandFrame commandStream accepted

structure Ingress where
  commandBytes : List UInt8
  envelope : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun ingress => (ingress.commandBytes, ingress.envelope))
    (fun (command, envelope) => ⟨command, envelope⟩)
    (by intro ingress; cases ingress; rfl)

def ingressFrame : List UInt8 := "DREGG/WELL/SIGNED/v1".toUTF8.toList

def ingressCodec : LawfulCodec Ingress := NativeHostCodec.framed ingressFrame ingressStream

theorem ingress_roundtrip (ingress : Ingress) :
    ingressCodec.decode (ingressCodec.encode ingress) = some ingress :=
  ingressCodec.decode_encode ingress

theorem ingress_canonical {bytes : List UInt8} {ingress : Ingress}
    (accepted : ingressCodec.decode bytes = some ingress) : ingressCodec.encode ingress = bytes :=
  NativeHostCodec.framed_canonical ingressFrame ingressStream accepted

/-- The Host's plan: the exact header bytes the subject signs over the current
image, beside the command they authorize. It discloses no decision. -/
structure SigningPlan where
  domain : Digest
  semantics : Digest
  commandBytes : List UInt8
  header : List UInt8
  deriving DecidableEq, Repr

def signingPlanStream : StreamCodec SigningPlan :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product bytesStream bytesStream)))
    (fun plan => (plan.domain, plan.semantics, plan.commandBytes, plan.header))
    (fun (domain, semantics, command, header) => ⟨domain, semantics, command, header⟩)
    (by intro plan; cases plan; rfl)

def planFrame : List UInt8 := "DREGG/WELL/PLAN/v1".toUTF8.toList

def signingPlanCodec : LawfulCodec SigningPlan :=
  NativeHostCodec.framed planFrame signingPlanStream

theorem plan_roundtrip (plan : SigningPlan) :
    signingPlanCodec.decode (signingPlanCodec.encode plan) = some plan :=
  signingPlanCodec.decode_encode plan

/-- info: 'Minidregg.Compiler.RealmWellCodec.command_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms command_roundtrip
/-- info: 'Minidregg.Compiler.RealmWellCodec.command_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms command_canonical
/-- info: 'Minidregg.Compiler.RealmWellCodec.ingress_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ingress_roundtrip
/-- info: 'Minidregg.Compiler.RealmWellCodec.ingress_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ingress_canonical
/-- info: 'Minidregg.Compiler.RealmWellCodec.plan_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms plan_roundtrip

end Minidregg.Compiler.RealmWellCodec
