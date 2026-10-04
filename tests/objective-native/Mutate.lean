/- A DISHONEST SIGNER for the native Objective refusal checks (test-only; run
with `lake env lean --run tests/objective-native/Mutate.lean`).

It takes an honest quote (`objective-quote` output: the derived command and its
prepare intent), applies ONE named mutation to the command or its signed claim,
and writes the prepare intent for the mutated command. The member then signs it
through the ordinary plan consent (endpoint 222, which signs whatever command
its intent names), so the Host's admission is the only thing left to refuse.

  MUTATION QUOTE.json INTENT-NONCE OUT-INTENT.bin [ARGUMENT]

Mutations:
  source-atom DECIMAL   the claim names another atom in the source document
  capability DECIMAL    the effect target is signed under another capability
  command-nonce         the command nonce moves; the signed queries keep theirs
  fee-debit             the claim declares one credit the compute quote does not charge
  tariff                the claim's proofWork is one below the tariff price
  argument              one byte of the argument packet changes; expectedInput stays
  output                the effect's created-atom payload byte changes
  none                  nothing changes: the honest command, signed later
                        (after the state it was derived from has moved)
-/
import Kernel.ObjectiveBendNativeAdmission
import Host.ObjectiveInvocationQuote
open Lean (Json toJson)
open Minidregg.Compiler Minidregg.Kernel Minidregg.Kernel.DeclaredResourceController
open Minidregg.Compiler.Tower256ConcreteBackend Minidregg.Theory.TypedAuthorization

def unhex (text : String) : IO (List UInt8) := do
  let some bytes := ObjectiveBendPlanAdapter.unhex text.toList | throw (IO.userError "hex")
  pure bytes

def claimOf (command : Command) : IO ObjectiveInvocationClaim.Claim := do
  let some family := command.family | throw (IO.userError "no family")
  let some claim := ObjectiveInvocationClaim.decode family.contextBytes | throw (IO.userError "claim")
  pure claim

def withClaim (command : Command) (claim : ObjectiveInvocationClaim.Claim) : Command :=
  { command with family := some (ObjectiveInvocationClaim.family claim) }

def mutatePayload (f : List UInt8 → List UInt8) : Payload → Payload
  | .content command => .content ⟨command.actions.map fun
      | .createAtom atom kind payload => .createAtom atom kind (f payload)
      | other => other⟩
  | other => other

def mutate (name : String) (argument : Option String) (command : Command) : IO Command := do
  let claim ← claimOf command
  match name, argument with
  | "source-atom", some atom =>
      pure (withClaim command { claim with sourceAtom := ⟨atom.toNat!⟩ })
  | "capability", some capability =>
      pure { command with targets := command.targets.map fun target =>
        { target with capability := ⟨capability.toNat!⟩ } }
  | "command-nonce", none => pure { command with nonce := command.nonce + 1 }
  | "none", none => pure command
  | "fee-debit", none =>
      pure (withClaim command { claim with capacity := { claim.capacity with feeDebit := claim.capacity.feeDebit + 1 } })
  | "tariff", none =>
      pure (withClaim command { claim with capacity := { claim.capacity with proofWork := claim.capacity.proofWork - 1 } })
  | "argument", none =>
      -- The packet's last natural is the byte; "7" becomes "9".
      let text := String.fromUTF8! claim.arguments.toByteArray
      let changed := text.replace "\"value\":\"7\"" "\"value\":\"9\""
      if changed == text then throw (IO.userError "argument packet has no byte 7")
      pure (withClaim command { claim with arguments := changed.toUTF8.toList })
  | "output", none =>
      pure { command with targets := command.targets.map fun target =>
        { target with payload := mutatePayload (fun bytes =>
            if bytes == [7] then [8] else bytes) target.payload } }
  | _, _ => throw (IO.userError s!"unknown mutation {name}")

def main (args : List String) : IO UInt32 := do
  let mutation :: quotePath :: nonceText :: outPath :: rest := args
    | IO.eprintln "usage: Mutate MUTATION QUOTE.json INTENT-NONCE OUT-INTENT.bin [ARGUMENT]"; return 2
  let quote ← IO.ofExcept (Json.parse (← IO.FS.readFile quotePath))
  let commandHex ← IO.ofExcept (quote.getObjValAs? String "command")
  let some command := commandCodec.decode (← unhex commandHex) | throw (IO.userError "command")
  let mutated ← mutate mutation rest.head? command
  if mutation != "none" && mutated == command then throw (IO.userError "the mutation changed nothing")
  let intent : NativeObservationCodec.Intent := ⟨mutated.subject,nonceText.toNat!,
    .prepare (.invoke (commandCodec.encode mutated)),
    mutated.targets.filterMap fun target =>
      target.observeCapability.map fun capability => ⟨target.kind,target.target,capability⟩⟩
  IO.FS.writeBinFile outPath (NativeObservationCodec.intentCodec.encode intent).toByteArray
  IO.println (Json.mkObj [("mutation",toJson mutation),
    ("commandChanged",toJson (commandCodec.encode mutated != commandCodec.encode command))]).compress
  return 0
