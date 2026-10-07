/-
Fresh event27 grant issue from one verifier-minted Mini history and one native
current-image admission. The lower birth/app checks cannot supply the original
event22 ticket by themselves. Receipt-only lookup selects only the exact
event27 admitted by the same verified walk, including its initialized cell root.
-/
import Kernel.NativeHost

namespace Minidregg.Kernel.ApplicationAgentLifetimeGrantReceiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.ApplicationAgentLifetimeGrantSource
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

def transaction (config : Config) (ingress : Ingress) :
    Minidregg.Theory.TypedAuthorization.Digest :=
  ResourceBirthController.Concrete.sourceIdentity config.profile.compilerProfile
    config.deployment ingress.spec.grant.approval.issuer
    ingress.spec.grant.approval.nonce

/-- A transaction ID occupied by a different original is a conflict, not a
missing grant that may be freshly submitted. -/
def lookupVerified {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress) :
    Option (Except String (NativeHostReplay.PriorLifetimeGrant config)) := do
  let tx := transaction config ingress
  let some _ := verified.opened.durable.image.accepted.find?
      (fun record => record.transactionId == tx)
    | none
  let some original := verified.grants.find?
      (fun prior => prior.record.transactionId == tx)
    | some (.error "agent lifetime grant transaction is not an admitted event27")
  if original.ingress.canonicalBytes.toByteArray ==
      ingress.canonicalBytes.toByteArray then
    some (.ok original)
  else some (.error "agent lifetime grant original ingress differs")

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation)
      (receipt : NativeHostCodec.Receipt) (index : Nat)
      (finalRoot : Minidregg.Theory.TypedAuthorization.Digest)
  | rejected (detail : String)
  | transactionConflict
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def confirmReadback (config : Config) (ingress : Ingress)
    (kind : DurableReceiverIO.Confirmation) : IO Result := do
  match ← NativeHost.openExisting config with
  | .error _ => return .uncertain "agent lifetime grant readback unavailable"
  | .ok opened =>
      let ⟨_, reader⟩ ← match ← NativeHost.historyReaderOfDurable config opened.durable with
        | .error refusal => return .uncertain ("agent lifetime grant readback history reader: " ++ refusal.detail)
        | .ok reader => pure reader
      match ← NativeHostReplay.verifyLoaded config reader opened.durable with
      | .error _ => return .uncertain "agent lifetime grant readback unverified"
      | .ok verified =>
          match lookupVerified verified ingress with
          | some (.ok original) =>
              return .confirmed kind original.receipt original.index original.finalRoot
          | _ => return .uncertain "agent lifetime grant original receipt unavailable"

/-- The exact source-derived birth and current app `.delegateObject` check are
re-derived from the verifier's private event22 history before the durable CAS.
Uncertain replies are recovered by lookup, never by making another grant. -/
def receiveVerified {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    IO Result := do
  let some ingress := ingressCodec.decode bytes
    | return .rejected "noncanonical agent lifetime grant ingress"
  unless ingress.canonicalBytes.toByteArray == bytes.toByteArray do
    return .rejected "noncanonical agent lifetime grant ingress"
  match lookupVerified verified ingress with
  | some (.ok original) =>
      return .confirmed .replayed original.receipt original.index original.finalRoot
  | some (.error _) => return .transactionConflict
  | none =>
      match ← NativeHostReplay.deriveVerified verified bytes with
      | .error _ => return .rejected "agent lifetime grant admission refused"
      | .ok derived =>
          match derived.grantIssue with
          | none => return .rejected "agent lifetime grant lacks original event22"
          | some ⟨selected, admitted⟩ =>
              unless selected.canonicalBytes.toByteArray == bytes.toByteArray do
                return .rejected "agent lifetime grant derived ingress differs"
              let _ := admitted
              match ← DurableReceiverIO.receiveLoaded config.transport
                  ResourceBirthCodec.rootBytes verified.opened.durable derived.intent with
              | .confirmed kind _ => confirmReadback config ingress kind
              | .rejected _ => return .rejected "agent lifetime grant durable refusal"
              | .contention => return .contention
              | .unavailable detail => return .unavailable detail
              | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationAgentLifetimeGrantReceiver
