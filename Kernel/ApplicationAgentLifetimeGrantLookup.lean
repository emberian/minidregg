/-
Historical event27 lookup returns only a verifier-minted original. It cannot
issue a new grant, reinterpret the old ticket, or authorize a later dispatch.
-/
import Kernel.ApplicationAgentLifetimeGrantReceiver

namespace Minidregg.Kernel.ApplicationAgentLifetimeGrantLookup

open Minidregg.Kernel
open Minidregg.Kernel.ApplicationAgentLifetimeGrantSource
open Minidregg.Compiler

set_option autoImplicit false

structure Original where
  ingress : Ingress
  index : Nat
  receipt : NativeHostCodec.Receipt
  finalRoot : Minidregg.Theory.TypedAuthorization.Digest

def lookupVerified {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    Except String (Option Original) := do
  let some ingress := ingressCodec.decode bytes
    | throw "noncanonical agent lifetime grant lookup ingress"
  if ingress.canonicalBytes.toByteArray != bytes.toByteArray then
    throw "noncanonical agent lifetime grant lookup ingress"
  match ApplicationAgentLifetimeGrantReceiver.lookupVerified verified ingress with
  | none => pure none
  | some (.error detail) => throw detail
  | some (.ok original) =>
      pure (some ⟨original.ingress, original.index,
        original.receipt, original.finalRoot⟩)

def lookupCurrent (config : NativeHost.Config) (bytes : List UInt8) :
    IO (Except String (Option Original)) := do
  match ← NativeHost.openExisting config with
  | .error detail => return .error detail
  | .ok opened =>
      let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf config.transport ResourceBirthCodec.rootBytes opened.durable with
        | .error _ => return .error "agent lifetime grant history reader unavailable"
        | .ok reader => pure reader
      match ← NativeHostReplay.verifyLoaded config reader opened.durable with
      | .error _ => return .error "agent lifetime grant history unverified"
      | .ok verified => return lookupVerified verified bytes

end Minidregg.Kernel.ApplicationAgentLifetimeGrantLookup
