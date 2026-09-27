/-
The distinct reserve signature context for event26. Event21's v2 context and
nonce remain unchanged. This v3 context commits the exact issued grant as
well as the HTTP request and current parent/purse coordinates before a
worker can request delivery.
-/
import Kernel.ApplicationAgentLifetimeGrant
import Kernel.ApplicationDispatchAgentReserveContext

namespace Minidregg.Kernel.ApplicationAgentLifetimeDispatchReserveContext

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ApplicationDispatchAgentReserveContext

set_option autoImplicit false

def grantDigest (grant : ApplicationAgentLifetimeGrant.Grant) : Digest :=
  (Sp800185Cshake256.hash
    "DREGG/APPLICATION/AGENT-LIFETIME-RESERVE-GRANT/v1".toUTF8.toList
    grant.canonicalBytes).digest

structure Context where
  base : ApplicationDispatchAgentReserveContext.Context
  grantResource : Nat
  grantIssueIndex : Nat
  grantDigest : Digest
  deriving DecidableEq, Repr

def contextStream : StreamCodec Context :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationDispatchAgentReserveContext.contextStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat digestStream)))
    (fun context => (context.base, context.grantResource,
      context.grantIssueIndex, context.grantDigest))
    (fun (base, grantResource, grantIssueIndex, grantDigest) =>
      ⟨base, grantResource, grantIssueIndex, grantDigest⟩)
    (by intro context; cases context; rfl)

def codec : LawfulCodec Context := ResourceBirthCodec.strictCodec
  (Minidregg.Compiler.NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-LIFETIME-RESERVE-CONTEXT/v3".toUTF8.toList
    contextStream)

def Context.canonicalBytes (context : Context) : List UInt8 :=
  codec.encode context

theorem decode_encode (context : Context) :
    codec.decode context.canonicalBytes = some context :=
  codec.decode_encode context

theorem canonicalBytes_injective : Function.Injective Context.canonicalBytes := by
  intro left right same
  have decoded := congrArg codec.decode same
  exact Option.some.inj (by simpa only [decode_encode] using decoded)

/-- Both the reserve and the later payer no-op use v3 nonces. Neither is
interchangeable with its event21 counterpart at the same app/request bytes. -/
def reserveNonce (context : Context) : Nat :=
  AgentGrain.contextNonce
    ("DREGG/APPLICATION/AGENT-LIFETIME-RESERVE/v3".toUTF8.toList ++
      context.canonicalBytes)

def payerNonce (context : Context) : Nat :=
  AgentGrain.contextNonce
    ("DREGG/APPLICATION/AGENT-LIFETIME-PAYER/v3".toUTF8.toList ++
      context.canonicalBytes)

def matchesGrant (context : Context)
    (grant : ApplicationAgentLifetimeGrant.Grant)
    (certifiedIssueIndex : Nat) : Bool :=
  decide (context.grantResource = grant.source.resource ∧
    context.grantIssueIndex = certifiedIssueIndex ∧
    context.grantDigest = grantDigest grant)

theorem matchesGrant_exact (context : Context)
    (grant : ApplicationAgentLifetimeGrant.Grant) (certifiedIssueIndex : Nat)
    (matched : matchesGrant context grant certifiedIssueIndex = true) :
    context.grantResource = grant.source.resource ∧
    context.grantIssueIndex = certifiedIssueIndex ∧
    context.grantDigest = grantDigest grant := by
  simpa only [matchesGrant, decide_eq_true_eq] using matched

end Minidregg.Kernel.ApplicationAgentLifetimeDispatchReserveContext
