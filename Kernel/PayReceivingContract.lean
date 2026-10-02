/-
Pure paid receiving identity shared by actual codecs/policy defaults and the
runtime profile. This leaf imports no receiver or runtime profile. Wire frames
remain byte-identical; the receiving revision explicitly binds meaning beyond
the PayCell schema. Numeric public operation allocation belongs to the native
control registry; this leaf does not claim that routing metadata is a
runtime-profile input.
-/
import Init

namespace Minidregg.Kernel.PayReceivingContract

/-- V1 allocation/replay remains explicit. V2 allocates exact requested weeks,
keeps every authenticated deposit as one immutable origin, atomically consumes
it once, and retains stale/expired value pending with zero mint. Fresh claims
use current owner/epoch (or precommitted successor for pending rotation), stable
identity and original deployment seed. Expiry is inclusive processing chain
hour from authenticated monotone evidence; exact historical replay precedes
current law, freshness, expiry and custody decisions. -/
def receivingVersion : List UInt8 :=
  "DREGG/PAY/RECEIVING/v2/exact-weeks-origin-consumption-current-custody-chain-tip".toUTF8.toList

@[simp] def memoPrefix : List UInt8 := "enrol:v2:".toUTF8.toList
@[simp] def memoPossession : List UInt8 := "DREGG/PAY/ENROL/POSSESSION/v2".toUTF8.toList
@[simp] def sshNamespace : List UInt8 := "dregg-enrol@v2".toUTF8.toList
@[simp] def observationFrame : List UInt8 := "DREGG/PAY/CLAIM/OBSERVATION/v1".toUTF8.toList
@[simp] def claimFrame : List UInt8 := "DREGG/PAY/CLAIM/v2".toUTF8.toList
@[simp] def pendingOwnerFrame : List UInt8 := "DREGG/PAY/PENDING-OWNER/v1".toUTF8.toList
@[simp] def acceptRequestFrame : List UInt8 := "DREGG/PAY/CLAIM/ACCEPT/v1".toUTF8.toList
@[simp] def consumptionFrame : List UInt8 := "DREGG/PAY/CLAIM/CONSUMPTION/v2".toUTF8.toList
@[simp] def commandFrame : List UInt8 := "DREGG/PAY/CLAIM/COMMAND/v1".toUTF8.toList
@[simp] def claimPossession : List UInt8 := "DREGG/PAY/CLAIM/POSSESSION/v1".toUTF8.toList
@[simp] def ingressFrame : List UInt8 := "DREGG/PAY/CLAIM/SIGNED/v1".toUTF8.toList
@[simp] def quoteRequestFrame : List UInt8 := "DREGG/PAY/CLAIM-QUOTE/REQUEST/v1".toUTF8.toList
@[simp] def quoteResponseFrame : List UInt8 := "DREGG/PAY/CLAIM-QUOTE/RESPONSE/v1".toUTF8.toList

@[simp] def unsignedMemoBytes : Nat := 229
@[simp] def binaryMemoBytes : Nat := 357
@[simp] def textMemoBytes : Nat := 485
@[simp] def maxQuoteLifetimeHours : Nat := 1
@[simp] def defaultMaxLagSeconds : Nat := 180

/-- Actual receiving frames, not a duplicate manifest of their spellings. -/
def frames : List (List UInt8) :=
  [receivingVersion, memoPrefix, memoPossession, sshNamespace, observationFrame,
   claimFrame, pendingOwnerFrame, acceptRequestFrame, consumptionFrame,
   commandFrame, claimPossession, ingressFrame, quoteRequestFrame, quoteResponseFrame]

def parameters : List Nat :=
  [unsignedMemoBytes, binaryMemoBytes, textMemoBytes,
   maxQuoteLifetimeHours, defaultMaxLagSeconds]

end Minidregg.Kernel.PayReceivingContract
