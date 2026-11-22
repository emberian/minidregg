/-
# `Compiler/PocketFpgaCaptpVat.lean` — Wearable SHE Organ #6 (Gap #1 Pocket-FPGA Companion)
Formalizes `Dregg-180` `dregg_captp_vat` RTL + 2-slot SPI-FRAM monotone counter + LUT4/PIP bitstream readback.
-/
import Init.Data.BitVec.Lemmas
import Init.Data.List.Pairwise
namespace Minidregg.Compiler.PocketFpgaCaptpVat
set_option autoImplicit false
set_option maxRecDepth 20000

/-! ## §1. Synchronous Cycle-Level `PocketCaptpVatRtl` -/
structure SecretKeyRegs where (k0 k1 k2 k3 : UInt64) deriving DecidableEq, Repr, Inhabited
def zeroSecretKey : SecretKeyRegs := ⟨0, 0, 0, 0⟩
structure PolicyDigest256 where (d0 d1 d2 d3 : BitVec 64) deriving DecidableEq, Repr, Inhabited
def guardStatefulFram : UInt16 := 0x0001
def guardPhysTouch    : UInt16 := 0x0002
def guardTofDist      : UInt16 := 0x0004
def guardPinVk        : UInt16 := 0x0008
def rightAttenuateBit : UInt16 := 0x0008
structure CapPolicyRegs where
  (rightsMask guardsMask : UInt16)
  (maxTofCycles epochFloor epochCeil spendLimit spendUsed : UInt32)
  policyDigest : PolicyDigest256
  deriving DecidableEq, Repr, Inhabited

def attenuateChildLegal (parent child : CapPolicyRegs) : Bool :=
  ((parent.rightsMask &&& rightAttenuateBit) == rightAttenuateBit) &&
  ((child.rightsMask &&& (~~~parent.rightsMask)) == 0) &&
  ((child.guardsMask &&& parent.guardsMask) == parent.guardsMask) &&
  (child.maxTofCycles.toNat <= parent.maxTofCycles.toNat) &&
  (parent.epochFloor.toNat <= child.epochFloor.toNat) &&
  (child.epochCeil.toNat <= parent.epochCeil.toNat) &&
  (child.epochFloor.toNat <= child.epochCeil.toNat) &&
  (child.spendLimit.toNat <= parent.spendLimit.toNat) && (child.spendLimit != 0)

theorem captp_attenuation_monotone_non_amplifying (parent child : CapPolicyRegs)
    (hLegal : attenuateChildLegal parent child = true) :
    child.rightsMask &&& (~~~parent.rightsMask) = 0 ∧
    child.guardsMask &&& parent.guardsMask = parent.guardsMask ∧
    child.maxTofCycles.toNat ≤ parent.maxTofCycles.toNat ∧
    parent.epochFloor.toNat ≤ child.epochFloor.toNat ∧
    child.epochCeil.toNat ≤ parent.epochCeil.toNat ∧
    child.spendLimit.toNat ≤ parent.spendLimit.toNat := by
  unfold attenuateChildLegal at hLegal
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hLegal
  exact ⟨hLegal.1.1.1.1.1.1.1.2, hLegal.1.1.1.1.1.1.2, hLegal.1.1.1.1.1.2,
         hLegal.1.1.1.1.2, hLegal.1.1.1.2, hLegal.1.2⟩

inductive VatFsmState where | Idle | Prepared | FramCommitted | SignArmed | DeadZeroized deriving DecidableEq, Repr, Inhabited
def spiOpNop         : UInt8 := 0x00
def spiOpReadDiag    : UInt8 := 0x05
def spiOpKeyLoad     : UInt8 := 0x40
def spiOpPrepSign    : UInt8 := 0x41
def spiOpFramCommit  : UInt8 := 0x43
def spiOpTriggerSign : UInt8 := 0x44
def spiOpAttenuate   : UInt8 := 0x52
structure VatCycleInput where
  spiCmdByte : UInt8
  spiArgWord : UInt64
  spiCandidatePolicy : CapPolicyRegs
  spiCandidateKey : SecretKeyRegs
  (reqEpoch reqSpend : UInt32)
  reqRightBit : UInt16
  measuredTofCycles : UInt32
  (framReadbackOk publicDiagBit msgChallengeBit physTouchAck tofWithinRadius tamperCanaryTripped : Bool)
  deriving DecidableEq, Repr, Inhabited
structure VatRtlState where
  fsm : VatFsmState
  secretKeyRegs : SecretKeyRegs
  (keyValid tamperLatched : Bool)
  policy : CapPolicyRegs
  (pendingLeaf hwmLeaf : UInt64)
  deriving DecidableEq, Repr, Inhabited
def initVatRtlState (genesisPolicy : CapPolicyRegs) : VatRtlState := ⟨.Idle, zeroSecretKey, false, false, genesisPolicy, 0, 0⟩
def vatPolicyInvokeLegal (st : VatRtlState) (inp : VatCycleInput) : Bool :=
  st.keyValid && ((st.policy.rightsMask &&& inp.reqRightBit) == inp.reqRightBit) &&
  (st.policy.epochFloor.toNat <= inp.reqEpoch.toNat) && (inp.reqEpoch.toNat <= st.policy.epochCeil.toNat) &&
  (st.policy.spendUsed.toNat + inp.reqSpend.toNat <= st.policy.spendLimit.toNat) &&
  (inp.measuredTofCycles.toNat <= st.policy.maxTofCycles.toNat)
def vatSignEnable (st : VatRtlState) (inp : VatCycleInput) : Bool :=
  !st.tamperLatched && !inp.tamperCanaryTripped && st.keyValid &&
  (st.fsm == .SignArmed) && vatPolicyInvokeLegal st inp && inp.physTouchAck && inp.tofWithinRadius
structure VatCycleOutput where (vatSignEnable spiMiso tamperFault : Bool) deriving DecidableEq, Repr, Inhabited
def evalVatRtlOutput (st : VatRtlState) (inp : VatCycleInput) : VatCycleOutput :=
  let signEn := vatSignEnable st inp
  let sigBit := signEn && (((st.secretKeyRegs.k0 &&& 1) == 1) != inp.msgChallengeBit)
  ⟨signEn, if signEn then sigBit else inp.publicDiagBit, st.tamperLatched || inp.tamperCanaryTripped⟩

def stepVatRtl (st : VatRtlState) (inp : VatCycleInput) : VatRtlState :=
  if st.tamperLatched || inp.tamperCanaryTripped then
    { st with fsm := .DeadZeroized, secretKeyRegs := zeroSecretKey, keyValid := false, tamperLatched := true }
  else if inp.spiCmdByte == spiOpKeyLoad then
    if !st.keyValid then
      { st with fsm := .Idle, secretKeyRegs := inp.spiCandidateKey, keyValid := true,
                policy := { inp.spiCandidatePolicy with spendUsed := 0 } }
    else { st with fsm := .Idle }
  else if inp.spiCmdByte == spiOpAttenuate then
    if st.keyValid && attenuateChildLegal st.policy inp.spiCandidatePolicy then
      { st with fsm := .Idle, policy := { inp.spiCandidatePolicy with spendUsed := st.policy.spendUsed } }
    else { st with fsm := .Idle }
  else if inp.spiCmdByte == spiOpPrepSign then
    if st.keyValid && (st.hwmLeaf.toNat <= inp.spiArgWord.toNat) && (inp.spiArgWord != 0xFFFFFFFFFFFFFFFF) then
      { st with fsm := .Prepared, pendingLeaf := inp.spiArgWord }
    else { st with fsm := .Idle }
  else if inp.spiCmdByte == spiOpFramCommit then
    if st.fsm == .Prepared && inp.framReadbackOk && vatPolicyInvokeLegal st inp then
      { st with fsm := .FramCommitted, hwmLeaf := st.pendingLeaf + 1 }
    else { st with fsm := .Idle }
  else if inp.spiCmdByte == spiOpTriggerSign then
    if st.fsm == .FramCommitted && vatPolicyInvokeLegal st inp && inp.physTouchAck && inp.tofWithinRadius then
      { st with fsm := .SignArmed }
    else { st with fsm := .Idle }
  else if st.fsm == .SignArmed then
    let nextSpend := if vatSignEnable st inp then UInt32.ofNat (st.policy.spendUsed.toNat + inp.reqSpend.toNat) else st.policy.spendUsed
    { st with fsm := .Idle, policy := { st.policy with spendUsed := nextSpend } }
  else { st with fsm := .Idle }

def runVatRtlTrace : VatRtlState → List VatCycleInput → List VatCycleOutput × VatRtlState
  | st, [] => ([], st)
  | st, inp :: rest =>
    let tail := runVatRtlTrace (stepVatRtl st inp) rest
    (evalVatRtlOutput st inp :: tail.1, tail.2)

theorem vatSignEnable_false_of_missing_touch_or_tof (st : VatRtlState) (inp : VatCycleInput)
    (hGate : inp.physTouchAck = false ∨ inp.tofWithinRadius = false ∨
             inp.tamperCanaryTripped = true ∨ st.tamperLatched = true) :
    vatSignEnable st inp = false := by
  unfold vatSignEnable; rcases hGate with h | h | h | h <;> simp [h]

theorem compromised_host_cannot_sign_without_touch_and_tof
    (st₀ : VatRtlState) (trace : List VatCycleInput)
    (hNoPresence : ∀ inp ∈ trace, inp.physTouchAck = false ∨ inp.tofWithinRadius = false ∨ inp.tamperCanaryTripped = true) :
    ∀ out ∈ (runVatRtlTrace st₀ trace).1, out.vatSignEnable = false := by
  induction trace generalizing st₀ with
  | nil => intro out hMem; simp [runVatRtlTrace] at hMem
  | cons inp rest ih =>
    intro out hMem; simp only [runVatRtlTrace, List.mem_cons] at hMem
    rcases hMem with rfl | hTail
    · simp only [evalVatRtlOutput]
      rcases hNoPresence inp (List.mem_cons_self ..) with h | h | h
      · exact vatSignEnable_false_of_missing_touch_or_tof st₀ inp (Or.inl h)
      · exact vatSignEnable_false_of_missing_touch_or_tof st₀ inp (Or.inr (Or.inl h))
      · exact vatSignEnable_false_of_missing_touch_or_tof st₀ inp (Or.inr (Or.inr (Or.inl h)))
    · exact ih (stepVatRtl st₀ inp) (fun x hx => hNoPresence x (List.mem_cons_of_mem _ hx)) out hTail

private theorem tampered_trace_stays_zeroized (st : VatRtlState) (suffix : List VatCycleInput)
    (hLatched : st.tamperLatched = true) (hZero : st.secretKeyRegs = zeroSecretKey) :
    (runVatRtlTrace st suffix).2.secretKeyRegs = zeroSecretKey ∧
    (runVatRtlTrace st suffix).2.tamperLatched = true ∧
    ∀ out ∈ (runVatRtlTrace st suffix).1, out.vatSignEnable = false := by
  induction suffix generalizing st with
  | nil => simp [runVatRtlTrace, hLatched, hZero]
  | cons inp rest ih =>
    have hOut0 : (evalVatRtlOutput st inp).vatSignEnable = false := by
      simp only [evalVatRtlOutput]
      exact vatSignEnable_false_of_missing_touch_or_tof st inp (Or.inr (Or.inr (Or.inr hLatched)))
    have hStep : (stepVatRtl st inp).tamperLatched = true ∧ (stepVatRtl st inp).secretKeyRegs = zeroSecretKey := by
      unfold stepVatRtl; simp [hLatched]
    have ⟨hEndZ, hEndL, hTailOuts⟩ := ih (stepVatRtl st inp) hStep.1 hStep.2
    refine ⟨hEndZ, hEndL, fun out hMem => ?_⟩
    simp only [runVatRtlTrace, List.mem_cons] at hMem
    rcases hMem with rfl | hMemRest
    · exact hOut0
    · exact hTailOuts out hMemRest

theorem tamper_canary_zeroizes_keys_in_one_cycle_and_locks_forever
    (st₀ : VatRtlState) (inp₀ : VatCycleInput) (suffix : List VatCycleInput) (hTrip : inp₀.tamperCanaryTripped = true) :
    (evalVatRtlOutput st₀ inp₀).vatSignEnable = false ∧
    (stepVatRtl st₀ inp₀).secretKeyRegs = zeroSecretKey ∧
    (runVatRtlTrace (stepVatRtl st₀ inp₀) suffix).2.secretKeyRegs = zeroSecretKey ∧
    (∀ out ∈ (runVatRtlTrace (stepVatRtl st₀ inp₀) suffix).1, out.vatSignEnable = false) := by
  have hImm : (evalVatRtlOutput st₀ inp₀).vatSignEnable = false := by
    simp only [evalVatRtlOutput]
    exact vatSignEnable_false_of_missing_touch_or_tof st₀ inp₀ (Or.inr (Or.inr (Or.inl hTrip)))
  have hStep1 : (stepVatRtl st₀ inp₀).secretKeyRegs = zeroSecretKey ∧ (stepVatRtl st₀ inp₀).tamperLatched = true := by
    unfold stepVatRtl; cases st₀.tamperLatched <;> simp [hTrip]
  have ⟨hEndZ, _, hSuffixFalse⟩ := tampered_trace_stays_zeroized (stepVatRtl st₀ inp₀) suffix hStep1.2 hStep1.1
  exact ⟨hImm, hStep1.1, hEndZ, hSuffixFalse⟩

def brokenCsrSignEnable (csrPresenceOverride : Bool) (st : VatRtlState) (inp : VatCycleInput) : Bool :=
  !st.tamperLatched && !inp.tamperCanaryTripped && st.keyValid && (st.fsm == .SignArmed) &&
  (inp.physTouchAck || csrPresenceOverride) && (inp.tofWithinRadius || csrPresenceOverride)

theorem tooth_software_csr_touch_override_allows_forged_sign :
    ∃ (st : VatRtlState) (inp : VatCycleInput),
      inp.physTouchAck = false ∧ inp.tofWithinRadius = false ∧
      brokenCsrSignEnable true st inp = true ∧ vatSignEnable st inp = false := by
  let pol : CapPolicyRegs := ⟨0xFFFF, 0x0007, 100, 1, 10, 50, 0, ⟨1#64, 2#64, 3#64, 4#64⟩⟩
  let st : VatRtlState := ⟨.SignArmed, ⟨0xCAFE, 1, 2, 3⟩, true, false, pol, 0, 0⟩
  let inp : VatCycleInput := ⟨spiOpNop, 0, pol, zeroSecretKey, 5, 1, 1, 20, true, false, false, false, false, false⟩
  refine ⟨st, inp, rfl, rfl, ?_, ?_⟩ <;> decide

/-! ## §2. Any-Bit Power-Cut Atomic 2-Slot SPI-FRAM Monotone Counter (`512`-Bit Slots) -/
structure Bits512 where (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) deriving DecidableEq, Repr, Inhabited
def zeroBits512 : Bits512 := ⟨0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64⟩
def bits512Word (b : Bits512) : Nat → BitVec 64
  | 0 => b.w0 | 1 => b.w1 | 2 => b.w2 | 3 => b.w3 | 4 => b.w4 | 5 => b.w5 | 6 => b.w6 | _ => b.w7
def bits512Bit (b : Bits512) (idx : Nat) : Bool := (bits512Word b (idx / 64)).getLsbD (idx % 64)
def tearWord64 (oldW newW : BitVec 64) (localCut : Nat) : BitVec 64 :=
  if localCut == 0 then oldW else if 64 <= localCut then newW
  else let mask : BitVec 64 := (1#64 <<< localCut) - 1#64; (newW &&& mask) ||| (oldW &&& (~~~mask))
def tearBits512 (oldRaw newRaw : Bits512) (cutBit : Nat) : Bits512 :=
  ⟨tearWord64 oldRaw.w0 newRaw.w0 (cutBit - 0),   tearWord64 oldRaw.w1 newRaw.w1 (cutBit - 64),
   tearWord64 oldRaw.w2 newRaw.w2 (cutBit - 128), tearWord64 oldRaw.w3 newRaw.w3 (cutBit - 192),
   tearWord64 oldRaw.w4 newRaw.w4 (cutBit - 256), tearWord64 oldRaw.w5 newRaw.w5 (cutBit - 320),
   tearWord64 oldRaw.w6 newRaw.w6 (cutBit - 384), tearWord64 oldRaw.w7 newRaw.w7 (cutBit - 448)⟩

private theorem mask64_all_ok :
    ((List.range 64).all fun k => (List.range 64).all fun j =>
      (((1#64 <<< k) - 1#64).getLsbD j) == decide (j < k)) = true := by decide
private theorem mask64_getLsbD (k j : Nat) (hk : k < 64) (hj : j < 64) :
    (((1#64 <<< k) - 1#64).getLsbD j) = decide (j < k) :=
  beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp mask64_all_ok k (List.mem_range.mpr hk)) j (List.mem_range.mpr hj))

theorem tearWord64_getLsbD (oldW newW : BitVec 64) (localCut j : Nat) (hj : j < 64) :
    (tearWord64 oldW newW localCut).getLsbD j = if j < localCut then newW.getLsbD j else oldW.getLsbD j := by
  unfold tearWord64
  by_cases h0 : localCut == 0
  · have hz : localCut = 0 := beq_iff_eq.mp h0; subst hz; simp
  · by_cases h64 : 64 ≤ localCut
    · have hlt : j < localCut := by omega
      simp [h0, h64, hlt]
    · have hklt : localCut < 64 := by omega
      have h64b : (64 <= localCut) = false := by simp [h64]
      simp only [h0, h64b, Bool.false_eq_true, ite_false]
      rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_and, BitVec.getLsbD_not, mask64_getLsbD localCut j hklt hj]
      by_cases hjlt : j < localCut <;> simp [hj, hjlt]

private theorem lt8_cases {q : Nat} (hq : q < 8) :
    q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 := by omega

theorem bits512Bit_tearBits512 (oldRaw newRaw : Bits512) (cutBit i : Nat) (hi : i < 512) :
    bits512Bit (tearBits512 oldRaw newRaw cutBit) i =
      if i < cutBit then bits512Bit newRaw i else bits512Bit oldRaw i := by
  unfold bits512Bit
  have hrem : i % 64 < 64 := Nat.mod_lt _ (by omega)
  have hdiv : i / 64 < 8 := by omega
  rcases lt8_cases hdiv with hq | hq | hq | hq | hq | hq | hq | hq <;>
    (rw [hq]; simp only [bits512Word, tearBits512, Nat.sub_zero, tearWord64_getLsbD _ _ _ _ hrem];
     by_cases hlt : i < cutBit
     · have hc : i % 64 < cutBit - (i / 64) * 64 := by omega
       rw [hq] at hc; try simp only [Nat.zero_mul, Nat.sub_zero] at hc
       simp [hlt, hc]
     · have hc : ¬(i % 64 < cutBit - (i / 64) * 64) := by omega
       rw [hq] at hc; try simp only [Nat.zero_mul, Nat.sub_zero] at hc
       simp [hlt, hc])

theorem tearWord64_zero (oldW newW : BitVec 64) : tearWord64 oldW newW 0 = oldW := rfl
theorem tearWord64_of_ge64 (oldW newW : BitVec 64) {k : Nat} (hk : 64 ≤ k) : tearWord64 oldW newW k = newW := by
  unfold tearWord64; have h0 : (k == 0) = false := by rw [beq_eq_false_iff_ne]; omega
  simp [h0, hk]
theorem tearBits512_complete (oldRaw newRaw : Bits512) {cutBit : Nat} (hFull : 512 ≤ cutBit) :
    tearBits512 oldRaw newRaw cutBit = newRaw := by
  unfold tearBits512
  rw [tearWord64_of_ge64 _ _ (by omega), tearWord64_of_ge64 _ _ (by omega),
      tearWord64_of_ge64 _ _ (by omega), tearWord64_of_ge64 _ _ (by omega),
      tearWord64_of_ge64 _ _ (by omega), tearWord64_of_ge64 _ _ (by omega),
      tearWord64_of_ge64 _ _ (by omega), tearWord64_of_ge64 _ _ (by omega)]

structure FramSlotRecord where
  policyDigest : PolicyDigest256
  (leafIdx spendUsed epochSeq crcTag : BitVec 64)
  deriving DecidableEq, Repr, Inhabited
def crc64StepBit (crc : BitVec 64) (bit : Bool) : BitVec 64 :=
  if (crc.getLsbD 0) != bit then (crc >>> 1) ^^^ 0xC96C5795D7870F42#64 else crc >>> 1
def crc64AbsorbWord (crc : BitVec 64) (w : BitVec 64) : BitVec 64 :=
  (List.range 64).foldl (fun acc i => crc64StepBit acc (w.getLsbD i)) crc
def computeFramCrcTag (pd : PolicyDigest256) (leafIdx spendUsed epochSeq : BitVec 64) : BitVec 64 :=
  ([pd.d0, pd.d1, pd.d2, pd.d3, leafIdx, spendUsed, epochSeq].foldl crc64AbsorbWord 0x445247314652414D#64) ^^^
    0xFFFFFFFFFFFFFFFF#64
def mkValidFramRecord (pd : PolicyDigest256) (leafIdx spendUsed epochSeq : BitVec 64) : FramSlotRecord :=
  ⟨pd, leafIdx, spendUsed, epochSeq, computeFramCrcTag pd leafIdx spendUsed epochSeq⟩
def encodeFramSlot (r : FramSlotRecord) : Bits512 :=
  ⟨r.policyDigest.d0, r.policyDigest.d1, r.policyDigest.d2, r.policyDigest.d3, r.leafIdx, r.spendUsed, r.epochSeq, r.crcTag⟩
def decodeFramSlot (raw : Bits512) : FramSlotRecord :=
  ⟨⟨raw.w0, raw.w1, raw.w2, raw.w3⟩, raw.w4, raw.w5, raw.w6, raw.w7⟩
theorem decodeFramSlot_encodeFramSlot (r : FramSlotRecord) : decodeFramSlot (encodeFramSlot r) = r := rfl
def framSlotValid (raw : Bits512) : Bool :=
  let r := decodeFramSlot raw
  (r.epochSeq != 0#64) && (r.epochSeq != 0xFFFFFFFFFFFFFFFF#64) &&
  (r.crcTag == computeFramCrcTag r.policyDigest r.leafIdx r.spendUsed r.epochSeq)
theorem framSlotValid_mkValid (pd : PolicyDigest256) (leafIdx spendUsed epochSeq : BitVec 64)
    (hNz : epochSeq ≠ 0#64) (hNotMax : epochSeq ≠ 0xFFFFFFFFFFFFFFFF#64) :
    framSlotValid (encodeFramSlot (mkValidFramRecord pd leafIdx spendUsed epochSeq)) = true := by
  unfold framSlotValid mkValidFramRecord encodeFramSlot decodeFramSlot; simp [hNz, hNotMax]

structure DualSlotFram where (slot0 slot1 : Bits512) deriving DecidableEq, Repr, Inhabited
def recoverDualFram (dual : DualSlotFram) : Option FramSlotRecord :=
  if framSlotValid dual.slot0 && framSlotValid dual.slot1 then
    if (decodeFramSlot dual.slot0).epochSeq.toNat < (decodeFramSlot dual.slot1).epochSeq.toNat then
      some (decodeFramSlot dual.slot1)
    else some (decodeFramSlot dual.slot0)
  else if framSlotValid dual.slot0 then some (decodeFramSlot dual.slot0)
  else if framSlotValid dual.slot1 then some (decodeFramSlot dual.slot1)
  else none
def selectStandbySlot (dual : DualSlotFram) : Bool :=
  if framSlotValid dual.slot0 && framSlotValid dual.slot1 then
    !((decodeFramSlot dual.slot0).epochSeq.toNat < (decodeFramSlot dual.slot1).epochSeq.toNat)
  else framSlotValid dual.slot0
def writeStandbyWithPowerCut (dual : DualSlotFram) (newRaw : Bits512) (cutBit : Nat) : DualSlotFram :=
  if selectStandbySlot dual then { dual with slot1 := tearBits512 dual.slot1 newRaw cutBit }
  else { dual with slot0 := tearBits512 dual.slot0 newRaw cutBit }
def WellFormedDualFram (dual : DualSlotFram) : Prop :=
  (framSlotValid dual.slot0 = true ∧ (decodeFramSlot dual.slot1).epochSeq.toNat < (decodeFramSlot dual.slot0).epochSeq.toNat) ∨
  (framSlotValid dual.slot1 = true ∧ (decodeFramSlot dual.slot0).epochSeq.toNat < (decodeFramSlot dual.slot1).epochSeq.toNat)
def genesisDualFram (pd : PolicyDigest256) : DualSlotFram := ⟨encodeFramSlot (mkValidFramRecord pd 0#64 0#64 1#64), zeroBits512⟩
theorem genesisDualFram_wellFormed (pd : PolicyDigest256) : WellFormedDualFram (genesisDualFram pd) := by
  refine Or.inl ⟨framSlotValid_mkValid pd 0#64 0#64 1#64 (by decide) (by decide), ?_⟩
  simp [genesisDualFram, decodeFramSlot, encodeFramSlot, mkValidFramRecord, zeroBits512]

private theorem wf_slot0_active {dual : DualSlotFram} {rec : FramSlotRecord}
    (hv0 : framSlotValid dual.slot0 = true)
    (hlt10 : (decodeFramSlot dual.slot1).epochSeq.toNat < (decodeFramSlot dual.slot0).epochSeq.toNat)
    (hRec : recoverDualFram dual = some rec) :
    rec = decodeFramSlot dual.slot0 ∧ selectStandbySlot dual = true := by
  have hNot : ¬((decodeFramSlot dual.slot0).epochSeq.toNat < (decodeFramSlot dual.slot1).epochSeq.toNat) := by omega
  unfold recoverDualFram at hRec; unfold selectStandbySlot
  cases hv1 : framSlotValid dual.slot1
  · simp [hv0, hv1] at hRec ⊢; exact hRec.symm
  · simp [hv0, hv1, hNot] at hRec ⊢; exact hRec.symm

private theorem wf_slot1_active {dual : DualSlotFram} {rec : FramSlotRecord}
    (hv1 : framSlotValid dual.slot1 = true)
    (hlt01 : (decodeFramSlot dual.slot0).epochSeq.toNat < (decodeFramSlot dual.slot1).epochSeq.toNat)
    (hRec : recoverDualFram dual = some rec) :
    rec = decodeFramSlot dual.slot1 ∧ selectStandbySlot dual = false := by
  unfold recoverDualFram at hRec; unfold selectStandbySlot
  cases hv0 : framSlotValid dual.slot0
  · simp [hv0, hv1] at hRec ⊢; exact hRec.symm
  · simp [hv0, hv1, hlt01] at hRec ⊢; exact hRec.symm

theorem recoverDualFram_of_wellFormed {dual : DualSlotFram} (hWf : WellFormedDualFram dual) :
    ∃ activeRec, recoverDualFram dual = some activeRec := by
  unfold recoverDualFram
  rcases hWf with ⟨hv0, _⟩ | ⟨hv1, _⟩
  · cases framSlotValid dual.slot1 <;> simp [hv0]
    split <;> exact ⟨_, rfl⟩
  · cases framSlotValid dual.slot0 <;> simp [hv1]
    split <;> exact ⟨_, rfl⟩

theorem fram_power_cut_any_bit_monotone_safe
    (dual : DualSlotFram) (activeRec nextRec : FramSlotRecord) (cutBit : Nat)
    (hWf : WellFormedDualFram dual) (hAct : recoverDualFram dual = some activeRec)
    (hMono : activeRec.leafIdx.toNat ≤ nextRec.leafIdx.toNat) :
    ∃ recAfter,
      recoverDualFram (writeStandbyWithPowerCut dual (encodeFramSlot nextRec) cutBit) = some recAfter ∧
      (recAfter.leafIdx = activeRec.leafIdx ∨ recAfter.leafIdx = nextRec.leafIdx) ∧
      activeRec.leafIdx.toNat ≤ recAfter.leafIdx.toNat := by
  unfold writeStandbyWithPowerCut
  rcases hWf with ⟨hv0, hlt10⟩ | ⟨hv1, hlt01⟩
  · obtain ⟨hAct0, hSel⟩ := wf_slot0_active hv0 hlt10 hAct
    have hActLeaf : (decodeFramSlot dual.slot0).leafIdx = activeRec.leafIdx := congrArg FramSlotRecord.leafIdx hAct0.symm
    rw [hSel]; simp only [ite_true]
    generalize hTorn1 : tearBits512 dual.slot1 (encodeFramSlot nextRec) cutBit = torn1
    unfold recoverDualFram; simp only
    cases framSlotValid torn1
    · simp only [hv0, Bool.and_false, Bool.false_eq_true, ite_false, ite_true]
      exact ⟨decodeFramSlot dual.slot0, rfl, Or.inl hActLeaf, by rw [hActLeaf]; exact Nat.le_refl _⟩
    · simp only [hv0, Bool.and_self, ite_true]
      by_cases hCut : cutBit ≤ 384
      · have hSub : cutBit - 384 = 0 := by omega
        have hEpEq : (decodeFramSlot torn1).epochSeq = (decodeFramSlot dual.slot1).epochSeq := by
          rw [← hTorn1]; simp only [decodeFramSlot, tearBits512, hSub, tearWord64_zero]
        have hNotDom : ¬((decodeFramSlot dual.slot0).epochSeq.toNat < (decodeFramSlot torn1).epochSeq.toNat) := by rw [hEpEq]; omega
        simp only [hNotDom, ite_false]
        exact ⟨decodeFramSlot dual.slot0, rfl, Or.inl hActLeaf, by rw [hActLeaf]; exact Nat.le_refl _⟩
      · have hLeafEq : (decodeFramSlot torn1).leafIdx = nextRec.leafIdx := by
          rw [← hTorn1]; simp only [decodeFramSlot, tearBits512, encodeFramSlot]
          exact tearWord64_of_ge64 _ _ (by omega)
        split
        · exact ⟨decodeFramSlot torn1, rfl, Or.inr hLeafEq, by rw [hLeafEq]; exact hMono⟩
        · exact ⟨decodeFramSlot dual.slot0, rfl, Or.inl hActLeaf, by rw [hActLeaf]; exact Nat.le_refl _⟩
  · obtain ⟨hAct1, hSel⟩ := wf_slot1_active hv1 hlt01 hAct
    have hActLeaf : (decodeFramSlot dual.slot1).leafIdx = activeRec.leafIdx := congrArg FramSlotRecord.leafIdx hAct1.symm
    rw [hSel]; simp only [Bool.false_eq_true, ite_false]
    generalize hTorn0 : tearBits512 dual.slot0 (encodeFramSlot nextRec) cutBit = torn0
    unfold recoverDualFram; simp only
    cases framSlotValid torn0
    · simp only [hv1, Bool.false_and, Bool.false_eq_true, ite_false, ite_true]
      exact ⟨decodeFramSlot dual.slot1, rfl, Or.inl hActLeaf, by rw [hActLeaf]; exact Nat.le_refl _⟩
    · simp only [hv1, Bool.and_self, ite_true]
      by_cases hCut : cutBit ≤ 384
      · have hSub : cutBit - 384 = 0 := by omega
        have hEpEq : (decodeFramSlot torn0).epochSeq = (decodeFramSlot dual.slot0).epochSeq := by
          rw [← hTorn0]; simp only [decodeFramSlot, tearBits512, hSub, tearWord64_zero]
        have hDom : (decodeFramSlot torn0).epochSeq.toNat < (decodeFramSlot dual.slot1).epochSeq.toNat := by rw [hEpEq]; exact hlt01
        simp only [hDom, ite_true]
        exact ⟨decodeFramSlot dual.slot1, rfl, Or.inl hActLeaf, by rw [hActLeaf]; exact Nat.le_refl _⟩
      · have hLeafEq : (decodeFramSlot torn0).leafIdx = nextRec.leafIdx := by
          rw [← hTorn0]; simp only [decodeFramSlot, tearBits512, encodeFramSlot]
          exact tearWord64_of_ge64 _ _ (by omega)
        split
        · exact ⟨decodeFramSlot dual.slot1, rfl, Or.inl hActLeaf, by rw [hActLeaf]; exact Nat.le_refl _⟩
        · exact ⟨decodeFramSlot torn0, rfl, Or.inr hLeafEq, by rw [hLeafEq]; exact hMono⟩

def bootResyncStandby (dual : DualSlotFram) : DualSlotFram :=
  if selectStandbySlot dual then { dual with slot1 := zeroBits512 } else { dual with slot0 := zeroBits512 }

theorem bootResyncStandby_preserves_recovery_and_wf {dual : DualSlotFram} {rec : FramSlotRecord}
    (hRec : recoverDualFram dual = some rec) :
    WellFormedDualFram (bootResyncStandby dual) ∧ recoverDualFram (bootResyncStandby dual) = some rec := by
  have hzValid : framSlotValid zeroBits512 = false := by decide
  have hzEpoch : (decodeFramSlot zeroBits512).epochSeq.toNat = 0 := by decide
  unfold bootResyncStandby; unfold recoverDualFram at hRec ⊢; unfold selectStandbySlot
  cases hv0 : framSlotValid dual.slot0 <;> cases hv1 : framSlotValid dual.slot1 <;>
    simp only [hv0, hv1, Bool.and_self, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_true, ite_false] at hRec ⊢
  · cases hRec
  · simp only [Option.some.injEq] at hRec
    have hPos : 0 < (decodeFramSlot dual.slot1).epochSeq.toNat := by
      unfold framSlotValid at hv1; simp only [Bool.and_eq_true, bne_iff_ne] at hv1
      exact Nat.pos_of_ne_zero fun h0 => hv1.1.1 (BitVec.eq_of_toNat_eq h0)
    exact ⟨Or.inr ⟨hv1, by simp only [hzEpoch]; exact hPos⟩, by simp [hzValid, hRec]⟩
  · simp only [Option.some.injEq] at hRec
    have hPos : 0 < (decodeFramSlot dual.slot0).epochSeq.toNat := by
      unfold framSlotValid at hv0; simp only [Bool.and_eq_true, bne_iff_ne] at hv0
      exact Nat.pos_of_ne_zero fun h0 => hv0.1.1 (BitVec.eq_of_toNat_eq h0)
    exact ⟨Or.inl ⟨hv0, by simp only [hzEpoch]; exact hPos⟩, by simp [hzValid, hRec]⟩
  · by_cases hCmp : (decodeFramSlot dual.slot0).epochSeq.toNat < (decodeFramSlot dual.slot1).epochSeq.toNat
    · simp only [hCmp, decide_true, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, Option.some.injEq] at hRec ⊢
      exact ⟨Or.inr ⟨hv1, by simp only [hzEpoch]; omega⟩, by simp [hzValid, hv1, hRec]⟩
    · simp only [hCmp, decide_false, Bool.not_false, ite_true, ite_false, Option.some.injEq] at hRec ⊢
      have hPos : 0 < (decodeFramSlot dual.slot0).epochSeq.toNat := by
        unfold framSlotValid at hv0; simp only [Bool.and_eq_true, bne_iff_ne] at hv0
        exact Nat.pos_of_ne_zero fun h0 => hv0.1.1 (BitVec.eq_of_toNat_eq h0)
      exact ⟨Or.inl ⟨hv0, by simp only [hzEpoch]; exact hPos⟩, by simp [hzValid, hv0, hRec]⟩

inductive FramPowerEvent where
  | signLeafComplete (reqLeaf : BitVec 64) (newSpend : BitVec 64) (newPolicy : PolicyDigest256)
  | interruptedWrite (reqLeaf : BitVec 64) (newSpend : BitVec 64) (newPolicy : PolicyDigest256) (cutBit : Nat)
  deriving DecidableEq, Repr

def stepFramEventWithCur (dual : DualSlotFram) (cur : FramSlotRecord) : FramPowerEvent → DualSlotFram × Option Nat
  | .signLeafComplete reqLeaf newSpend newPd =>
    if cur.leafIdx.toNat ≤ reqLeaf.toNat && reqLeaf.toNat + 1 < 2 ^ 64 && cur.epochSeq.toNat + 1 < 2 ^ 64 - 1 then
      let nextRec := mkValidFramRecord newPd (BitVec.ofNat 64 (reqLeaf.toNat + 1)) newSpend (BitVec.ofNat 64 (cur.epochSeq.toNat + 1))
      (bootResyncStandby (writeStandbyWithPowerCut dual (encodeFramSlot nextRec) 512), some reqLeaf.toNat)
    else (dual, none)
  | .interruptedWrite reqLeaf newSpend newPd cutBit =>
    if cur.leafIdx.toNat ≤ reqLeaf.toNat && reqLeaf.toNat + 1 < 2 ^ 64 && cur.epochSeq.toNat + 1 < 2 ^ 64 - 1 then
      let nextRec := mkValidFramRecord newPd (BitVec.ofNat 64 (reqLeaf.toNat + 1)) newSpend (BitVec.ofNat 64 (cur.epochSeq.toNat + 1))
      (bootResyncStandby (writeStandbyWithPowerCut dual (encodeFramSlot nextRec) cutBit), none)
    else (dual, none)
def stepFramEvent (dual : DualSlotFram) (ev : FramPowerEvent) : DualSlotFram × Option Nat :=
  match recoverDualFram dual with | none => (dual, none) | some cur => stepFramEventWithCur dual cur ev
def runFramEvents : DualSlotFram → List FramPowerEvent → List Nat × DualSlotFram
  | dual, [] => ([], dual)
  | dual, ev :: rest =>
    let (dual', rel?) := stepFramEvent dual ev
    let (tailLeaves, endDual) := runFramEvents dual' rest
    match rel? with | some ell => (ell :: tailLeaves, endDual) | none => (tailLeaves, endDual)

private theorem complete_write_advances_leaf
    (dual : DualSlotFram) (cur : FramSlotRecord) (newPd : PolicyDigest256) (reqLeaf newSpend : BitVec 64)
    (hWf : WellFormedDualFram dual) (hRec : recoverDualFram dual = some cur)
    (hEpochBound : cur.epochSeq.toNat + 1 < 2 ^ 64 - 1) :
    let nextRec := mkValidFramRecord newPd (BitVec.ofNat 64 (reqLeaf.toNat + 1)) newSpend (BitVec.ofNat 64 (cur.epochSeq.toNat + 1))
    recoverDualFram (writeStandbyWithPowerCut dual (encodeFramSlot nextRec) 512) = some nextRec := by
  intro nextRec
  let nextEpoch := BitVec.ofNat 64 (cur.epochSeq.toNat + 1)
  let nextLeaf := BitVec.ofNat 64 (reqLeaf.toNat + 1)
  have hEpochToNat : nextEpoch.toNat = cur.epochSeq.toNat + 1 := by simp only [nextEpoch, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hNz : nextEpoch ≠ 0#64 := fun hEq => by have := congrArg BitVec.toNat hEq; simp only [hEpochToNat, BitVec.toNat_ofNat, Nat.zero_mod] at this; omega
  have hNotMax : nextEpoch ≠ 0xFFFFFFFFFFFFFFFF#64 := fun hEq => by
    have := congrArg BitVec.toNat hEq; have hMax : (0xFFFFFFFFFFFFFFFF#64).toNat = 2 ^ 64 - 1 := by decide
    rw [hMax, hEpochToNat] at this; omega
  have hValidNext : framSlotValid (encodeFramSlot nextRec) = true := framSlotValid_mkValid newPd nextLeaf newSpend nextEpoch hNz hNotMax
  have hNextEp : nextRec.epochSeq.toNat = cur.epochSeq.toNat + 1 := by
    change nextEpoch.toNat = cur.epochSeq.toNat + 1; exact hEpochToNat
  unfold writeStandbyWithPowerCut
  rcases hWf with ⟨hv0, hlt10⟩ | ⟨hv1, hlt01⟩
  · obtain ⟨hCur0, hSel⟩ := wf_slot0_active hv0 hlt10 hRec
    rw [hSel]; simp only [ite_true]
    rw [tearBits512_complete dual.slot1 (encodeFramSlot nextRec) (by omega)]
    unfold recoverDualFram; simp only [hv0, hValidNext, decodeFramSlot_encodeFramSlot, Bool.and_self, ite_true]
    have hDom : (decodeFramSlot dual.slot0).epochSeq.toNat < nextRec.epochSeq.toNat := by
      rw [← hCur0, hNextEp]; omega
    simp [hDom]
  · obtain ⟨hCur1, hSel⟩ := wf_slot1_active hv1 hlt01 hRec
    rw [hSel]; simp only [Bool.false_eq_true, ite_false]
    rw [tearBits512_complete dual.slot0 (encodeFramSlot nextRec) (by omega)]
    unfold recoverDualFram; simp only [hValidNext, hv1, decodeFramSlot_encodeFramSlot, Bool.and_self, ite_true]
    have hNotDom : ¬(nextRec.epochSeq.toNat < (decodeFramSlot dual.slot1).epochSeq.toNat) := by
      rw [← hCur1, hNextEp]; omega
    simp [hNotDom]

private theorem stepFramEvent_preserves_hwm
    (dual : DualSlotFram) (cur : FramSlotRecord) (ev : FramPowerEvent)
    (hWf : WellFormedDualFram dual) (hRec : recoverDualFram dual = some cur) :
    ∃ cur', WellFormedDualFram (stepFramEvent dual ev).1 ∧ recoverDualFram (stepFramEvent dual ev).1 = some cur' ∧
      cur.leafIdx.toNat ≤ cur'.leafIdx.toNat ∧
      (∀ ell, (stepFramEvent dual ev).2 = some ell → cur.leafIdx.toNat ≤ ell ∧ ell < cur'.leafIdx.toNat) := by
  have hEq : stepFramEvent dual ev = stepFramEventWithCur dual cur ev := by unfold stepFramEvent; rw [hRec]
  rw [hEq]
  cases ev with
  | signLeafComplete reqLeaf newSpend newPd =>
    unfold stepFramEventWithCur
    by_cases hCond : (decide (cur.leafIdx.toNat ≤ reqLeaf.toNat) &&
                      decide (reqLeaf.toNat + 1 < 2 ^ 64) && decide (cur.epochSeq.toNat + 1 < 2 ^ 64 - 1)) = true
    · simp only [hCond, ite_true]; simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
      obtain ⟨⟨hGe, hLb⟩, hEb⟩ := hCond
      have h512 := complete_write_advances_leaf dual cur newPd reqLeaf newSpend hWf hRec hEb
      have ⟨hWf', hRec'⟩ := bootResyncStandby_preserves_recovery_and_wf h512
      have hNextLeafNat : (BitVec.ofNat 64 (reqLeaf.toNat + 1)).toNat = reqLeaf.toNat + 1 := by
        simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hLb
      refine ⟨_, hWf', hRec', by simp only [mkValidFramRecord, hNextLeafNat]; omega, ?_⟩
      intro ell hSome; simp only [Option.some.injEq] at hSome; subst hSome; simp only [mkValidFramRecord, hNextLeafNat]; omega
    · simp only [hCond]; exact ⟨cur, hWf, hRec, Nat.le_refl _, fun _ h => by simp at h⟩
  | interruptedWrite reqLeaf newSpend newPd cutBit =>
    unfold stepFramEventWithCur
    by_cases hCond : (decide (cur.leafIdx.toNat ≤ reqLeaf.toNat) &&
                      decide (reqLeaf.toNat + 1 < 2 ^ 64) && decide (cur.epochSeq.toNat + 1 < 2 ^ 64 - 1)) = true
    · simp only [hCond, ite_true]; simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
      obtain ⟨⟨hGe, hLb⟩, _⟩ := hCond
      have hNextLeafNat : (BitVec.ofNat 64 (reqLeaf.toNat + 1)).toNat = reqLeaf.toNat + 1 := by
        simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hLb
      let nextRec := mkValidFramRecord newPd (BitVec.ofNat 64 (reqLeaf.toNat + 1)) newSpend (BitVec.ofNat 64 (cur.epochSeq.toNat + 1))
      have hMono : cur.leafIdx.toNat ≤ nextRec.leafIdx.toNat := by simp only [nextRec, mkValidFramRecord, hNextLeafNat]; omega
      obtain ⟨recTorn, hRecTorn, _, hLeTorn⟩ := fram_power_cut_any_bit_monotone_safe dual cur nextRec cutBit hWf hRec hMono
      have ⟨hWf', hRec'⟩ := bootResyncStandby_preserves_recovery_and_wf hRecTorn
      exact ⟨recTorn, hWf', hRec', hLeTorn, fun _ h => by simp at h⟩
    · simp only [hCond]; exact ⟨cur, hWf, hRec, Nat.le_refl _, fun _ h => by simp at h⟩

private theorem runFramEvents_above_hwm
    (dual : DualSlotFram) (cur : FramSlotRecord) (events : List FramPowerEvent)
    (hWf : WellFormedDualFram dual) (hRec : recoverDualFram dual = some cur) :
    (∀ ell ∈ (runFramEvents dual events).1, cur.leafIdx.toNat ≤ ell) ∧
    (runFramEvents dual events).1.Pairwise (· < ·) ∧ WellFormedDualFram (runFramEvents dual events).2 ∧
    (∃ endRec, recoverDualFram (runFramEvents dual events).2 = some endRec) := by
  induction events generalizing dual cur with
  | nil => exact ⟨by simp [runFramEvents], List.Pairwise.nil, hWf, ⟨cur, hRec⟩⟩
  | cons ev rest ih =>
    obtain ⟨cur', hWf', hRec', hLe, hRelSpec⟩ := stepFramEvent_preserves_hwm dual cur ev hWf hRec
    obtain ⟨hTailGe, hTailPw, hEndWf, hEndRec⟩ := ih (stepFramEvent dual ev).1 cur' hWf' hRec'
    unfold runFramEvents
    cases hStep : stepFramEvent dual ev with
    | mk d1 rel? =>
      have hd1 : d1 = (stepFramEvent dual ev).1 := by rw [hStep]
      have hrel : rel? = (stepFramEvent dual ev).2 := by rw [hStep]
      rw [← hd1] at hTailGe hTailPw hEndWf hEndRec
      cases rel? with
      | none => exact ⟨fun ell hm => Nat.le_trans hLe (hTailGe ell hm), hTailPw, hEndWf, hEndRec⟩
      | some ell0 =>
        have ⟨hGe0, hLt0⟩ := hRelSpec ell0 hrel.symm
        refine ⟨fun ell hm => ?_, List.Pairwise.cons (fun x hx => Nat.lt_of_lt_of_le hLt0 (hTailGe x hx)) hTailPw, hEndWf, hEndRec⟩
        rcases List.mem_cons.mp hm with rfl | hmTail
        · exact hGe0
        · exact Nat.le_trans hLe (hTailGe ell hmTail)

theorem no_leaf_reuse_across_arbitrary_power_cuts
    (dual₀ : DualSlotFram) (events : List FramPowerEvent) (hWf₀ : WellFormedDualFram dual₀) :
    (runFramEvents dual₀ events).1.Pairwise (· < ·) ∧
    (runFramEvents dual₀ events).1.Pairwise (· ≠ ·) ∧
    (∃ endRec, recoverDualFram (runFramEvents dual₀ events).2 = some endRec) := by
  obtain ⟨cur₀, hRec₀⟩ := recoverDualFram_of_wellFormed hWf₀
  obtain ⟨_, hPwLt, _, hEndSome⟩ := runFramEvents_above_hwm dual₀ cur₀ events hWf₀ hRec₀
  exact ⟨hPwLt, hPwLt.imp (fun hlt heq => by omega), hEndSome⟩

theorem tooth_single_slot_overwrite_bricks_on_mid_write_power_cut :
    let pd : PolicyDigest256 := ⟨11#64, 22#64, 33#64, 44#64⟩
    let slotOld := encodeFramSlot (mkValidFramRecord pd 5#64 0#64 1#64)
    let slotNew := encodeFramSlot (mkValidFramRecord pd 6#64 0#64 2#64)
    framSlotValid slotOld = true ∧ framSlotValid slotNew = true ∧ framSlotValid (tearBits512 slotOld slotNew 288) = false := by decide

def brokenCommitFirstEncode (epoch leaf : BitVec 64) : Bits512 := ⟨epoch, leaf, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64⟩
def brokenCommitFirstRecover (slot0 slot1 : Bits512) : BitVec 64 := if slot0.w0.toNat < slot1.w0.toNat then slot1.w1 else slot0.w1
theorem tooth_commit_before_payload_permits_leaf_rollback :
    let activeSlot0  := brokenCommitFirstEncode 2#64 10#64
    let standbySlot1 := brokenCommitFirstEncode 1#64 3#64
    let nextSlot1    := brokenCommitFirstEncode 3#64 11#64
    let tornSlot1    := tearBits512 standbySlot1 nextSlot1 64
    brokenCommitFirstRecover activeSlot0 standbySlot1 = 10#64 ∧ brokenCommitFirstRecover activeSlot0 tornSlot1 = 3#64 := by decide

/-! ## §3. Inspectable Pocket-FPGA LUT4/FF + Switch-Matrix PIP Bitstream Readback Verifier -/
def mux2b (s x0 x1 : Bool) : Bool := if s then x1 else x0
def evalLut4 (init : BitVec 16) (i0 i1 i2 i3 : Bool) : Bool :=
  init.getLsbD (i0.toNat + 2 * i1.toNat + 4 * i2.toNat + 8 * i3.toNat)

inductive PipSource where | const (b : Bool) | padIn (pinIdx : Nat) | belOut (tileIdx : Nat) (belIdx : Nat) deriving DecidableEq, Repr, Inhabited
structure SmMux4 where (in0 in1 in2 in3 : PipSource) (cfgTile cfgBitLo : Nat) deriving DecidableEq, Repr, Inhabited
abbrev VatBitstream := Bits512
def bsBit (bs : VatBitstream) (tileIdx bitOffset : Nat) : Bool := (bits512Word bs tileIdx).getLsbD bitOffset
def smMux4Sel (m : SmMux4) (bs : VatBitstream) : Nat :=
  (if bsBit bs m.cfgTile m.cfgBitLo then 1 else 0) + (if bsBit bs m.cfgTile (m.cfgBitLo + 1) then 2 else 0)
def smMux4SelectedSrc (m : SmMux4) (bs : VatBitstream) : PipSource :=
  match smMux4Sel m bs with | 0 => m.in0 | 1 => m.in1 | 2 => m.in2 | _ => m.in3
structure BelCellSpec where (tileIdx belIdx belCfgBase : Nat) (muxI0 muxI1 muxI2 muxI3 muxEn muxSr : SmMux4) deriving DecidableEq, Repr, Inhabited
def belInitBits (c : BelCellSpec) (bs : VatBitstream) : BitVec 16 := ((bits512Word bs c.tileIdx) >>> c.belCfgBase).setWidth 16
def belIsFlop   (c : BelCellSpec) (bs : VatBitstream) : Bool := bsBit bs c.tileIdx (c.belCfgBase + 16)
def belSrVal    (c : BelCellSpec) (bs : VatBitstream) : Bool := bsBit bs c.tileIdx (c.belCfgBase + 17)
structure VatFabricGrid where
  bels : List BelCellSpec
  (signEnableMux spiMisoMux : SmMux4)
  deriving DecidableEq, Repr
structure DecodedBel where (tileIdx belIdx : Nat) (init : BitVec 16) (isFlop srVal : Bool) (srcI0 srcI1 srcI2 srcI3 srcEn srcSr : PipSource) deriving DecidableEq, Repr
structure DecodedFabric where
  bels : List DecodedBel
  (signEnableSrc spiMisoSrc : PipSource)
  deriving DecidableEq, Repr
def decodeFabricGrid (grid : VatFabricGrid) (bs : VatBitstream) : DecodedFabric :=
  { bels := grid.bels.map fun c =>
      ⟨c.tileIdx, c.belIdx, belInitBits c bs, belIsFlop c bs, belSrVal c bs,
       smMux4SelectedSrc c.muxI0 bs, smMux4SelectedSrc c.muxI1 bs, smMux4SelectedSrc c.muxI2 bs,
       smMux4SelectedSrc c.muxI3 bs, smMux4SelectedSrc c.muxEn bs, smMux4SelectedSrc c.muxSr bs⟩
    signEnableSrc := smMux4SelectedSrc grid.signEnableMux bs
    spiMisoSrc    := smMux4SelectedSrc grid.spiMisoMux bs }

structure VatFabricInputs where
  (tamperCanaryTripped physTouchAck tofWithinRadius spiKeyLoadCmd spiKeyBitIn
   spiSignReqCmd policyAndFramOk msgChallengeBit publicDiagBit : Bool)
  deriving DecidableEq, Repr, Inhabited
def fabricPinAt (inp : VatFabricInputs) : Nat → Bool
  | 0 => inp.tamperCanaryTripped | 1 => inp.physTouchAck    | 2 => inp.tofWithinRadius
  | 3 => inp.spiKeyLoadCmd       | 4 => inp.spiKeyBitIn     | 5 => inp.spiSignReqCmd
  | 6 => inp.policyAndFramOk     | 7 => inp.msgChallengeBit | 8 => inp.publicDiagBit | _ => false
structure VatFabricState where (tamperLatched keyValid secretKeyReg signArmed : Bool) deriving DecidableEq, Repr, Inhabited
def flopStateAt (st : VatFabricState) (tileIdx belIdx : Nat) : Bool :=
  match tileIdx, belIdx with | 0, 0 => st.tamperLatched | 0, 1 => st.keyValid | 1, 0 => st.secretKeyReg | 1, 1 => st.signArmed | _, _ => false
def initFlopWires (st : VatFabricState) : List ((Nat × Nat) × Bool) :=
  [((0, 0), st.tamperLatched), ((0, 1), st.keyValid), ((1, 0), st.secretKeyReg), ((1, 1), st.signArmed)]

def stepVatCoreRtl (st : VatFabricState) (inp : VatFabricInputs) : VatFabricState :=
  let tamperAny  := st.tamperLatched || inp.tamperCanaryTripped
  let presenceOk := inp.physTouchAck && inp.tofWithinRadius && !tamperAny
  { tamperLatched := tamperAny
    keyValid      := if tamperAny then false else (st.keyValid || inp.spiKeyLoadCmd)
    secretKeyReg  := if tamperAny then false else if !st.keyValid && inp.spiKeyLoadCmd then inp.spiKeyBitIn else st.secretKeyReg
    signArmed     := !tamperAny && st.keyValid && inp.spiSignReqCmd && inp.policyAndFramOk && presenceOk }
def evalVatCoreSignEnable (st : VatFabricState) (inp : VatFabricInputs) : Bool :=
  st.signArmed && st.keyValid && inp.physTouchAck && inp.tofWithinRadius && !(st.tamperLatched || inp.tamperCanaryTripped)
def evalVatCoreSpiMiso (st : VatFabricState) (inp : VatFabricInputs) : Bool :=
  let signEn := evalVatCoreSignEnable st inp
  if signEn then signEn && (st.secretKeyReg != inp.msgChallengeBit) else inp.publicDiagBit
def runVatCoreRtlTrace : VatFabricState → List VatFabricInputs → List (Bool × Bool) × VatFabricState
  | st, [] => ([], st)
  | st, inp :: rest =>
    let tail := runVatCoreRtlTrace (stepVatCoreRtl st inp) rest
    ((evalVatCoreSignEnable st inp, evalVatCoreSpiMiso st inp) :: tail.1, tail.2)

theorem full_vat_rtl_tamper_projects_to_core (st : VatRtlState) (inp : VatCycleInput)
    (hTamper : st.tamperLatched = true ∨ inp.tamperCanaryTripped = true) :
    let coreSt : VatFabricState := ⟨st.tamperLatched, st.keyValid, (st.secretKeyRegs.k0 &&& 1) == 1, st.fsm == .SignArmed⟩
    let coreIn : VatFabricInputs :=
      ⟨inp.tamperCanaryTripped, inp.physTouchAck, inp.tofWithinRadius, inp.spiCmdByte == spiOpKeyLoad,
       (inp.spiCandidateKey.k0 &&& 1) == 1, inp.spiCmdByte == spiOpTriggerSign, vatPolicyInvokeLegal st inp,
       inp.msgChallengeBit, inp.publicDiagBit⟩
    ((stepVatRtl st inp).secretKeyRegs.k0 &&& 1 == 1) = (stepVatCoreRtl coreSt coreIn).secretKeyReg ∧
    vatSignEnable st inp = evalVatCoreSignEnable coreSt coreIn ∧
    (evalVatRtlOutput st inp).spiMiso = evalVatCoreSpiMiso coreSt coreIn := by
  rcases hTamper with hL | hT
  · have hSe := vatSignEnable_false_of_missing_touch_or_tof st inp (Or.inr (Or.inr (Or.inr hL)))
    simp [stepVatRtl, stepVatCoreRtl, evalVatCoreSignEnable, evalVatCoreSpiMiso, evalVatRtlOutput, zeroSecretKey, hL, hSe]
  · have hSe := vatSignEnable_false_of_missing_touch_or_tof st inp (Or.inr (Or.inr (Or.inl hT)))
    cases st.tamperLatched <;>
      simp [stepVatRtl, stepVatCoreRtl, evalVatCoreSignEnable, evalVatCoreSpiMiso, evalVatRtlOutput, zeroSecretKey, hT, hSe]

def evalPipSource (inp : VatFabricInputs) (belVals : List ((Nat × Nat) × Bool)) : PipSource → Bool
  | .const b => b | .padIn p => fabricPinAt inp p
  | .belOut t b => match belVals.find? (fun e => e.1.1 == t && e.1.2 == b) with | some (_, v) => v | none => false

def evalDecodedBelsAux (st : VatFabricState) (inp : VatFabricInputs) :
    List DecodedBel → List ((Nat × Nat) × Bool) → List ((Nat × Nat) × Bool) × List ((Nat × Nat) × Bool)
  | [], outs => (outs, [])
  | c :: cs, outs =>
    let lutOut := evalLut4 c.init (evalPipSource inp outs c.srcI0) (evalPipSource inp outs c.srcI1)
      (evalPipSource inp outs c.srcI2) (evalPipSource inp outs c.srcI3)
    let qCur := flopStateAt st c.tileIdx c.belIdx
    let qNext := mux2b (evalPipSource inp outs c.srcEn) qCur (mux2b (evalPipSource inp outs c.srcSr) lutOut c.srVal)
    let outs' := if c.isFlop then outs else outs ++ [((c.tileIdx, c.belIdx), lutOut)]
    let (finalOuts, tailFlops) := evalDecodedBelsAux st inp cs outs'
    (finalOuts, ((c.tileIdx, c.belIdx), qNext) :: tailFlops)

def lookupNextFlop (flops : List ((Nat × Nat) × Bool)) (t b : Nat) : Bool :=
  match flops.find? (fun e => e.1.1 == t && e.1.2 == b) with | some (_, v) => v | none => false
def evalDecodedCycle (dec : DecodedFabric) (st : VatFabricState) (inp : VatFabricInputs) : Bool × Bool × VatFabricState :=
  let (outs, nextFlops) := evalDecodedBelsAux st inp dec.bels (initFlopWires st)
  (evalPipSource inp outs dec.signEnableSrc, evalPipSource inp outs dec.spiMisoSrc,
   ⟨lookupNextFlop nextFlops 0 0, lookupNextFlop nextFlops 0 1, lookupNextFlop nextFlops 1 0, lookupNextFlop nextFlops 1 1⟩)
def evalFabricCycle (grid : VatFabricGrid) (bs : VatBitstream) (st : VatFabricState) (inp : VatFabricInputs) :=
  evalDecodedCycle (decodeFabricGrid grid bs) st inp
def evalFabricSignEnable (grid : VatFabricGrid) (bs : VatBitstream) (st : VatFabricState) (inp : VatFabricInputs) : Bool := (evalFabricCycle grid bs st inp).1
def evalFabricSpiMiso (grid : VatFabricGrid) (bs : VatBitstream) (st : VatFabricState) (inp : VatFabricInputs) : Bool := (evalFabricCycle grid bs st inp).2.1
def stepFabricState (grid : VatFabricGrid) (bs : VatBitstream) (st : VatFabricState) (inp : VatFabricInputs) : VatFabricState := (evalFabricCycle grid bs st inp).2.2
def runFabricTrace (grid : VatFabricGrid) (bs : VatBitstream) : VatFabricState → List VatFabricInputs → List (Bool × Bool) × VatFabricState
  | st, [] => ([], st)
  | st, inp :: rest =>
    let (se, miso, nextSt) := evalFabricCycle grid bs st inp
    let tail := runFabricTrace grid bs nextSt rest
    ((se, miso) :: tail.1, tail.2)

private def mkConstMux (tile bitLo : Nat) (b : Bool) : SmMux4 := ⟨.const b, .const false, .const false, .const false, tile, bitLo⟩
private def mux2p (a b : PipSource) (tile bitLo : Nat) : SmMux4 := ⟨a, b, .const false, .const false, tile, bitLo⟩
def vatOrderedGrid : VatFabricGrid :=
  let c00 : BelCellSpec := ⟨0, 0, 0,  mux2p (.const false) (.belOut 0 0) 0 36, mux2p (.const false) (.padIn 0) 0 38, mkConstMux 0 40 false, mkConstMux 0 42 false, mkConstMux 0 44 true, mkConstMux 0 46 false⟩
  let c20 : BelCellSpec := ⟨2, 0, 0,  mux2p (.const false) (.belOut 0 0) 2 36, mux2p (.const false) (.padIn 0) 2 38, mkConstMux 2 40 false, mkConstMux 2 42 false, mkConstMux 2 44 false, mkConstMux 2 46 false⟩
  let c21 : BelCellSpec := ⟨2, 1, 18, mux2p (.const false) (.padIn 1) 2 48, mux2p (.const false) (.padIn 2) 2 50, mux2p (.const false) (.belOut 2 0) 2 52, mkConstMux 2 54 false, mkConstMux 2 56 false, mkConstMux 2 58 false⟩
  let c01 : BelCellSpec := ⟨0, 1, 18, mux2p (.const false) (.belOut 0 1) 0 48, mux2p (.const false) (.padIn 3) 0 50, mkConstMux 0 52 false, mkConstMux 0 54 false, mkConstMux 0 56 true, mux2p (.const false) (.belOut 2 0) 0 58⟩
  let c10 : BelCellSpec := ⟨1, 0, 0,  mux2p (.const false) (.belOut 1 0) 1 36, mux2p (.const false) (.belOut 0 1) 1 38, mux2p (.const false) (.padIn 3) 1 40, mux2p (.const false) (.padIn 4) 1 42, mkConstMux 1 44 true, mux2p (.const false) (.belOut 2 0) 1 46⟩
  let c11 : BelCellSpec := ⟨1, 1, 18, mux2p (.const false) (.belOut 0 1) 1 48, mux2p (.const false) (.padIn 5) 1 50, mux2p (.const false) (.padIn 6) 1 52, mux2p (.const false) (.belOut 2 1) 1 54, mkConstMux 1 56 true, mux2p (.const false) (.belOut 2 0) 1 58⟩
  let c30 : BelCellSpec := ⟨3, 0, 0,  ⟨.const false, .padIn 8, .belOut 1 0, .const false, 3, 36⟩, mkConstMux 3 38 false, mkConstMux 3 40 false, mkConstMux 3 42 false, mkConstMux 3 44 false, mkConstMux 3 46 false⟩
  let c60 : BelCellSpec := ⟨6, 0, 0,  mux2p (.const false) (.belOut 1 1) 6 36, mux2p (.const false) (.belOut 0 1) 6 38, mux2p (.const false) (.belOut 2 1) 6 40, mkConstMux 6 42 false, mkConstMux 6 44 false, mkConstMux 6 46 false⟩
  let c61 : BelCellSpec := ⟨6, 1, 18, mux2p (.const false) (.belOut 6 0) 6 48, mux2p (.const false) (.belOut 1 0) 6 50, mux2p (.const false) (.padIn 7) 6 52, mkConstMux 6 54 false, mkConstMux 6 56 false, mkConstMux 6 58 false⟩
  let c70 : BelCellSpec := ⟨7, 0, 0,  mux2p (.const false) (.belOut 6 0) 7 36, mux2p (.const false) (.belOut 6 1) 7 38, ⟨.const false, .padIn 8, .belOut 3 0, .const false, 7, 40⟩, mkConstMux 7 42 false, mkConstMux 7 44 false, mkConstMux 7 46 false⟩
  { bels := [c00, c20, c21, c01, c10, c11, c30, c60, c61, c70]
    signEnableMux := mux2p (.const false) (.belOut 6 0) 7 48
    spiMisoMux := ⟨.const false, .belOut 7 0, .belOut 3 0, .const false, 7, 50⟩ }

def packTileCfgWord (laInit : BitVec 16) (laFlop laSr : Bool) (lbInit : BitVec 16) (lbFlop lbSr : Bool) (smMask : BitVec 28) : BitVec 64 :=
  (laInit.setWidth 64) ||| ((if laFlop then 1#64 else 0#64) <<< 16) ||| ((if laSr then 1#64 else 0#64) <<< 17) |||
  ((lbInit.setWidth 64) <<< 18) ||| ((if lbFlop then 1#64 else 0#64) <<< 34) ||| ((if lbSr then 1#64 else 0#64) <<< 35) |||
  ((smMask.setWidth 64) <<< 36)

def vatGoldenBitstream : VatBitstream :=
  { w0 := packTileCfgWord 0xEEEE#16 true  false 0xEEEE#16 true  false 0x0405005#28
    w1 := packTileCfgWord 0xBA8A#16 true  false 0x8000#16 true  false 0x0455455#28
    w2 := packTileCfgWord 0xEEEE#16 false false 0x0808#16 false false 0x0015005#28
    w3 := 0#64, w4 := 0#64, w5 := 0#64
    w6 := packTileCfgWord 0x8080#16 false false 0x2828#16 false false 0x0015015#28
    w7 := packTileCfgWord 0xD8D8#16 false false 0x0000#16 false false 0x0005015#28 }

private def goldenDecodedFabric : DecodedFabric :=
  { bels :=
      [ ⟨0, 0, 0xEEEE#16, true,  false, .belOut 0 0, .padIn 0,    .const false, .const false, .const true,  .const false⟩
      , ⟨2, 0, 0xEEEE#16, false, false, .belOut 0 0, .padIn 0,    .const false, .const false, .const false, .const false⟩
      , ⟨2, 1, 0x0808#16, false, false, .padIn 1,    .padIn 2,    .belOut 2 0,  .const false, .const false, .const false⟩
      , ⟨0, 1, 0xEEEE#16, true,  false, .belOut 0 1, .padIn 3,    .const false, .const false, .const true,  .belOut 2 0⟩
      , ⟨1, 0, 0xBA8A#16, true,  false, .belOut 1 0, .belOut 0 1, .padIn 3,     .padIn 4,     .const true,  .belOut 2 0⟩
      , ⟨1, 1, 0x8000#16, true,  false, .belOut 0 1, .padIn 5,    .padIn 6,     .belOut 2 1,  .const true,  .belOut 2 0⟩
      , ⟨3, 0, 0x0000#16, false, false, .const false,.const false,.const false, .const false, .const false, .const false⟩
      , ⟨6, 0, 0x8080#16, false, false, .belOut 1 1, .belOut 0 1, .belOut 2 1,  .const false, .const false, .const false⟩
      , ⟨6, 1, 0x2828#16, false, false, .belOut 6 0, .belOut 1 0, .padIn 7,     .const false, .const false, .const false⟩
      , ⟨7, 0, 0xD8D8#16, false, false, .belOut 6 0, .belOut 6 1, .padIn 8,     .const false, .const false, .const false⟩ ]
    signEnableSrc := .belOut 6 0, spiMisoSrc := .belOut 7 0 }

private theorem decodeFabricGrid_golden : decodeFabricGrid vatOrderedGrid vatGoldenBitstream = goldenDecodedFabric := by decide
private theorem lut_zero   (a b c d : Bool) : evalLut4 0x0000#16 a b c d = false := by cases a <;> cases b <;> cases c <;> cases d <;> decide
private theorem lut_or2    (a b c d : Bool) : evalLut4 0xEEEE#16 a b c d = (a || b) := by cases a <;> cases b <;> cases c <;> cases d <;> decide
private theorem lut_and3n2 (a b c d : Bool) : evalLut4 0x0808#16 a b c d = (a && b && !c) := by cases a <;> cases b <;> cases c <;> cases d <;> decide
private theorem lut_keyld  (a b c d : Bool) : evalLut4 0xBA8A#16 a b c d = (if !b && c then d else a) := by cases a <;> cases b <;> cases c <;> cases d <;> decide
private theorem lut_and4   (a b c d : Bool) : evalLut4 0x8000#16 a b c d = (a && b && c && d) := by cases a <;> cases b <;> cases c <;> cases d <;> decide
private theorem lut_and3   (a b c d : Bool) : evalLut4 0x8080#16 a b c d = (a && b && c) := by cases a <;> cases b <;> cases c <;> cases d <;> decide
private theorem lut_gsig   (a b c d : Bool) : evalLut4 0x2828#16 a b c d = (a && (b != c)) := by cases a <;> cases b <;> cases c <;> cases d <;> decide
private theorem lut_miso   (a b c d : Bool) : evalLut4 0xD8D8#16 a b c d = (if a then b else c) := by cases a <;> cases b <;> cases c <;> cases d <;> decide

structure VatReadbackCert where
  expectedBitstream : VatBitstream
  secretBel : Nat × Nat
  deriving DecidableEq, Repr
def vatGoldenCert : VatReadbackCert := ⟨vatGoldenBitstream, (1, 0)⟩
def muxReadsSecret (secretBel : Nat × Nat) (m : SmMux4) (bs : VatBitstream) : Bool := smMux4SelectedSrc m bs == .belOut secretBel.1 secretBel.2
def checkNoUnauthorizedSecretPips (grid : VatFabricGrid) (secretBel : Nat × Nat) (bs : VatBitstream) : Bool :=
  (grid.bels.all fun c =>
    (!muxReadsSecret secretBel c.muxI0 bs || (c.tileIdx == 1 && c.belIdx == 0)) &&
    (!muxReadsSecret secretBel c.muxI1 bs || (c.tileIdx == 6 && c.belIdx == 1)) &&
    !muxReadsSecret secretBel c.muxI2 bs && !muxReadsSecret secretBel c.muxI3 bs &&
    !muxReadsSecret secretBel c.muxEn bs && !muxReadsSecret secretBel c.muxSr bs) &&
  !muxReadsSecret secretBel grid.signEnableMux bs && !muxReadsSecret secretBel grid.spiMisoMux bs
def verifyVatFabricReadback (grid : VatFabricGrid) (cert : VatReadbackCert) (bs : VatBitstream) : Bool :=
  (grid == vatOrderedGrid) && (cert == vatGoldenCert) && (bs == cert.expectedBitstream) && checkNoUnauthorizedSecretPips grid cert.secretBel bs
theorem vatGoldenBitstream_accepted : verifyVatFabricReadback vatOrderedGrid vatGoldenCert vatGoldenBitstream = true := by decide

private theorem golden_decoded_cycle_eq (st : VatFabricState) (inp : VatFabricInputs) :
    evalDecodedCycle goldenDecodedFabric st inp =
      (evalVatCoreSignEnable st inp, evalVatCoreSpiMiso st inp, stepVatCoreRtl st inp) := by
  rcases st with ⟨s0, s1, s2, s3⟩; rcases inp with ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8⟩
  simp only [goldenDecodedFabric, evalDecodedCycle, evalDecodedBelsAux, initFlopWires,
             evalPipSource, fabricPinAt, flopStateAt, lookupNextFlop, List.find?,
             List.cons_append, List.nil_append, beq_self_eq_true, Nat.reduceBEq,
             Bool.and_self, Bool.and_false, Bool.and_true, ite_true, ite_false, Bool.false_eq_true,
             lut_zero, lut_or2, lut_and3n2, lut_keyld, lut_and4, lut_and3, lut_gsig, lut_miso, mux2b,
             evalVatCoreSignEnable, evalVatCoreSpiMiso, stepVatCoreRtl, Prod.mk.injEq, VatFabricState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases s0 <;> cases s1 <;> cases s3 <;> cases p0 <;> cases p1 <;> cases p2 <;> simp
  · cases s0 <;> cases s1 <;> cases s2 <;> cases s3 <;> cases p0 <;> cases p1 <;> cases p2 <;> cases p7 <;> cases p8 <;> simp
  · cases s0 <;> cases p0 <;> simp
  · cases s0 <;> cases s1 <;> cases p0 <;> cases p3 <;> simp
  · cases s0 <;> cases s1 <;> cases s2 <;> cases p0 <;> cases p3 <;> cases p4 <;> simp
  · cases s0 <;> cases s1 <;> cases p0 <;> cases p1 <;> cases p2 <;> cases p5 <;> cases p6 <;> simp

theorem golden_fabric_step_and_outputs_eq_rtl (st : VatFabricState) (inp : VatFabricInputs) :
    evalFabricSignEnable vatOrderedGrid vatGoldenBitstream st inp = evalVatCoreSignEnable st inp ∧
    evalFabricSpiMiso vatOrderedGrid vatGoldenBitstream st inp = evalVatCoreSpiMiso st inp ∧
    stepFabricState vatOrderedGrid vatGoldenBitstream st inp = stepVatCoreRtl st inp := by
  simp [evalFabricSignEnable, evalFabricSpiMiso, stepFabricState, evalFabricCycle, decodeFabricGrid_golden, golden_decoded_cycle_eq st inp]

private theorem golden_fabric_trace_eq_rtl (st₀ : VatFabricState) (tr : List VatFabricInputs) :
    runFabricTrace vatOrderedGrid vatGoldenBitstream st₀ tr = runVatCoreRtlTrace st₀ tr := by
  induction tr generalizing st₀ with
  | nil => rfl
  | cons inp rest ih =>
    unfold runFabricTrace runVatCoreRtlTrace
    simp only [evalFabricCycle, decodeFabricGrid_golden, golden_decoded_cycle_eq st₀ inp, ih]

theorem verifyVatFabricReadback_sound
    (grid : VatFabricGrid) (cert : VatReadbackCert) (bs : VatBitstream) (hAccept : verifyVatFabricReadback grid cert bs = true) :
    (∀ st₀ tr, runFabricTrace grid bs st₀ tr = runVatCoreRtlTrace st₀ tr) ∧
    (∀ st inp, (inp.physTouchAck = false ∨ inp.tofWithinRadius = false ∨ inp.tamperCanaryTripped = true) →
      evalFabricSignEnable grid bs st inp = false) ∧
    checkNoUnauthorizedSecretPips grid (1, 0) bs = true ∧
    (∀ st inp (k₁ k₂ : Bool),
      (inp.tamperCanaryTripped = true ∨ st.tamperLatched = true ∨ evalFabricSignEnable grid bs st inp = false) →
      evalFabricSpiMiso grid bs { st with secretKeyReg := k₁ } inp =
      evalFabricSpiMiso grid bs { st with secretKeyReg := k₂ } inp) := by
  unfold verifyVatFabricReadback at hAccept; simp only [Bool.and_eq_true, beq_iff_eq] at hAccept
  obtain ⟨⟨⟨rfl, rfl⟩, hBs⟩, hNoPip⟩ := hAccept; simp only [vatGoldenCert] at hBs hNoPip; subst hBs
  refine ⟨golden_fabric_trace_eq_rtl, ?_, hNoPip, ?_⟩
  · intro st inp hGate; rw [(golden_fabric_step_and_outputs_eq_rtl st inp).1]
    unfold evalVatCoreSignEnable; rcases hGate with h | h | h <;> simp [h]
  · intro st inp k₁ k₂ hDis
    rw [(golden_fabric_step_and_outputs_eq_rtl { st with secretKeyReg := k₁ } inp).2.1,
        (golden_fabric_step_and_outputs_eq_rtl { st with secretKeyReg := k₂ } inp).2.1]
    have hFalse : evalVatCoreSignEnable st inp = false := by
      rcases hDis with hT | hL | hSeF
      · unfold evalVatCoreSignEnable; simp [hT]
      · unfold evalVatCoreSignEnable; simp [hL]
      · rwa [(golden_fabric_step_and_outputs_eq_rtl st inp).1] at hSeF
    unfold evalVatCoreSpiMiso
    change (if evalVatCoreSignEnable st inp then _ else _) = (if evalVatCoreSignEnable st inp then _ else _)
    rw [hFalse]; simp

def trojanPipBitstream : VatBitstream :=
  { vatGoldenBitstream with
    w3 := packTileCfgWord 0xAAAA#16 false false 0x0000#16 false false 0x0000002#28
    w7 := packTileCfgWord 0xD8D8#16 false false 0x0000#16 false false 0x0009015#28 }
theorem tooth_trojan_pip_exfiltrates_key_and_is_rejected :
    let st0 : VatFabricState := ⟨false, true, false, false⟩; let st1 : VatFabricState := ⟨false, true, true, false⟩
    let diagInp : VatFabricInputs := ⟨false, false, false, false, false, false, false, false, false⟩
    evalFabricSignEnable vatOrderedGrid trojanPipBitstream st0 diagInp = false ∧
    evalFabricSignEnable vatOrderedGrid trojanPipBitstream st1 diagInp = false ∧
    evalFabricSpiMiso vatOrderedGrid trojanPipBitstream st0 diagInp = false ∧
    evalFabricSpiMiso vatOrderedGrid trojanPipBitstream st1 diagInp = true ∧
    checkNoUnauthorizedSecretPips vatOrderedGrid (1, 0) trojanPipBitstream = false ∧
    verifyVatFabricReadback vatOrderedGrid vatGoldenCert trojanPipBitstream = false := by decide

def trojanLutBitstream : VatBitstream :=
  { vatGoldenBitstream with
    w6 := packTileCfgWord 0x8080#16 false false 0xCCCC#16 false false 0x0015015#28
    w7 := packTileCfgWord 0xCCCC#16 false false 0x0000#16 false false 0x0005015#28 }
theorem tooth_trojan_lut_init_leaks_key_and_is_rejected :
    let st0 : VatFabricState := ⟨false, true, false, false⟩; let st1 : VatFabricState := ⟨false, true, true, false⟩
    let diagInp : VatFabricInputs := ⟨false, false, false, false, false, false, false, false, false⟩
    checkNoUnauthorizedSecretPips vatOrderedGrid (1, 0) trojanLutBitstream = true ∧
    evalFabricSignEnable vatOrderedGrid trojanLutBitstream st1 diagInp = false ∧
    evalFabricSpiMiso vatOrderedGrid trojanLutBitstream st0 diagInp = false ∧
    evalFabricSpiMiso vatOrderedGrid trojanLutBitstream st1 diagInp = true ∧
    verifyVatFabricReadback vatOrderedGrid vatGoldenCert trojanLutBitstream = false := by decide

/-! ## §4. Golden Vectors & Axiom Audit (`#guard_msgs` Pins) -/
def goldenPolicyDigest : PolicyDigest256 := ⟨0x0102030405060708#64, 0x1112131415161718#64, 0x2122232425262728#64, 0x3132333435363738#64⟩
/-- info: 'Minidregg.Compiler.PocketFpgaCaptpVat.captp_attenuation_monotone_non_amplifying' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms captp_attenuation_monotone_non_amplifying
/-- info: 'Minidregg.Compiler.PocketFpgaCaptpVat.compromised_host_cannot_sign_without_touch_and_tof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compromised_host_cannot_sign_without_touch_and_tof
/-- info: 'Minidregg.Compiler.PocketFpgaCaptpVat.tamper_canary_zeroizes_keys_in_one_cycle_and_locks_forever' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tamper_canary_zeroizes_keys_in_one_cycle_and_locks_forever
/-- info: 'Minidregg.Compiler.PocketFpgaCaptpVat.tooth_software_csr_touch_override_allows_forged_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_software_csr_touch_override_allows_forged_sign
/-- info: 'Minidregg.Compiler.PocketFpgaCaptpVat.bits512Bit_tearBits512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bits512Bit_tearBits512
/-- info: 'Minidregg.Compiler.PocketFpgaCaptpVat.fram_power_cut_any_bit_monotone_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fram_power_cut_any_bit_monotone_safe
/-- info: 'Minidregg.Compiler.PocketFpgaCaptpVat.no_leaf_reuse_across_arbitrary_power_cuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_leaf_reuse_across_arbitrary_power_cuts
/-- info: 'Minidregg.Compiler.PocketFpgaCaptpVat.tooth_single_slot_overwrite_bricks_on_mid_write_power_cut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_single_slot_overwrite_bricks_on_mid_write_power_cut
/-- info: 'Minidregg.Compiler.PocketFpgaCaptpVat.tooth_commit_before_payload_permits_leaf_rollback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_commit_before_payload_permits_leaf_rollback
/-- info: 'Minidregg.Compiler.PocketFpgaCaptpVat.verifyVatFabricReadback_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyVatFabricReadback_sound
/-- info: 'Minidregg.Compiler.PocketFpgaCaptpVat.tooth_trojan_pip_exfiltrates_key_and_is_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_trojan_pip_exfiltrates_key_and_is_rejected
/-- info: 'Minidregg.Compiler.PocketFpgaCaptpVat.tooth_trojan_lut_init_leaks_key_and_is_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_trojan_lut_init_leaks_key_and_is_rejected
end Minidregg.Compiler.PocketFpgaCaptpVat
