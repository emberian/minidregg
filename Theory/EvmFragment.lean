/-
# `Theory/EvmFragment.lean` — the Stage-0 EVM fragment semantics, stated directly

The EVM-decompilation Stage 0 (`zkml-research/notes/evm-decompilation.md` §9,
build log `notes/evm-stage0.md`): the five-opcode-kind fragment
{PUSH1, CALLDATALOAD, ADD, MSTORE, RETURN}, as a byte-level interpreter — real
bytecode, byte-granular PC, a real stack with the 1024-depth check, byte-addressed
memory, CALLDATALOAD's zero-padding past the calldata end, and the implicit STOP
of zero-extended code. The machine is deliberately PRESENT here: the decompilation
theorem (`Theory/EvmResidual.lean`) is only visible if the stack, PC and decode
exist in the semantics and then die in the residual.

## The anchor decision (design note §6, taken here)

This is a DIRECT statement of the fragment semantics, not an import of
EVMYulLean. The fragment is five opcode kinds and ~100 lines; importing a
whole-surface Cancun model into `Theory/` (whose import boundary is mechanically
Mathlib-only) buys nothing at this stage. The fidelity register is therefore
**differential, not machine-checked**: the conformance theorems at the bottom
pin `evmRun` to five vectors executed by a real EVM — anvil v1.7.1 (revm),
`anvil_setCode` + `eth_call` of the actual 15-byte runtime — including a
wraparound ADD and a CALLDATALOAD read past the calldata end. EquiVM/EVMYulLean
remain the upgrade path when solc-emitted dispatch enters (Stage 3+); nothing in
the statement shape changes.

## Honest premises

* **Gas-free** (design note §7.5): `evmRun` has no gas. Every downstream theorem
  speaks about executions the deployed EVM completes within gas; an OOG execution
  is one this semantics neither accepts nor claims.
* Words are `ℕ` kept below `2^256` by construction (every producer is a `% 2^256`
  or a 32-byte read); bytes are `ℕ` below `256` by construction (every producer
  is a `% 256` or calldata, whose vectors are byte lists). The codec is the ONE
  little-endian algebra of `Theory.Bignum`, big-endianized by `List.reverse` —
  no second pack/unpack.
* `deriving DecidableEq` on the result type is what lets every conformance vector
  be a kernel-`decide`d NAMED theorem, not a `#guard`.
-/
import Mathlib.Tactic
import Mathlib.Data.List.GetD
import Theory.Bignum

namespace Minidregg.Theory.EvmFragment

-- `Bignum.…` resolves through the enclosing `Minidregg.Theory` namespace.

set_option autoImplicit false

/-! ## §1. Words and the byte codec — `Theory.Bignum`'s algebra, big-endianized. -/

/-- The EVM word modulus. Wraparound at this modulus IS the ADD semantics. -/
def wordMod : ℕ := 2 ^ 256

/-- The 32 big-endian bytes of a word: `Bignum.digitsLE` (the one little-endian
codec), reversed. Every byte is `< 256` (`digitsLE_ranged`). -/
def beBytes (v : ℕ) : List ℕ := (Bignum.digitsLE 256 32 v).reverse

/-- CALLDATALOAD's read: 32 bytes at `off`, ZERO-PADDED past the calldata end
(`List.getD … 0` — this is the deployed EVM's semantics, and conformance vector
V4 below exercises it against a real EVM), assembled big-endian. -/
def cdWord (cd : List ℕ) (off : ℕ) : ℕ :=
  Bignum.denoteNat 256 (((List.range 32).map fun k => cd.getD (off + k) 0).reverse)

/-- Byte-addressed memory: total, zero-initialized — the EVM's memory model
(expansion cost is gas, which this semantics does not carry). -/
def Mem : Type := ℕ → ℕ

/-- MSTORE's write: the 32 big-endian bytes of `v` at `[off, off+32)`. -/
def mstore32 (m : Mem) (off v : ℕ) : Mem := fun a =>
  if off ≤ a ∧ a < off + 32 then (beBytes v).getD (a - off) 0 else m a

/-! ## §2. The machine. -/

/-- Machine state: byte-granular `pc`, the stack (head = top), memory. -/
structure MState where
  pc : ℕ
  stack : List ℕ
  mem : Mem

/-- One step's outcome. `fail` is a REFUSAL (stack underflow/overflow, an opcode
outside the fragment) — never a default, never a repair. -/
inductive StepResult
  | cont (s : MState)
  | done (ret : List ℕ)
  | fail (msg : String)

/-- An execution's outcome. -/
inductive ExecResult
  | ok (ret : List ℕ)
  | fail (msg : String)
  deriving DecidableEq, Repr

/-- **One step of the fragment machine.** Fetch is `code.getD pc 0` — code is
zero-extended, so running off the end is the implicit STOP, exactly the deployed
EVM's convention. Stack pops are by pattern; operand order is the EVM's
(top first: ADD pops `a` then `b`; MSTORE pops `off` then `v`; RETURN pops `off`
then `len`). -/
def step (code cd : List ℕ) (s : MState) : StepResult :=
  match code.getD s.pc 0 with
  | 0x00 =>       -- STOP (explicit, or the zero-extension past the code end)
      .done []
  | 0x01 =>       -- ADD: (a + b) mod 2^256 — wraparound IS the semantics
      match s.stack with
      | a :: b :: rest => .cont ⟨s.pc + 1, ((a + b) % wordMod) :: rest, s.mem⟩
      | _ => .fail "ADD: stack underflow"
  | 0x35 =>       -- CALLDATALOAD
      match s.stack with
      | off :: rest => .cont ⟨s.pc + 1, cdWord cd off :: rest, s.mem⟩
      | _ => .fail "CALLDATALOAD: stack underflow"
  | 0x52 =>       -- MSTORE
      match s.stack with
      | off :: v :: rest => .cont ⟨s.pc + 1, rest, mstore32 s.mem off v⟩
      | _ => .fail "MSTORE: stack underflow"
  | 0x60 =>       -- PUSH1 (immediate zero-extended past the code end, like fetch)
      if 1024 ≤ s.stack.length then .fail "PUSH1: stack overflow"
      else .cont ⟨s.pc + 2, code.getD (s.pc + 1) 0 :: s.stack, s.mem⟩
  | 0xf3 =>       -- RETURN
      match s.stack with
      | off :: len :: _ => .done ((List.range len).map fun k => s.mem (off + k))
      | _ => .fail "RETURN: stack underflow"
  | _ => .fail "opcode outside the Stage-0 fragment"

/-- The fueled driver. Fuel exhaustion is a refusal, not a semantics. -/
def exec (code cd : List ℕ) : ℕ → MState → ExecResult
  | 0, _ => .fail "out of fuel"
  | fuel + 1, s =>
      match step code cd s with
      | .cont s' => exec code cd fuel s'
      | .done r => .ok r
      | .fail m => .fail m

/-- **The fragment semantics**: run `code` on `cd` from the empty machine. -/
def evmRun (fuel : ℕ) (code cd : List ℕ) : ExecResult :=
  exec code cd fuel ⟨0, [], fun _ => 0⟩

/-! ## §3. The Stage-0 fragment program. -/

/-- The 15-byte runtime — built programmatically, deployed to anvil verbatim:
`0x6000356020350160005260206000f3`, i.e.
`PUSH1 0 · CALLDATALOAD · PUSH1 32 · CALLDATALOAD · ADD · PUSH1 0 · MSTORE ·
PUSH1 32 · PUSH1 0 · RETURN`. The design note's "five opcodes" are the five
KINDS; the three PUSH1-fed operands make the program 15 bytes (build-log D2). -/
def fragmentCode : List ℕ :=
  [0x60, 0x00, 0x35, 0x60, 0x20, 0x35, 0x01, 0x60, 0x00, 0x52,
   0x60, 0x20, 0x60, 0x00, 0xf3]

/-- Fuel committed for every fragment statement (the run takes 10 steps). -/
def fragmentFuel : ℕ := 16

/-- The 64-byte two-word calldata of the fragment's intended ABI. -/
def calldataOf (X Y : ℕ) : List ℕ := beBytes X ++ beBytes Y

/-! ## §4. Conformance — the differential anchor, vectors from a REAL EVM.

Executed 2026-08-17 against anvil v1.7.1 (revm): `anvil_setCode` of
`fragmentCode`, then `eth_call`. Raw transcript: zkml-research scratchpad
`evm-stage0/vectors.json`; the committed form is these kernel-decided theorems.
Each is a NAMED theorem, not a `#guard` — a fact worth asserting is worth
naming. -/

/-- V1, small values: `1 + 2 = 3`. -/
theorem conformance_v1 :
    evmRun fragmentFuel fragmentCode (calldataOf 1 2) = .ok (beBytes 3) := by
  decide

/-- V2, arbitrary 256-bit operands (π-digit words), anvil's returndata verbatim. -/
theorem conformance_v2 :
    evmRun fragmentFuel fragmentCode
      (calldataOf 0x243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89
                  0x452821e638d01377be5466cf34e90c6cc0ac29b7c97c50dd3f84d5b5b5470917)
      = .ok (beBytes 0x69678c6ebe731c4ad16df0fd38597fb164b561d9f31b82ad47b3d04ea19575a0) := by
  decide

/-- V3, **wraparound**: `(2^256 − 1) + 5 = 4 (mod 2^256)`. A `< p`-scoped circuit
could not even state this vector; the 16×16-limb geometry of
`Compiler/EvmAddAir.lean` proves it. -/
theorem conformance_v3_wrap :
    evmRun fragmentFuel fragmentCode (calldataOf (2 ^ 256 - 1) 5)
      = .ok (beBytes 4) := by
  decide

/-- V4, **CALLDATALOAD past the calldata end**: 40 bytes of calldata, so the
second word is 8 real bytes zero-padded to 32 — and the sum ripples a carry into
the top byte (`0xfe + 0x11 = 0x10f`). anvil's returndata verbatim. -/
theorem conformance_v4_short_calldata :
    evmRun fragmentFuel fragmentCode
      (beBytes 0xfedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210
        ++ [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88])
      = .ok (beBytes 0x0ffeeddccbbaa998fedcba9876543210fedcba9876543210fedcba9876543210) := by
  decide

/-- V5, empty calldata: both loads read pure padding; `0 + 0 = 0`. -/
theorem conformance_v5_empty :
    evmRun fragmentFuel fragmentCode [] = .ok (beBytes 0) := by
  decide

/-! ## §5. The codec facts the meaning theorem consumes.

All three reduce to `Theory.Bignum`'s codec theorems through `List.reverse`; the
only new content is the `getD`-slicing of an appended calldata. -/

/-- `256^32 = 2^256` — the byte codec's capacity is exactly the word modulus. -/
theorem byte_capacity : (256 : ℕ) ^ 32 = wordMod := by norm_num [wordMod]

@[simp] theorem beBytes_length (v : ℕ) : (beBytes v).length = 32 := by
  simp [beBytes]

/-- Reading a list back out of its own `getD` graph. -/
theorem range_map_getD {α : Type} (d : α) :
    ∀ l : List α, (List.range l.length).map (fun k => l.getD k d) = l := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons,
        List.map_map]
      exact congrArg (x :: ·) (by simpa [Function.comp] using ih)

/-- The byte encoding recomposes: `beBytes` is injective below the word modulus —
the boundary encoding loses nothing, as a THEOREM, not an assumption. -/
theorem beBytes_inj {X Z : ℕ} (hX : X < wordMod) (hZ : Z < wordMod)
    (h : beBytes X = beBytes Z) : X = Z := by
  have h' : Bignum.digitsLE 256 32 X = Bignum.digitsLE 256 32 Z :=
    List.reverse_injective h
  have hcap : (256 : ℕ) ^ 32 = wordMod := byte_capacity
  calc X = Bignum.denoteNat 256 (Bignum.digitsLE 256 32 X) :=
        (Bignum.denoteNat_digitsLE (by norm_num) 32 X (hcap ▸ hX)).symm
    _ = Bignum.denoteNat 256 (Bignum.digitsLE 256 32 Z) := by rw [h']
    _ = Z := Bignum.denoteNat_digitsLE (by norm_num) 32 Z (hcap ▸ hZ)

/-- The first calldata word of the two-word ABI is `X`. -/
theorem cdWord_calldataOf_zero {X : ℕ} (Y : ℕ) (hX : X < wordMod) :
    cdWord (calldataOf X Y) 0 = X := by
  have hslice : ((List.range 32).map fun k => (calldataOf X Y).getD (0 + k) 0)
      = beBytes X := by
    have hlen : (beBytes X).length = 32 := beBytes_length X
    calc ((List.range 32).map fun k => (calldataOf X Y).getD (0 + k) 0)
        = (List.range 32).map fun k => (beBytes X).getD k 0 := by
          refine List.map_congr_left fun k hk => ?_
          have hk32 : k < 32 := List.mem_range.mp hk
          rw [Nat.zero_add]
          exact List.getD_append _ _ _ _ (by omega)
      _ = beBytes X := by rw [← hlen]; exact range_map_getD 0 (beBytes X)
  rw [cdWord, hslice, beBytes, List.reverse_reverse]
  exact Bignum.denoteNat_digitsLE (by norm_num) 32 X (byte_capacity ▸ hX)

/-- The second calldata word of the two-word ABI is `Y`. -/
theorem cdWord_calldataOf_32 (X : ℕ) {Y : ℕ} (hY : Y < wordMod) :
    cdWord (calldataOf X Y) 32 = Y := by
  have hslice : ((List.range 32).map fun k => (calldataOf X Y).getD (32 + k) 0)
      = beBytes Y := by
    have hlenX : (beBytes X).length = 32 := beBytes_length X
    calc ((List.range 32).map fun k => (calldataOf X Y).getD (32 + k) 0)
        = (List.range 32).map fun k => (beBytes Y).getD k 0 := by
          refine List.map_congr_left fun k hk => ?_
          have : (calldataOf X Y).getD (32 + k) 0
              = (beBytes Y).getD (32 + k - (beBytes X).length) 0 :=
            List.getD_append_right _ _ _ _ (by omega)
          rw [this, hlenX]
          congr 1
          omega
      _ = beBytes Y := by
          rw [← beBytes_length Y]; exact range_map_getD 0 (beBytes Y)
  rw [cdWord, hslice, beBytes, List.reverse_reverse]
  exact Bignum.denoteNat_digitsLE (by norm_num) 32 Y (byte_capacity ▸ hY)

/-! ## §6. Axiom accounting. -/

/-- info: 'Minidregg.Theory.EvmFragment.conformance_v3_wrap' depends on axioms:
[propext] -/
#guard_msgs (whitespace := lax) in #print axioms conformance_v3_wrap

/-- info: 'Minidregg.Theory.EvmFragment.beBytes_inj' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms beBytes_inj

/-- info: 'Minidregg.Theory.EvmFragment.cdWord_calldataOf_32' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cdWord_calldataOf_32

end Minidregg.Theory.EvmFragment
