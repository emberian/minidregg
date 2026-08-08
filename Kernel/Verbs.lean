/-
# Kernel/Verbs.lean — `create` · `gwrite`: the remaining conservation-algebra verbs

**SUBSTRATE, SAID OUT LOUD: this file is the conservation ALGEBRA** — plain
functions on `KernelState` in exactly the mold of `move`/`mint`
(`Kernel/State.lean` §5) — NOT the gated executor. No admission predicate, no
4-leg gate, no `Verb` structure lives here; the gated verb is the executor and
it comes out of the compiler (the derived-path law).

The two verbs `Kernel.lean`'s header named as still missing (`move` already
landed in `State.lean`):

  * **`create k c`** — bring cell `c` into existence: `accounts := insert c`,
    everything else standing still. Existence ≠ value: a fresh cell is supposed
    to hold zero of every asset, so conservation carries the HONEST
    side-condition `k.bal c a = 0` (`create_conserves`) — and that condition has
    teeth: `create`-ing a cell that already carries escaped value (a `mint` into
    a non-account credited `bal` outside the Σ) pulls the value INTO the ledger
    and strictly changes the total (`create_unbacked_breaks`). The general exact
    form is `create_adds`.
  * **`gwrite k u v`** — write the ONE keyed map at address `u`:
    `umap := Function.update k.umap u v`, everything else standing still.
    `gwrite` never touches `accounts` or `bal`, so conservation is
    UNCONDITIONAL and definitional (`gwrite_conserves`). The frame mirrors
    `uproj_move_frame`'s shape: the map changes ONLY at `u`
    (`gwrite_umap_frame`), and the write is genuinely there at `u`
    (`gwrite_umap_self`).

Receipt bridge (OB-3's kernel side, `Kernel/Receipt.lean`): `create` is
INVISIBLE to the receipt word — `uproj w (create k c) = uproj w k` holds by
`rfl`, even when the window observes the created cell's balance coordinate
(`uproj` reads only `bal`/`umap` and `create` touches neither; under the honest
side-condition that coordinate reads 0 before and after). `gwrite` moves the
word at EXACTLY the written key's `obsKey` coordinate (`uproj_gwrite_self`) and
nowhere else (`uproj_gwrite_frame`).
-/
import Kernel.Receipt

namespace Minidregg.Kernel

/-! ## §1. The two verbs — plain state functions. -/

/-- **`create`** — bring cell `c` into existence: `accounts := insert c`.
Touches only the existence plane; `bal`, `caps`, `umap` stand still. Idempotent
on an existing cell (`insert` of a member is the identity). -/
def create (k : KernelState) (c : CellId) : KernelState :=
  { k with accounts := insert c k.accounts }

/-- **`gwrite`** — write the one keyed map at address `u` to `v` (`some` =
present with value, `none` = erase to absent). Touches only `umap`; `accounts`,
`bal`, `caps` stand still. -/
def gwrite (k : KernelState) (u : UKey) (v : Option ℤ) : KernelState :=
  { k with umap := Function.update k.umap u v }

/-! ## §2. `create` — conservation (with its honest side-condition) + frame. -/

/-- The exact form: creating a genuinely new cell shifts the per-asset total by
that cell's pre-existing balance — the newly counted summand. This is the whole
conservation story of `create` in one equation; the two theorems below are its
two poles. -/
theorem create_adds (k : KernelState) (c : CellId) (a : AssetId)
    (hc : c ∉ k.accounts) :
    totalAsset (create k c) a = totalAsset k a + k.bal c a := by
  simp only [totalAsset, create]
  rw [Finset.sum_insert hc, add_comm]

/-- **`create` CONSERVES** under the honest side-condition that the created
cell holds zero of the asset (`k.bal c a = 0` — existence ≠ value; a fresh cell
carries nothing). No membership hypothesis: an already-existing `c` makes the
`insert` a no-op, a genuinely new `c` contributes its zero. -/
theorem create_conserves (k : KernelState) (c : CellId) (a : AssetId)
    (hbal : k.bal c a = 0) :
    totalAsset (create k c) a = totalAsset k a := by
  simp only [totalAsset, create]
  by_cases hc : c ∈ k.accounts
  · rw [Finset.insert_eq_self.mpr hc]
  · rw [Finset.sum_insert hc, hbal, zero_add]

/-- **THE SIDE-CONDITION'S TOOTH.** Creating a cell that already carries a
NONZERO balance strictly breaks conservation — the escaped value enters the
ledger. The zero-balance hypothesis on `create_conserves` is load-bearing, not
decorative. -/
theorem create_unbacked_breaks (k : KernelState) (c : CellId) (a : AssetId)
    (hc : c ∉ k.accounts) (hbal : k.bal c a ≠ 0) :
    totalAsset (create k c) a ≠ totalAsset k a := by
  rw [create_adds k c a hc]
  intro h
  omega

/-- Frame: `create` leaves the ledger untouched (definitional). -/
theorem create_bal_frame (k : KernelState) (c : CellId) :
    (create k c).bal = k.bal := rfl

/-- Frame: `create` leaves the capability table untouched (definitional). -/
theorem create_caps_frame (k : KernelState) (c : CellId) :
    (create k c).caps = k.caps := rfl

/-- Frame: `create` leaves the keyed map untouched (definitional). -/
theorem create_umap_frame (k : KernelState) (c : CellId) :
    (create k c).umap = k.umap := rfl

/-- The touched plane, positive pole: the created cell EXISTS afterwards. -/
theorem create_mem_self (k : KernelState) (c : CellId) :
    c ∈ (create k c).accounts :=
  Finset.mem_insert_self c k.accounts

/-- The touched plane's frame: every OTHER cell's existence is unchanged —
`create` adds `c` and nothing else. -/
theorem create_accounts_frame (k : KernelState) (c c' : CellId) (h : c' ≠ c) :
    c' ∈ (create k c).accounts ↔ c' ∈ k.accounts := by
  simp [create, Finset.mem_insert, h]

/-! ## §3. `gwrite` — unconditional conservation + frame. -/

/-- **`gwrite` CONSERVES, unconditionally** — it never touches `accounts` or
`bal`, so the per-asset total is DEFINITIONALLY unchanged. No side-condition;
the cleanest conservation statement in the algebra. -/
theorem gwrite_conserves (k : KernelState) (u : UKey) (v : Option ℤ)
    (a : AssetId) :
    totalAsset (gwrite k u v) a = totalAsset k a := rfl

/-- Frame: `gwrite` leaves the existence plane untouched (definitional). -/
theorem gwrite_accounts_frame (k : KernelState) (u : UKey) (v : Option ℤ) :
    (gwrite k u v).accounts = k.accounts := rfl

/-- Frame: `gwrite` leaves the ledger untouched (definitional). -/
theorem gwrite_bal_frame (k : KernelState) (u : UKey) (v : Option ℤ) :
    (gwrite k u v).bal = k.bal := rfl

/-- Frame: `gwrite` leaves the capability table untouched (definitional). -/
theorem gwrite_caps_frame (k : KernelState) (u : UKey) (v : Option ℤ) :
    (gwrite k u v).caps = k.caps := rfl

/-- The touched plane, positive pole: the write is genuinely THERE — the map
reads back `v` at the written address. -/
theorem gwrite_umap_self (k : KernelState) (u : UKey) (v : Option ℤ) :
    (gwrite k u v).umap u = v := by
  simp [gwrite]

/-- The touched plane's frame (the `uproj_move_frame` shape on the map): the
keyed map changes ONLY at `u` — every other address reads exactly as before. -/
theorem gwrite_umap_frame (k : KernelState) (u : UKey) (v : Option ℤ)
    (u' : UKey) (h : u' ≠ u) :
    (gwrite k u v).umap u' = k.umap u' := by
  simp [gwrite, h]

/-! ## §4. The receipt bridge — how the verbs land in Q (`Kernel/Receipt.lean`). -/

/-- **`create` is invisible to the receipt word** — definitionally: `uproj`
reads only `bal` and `umap`, and `create` touches neither. This holds even when
the window observes the created cell's balance coordinate: that coordinate reads
`k.bal c a` before and after (under `create_conserves`' honest side-condition,
0). Existence is not an observed plane of Q. -/
theorem uproj_create (w : Window) (k : KernelState) (c : CellId) :
    uproj w (create k c) = uproj w k := rfl

/-- **The write is observable in Q**: `gwrite`'s effect lands in the word at
exactly the written address's `obsKey` coordinate — presence bit and value. -/
theorem uproj_gwrite_self (w : Window) (k : KernelState) (u : UKey)
    (v : Option ℤ) (hu : u ∈ w.keys) :
    (uproj w (gwrite k u v)).2 ⟨u, hu⟩ = obsKey v := by
  simp [uproj, gwrite]

/-- **The `gwrite` frame, as a receipt fact** (mirror of `uproj_move_frame`): a
`gwrite` at `u` leaves the ENTIRE balance half of the word unchanged
(definitional — a map write never touches `bal`), and every keyed coordinate
other than `u` unchanged. OB-3 constraint (2) again: the frame is an equality of
word coordinates, not a separate circuit. -/
theorem uproj_gwrite_frame (w : Window) (k : KernelState) (u : UKey)
    (v : Option ℤ) :
    (uproj w (gwrite k u v)).1 = (uproj w k).1
    ∧ (∀ u' : {x // x ∈ w.keys}, u'.1 ≠ u →
        (uproj w (gwrite k u v)).2 u' = (uproj w k).2 u') := by
  refine ⟨rfl, ?_⟩
  intro u' h
  simp only [uproj, gwrite, Function.update_apply, if_neg h]

/-! ## §5. Witnesses — the poles FIRE on concrete states (sums genuinely
computed; the audit law). Reuses `State.lean`'s `k0`: accounts `{0, 1}` holding
5 and 3 of asset 0, total 8, keyed map empty. -/

/-- *Satisfiable (`create`)*: cell 2 was NOT an account before … -/
example : 2 ∉ k0.accounts := by decide

/-- … and genuinely EXISTS afterwards (teeth: the accounts plane changed) … -/
example : 2 ∈ (create k0 2).accounts := by decide

/-- … holding ZERO balance — existence ≠ value; the fresh cell inhabits
`create_conserves`' honest side-condition. -/
example : (create k0 2).bal 2 0 = 0 := by decide

/-- Conservation FIRES with the Σ genuinely folded over the grown account set
`{2, 0, 1}`: 0 + 5 + 3 = 8, same total as before. -/
example : totalAsset (create k0 2) 0 = 8 := by
  simp only [totalAsset, create, k0]
  rw [Finset.sum_insert (by decide),
    Finset.sum_pair (show (0 : CellId) ≠ 1 by decide)]
  decide

example : totalAsset (create k0 2) 0 = totalAsset k0 0 :=
  create_conserves k0 2 0 (by decide)

/-- Frame (`create`), an actually-untouched coordinate: cell 0's balance reads
5 before and after — the ledger plane genuinely stood still. -/
example : (create k0 2).bal 0 0 = k0.bal 0 0 := by decide

/-- *The side-condition's tooth, staged*: `kEsc` mints 4 of asset 0 into cell 2
while 2 is NOT an account — the value escapes the Σ (the ledger still totals 8
below), sitting outside the existence plane. -/
private def kEsc : KernelState := mint k0 2 0 4

/-- The escaped value is really on the `bal` column … -/
example : kEsc.bal 2 0 = 4 := by decide

/-- … and really invisible to the total (2 ∉ accounts, so the Σ skips it). -/
example : totalAsset kEsc 0 = 8 := by
  simp only [totalAsset, kEsc, mint, mintBal, k0]
  rw [Finset.sum_pair (show (0 : CellId) ≠ 1 by decide)]
  decide

/-- *The tooth FIRES*: `create`-ing the value-carrying cell pulls the escaped 4
INTO the ledger — total 8 → 12, computed. -/
example : totalAsset (create kEsc 2) 0 = 12 := by
  simp only [totalAsset, create, kEsc, mint, mintBal, k0]
  rw [Finset.sum_insert (by decide),
    Finset.sum_pair (show (0 : CellId) ≠ 1 by decide)]
  decide

example : totalAsset (create kEsc 2) 0 ≠ totalAsset kEsc 0 :=
  create_unbacked_breaks kEsc 2 0 (by decide) (by decide)

/-- *Satisfiable (`gwrite`)*: spending nullifier 7 — the write lands as
`some 0` (present-with-value-0, exactly the entry the presence bit keeps
distinct from absent). -/
example : (gwrite k0 (UKey.nullifier 7) (some 0)).umap (UKey.nullifier 7)
    = some 0 := by decide

/-- *Teeth*: the map genuinely CHANGED at the written address (`none` before,
`some 0` after — the write is observable). -/
example : (gwrite k0 (UKey.nullifier 7) (some 0)).umap (UKey.nullifier 7)
    ≠ k0.umap (UKey.nullifier 7) := by decide

/-- Frame (`gwrite`), the touched plane: a DIFFERENT address reads exactly as
before (the write hit `u` and nothing else). -/
example : (gwrite k0 (UKey.nullifier 7) (some 0)).umap (UKey.nullifier 8)
    = k0.umap (UKey.nullifier 8) := by decide

/-- Frame (`gwrite`), an untouched plane: cell 0's balance still reads 5 — the
ledger genuinely stood still under the map write. -/
example : (gwrite k0 (UKey.nullifier 7) (some 0)).bal 0 0 = k0.bal 0 0 := by
  decide

/-- Conservation FIRES for `gwrite` — definitionally (the total never saw the
write). -/
example : totalAsset (gwrite k0 (UKey.nullifier 7) (some 0)) 0
    = totalAsset k0 0 := rfl

/-! ### Receipt-bridge witnesses — window `wV` observes the created cell's own
balance coordinate `(2, 0)` AND the nullifier-7 key: the adversarial window for
both bridge claims. -/

private def wV : Window := ⟨{(2, 0)}, {UKey.nullifier 7}⟩

/-- `create` is word-invisible EVEN under a window watching the new cell's
balance coordinate — Q reads the same word before and after. -/
example : uproj wV (create k0 2) = uproj wV k0 := rfl

/-- The spend shows up in Q with the presence bit set — `(1, 0)`, distinct from
absent `(0, 0)`: the `none`/`some 0` non-conflation doing its job on a write. -/
example : (uproj wV (gwrite k0 (UKey.nullifier 7) (some 0))).2
    ⟨UKey.nullifier 7, by decide⟩ = (1, 0) := by decide

/-- And the whole word genuinely CHANGES — the receipt binds the write. -/
example : uproj wV (gwrite k0 (UKey.nullifier 7) (some 0)) ≠ uproj wV k0 := by
  intro h
  have h7 := ((uproj_faithful wV _ _).mp h).2 (UKey.nullifier 7) (by decide)
  simp [gwrite, k0] at h7

/-! ## §6. Axiom pins (exact-output, self-verifying — `State.lean` §8's
discipline). Kernel-clean throughout: every footprint is
`⊆ {propext, Classical.choice, Quot.sound}`. Even the `rfl` theorems report
`[propext, Quot.sound]` — `#print axioms` follows the CONSTANTS in the term,
and `totalAsset`/`uproj` ride the `Quot`-quotiented `Finset`; the pin is the
honest transitive footprint, not a claim of axiom-free proofs. -/

/-- info: 'Minidregg.Kernel.create_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms create_conserves

/-- info: 'Minidregg.Kernel.create_unbacked_breaks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms create_unbacked_breaks

/-- info: 'Minidregg.Kernel.gwrite_conserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms gwrite_conserves

/-- info: 'Minidregg.Kernel.gwrite_umap_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms gwrite_umap_frame

/-- info: 'Minidregg.Kernel.uproj_create' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms uproj_create

/-- info: 'Minidregg.Kernel.uproj_gwrite_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms uproj_gwrite_frame

end Minidregg.Kernel
