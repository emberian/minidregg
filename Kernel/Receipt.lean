/-
# `Kernel/Receipt.lean` — the receipt word Q (kernel side of OB-3)

`docs/OB3-RECEIPT-ENCODING.md` §1: a committed turn leaves one receipt Q — the committed
whole post-state under one commitment scheme, anchored at the hyperedge's apex. The
ENCODING side (Q's word as the accumulator's committed codeword, the CRS claim) is Loom's
(`Loom/ReceiptClaim.lean`, future); THIS file is the kernel side: the projection of a
`KernelState` to the observation word, and the two theorems OB-3's constraints ride on:

  * **faithfulness** — the word determines the observed state exactly (two states agree
    on the window iff their words are equal). This is what makes "the receipt binds the
    post-state" a fact about the WORD, so Loom's evaluation constraint `û(α)=μ` binds Q.
  * **the frame** — a `move` changes the word ONLY at its touched coordinates; untouched
    coordinates are untouched in the word. OB-3 constraint (2): frame-preservation is the
    SAME evaluation constraint over the untouched coordinates — no separate frame circuit.

One deliberate encoding decision, pinned here with its tooth: the keyed map is
`UKey → Option ℤ`, and a word coordinate must NOT conflate `none` with `some 0` (that
would be a binding hole — a prover could materialize an absent nullifier as a zero one).
Keyed observations are therefore presence-bit pairs: `none ↦ (0,0)`, `some v ↦ (1,v)`,
with injectivity PROVED (`obsKey_injective`), not assumed.
-/
import Kernel.State

namespace Minidregg.Kernel

/-- A finite observation window: which balance cells and which keyed-map addresses the
receipt observes. v0 keeps Q windowed (OB-3 §2's honest degrade: encode the touched
coordinates + a frame digest for the rest; the WHOLE-state word is the `window = ⊤` case
once the address universe is finitized). -/
structure Window where
  cells : Finset (CellId × AssetId)
  keys  : Finset UKey

/-- The presence-bit observation of one keyed-map entry. `none ↦ (0,0)`, `some v ↦ (1,v)`:
the first coordinate is the presence bit, so `some 0` and `none` stay distinct. -/
def obsKey : Option ℤ → ℤ × ℤ
  | none => (0, 0)
  | some v => (1, v)

/-- **The presence bit does its job** — `obsKey` is injective, so a word coordinate
determines the map entry exactly. In particular `some 0 ≠ none` in the word: the
would-be binding hole, closed by construction and proved rather than hoped. -/
theorem obsKey_injective : Function.Injective obsKey := by
  intro a b h
  cases a <;> cases b <;> simp_all [obsKey]

/-- The receipt word: the state's observations over the window. Balance coordinates read
`bal`; key coordinates read the presence-bit pair. (The flattening of `ℤ × ℤ` into two
field coordinates is Loom's encoding concern; the kernel word keeps the pair.) -/
def uproj (w : Window) (k : KernelState) :
    (w.cells → ℤ) × (w.keys → ℤ × ℤ) :=
  (fun c => k.bal c.1.1 c.1.2, fun u => obsKey (k.umap u.1))

/-- **Faithfulness, the binding half of Q**: two states have equal words over `w` iff they
agree on every observed coordinate. The `mpr` direction is definitional; the `mp`
direction is what makes the receipt BIND — a word equality forces balance-and-map
agreement on the window (via `obsKey_injective` on the key half). -/
theorem uproj_faithful (w : Window) (k k' : KernelState) :
    uproj w k = uproj w k' ↔
      (∀ c ∈ w.cells, k.bal c.1 c.2 = k'.bal c.1 c.2)
      ∧ (∀ u ∈ w.keys, k.umap u = k'.umap u) := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    constructor
    · intro c hc
      exact congrFun h1 ⟨c, hc⟩
    · intro u hu
      exact obsKey_injective (congrFun h2 ⟨u, hu⟩)
  · intro ⟨h1, h2⟩
    unfold uproj
    refine Prod.ext ?_ ?_
    · funext c; exact h1 c.1 c.2
    · funext u; exact congrArg obsKey (h2 u.1 u.2)

/-- **The frame, as a receipt fact** (OB-3 constraint (2)'s substrate): a `move` of asset
`a` between `src` and `dst` leaves every window coordinate that is NOT one of the two
touched balance coordinates unchanged in the word — including EVERY keyed coordinate
(a move never touches the map). Untouched cells are untouched in Q; the frame is an
equality of word coordinates, not a separate circuit. -/
theorem uproj_move_frame (w : Window) (k : KernelState)
    (src dst : CellId) (a : AssetId) (δ : ℤ) :
    (∀ c : {x // x ∈ w.cells}, c.1 ≠ (src, a) → c.1 ≠ (dst, a) →
      (uproj w (move k src dst a δ)).1 c = (uproj w k).1 c)
    ∧ (uproj w (move k src dst a δ)).2 = (uproj w k).2 := by
  constructor
  · intro c hs hd
    rcases c with ⟨⟨cid, aid⟩, hc⟩
    simp only [uproj, move, moveBal]
    by_cases ha : aid = a
    · subst ha
      have h1 : cid ≠ src := fun h => hs (by simp [h])
      have h2 : cid ≠ dst := fun h => hd (by simp [h])
      simp [h1, h2]
    · simp [ha]
  · rfl

/-! ### Keystone witnesses — built, both poles, computing (the audit law).

Window `{(0,0),(1,0)}` balances + key `nullifier 7`; state `k₀` = cell 0 holds 5, cell 1
holds 3, nullifier 7 unspent. -/

private def w₀ : Window := ⟨{(0, 0), (1, 0)}, {UKey.nullifier 7}⟩
private def k₀ : KernelState :=
  ⟨{0, 1}, fun c a => if c = 0 ∧ a = 0 then 5 else if c = 1 ∧ a = 0 then 3 else 0,
   fun _ => [], fun _ => none⟩

/-- *Satisfiable*: the word genuinely observes — balance coordinate `(0,0)` reads `5`,
and the unspent nullifier reads presence-bit `(0,0)`. -/
example : (uproj w₀ k₀).1 ⟨(0, 0), by decide⟩ = 5 := by decide
example : (uproj w₀ k₀).2 ⟨UKey.nullifier 7, by decide⟩ = (0, 0) := by decide

/-- *Teeth (tamper)*: spending the nullifier (`some 0`!) CHANGES the word — the presence
bit catches exactly the `none`/`some 0` conflation the encoding was designed against. -/
example :
    (uproj w₀ { k₀ with umap := fun u => if u = UKey.nullifier 7 then some 0 else none }).2
      ⟨UKey.nullifier 7, by decide⟩ = (1, 0) := by decide

/-- *Teeth (binding)*: the tampered state's word differs from the honest one — Q binds. -/
example :
    uproj w₀ { k₀ with umap := fun u => if u = UKey.nullifier 7 then some 0 else none }
      ≠ uproj w₀ k₀ := by
  intro h
  have := (uproj_faithful w₀ _ _).mp h
  have h7 := this.2 (UKey.nullifier 7) (by decide)
  simp [k₀] at h7

end Minidregg.Kernel
