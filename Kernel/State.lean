/-
# Kernel.State — the minimal kernel state (ATLAS §7 carve).

The compressed state, NOT breadstuffs' 19-field `RecordKernelState`. That record
is the debt ATLAS §5 names: an additive-extension pile ("the additive extension,
exactly as nullifiers/commitments were added" — verbatim ~10× in one structure).
`UniversalBridge.UKey` (breadstuffs `Dregg2/Exec/UniversalBridge.lean`) already
PROVED the compression — all 17 kernel fields + the receipt log project onto ONE
`(Domain, key) ↦ Option ℤ` universal address space, and the three verbs are memory
programs over it (`gwrite/move/create_is_memory_program`). Minidregg's founding
move (ATLAS §1) is the inversion: the compressed form is the ONLY form. So the
kernel state is four fields:

  * `accounts : Finset CellId` — which cells exist (the existence plane).
  * `bal : CellId → AssetId → ℤ` — the per-asset signed ledger (the value spine;
    ATLAS §3 item 8: `bal` over `Finset accounts`, issuer wells carrying −supply,
    Σ = 0 as identity).
  * `caps : CellId → List Cap` — the held-capability slot table.
  * `umap : UKey → Option ℤ` — the ONE keyed map. `UKey` is a small faithful
    transcription of breadstuffs' `UKey` DESIGN (the inductive address, not the
    19 fields): heaps / nullifiers / commitments / revoked / lifecycle all live
    as distinct constructors of one address type, `none` = absent, exactly the
    circuit's `(present, value)` encoding. New side tables are new CONSTRUCTORS,
    never new record fields — the compression is structural.

The keystone here is the ATLAS §3 item-8 conservation spine, the *concrete* `ℤ`
ledger shadow of `Camera.conservation_is_fpu` (the abstract `Auth M` law): a
`move` (debit / credit on the `bal` column) preserves each per-asset total
`totalAsset k a = Σ_{c ∈ accounts} bal c a` EXACTLY, and — the tooth — a `mint`
without a matching issuer-well debit strictly BREAKS it. Both poles are BUILT on
a concrete state (ATLAS §6 law 2: a keystone that cannot exhibit both poles does
not compile), the sum genuinely computed.

Deliberately NOT here: the executor, the 4-leg gate, the hyperedge turn shape
(the `Kernel/Turn` lane). The other two verbs' conservation ALGEBRA —
`create`/`gwrite` as plain functions with their own conservation + frame
theorems — is the sibling `Kernel/Verbs.lean`. `move`/`mint` here are plain
functions on the `bal` column — the conservation ALGEBRA, not the gated verb.
-/
import Kernel.Camera  -- the four-substance product camera this state's Σ-law shadows
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Insert

namespace Minidregg.Kernel

/-! ## §1. The scalar names. -/

/-- A **cell** identity — the unit of ownership (an account, a note, a factory,
a capability holder). `Nat` is the abstract id; the deployed realization is a
content address, injective under the CR floor. -/
abbrev CellId : Type := Nat

/-- An **asset** identity. **An asset IS its issuer cell**: the id of an asset is
the `CellId` of the cell that issues it (its well). This is what makes
"mint = move" honest — issuing supply is a `move` OUT of the issuer well (which
carries −supply), so the per-asset Σ stays 0; a `mint` with no issuer-well debit
is the tooth below. (Type-equal to `CellId` because an asset is named by a cell;
kept a distinct `abbrev` for reading intent at use sites.) -/
abbrev AssetId : Type := Nat

/-! ## §2. Capabilities — the minimal shape.

Kept a plain structure for now (ATLAS §7: the 4-leg gate / guard lattice is the
`Kernel/Turn` lane). A capability names a `target` cell and a `rights` word (a
rights bitmask — the deployed authority encoding; here an abstract `Nat`). -/

/-- A **capability**: authority over `target` carrying `rights`. Minimal on
purpose — attenuation, caveats, and the amplification algebra arrive with the
gate. -/
structure Cap where
  /-- The cell this capability authorizes action over. -/
  target : CellId
  /-- The rights word (a bitmask of authorized operations; abstract `Nat` here). -/
  rights : Nat
  deriving DecidableEq, Repr

/-! ## §3. `UKey` — the universal address (the compression, transcribed).

The DESIGN port of breadstuffs `UniversalBridge.UKey`: ONE inductive address type
whose constructors are the side-table planes. A small faithful set — enough to
exhibit that heaps, nullifiers, commitments, revocations, and lifecycle all share
one address space (they do NOT need five record fields). Each constructor is the
abstract `(collection_id, key)` content of the deployed `addr = hash[domain_tag,
collection_id, key]`; the three insert-only sets (nullifier / commitment /
revoked) share the `nullifiers` domain as DISTINCT collections. -/
inductive UKey where
  /-- `heaps c` key `k`: the per-cell openable user map. -/
  | heap (c : CellId) (k : ℤ)
  /-- `lifecycle c`: the cell lifecycle discriminant. -/
  | lifecycle (c : CellId)
  /-- `nullifiers`: the spent-note set (insert-only). -/
  | nullifier (n : Nat)
  /-- `commitments`: the note-commitment set (insert-only). -/
  | commitment (n : Nat)
  /-- `revoked`: the credential-revocation registry (insert-only). -/
  | revoked (n : Nat)
  deriving DecidableEq, Repr

/-- The universal-memory **domains** (the address-tag coarsening). The tag is part
of the address, so distinct collections never alias inside the one map. -/
inductive Domain where
  | heap
  | nullifiers
  deriving DecidableEq, Repr

/-- The domain assignment — the projection table's right column (breadstuffs
`UKey.domain`). The three insert-only sets share `nullifiers` (distinct
constructors = distinct collections in one domain). -/
def UKey.domain : UKey → Domain
  | .heap _ _ | .lifecycle _ => .heap
  | .nullifier _ | .commitment _ | .revoked _ => .nullifiers

/-! ## §4. The kernel state. -/

/-- **The minimal kernel state** (ATLAS §7): existence + ledger + caps + the one
keyed map. `umap` is the universal address space that subsumes the side tables a
19-field record would spell out — `none` = absent (the circuit's `(present,
value)` cell). -/
structure KernelState where
  /-- Which cells exist (the `accounts`/existence plane). -/
  accounts : Finset CellId
  /-- The per-asset signed ledger — the value spine (`bal c a` = holdings of asset
  `a` at cell `c`; may be negative for issuer wells). -/
  bal : CellId → AssetId → ℤ
  /-- The held-capability slot table (holder ↦ its capability slots). -/
  caps : CellId → List Cap
  /-- The ONE keyed map — the universal address space (heaps / nullifiers /
  commitments / revoked / lifecycle), `none` = absent. -/
  umap : UKey → Option ℤ

/-! ## §5. The per-asset total and the two ledger operations.

`move`/`mint` act on the `bal` COLUMN only — plain functions, not the gated
executor (that is `Kernel/Turn`). This is the conservation ALGEBRA. -/

/-- The **per-asset total** — the conserved quantity, Σ over the existing cells.
Only cells IN `accounts` are counted: this is why a credit to a non-account cell
(a `mint`) escapes the ledger and breaks conservation. -/
def totalAsset (k : KernelState) (a : AssetId) : ℤ :=
  ∑ c ∈ k.accounts, k.bal c a

/-- The `bal`-column update of a **move**: debit `src`, credit `dst`, of asset `a`
by `δ`, leaving every other asset column untouched. A self-move (`src = dst`) is
a balance no-op (`−δ + δ = 0`). -/
def moveBal (bal : CellId → AssetId → ℤ) (src dst : CellId) (a : AssetId) (δ : ℤ) :
    CellId → AssetId → ℤ :=
  fun c a' =>
    if a' = a then bal c a' - (if c = src then δ else 0) + (if c = dst then δ else 0)
    else bal c a'

/-- **`move`** — the conserving ledger operation: debit `src` / credit `dst` of
asset `a` by `δ`. Touches only `bal`; `accounts`, `caps`, `umap` stand still. -/
def move (k : KernelState) (src dst : CellId) (a : AssetId) (δ : ℤ) : KernelState :=
  { k with bal := moveBal k.bal src dst a δ }

/-- The `bal`-column update of a **mint-without-issuer-well**: credit `dst` of
asset `a` by `δ` with NO matching debit — the value-conservation violation. -/
def mintBal (bal : CellId → AssetId → ℤ) (dst : CellId) (a : AssetId) (δ : ℤ) :
    CellId → AssetId → ℤ :=
  fun c a' => if a' = a then bal c a' + (if c = dst then δ else 0) else bal c a'

/-- **`mint`** (without issuer well) — credit `dst` of asset `a` by `δ`, debiting
no one. This is precisely the operation the conservation law FORBIDS; the tooth
below shows it breaks `totalAsset`. -/
def mint (k : KernelState) (dst : CellId) (a : AssetId) (δ : ℤ) : KernelState :=
  { k with bal := mintBal k.bal dst a δ }

/-! ## §6. The conservation keystone (BUILT, with both poles).

The concrete `ℤ`-ledger shadow of `Camera.conservation_is_fpu`. -/

/-- **THE CONSERVATION KEYSTONE.** A `move` between two EXISTING cells preserves
the per-asset total exactly — `totalAsset` is unchanged, `Σ_{c} bal c a` invariant.
The `accounts` membership of both endpoints is load-bearing: the debit at `src`
and the credit at `dst` are both inside the sum, so they cancel. -/
theorem move_conserves (k : KernelState) (src dst : CellId) (a : AssetId) (δ : ℤ)
    (hsrc : src ∈ k.accounts) (hdst : dst ∈ k.accounts) :
    totalAsset (move k src dst a δ) a = totalAsset k a := by
  simp only [totalAsset, move, moveBal, if_true]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', if_pos hsrc, if_pos hdst]
  omega

/-- The credit-only form of a mint: it shifts the total by exactly `+δ` (when the
credited cell exists). The equality that makes the tooth sharp. -/
theorem mint_adds (k : KernelState) (dst : CellId) (a : AssetId) (δ : ℤ)
    (hdst : dst ∈ k.accounts) :
    totalAsset (mint k dst a δ) a = totalAsset k a + δ := by
  simp only [totalAsset, mint, mintBal, if_true]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', if_pos hdst]

/-- **THE TOOTH.** A `mint` without an issuer-well debit genuinely BREAKS
conservation: for any nonzero `δ` and existing `dst`, the per-asset total
strictly changes. The law has content — it is not satisfied by every operation.
(breadstuffs `oldMint_breaks_conservation`, ATLAS §3 item 8.) -/
theorem mint_breaks_conservation (k : KernelState) (dst : CellId) (a : AssetId) (δ : ℤ)
    (hdst : dst ∈ k.accounts) (hδ : δ ≠ 0) :
    totalAsset (mint k dst a δ) a ≠ totalAsset k a := by
  rw [mint_adds k dst a δ hdst]
  intro h
  omega

/-! ## §7. Witnesses — the poles FIRE on a concrete state (sum genuinely computed).

`k0`: two accounts `{0, 1}` holding 5 and 3 of asset `0` (total 8). Everything
below is decided/computed against this literal state — non-vacuity is exercised,
not asserted. -/

/-- A concrete two-account state: cell 0 holds 5, cell 1 holds 3, of asset 0. -/
def k0 : KernelState where
  accounts := {0, 1}
  bal := fun c a => if a = 0 then (if c = 0 then 5 else if c = 1 then 3 else 0) else 0
  caps := fun _ => []
  umap := fun _ => none

/-- Satisfiability: the total is a genuine nonzero value — the Σ actually folds
`{0, 1}` (5 + 3 = 8). The conservation law below is about a non-degenerate state. -/
example : totalAsset k0 0 = 8 := by
  simp only [totalAsset, k0]
  rw [Finset.sum_pair (show (0 : CellId) ≠ 1 by decide)]
  decide

/-- The move genuinely REARRANGES the ledger: cell 0 debited 5 → 3 … -/
example : (move k0 0 1 0 2).bal 0 0 = 3 := by decide

/-- … cell 1 credited 3 → 5 (the balances actually moved) … -/
example : (move k0 0 1 0 2).bal 1 0 = 5 := by decide

/-- … yet the per-asset total is CONSERVED (the keystone fires with real content:
the ledger changed, the total did not). -/
example : totalAsset (move k0 0 1 0 2) 0 = totalAsset k0 0 :=
  move_conserves k0 0 1 0 2 (by decide) (by decide)

/-- The mint credits cell 1 by 2 with no debit: total 8 → 10 (the sum computed). -/
example : totalAsset (mint k0 1 0 2) 0 = 10 := by
  simp only [totalAsset, mint, mintBal, k0]
  rw [Finset.sum_pair (show (0 : CellId) ≠ 1 by decide)]
  decide

/-- The tooth FIRES on the concrete state: minting 2 into cell 1 strictly changes
the total (10 ≠ 8). The keystone's negative pole has teeth. -/
example : totalAsset (mint k0 1 0 2) 0 ≠ totalAsset k0 0 :=
  mint_breaks_conservation k0 1 0 2 (by decide) (by decide)

/-! ## §8. Axiom pins.

Kernel-clean is `⊆ {propext, Classical.choice, Quot.sound}` (the Σ-law rides
`Finset`/`Multiset`, which is `Quot`-quotiented — hence `Quot.sound`). Exact-output
pins, self-verifying (the build fails if a proof change alters the footprint). -/

/-- info: 'Minidregg.Kernel.move_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms move_conserves

/-- info: 'Minidregg.Kernel.mint_breaks_conservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mint_breaks_conservation

end Minidregg.Kernel
