/-
# Kernel/Gate.lean — the gated executor: `Verb = admission × footprint`, the 4-leg gate

**SUBSTRATE, SAID OUT LOUD: this is the kernel MODEL / semantic executor** — a
Bool-level fail-closed gate + the `Verb` structure + an `Option`-valued `admit`.
NOT AIR: no constraints, no circuits, nothing arithmetized here. The
arithmetization (Compiler/AdmissionAir) is a separate weaving lane, and per the
derived-path law it must REFINE this model — this file is the spec/source the
compiler lowers, not a hand-written twin of derived output.

The shape is ATLAS §3 item 7 (breadstuffs `Exec/FullForestAuth.lean:433-585`),
re-expressed over minidregg's compressed `KernelState`:

  * **`gateOK` — the 4-leg fail-closed conjunction.**
      credential (WHO: the actor authenticates through the `Theory.Verifiable`
      portal seam) ∧ capability (WHAT: a held cap in `k.caps` grants the act's
      target + rights word) ∧ caveats (the presented attenuation chain is
      discharged against the act) ∧ revocation (the credential nullifier is NOT
      in the COMMITTED `umap` revocation registry — adversary-uncontrollable
      state, never a wire bit).
    Fail-closed: `gateOK` is a bare `&&`-conjunction of positive checks — the
    only path to `true` is all four legs affirmatively passing
    (`gateOK_eq_true_iff`); any single false leg denies.
  * **`Verb = admission × footprint`** (ATLAS §3 item 3's kernel-model shadow):
    a verb is an admission predicate (the epistemic gate) paired with the
    footprint it may touch (the ontic bound). The footprint here is the
    CELL-SET shadow of the camera-tier footprint-Fpu; the `Fpu`-typed
    refinement in the product camera is the named residual `[GATE-fpu]`.
  * **`admit` — the fail-closed executor step**: apply the act IFF
    admission ∧ well-formed ∧ footprint-respected, else `none` (deny). The
    action alphabet is EXACTLY the three conservation-algebra verbs
    (`move`/`create`/`gwrite` — reused, never re-derived); the unbacked `mint`
    is not an `Act` constructor, so the conservation-breaking operation is
    unreachable through the executor *by construction*.

Gate soundness, proved: `admit_fail_closed` (gate false ⇒ deny, plus the four
per-leg denial theorems), `admit_conserves` (an admitted turn conserves every
asset column, via the algebra's conservation theorems, with `create`'s honest
zero-balance side-condition carried as a hypothesis — existence ≠ value),
`admit_footprint` (an admitted turn touches ONLY its declared footprint; in
particular `caps` never changes — the v0 executor cannot mint authority), and
`admit_check_eq_use` (no-TOCTOU: the gate held on EXACTLY the pre-state the act
applied to — one indivisible snapshot, breadstuffs' `gatedNode_check_eq_use`).

Named residuals (honest-partial, not half-ported):

  [GATE-portal]    the credential leg routes through `Theory.Verifiable` (the
     verify/find seam). Its *cryptographic* non-forgeability is the portal
     floor (seL4-style; breadstuffs' `AuthPortal`, "NEVER proved sound in
     Lean") — the kernel model trusts the decidable verifier's verdict. The
     `PortalWit` instance below is the witness instantiation, a stand-in.
  [GATE-chain]     caveats ride the presented turn (macaroon-style). Their
     NON-STRIPPABILITY is credential-integrity (HMAC/signature — the same
     portal floor); the model gates GIVEN the presented chain. The caveat
     vocabulary is a tiny closed AST here; the ONE predicate algebra it merges
     into is the Pred lane's.
  [GATE-hyperedge] `admit` takes a single-incidence request — the `ι = 1`
     slice of `Kernel/Turn.lean`'s hyperedge. The N-party joint gate
     (per-incidence legs over the wide pullback, connecting to
     `[N-TURN-a]`'s `Admissible`) is the connection residual.
  [GATE-fpu]       footprint as an `Fpu` in the four-substance product camera
     (`Kernel/Camera.lean`) — here it is the cell-set shadow.
  [GATE-grant]     no authority-producing verb yet (grant/attenuate/amplify —
     `AmpClosed` territory); `admit_caps_still` proves v0's alphabet leaves
     `caps` untouched, so the gate cannot yet be used to mint authority.
  [GATE-registry-owner] the insert-only registry planes (nullifier /
     commitment / revoked) are owned by `registryCell = 0` in this model;
     refined registry sovereignty is future vocabulary.
-/
import Theory.Knowledge
import Kernel.Verbs

namespace Minidregg.Kernel

/-! ## §1. Rights words and capability grants (against `KernelState.caps`). -/

/-- The rights bit authorizing `move` out of a cell. -/
def rightMove : Nat := 1
/-- The rights bit authorizing `create` at a cell address. -/
def rightCreate : Nat := 2
/-- The rights bit authorizing `gwrite` into a cell's keyed planes. -/
def rightGwrite : Nat := 4

/-- **`Cap.grants`** — does this held capability grant rights word `r` over
`tgt`? Target must match exactly; the required bits must be INCLUDED in the
cap's rights word (`r &&& rights = r` — bitmask inclusion, so an attenuated
cap genuinely grants less). -/
def Cap.grants (cap : Cap) (tgt : CellId) (r : Nat) : Bool :=
  decide (cap.target = tgt) && decide (r &&& cap.rights = r)

/-- The registry sovereign: the model cell that owns the global insert-only
planes (nullifiers / commitments / revocations). `[GATE-registry-owner]`. -/
def registryCell : CellId := 0

/-- The owning cell of a universal address — whose authority a `gwrite` there
demands. Per-cell planes are owned by their cell; registry planes by
`registryCell`. -/
def UKey.owner : UKey → CellId
  | .heap c _ | .lifecycle c => c
  | .nullifier _ | .commitment _ | .revoked _ => registryCell

/-! ## §2. The action alphabet — EXACTLY the three conservation-algebra verbs.

`Act.apply` reuses `move`/`create`/`gwrite` verbatim (State §5, Verbs §1) —
the derived-path law: the executor's semantics IS the algebra's, not a twin.
`mint` is deliberately NOT a constructor: the conservation-breaking operation
has no name in the executor's alphabet. -/

/-- A requested kernel action: one of the three verbs. -/
inductive Act where
  /-- debit `src` / credit `dst` of asset `a` by `δ` (`State.move`). -/
  | move (src dst : CellId) (a : AssetId) (δ : ℤ)
  /-- bring cell `c` into existence (`Verbs.create`). -/
  | create (c : CellId)
  /-- write the one keyed map at `u` (`Verbs.gwrite`). -/
  | gwrite (u : UKey) (v : Option ℤ)
  deriving DecidableEq, Repr

/-- The action's semantics — the conservation-algebra verbs, reused. -/
def Act.apply (act : Act) (k : KernelState) : KernelState :=
  match act with
  | .move src dst a δ => Kernel.move k src dst a δ
  | .create c => Kernel.create k c
  | .gwrite u v => Kernel.gwrite k u v

/-- The cell whose AUTHORITY the act exercises: a `move` demands authority
over the debited `src` (receiving is permissionless in v0), a `create` over
the created address, a `gwrite` over the written address's owner. -/
def Act.target : Act → CellId
  | .move src _ _ _ => src
  | .create c => c
  | .gwrite u _ => u.owner

/-- The rights word the act demands. -/
def Act.reqRights : Act → Nat
  | .move .. => rightMove
  | .create _ => rightCreate
  | .gwrite .. => rightGwrite

/-- The signed amount the act moves (`0` for non-moves) — what amount-caveats
attenuate. -/
def Act.delta : Act → ℤ
  | .move _ _ _ δ => δ
  | _ => 0

/-- **The executor's well-formedness check** (NOT an auth leg — the executor's
own precondition, breadstuffs' `execFullA`-returns-`none` face): a `move`'s
endpoints must both EXIST, so that conservation holds outright (the debit and
credit both land inside the Σ — `move_conserves`' hypotheses, checked rather
than assumed). -/
def Act.wf (a : Act) (k : KernelState) : Bool :=
  match a with
  | .move src dst _ _ => decide (src ∈ k.accounts) && decide (dst ∈ k.accounts)
  | .create _ => true
  | .gwrite _ _ => true

/-! ## §3. Caveats — a tiny CLOSED AST (no opaque `Ctx → Bool` — that is named
debt, ATLAS §5). Merges into the Pred lane's ONE algebra when it lands. -/

/-- A caveat: one attenuation atom carried by the presented chain. -/
inductive Caveat where
  /-- the exercised amount is bounded: `|Act.delta| ≤ n`. -/
  | maxMove (n : ℤ)
  /-- the act's target cell is exactly `c` (scope attenuation). -/
  | onlyCell (c : CellId)
  deriving DecidableEq, Repr

/-- Decidable caveat discharge against the requested act. -/
def Caveat.holds (cv : Caveat) (a : Act) : Bool :=
  match cv with
  | .maxMove n => decide (a.delta ≤ n) && decide (-n ≤ a.delta)
  | .onlyCell c => decide (a.target = c)

/-! ## §4. The turn request — the `ι = 1` slice the gate admits.

The hyperedge (`Kernel/Turn.lean`) is THE turn shape; a `TurnReq` is one
incidence's request: actor + credential (witness for the portal, nullifier for
the registry) + presented caveat chain + the act. `[GATE-hyperedge]` names the
joint N-incidence gate. -/

/-- A single-incidence turn request, parameterized by the credential-witness
type `W` (the portal seam's witness). -/
structure TurnReq (W : Type) where
  /-- who fires the turn. -/
  actor : CellId
  /-- the credential witness — verified by the `Theory.Verifiable` portal. -/
  credWit : W
  /-- the credential's revocation nullifier (looked up in the COMMITTED
  `umap` registry, never a wire bit). -/
  credNul : Nat
  /-- the presented attenuation chain (`[GATE-chain]`: non-strippability is
  the credential-integrity floor). -/
  caveats : List Caveat
  /-- the requested action. -/
  act : Act

variable {W : Type}

/-! ## §5. The four legs and `gateOK` — the fail-closed conjunction. -/

/-- **Leg 1, credential (WHO)**: the actor authenticates — the presented
witness `Verify`s the claim "I am `actor`" through the `Theory.Knowledge`
seam. The verifier's verdict is trusted (decidable, verifier-local); its
crypto soundness is the portal floor `[GATE-portal]`. -/
def credOK [Theory.Verifiable CellId W] (t : TurnReq W) : Bool :=
  Theory.Verifiable.Verify t.actor t.credWit

/-- **Leg 2, capability (WHAT)**: some capability HELD by the actor in the
state's cap table (`k.caps` — the authority store) grants the act's target and
required rights word. Reads the pre-state; an actor with no matching cap fails
closed. -/
def capOK (k : KernelState) (t : TurnReq W) : Bool :=
  (k.caps t.actor).any fun cap => cap.grants t.act.target t.act.reqRights

/-- **Leg 3, caveats**: every caveat on the presented chain is discharged
against the requested act. An empty chain passes (`List.all [] = true` — an
unattenuated credential carries no extra conditions); a violated caveat
fail-closes. -/
def cavOK (t : TurnReq W) : Bool :=
  t.caveats.all fun cv => cv.holds t.act

/-- **Leg 4, revocation**: the credential's nullifier is NOT present in the
COMMITTED revocation registry — a read of `k.umap` at the `UKey.revoked`
plane, i.e. adversary-uncontrollable kernel state (breadstuffs'
`revocationGate`: never the wire-supplied bit). Present ⇒ revoked ⇒ deny. -/
def revOK (k : KernelState) (t : TurnReq W) : Bool :=
  (k.umap (UKey.revoked t.credNul)).isNone

/-- **`gateOK` — the 4-leg FAIL-CLOSED admission gate**: credential ∧
capability ∧ caveats ∧ revocation. A bare `&&`-conjunction of positive
checks — deny is the default; the only path to `true` is all four legs
affirmatively passing. -/
def gateOK [Theory.Verifiable CellId W] (k : KernelState) (t : TurnReq W) : Bool :=
  credOK t && capOK k t && cavOK t && revOK k t

/-- The fail-closed characterization: `gateOK` is `true` EXACTLY when all four
legs are — there is no fifth path in and no leg that can be skipped. -/
theorem gateOK_eq_true_iff [Theory.Verifiable CellId W] {k : KernelState} {t : TurnReq W} :
    gateOK k t = true ↔
      credOK t = true ∧ capOK k t = true ∧ cavOK t = true ∧ revOK k t = true := by
  simp [gateOK, Bool.and_eq_true, and_assoc]

/-- Leg-1 denial: a failed credential kills the gate. -/
theorem gateOK_false_of_cred [Theory.Verifiable CellId W] {k : KernelState} {t : TurnReq W}
    (h : credOK t = false) : gateOK k t = false := by
  simp [gateOK, h]

/-- Leg-2 denial: no granting capability kills the gate. -/
theorem gateOK_false_of_cap [Theory.Verifiable CellId W] {k : KernelState} {t : TurnReq W}
    (h : capOK k t = false) : gateOK k t = false := by
  simp [gateOK, h]

/-- Leg-3 denial: a violated caveat kills the gate. -/
theorem gateOK_false_of_cav [Theory.Verifiable CellId W] {k : KernelState} {t : TurnReq W}
    (h : cavOK t = false) : gateOK k t = false := by
  simp [gateOK, h]

/-- Leg-4 denial: a failed revocation check kills the gate. -/
theorem gateOK_false_of_rev [Theory.Verifiable CellId W] {k : KernelState} {t : TurnReq W}
    (h : revOK k t = false) : gateOK k t = false := by
  simp [gateOK, h]

/-- **Revocation reads COMMITTED state**: any entry at the credential's
`UKey.revoked` address in the one keyed map — however it got there, e.g. by a
prior admitted `gwrite` — denies the gate. The registry is kernel state, so a
revoked credential cannot pass no matter how valid its signature or how
discharged its caveats. -/
theorem gateOK_false_of_revoked [Theory.Verifiable CellId W] {k : KernelState}
    {t : TurnReq W} {r : ℤ} (h : k.umap (UKey.revoked t.credNul) = some r) :
    gateOK k t = false :=
  gateOK_false_of_rev (by simp [revOK, h])

/-! ## §6. `Verb = admission × footprint`, and the executor `admit`. -/

/-- A finite footprint: the balance/existence cells and keyed-map addresses a
verb may touch. -/
structure Footprint where
  /-- cells whose `bal`/`accounts` coordinates may change. -/
  cells : Finset CellId
  /-- keyed-map addresses that may change. -/
  keys : Finset UKey

/-- Decidable footprint containment (both planes, componentwise `⊆`). -/
def Footprint.within (f g : Footprint) : Bool :=
  decide (f.cells ⊆ g.cells) && decide (f.keys ⊆ g.keys)

/-- The EXACT footprint of an act — what its semantics touches. -/
def Act.touched : Act → Footprint
  | .move src dst _ _ => ⟨{src, dst}, ∅⟩
  | .create c => ⟨{c}, ∅⟩
  | .gwrite u _ => ⟨∅, {u}⟩

/-- **`Verb` — admission × footprint** (ATLAS §3 item 3, kernel-model tier): a
verb is a fail-closed admission predicate on state + request, paired with the
declared footprint the verb may touch. `[GATE-fpu]` names the camera-tier
`Fpu` refinement of the footprint half. -/
structure Verb (W : Type) where
  /-- the admission gate (fail-closed: `false` denies). -/
  admission : KernelState → TurnReq W → Bool
  /-- the declared bound on what the verb may touch. -/
  footprint : Footprint

/-- **The canonical gated verb**: admission = the 4-leg `gateOK`, with
declared footprint `fp`. THE kernel executor's verb. -/
def gatedVerb [Theory.Verifiable CellId W] (fp : Footprint) : Verb W :=
  ⟨gateOK, fp⟩

/-- **`admit` — the fail-closed gated executor step.** Apply the requested act
IFF the verb admits ∧ the act is well-formed ∧ the act's exact footprint sits
inside the verb's declared footprint; otherwise `none` (deny). The `some`
branch is EXACTLY the conservation algebra's function — the gate wraps, never
re-derives. -/
def admit (k : KernelState) (v : Verb W) (t : TurnReq W) : Option KernelState :=
  if v.admission k t && t.act.wf k && t.act.touched.within v.footprint
  then some (t.act.apply k)
  else none

/-! ## §7. The gate-soundness theorems: fail-closed, no-TOCTOU. -/

/-- **The load-bearing unfolding lemma** (breadstuffs' `execFullAGated_some_iff`):
`admit` commits IFF admission ∧ well-formedness ∧ footprint containment all
held on the pre-state AND the post-state is exactly the act's application.
Everything below rests on this. -/
theorem admit_some_iff {k k' : KernelState} {v : Verb W} {t : TurnReq W} :
    admit k v t = some k' ↔
      v.admission k t = true ∧ t.act.wf k = true
        ∧ t.act.touched.within v.footprint = true ∧ k' = t.act.apply k := by
  cases ha : v.admission k t <;> cases hw : t.act.wf k
    <;> cases hf : t.act.touched.within v.footprint
    <;> simp [admit, ha, hw, hf, eq_comm]

/-- A refused admission denies — for ANY verb (fail-closed is structural in
`admit`, not a property of the canonical gate only). -/
theorem admit_denies_of_admission_false {k : KernelState} {v : Verb W} {t : TurnReq W}
    (h : v.admission k t = false) : admit k v t = none := by
  simp [admit, h]

/-- **`admit_fail_closed`** — an unauthorized turn is DENIED: if the 4-leg
gate says `false`, the gated verb's executor step is `none`, unconditionally
(no matter the footprint, the act, or the state). -/
theorem admit_fail_closed [Theory.Verifiable CellId W] {k : KernelState} {t : TurnReq W}
    (fp : Footprint) (h : gateOK k t = false) : admit k (gatedVerb fp) t = none :=
  admit_denies_of_admission_false h

/-- Teeth, leg 1: a bad credential alone denies. -/
theorem admit_no_credential [Theory.Verifiable CellId W] {k : KernelState} {t : TurnReq W}
    (fp : Footprint) (h : credOK t = false) : admit k (gatedVerb fp) t = none :=
  admit_fail_closed fp (gateOK_false_of_cred h)

/-- Teeth, leg 2: a missing/insufficient capability alone denies. -/
theorem admit_no_capability [Theory.Verifiable CellId W] {k : KernelState} {t : TurnReq W}
    (fp : Footprint) (h : capOK k t = false) : admit k (gatedVerb fp) t = none :=
  admit_fail_closed fp (gateOK_false_of_cap h)

/-- Teeth, leg 3: a violated caveat alone denies. -/
theorem admit_caveat_violated [Theory.Verifiable CellId W] {k : KernelState} {t : TurnReq W}
    (fp : Footprint) (h : cavOK t = false) : admit k (gatedVerb fp) t = none :=
  admit_fail_closed fp (gateOK_false_of_cav h)

/-- Teeth, leg 4: a revoked credential — an entry at its nullifier in the
committed registry — alone denies. -/
theorem admit_revoked [Theory.Verifiable CellId W] {k : KernelState} {t : TurnReq W}
    (fp : Footprint) {r : ℤ} (h : k.umap (UKey.revoked t.credNul) = some r) :
    admit k (gatedVerb fp) t = none :=
  admit_fail_closed fp (gateOK_false_of_revoked h)

/-- Teeth, footprint: an act reaching OUTSIDE the verb's declared footprint is
denied — even with all four gate legs passing. -/
theorem admit_footprint_violation {k : KernelState} {v : Verb W} {t : TurnReq W}
    (h : t.act.touched.within v.footprint = false) : admit k v t = none := by
  simp [admit, h]

/-- Teeth, well-formedness: an ill-formed act (a `move` with a nonexistent
endpoint) is denied — the executor checks its own preconditions. -/
theorem admit_not_wf {k : KernelState} {v : Verb W} {t : TurnReq W}
    (h : t.act.wf k = false) : admit k v t = none := by
  simp [admit, h]

/-- **No-TOCTOU** (breadstuffs' `gatedNode_check_eq_use`): a committed gated
step proves the 4-leg gate held on EXACTLY the pre-state the act then applied
to — one indivisible snapshot; no window between check and use. -/
theorem admit_check_eq_use [Theory.Verifiable CellId W] {k k' : KernelState}
    {fp : Footprint} {t : TurnReq W} (h : admit k (gatedVerb fp) t = some k') :
    gateOK k t = true ∧ k' = t.act.apply k :=
  let ⟨hg, _, _, hk⟩ := admit_some_iff.mp h
  ⟨hg, hk⟩

/-! ## §8. Conservation and the frame — an admitted turn is SOUND. -/

/-- A `move` of asset `aM` conserves EVERY asset column's total (the moved
column by `move_conserves`; every other column untouched pointwise). -/
theorem move_conserves_col (k : KernelState) (src dst : CellId) (aM : AssetId)
    (δ : ℤ) (hsrc : src ∈ k.accounts) (hdst : dst ∈ k.accounts) (a : AssetId) :
    totalAsset (move k src dst aM δ) a = totalAsset k a := by
  by_cases ha : a = aM
  · subst ha; exact move_conserves k src dst a δ hsrc hdst
  · simp only [totalAsset, move, moveBal, if_neg ha]

/-- **`admit_conserves`** — an ADMITTED turn conserves every per-asset total,
via the conservation algebra: `move` outright (its endpoint-existence
hypotheses are CHECKED by `Act.wf`, not assumed), `gwrite` definitionally, and
`create` under its honest side-condition (`create_conserves`' existence ≠
value: the created cell holds zero of the asset — carried as a hypothesis
because "all asset columns are zero" is not a decidable executor check; the
tooth for violating it is `create_unbacked_breaks`). -/
theorem admit_conserves {k k' : KernelState} {v : Verb W} {t : TurnReq W}
    (a : AssetId) (h : admit k v t = some k')
    (hcreate : ∀ c, t.act = Act.create c → k.bal c a = 0) :
    totalAsset k' a = totalAsset k a := by
  obtain ⟨-, hwf, -, rfl⟩ := admit_some_iff.mp h
  cases hact : t.act with
  | move src dst aM δ =>
    rw [hact] at hwf
    simp only [Act.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    exact move_conserves_col k src dst aM δ hwf.1 hwf.2 a
  | create c =>
    exact create_conserves k c a (hcreate c hact)
  | gwrite u vv =>
    exact gwrite_conserves k u vv a

/-- **`admit_footprint`** — the FRAME: an admitted turn touches ONLY the
verb's declared footprint. Every cell outside `footprint.cells` keeps its
entire balance column and its existence bit; every address outside
`footprint.keys` keeps its map entry; and the capability table NEVER changes
(v0's alphabet has no authority-producing verb — `[GATE-grant]`). -/
theorem admit_footprint {k k' : KernelState} {v : Verb W} {t : TurnReq W}
    (h : admit k v t = some k') :
    (∀ c : CellId, c ∉ v.footprint.cells →
        (∀ a : AssetId, k'.bal c a = k.bal c a) ∧ (c ∈ k'.accounts ↔ c ∈ k.accounts))
    ∧ (∀ u : UKey, u ∉ v.footprint.keys → k'.umap u = k.umap u)
    ∧ k'.caps = k.caps := by
  obtain ⟨-, -, hfp, rfl⟩ := admit_some_iff.mp h
  cases hact : t.act with
  | move src dst aM δ =>
    rw [hact] at hfp
    simp only [Act.touched, Footprint.within, Bool.and_eq_true,
      decide_eq_true_eq] at hfp
    obtain ⟨hcells, -⟩ := hfp
    refine ⟨fun c hc => ?_, fun u _ => rfl, rfl⟩
    have hcs : c ≠ src := fun hh => hc (hcells (by simp [hh]))
    have hcd : c ≠ dst := fun hh => hc (hcells (by simp [hh]))
    exact ⟨fun a => by
      show moveBal k.bal src dst aM δ c a = k.bal c a
      simp [moveBal, hcs, hcd], Iff.rfl⟩
  | create c0 =>
    rw [hact] at hfp
    simp only [Act.touched, Footprint.within, Bool.and_eq_true,
      decide_eq_true_eq] at hfp
    obtain ⟨hcells, -⟩ := hfp
    refine ⟨fun c hc => ?_, fun u _ => rfl, rfl⟩
    have hcc : c ≠ c0 := fun hh => hc (hcells (by simp [hh]))
    exact ⟨fun _ => rfl, create_accounts_frame k c0 c hcc⟩
  | gwrite u0 v0 =>
    rw [hact] at hfp
    simp only [Act.touched, Footprint.within, Bool.and_eq_true,
      decide_eq_true_eq] at hfp
    obtain ⟨-, hkeys⟩ := hfp
    refine ⟨fun c _ => ⟨fun _ => rfl, Iff.rfl⟩, fun u hu => ?_, rfl⟩
    have huu : u ≠ u0 := fun hh => hu (hkeys (by simp [hh]))
    exact gwrite_umap_frame k u0 v0 u huu

/-- The authority plane stands still under EVERY admitted v0 turn: the gate
consumes authority (checks caps), it never produces it. `[GATE-grant]` names
the future authority-producing verbs — they enter as new `Act` vocabulary with
their own admission legs, not as a bypass. -/
theorem admit_caps_still {k k' : KernelState} {v : Verb W} {t : TurnReq W}
    (h : admit k v t = some k') : k'.caps = k.caps :=
  (admit_footprint h).2.2

/-! ## §9. The portal instantiation + keystone witnesses (built, both poles,
computing — the audit law).

`PortalWit` is the WITNESS instantiation of the `[GATE-portal]` seam: a
stand-in keyed relation in place of signature verification (type-distinct from
any real credential — ATLAS §6 law 3's toy discipline). The gate's theorems
above are generic in the seam; nothing below feeds back into them. -/

/-- The stand-in credential witness (portal floor: `[GATE-portal]`). -/
structure PortalWit where
  /-- the presented secret. -/
  secret : Nat
  deriving DecidableEq, Repr

/-- The stand-in portal relation: the secret expected of `c` ("signature
verification" collapsed to a keyed table — the floor, not the model's claim). -/
def portalKey (c : CellId) : Nat := 2 * c + 101

instance portalVerifier : Theory.Verifiable CellId PortalWit :=
  ⟨fun c w => decide (w.secret = portalKey c)⟩

/-- `kA`: `State.k0` (cells `{0,1}` holding 5 and 3 of asset 0) with actor 0
holding ONE capability: `move` rights over cell 0 — the minimal authority the
good turn needs, and nothing else (so the teeth below genuinely isolate
legs). -/
private def kA : KernelState :=
  { k0 with caps := fun c => if c = 0 then [⟨0, rightMove⟩] else [] }

private def fpG : Footprint := ⟨{0, 1}, ∅⟩

private def vG : Verb PortalWit := gatedVerb fpG

/-- The AUTHORIZED turn: actor 0, correct portal secret, unrevoked nullifier,
caveats `|δ| ≤ 3` and `target = 0` both satisfied, moving 2 of asset 0 from
cell 0 to cell 1 inside the declared footprint. -/
private def tGood : TurnReq PortalWit :=
  { actor := 0, credWit := ⟨portalKey 0⟩, credNul := 7,
    caveats := [.maxMove 3, .onlyCell 0], act := .move 0 1 0 2 }

/-- *Satisfiable*: all four legs pass, COMPUTED (`gateOK` evaluates `true` on
the concrete state and turn — the gate is passable, not `false`-everywhere). -/
example : gateOK kA tGood = true := by decide

/-- *Satisfiable*: the authorized turn IS ADMITTED — `admit` commits to
exactly the algebra's `move`. All three guard conjuncts computed. -/
theorem tGood_admitted : admit kA vG tGood = some (move kA 0 1 0 2) :=
  admit_some_iff.mpr ⟨by decide, by decide, by decide, rfl⟩

/-- *Satisfiable*: the admitted turn CONSERVES — via `admit_conserves` (the
`create` side-condition discharged vacuously: the act is a move). -/
example : totalAsset (move kA 0 1 0 2) 0 = totalAsset kA 0 :=
  admit_conserves 0 tGood_admitted (fun c h => by simp [tGood] at h)

/-- … and the total is genuinely COMPUTED on both sides (Σ folds `{0,1}`:
3 + 5 = 8 after, 5 + 3 = 8 before — the ledger moved, the total did not). -/
example : totalAsset (move kA 0 1 0 2) 0 = 8 := by
  simp only [totalAsset, move, moveBal, kA, k0]
  rw [Finset.sum_pair (show (0 : CellId) ≠ 1 by decide)]
  decide

example : totalAsset kA 0 = 8 := by
  simp only [totalAsset, kA, k0]
  rw [Finset.sum_pair (show (0 : CellId) ≠ 1 by decide)]
  decide

/-! ### Teeth — each leg's failure DENIES, and each is load-bearing: in every
tooth below the OTHER three legs still pass (computed beside the denial), so
the deny is attributable to exactly the failed leg. -/

/-- Leg 1 tooth: wrong portal secret. -/
private def tBadCred : TurnReq PortalWit := { tGood with credWit := ⟨0⟩ }

example : credOK tBadCred = false := by decide
/-- the other three legs still pass — the credential leg alone denies. -/
example : (capOK kA tBadCred && cavOK tBadCred && revOK kA tBadCred) = true := by
  decide
example : admit kA vG tBadCred = none := admit_no_credential fpG (by decide)

/-- Leg 2 tooth (no cap): actor 1 authenticates fine but holds NO capability. -/
private def tNoCap : TurnReq PortalWit :=
  { tGood with actor := 1, credWit := ⟨portalKey 1⟩ }

example : capOK kA tNoCap = false := by decide
example : (credOK tNoCap && cavOK tNoCap && revOK kA tNoCap) = true := by decide
example : admit kA vG tNoCap = none := admit_no_capability fpG (by decide)

/-- Leg 2 tooth (insufficient rights): actor 0's cap targets cell 0 but its
rights word is `rightMove` — a `gwrite` into cell 0's heap demands
`rightGwrite`, and bitmask inclusion refuses. Attenuation is real: holding
SOME cap on the target is not holding THE right. -/
private def tWrongRights : TurnReq PortalWit :=
  { tGood with act := .gwrite (UKey.heap 0 0) (some 1), caveats := [] }

example : capOK kA tWrongRights = false := by decide
example : (credOK tWrongRights && cavOK tWrongRights && revOK kA tWrongRights) = true := by
  decide
example : admit kA (gatedVerb ⟨∅, {UKey.heap 0 0}⟩) tWrongRights = none :=
  admit_no_capability _ (by decide)

/-- Leg 3 tooth: moving 5 violates the presented `maxMove 3` caveat. -/
private def tBadCav : TurnReq PortalWit := { tGood with act := .move 0 1 0 5 }

example : cavOK tBadCav = false := by decide
example : (credOK tBadCav && capOK kA tBadCav && revOK kA tBadCav) = true := by decide
example : admit kA vG tBadCav = none := admit_caveat_violated fpG (by decide)

/-- Leg 4 tooth: revoke the credential IN COMMITTED STATE — via the kernel's
own `gwrite` into the `UKey.revoked` registry plane — and the previously
admitted `tGood` is now DENIED on the new state. The registry is state, not
wire. -/
private def kRev : KernelState := gwrite kA (UKey.revoked 7) (some 1)

example : revOK kRev tGood = false := by decide
example : (credOK tGood && capOK kRev tGood && cavOK tGood) = true := by decide
example : admit kRev vG tGood = none := admit_revoked fpG (r := 1) (by decide)

/-- Footprint tooth: the SAME fully authorized turn (`gateOK = true`,
computed above) is DENIED under a verb whose declared footprint omits cell 1 —
the footprint bound bites independently of the auth legs. -/
example : admit kA (gatedVerb ⟨{0}, ∅⟩ : Verb PortalWit) tGood = none :=
  admit_footprint_violation (by decide)

/-- Well-formedness tooth: a move out of the nonexistent cell 5 — actor 0
even HOLDS a cap over cell 5, the portal and caveats pass — is denied by the
executor's own precondition check (`Act.wf`: 5 ∉ accounts). -/
private def kA5 : KernelState :=
  { k0 with caps := fun c => if c = 0 then [⟨5, rightMove⟩] else [] }

private def tGhost : TurnReq PortalWit :=
  { tGood with act := .move 5 1 0 2, caveats := [] }

example : gateOK kA5 tGhost = true := by decide
example : Act.wf tGhost.act kA5 = false := by decide
example : admit kA5 (gatedVerb ⟨{5, 1}, ∅⟩ : Verb PortalWit) tGhost = none :=
  admit_not_wf (by decide)

/-! ## §10. The FFI seam — the kernel IS the executor (`@[export]`).

ATLAS §2: "The Lean kernel IS the executor (FFI export)." This is the FIRST
`@[export]` in `Kernel/` — it proves the export path EXISTS for the gate: the
monomorphic 4-leg decision is a compiled symbol (`minidregg_gate_ok`) a Rust
caller links against (rust/ authors nothing; every decision point is a Lean
export). The full marshalling story (state handles, turn codecs) is
Distributed/rust-lane work; the seam itself is now real. -/

@[export minidregg_gate_ok]
def gateOKExport (k : KernelState) (t : TurnReq PortalWit) : Bool :=
  gateOK k t

/-! ## §11. Axiom pins (exact-output, self-verifying — State §8's discipline).
Kernel-clean throughout: every footprint `⊆ {propext, Classical.choice,
Quot.sound}`. -/

/-- info: 'Minidregg.Kernel.admit_fail_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms admit_fail_closed

/-- info: 'Minidregg.Kernel.admit_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms admit_conserves

/-- info: 'Minidregg.Kernel.admit_footprint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms admit_footprint

/-- info: 'Minidregg.Kernel.admit_check_eq_use' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms admit_check_eq_use

/-- info: 'Minidregg.Kernel.gateOK_eq_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms gateOK_eq_true_iff

end Minidregg.Kernel
