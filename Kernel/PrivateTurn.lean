/-
# `Kernel/PrivateTurn.lean` — the private-witness turn, the kernel MODEL (`[PRIVATE-TURN-kernel]`)

**Substrate, said out loud (the tripwire):** this file is PURE DATA/MODEL — `Kernel/Turn.lean`'s
`Hyperedge` instantiated at a product carrier, plus theorems about its public projection. NO
AIR, NO constraint system, NO gated Verb/admission, NO executor arm is authored here. The
constraint side that would make a private turn SOUNDLY CONSTRAIN is the Lean-authored
`[PRIVATE-TURN-air]` lane (named in `Assurance/PrivateTurn.lean`), and the CRYPTOGRAPHIC hiding
— a verifier's masked-opening view cannot distinguish witnesses — is Assurance-level
(`Assurance/PrivateTurn.lean`, riding Selvage; the Kernel boundary forbids importing either here).

What the KERNEL owns is the model fact both of those sit on: a participant's state splits into
a PUBLIC half and a PRIVATE witness (`Pub × Priv`); a private-witness turn is the ONE hyperedge
over that carrier — validity (`agree` + `balanced`) is imposed on the FULL state, witness
included — while the OBSERVABLE (`publicView`) reads only the public projections, the turn, the
apex, and the aggregate. The keystone `privateTurn_public_indistinguishable`: two valid
private-witness turns agreeing on public data present IDENTICAL public views however their
witnesses differ. Three of its four legs are congruence; the load-bearing leg is the aggregate,
which is computed over the full (witness-carrying) states and agrees only BECAUSE both turns
are `balanced`. So "a turn can carry a hidden witness" is a kernel theorem: the view is blind
to the witness, the validity is not.

This closes `[PRIVATE-TURN-kernel]` as named in `Assurance/PrivateTurn.lean` ("the wire-up to
a `Kernel/Turn` variant carrying a private witness … a model design step, not taken") — and
the variant is NOT a new primitive: HYPEREDGE-DESIGN's one turn shape, at carrier `Pub × Priv`.

Modeling choice, stated plainly: the turn instruction `t` and the apex `tid` are PUBLIC (the
declared effect is revealed — matching `Assurance/PrivateTurn`'s public claim); what hides is
the participants' witness halves. Hiding here is EQUALITY of views (the model statement), not
an adversary/distribution statement — that stronger claim lives in Assurance and is not made
by this file.
-/
import Kernel.Turn
import Mathlib.Tactic.FinCases

namespace Minidregg.Kernel

universe u v

/-! ## §1. The private carrier and the private-witness turn.

A private carrier is a product `Pub × Priv`: a public half (what the verifier sees) and a
private witness (what only the participant holds). The projection `π = Prod.fst` is the
observable. A private-witness turn is then nothing new — the one hyperedge, at the product
carrier. -/

/-- **The private-witness hyperedge** — `Hyperedge` at carrier `Pub × Priv`. An `abbrev`, so a
`PrivateHyperedge` IS a `Hyperedge` definitionally: every hyperedge theorem (`legs_agree`,
`binary_balanced`, …) applies verbatim, nothing re-derived. `agree` and `balanced` bind the
FULL `(pub, priv)` states — the witness sits inside validity, not beside it. -/
abbrev PrivateHyperedge (ι : Type v) [Fintype ι]
    (Pub Priv Turn TurnId Bal : Type u) [AddCommMonoid Bal] [DecidableEq TurnId]
    (step : Pub × Priv → Turn → Pub × Priv)
    (turnId : ι → Pub × Priv → TurnId)
    (halfEdge : ι → Pub × Priv → Turn → Bal) :=
  Hyperedge ι (Pub × Priv) Turn TurnId Bal step turnId halfEdge

variable {ι : Type v} [Fintype ι]
variable {Pub Priv Turn TurnId Bal : Type u} [AddCommMonoid Bal] [DecidableEq TurnId]
variable {step : Pub × Priv → Turn → Pub × Priv}
variable {turnId : ι → Pub × Priv → TurnId}
variable {halfEdge : ι → Pub × Priv → Turn → Bal}

/-- **A private-witness turn IS a hyperedge over the full state** — definitionally. Recorded
as a checked type equality so the IS-A is a verified statement, not prose: whatever holds of
hyperedges holds of private-witness turns, and `agree`/`balanced` constrain the complete
`(pub, priv)` participant states, witness included. -/
theorem privateHyperedge_is_hyperedge :
    PrivateHyperedge ι Pub Priv Turn TurnId Bal step turnId halfEdge
      = Hyperedge ι (Pub × Priv) Turn TurnId Bal step turnId halfEdge := rfl

/-! ## §2. The public observable. -/

/-- **What the verifier sees** of a private-witness turn: the public projection of each
participant's pre-state (`π ∘ x`), the (public) turn instruction, the (public) shared apex,
and the claimed conservation aggregate. The private halves appear NOWHERE in this record —
that absence is the model's whole content. -/
structure PublicView (ι : Type v) (Pub Turn TurnId Bal : Type u) where
  /-- the public projection of each participant's pre-state (`π ∘ x`). -/
  pubs : ι → Pub
  /-- the turn instruction (public — the declared effect is revealed). -/
  t : Turn
  /-- the shared apex id (public — Mina's `account_updates_hash` analogue). -/
  tid : TurnId
  /-- the claimed conservation aggregate. -/
  balance : Bal

/-- The public observable of a private-witness turn. Note `balance` is computed over the FULL
states (the half-edges read the witness halves) — the keystone below is about when that
computation is nonetheless invisible. -/
def PrivateHyperedge.publicView
    (H : PrivateHyperedge ι Pub Priv Turn TurnId Bal step turnId halfEdge) :
    PublicView ι Pub Turn TurnId Bal where
  pubs i := (H.x i).1
  t := H.t
  tid := H.tid
  balance := Finset.univ.sum fun i => halfEdge i (H.x i) H.t

/-- A valid turn's published aggregate is `0` — `balanced`, exported to the observable. -/
theorem PrivateHyperedge.publicView_balance_zero
    (H : PrivateHyperedge ι Pub Priv Turn TurnId Bal step turnId halfEdge) :
    H.publicView.balance = 0 := H.balanced

/-! ## §3. The keystone — public indistinguishability. -/

/-- **`[PRIVATE-TURN-kernel]` — public indistinguishability of the hidden witness.** Two
private-witness turns agreeing on their PUBLIC data — participant projections, turn, apex —
present IDENTICAL public views, whatever their private witnesses. The `pubs`/`t`/`tid` legs
are congruence; the `balance` leg is the genuine one: the aggregate is a sum over the FULL
states, whose witness halves may differ arbitrarily between `H₁` and `H₂` — it agrees because
BOTH turns are valid (`balanced` pins both sums to `0`). So on valid turns the observable is
a function of public data alone, and a hidden witness leaves no trace in it. (The
cryptographic form — a verifier's spot-check distribution cannot distinguish — is
`Assurance/PrivateTurn.lean`'s `privateTurn_witness_hidden`; not this file's claim.) -/
theorem privateTurn_public_indistinguishable
    (H₁ H₂ : PrivateHyperedge ι Pub Priv Turn TurnId Bal step turnId halfEdge)
    (hpub : ∀ i, (H₁.x i).1 = (H₂.x i).1)
    (ht : H₁.t = H₂.t) (htid : H₁.tid = H₂.tid) :
    H₁.publicView = H₂.publicView := by
  have hb : (Finset.univ.sum fun i => halfEdge i (H₁.x i) H₁.t)
      = Finset.univ.sum fun i => halfEdge i (H₂.x i) H₂.t :=
    H₁.balanced.trans H₂.balanced.symm
  simp only [PrivateHyperedge.publicView, PublicView.mk.injEq]
  exact ⟨funext hpub, ht, htid, hb⟩

/-- **The post-state does not leak either — under a witness-blind step.** If `step`'s public
half depends only on the public half (`hblind`), two publicly-agreeing turns also agree on
every POST-step public projection. `hblind` is a REAL premise, not derivable — see
`leaky_step_leaks` — and it names exactly the non-leakage obligation a deployed step owes. -/
theorem post_public_agrees
    (H₁ H₂ : PrivateHyperedge ι Pub Priv Turn TurnId Bal step turnId halfEdge)
    (hblind : ∀ (p : Pub) (v v' : Priv) (τ : Turn), (step (p, v) τ).1 = (step (p, v') τ).1)
    (hpub : ∀ i, (H₁.x i).1 = (H₂.x i).1) (ht : H₁.t = H₂.t) (i : ι) :
    (step (H₁.x i) H₁.t).1 = (step (H₂.x i) H₂.t).1 := by
  have h := hblind (H₁.x i).1 (H₁.x i).2 (H₂.x i).2 H₁.t
  rw [Prod.mk.eta] at h
  rw [h, hpub i, ht, Prod.mk.eta]

/-- **Witness-blindness has teeth** (the premise is genuine): a step that funnels the witness
into the public half leaks it — two states with equal public halves and distinct witnesses
get DISTINCT post-step public projections. So `post_public_agrees`'s `hblind` cannot be
dropped; a deployed step must actually discharge it. -/
theorem leaky_step_leaks :
    ∃ (step : ℤ × ℤ → ℤ → ℤ × ℤ) (s₁ s₂ : ℤ × ℤ),
      s₁.1 = s₂.1 ∧ s₁.2 ≠ s₂.2 ∧ (step s₁ 0).1 ≠ (step s₂ 0).1 :=
  ⟨fun s _ => (s.2, s.2), (5, 3), (5, 7), rfl, by decide, by decide⟩

/-! ## §4. The concrete private-witness turn — a hidden-note transfer (`ι = Fin 2`).

Turn.lean's `ℤ` flavor with carrier `ℤ × ℤ`: public half = the cell's public balance, private
half = the value of a note the cell holds. The turn `δ : ℤ` is the PUBLIC declared amount.
The balance monoid is `ℤ × ℤ` — a PUBLIC value column and a PRIVATE note column:

  * public column: sender `−δ`, receiver `+δ` — the transfer effect, revealed (a function of
    the public instruction alone);
  * private column: sender `−note`, receiver `+note` — the note leaves cell 0 and lands in
    cell 1; `balanced` forces the arriving note to EQUAL the departing note without the view
    revealing either.

`nstep` spends the note (zeroes the private register — the consumed post-state; the deployed
kernel records exactly this fact on `Kernel/State.lean`'s `UKey.nullifier` plane) and carries
the public half through — witness-blind in the `post_public_agrees` sense. `nturnId` reads the
post-step private register: the apex condition "every leg reads `0`" is the nullification
fact — a condition ON the private state that reveals nothing about its value. -/

namespace NoteTransfer

/-- the step: the turn consumes (nullifies) the note; the public half is carried through (the
ledger application is the executor lane, not this model). Witness-blind on its public half. -/
def nstep : ℤ × ℤ → ℤ → ℤ × ℤ := fun s _ => (s.1, 0)

/-- each leg's apex reading: the post-step private register. `agree` at `tid = 0` says "the
note was consumed at every incidence" — a real condition on the private state, value-blind. -/
def nturnId : Fin 2 → ℤ × ℤ → ℤ := fun _ s => s.2

/-- the two-column half-edges `(public flow, private note flow)`: sender `(−δ, −note)`,
receiver `(+δ, +note)`. -/
def nhalfEdge : Fin 2 → ℤ × ℤ → ℤ → ℤ × ℤ :=
  ![fun s δ => (-δ, -s.2), fun s δ => (δ, s.2)]

/-- **The private-witness note transfer at witness `v`**: cell 0 (public balance 5) sends,
cell 1 (public balance 9) receives; declared public amount `2`; the note value `v` is the
private witness — forced equal on both sides by `balanced`, revealed by nothing. -/
def transfer (v : ℤ) :
    PrivateHyperedge (Fin 2) ℤ ℤ ℤ ℤ (ℤ × ℤ) nstep nturnId nhalfEdge where
  x := ![(5, v), (9, v)]
  t := 2
  tid := 0
  agree := by intro i; fin_cases i <;> rfl
  balanced := by rw [Fin.sum_univ_two]; simp [nhalfEdge]

/-! ## §5. Keystone fields — BUILT (`ι = Fin 2`).

satisfiable — a genuine private-witness turn exists, valid over the full state;
teeth — TWO turns, SAME public view, DIFFERENT witnesses, both valid;
premise-inhabitation — the private carrier is inhabited;
plus the constraint tooth: validity genuinely binds the witness (mismatched notes admit NO
turn), so hiding is not indifference. -/

/-- The turn carrying witness `3`. -/
def T₁ : PrivateHyperedge (Fin 2) ℤ ℤ ℤ ℤ (ℤ × ℤ) nstep nturnId nhalfEdge := transfer 3

/-- The turn carrying witness `7`. -/
def T₂ : PrivateHyperedge (Fin 2) ℤ ℤ ℤ ℤ (ℤ × ℤ) nstep nturnId nhalfEdge := transfer 7

/-- **satisfiable** — a private-witness turn EXISTS: `T₁` is a genuine `PrivateHyperedge`
(its `agree`/`balanced` fields are real proofs over the full `(pub, priv)` states, witness
`3` inside the aggregate). -/
theorem privateTurn_satisfiable :
    Nonempty (PrivateHyperedge (Fin 2) ℤ ℤ ℤ ℤ (ℤ × ℤ) nstep nturnId nhalfEdge) := ⟨T₁⟩

/-- Reuse exhibited, not re-derived: `Hyperedge.legs_agree` applies to a private-witness turn
verbatim (the `abbrev` IS-A, exercised). -/
example (i j : Fin 2) :
    nturnId i (nstep (T₁.x i) T₁.t) = nturnId j (nstep (T₁.x j) T₁.t) :=
  T₁.legs_agree i j

/-- The witnesses are what they claim (the hidden values are genuinely in the states). -/
example : (T₁.x 0).2 = 3 ∧ (T₂.x 0).2 = 7 := by decide

/-- The public view carries the genuine public data (pubs actually read the states). -/
example : T₁.publicView.pubs 0 = 5 ∧ T₁.publicView.pubs 1 = 9 ∧ T₁.publicView.t = 2 := by
  refine ⟨rfl, rfl, rfl⟩

/-- **teeth** — the hidden witness is REAL: `T₁` and `T₂` present the IDENTICAL public view
while carrying DISTINCT private witnesses (`3 ≠ 7`) — and both are valid by TYPE (each is a
`PrivateHyperedge`, its validity fields real proofs). The verifier's observable cannot
separate them; only the hidden halves differ. -/
theorem witness_hidden :
    T₁.publicView = T₂.publicView ∧ (T₁.x 0).2 ≠ (T₂.x 0).2 :=
  ⟨privateTurn_public_indistinguishable T₁ T₂ (by decide) rfl rfl, by decide⟩

/-- The whole witness FAMILY collapses to one view: for EVERY pair of note values the
transfer's public view is the same — the observable quotients out the witness entirely
(`Selvage`'s `witness_free` shape, at the model level). -/
theorem transfer_view_witness_free (v w : ℤ) :
    (transfer v).publicView = (transfer w).publicView :=
  privateTurn_public_indistinguishable (transfer v) (transfer w)
    (by intro i; fin_cases i <;> rfl) rfl rfl

/-- **The constraint tooth — hiding is not indifference**: validity genuinely BINDS the
witness. Mismatched notes (sent `3`, received `4`) admit NO private-witness turn on this
incidence data, whatever the instruction — `balanced`'s private column refuses (`−3 + 4 ≠ 0`).
The witness is hidden by the VIEW yet bound by the TURN: the ZK shape, at the model level. -/
theorem mismatched_notes_rejected :
    ¬ ∃ H : PrivateHyperedge (Fin 2) ℤ ℤ ℤ ℤ (ℤ × ℤ) nstep nturnId nhalfEdge,
      H.x = ![(5, 3), (9, 4)] := by
  rintro ⟨H, hx⟩
  have hb := H.balanced
  rw [Fin.sum_univ_two, hx] at hb
  simp [nhalfEdge, Prod.ext_iff] at hb

/-- **premise-inhabitation** — the private carrier is inhabited (nothing above is about an
empty type): a concrete `(pub, priv)` point, the very one `T₁`'s sender holds. -/
theorem private_carrier_inhabited : Nonempty (ℤ × ℤ) := ⟨(5, 3)⟩

end NoteTransfer

/-! ## §6. Honest residual + axiom pins.

What this file does NOT claim, named:

  `[PRIVATE-TURN-air]` — unchanged, still the named Assurance lane: the Lean-authored
     constraint system (note-opening, exact-nullifier derivation, membership) that makes a
     private turn SOUNDLY CONSTRAIN. Nothing here is a constraint system, by design.

  `[PRIVATE-TURN-crypto]` — hiding here is EQUALITY of public views: perfect, model-level,
     no adversary, no distribution, no computational content. The cryptographic statement
     (masked openings, simulator) is `Assurance/PrivateTurn.lean` + Selvage; this file only
     supplies the kernel object it is ABOUT.

  `[PRIVATE-TURN-exec]` — the admission side (a gated verb accepting a private turn given
     only its `publicView`) is the executor lane; when it lands it comes out of the compiler,
     never hand-written here. `post_public_agrees` already names the obligation a deployed
     `step` owes it (`hblind` — and `leaky_step_leaks` shows the obligation is real).
-/

/-- info: 'Minidregg.Kernel.privateTurn_public_indistinguishable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms privateTurn_public_indistinguishable

/-- info: 'Minidregg.Kernel.NoteTransfer.witness_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NoteTransfer.witness_hidden

/-- info: 'Minidregg.Kernel.NoteTransfer.mismatched_notes_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NoteTransfer.mismatched_notes_rejected

end Minidregg.Kernel
