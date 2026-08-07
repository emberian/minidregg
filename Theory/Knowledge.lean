/-
# Theory.Knowledge — the verify/find seam: the foundation of constructive knowledge.

The whole edifice is organized around one asymmetry: **proof-checking is cheap and
trusted; proof-search is undecidable and untrusted** — the BHK / realizability
reading of intuitionistic logic, made operational and distributed. The **verify**
side is decidable and verifier-local (`Verify p w : Bool`); the **find/search**
side is an opaque, possibly-undecidable plugin (the prover / matcher / solver).
The metatheory commits ONLY to the verify side; whatever `find` returns is
re-`Verify`d and never trusted.

A *claim* carries a verifier-side `stmt : P`, and a knower **holds** it iff it can
exhibit a witness `w` that `Verify`s `stmt` — knowledge = a verifiable witness,
full stop, no hidden assertion channel (`holds_iff_discharged_witness`).

Transcribed from breadstuffs' `Dregg2/Laws.lean` (the `Verify`/`find` seam) and
`Metatheory/ConstructiveKnowledge.lean` (`Claim`/`Holds`/`Knower`), renamespaced
`Minidregg.Theory` and candidate-independent from line one.
-/
import Mathlib.Tactic.TypeStar

namespace Minidregg.Theory

universe u

variable {P : Type*} {W : Type*}

/-- The decidable, verifier-local check: does witness `w` satisfy predicate `p`?

This is *simultaneously* the proof target and a runnable function — a Lean
`def … : Bool` is both the spec and the executable golden oracle. -/
class Verifiable (P : Type*) (W : Type*) where
  Verify : P → W → Bool

/-- `Discharged p w` ≜ the verifier accepts: the proof-relevant statement that a
witness discharges a predicate. This is the cross-vat admissibility object — a
freely copyable, verifier-checkable certificate, no off-island mediator. -/
def Discharged [Verifiable P W] (p : P) (w : W) : Prop :=
  Verifiable.Verify p w = true

instance [Verifiable P W] (p : P) (w : W) : Decidable (Discharged p w) := by
  unfold Discharged; exact inferInstanceAs (Decidable (_ = true))

/-- **The opaque search side (the prover plugin).** Given a predicate, *try* to
produce a discharging witness. Modelled as a partial function (`Option`) because
the search may be undecidable / nonterminating; the metatheory makes NO promise
about when it returns `some`. This class is the UNTRUSTED plugin: a `Searchable`
instance may return garbage — an adversarial `find` that returns a non-discharging
witness is a *legal* instance. Soundness is DELIBERATELY NOT a field here precisely
because that would forbid such adversarial plugins; consumers re-`Verify` whatever
`find` returns and never trust it. -/
class Searchable (P : Type*) (W : Type*) where
  find : P → Option W

/-- An abstract **claim** the knower may hold authority over / know. The only
structure a claim has, metatheoretically, is its *verifier statement* `stmt` —
the predicate a witness must discharge to demonstrate the claim. -/
structure Claim (P : Type u) where
  /-- The verifier-side predicate that *demonstrating* this claim must discharge. -/
  stmt : P

/-- **`Holds X`** (the realizability core): a claim is *held* — known
constructively — exactly when **there exists a witness that `Verify`s** its
statement. This is the BHK clause for an atomic capability: knowing `X` ≡
possessing a realizer for `stmt X`. It is *constructive demonstrability*, not
assertion: `Holds` is `∃ w, Discharged X.stmt w`, the existential of the
**decidable, verifier-local** check — authority is established by *exhibiting a
discharging witness at the point of use, and checking it*, never by a global
registry of who-can-do-what. -/
def Holds {P W : Type u} [Verifiable P W] (X : Claim P) : Prop :=
  ∃ w : W, Discharged (P := P) (W := W) X.stmt w

/-- **The verify/find asymmetry, as a structure.** A `Knower` carries the
**trusted, decidable** side — a `Verifiable` instance (`Verify p w : Bool`, the
cheap checkable golden oracle) — but its prover/matcher (`find`) is an
**untrusted, opaque, possibly-undecidable** plugin (`Searchable`, an
`Option`-valued partial function with no completeness/termination promise). The
metatheory commits ONLY to the verify side.

Bundling them in one structure is the faithful statement of the asymmetry: a
knower *is* its decidable verifier together with whatever (untrusted) search it
happens to run. -/
structure Knower (P W : Type u) where
  /-- The TRUSTED side: the cheap, decidable, verifier-local check (the TCB). -/
  verify : Verifiable P W
  /-- The UNTRUSTED side: the opaque prover/matcher plugin (no completeness, no
  termination); the metatheory makes NO promise about when it returns `some`. -/
  search : Searchable P W

/-- **Realizability closure under the verify seam.** Holding is *closed under the
`Verify` seam*: if a knower already verifies a witness `w` for `X`
(`Discharged X.stmt w`), then it `Holds X`. Trivially the converse direction holds
too, so holding **is exactly** "a discharging witness exists." This is the
load-bearing fact that `Holds` is the realizability predicate and nothing more:
knowledge = a verifiable witness, full stop — no hidden assertion channel. -/
theorem holds_iff_discharged_witness {P W : Type u} [Verifiable P W] (X : Claim P) :
    Holds (W := W) X ↔ ∃ w : W, Discharged (P := P) (W := W) X.stmt w :=
  Iff.rfl

end Minidregg.Theory
