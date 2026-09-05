/-
# Compiler.DistributiveLaw — N4: the kernel as a distributive law (Turi–Plotkin), abstract half

## What this file is (KERNEL-NECESSITY §N4, designed in `docs/N4-DISTRIBUTIVE-LAW.md`)

N3 (`Compiler/Signature.lean`) fixed the SYNTAX side: a polynomial signature `Σ`, its
initial algebra `Term S` (mathlib `WType`), and `fold_unique` — one induction. N4 adds the
BEHAVIOUR side and the bridge between them. Over an abstract polynomial syntax functor `Σ`
(a `Signature`) and an abstract polynomial behaviour functor `B` (a `PFunctor`, so that
mathlib's `PFunctor.M` is its final coalgebra), a DISTRIBUTIVE LAW `λ : Σ∘B ⇒ B∘Σ` yields
two canonical λ-bialgebras — the OPERATIONAL model on closed terms (a `B`-coalgebra on
`Term S`, built by `fold`) and the DENOTATIONAL model on behaviours (a `Σ`-algebra on
`M B`, built by `M.corec`) — and the theorem:

  * `N4_adequacy`  — `fold (denModel l) = M.corec (opModel l)`: the compositional reading
    and the coinductive unfolding are ONE map `Term S → M B`, and it is the unique
    bialgebra homomorphism (unique as a Σ-hom by `fold_unique`, as a B-hom by
    `M.corec_unique`).
  * `N4_congruence` — behavioural equivalence (`Bisim`: equal points of `νB`) is a
    congruence at EVERY shape of `Σ`: bisimilar arguments, bisimilar node.

## What the file finds (the §3 answer to "does the fail-closed `Option` gate fit?")

The only axiom of a plain endofunctor law is NATURALITY (the η/μ squares belong to the
free-monad refinement, `[N4-gsos]`). Naturality does NOT force fail-closedness: at the
toy signature (two leaves, one unary `tick`, one binary `join`) BOTH the strict law
(`strictLaw`, the `Option`-traversal — a refused leg refuses the joint node) and the
fail-open law (`openLaw` — the refused leg is dropped and the joint node COMMITS) are
`DistLaw`s. Fail-closedness is therefore a separate keystone Prop on a law, `FailClosed`,
proved for `strictLaw` and REFUTED for `openLaw` on the concrete term
`joinT goT stopT` — a joint turn with one refusing participant, which `openLaw` commits
(`open_joint_commits`) and `strictLaw` refuses (`strict_joint_refuses`).

And the collapse the design predicted, stated as theorems rather than padded over: at a
UNARY shape the strict law is literally `Option.map` (`sequential_law_is_option_map`,
`rfl`), and the unary node is invisible to behaviour (`tick_invisible`, via `M.bisim`) —
N4 has no content at the sequential fragment; its content is the binary `join`, where
`N4_congruence` bites on a bisimilar-but-syntactically-distinct pair
(`congruence_fires` + `congruence_pair_distinct`).

## Mathlib reuse (pin 1c2b90b / v4.30.0)

`PFunctor` (`Obj`/`map`/`map_map`/`map_eq`/`fst_map`), `PFunctor.M` with `M.corec`,
`M.dest`, `M.dest_corec`, `M.corec_unique`, `M.bisim`; from `Compiler.Signature`:
`Signature`, `Term`, `Alg`, `fold`, `fold_mk`, `fold_unique`, `termAlg`. Mathlib at this pin
has NO distributive law and NO bialgebra (`CategoryTheory/Distributive/` is distributive
CATEGORIES; `RingTheory/Bialgebra/` is Hopf); `DistLaw`/`Bialgebra` are authored here.

## Residuals (prose tags, not stubs)

  [N4-home]      This is candidate-independent content and belongs in `Theory/`, but
     `Theory/` may import only Mathlib + Theory and the N3 engine (`fold`,
     `fold_unique`) lives in `Compiler/Signature.lean`; re-deriving it in Theory would
     be a twin. The move is relocating `Signature.lean` → `Theory/` (it imports Mathlib
     only) and this file with it — an owner decision, not tonight's.
  [N4-hyperedge-instance]  The kernel instance: `Kernel/Turn.lean`'s `Hyperedge` as the
     `ι`-ary joint shape over the Moore behaviour functor `Req → Obs × X` with cells as
     constants and the balance side-condition read off `Obs` (the half-edge must be
     OBSERVABLE for the joint rule to be in-format — `docs/N4-DISTRIBUTIVE-LAW.md` §3.4).
     Waits on the twin decision (`docs/KERNEL-TWIN-AUDIT.md` §8) and on `Obs`.
  [N4-gsos]      Only the plain law `Σ∘B ⇒ B∘Σ` is built. It cannot express prefixing
     (`o;x → x` steps to a bare variable); sequencing needs the GSOS shape
     `ρ : Σ(Id × B) ⇒ B T_Σ` over the free monad, with the η/μ squares. That is why the
     unary `tick` here is a LIFT (`Option.map`), not a prefix.

## Boundary

Imports Mathlib + `Compiler.Signature` only (Compiler may import Mathlib + Theory + Compiler).
-/
import Mathlib.Data.PFunctor.Univariate.M
import Compiler.Signature

namespace Minidregg.Compiler.DistributiveLaw

open Minidregg.Compiler PFunctor

universe u

/-! ## §1. Distributive laws and λ-bialgebras, over abstract polynomial `Σ` and `B`.

Everything lives in one universe `u` so that `Term S`, `M B`, and the composites
`Σ (B X)`, `B (Σ X)` all sit in `Type u` without `ULift`. -/

/-- **`DistLaw S B`** — a distributive law of the syntax functor `Σ = S.toPFunctor` over the
behaviour functor `B`: a family of components `Σ (B X) → B (Σ X)` that is NATURAL in `X`.
Naturality is the ONLY axiom of a plain endofunctor law; the unit/multiplication squares of
Turi–Plotkin's monad/comonad refinement are `[N4-gsos]`. -/
structure DistLaw (S : Signature.{u, u}) (B : PFunctor.{u, u}) where
  /-- The component at `X`. -/
  app : ∀ {X : Type u}, S.toPFunctor.Obj (B.Obj X) → B.Obj (S.toPFunctor.Obj X)
  /-- Naturality: the components commute with the functor actions. -/
  natural : ∀ {X Y : Type u} (f : X → Y) (s : S.toPFunctor.Obj (B.Obj X)),
    B.map (S.toPFunctor.map f) (app s) = app (S.toPFunctor.map (B.map f) s)

variable {S : Signature.{u, u}} {B : PFunctor.{u, u}}

/-- **`Bialgebra l`** — a λ-bialgebra for the law `l`: ONE carrier `X` with a `Σ`-algebra
(curried, so `fold` applies) and a `B`-coalgebra, glued by the pentagon
`coalg ∘ alg = B alg ∘ λ ∘ Σ coalg`. -/
structure Bialgebra (l : DistLaw S B) where
  /-- The carrier. -/
  X : Type u
  /-- The `Σ`-algebra (one operation per shape). -/
  alg : Alg S X
  /-- The `B`-coalgebra (the one-step behaviour). -/
  coalg : X → B.Obj X
  /-- The pentagon: observing a built node = the law applied to the observed children. -/
  pentagon : ∀ (a : S.Op) (k : S.ar a → X),
    coalg (alg a k)
      = B.map (fun x : S.toPFunctor.Obj X => alg x.1 x.2) (l.app ⟨a, fun i => coalg (k i)⟩)

/-- A bialgebra homomorphism: simultaneously a `Σ`-algebra hom (the `IsFoldHom` shape) and a
`B`-coalgebra hom. -/
def IsBialgebraHom {l : DistLaw S B} (A₁ A₂ : Bialgebra l) (f : A₁.X → A₂.X) : Prop :=
  (∀ (a : S.Op) (k : S.ar a → A₁.X), f (A₁.alg a k) = A₂.alg a fun i => f (k i))
    ∧ ∀ x, A₂.coalg (f x) = B.map f (A₁.coalg x)

/-! ## §2. The two canonical models — operational by `fold`, denotational by `corec`. -/

/-- The initial algebra's structure map, uncurried: a `Σ`-node of terms IS a term. -/
def node (x : S.toPFunctor.Obj (Term S)) : Term S := WType.mk x.1 x.2

/-- The operational algebra: read a node's children's behaviours, distribute, rebuild. -/
def opAlg (l : DistLaw S B) : Alg S (B.Obj (Term S)) :=
  fun a k => B.map node (l.app ⟨a, k⟩)

/-- **`opModel l`** — the OPERATIONAL model: the `B`-coalgebra on closed terms, a `fold`
(the small-step machine on syntax, derived from the law by the N3 engine). -/
def opModel (l : DistLaw S B) : Term S → B.Obj (Term S) := fold (opAlg l)

/-- The denotational step: unfold the children's behaviours one step, then distribute. -/
def denStep (l : DistLaw S B) : S.toPFunctor.Obj (M B) → B.Obj (S.toPFunctor.Obj (M B)) :=
  fun s => l.app (S.toPFunctor.map M.dest s)

/-- **`denModel l`** — the DENOTATIONAL model: the `Σ`-algebra on behaviours `νB = M B`, a
`corec` (each shape interpreted as an operation on behaviours). -/
def denModel (l : DistLaw S B) : Alg S (M B) := fun a k => M.corec (denStep l) ⟨a, k⟩

/-- The initial λ-bialgebra: closed terms with `termAlg` and `opModel`. Its pentagon is
definitional (`fold_mk`). -/
def initialBialgebra (l : DistLaw S B) : Bialgebra l where
  X := Term S
  alg := termAlg S
  coalg := opModel l
  pentagon := fun _ _ => rfl

/-- The final λ-bialgebra: behaviours with `denModel` and `M.dest`. Its pentagon is
`M.dest_corec`. -/
def finalBialgebra (l : DistLaw S B) : Bialgebra l where
  X := M B
  alg := denModel l
  coalg := M.dest
  pentagon := fun a k => by
    show M.dest (M.corec (denStep l) ⟨a, k⟩) = _
    rw [M.dest_corec]
    rfl

/-! ## §3. N4a — adequacy: operational = denotational, uniquely. -/

/-- The one computation: the fold of the denotational algebra is a `B`-coalgebra
homomorphism from `opModel` to `M.dest`. Proved by the ONE structural induction of this
file, through `M.dest_corec`, naturality, and the two functor laws. -/
theorem dest_fold_denModel (l : DistLaw S B) (t : Term S) :
    M.dest (fold (denModel l) t) = B.map (fold (denModel l)) (opModel l t) := by
  induction t with
  | mk a k ih =>
    -- one `dest_corec` step, with the induction hypothesis folded into the children
    have e1 : M.dest (fold (denModel l) (WType.mk a k))
        = B.map (M.corec (denStep l))
            (l.app ⟨a, fun i => B.map (fold (denModel l)) (opModel l (k i))⟩) :=
      (M.dest_corec (denStep l) ⟨a, fun i => fold (denModel l) (k i)⟩).trans
        (congrArg (fun F => B.map (M.corec (denStep l)) (l.app ⟨a, F⟩)) (funext ih))
    -- naturality of the law, read right-to-left
    have e3 : l.app ⟨a, fun i => B.map (fold (denModel l)) (opModel l (k i))⟩
        = B.map (S.toPFunctor.map (fold (denModel l)))
            (l.app ⟨a, fun i => opModel l (k i)⟩) :=
      (l.natural (fold (denModel l)) ⟨a, fun i => opModel l (k i)⟩).symm
    rw [e1, e3, PFunctor.map_map]
    show _ = B.map (fold (denModel l)) (B.map node (l.app ⟨a, fun i => opModel l (k i)⟩))
    rw [PFunctor.map_map]
    exact congrArg (fun g => B.map g (l.app ⟨a, fun i => opModel l (k i)⟩))
      (funext fun x => by rcases x with ⟨a', k'⟩; rfl)

/-- **[N4a] ADEQUACY — the operational and denotational readings are one map, uniquely.**
`fold (denModel l)` (the compositional reading: interpret each shape on behaviours) equals
`M.corec (opModel l)` (the coinductive reading: unfold the small-step machine), and ANY
bialgebra homomorphism from the initial to the final model is that map — unique as a
`Σ`-hom by `fold_unique` (N3's one induction) and as a `B`-hom by `M.corec_unique`. -/
theorem N4_adequacy (l : DistLaw S B) :
    fold (denModel l) = M.corec (opModel l)
    ∧ ∀ f : Term S → M B, IsBialgebraHom (initialBialgebra l) (finalBialgebra l) f →
        f = fold (denModel l) ∧ f = M.corec (opModel l) :=
  ⟨M.corec_unique (opModel l) (fold (denModel l)) (dest_fold_denModel l),
   fun f ⟨hS, hB⟩ => ⟨fold_unique (denModel l) f hS, M.corec_unique (opModel l) f hB⟩⟩

/-! ## §4. N4b — behavioural equivalence is a congruence. -/

/-- **`Bisim l t u`** — closed terms are behaviourally equivalent when they denote the same
point of the final coalgebra `M B` (the kernel of the final map). -/
def Bisim (l : DistLaw S B) (t u : Term S) : Prop :=
  M.corec (opModel l) t = M.corec (opModel l) u

theorem Bisim.refl (l : DistLaw S B) (t : Term S) : Bisim l t t := rfl

/-- **[N4b] CONGRUENCE — bisimilar arguments give a bisimilar node, at EVERY shape.** A
three-line corollary of adequacy: the final map is a `Σ`-hom, so it only sees the
arguments' behaviours. At a joint shape this is "a turn over observationally-equal cells is
observationally equal". -/
theorem N4_congruence (l : DistLaw S B) (a : S.Op) (f g : S.ar a → Term S)
    (h : ∀ i, Bisim l (f i) (g i)) : Bisim l (.mk a f) (.mk a g) := by
  have e := (N4_adequacy l).1
  show M.corec (opModel l) (.mk a f) = M.corec (opModel l) (.mk a g)
  rw [← e, fold_mk, fold_mk]
  exact congrArg (denModel l a) (funext fun i => by
    have hi := h i
    unfold Bisim at hi
    rw [← e] at hi
    exact hi)

/-! ## §5. The toy behaviour functor — `Option`, as a `PFunctor` — and `FailClosed`.

Refusal is a VALUE of the behaviour (`Beh.refuse`, no children), so "a leg refuses" is a
pattern match, not a negative premise. `optionPEquiv` records that this IS `Option`. -/

/-- One-step behaviour shapes: refuse (no successor) or step (one successor). -/
inductive Beh
  | refuse
  | step
  deriving DecidableEq, Repr, Inhabited

/-- `Option` as a polynomial functor: `optionP.Obj X ≃ Option X`. -/
def optionP : PFunctor.{0, 0} :=
  ⟨Beh, fun b => match b with
    | .refuse => Empty
    | .step => Unit⟩

/-- The refusing behaviour (`none`). -/
def refuseB {X : Type} : optionP.Obj X := ⟨Beh.refuse, nofun⟩

/-- The stepping behaviour (`some x`). -/
def stepB {X : Type} (x : X) : optionP.Obj X := ⟨Beh.step, fun _ => x⟩

theorem map_refuseB {X Y : Type} (g : X → Y) : optionP.map g refuseB = refuseB :=
  congrArg (Sigma.mk Beh.refuse) (funext fun e => nomatch e)

theorem map_stepB {X Y : Type} (g : X → Y) (x : X) : optionP.map g (stepB x) = stepB (g x) :=
  rfl

/-- The toy `B` is `Option` on the nose. -/
def optionPEquiv {X : Type} : optionP.Obj X ≃ Option X where
  toFun s := match s with
    | ⟨Beh.refuse, _⟩ => none
    | ⟨Beh.step, f⟩ => some (f ())
  invFun o := match o with
    | none => refuseB
    | some x => stepB x
  left_inv s := by
    rcases s with ⟨_ | _, k⟩
    · exact congrArg (Sigma.mk Beh.refuse) (funext fun e => nomatch e)
    · exact congrArg (Sigma.mk Beh.step) (funext fun u => by cases u; rfl)
  right_inv o := by cases o <;> rfl

/-- **`FailClosed l`** — a PROPERTY of a law, not an axiom of laws: whenever some argument
refuses, the node refuses. (`docs/N4-DISTRIBUTIVE-LAW.md` §3.4: absorption is a choice of
`λ`; the Moore-functor form with a designated refusal observation is
`[N4-hyperedge-instance]`.) -/
def FailClosed {S : Signature.{0, 0}} (l : DistLaw S optionP) : Prop :=
  ∀ {X : Type} (a : S.Op) (k : S.ar a → optionP.Obj X),
    (∃ i, (k i).1 = Beh.refuse) → (l.app ⟨a, k⟩).1 = Beh.refuse

/-! ## §6. The toy signature — two leaves, the unary `tick`, the binary `join`. -/

/-- Toy shapes: a refusing cell, an always-admitting cell, the sequential unary node, and
the binary joint node. -/
inductive ToyOp
  | stop
  | go
  | tick
  | join
  deriving DecidableEq, Repr

/-- The toy signature: `stop`/`go` are leaves, `tick` is unary, `join` is binary. -/
def ToySig : Signature.{0, 0} where
  Op := ToyOp
  ar := fun a => match a with
    | .stop => Empty
    | .go => Empty
    | .tick => Unit
    | .join => Bool

/-- Node vocabulary (as `Σ X` elements), used both by the laws and to build terms. -/
def stopNode {X : Type} : ToySig.toPFunctor.Obj X := ⟨ToyOp.stop, nofun⟩
def goNode {X : Type} : ToySig.toPFunctor.Obj X := ⟨ToyOp.go, nofun⟩
def tickNode {X : Type} (x : X) : ToySig.toPFunctor.Obj X := ⟨ToyOp.tick, fun _ => x⟩
def joinNode {X : Type} (x y : X) : ToySig.toPFunctor.Obj X :=
  ⟨ToyOp.join, fun b => bif b then y else x⟩

theorem map_goNode {X Y : Type} (f : X → Y) : ToySig.toPFunctor.map f goNode = goNode :=
  congrArg (Sigma.mk ToyOp.go) (funext fun e => nomatch e)

theorem map_tickNode {X Y : Type} (f : X → Y) (x : X) :
    ToySig.toPFunctor.map f (tickNode x) = tickNode (f x) :=
  rfl

theorem map_joinNode {X Y : Type} (f : X → Y) (x y : X) :
    ToySig.toPFunctor.map f (joinNode x y) = joinNode (f x) (f y) :=
  congrArg (Sigma.mk ToyOp.join) (funext fun b => by cases b <;> rfl)

/-- Closed toy terms, built by the initial algebra's structure map from the node vocabulary. -/
def stopT : Term ToySig := node stopNode
def goT : Term ToySig := node goNode
def tickT (t : Term ToySig) : Term ToySig := node (tickNode t)
def joinT (l r : Term ToySig) : Term ToySig := node (joinNode l r)

/-! ### The STRICT (fail-closed) law — `Option`'s traversal of the container. -/

/-- The joint component, strict: both legs step, or the node refuses. -/
def joinStrict {X : Type} : optionP.Obj X → optionP.Obj X → optionP.Obj (ToySig.toPFunctor.Obj X)
  | ⟨Beh.step, f⟩, ⟨Beh.step, g⟩ => stepB (joinNode (f ()) (g ()))
  | _, _ => refuseB

theorem joinStrict_natural {X Y : Type} (f : X → Y) (x y : optionP.Obj X) :
    optionP.map (ToySig.toPFunctor.map f) (joinStrict x y)
      = joinStrict (optionP.map f x) (optionP.map f y) := by
  rcases x with ⟨_ | _, kx⟩ <;> rcases y with ⟨_ | _, ky⟩
  · exact map_refuseB _
  · exact map_refuseB _
  · exact map_refuseB _
  · show optionP.map (ToySig.toPFunctor.map f) (stepB (joinNode (kx ()) (ky ())))
        = stepB (joinNode (f (kx ())) (f (ky ())))
    rw [map_stepB, map_joinNode]

/-- **`strictLaw`** — the fail-closed distributive law: leaves behave as declared, `tick`
LIFTS its child's behaviour (`Option.map`), `join` is the strict traversal. -/
def strictLaw : DistLaw ToySig optionP where
  app := fun s => match s with
    | ⟨ToyOp.stop, _⟩ => refuseB
    | ⟨ToyOp.go, _⟩ => stepB goNode
    | ⟨ToyOp.tick, k⟩ => optionP.map tickNode (k ())
    | ⟨ToyOp.join, k⟩ => joinStrict (k false) (k true)
  natural := by
    intro X Y f s
    rcases s with ⟨_ | _ | _ | _, k⟩
    · exact map_refuseB _
    · show optionP.map (ToySig.toPFunctor.map f) (stepB goNode) = stepB goNode
      rw [map_stepB, map_goNode]
    · show optionP.map (ToySig.toPFunctor.map f) (optionP.map tickNode (k ()))
          = optionP.map tickNode (optionP.map f (k ()))
      rw [PFunctor.map_map, PFunctor.map_map]
      exact congrArg (fun g => optionP.map g (k ())) (funext fun x => map_tickNode f x)
    · exact joinStrict_natural f (k false) (k true)

/-! ### The FAIL-OPEN law — lawful, and wrong. -/

/-- The joint component, fail-open: a refused leg is DROPPED and the node commits with the
stepping leg alone (as a `tick`). The half-committed transfer. -/
def joinOpen {X : Type} : optionP.Obj X → optionP.Obj X → optionP.Obj (ToySig.toPFunctor.Obj X)
  | ⟨Beh.step, f⟩, ⟨Beh.step, g⟩ => stepB (joinNode (f ()) (g ()))
  | ⟨Beh.step, f⟩, ⟨Beh.refuse, _⟩ => stepB (tickNode (f ()))
  | ⟨Beh.refuse, _⟩, ⟨Beh.step, g⟩ => stepB (tickNode (g ()))
  | ⟨Beh.refuse, _⟩, ⟨Beh.refuse, _⟩ => refuseB

theorem joinOpen_natural {X Y : Type} (f : X → Y) (x y : optionP.Obj X) :
    optionP.map (ToySig.toPFunctor.map f) (joinOpen x y)
      = joinOpen (optionP.map f x) (optionP.map f y) := by
  rcases x with ⟨_ | _, kx⟩ <;> rcases y with ⟨_ | _, ky⟩
  · exact map_refuseB _
  · rfl
  · rfl
  · show optionP.map (ToySig.toPFunctor.map f) (stepB (joinNode (kx ()) (ky ())))
        = stepB (joinNode (f (kx ())) (f (ky ())))
    rw [map_stepB, map_joinNode]

/-- **`openLaw`** — the fail-open distributive law. It satisfies naturality: the axioms of
distributive laws do NOT rule it out. -/
def openLaw : DistLaw ToySig optionP where
  app := fun s => match s with
    | ⟨ToyOp.stop, _⟩ => refuseB
    | ⟨ToyOp.go, _⟩ => stepB goNode
    | ⟨ToyOp.tick, k⟩ => optionP.map tickNode (k ())
    | ⟨ToyOp.join, k⟩ => joinOpen (k false) (k true)
  natural := by
    intro X Y f s
    rcases s with ⟨_ | _ | _ | _, k⟩
    · exact map_refuseB _
    · show optionP.map (ToySig.toPFunctor.map f) (stepB goNode) = stepB goNode
      rw [map_stepB, map_goNode]
    · show optionP.map (ToySig.toPFunctor.map f) (optionP.map tickNode (k ()))
          = optionP.map tickNode (optionP.map f (k ()))
      rw [PFunctor.map_map, PFunctor.map_map]
      exact congrArg (fun g => optionP.map g (k ())) (funext fun x => map_tickNode f x)
    · exact joinOpen_natural f (k false) (k true)

/-! ## §7. Keystones, BUILT (the audit lesson: exhibit, never assert). -/

/-! ### satisfiable — the strict law is a `DistLaw`; adequacy and congruence FIRE on it. -/

/-- Adequacy, instantiated: the two readings coincide on a concrete joint term. -/
theorem adequacy_fires :
    fold (denModel strictLaw) (joinT goT goT) = M.corec (opModel strictLaw) (joinT goT goT) :=
  congrFun (N4_adequacy strictLaw).1 _

/-- Operational value: the joint turn of two admitting cells COMMITS, to the joint turn of
their successors. -/
theorem strict_joint_commits : opModel strictLaw (joinT goT goT) = stepB (joinT goT goT) :=
  rfl

/-- Operational value: the joint turn with a refusing participant REFUSES. -/
theorem strict_joint_refuses : (opModel strictLaw (joinT goT stopT)).1 = Beh.refuse :=
  rfl

/-- Denotational value, through adequacy: the behaviour of that term refuses at its first
observation. -/
theorem den_joint_refuses :
    (M.dest (fold (denModel strictLaw) (joinT goT stopT))).1 = Beh.refuse := by
  rw [(N4_adequacy strictLaw).1, M.dest_corec, fst_map]
  rfl

/-- **The collapse at a unary shape, as a theorem**: the strict law's component at `tick` is
`Option.map` of the node — the whole of "N4 at the sequential fragment". -/
theorem sequential_law_is_option_map {X : Type} (k : Unit → optionP.Obj X) :
    strictLaw.app ⟨ToyOp.tick, k⟩ = optionP.map tickNode (k ()) :=
  rfl

theorem opModel_tickT (t : Term ToySig) :
    opModel strictLaw (tickT t) = optionP.map tickT (opModel strictLaw t) := by
  show optionP.map node (optionP.map tickNode (opModel strictLaw t)) = _
  rw [PFunctor.map_map]
  rfl

/-- **The unary node is INVISIBLE to behaviour** (`M.bisim`): `tick t` and `t` denote the same
point of `νB`. The sequential fragment contributes nothing to `Bisim`. -/
theorem tick_invisible (t : Term ToySig) : Bisim strictLaw (tickT t) t := by
  refine M.bisim (fun x y => ∃ u : Term ToySig,
      x = M.corec (opModel strictLaw) (tickT u) ∧ y = M.corec (opModel strictLaw) u)
    ?_ _ _ ⟨t, rfl, rfl⟩
  rintro x y ⟨u, rfl, rfl⟩
  rw [M.dest_corec, M.dest_corec, opModel_tickT]
  generalize opModel strictLaw u = s
  rcases s with ⟨b, k⟩
  exact ⟨b, _, _, rfl, rfl, fun i => ⟨k i, rfl, rfl⟩⟩

/-- **Congruence FIRES at the binary shape**: a join over a bisimilar-but-distinct pair of
cells is bisimilar to the join over the originals. -/
theorem congruence_fires : Bisim strictLaw (joinT (tickT goT) goT) (joinT goT goT) :=
  N4_congruence strictLaw ToyOp.join
    (fun b => bif b then goT else tickT goT) (fun b => bif b then goT else goT)
    (fun b => by
      cases b
      · exact tick_invisible goT
      · exact Bisim.refl _ _)

/-- Node-count reading — to witness that the congruence pair is syntactically distinct. -/
def sizeAlg : Alg ToySig ℕ := fun a => match a with
  | .stop => fun _ => 1
  | .go => fun _ => 1
  | .tick => fun k => k () + 1
  | .join => fun k => k false + k true + 1

/-- The pair `congruence_fires` relates is NOT syntactically equal (sizes 4 ≠ 3): the
congruence is about behaviour, not about equal terms. -/
theorem congruence_pair_distinct : joinT (tickT goT) goT ≠ joinT goT goT := fun h =>
  absurd (congrArg (fold sizeAlg) h) (by decide)

/-! ### teeth — the fail-open law is ALSO a `DistLaw`, and it is wrong. -/

/-- The strict law is fail-closed. -/
theorem strictLaw_failClosed : FailClosed strictLaw := by
  intro X a k hk
  obtain ⟨i, hi⟩ := hk
  cases a with
  | stop => rfl
  | go => cases i
  | tick =>
    show (optionP.map tickNode (k ())).1 = Beh.refuse
    rw [fst_map]
    cases i
    exact hi
  | join =>
    show (joinStrict (k false) (k true)).1 = Beh.refuse
    rcases hf : k false with ⟨_ | _, kf⟩ <;> rcases ht : k true with ⟨_ | _, kt⟩
    · rfl
    · rfl
    · rfl
    · exfalso
      cases i
      · rw [hf] at hi
        exact Beh.noConfusion hi
      · rw [ht] at hi
        exact Beh.noConfusion hi

/-- **TEETH — the fail-open law violates `FailClosed`**: at a join whose second leg refuses,
`openLaw` observes a STEP. The distributive-law axioms did not stop it; only the Prop does. -/
theorem openLaw_not_failClosed : ¬ FailClosed openLaw := by
  intro h
  have hrefuse := h (X := Unit) ToyOp.join (fun b => bif b then refuseB else stepB ()) ⟨true, rfl⟩
  have hstep : (openLaw.app (X := Unit)
      ⟨ToyOp.join, fun b => bif b then refuseB else stepB ()⟩).1 = Beh.step := rfl
  exact Beh.noConfusion (hstep.symm.trans hrefuse)

/-- **The concrete term**: under `openLaw` the joint turn `join go stop` — one admitting
participant, one refusing — COMMITS, proceeding with the admitting leg alone. This is the
half-committed transfer that `Kernel/Turn.lean`'s `balanced` and
`MultiCellHyperedge.no_commit_of_nonzero_balance` exist to refuse. -/
theorem open_joint_commits : opModel openLaw (joinT goT stopT) = stepB (tickT goT) :=
  rfl

/-- The two laws are genuinely different laws (so `∀ l` in N4a/N4b is over a domain with at
least two elements, and `FailClosed` genuinely separates them). -/
theorem laws_differ : strictLaw ≠ openLaw := fun h =>
  let probe : ToySig.toPFunctor.Obj (optionP.Obj Unit) :=
    ⟨ToyOp.join, fun b => bif b then refuseB else stepB ()⟩
  have hstrict : (strictLaw.app probe).1 = Beh.refuse := rfl
  have hopen : (openLaw.app probe).1 = Beh.step := rfl
  Beh.noConfusion (hstrict.symm.trans
    ((congrArg (fun l : DistLaw ToySig optionP => (l.app probe).1) h).trans hopen))

/-! ### premise-inhabitation — the toy `Σ` is a `Signature`, the toy `B` is `Option`, both
universal objects are inhabited, and the law type has two distinct inhabitants. -/

example : Signature := ToySig
example : PFunctor := optionP
example {X : Type} : optionP.Obj X ≃ Option X := optionPEquiv

/-- Closed terms exist (a leaf shape with empty arity). -/
theorem terms_inhabited : Nonempty (Term ToySig) := ⟨stopT⟩

/-- The always-refusing behaviour — `νB` is inhabited. -/
def deadBeh : M optionP := M.corec (fun _ : Unit => refuseB) ()

theorem behaviours_inhabited : Nonempty (M optionP) := ⟨deadBeh⟩

/-- Both laws are `DistLaw`s: the domain of `N4_adequacy`/`N4_congruence` at this signature
has (at least) two elements, one fail-closed and one not. -/
theorem laws_inhabited : ∃ l₁ l₂ : DistLaw ToySig optionP,
    l₁ ≠ l₂ ∧ FailClosed l₁ ∧ ¬ FailClosed l₂ :=
  ⟨strictLaw, openLaw, laws_differ, strictLaw_failClosed, openLaw_not_failClosed⟩

/-! ## §8. Axiom pins — exact-output, self-verifying (the build fails on drift).

The abstract theorems ride `M.corec_unique`/`M.bisim` (mathlib's `M` uses classical choice
in its bisimulation-to-equality step) plus `fold_unique`'s `funext`; the toy teeth are
`rfl`/`noConfusion` over definitions whose naturality proofs used `funext`. All inside the
`{propext, Classical.choice, Quot.sound}` ceiling; no `sorryAx`. -/

/-- info: 'Minidregg.Compiler.DistributiveLaw.N4_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms N4_adequacy

/-- info: 'Minidregg.Compiler.DistributiveLaw.N4_congruence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms N4_congruence

/-- info: 'Minidregg.Compiler.DistributiveLaw.tick_invisible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tick_invisible

/-- info: 'Minidregg.Compiler.DistributiveLaw.congruence_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms congruence_fires

/-- info: 'Minidregg.Compiler.DistributiveLaw.strictLaw_failClosed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms strictLaw_failClosed

/-- info: 'Minidregg.Compiler.DistributiveLaw.openLaw_not_failClosed' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms openLaw_not_failClosed

/-- info: 'Minidregg.Compiler.DistributiveLaw.open_joint_commits' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms open_joint_commits

/-- info: 'Minidregg.Compiler.DistributiveLaw.laws_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms laws_inhabited

end Minidregg.Compiler.DistributiveLaw
