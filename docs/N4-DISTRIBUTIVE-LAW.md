# N4 — the kernel as a distributive law (Turi–Plotkin), stated for THIS tree

*Design, 2026-09-05, statement-first — no Lean tonight. In the style of
`docs/N2-HYPEREDGE-LIMIT.md`: fix the category and the statement before the Lean, name the
keystone fields, name the risk. Every claim about the tree cites `absolute path:lines` and was
read tonight unless marked **inferred** or **from memory** (literature). Mathlib is the pin
`1c2b90b` (`/Users/ember/dev/minidregg/lake-manifest.json`, `"rev": "1c2b90b13009…"`; also
`/Users/ember/dev/minidregg/Compiler/Signature.lean:16`).*

## 0. What N4 asks, and what the tree actually holds

KERNEL-NECESSITY §N4 (`/Users/ember/dev/minidregg/docs/KERNEL-NECESSITY.md:101-122`): effects
form a syntax functor Σ (N3, initial side); living cells form a behaviour functor B with final
coalgebra νB; the kernel "is exactly a distributive law λ : Σ∘B ⇒ B∘Σ"; Turi–Plotkin then gives
bisimilarity-is-a-congruence, operational = denotational, uniqueness. The named risk (`:117-122`):
does the fail-closed `Option` gate fit the GSOS format?

What the tree holds tonight:

- **Σ side — held, whole.** `/Users/ember/dev/minidregg/Compiler/Signature.lean`: `Signature` =
  mathlib `PFunctor` under kernel names (`:55-71`), `Term S = WType S.ar` (`:78-83`),
  `fold = WType.elim` (`:110-116`), `fold_unique` (`:165-171`), `agree_by_initiality`
  (`:183-185`), the N3-converse (`:423-474`). `/Users/ember/dev/minidregg/Effects/EffectSpec.lean`
  derives `sig`/`Prog`/`derivedExecutor`/`derivedDescriptor`/`derive` from one declaration
  (`:101-132, 186, 255-261`).
- **B side — nothing.** No coalgebra, no `corec`, no bisimulation, no `nuF` exists in any `.lean`
  file (grep over the tree excluding `.lake`, tonight: zero hits; the twin audit agrees,
  `/Users/ember/dev/minidregg/docs/KERNEL-TWIN-AUDIT.md:72-77`). ATLAS lists `nuF = List Adm → Obs`
  as a held breadstuffs artifact (`/Users/ember/dev/minidregg/ATLAS.md:140`) and as `Theory/`
  content (`:245-248`); it was never ported.
- **Mathlib at the pin has NO distributive law and NO bialgebra.** Confirmed: `grep -rniE
  "DistributiveLaw|distributive law|Bialgebra" Mathlib/CategoryTheory/` is empty;
  `Mathlib/CategoryTheory/Distributive/` is distributive *categories* (products over coproducts —
  `Distributive/Cartesian.lean:12-20`), unrelated; `Mathlib/RingTheory/Bialgebra/` is Hopf-algebra
  bialgebras, unrelated. What IS there: `Endofunctor.Algebra`/`Coalgebra` with `Initial`/`Terminal`
  (`Mathlib/CategoryTheory/Endofunctor/Algebra.lean:39, 227, 196-222, 387-414`), `Monad`/`Comonad`
  (`Mathlib/CategoryTheory/Monad/Basic.lean:40, 65`), Eilenberg–Moore
  (`Mathlib/CategoryTheory/Monad/Algebra.lean:41`), and — the load-bearing pieces —
  `PFunctor.W` (`Mathlib/Data/PFunctor/Univariate/Basic.lean:84-112`), `PFunctor.comp` (`:148`),
  and `PFunctor.M` with `M.corec` (`Mathlib/Data/PFunctor/Univariate/M.lean:175`), `M.dest` (`:216`),
  `dest_corec` (`:566`), `M.bisim` (`:569`), `M.corec_unique` (`:609`), `M.inhabited [Inhabited F.A]`
  (`:159`).
- **The twin caveat.** Two state/turn models coexist — (A) `KernelState`/`Gate` and (B) the typed
  cell (`Theory/CellState` + `Kernel/MultiCellHyperedge`) — and the audit proposes (B) survives
  (`KERNEL-TWIN-AUDIT.md:712-736`; D-0002 already says so,
  `/Users/ember/dev/minidregg/docs/decisions/D-0002-canonical-hyperedge-kernel.md:3-16`). N4 is
  therefore stated below over an abstract polynomial Σ and an abstract polynomial B, with EITHER
  gate as an instance (§2.4 shows both twins already have the same refusal shape).

## 1. Σ, precisely

**`Signature` in general is Σ's home; `EffectSpec.sig` is the sequential instance.** A
`Signature` is `⟨Op, ar⟩` = `PFunctor` (`Signature.lean:55-63`), i.e. the endofunctor on `Type`
`Σ X = Σ (s : Op), (ar s → X)` (`PFunctor.Obj`, `Basic.lean:45`). Its free term algebra is the
W-type `Term S = WType S.ar = S.toPFunctor.W` (`Signature.lean:78-83`) — the *closed* terms, the
initial Σ-algebra (`fold_unique`, `:165-171`). The free MONAD `T_Σ X = μY. X + Σ Y` is not in the
tree and not in mathlib; `Term S = T_Σ ∅`.

**`EffectSpec.sig`** (`EffectSpec.lean:101-105`): `Op := Option E.Op`, `ar none = Empty`,
`ar (some _) = Unit`. As an endofunctor:

    Σ_E X  =  1 + Op × X          (one leaf `done`, one UNARY node per op)
    T_Σ_E X ≅ List Op × Option X  (op-sequences ending in `done` or in a variable)   [inferred]
    Prog E = Term sig ≅ List Op   (closed terms = the free monoid on Op)

The `derivedDescriptor : Prog E → List E.Op` (`EffectSpec.lean:177-186`) is that isomorphism read
off as a fold; `descriptor_faithful` (`:215-218`) says it loses nothing.

*What the sequential simplification buys:* closed terms exist (the leaf), executor and descriptor
are one-shape folds, `agree_by_initiality` fires at every reading (`:163-172, 206-218`), and the
kernel's `move` is derived end-to-end (`:286-353`). *What it costs for N4:* a unary signature has
**no operator that combines two cells or two programs**. Turi–Plotkin's content — "bisimilarity is
a congruence" — quantifies over operators with ≥ 2 recursive arguments; over `Σ_E` every congruence
statement is about a single argument and collapses to functoriality (§3.1, §6). The joint turn
(`Hyperedge`, `/Users/ember/dev/minidregg/Kernel/Turn.lean:38-55`, `ι`-ary with `Fintype ι`) is
exactly the missing branching node. So: **Σ for N4 = `Signature`, instantiated at a signature that
contains `EffectSpec.sig`'s prefix nodes AND an `ι`-ary joint node.** N3 needs only the former; N4
is empty without the latter.

## 2. B, precisely — the candidates, their final coalgebras, and the gate as an instance

Three shapes, each a polynomial functor (so `PFunctor.M` is νB for free — mathlib's `M` is the
final coalgebra: `dest_corec` + `corec_unique`, `M.lean:566, 609`, with `M.bisim`, `:569`).

**(a) `B X = Option X`** — "step or refuse", the request forgotten. PFunctor
`⟨Bool, fun b => cond b Unit Empty⟩` with `Obj X ≃ Option X`. νB ≅ ℕ∞ (the conaturals: a
behaviour is "how many steps until refusal, possibly never") — standard, **not in mathlib** at the
pin as a theorem about `M` (inferred). `Gate.admit` gives an `Option`-coalgebra on `KernelState`
only after FIXING `v` and `t`: `fun k => admit k v t` (`Gate.lean:313-316`). Observational
equivalence then says "the same fixed request can be re-admitted the same number of times" —
nearly meaningless for a kernel. *Verdict: honest, polynomial, degenerate.*

**(b) `B X = Req → Option X`** — deterministic, partial, labelled. PFunctor
`⟨Req → Bool, fun f => {r // f r = true}⟩` (shape = which requests are admitted; arity = the
admitted ones). νB ≅ prefix-closed languages over `Req` (the final deterministic partial
automaton; **from memory**, Rutten's universal coalgebra). `Gate.admit` IS such a coalgebra:
`c k := fun t => admit k (gatedVerb fp) t` with `Req := TurnReq W` (`Gate.lean:183-196, 305-316`).
Equivalence = same admitted-request language. *Verdict: honest and minimal; but it throws away what
happens AFTER a refusal.*

**(c) `B X = Req → Obs × X`** — a Moore machine; refusal is an OBSERVATION and the cell
stutters. PFunctor `⟨Req → Obs, fun _ => Req⟩` — the cleanest encoding of the three (constant
arity). νB ≅ `List Req → Obs` (final Moore coalgebra; **from memory**, Rutten 2000 Thm.
"O^{A*}") — which is EXACTLY ATLAS item 15's `nuF = List Adm → Obs` (`ATLAS.md:140`). Breadstuffs'
"100 constructive lines, no Adámek" is consistent with a direct `corec`-style construction of
that function space (inferred). `Gate.admit` is such a coalgebra by folding refusal into `Obs`:

    c k r := match admit k (gatedVerb fp) r with
             | some k' => (Obs.ok ⟨…receipt…⟩, k')      -- admit_check_eq_use: gateOK k r ∧ k' = r.act.apply k
             | none    => (Obs.refused, k)               -- admit_fail_closed: the cell is UNCHANGED

`Obs.ok` can carry precisely what `admit_check_eq_use` certifies (`Gate.lean:382-386`) — the OB-3
receipt — and `Obs` is the "observation word with a faithfulness theorem" the twin audit says the
(B) side lacks (`KERNEL-TWIN-AUDIT.md:745-749`). Choosing `Obs` and closing that gap are one
decision.

**(c′) `B X = Req → Obs × Option X`** — refuse-or-step-with-observation. Collapses to (c) once
refusal is a stutter (`none ↦ (refused, self)`). The only semantic difference: is a refused cell
*dead* (no further requests) or *alive* (retry)? The tree is unambiguous: `admit` is a pure
function of `k` (`Gate.lean:313-316`), a refused `k` accepts later requests; and on the (B) side
"rejected ⇒ post = pre" is stated four times (`Theory/CanonicalTransition.lean:182-186`
`Decision.logicalPost`; `Theory/CellState.lean:355-358` `ApplyOutcome.post`;
`Kernel/MultiCellHyperedge.lean:369-375` `Admission.rejected_atomic`;
`Kernel/DeclaredHyperedge.lean:529-536` `execute_rejected_unchanged`, quoted in
`KERNEL-TWIN-AUDIT.md:213-221`). **The `Option` in `admit` is the partiality of a MAP, not the
termination of a BEHAVIOUR.** The behaviour functor is total.

**2.4 The twin-independence of B.** Both twins already refuse the same way: (A) as `Option`
(`Gate.lean:313-316`), (B) as `Except Reject`/`Decision.rejected`/`Outcome.rejected` with
post = pre (`MultiCellHyperedge.lean:343-355`; `CanonicalTransition.lean:171-179`;
`Theory/ReactiveCellTransition.lean:61-83`). Under (c) both are Moore coalgebras with
`Obs ⊇ Reject`; the abstract statement never sees which. One N3-flavoured constraint carries over:
the LABEL alphabet `Req` must be syntactic (countable codes), for the reason `OpaqueSig` gives
(`Signature.lean:289-331`) — a trace/receipt is data only if its labels are. `Verb W` is NOT such
an alphabet (it carries a closure `admission : KernelState → TurnReq W → Bool`, `Gate.lean:297-302`);
fixing `v := gatedVerb fp` (`:305-306`) and labelling by `Footprint × TurnReq W` is syntactic iff
`W` is (`PortalWit` is, `:479-482`). νB itself is a function space and need not be syntactic — it
is the semantic object, as `List Adm → Obs` always was.

**Decision for the statement: B = (c), the Moore functor `Req → Obs × X`, with refusal in `Obs`
and a stutter successor.** `Option` disappears from B entirely; it reappears in §3 as the
STRICTNESS of the distributive law at the joint node.

## 3. The distributive law, stated — and where fail-closed actually lives

Three layers of "distributive law", from memory (Turi–Plotkin 1997; Klin 2011 §3–4;
Lenisa–Power–Watanabe 2000 for the GSOS bijection), each checked by hand on the concrete shape.

**3.1 Plain endofunctor law λ : Σ∘B ⇒ B∘Σ (what KERNEL-NECESSITY literally writes).** Its ONLY
axiom is naturality: `B.map (Σ.map f) ∘ λ_X = λ_Y ∘ Σ.map (B.map f)`. There are no unit or
multiplication squares because Σ and B are bare functors. Component for `Σ_E` over `Option`:

    λ_X : 1 + Op × Option X  →  Option (1 + Op × X)
    λ (inl ())          = some (inl ())          -- `done` lifts
    λ (inr (o, none))   = none                   -- a refused continuation refuses the node   ← fail-closed
    λ (inr (o, some x)) = some (inr (o, x))      -- a stepping continuation steps the node

Naturality, by hand (three cases): `Option.map (Σ f) (λ (inr (o, some x))) = some (inr (o, f x)) =
λ (inr (o, Option.map f (some x)))`; the `none` and `inl` cases are constants on both sides. ✓
This λ is `Option`'s *traversal* of the container Σ (`sequence` for one node — mathlib has
`LawfulTraversable Option`, `Mathlib/Control/Traversable/Instances.lean:52`). **But the FAIL-OPEN
law is natural too**: `λ' (inr (o, none)) = some (inl ())` — "if the rest refuses, the program is
done". Check: `Option.map (Σ f) (some (inl ())) = some (inl ()) = λ' (inr (o, Option.map f none))`.
✓ Both are distributive laws. Naturality does not see absorption.

Two further facts about this layer. (i) For a UNARY node the strict λ is literally `Option.map`
on the tail: the whole of "N4 at the sequential Σ over `Option`" is Option's functoriality. (ii)
The plain shape `Σ B ⇒ B Σ` cannot express PREFIXING at all: the rule `o;x —o→ x` has successor
`x : X`, but `Σ X = 1 + Op × X` has no `X` summand, so no `λ` yields it (the conclusion of a
plain law is a depth-one Σ-term over successors of EVERY argument). KERNEL-NECESSITY's `Σ∘B ⇒
B∘Σ` is the right shape for a synchronous product — the hyperedge — and the wrong shape for
sequencing.

**3.2 Abstract GSOS ρ : Σ(Id × B) ⇒ B T_Σ (Turi–Plotkin's format).** Conclusions may be arbitrary
terms over the arguments and their successors. Prefix, with `B X = Req → Obs × X` and `Req = Op`:

    ρ (inl ())             = fun _ => (refused, done)                      -- `done` refuses everything, stutters
    ρ (inr (o, (x, b)))    = fun r => if r = o then (ok, η x) else (refused, η (o;x))

No premise on `b` at all: at the sequential fragment "refusal" is LABEL MISMATCH, not a gate. The
state-dependent `gateOK k t` (`Gate.lean:233-234`) is nowhere in this picture, because the carrier
contains programs and no cells. For the gate to enter the format, cells must enter the carrier —
as CONSTANTS of Σ (zero-ary shapes `k : K`, with the rule `ρ(k) = c(k)`, the cell's own coalgebra
step; zero-premise rules are GSOS). Then the configuration signature is

    Σ_K X = K + Op × X + (ι → X)        -- cells · prefix · the ι-ary JOINT node (the hyperedge)

and the joint rule is the one that has content:

    ρ (join (xᵢ, bᵢ)ᵢ) = fun r => if (∀ i, (bᵢ r).1 = ok) ∧ Balanced (bᵢ r)ᵢ
                                  then (ok,      join (η (bᵢ r).2)ᵢ)          -- all legs step: commit
                                  else (refused, join (η xᵢ)ᵢ)                 -- any leg refuses: stutter, NO leg moves

This IS a plain `Σ B ⇒ B Σ` law at the `join` shape (every argument's successor used once, depth
one) — the strict `Option`/`Except`-traversal of the `ι`-tuple, plus a side-condition
(`Balanced`, the N2b equalizer, `/Users/ember/dev/minidregg/Kernel/TurnBalancedLimit.lean:90-115`).
And AGAIN a fail-open sibling is lawful: `ρ'` that commits the stepping legs and drops the refused
ones (`Σ_K` has the unary prefix/solo shapes to land in) is natural and GSOS — and it is the
half-committed transfer, R6 violated, the exact thing `no_commit_of_nonzero_balance`
(`MultiCellHyperedge.lean:415-420`) and `binding_is_proper` (`Turn.lean:93-100`) exist to refuse.

**3.3 The monad/comonad refinement (T_Σ over the cofree comonad D_B).** Squares: for a law of
the monad T_Σ over a functor, the η-square `λ ∘ η_B = B η` and the μ-square
`λ ∘ μ_B = B μ ∘ λ_T ∘ T λ`; dually the ε- and δ-squares over a comonad; all four for TP's full
version. From memory: GSOS laws `Σ(Id × B) ⇒ B T_Σ` are in BIJECTION with distributive laws of
`T_Σ` over `D_B` (the free extension is unique), so the refinement adds NO constraint on which
rules are allowed — it only packages them. For the strict traversal the η-square is
`λ (var (some x)) = some (var x)`, `λ (var none) = none`, and the μ-square is the traversal's
composition law (`LawfulTraversable.comp_traverse`-shaped); both hold by hand on the 2-op toy.
The fail-open `λ'` extends freely as well. The squares do not discriminate either.

**3.4 Where fail-closed lives — the answer to the format-fit question.**

- *Is it forced by the law (i)?* **No.** At every layer the fail-open sibling is a lawful
  distributive law. Absorption is not an axiom of distributive laws.
- *Is it a choice of λ (ii)?* **Yes — and a nameable one.** Fail-closed = "λ at every shape is the
  STRICT traversal": for the Moore B, `(∃ i, (bᵢ r).1 = refused) → (λ s r).1 = refused ∧
  successor = the node itself`. At the sequential fragment this is nothing more than `Option`'s
  left-zero `none >>= f = none` (Kleisli iteration of `List Op` over `K → Option K`); at the joint
  node it is joint atomicity (R6). This is a Prop ABOUT a law, to be stated and given teeth
  separately (§5).
- *Is anything outside the format (iii)?* **Two things, precisely.** (1) The gate's
  state-dependence (`gateOK k t`, `Act.wf` reading `k.accounts`, `Gate.lean:151-155`) is in-format
  only via cells-as-constants; that is fine. (2) The joint rule's side-condition. In GSOS a rule
  may inspect the arguments' BEHAVIOURS (`bᵢ`), never their identities. `Hyperedge.balanced` is
  `Σᵢ halfEdge i (x i) t = 0` with `halfEdge : ι → Carrier → Turn → Bal` (`Turn.lean:45, 55`) — it
  reads the CARRIER. For the joint gate to be GSOS, the half-edge must be OBSERVABLE: `Obs` must
  expose the signed δ of a leg at request `r` (i.e. `Bal ↪ Obs`). If the design insists balance be
  checked on hidden state, the joint gate is not GSOS — and that is the exact, honest sense in
  which KERNEL-NECESSITY §3's "failure names the kernel's signature" would apply. The (B)-side
  `aggregateDelta` over accepted legs (`MultiCellHyperedge.lean:195`) already computes from the
  leg data, which suggests it is observable there (**inferred**, not verified in the Lean).
- *Negative premises* (`x ↛`) — the classical GSOS danger — are harmless here BECAUSE B is
  deterministic: refusal is a VALUE (`refused : Obs`, or `none`), so "x refuses" is a pattern
  match, not a negative hypothesis over a nondeterministic successor set. A powerset B (`Set X`)
  would lose this AND lose polynomiality (no `PFunctor.M`). The determinism of the gate is what
  makes it fit.

**Verdict on format-fit: the fail-closed gate FITS (as the strict traversal at every shape, with
refusal a stutter observation); the format does NOT ENFORCE fail-closedness; fail-closedness is
therefore a keystone Prop on λ with its own teeth; the only genuine non-fit risk is a
carrier-reading side-condition at the joint node, which is repaired by making the half-edge an
observation.**

## 4. What Turi–Plotkin gives — and what it does not

Given a law λ (any of the layers above), with Σ, B polynomial:

- **Two canonical λ-bialgebras.** On closed terms `W Σ` (initial Σ-algebra `W.mk`) the
  *operational model* `opModel : W Σ → B (W Σ) := fold (B.map W.mk ∘ λ)`; on behaviours `M B`
  (final B-coalgebra `M.dest`) the *denotational model* `denModel : Σ (M B) → M B :=
  M.corec (λ ∘ Σ.map M.dest)`. Both satisfy the bialgebra pentagon
  `coalg ∘ alg = B.map alg ∘ λ ∘ Σ.map coalg`.
- **Adequacy (operational = denotational).** `fold denModel = corec opModel : W Σ → M B`, and it
  is the UNIQUE bialgebra homomorphism (unique as a Σ-hom by `fold_unique`, unique as a B-hom by
  `M.corec_unique`). In tree terms it identifies two readings the tree has only ONE of today:
  the compositional reading — `derivedExecutor = fold execAlg` (`EffectSpec.lean:132`) and the
  descriptor `replay` (`:199-218`) are instances — and the trace reading, the `corec` of a
  small-step machine on configurations `⟨program, cell⟩`, which does not exist in the tree (no
  `corec` anywhere). N4 would MAKE the second reading and prove it equal to the first by one
  theorem, the coalgebraic mirror of `agree_by_initiality`.
- **Bisimilarity is a congruence.** `Bisim t u := corec opModel t = corec opModel u` (the kernel
  of the final map; for polynomial B on `Type` this is the largest bisimulation — from memory).
  Congruence: `(∀ i, Bisim (f i) (g i)) → Bisim (W.mk ⟨a, f⟩) (W.mk ⟨a, g⟩)` for EVERY shape `a` —
  a three-line corollary of the Σ-hom half of adequacy. At the joint shape with cells as constants
  this is the sentence paper2 promised: *a hyperedge over observationally-equal cells
  (equal `List Req → Obs` behaviours) is observationally equal* — turns compose over behavioural
  equivalence. Since B is deterministic, bisimilarity = trace equivalence (equal `nuF` points).
- **Relation to `sound_bisim_ill_posed`** (`/Users/ember/dev/minidregg/docs/HYPEREDGE-DESIGN.md:91-94`,
  `Turn.lean:115-117` `[N-TURN-b]`): that wall refutes *soundness as bisimulation to a FREE
  abstract Spec*. N4's bisimilarity is on ONE bialgebra — the kernel's own λ — with no sibling
  spec. N4 does not resurrect the sibling; it is compatible with the wall.

**What it does NOT give** (so nobody labels it as more): conservation (`admit_conserves`,
`Gate.lean:406-419`, and `no_commit_of_nonzero_balance` are properties of the specific Σ-algebra
and side-condition — N1/N2b content); authority, non-amplification, unforgeability (N5, the portal
floor `[GATE-portal]`); fail-closedness itself (§3.4 — a property of λ, not of the framework);
frame/footprint (`admit_footprint`, `:426-431`, N1); anything cryptographic. N4 gives structure:
one λ ⇒ two agreeing readings ⇒ composability of turns under behavioural equivalence.

## 5. The Lean statement, keystone-fielded

**Home.** The statement is candidate-independent (abstract `PFunctor`s), so `Theory/` — but
`Theory/` may import only Mathlib + Theory (`/Users/ember/dev/minidregg/scripts/check-import-boundary.sh:4-9,
37-38`) and the N3 engine (`fold`, `fold_unique`) lives in `Compiler/Signature.lean`, which imports
Mathlib only (`Signature.lean:34-35`). Re-deriving `fold_unique` in Theory would be a twin. Two
honest options: (α) relocate `Compiler/Signature.lean` → `Theory/Signature.lean` verbatim (legal by
its imports; one import line changes in `Effects/EffectSpec.lean:67`), then author
`Theory/Bialgebra.lean`; or (β) author `Compiler/Bialgebra.lean` next to `Signature.lean` now and
move both later. Owner decision; (α) is the ATLAS-faithful one.

**Mathlib reused:** `PFunctor`, `PFunctor.Obj/map/comp/W/W.mk/W.dest`, `WType.elim`; `PFunctor.M`,
`M.corec`, `M.dest`, `M.dest_corec`, `M.corec_unique`, `M.bisim`, `M.inhabited`. **Authored:**
`DistLaw`, `Bialgebra`, `IsBialgebraHom`, the two canonical models, adequacy, congruence,
`FailClosed`. Universes: keep everything in one `Type u` (`PFunctor.{u,u}`), so `Obj`, `W`, `M`
all land in `Type u` and `Σ (B X)` typechecks without `ULift`.

```lean
-- Theory/Bialgebra.lean (N4). Over abstract polynomial Σ, B — no kernel imports.
/-- A distributive law of the syntax functor over the behaviour functor: the component
family plus NATURALITY, which is its only axiom. (Absent from mathlib at 1c2b90b.) -/
structure DistLaw (Σ B : PFunctor.{u, u}) where
  app : ∀ {X : Type u}, Σ (B X) → B (Σ X)
  natural : ∀ {X Y : Type u} (f : X → Y) (s : Σ (B X)),
    B.map (Σ.map f) (app s) = app (Σ.map (B.map f) s)

/-- A λ-bialgebra: one carrier, a Σ-algebra and a B-coalgebra, glued by the pentagon. -/
structure Bialgebra (l : DistLaw Σ B) where
  X : Type u
  alg : Σ X → X
  coalg : X → B X
  pentagon : ∀ s : Σ X, coalg (alg s) = B.map alg (l.app (Σ.map coalg s))

def IsBialgebraHom (A₁ A₂ : Bialgebra l) (f : A₁.X → A₂.X) : Prop :=
  (∀ s, f (A₁.alg s) = A₂.alg (Σ.map f s)) ∧ (∀ x, A₂.coalg (f x) = B.map f (A₁.coalg x))

/-- Operational model: the B-coalgebra on closed terms, BY FOLD (N3's engine). -/
def opModel (l : DistLaw Σ B) : Σ.W → B Σ.W :=
  WType.elim _ (fun s => B.map PFunctor.W.mk (l.app ⟨s.1, s.2⟩))
/-- Denotational model: the Σ-algebra on behaviours, BY COREC (mathlib's final coalgebra). -/
def denModel (l : DistLaw Σ B) : Σ (PFunctor.M B) → PFunctor.M B :=
  PFunctor.M.corec (fun s => l.app (Σ.map PFunctor.M.dest s))

def initialBialgebra (l) : Bialgebra l := ⟨Σ.W, PFunctor.W.mk, opModel l, …⟩
def finalBialgebra   (l) : Bialgebra l := ⟨PFunctor.M B, denModel l, PFunctor.M.dest, …⟩

/-- **N4a — adequacy.** The fold of the denotational algebra IS the corec of the operational
coalgebra, and it is the unique bialgebra homomorphism from the initial to the final model. -/
theorem N4_adequacy (l : DistLaw Σ B) :
    WType.elim _ (denModel l) = PFunctor.M.corec (opModel l)
    ∧ ∀ f, IsBialgebraHom (initialBialgebra l) (finalBialgebra l) f
        → f = PFunctor.M.corec (opModel l)

/-- Behavioural equivalence of closed terms: equal points of νB. -/
def Bisim (l : DistLaw Σ B) (t u : Σ.W) : Prop :=
  PFunctor.M.corec (opModel l) t = PFunctor.M.corec (opModel l) u

/-- **N4b — congruence.** Bisimilar arguments, bisimilar term — at EVERY shape. -/
theorem N4_congruence (l : DistLaw Σ B) (a : Σ.A) (f g : Σ.B a → Σ.W)
    (h : ∀ i, Bisim l (f i) (g i)) : Bisim l (.mk ⟨a, f⟩) (.mk ⟨a, g⟩)

/-- **Fail-closed is a PROPERTY of a law, not an axiom of laws** (§3.4): with refusal a value
of the behaviour, a refused argument refuses the node. Stated for the Moore B with a
designated `refused : Obs`; the `Option` form is the special case `Obs = Unit + 1`. -/
def FailClosed (l : DistLaw Σ (moore Req Obs)) (refused : Obs) : Prop :=
  ∀ {X} (s : Σ (moore Req Obs X)) (r : Req),
    (∃ i, (obs (s.2 i) r) = refused) → obs (l.app s) r = refused
```

**Keystone fields (to be BUILT, per the audit discipline — no `Prop := True`):**

- *satisfiable.* The toy: `Σ_toy X = 1 + X × X` (a leaf and one BINARY joint node — the
  smallest signature where N4 is not functoriality), `B = optionP` (`⟨Bool, cond · Unit Empty⟩`),
  `λ_strict` = the strict traversal (`join (some x, some y) ↦ some (join x y)`, else `none`) with
  `natural` discharged by cases. Exhibit: `opModel` on a two-leaf tree steps; `denModel` on two
  behaviours computes; `N4_adequacy` instantiated; `N4_congruence` fires on a concrete pair of
  bisimilar-but-unequal terms (two trees with equal step-counts, e.g. `join leaf leaf` vs a
  leaf-only shape refusing at the same depth) — the congruence bites where syntactic equality
  fails. Then the 2-op sequential toy (`Op = Bool`) with prefix nodes, checking §3.1's three cases
  by `rfl`.
- *teeth.* `λ_open` — the fail-open law (`join (some x, none) ↦ some (solo x)`, with a unary
  `solo` shape added to Σ so it has somewhere to land) — is a genuine `DistLaw` (naturality
  proved), and `¬ FailClosed λ_open` is witnessed at one node; and, the R6 bite: under
  `λ_open` a joint term with one refused leg has `opModel` = `some _` (a commit with an
  unadmitted leg), while under `λ_strict` it is `none`. This is `binding_is_proper`'s cousin: the
  format admits the bug; the Prop refuses it.
- *premise-inhabitation.* `Σ.W` nonempty (a leaf shape with `Empty` arity — `EffectSpec.sig`'s
  `none`, `Signature.lean:101-105`), `M B` inhabited (`Inhabited B.A`: `Bool` for `optionP`;
  `Req → Obs` for Moore when `Obs` is inhabited), the pentagons of both models proved (not
  stipulated), and `DistLaw` inhabited by BOTH λ_strict and λ_open so the `∀ l` of N4a/N4b is
  over a domain with at least two elements.

**Then the kernel instance (a second file, after the twin decision, §7):** `Req := Footprint ×
TurnReq W` (or the (B)-side typed request), `Obs := Reject ⊕ Receipt` with `Bal ↪ Receipt`,
`c := ` the Moore coalgebra of §2(c) built from whichever gate survives, cells as constants, the
`ι`-ary joint shape with `Balanced` read off `Obs`, `λ := ` strict traversal + side-condition,
`FailClosed λ` proved, `N4_congruence` specialised to "a hyperedge over `nuF`-equal cells is
`nuF`-equal".

## 6. Verdict and the risk

**Can N4 be stated at this pin?** Yes, self-contained, at modest cost: mathlib supplies both
universal objects (`PFunctor.W`, `PFunctor.M`) and both uniqueness principles (`fold_unique` in
the tree, `M.corec_unique` in mathlib); what must be authored is a ~15-line `DistLaw`, a ~15-line
`Bialgebra`, the two canonical models with their pentagons (~60 lines), adequacy (~60-90 lines —
the one real proof: `WType.elim denModel` is a B-coalgebra hom, by W-induction through
`dest_corec` and `natural`, then `corec_unique`), congruence (~10 lines), keystones (~80 lines):
**≈250-300 lines**, comparable to `TurnBalancedLimit.lean` (277). No Adámek, no ω-limits, no
enrichment. **But the honest reading of its content is this: at the sequential `EffectSpec.sig`
with `B = Option`, N4 IS a triviality** — the distributive law is `Option.map` on the tail, νB is
ℕ∞, bisimilarity of closed programs is equality of op-lists, and "congruence" is functoriality.
That is information, not failure: it says N4's content lives exactly where N3's does not — at a
BRANCHING Σ, the `ι`-ary joint node, i.e. the hyperedge as an operator of the syntax. N2 fixed
the hyperedge as a LIMIT of states; N4 needs it as a SHAPE of Σ whose λ-component is the strict
traversal. The two results compose: N2b's equalizer is N4's side-condition. **The single most
likely point of failure** is §3.4(iii)(2): the joint rule must decide `Balanced` from the legs'
OBSERVATIONS, and `Hyperedge.halfEdge` today reads the carrier (`Turn.lean:45`). If `Obs` cannot be
made to carry the half-edge (or the design refuses to expose it — privacy, `Kernel/PrivateTurn`),
the joint gate is not GSOS and N4 must be stated for the admission half only, with conservation
outside the format. That would be a real, nameable result about the kernel's signature; it is not
a reason to skip the abstract file.

## 7. Sequencing

1. **Decide B's shape first — it does not wait on the twin collapse.** Recommend (c): the Moore
   functor `Req → Obs × X`, refusal as an observation with a stutter successor, νB = `List Req →
   Obs` = ATLAS item 15. Both twins already have this refusal shape (§2.4); the choice of `Obs`
   (with `Reject` and the receipt inside, and `Bal` observable) is the same decision the twin
   audit's Phase 2 needs anyway (`KERNEL-TWIN-AUDIT.md:745-749`). Make it once.
2. **Decide Σ's joint shape** — that N4's Σ contains the `ι`-ary `join` alongside
   `EffectSpec.sig`'s prefix nodes, and that `Balanced` is computed from observations. This is
   the only design input the abstract file needs and the only place it can go wrong.
3. **The twin collapse** gates the INSTANCE file only. The abstract N4 file imports no kernel.
4. **Smallest Lean file worth writing:** `Theory/Bialgebra.lean` (after relocating
   `Compiler/Signature.lean` → `Theory/`, §5 option α; else `Compiler/Bialgebra.lean`) —
   `DistLaw`, `Bialgebra`, `opModel`/`denModel`, `N4_adequacy`, `N4_congruence`, `FailClosed`, with
   the keystones of §5 built at the leaf-plus-binary-join toy over `optionP` and at the 2-op
   sequential toy, `λ_strict` and `λ_open` both exhibited. Statement-first: land the `def`s and the
   theorem STATEMENTS with the keystone witnesses before the adequacy proof is fanned out. A
   fan-out lane for the adequacy proof is bounded and mathlib-only (`M.corec_unique` +
   W-induction), the same safe shape as N2a's lane.
5. **Do not** port breadstuffs' `nuF`/`TurnCoalg`: `PFunctor.M` at the Moore PFunctor IS νB, and
   `List Req → Obs` is a theorem about it (`M ≃ (List Req → Obs)`), not a parallel construction.
   Nothing lands beside what it supersedes.
