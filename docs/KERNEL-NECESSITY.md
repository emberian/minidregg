# KERNEL-NECESSITY — exhibiting the kernel instead of designing it

*Charter, 2026-08-07. The kernel lane's brief (ember): find the "new / more
abstract / purer / less rigid / more formally-necessary-by-the-laws-of-category"
structure for the problem class — then discover what to express WITH it. This
document turns that into a research program with six candidate necessity
theorems. Each is stated informally, given its universality shape, its
already-held pieces in breadstuffs, its genuinely-new content, and its risk.
Method: every N-theorem enters the Lean tree statement-first (ATLAS keystone
fields), with the universal property AS the statement — so "the kernel is
necessary" is machine-checked or it is nothing.*

## 0. The question, sharpened

Breadstuffs' kernel is *good design*: eight verbs with a proved-injective
behavior table, later proved compressible to three. But `VerbCompression`'s own
`verb_minimality_is_ontology_relative` exposed the ceiling: minimality relative
to a hand-chosen ontology is taste wearing a theorem's clothes. The question
this lane answers is one level up:

> **Fix the problem class P. What structure does ANY solution of P necessarily
> carry — and is there a universal (initial/final/free) solution K such that
> every solution factors through K uniquely?**

If K exists, the kernel stops being a design and becomes an *exhibit*: the
verbs, the substances, the turn shape, the receipt algebra are read off K, and
"what can we express with it" becomes the study of K's internal language
rather than a feature roadmap.

**The problem class P** (the requirements, as axioms — distilled from paper2
and ATLAS; each is a formal hypothesis, not prose):

- **R1 Locality.** State is partitioned into owned units; an update's
  admissibility and effect are functions of its footprint (the frame rule).
- **R2 Verification asymmetry.** Lawfulness is a decidable predicate on
  witnesses; witness *production* is unconstrained/untrusted (BHK operational).
- **R3 Resource discipline.** Designated quantities admit no copy and no
  silent discard (exact conservation).
- **R4 Authority discipline.** Permission is unforgeable, attenuable along an
  order, and generative only from held permission (with amplification).
- **R5 Evidence monotonicity.** Verified facts persist.
- **R6 Joint atomicity.** Multi-party updates commit together or not at all,
  leaving one shared receipt.
- **R7 Auditability.** The whole evolution is verifiable from receipts alone;
  the log is the truth.
- **R8 Openness.** No global view: the system is a merge (colimit) of partial,
  concurrently-evolving views.

## 1. The six candidate necessity theorems

### N1 — Substance classification (the four substances as a theorem)

**Claim.** Over a product resource algebra (camera), the update disciplines
compatible with R1–R5 are classified — every one factors, essentially
uniquely, as a product drawn from: exclusive (linear value), authoritative
(`Auth M`, whose two polarities are *precisely* non-amplification and monotone
growth — breadstuffs already proved authority and evidence are one camera:
`authority_evidence_share_camera`), and guard-restricted exclusive (guarded
state). **Shape:** an equivalence between the category of R1–R5-compatible
FPU-disciplines and products of the three generators. **Held:** the camera
constructions, `fpu_prod`, `camera_blind_to_caveats` (admission ⊥ footprint),
`value_no_free_copy`. **New:** the classification itself — the *exhaustiveness*
direction ("there is no fourth substance") which no one has stated. **Risk:**
medium — exhaustiveness needs the right notion of "discipline morphism"; a
too-loose notion makes it false, a too-tight one makes it trivial. This is the
first statement to write, because getting the category of disciplines right is
the whole game.

### N2 — The turn is a limit (hyperedge universality)

**Claim.** Any N-party atomic-update object satisfying R6 (one shared anchor,
per-party local checks) with derivable pairwise consistency is a cone; the
hyperedge is the **limit** — the universal such object. Pairwise agreement as
a theorem instead of C(N,2) data is exactly the limit property. The witness-
DAG factorization of forests (HYPEREDGE-DESIGN §2) is the comma-category
structure over the limit. **Held:** the `Hyperedge` structure IS a wide
pullback; the three negative theorems, which reread beautifully in this
language — proper-subobject = the cone conditions are data; needs-binding =
an arbitrary cone is not the limit; bisim-ill-posed = **no free completion
exists** (conjecture: the forgetful functor from lawful models to free spec
models has no left adjoint — worth attempting, it would make the "no abstract
sibling spec" law a theorem). **New:** the universality statement and the
no-left-adjoint conjecture. **Risk:** low for universality; medium for the
adjoint refutation.

### N3 — One induction (initiality as law, not technique)

**Claim.** The kernel's effect signature must be a **polynomial functor**
(syntactic leaves), and its semantics the **initial algebra** — because that
is the unique choice under which every second reading (circuit, cost model,
explainer, differ) agrees with the executor by initiality, with one induction
total. Breadstuffs *discovered* this negatively: opaque closures in the leaves
broke functoriality (`compile_not_a_seq_hom`), forcing three compiles and 11K
lines of welds. **Shape:** `fold_unique` elevated from lemma to architectural
axiom — the derivation-totality requirement (ATLAS's "everything derived")
*formally forces* initial-algebra semantics over a polynomial signature.
**Held:** `Initiality.lean` nearly whole. **New:** the converse direction —
totality of derivation ⟹ polynomiality — stated precisely. **Risk:** low;
mostly a matter of honest formulation.

### N4 — The centerpiece: the kernel as a distributive law (Turi–Plotkin)

**Claim.** Effects form a syntax functor Σ (N3, initial side); living cells
form a behavior functor B with **final coalgebra** νB (held: `nuF = List Adm →
Obs`, constructed, with uniqueness). The kernel — the thing that runs turns
over cells — is exactly a **distributive law λ : Σ∘B ⇒ B∘Σ** (abstract GSOS).
Turi–Plotkin's theorem then *gives for free* precisely the properties paper2
promises: behavioral equivalence is a congruence (composability of turns over
observationally-equal cells), the operational and denotational readings agree,
and the bialgebraic semantics is unique. **This is the literal content of
"formally necessary by the laws of category to solve any problem like this":
well-behaved operational semantics ARE distributive laws** — that is a
theorem, not a school of thought. **Held:** both ends (initial Σ-algebra
material, `TurnCoalg`/`nuF`); the two never met in breadstuffs — the abstract
coalgebra tower was one of the proven-disconnected parallel towers. The
distributive law is the *bridge that makes the tower load-bearing* instead of
parallel. **New:** exhibiting λ for the admission×footprint signature;
checking the gate (fail-closed `Option`) fits the GSOS format (likely needs
the monad-comonad refinement of TP: Σ free monad over effects, B cofree over
observations, λ a mixed distributive law — the `Option` layering is exactly
where care lives). **Risk:** the real research risk of this lane — GSOS
format-fit is where it could genuinely fail and teach us the most.

### N5 — Freeness is unforgeability (authority as a free structure)

**Claim.** The authority dynamics of R4 are the **free** ⊗-⋁-closure of the
initial connectivity: reachable authority = elements constructible from
generators under attenuation (≤) and amplification (⊗) — and *freeness itself
is the no-forgery theorem*: an element exists only with a derivation, and the
derivation IS the witness (tying N5 to N2's witness-DAGs: the forest is the
term). Receipt-disclosure of generative acts = the presentation of each
element is recorded. **Held:** `AmpProduces`/`AmpClosed`/`amp_noforge_closure`
are the closure half. **New:** the freeness half (no relations beyond those
imposed — i.e., the closure is not just sound but *initial* among R4-models),
which upgrades "nothing ex nihilo" to "the authority object is canonically
determined." **Risk:** low-medium; the right ambient category (ordered
commutative monoids with joins?) needs choosing once.

### N6 — Aggregation is a colimit (Loom's receipt-nativity, justified)

**Claim.** The receipt chain is a diagram; the whole-history object is its
**colimit**; the light-client theorem is the *uniqueness of the mediating
morphism* out of it; and Loom's accumulator is an incremental colimit
computation carrying proofs. R8's federation-merge is a colimit of partial
views one level up (LaceMerge's join-semilattice is its poset shadow —
already proved). **Held:** LaceMerge laws; the Q-chain seam-pinning.
**New:** stating aggregation-as-colimit so that "receipt-native accumulation"
(LOOM §3) is the *computed* universal object — which explains WHY accumulating
the kernel's own algebra is canonical and a zkVM wrapper is not: the wrapper
computes a colimit of the wrong diagram. **Risk:** low; the value is
architectural clarity and the exact statement of "attests the whole history."

### The connective tissue — one fibration of predicates, enriched dials

The guard algebra's "one `Pred` at four polarities" becomes: **one fibration**
of decidable predicates over the base (cells and turns), with the four
polarities as restriction along the four canonical projections (object /
delegated arrow / incoming proarrow / hole). The two dials become
**enrichment**: coordination price and disclosure price as quantale-valued
structure on homs — a guard doesn't *have* a price, it *is* priced by where
it lives in the enriched category. Speculative, listed last deliberately: it
only becomes load-bearing if N1–N4 land, and then it is the natural home of
"what to express WITH it."

## 2. "What to express with it" — the discovery direction

Once K is exhibited, expressivity is *read off*, not legislated:

1. The **internal language** of the fibration (§ connective tissue) is the
   guard/program language — its decidable fragment is what factories may
   install; anything outside is witnessed-predicate territory *by theorem*.
2. The **algebra of Σ** enumerates the effects: if N1's classification holds,
   the verb set is the generator set of the classified disciplines — the
   3-verb kernel becomes forced, and any proposed verb either factors (is a
   program) or extends a substance (is a new discipline, and N1 says there is
   no fifth... or exhibits the fourth we missed, which would be the best
   possible outcome of the program).
3. The **coalgebraic side** enumerates observations: lenses, views, fog-of-war
   — everything hyperdreggmedia wants is a comonadic structure over νB, and
   deos's "affordance = cap-gated effect-template" should fall out as: an
   affordance is a λ-compatible pairing of one Σ-generator with one B-observation.
4. **Loom consumes N3+N6 directly**: descriptors are folds (N3); the aggregate
   is the colimit (N6); receipt-nativity is canonicality.

## 3. Method and sequencing

- Statement-first, universality-shaped, keystone-fielded. A necessity claim
  that cannot be stated as an initial/final/free/limit/colimit property gets
  demoted to design note until it can.
- **Order:** N3 (cheapest, mostly held) → N2 (universality of the held object)
  → N1 (the classification — hardest statement, start the category-of-
  disciplines definition early and let it bake) → N4 (the centerpiece; attempt
  after N2/N3 fix Σ and B precisely) → N5, N6 alongside as their lanes need.
- The Lean home is `Theory/` (candidate-independent, import-boundary-enforced)
  for the shapes, with `Kernel/` instantiating. The distributive-law
  development may need mathlib's category theory at depth — one reason the
  boundary allows Mathlib.
- **Failure semantics:** each N failing is *information that redesigns the
  kernel* — e.g., if N4's format-fit fails at the gate's `Option`, the failure
  names the exact sense in which fail-closed admission is not GSOS, and that
  becomes the kernel's honest signature instead. The program cannot lose; it
  can only stop flattering us.

## 4. Relation to the other lanes

Loom (proof system) does not block on this lane and vice versa: Loom consumes
descriptors whatever their provenance; this lane determines what the
descriptors *are* descriptors of. The first shared artifact is Σ-as-polynomial-
functor (N3), which the Compiler lane needs anyway for syntactic leaves — so
N3 is the natural first statement in the tree, serving both masters.
