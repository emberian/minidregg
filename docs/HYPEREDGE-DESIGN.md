# HYPEREDGE-DESIGN — the turn is a wide pullback (ATLAS §8, decision 3)

*Design pass 2026-08-07. Inputs: breadstuffs' `Dregg2/Hyperedge.lean` (the wide-pullback
model and its three negative theorems), `Exec/FullForestAuth.lean` (the deployed
delegation-forest model), `Substrate/VerbCompression.lean` (the proved 3-verb kernel),
`Metatheory/Dynamics/` (verb = admission × footprint-Fpu in the product camera), and
the accumulation-native aggregation decision from PROOF-SYSTEM-SURVEY.md.*

## 0. The decision

**Minidregg has ONE turn model: the hyperedge.** A turn is a wide pullback —

```
Turn := { legs     : ι → Leg              -- finite; ONE leg per cell (see §5)
        , body     : AdmissibleBody       -- the shared transition, fired atomically
        , apex     : TurnId               -- the shared identity (the receipt anchor)
        , agree    : ∀ i, turnId (next (state i) body) = apex   -- N cone legs
        , balanced : ∀ a : AssetId, Σ i, δ i a = 0              -- per-asset half-edges
        }
```

Breadstuffs carried two disconnected formalizations of "a turn" — the executed
delegation forest (`FullForestG`, the production entry) and the hyperedge (proved,
disconnected, with the honest negatives) — plus bridges (`JointViaHyper`) welding
fragments. Minidregg inverts: the hyperedge is the primitive; everything breadstuffs
expressed as tree structure becomes **witness structure** (§2). What dies: the second
turn model, the `eraseG` gated/ungated twin, the JointTurn bridge modules, and ~38 of
the 40 `exec*` entry points.

A single-cell action is the `ι = 1` hyperedge. A transfer is `ι = 2` (debit leg,
credit leg, balanced). An N-party joint turn is `ι = N` — *the same object, no
special shape*. Pairwise agreement between any two participants is a theorem
(`(agree i).trans (agree j).symm`), never C(N,2) data — that economy, proved in
breadstuffs, is the reason this primitive wins.

## 1. The two gates, at hyperedge granularity

The metatheory already dictates the verb shape: **admission × footprint**, provably
non-collapsing (`camera_blind_to_caveats`). The hyperedge lifts both gates once:

- **Admission (epistemic):** every leg's demand is discharged by its witness —
  `∀ i, Verify (demand i) (witness i)`. Four sub-legs per breadstuffs' deployed gate,
  kept: credential (portal), capability authority (`granted ≤ held`, in Lean),
  caveats, revocation-read-from-committed-state. Fail-closed on any leg of any leg.
- **Footprint (ontic):** ONE frame-preserving update in the product camera over the
  *joint* footprint. Disjoint legs compose by `fpu_prod`; `balanced` is exactly the
  value-camera component; non-amplification and evidence-monotonicity are the `Auth`
  camera components (the same camera, per `authority_evidence_share_camera`). The
  frame rule — cells not in the tuple are untouched — is the camera frame, read four
  ways (sovereignty, joint composition, sharding, offline merge) as in paper2 §1.3.

Two hyperedges with **disjoint footprints commute** — the confluence dial's
coordination-free fragment is separating conjunction on footprints, priced by the
classifier, exactly where breadstuffs' guard algebra put it.

## 2. Forests become witness structure

In breadstuffs a delegation forest *executes*: the parent's `delegateAttenA` runs,
mutating state, then the child's action runs against the mutated state — order
threaded through `execFullChildrenG`. That sequencing is why the forest and the
hyperedge could never unify there.

Minidregg moves the tree out of the state-threading and into the **authorization
derivation**: a leg's witness may cite an *intra-turn conferral* — "the leg over
cell P grants me exactly this attenuated capability" — forming a DAG of witnesses
whose shape IS the old forest. The turn's *shape* (participants, footprint, δ,
demands) stays flat and eager; the *witnesses* carry the derivation, lazily.

- **Determination is eager; witness is lazy** (the breadstuffs spine sentence) — now
  a structural fact of the turn type rather than a discipline.
- Non-amplification per delegation edge (`conferred ≤ held`, over the real
  attenuation lattice) becomes a well-formedness condition on witness derivations —
  the same theorem, stated once over the DAG instead of once per executed edge.
- Acyclicity of the witness DAG is demanded by construction (derivations are
  inductive); the forest's execution order is recovered as any topological
  linearization, and the theorem that all linearizations agree is the confluence of
  disjoint intra-turn conferrals — small, and it replaces two 60KB+ executor files.

## 3. The three negative theorems are load-bearing walls

Breadstuffs proved three refusals; minidregg builds them into the types:

1. **`hyper_binding_is_proper`** — the binding (agree ∧ balanced) is a *proper*
   subobject: genuine data, underivable. → The `Turn` constructor demands both
   fields; no smart constructor infers them; `balanced` is *checked* at admission
   (a decidable per-asset sum), never assumed.
2. **`hyperedge_sound_needs_binding`** — step-completeness alone does not give
   joint admissibility. → Soundness theorems take the binding as an explicit
   premise; the anti-vacuity witness is the `ι = Unit`, half-edge `1` instance
   (kept in-tree, RED, per the witness discipline).
3. **`hyperedge_sound_bisim_ill_posed`** — soundness-as-bisimulation-to-a-free-Spec
   is false. → No abstract sibling spec: soundness is stated over the executable
   kernel directly. This is ATLAS law 6 (one executable tower) arriving
   independently from the mathematics.

## 4. Receipts and accumulation-native aggregation

A committed turn leaves **one receipt Q** — the committed whole-post-state of all
legs under the one commitment scheme — anchored at `apex`. Because every turn is one
hyperedge regardless of ι, **the accumulated object is uniform**: no separate
single/joint/conditional proof shapes, which is precisely what lets the descriptor
compiler stay a fold (one IR family for bodies; `interp` = executor, `compile` =
descriptor, agreement by initiality — with syntactic leaves per ATLAS).

Aggregation is the Arc/WARP-shape accumulator from PROOF-SYSTEM-SURVEY §0, **ours,
mechanized in-house**: per link, the accumulation verifier folds the proximity
claims for the encoded (body, Q, seam) witness — including the chain seam
`post-root i = pre-root (i+1)` as an accumulated claim — and the light client
checks the running accumulator plus one final decider pass. Straightline extraction
makes whole-history soundness hold at deployed depth as a theorem. In-circuit
recursive verification exists only as the final compression step.

## 5. Sharp edges, decided

- **One leg per cell per turn.** Breadstuffs' contended cross-cell forest was an
  honest OPEN behind a `distinctCells` NoDup gate; we adopt the proven fragment as
  the law. Multiple writes to one cell within a turn = one leg carrying a *composed*
  `gwrite` (guard composition is the predicate algebra's ∧ — already priced by the
  dials). Fail-closed on duplicate cells.
- **The leg vocabulary is the compressed kernel**: `create · gwrite(g) · move`, with
  `g` from the proved four-level guard lattice (`local ⊂ literal ⊂ +absence ⊂
  +order`; conservation outside all of them, carried by `balanced`). The handler
  registry is small by construction — 3 verbs × guard classes, every handler with
  all floor obligations as proof fields.
- **Holes are legs with lazy witnesses.** An intent is a turn shape with an unfilled
  leg whose δ, footprint, and demand are already fixed (eager); fulfillment supplies
  the witness; the hole's `Pred` admits it. The GUARDED-HOLES guardrail — a fill
  binds its δ and guard into the proof — is the leg type, not a review rule.
- **Revocation reads committed state** (never the wire), unchanged from breadstuffs'
  deployed gate — the adversary-uncontrollability argument carries over verbatim.

## 6. What must be proved early (the keystone slate)

1. `fpu_prod`-composition of leg footprints + the frame reading (mostly ports from
   `Metatheory/Dynamics/`).
2. Witness-DAG linearization confluence (§2) — the theorem that retires the forest
   executor pair.
3. `balanced`-checked conservation: reachable ⇒ per-asset Σ = 0 identically (issuer
   wells; port of `reachable_total_zero`).
4. Non-amplification over witness derivations (port of `execFullForestG_no_amplify`
   restated on the DAG).
5. The two RED witnesses from §3 kept in-tree.
6. Body-IR initiality: interp and compile as folds of one algebra over syntactic
   leaves — the single induction the whole circuit story rides.

## 7. Open

- Leg-level *ordering effects* inside one cell's composed gwrite when guards are
  order-sensitive (the `+order` lattice level): canonical order carried in the shape,
  or forbidden at v0? Leaning: carried, since `admitTable` automata already encode
  order-sensitivity as state.
- Whether `apex` is derived (hash of shape) or free (chosen, then bound by Q) — the
  Mina `account_updates_hash` precedent suggests derived; derived kills a whole
  equivocation class at the cost of recomputation in-circuit.
- The exact encoding of witness-DAG citations in the wire format (affects the
  disclosure dial: an intra-turn conferral is visible structure vs committed).
