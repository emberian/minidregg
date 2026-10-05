# Modular typing for Objective Bend (design, OB-LTUO LT2)

Status: BUILT except D2 and the step-4 theorem. Step 1 (D3, D4: closed specs with an open
inherited row, checked `requires`), step 2 (`canonical_instantiate`,
`Theory/ObjectiveBendTemplates.lean`), step 3a (D6: records may name themselves) and step 3b
(D1, D5: open declarations over `Self`/`Super`, discharged at `fix`) are landed. Open:
D2 (`Assumptions.rigid`) and `infer_instantiate` (step 4), below.

Step 3b as built. An open declaration (`extension E[Self has {...}, Super has {...}](self:
Self, super: Super) -> Super with {...}:` or `spec S[Self has {...}, Super has {...}]:`, its
`requires` lines joining the Self bound) is checked ONCE at its own bounds: its knot field is
the instance at Self = a bounded variable whose bound is the Self row (so an F-bound such as
`heavier(other: Self) -> Self` refers to it) and Super = the Super bound row; a body that
reads `self.m` outside the Self bound is `refused (self-unbound-member)`, a `super.m` outside
the Super bound `refused (inherited-unprovided)`. In `fix(X, seed)` / `fix(compose(...), seed)`
each open layer is instantiated (re-elaborated, memoized `M.E@i`) at Self = the final self and
Super = the row beneath it, after discharging both bounds (`refused (self-bound)` /
`(inherited-unprovided)`, by member). The final self is the closed layers' (all equal, else
`self-conflict`), else the expected type (the enclosing definition's result when the fix is
its tail, or an annotated `let`), else `refused (self-undetermined)`. Closed extension layers
keep their declared types (`inherited-mismatch` when the row beneath differs). A recursive
record target is discharged against its row and the last layer is annotated with the variable
itself. An open declaration referenced as an ordinary value is its bound instance.

What stands in for D2 today: the bound-instance check uses the existing checker, where the
Self variable is an ALIAS of its bound. That is stricter than nothing and catches every
undeclared member read, but it is not the rigid check: a body could use `self` where a value
of exactly the bound row is expected, which an alias accepts and a wider instance then refuses
(as an anonymous typing refusal, never unsoundly: every instance is checked). D2 plus
`infer_instantiate` (step 4) is what turns "every instance is re-checked" into "an instance
whose bounds are discharged is accepted".

Step 1 as built (`chainFix`, `layerAt` in `Compiler/ObjectiveBendElaborate.lean`): `fix(S,
seed)` / `fix(compose(S1..Sn), seed)` over declared plain specs with a seed that is not a
whole target instantiates each layer at the row beneath it by re-elaborating the layer
with `super` typed at that row (memoized knot fields `M.S@i`, metadata = the declared
spec's), discharges at the end, and refuses by name: `inherited-unprovided` (a `super.m`
read with nothing beneath), `requires-unprovided` (a target member nobody provides, naming
the specs that require it), `seed-extra`, `provided-mismatch`; `requires-signature` and
an undeclared requirement are refused at the declaration. A whole-target seed, or any
operand that is not a declared plain spec (ancestry specs, extensions, computed values),
keeps the closed lowering, so every existing program elaborates to the same term. The
re-elaboration stands in for the rigid template check of section 4.1 for CLOSED specs: the
declared closed layer (Super = T) is still emitted and checked, so any error in a body
other than a `super` read already refuses there. Not yet covered: ancestry (non-plain)
specs in a partial-seed chain (they keep the whole-target rule).
Every acceptance program below is already a pinned row of
`tests/objective-bend-source/ltuo/probe-cohort.json` with its current outcome and its
target, so the work is done when those rows are promoted, not when this document says so.

## 1. The problem, measured

Fare's chapter 8 separates two things: typing an extension against one already-known
complete context ("trivial non-modular types", section 8.2.1), and typing it against
only what it uses, so it survives collaborators that did not exist when it was written.
Objective Bend today is the first kind. Measured through the front end (LT0, logs in the
lane):

| probe | program | today | why |
|---|---|---|---|
| W05 | three one-method review specs, `fix(compose(...), {})` | refused | `spec S for T` types both `self` and `super` as the whole `T` (`selfSuperParams`), so the seed must be a whole `T` |
| W06 | `requires missing` that no layer or seed provides, seed `{}` | refused, for the seed's type | `requires` is a string in the interface label; the whole-`T` seed makes every requirement trivially "provided" by a placeholder |
| W06b | the same with a placeholder seed | accepted, answers 0 | the placeholder answers instead of the missing member |
| W07 | `requires review(value: String)` against a `Nat` member | accepted | the requirement is never compared |
| W04 | `record Node: combine(other: Node) -> Node` | refused | `recursive row annotation requires explicit future-row binder` and no surface binder exists |
| C09 | `AddY(self: XYZ, ...)` under a four-field self | refused | correct: the extension names a closed self |
| W09b | AddY written over `Self has {x}` / `Super has {x}`, reused at XYZW | refused (no syntax) | target 11 |
| W10 | an F-bounded binary method closed at two records | refused (no syntax) | target 12 |

The Core4 kernel already has every ingredient (rigid variables with bounds, row tails
retained by `extend`, `Ty.supports` as lookup-based width checking, heterogeneous
`mix`, `Ty.instantiate`, the `future_row_instantiation_accepted` example). What is
missing is an authored binder, a discipline that checks an extension against its
binder alone, and a closing rule that discharges the binder at `fix`.

## 2. Decisions

**D1. Instantiation, not polymorphic Core4 terms.** An open extension is a *template*:
checked once, at its declaration, against its declared bounds with `Self` and `Super`
as rigid variables; every use is an *instance* in which the elaborator substitutes the
actual final self and inherited types into the template's annotations. The emitted
program contains only instances, so it is an ordinary closed Core4 program.
Reason: a Core4 `forall`/type-application former would add a case to every machine
preservation proof (the same detour OB1 rejected for surface semantics), and the
machine never needs to see a type variable it cannot instantiate. With templates, the
no-refusal theorem keeps its statement *and its proof*; the new obligation is one
checker-level theorem (section 6). Cost: code size grows with the number of distinct
instances (memoized per instantiation, section 5.4), and an open template is
second-class: a function parameter cannot be "any extension over Self has {x}". It
can be any closed `Extension<T, I>` value, which is what first-class code needs.

**D2. Rigid parameters are not aliases.** Today a bounded variable is an *alias*: the
recursive global knot (variable 0) and recursive sums are equal to their bound, and
`sameType` unfolds one head. A template's `Self`/`Super` bound is a *lower bound*: the
instance's type supports it, it is not equal to it. So `Assumptions` gains
`rigid : List Nat` (default `[]`), and `sameType`'s two alias clauses skip rigid
indices. With `rigid = []` the checker is the current checker definitionally, so every
existing proof and the demand machine are untouched; only template checks use rigid
variables, and they never reach the machine.

**D3. Closed specs get an open inherited row.** `spec S for T` keeps `self : T` (closed
final self, the trivial non-modular case Fare starts from) but `super` becomes a rigid
`Super` whose bound is exactly the members `S` reads through `super` (`Super has
{m: T.m | super.m occurs in S}`) and whose provided type is `Super with {S's defs}`.
This alone repairs W05, W06 and W07 with no new syntax, and keeps every existing program
meaning what it meant (a whole-`T` seed still discharges every bound).

**D4. `requires` is the self bound, and it is checked.** In an open spec, each
`requires m(...) -> R` is a member of the `Self` bound. In a closed `spec S for T` it
must equal `T`'s member `m` exactly (`refused (requires-signature)` otherwise, naming
the spec, the member, and both signatures); W07.

**D5. `fix` discharges.** `fix(compose(L1, ..., Ln), seed)` types the chain bottom-up
from the seed (section 4.3). The final provided row must be exactly the target; a
member of the target that no layer and no seed provides is `refused
(requires-unprovided)` naming the member and the spec(s) that require it (W06). A
layer reading `super.m` that nothing below provides is `refused
(inherited-unprovided)`. The placeholder-seed form (W06b) remains legal: a seed that
provides a member discharges a requirement for it. That is not a loophole: it is
inheritance from the seed, and the member that answers is the one the seed supplied.

**D6. Recursive records are nominal, through the same bounded-variable machinery as
recursive sums.** `record Node: combine(other: Node) -> Node` resolves `Node` to an
alias variable bound to its row (sum-style `sumVariables`/`sumBounds`, keyed by the
record). The "future-row binder" of the audit is the template binder of D1, which is a
different thing: `Node` is one closed recursive type; `Self has {combine(other: Self)
-> Self}` ranges over every future type with such a method (F-bounded, W10).

## 3. Surface syntax

```
extension AddY[Self has {x: Nat}, Super has {x: Nat}](self: Self, super: Super) -> Super with {y: Nat}:
  extend(super, {y: 2n * self.x})

spec Heavier[Self has {weight: Nat, heavier(other: Self) -> Self}, Super has {weight: Nat}]:
  def heavier(other: Self) -> Self:
    if other.weight <= self.weight then self else other

spec Twice[Self has {}]:                      # requires lines extend the Self bound
  requires review(value: Nat) -> Nat
  def twice(value: Nat) -> Nat:
    self.review(self.review(value))
```

- Binder list `[Self has R, Super has R']` after the declaration name. `Self` and
  `Super` are the only binder names in edition 1. An omitted `Super has` means `Super
  has {}` (the template reads nothing through `super`). A row `R` is the record-type
  syntax already accepted by `sourceType`, with method signatures allowed and `Self`
  allowed inside it (F-bounded).
- Type former `Super with {f: T, ...}`: the row `Super` overlaid by the listed fields
  (Core4 `overlay`; the tail `Super` is retained). Only in an open declaration's result.
- A spec with a binder list has no `for T`; its provided type is `Super with {defs}`.
- `Specification<T, I>` and `Extension<T, I>`: a closed specification/extension whose
  final self is `T` and whose inherited type is `I` (provided `T`). `Specification<T>`
  stays `Specification<T, T>`.
- Records may name themselves (D6).

## 4. Typing rules

Notation: `Δ` is the rigid context `{Self ≥ R_S, Super ≥ R_I}`; `≥` is "supports"
(`Ty.supports`: every field of the bound is present in the actual type with exactly the
bound's member type, and the actual is a row).

### 4.1 Declaration (template check, once)

```
Δ = {Self ≥ R_S ∪ requires ∪ defs, Super ≥ R_I}       (rigid)
Δ; self: Self, super: Super ⊢ body : Super with {defs}
---------------------------------------------------------------- (T-Decl)
template S : ∀ Self ≥ ..., Super ≥ R_I. Self → Super → Super with {defs}
```

The check is the Core4 checker with `rigid = [Self, Super]`. Inside it, `self.m` and
`super.m` look up through the bounds only, so a body that uses a member it did not
declare is refused here, at the declaration, naming the template (the "checked ONLY
against declared assumptions" obligation). `extend(super, {...})` has type
`overlay {...} Super`: unrelated inherited structure is carried in the tail, never
dropped and never inspected.

A closed `spec S for T` is the template with `Self := T` fixed and `Super ≥ {m: T.m |
super.m ∈ S}` (D3).

### 4.2 Instance

```
template S : ∀ Self ≥ B_S, Super ≥ B_I. ...      σ = {Self ↦ A_S, Super ↦ A_I}
A_S ≥ B_S[σ]    A_I ≥ B_I[σ]    A_S, A_I shareable
--------------------------------------------------------------------- (T-Inst)
S@σ : A_S → A_I → (Super with {defs})[σ]
```

`B_S[σ]` substitutes inside the bound: that is how `heavier(other: Self) -> Self`
becomes `heavier(other: Node) -> Node` at `Node` (W10), and why the instance's member
must match exactly.

### 4.3 Composition and closing

`compose(L1, ..., Ln)` under a known final self `T` and inherited type `I_0`:

```
I_0 = type of the seed (or the I of an expected Specification<T, I>)
for k = 1..n:   σ_k = {Self ↦ T, Super ↦ I_{k-1}}
                I_{k-1} ≥ B_I(L_k)[σ_k]     else refused (inherited-unprovided): L_k reads m
                T ≥ B_S(L_k)[σ_k]           else refused (requires-unprovided) / (requires-signature)
                I_k = canonical(provided(L_k)[σ_k])
fix(compose(...), seed) : T   requires   I_n = T (canonical)
                                         else refused (requires-unprovided): the members of T
                                         no layer and no seed provides, with who requires them
```

Where `T` comes from: an expected type (`fix(...) : T` by annotation of the enclosing
definition, or `Specification<T, I>`), else the unique closed final self among the
layers (a closed spec's `for T`, a closed extension's `self: T`), else `refused
(self-undetermined): annotate the target`. Two closed layers with different selves are
the existing type disagreement (C09 stays refused: a closed annotation is closed).

Assumption reconciliation is this chain: a composition never merges bounds
symbolically; it discharges each layer's bounds at the one place every type is known.
A `compose` that is not under a known `T` (bound by `let` with no annotation, passed as
a value) is closed at `Specification<T, T>` from the declared types of its operands, the
current rule.

### 4.4 Records

`record R:` whose fields mention `R` resolves to alias variable `k` with bound the
row (exactly like a recursive `sum`); values are built by `{...}` and converted by the
existing one-head unfold. W04's `leaf().combine(leaf()).weight = 2`.

## 5. Elaboration

1. Parser: binder list, `with` rows, `Specification<T, I>`/`Extension<T, I>`, record
   self-reference. New AST fields; the front-end identity changes (re-emit).
2. Templates table in `St`: per open declaration, its rigid bounds, its body ATerm with
   annotations over rigid variables, and its template check result (`checkTemplate`,
   run once; a refusal names the declaration).
3. Instantiation context: `fix` and expected-type positions carry `(T, I_0)` into
   `compose`; the chain of section 4.3 is computed there with named refusals.
4. Instances are knot fields `M.S@<sha256 of the canonical σ JSON>`, memoized, so
   `compose(A, A, A)` and two uses at one σ share one instance and the term stays linear
   in the source (the existing COMPOSE SHARING assertion extends to instances).
5. Annotation substitution: each lambda/injection annotation of the template gets
   `Ty.instantiate σ`; then the existing `annotate`/`proposalJson` path, no new wire.
6. `SpecMeta` (LT1) gains nothing: an instance's metadata is the template's
   `declared` record; the interface label records the binder rows.

## 6. What the safety theorems become

The demand-machine theorems and `ObjectiveBendFrontEndAdequacy.accepted_never_refused`
are unchanged in statement and proof: the front end still emits a closed Core4 program
and accepts it only when `check` returns a derivation (D1, D2: no rigid variable is
ever in an emitted program).

New obligations, in `Theory/ObjectiveBendTemplates.lean` (a `Theory.ObjectiveBend*`
module: the statement snapshot and axiom pin re-pin):

- `sameType_rigid_nil`: with `rigid = []`, `sameType` is today's `sameType` (rfl), so
  every existing lemma transfers.
- `canonical_instantiate`: `(τ.instantiate σ).canonical = (τ.canonical.instantiate
  σ).canonical`. The shadowing case (a tail instantiated with a row that repeats a listed
  field: an override, e.g. Augmented's `review`) is the main proof risk; `overlay` puts
  the overriding field first and `insertCanonical` keeps the first, so the two sides
  agree, but this is the lemma to spike first.
- `infer_instantiate`: if `infer Δ ann ctx pos fuel t = some r` under rigid bounds and
  `σ` discharges them (each `σ k ≥ bound[σ]`, shareable), then
  `infer {rigid := []} (σ ∘ ann) (ctx[σ]) pos fuel t = some r'` with `r'.type =
  r.type.instantiate σ` up to `canonical`. Operational, by induction on `fuel` mirroring
  `infer`: the `get`/`extend`/`inject` cases use `supports` (lookup equality and
  `isRow`); the conversion cases use `canonical_instantiate`; the `mix`/`fix` exact
  equalities hold because the elaborator annotates every layer of a chain with the same
  `σ`-images (section 4.3), which is also why instances are canonicalized.
- `instance_accepted` (front end): a template accepted by `checkTemplate` plus a
  discharge the elaborator computed is accepted by `check` in the emitted program. So
  every refusal after a successful template check is one of the named discharge
  refusals of section 4.3, never an anonymous "typing refused" from inside a template:
  the modularity theorem, stated on the real checker.
- Inhabitants by `native_decide` + `#assert_compiled` (W05, W09b, W10 accepted; W06,
  W07 refused with their names), and a planted fault: drop the `supports` check in the
  discharge and `instance_accepted` must fail to build.

## 7. Acceptance (each a pinned probe row)

| row | target |
|---|---|
| W04 | `record Node` self-reference accepted, `two() = 2` |
| W05 | review example with seed `{}`: `twiceOfThree() = 7` (no placeholder) |
| W06 | `refused (requires-unprovided): missing ...` |
| W06b | still accepted, answers 0 (seed discharges) |
| W07 | `refused (requires-signature): Twice requires review(value: String) -> Nat; Target.review is (value: Nat) -> Nat` |
| W09b | yesterday's AddY at XYZW without edits: `wOfFive() = 11` |
| W10 | F-bounded `heavier` closed at Node and ColoredNode: `pick() = 12` |
| C09 | stays refused (closed annotations stay closed) |
| W01-W03, R01, R02, controls | unchanged |

Plus the existing cohorts unchanged (preview, examples, tutorial), and `fix` with a
whole-`T` seed of every existing program elaborating to the same core term except for
instance field names.

## 8. Order of work and cost

Dominant term: `infer_instantiate` (one induction over the cases of `infer`, the
conversion and shadowing cases are the hard ones). Cheapest spike: `canonical_instantiate`
alone, then the `get`/`extend` cases on a two-field example. Elaboration (sections 3-5)
is mechanical by comparison and can run in parallel once the AST is fixed. D3 (closed
specs with open `Super`) is independently landable first and turns W05, W06, W07 green
with the smallest change; D6 (recursive records) is independent of everything and
turns W04 green.

Interactions: OB1/LT3 (surface semantics) will need the template/instance distinction
in its `Lowers` relation (lower an instance as the template's lowering under σ); LT6
(laws) checks a law at each instance's types; LT5 (ecosystem) needs D1's instances
across package roots, which this design does not yet address.
