# Modular typing: design record

Why Objective Bend types specifications the way it does (OB-LTUO row LT2). The rules as a
user meets them are in [the overview](../OBJECTIVE-BEND.md#modular-typing); every program
named here is a row of `tests/objective-bend-source/ltuo/probe-cohort.json`, pinned at its
current outcome.

## 1. The problem

Faré's chapter 8 separates typing an extension against one already-known complete context
("trivial non-modular types", ltuo §8.2.1) from typing it against only what it uses, so it
survives collaborators that did not exist when it was written. The first front end did the
former: `spec S for T` typed both `self` and `super` as the whole `T`, so a one-method spec
needed a whole-`T` seed (W05), `requires` was a string nobody compared (W06, W07), a record
could not name itself (W04), and an extension written for three fields could not be reused at
four (W09b). Core4 already had the ingredients: bounded variables that keep row tails,
`Ty.supports` as lookup-based width checking, heterogeneous `mix`, `Ty.instantiate`. What was
missing was an authored binder, a discipline that checks an extension against its binder
alone, and a closing rule that discharges the binder at `fix`.

## 2. Decisions

**D1. Instantiation, not polymorphic Core4 terms.** An open declaration is a *template*,
checked once against its bounds with `Self` and `Super` rigid; every use is an *instance*
with the actual final self and inherited types substituted. The emitted program contains only
instances, so it is an ordinary closed Core4 program. A core `forall` would add a case to every
machine preservation proof; with templates the machine theorems keep their statements and
proofs, and the new obligation is one checker-level theorem. Cost: code grows with the number
of distinct instances (memoized), and an open template is second-class (a parameter can be any
closed `Extension<T>`, not "any extension over `Self has {x}`").

**D2. Rigid variables are not aliases.** An ordinary bounded variable (the global knot,
recursive sums) is equal to its bound. A template's `Self` is a lower bound: the instance
supports it, it is not equal to it. `Assumptions.rigid` lists rigid indices, and conversion
never unfolds one (`Assumptions.alias` is `none` for it), while lookups still read members
through the bound. With `rigid = []` the checker is the old checker
(`Assumptions.alias_of_rigid_nil`), so nothing emitted is affected.

**D3. Closed specs get an open inherited row.** `spec S for T` keeps `self : T` but types
`super` at the members `S` reads through it. This alone makes the partial seed (W05) work and
every whole-`T` seed still discharge.

**D4. `requires` is the Self bound, and it is checked.** In a closed spec each
`requires m(...) -> R` must equal `T`'s member exactly (`requires-signature`, W07).

**D5. `fix` discharges.** `fix(compose(L1, ..., Ln), seed)` types the chain bottom-up from the
seed; the final row must be the target. A missing member is `requires-unprovided` naming who
requires it (W06); a `super.m` with nothing below is `inherited-unprovided`. A seed that
provides a member discharges a requirement for it (W06b): that is inheritance from the seed.

**D6. Recursive records are nominal**, through the bounded-variable machinery of recursive
sums (W04). This is distinct from the F-bounded binder: `Node` is one closed recursive type;
`Self has {combine(other: Self) -> Self}` ranges over every future type with such a method
(W10).

## 3. Surface

```text
extension AddY[Self has {x: Nat}, Super has {x: Nat}](self: Self, super: Super) -> Super with {y: Nat}:
  extend(super, {y: 2n * self.x})

spec Heavier[Self has {weight: Nat, heavier(other: Self) -> Self}, Super has {weight: Nat}]:
  def heavier(other: Self) -> Self:
    if other.weight <= self.weight then self else other
```

`Self` and `Super` are the only binder names; an omitted `Super has` is `{}`; a bound may
mention `Self`; `requires` lines join the Self bound. `Super with {f: T}` is `Super` overlaid
by `f`, keeping the tail. A spec with binders has no `for T`.

## 4. Typing rules

- **Declaration** (once): the body is checked by the Core4 checker under
  `Self ≥ R_S ∪ requires ∪ defs`, `Super ≥ R_I`, with `Self` rigid, in the knot context; a
  read outside the bounds is refused at the declaration (`self-unbound-member`,
  `inherited-unprovided`), and a use that only an alias would accept is `self-rigid`.
- **Instance**: at substitution σ = {Self ↦ A_S, Super ↦ A_I}, require `A_S ≥ B_S[σ]` and
  `A_I ≥ B_I[σ]`; substituting inside the bound is how `heavier(other: Self) -> Self` becomes
  `heavier(other: Node) -> Node`.
- **Chain**: for k = 1..n, σ_k = {Self ↦ T, Super ↦ I_{k-1}}, discharge both bounds,
  `I_k = canonical(provided(L_k)[σ_k])`; `fix` requires `I_n = T`. `T` comes from the closed
  layers (all equal, else `self-conflict`), else the expected type, else `self-undetermined`.
  Bounds are never merged symbolically: each layer is discharged where every type is known.

## 5. Elaboration

Each open declaration's knot field is checked once (`checkTemplates`); each use in a chain is a
memoized knot field `M.E@i` holding the layer re-elaborated at its instance, so repeated uses
at one substitution share one field and the term stays linear in the source. No new wire: an
instance's annotations go through the ordinary typing proposal, and its metadata is the
template's `declared` record.

## 6. Theorems and status

Built: D1-D6 in `Compiler/ObjectiveBendElaborate.lean` (`chainFix`, `layerAt`,
`checkTemplates` run by every lowering). Proved in `Theory/ObjectiveBendTemplates.lean`:
`canonical_instantiate`; `Discharges.infer_instantiate` and `Discharges.check_instantiate` (an
accepted template is accepted at a discharged instance, at the instantiated type, same uses,
with `extra` fuel; `extend`'s row check reads `isRow` at `fuel + 64` for this reason);
inhabitant `coloured_discharges` / `coloured_instance_accepted`; tooth
`self_as_bound_row_alias_accepted` / `self_as_bound_row_rigid_refused`.

Open:

- **`instance_accepted`.** Since GPT-6 row D, `Super` in a template is a second rigid bounded
  variable (`super-rigid` refuses a use of `super` as its bound row), and chainFix EMITS each open
  instance as `ATerm.instantiate σ template` from the one cached `templateLayer` that the knot field
  holds and `checkTemplates` checks. So the square holds at the term level by construction. What
  is still open is the theorem composing it with `Discharges.check_instantiate`, which needs the
  PTy→Ty proposal translation to commute with substitution and canonicalization (cv 01a115d6-7ee9).
  Meanwhile every instance is still re-checked in the whole program, which is sound.
- **Composition contract.** `Compiler/ObjectiveBendContract.lean` is the contract algebra that
  chainFix runs (`run_append`: C_{A;B}(S,I) = C_A(S,I) ∧ C_B(S, F_A(S,I))). Per-operation
  constraints: add (absent beneath), override (same type), and a type change is `replace-undeclared`.
- **Staged modularity.** An open declaration is checked once against its bounds alone, then linked
  by `compose` + `fix` before closed Core4. Nothing below Core4 sees an open term: the checker
  and machine receive a closed program.
- Ancestry specs and non-plain operands in a partial-seed chain keep the whole-target rule.
- Instances across package roots (LT5).
- Laws checked at each instance's types (LT6); the `Lowers` relation of a surface semantics
  must lower an instance as the template's lowering under σ (LT3).
