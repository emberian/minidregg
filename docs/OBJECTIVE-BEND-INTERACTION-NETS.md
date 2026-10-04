# Objective Bend on interaction nets — design note (NOT a backend)

Status: **design only, authored**. Nothing in this note is implemented, compiled
or claimed. Lane W3.BACKENDS, 2026-10-04. The verdict and its sources are in
the lane's BACKENDS-ASSESSMENT.md §(b); this note records what an encoding would
be, what it must prove, and the programs that would refute it first.

## Why it is not a backend today

- **Open recursion is outside the fragment where oracle-free optimal reduction
  is sound.** `mix` continues with `λself.λsuper. upper self (lower self super)`:
  `self` is duplicated into two extensions; `fix` ties `self` to a spec that
  duplicates it. A duplicated lambda whose copies duplicate each other is
  exactly the shape HVM documents as undefined behaviour (hvm 1.0.20-beta
  `guide/HOW.md:742-811`; HVM2 paper §"unsound"); the soundness theorem for the
  oracle-free algorithm covers EAL/LAL-typable terms only (Baillot–Coppola–Dal
  Lago, arXiv 0704.2448).
- The CUDA runtime (HVM2) is eager: `LazyUnusedArgument` and `LazyUnusedField`
  (tests/objective-bend-source) would not terminate.
- A partially reduced net has no readback to a Core4 `State`, so a suspended
  run cannot migrate; Core4 States do (the C backend's resume cases).

## The encoding, if a typed fragment ever admits it

Target: the interaction calculus with labelled DUP/SUP (HVM3/HVM4 lazy mode),
not interaction combinators (HVM2 has one unlabeled DUP).

| Core4 | Net |
|---|---|
| `lam b` | LAM node; the binder's uses go through one DUP tree per extra use |
| `app f a` | APP node; `a` is a sub-net, not a heap cell — sharing comes from DUP, not from an update frame |
| `bound i` | wire to the binder's (possibly duplicated) port |
| `fix s i` | a recursive global reference expanded lazily (REF), never an inline knot |
| `mix l u` | inline `λself.λsuper. u self (l self super)`: a DUP on `self` with a **fresh dynamic label per unfolding** |
| `record fs` / `get` | a constructor node per field; `get` = a projection rule; fields stay unreduced sub-nets |
| `specification` / `prototype` / `reflect` / `metadata` / `project` | two-field constructors and their projections |
| `nat` / `binary` | numeric nodes + OP2; unbounded naturals have no native IN representation (HVM numbers are 24/32/60-bit) and would need a bignum constructor encoding |
| `inject` / `case` / `ifBool` | constructor + MAT/SWI |

What has no image:

- **Blackholing.** A thunk that demands itself is a vicious circle, a redex
  that never fires. Core4 observes `divergent address`. An IN backend would
  need a separate cycle detector over the net, with its own adequacy theorem.
- **Ticks.** One Core4 tick is one `stepRaw`. An interaction is a different
  unit. Interaction counts are deterministic (strong confluence), so they can
  carry a tariff, but a conversion to the `Limits`/tick tariff is a theorem.
- **Yield.** Strong confluence gives no evaluation order, so a yield is only
  well placed at the top of a run (HVM2 IO: normalise, read back `IO_CALL`).
  Yields inside shared forced thunks must be excluded by typing before this
  backend could be used. Core4 already forbids effects inside a forced shared
  thunk; the IN backend needs that rule to be a theorem, not a convention.

## The refinement obligation

For the typed fragment `F` the encoding admits:

  `∀ t ∈ F, ∀ v, (∃ n, runBounded L n (initial t) = .finished v _) ↔
     normal form of ⟦t⟧ reads back to an observation of v`

restricted to ground observations (Nat, Bool, label). For a non-ground value,
readback of partially shared nets is the hard part of optimal reduction, and
no statement is proposed. The proof needs:

1. `F` defined by a stratification (EAL-like levels for `fix`/`mix`).
2. Soundness of oracle-free reduction on `F`, a port of Baillot–Coppola–Dal Lago.
3. Adequacy of ⟦·⟧ against the CBN reference `Step`. Core4 already relates
   `Step` to `runBounded` (`runBounded_natural_sound` and its relatives).

Size: a Core4→IC compiler is about 1.5–3k lines. (1) and (2) are research.

## First discriminating programs (in the surface language)

1. **A shared thunk forced twice must evaluate once, in both machines.**

   ```
   def double(x: Nat) -> Nat:
     x + x
   def work(n: Nat) -> Nat:
     match n:
       case 0n: 1n
       case 1n+p: work(p) + work(p)
   def once() -> Nat:
     double(work(10n))
   ```

   Call-by-need forces the argument thunk `work(10n)` once and reads the
   cached value the second time. Optimal reduction also shares it. A naive-copy
   IN encoding does the work twice: twice the cost, the same answer. The
   answer cannot see the difference; only the cost can.
   Observable cost: Core4 ticks against interactions. Both must equal the
   single-evaluation count under the declared conversion.
   (`native/objective-emit/Stress.obend` `sharedWork` is the iterated form;
   `tests/objective-bend-source/LazySharedField.obend` is the record form.)

2. **Open recursion through `mix`** — `EvenOdd.evenTen`
   (`fix(compose(Even, Odd), …).even(10n)`). This is the shape outside EAL.
   An encoding without per-unfolding labels must be shown to give the wrong
   answer here. That is the falsifier that labels are needed.

3. **Laziness** — `LazyUnusedArgument.result` must be `7` (HVM2 eager: hangs).
