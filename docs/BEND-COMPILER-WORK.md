# Sustained compiler work

This tracker records receiving capabilities, not fixture counts. Objective Bend
Core4 is the only Bend language; see [Objective Bend](OBJECTIVE-BEND.md).

* **Objective front end.** The parser, capture and elaborator are TypeScript
  (`native/bend-source/objective-*.ts`) and are a trusted boundary. Defects to fix
  first: `compose` copies its operands syntactically into both the metadata and
  the `mix`, so term size grows as 2^k in the number of composed specifications;
  `literalAnnotations` throws for any package declaring a `spec`, so such packages
  cannot reach the typed preview; `!= < > <= >= || - /` parse but are refused at
  elaboration; the front end cannot emit affine or linear quantities; `./NAME.bend`
  imports are still accepted. Then: a Lean-side elaborator or a checked
  translation-validation statement.
* **Core constructors.** Sums with case (which gives a Boolean branch), a
  Plan-yielding activity, checked `requires`. Ranked with costs in the language
  guide.
* **Numeric and circuit specialization.** None on main. The natural-number,
  Boolean-logic and FHE specializations of the upstream Bend kernel were deleted
  on 2026-10-04 (Git history keeps them). Re-deriving them from the demand
  machine's `stepRaw` is open work; their grammar was input/literal/add over
  public source and private bounded Nat inputs, with no-wrap integer bounds.
* **Plan mapping.** The Objective route is `Kernel/ObjectiveBendPreparedOutput`
  to `Compiler/ObjectiveBendPlanAdapter` (scalar writes only).
* **Metering.** The Objective path is not priced: `PreparedOutput.Usage` has no
  consumer and no link to fee preparation, and the tick bound in the proofs is
  not the number anyone charges. A public cost law over a fixed capacity envelope
  is required before native admission charges for Objective work.

