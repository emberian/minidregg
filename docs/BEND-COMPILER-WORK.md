* **Objective front end.** One program, in Lean: parser, elaborator, C4 linearization and
  the capture, preview and publication commands (`Host/ObjectiveBendFrontEnd.lean`;
  [front end](OBJECTIVE-BEND-FRONTEND.md)). The TypeScript front end was ported, translation
  validated and deleted on 2026-10-04, and the receiver re-runs the Lean one on every
  package. A trusted boundary remains: there is no surface semantics, so no theorem states
  that the core means what the source means. Open: `requires` is carried and never checked;
  `before` and `after` methods are refused; `- < <= > >= /` lower to a package prelude and
  cost O(value) machine steps; no surface form names another package's root.
* **Core constructors.** Sums with case, and the Plan-yielding activity, have landed. Open:
  checked `requires`, a guardedness check on self-calls under a perform, dynamic `get`.
  Ranked with costs in the language guide.
* **Numeric and circuit specialization.** None on main. The natural-number,
  Boolean-logic and FHE specializations of the upstream Bend kernel were deleted
  on 2026-10-04 (Git history keeps them). Re-deriving them from the demand
  machine's `stepRaw` is open work; their grammar was input/literal/add over
  public source and private bounded Nat inputs, with no-wrap integer bounds.
* **Plan mapping.** The Objective route lowers a result through four output adapters
  (scalar Plan, result atom, combined, generic; `Output`,
  `Kernel/ObjectiveBendNativeAdmission.lean:191`) and requires the Plan's effects to equal the
  command's (`Output.exact`, `:219`).
* **Metering.** The Objective path is priced by one public tariff over the declared capacity
  envelope (`Kernel/ObjectiveTariff.lean`): native admission requires the claim's `proofWork` to
  equal the tariff's price of its envelope (`tariffExact`,
  `Kernel/ObjectiveBendNativeAdmission.lean:468`) and the activity kernel prices every turn by it.
  Open: a storage charge for published packages and checkpoints (lane RETENTION-PAYERS).
