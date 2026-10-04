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
* **Numeric and circuit specialization.** `Compiler/BendNatural*`, `BendLogic*`
  and the FHE adapters specialize the retiring BendTT core. They must be
  re-targeted at the demand machine (cut point: `Compiler.ObliviousNatAdd` to
  `BendNaturalCompiler`) before they say anything about Objective Bend. Supported
  BendTT grammar was input/literal/add over public source and private bounded Nat
  inputs, with no-wrap integer bounds.
* **Plan mapping.** The Objective route is `Kernel/ObjectiveBendPreparedOutput`
  to `Compiler/ObjectiveBendPlanAdapter` (scalar writes only).
  `Compiler.BendArtifactBinding` binds BendTT Books and retires with them.
* **Metering.** The Objective path is not priced: `PreparedOutput.Usage` has no
  consumer and no link to fee preparation, and the tick bound in the proofs is
  not the number anyone charges. A public cost law over a fixed capacity envelope
  is required before native admission charges for Objective work.

Historical: the DrEX262 `Book.check` 60-second timeout and the open-reduction cache
work were BendTT checker problems; they end with that path.
