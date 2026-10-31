/-
# Effects — the open handler registry (ATLAS §7).

The derivation engine: Kernel and Compiler consume what it derives, so it imports only
Mathlib, Lean core and Theory (`scripts/check-import-boundary.sh`). Its keystones over the
deployed kernel (the content, prepare, host-teeth, commuting and activity proofs) and its
first declaration (`moveEffect`) are consumers and live under `Kernel/` (`Kernel.lean`).
-/
import Effects.Placeholder  -- carve marker: the REMAINING registry carve — full declaration vocabulary (view/touched/guard AST/δ/authority, floor obligations as proof fields), the open registry + dispatch, the weld to the emit path, frame/reject teeth, the witness generator — [EFFECT-registry]
import Effects.EffectSpec  -- the DERIVATION ENGINE: EffectSpec (Op + State + sem) → derive : DerivedEffect (term + executor + descriptor, laws as PROOF FIELDS) — executor-equality (derived_agrees/executor_unique) + descriptor-faithfulness (descriptor_faithful) FREE by initiality (Theory.Signature REUSED, zero induction at use sites); its first declaration, moveEffect over Kernel.move, is a consumer: Kernel/MoveEffect.lean
import Effects.Revival.EngineProofs  -- the engine and completeness keystones PROVED, with every satisfiable/teeth/premise witness of the two-entry pole (kernel-free closure)
