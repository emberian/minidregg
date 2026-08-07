# GOAL — mutually elaborate minidregg + Loom to a green-audited v0 slice

**North star:** OB-3, the kill-checkpoint — a turn's receipt claim Q is NATIVE to the
Loom accumulator (the light-client object IS the Q-chain, not a SNARK of a VM). v0 =
a coherent slice: kernel turn → receipt Q → Loom link-accumulation stating whole-history
soundness, all green + audited.

**Discipline:** statement-first; a keystone is not landed until satisfiable + teeth +
premise-inhabitation are BUILT in Lean (OB-2 was refuted for lack of this). I author
statements; swarm proves/ports; I audit every lane by hand (axioms + non-vacuity) before
integrate+push. origin/main stays green; Theory/ boundary clean.

## Current thrust
Build the kernel spine the receipt needs (state → hyperedge turn → Q), while closing
Loom's depth seam (OB-2a) and standing up the sumcheck front — so OB-3 has both a Q to
encode and an accumulator to encode it into.

## Next 3 moves
1. Fan out the kernel spine: `Kernel/State.lean` (cells + bal + caps + one keyed map,
   ATLAS §7) and `Kernel/Turn.lean` (the hyperedge wide-pullback + its 3 negative
   theorems, from breadstuffs Hyperedge.lean).
2. Fan out `Loom/Sumcheck.lean` (the arithmetization front — sumcheck soundness) and push
   OB-2a (the game-slot lazy-rnd resolver) toward closing the depth theorem.
3. Author N2 (hyperedge-as-limit) once the turn structure lands; then design the Q →
   CRS-claim encoding (OB-3) against the landed turn + Loom's accumulated-claim shape.

## Kernel spine COMPLETE (green, 1973 jobs)
Camera (substances) + State (ledger + Σ-conservation, audited) + Turn (hyperedge,
audited) — the substrate N2 and OB-3 both need. Next: N2 (hyperedge-as-limit),
then Receipt Q → OB-3 encoding.

## In flight (wave 2, bounded/mathlib-only to dodge the stall)
- `Loom/Sumcheck.lean` — round-by-round soundness (reuse RS card_agreeSet_lt_of_ne)
- `Kernel/TurnLimit.lean` — N2a (hyperedge-cone = wide pullback), statement-first

## Next (fresh focus)
- Audit + wire wave-2 lanes; author N2b (balanced-limit category, designed in
  docs/N2-HYPEREDGE-LIMIT §1); Receipt Q (Kernel) → OB-3 encoding (the checkpoint).

## ⚠ Finding: subagent stream-watchdog stalls (2026-08-07 eve)
2 of 3 wave-1 lanes died at "no progress 600s (stream watchdog)" mid-large-file
read — a systemic subagent-stream issue tonight, not content. Strategy under it:
the station does load-bearing lanes BY HAND (Turn done so), fans out only when
the stream recovers. Not owner-blocking; a workaround, noted so the pattern is
visible if it persists.

## Awaiting-wire
- `Kernel/Turn.lean` — landed by hand, axiom-clean, NOT yet in Kernel.lean (a
  live State lane holds that shared root); wire Turn+State together once State lands.

## Done-log
- 2026-08-07 OB3-RECEIPT-ENCODING.md — the kill-checkpoint design: Q as a native
  accumulated claim, PASS/FAIL criteria + candidate failure sites. Target for OB-3 fixed.
- 2026-08-07 keystones green+audited on main: OB-6 (MCA@UD, +paper typo), Camera (4
  substances=1 Fpu), N3 (fold_unique — syntactic leaves forced), Reed-Solomon (Cor 4.11),
  OB-2 depth tower (as-stated REFUTED; repaired modulo OB-2a), Pred (the one algebra).
- 2026-08-07 helm macOS: gate-bind + port-owner /proc fallbacks (tested, PR #1).
