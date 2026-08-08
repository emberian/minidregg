/-
# Theory — the candidate-independent core (ATLAS §7).

Everything here must be the metatheory of *any* system built this way: abstract
parameters only, no imports outside Mathlib + Theory itself (enforced by
`scripts/check-import-boundary.sh`).
-/
import Theory.Knowledge  -- the verify/find seam: Verifiable/Discharged/Searchable, Claim/Holds/Knower
import Theory.BinaryTower  -- [OB-8-tower] the GF(2) binary-tower field substrate (Binius path)
import Theory.BinaryTowerFanPaar  -- [BTOWER-fanpaar] the Fan–Paar generator recursion + fast tower multiplication
import Theory.BinaryTowerTrace  -- [BTOWER-fanpaar-basis] CLOSED (Wiedemann trace induction) — FanPaarRecursion holds
import Theory.AdditiveNTT  -- [BTOWER-additive-fri] additive domains + subspace-vanishing (GF(2)-linear) + novelpoly basis + the additive FRI fold; residuals [ANTT-transform]/[ANTT-fri]
import Theory.AdditiveNTTTransform  -- [ANTT-transform] CLOSED (the additive NTT is a linear bijection); [ANTT-fri] REDUCED to the additive proximity gap [ANTT-proximity] (exact regime PROVED, b = 1)
