/-
# Loom — the proof system.

Import-boundary-checked: Loom/ may import only Mathlib, Theory, and Loom
(`scripts/check-import-boundary.sh`).
-/
import Loom.Statements  -- OB-2 / OB-6 statements, statement-first
import Loom.CorrelatedAgreement  -- OB-6 realized: mutual correlated agreement at unique decoding (WHIR Lemma 4.10), proved
import Loom.ReedSolomon  -- RS instantiation: Cor 4.11's UD shape (exact min distance; Thm 4.8 stays a hypothesis)
import Loom.Rbr         -- RBR knowledge-soundness vocabulary (WARP §4 + App. B); [OB-2] depth composition stated
import Loom.Depth       -- [OB-2] audit: as-stated REFUTED (Z = ∅ corner); [OB-2′] repair + Thm B.4 tower (B.5 extractor, Claim B.6, fresh-slot bound) modulo one named seam [OB-2a]
import Loom.Sumcheck    -- sumcheck soundness: single-round root-counting (reuses ReedSolomon), v-round union bound (reuses uniformProb toolkit); fully-adaptive case is [OB-SC]
