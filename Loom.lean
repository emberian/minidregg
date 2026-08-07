/-
# Loom — the proof system.

Import-boundary-checked: Loom/ may import only Mathlib, Theory, and Loom
(`scripts/check-import-boundary.sh`).
-/
import Loom.Statements  -- OB-2 / OB-6 statements, statement-first
import Loom.Rbr         -- RBR knowledge-soundness vocabulary (WARP §4 + App. B); [OB-2] depth composition stated
