/-
# Assurance.ZkmlMatmulChecker — a versioned fail-closed byte checker

This is the first runnable checker boundary for the tiny 2×2 F7 contraction.
The byte envelope carries only neutral candidate data: exact suite/checker/
statement/planning/request identities, two canonical field matrices, and a
candidate output.  It carries no authority, acceptance bit, policy, proof, or
continuation.

Lean owns parsing and the decision.  The decoder rejects wrong length, magic,
codec version, and non-canonical field bytes.  The checker then binds every
identity and recomputes the matrix contraction.  Only the successful branch
constructs `CheckedCandidate`, whose `outputExact` field is the semantic fact
later evidence consumes.

This checker is intentionally exact recomputation over F7.  It is a runnable
versioned predecessor of the succinct BabyBear/BaseFold checker, not a claim
about native refinement or production cryptographic soundness.
-/

import Assurance.ZkmlMatmulSumcheck

namespace Minidregg.Assurance.ZkmlMatmulChecker

set_option autoImplicit false

abbrev F := ZMod 7
abbrev Cells := Fin 4 → F

structure ExpectedProfile where
  codecVersion : UInt8
  suiteId : UInt8
  checkerId : UInt8
  statementId : UInt8
  planningArtifactId : UInt8
  requestId : UInt8
  deriving DecidableEq, Repr

/-- Neutral decoded bytes.  In particular, there is no `accepted : Bool`. -/
structure Candidate where
  codecVersion : UInt8
  suiteId : UInt8
  checkerId : UInt8
  statementId : UInt8
  planningArtifactId : UInt8
  requestId : UInt8
  left : Cells
  right : Cells
  output : Cells
  deriving DecidableEq

inductive Failure where
  | malformedLength
  | badMagic
  | unsupportedCodec (actual : UInt8)
  | nonCanonicalField
  | suiteMismatch
  | checkerMismatch
  | statementMismatch
  | planningArtifactMismatch
  | requestMismatch
  | wrongOutput
  deriving DecidableEq, Repr

def expected : ExpectedProfile where
  codecVersion := 1
  suiteId := 101
  checkerId := 102
  statementId := 103
  planningArtifactId := 104
  requestId := 105

def cells (a b c d : UInt8) : Cells :=
  ![(a.toNat : F), (b.toNat : F), (c.toNat : F), (d.toNat : F)]

def cellIndex (row column : Fin 2) : Fin 4 :=
  ⟨row.val * 2 + column.val, by omega⟩

def rowOf (index : Fin 4) : Fin 2 :=
  ⟨index.val / 2, by omega⟩

def columnOf (index : Fin 4) : Fin 2 :=
  ⟨index.val % 2, Nat.mod_lt _ (by omega)⟩

def at (matrix : Cells) (row column : Fin 2) : F :=
  matrix (cellIndex row column)

/-- Literal row-major `2×2 · 2×2` contraction. -/
def contraction (left right : Cells) : Cells :=
  fun index => ∑ inner : Fin 2,
    at left (rowOf index) inner * at right inner (columnOf index)

def canonicalFieldPayload (bytes : List UInt8) : Bool :=
  bytes.all fun byte => decide (byte.toNat < 7)

/-- The exact v1 envelope:

`MM || version || suite || checker || statement || plan || request || A4 || B4 || C4`.
-/
def decode : List UInt8 → Except Failure Candidate
  | [magic0, magic1, version, suite, checker, statement, plan, request,
      a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3] =>
      if magic0 != 77 || magic1 != 77 then
        .error .badMagic
      else if version != 1 then
        .error (.unsupportedCodec version)
      else if !canonicalFieldPayload
          [a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3] then
        .error .nonCanonicalField
      else
        .ok
          { codecVersion := version
            suiteId := suite
            checkerId := checker
            statementId := statement
            planningArtifactId := plan
            requestId := request
            left := cells a0 a1 a2 a3
            right := cells b0 b1 b2 b3
            output := cells c0 c1 c2 c3 }
  | _ => .error .malformedLength

/-- Proof-bearing output constructed only by Lean after all executable checks. -/
structure CheckedCandidate (profile : ExpectedProfile) where
  candidate : Candidate
  codecExact : candidate.codecVersion = profile.codecVersion
  suiteExact : candidate.suiteId = profile.suiteId
  checkerExact : candidate.checkerId = profile.checkerId
  statementExact : candidate.statementId = profile.statementId
  planningArtifactExact :
    candidate.planningArtifactId = profile.planningArtifactId
  requestExact : candidate.requestId = profile.requestId
  outputExact : candidate.output = contraction candidate.left candidate.right

/-- Parse, bind every identity, and recompute.  Every failure is explicit and
no supplied bit can skip a check. -/
def check (profile : ExpectedProfile) (bytes : List UInt8) :
    Except Failure (CheckedCandidate profile) := by
  match hdecode : decode bytes with
  | .error failure => exact .error failure
  | .ok candidate =>
      if hcodec : candidate.codecVersion = profile.codecVersion then
        if hsuite : candidate.suiteId = profile.suiteId then
          if hchecker : candidate.checkerId = profile.checkerId then
            if hstatement : candidate.statementId = profile.statementId then
              if hplan :
                  candidate.planningArtifactId = profile.planningArtifactId then
                if hrequest : candidate.requestId = profile.requestId then
                  if houtput :
                      candidate.output = contraction candidate.left candidate.right then
                    exact .ok
                      { candidate := candidate
                        codecExact := hcodec
                        suiteExact := hsuite
                        checkerExact := hchecker
                        statementExact := hstatement
                        planningArtifactExact := hplan
                        requestExact := hrequest
                        outputExact := houtput }
                  else exact .error .wrongOutput
                else exact .error .requestMismatch
              else exact .error .planningArtifactMismatch
            else exact .error .statementMismatch
          else exact .error .checkerMismatch
        else exact .error .suiteMismatch
      else exact .error (.unsupportedCodec candidate.codecVersion)

def accepts (profile : ExpectedProfile) (bytes : List UInt8) : Bool :=
  match check profile bytes with
  | .ok _ => true
  | .error _ => false

/-- The canonical fixed turn: `[[1,2],[3,4]] · [[5,6],[0,1]] =
[[5,1],[1,1]]` over F7. -/
def canonicalBytes : List UInt8 :=
  [77, 77, 1, 101, 102, 103, 104, 105,
   1, 2, 3, 4, 5, 6, 0, 1, 5, 1, 1, 1]

def wrongOutputBytes : List UInt8 :=
  [77, 77, 1, 101, 102, 103, 104, 105,
   1, 2, 3, 4, 5, 6, 0, 1, 6, 1, 1, 1]

def wrongSuiteBytes : List UInt8 :=
  [77, 77, 1, 100, 102, 103, 104, 105,
   1, 2, 3, 4, 5, 6, 0, 1, 5, 1, 1, 1]

def wrongPlanBytes : List UInt8 :=
  [77, 77, 1, 101, 102, 103, 99, 105,
   1, 2, 3, 4, 5, 6, 0, 1, 5, 1, 1, 1]

def nonCanonicalBytes : List UInt8 :=
  [77, 77, 1, 101, 102, 103, 104, 105,
   1, 2, 3, 4, 5, 6, 0, 1, 7, 1, 1, 1]

theorem canonical_accepts : accepts expected canonicalBytes = true := by decide

theorem wrong_output_refused : accepts expected wrongOutputBytes = false := by
  decide

theorem wrong_suite_refused : accepts expected wrongSuiteBytes = false := by
  decide

theorem wrong_plan_refused : accepts expected wrongPlanBytes = false := by
  decide

theorem noncanonical_field_refused :
    accepts expected nonCanonicalBytes = false := by decide

theorem trailing_byte_refused :
    accepts expected (canonicalBytes ++ [0]) = false := by decide

/-- Any accepted bytes expose the exact decoded candidate and its checked
contraction equality. -/
theorem accepts_sound {profile : ExpectedProfile} {bytes : List UInt8}
    (accepted : accepts profile bytes = true) :
    ∃ checked, check profile bytes = .ok checked ∧
      checked.candidate.output =
        contraction checked.candidate.left checked.candidate.right := by
  unfold accepts at accepted
  cases hcheck : check profile bytes with
  | error failure => simp [hcheck] at accepted
  | ok checked => exact ⟨checked, hcheck, checked.outputExact⟩

#check @accepts_sound

end Minidregg.Assurance.ZkmlMatmulChecker
