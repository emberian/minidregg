/-
# Assurance.CostModel: the cost model as a total function, with security drawn from the proven walls

`zkml-research/docs/COST-MODEL.md` established the method (2026-08-14): operation counts are the primary
instrument, a clock only calibrates the exchange rate between operation classes, and work and latency are
different units. This file lifts those counts into one total, computable function of the proof-system
knobs

  `(field, extension, blowup, queries, query grinding, commit grinding, hash, leaf width, folding arity)`

and of the relation's shape, returning field multiplications, hash permutations, queries, proof bytes and
memory traffic. Security comes from the walls this tree has already proved, with the decoding regime in
the name and the type:

* the FRI query column at unique decoding, `Assurance.TwoRegimeQueryBudget.queryErr .UDR`
  (`udrQueryErr_sq` identifies this file's rational with that file's squared error);
* the field-size wall, `Assurance.ErrorBudget` / `ErrorBudget120` (`algErr_eq_soundnessErrorPoW`
  identifies this file's rational with the real-valued `soundnessErrorPoW`);
* the FRI commit-phase term at unique decoding, `(2^a − 1)·(n + 1)/|F|` per fold round, divided by the
  commit grinding (`IR2_FRI_COMMIT_POW_BITS`, `Dregg2.Circuit.FriCommitPow`);
* the LogUp fingerprint wall, `Assurance.TwoRegimeQueryBudget.logupErr`.

They compose by the union bound. The composition of the query column with the algebraic budget is
ErrorBudget's named residual `[BUDGET-compose]`, and the PoW discount is `[BUDGET-PoW-compose]`; nothing
here claims either. The commit-phase term for arity `2^a > 2` is BCIKS20's unique-decoding curve bound; it
is proved in this tree only for lines (`Selvage.ProximityGapUD`), i.e. at `logArity = 1`, which is why the
proven configuration below folds by 2.

What the counts are, and are not:
* exact functions of the knobs, written to match the shipped Plonky3/BabyBear prover and the Tower256
  prover's kernel schedule (`zkml-research/notes/accelerator-readiness/tower256_schedule_model.py`);
* not a clock. A `Machine` turns counts into seconds through named calibration constants, and
  `Assurance.CostCalibration` holds the measured ones.
-/
import Assurance.TwoRegimeQueryBudget
import Assurance.ErrorBudget120

namespace Minidregg.Assurance.Cost

open Minidregg.Assurance

/-! ## §1 The knobs -/

/-- The base field of the committed trace. -/
inductive BaseField where
  | babyBear
  | koalaBear
  | m31
  | goldilocks
  /-- The 256-bit binary tower (Fan–Paar), minidregg's additive-FRI substrate. -/
  | tower256
  deriving DecidableEq, Repr, Inhabited

/-- `|F|` of the base field. -/
def BaseField.card : BaseField → ℕ
  | .babyBear => 2013265921
  | .koalaBear => 2130706433
  | .m31 => 2147483647
  | .goldilocks => 18446744069414584321
  | .tower256 => 2 ^ 256

/-- Bytes per base element as stored. -/
def BaseField.elemBytes : BaseField → ℕ
  | .babyBear | .koalaBear | .m31 => 4
  | .goldilocks => 8
  | .tower256 => 32

/-- The NTT family the field admits. -/
inductive NttKind where
  /-- Radix-2 Cooley–Tukey on a multiplicative subgroup (two-adic primes; M31 via the circle). -/
  | multiplicative
  /-- Gao–Mateer additive FFT on an `F₂`-subspace (binary towers). -/
  | additive
  deriving DecidableEq, Repr, Inhabited

def BaseField.ntt : BaseField → NttKind
  | .tower256 => .additive
  | _ => .multiplicative

/-- The Merkle/transcript hash. -/
inductive HashFn where
  /-- Poseidon2, width 16, over a 31-bit field: rate 8 elements. -/
  | poseidon2W16
  /-- Poseidon2, width 24, over a 31-bit field: rate 16 elements. -/
  | poseidon2W24
  /-- Keccak-f[1600] under cSHAKE256 / SHA3-256 (capacity 512): rate 136 bytes. -/
  | keccakF1600
  deriving DecidableEq, Repr, Inhabited

/-- Bytes absorbed per permutation. -/
def HashFn.rateBytes : HashFn → ℕ
  | .poseidon2W16 => 32
  | .poseidon2W24 => 64
  | .keccakF1600 => 136

/-- Digest bytes (every hash here commits to 256 bits). -/
def HashFn.digestBytes : HashFn → ℕ
  | _ => 32

/-- Base-field multiplications inside one permutation (Poseidon2-16: 564, `COST-MODEL.md`; Keccak has
none: it is bitwise). Used only to report a permutation's arithmetic, never to convert it. -/
def HashFn.mulsPerPerm : HashFn → ℕ
  | .poseidon2W16 => 564
  | .poseidon2W24 => 852
  | .keccakF1600 => 0

/-- **The proof-system knobs.** One FRI/STARK-style commitment scheme. -/
structure Params where
  field : BaseField
  /-- Challenge extension degree (BabyBear⁴: 4; Tower256: 1). -/
  extDeg : ℕ
  logBlowup : ℕ
  numQueries : ℕ
  /-- Query-phase grinding bits (`IR2_FRI_QUERY_POW_BITS`). -/
  powBits : ℕ
  /-- Commit-phase grinding bits (`IR2_FRI_COMMIT_POW_BITS`; ErrorBudget120's transcript PoW). -/
  commitPowBits : ℕ
  hash : HashFn
  /-- FRI folding arity `2^logArity`. -/
  logArity : ℕ
  /-- Elements per FRI-layer Merkle leaf, log₂ (Plonky3 groups a coset: `= logArity`; Tower256: 0). -/
  foldLeafLog : ℕ
  /-- Folding stops at a domain of `2^logFinal` points; the final polynomial is sent in the clear. -/
  logFinal : ℕ
  /-- STARK (`true`): a separate DEEP-combined codeword is committed and folded. FRI-IOPP on the trace
  codeword itself (`false`, the Tower256 prover): the trace tree is layer 0. -/
  deep : Bool
  deriving DecidableEq, Repr, Inhabited

/-- **The relation being proved**: one committed trace matrix. -/
structure Shape where
  logRows : ℕ
  /-- Base columns: the Merkle LEAF WIDTH of the trace commitment. -/
  width : ℕ
  /-- Quotient chunks `2^logQuot` (`log2_ceil(constraint degree − 1)`), each `extDeg` base columns. -/
  logQuot : ℕ
  /-- Extension multiplications to evaluate every constraint at one point. -/
  constraintMulsPerRow : ℕ
  /-- LogUp arguments `K`. -/
  lookups : ℕ
  /-- LogUp column-aggregation factor `R`. -/
  lookupArity : ℕ
  deriving DecidableEq, Repr, Inhabited

/-! ## §2 Counts -/

/-- **Counts.** Work and bytes in separate fields; there is no duration field. -/
structure Counts where
  baseMuls : ℕ
  extMuls : ℕ
  perms : ℕ
  queries : ℕ
  proofBytes : ℕ
  memBytes : ℕ
  deriving DecidableEq, Repr, Inhabited

instance : Add Counts :=
  ⟨fun a b => ⟨a.baseMuls + b.baseMuls, a.extMuls + b.extMuls, a.perms + b.perms,
    a.queries + b.queries, a.proofBytes + b.proofBytes, a.memBytes + b.memBytes⟩⟩
instance : Zero Counts := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩
instance : SMul ℕ Counts :=
  ⟨fun k a => ⟨k * a.baseMuls, k * a.extMuls, k * a.perms, k * a.queries, k * a.proofBytes,
    k * a.memBytes⟩⟩

/-- Componentwise order. -/
def Counts.le (a b : Counts) : Prop :=
  a.baseMuls ≤ b.baseMuls ∧ a.extMuls ≤ b.extMuls ∧ a.perms ≤ b.perms ∧ a.queries ≤ b.queries ∧
    a.proofBytes ≤ b.proofBytes ∧ a.memBytes ≤ b.memBytes

/-- One kernel of a schedule: arithmetic and the bytes it moves. Its time is
`max(arith, bytes / bandwidth)`: a kernel overlaps its own traffic with its own arithmetic and nothing
else. -/
structure Kernel where
  baseMuls : ℕ := 0
  extMuls : ℕ := 0
  perms : ℕ := 0
  memBytes : ℕ := 0
  deriving DecidableEq, Repr, Inhabited

def Kernel.scale (k : ℕ) (x : Kernel) : Kernel :=
  ⟨k * x.baseMuls, k * x.extMuls, k * x.perms, k * x.memBytes⟩

/-- **Per-element bytes of each kernel class**: calibration constants, not the model. -/
structure ByteModel where
  /-- Additive NTT, per coefficient per depth: the scale kernel. -/
  scale : ℕ
  /-- Additive NTT, per coefficient per Taylor XOR pass. -/
  taylor : ℕ
  /-- Additive NTT, per coefficient per depth: deinterleave. -/
  deinterleave : ℕ
  /-- Per output point per NTT layer: the butterfly kernel. -/
  butterfly : ℕ
  /-- Per output point, once: the final write. -/
  final : ℕ
  /-- Per Merkle leaf (leaf read plus node writes). -/
  merklePerLeaf : ℕ
  /-- Per fold multiplication. -/
  foldPerMul : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Compulsory traffic only, for a cache-blocked CPU prover: each NTT output element is written once
and read once by the Merkle leaf hash, and no layer pass touches memory. `eb` is the element size. -/
def ByteModel.compulsory (eb : ℕ) : ByteModel :=
  { scale := 0, taylor := 0, deinterleave := 0, butterfly := 0, final := 2 * eb,
    merklePerLeaf := 64, foldPerMul := 2 * eb }

/-- Permutations to absorb `bytes` (at least one). -/
def HashFn.absorbPerms (h : HashFn) (bytes : ℕ) : ℕ :=
  max 1 ((bytes + h.rateBytes - 1) / h.rateBytes)

/-- A Merkle tree over `leaves` leaves of `leafBytes` each: one sponge per leaf, one compression per
internal node. -/
def merklePerms (h : HashFn) (leaves leafBytes : ℕ) : ℕ :=
  leaves * h.absorbPerms leafBytes + (leaves - 1)

/-- Taylor XOR passes of the Gao–Mateer encode at `D` depths. -/
def taylorPasses (D : ℕ) : ℕ := ((List.range D).map fun d => D - d - 1).sum

/-- **The low-degree extension of `cols` columns** from `2^logRows` to `2^(logRows + lb)` points, as
kernels. Multiplicative: inverse NTT, coset scaling, forward NTT. Additive: Gao–Mateer from coefficients
(per depth `L` scalings and `n/2` butterflies, plus `2L`), then the memory-only Taylor and deinterleave
passes, exactly the Tower256 schedule's kernels. -/
def ldeKernels (bm : ByteModel) : NttKind → (cols logRows lb : ℕ) → List Kernel
  | .multiplicative, w, lr, lb =>
    let R := 2 ^ lr
    let n := 2 ^ (lr + lb)
    [{ baseMuls := w * (R / 2 * lr + R + n / 2 * (lr + lb)),
       memBytes := w * (bm.butterfly * n * (lr + lb) + bm.final * n) }]
  | .additive, w, lr, lb =>
    let L := 2 ^ lr
    let n := 2 ^ (lr + lb)
    let D := lr
    [{ baseMuls := w * (D * L + D * n / 2 + 2 * L),
       memBytes := w * (bm.scale * D * L + bm.butterfly * n * D) },
     { memBytes := w * (bm.taylor * L * taylorPasses D + bm.deinterleave * D * L + bm.final * n) }]

/-- Number of FRI fold rounds. -/
def Params.rounds (p : Params) (s : Shape) : ℕ :=
  (s.logRows + p.logBlowup - p.logFinal) / max 1 p.logArity

/-- Log₂ size of the LDE domain. -/
def Params.logN (p : Params) (s : Shape) : ℕ := s.logRows + p.logBlowup

/-- Log₂ sizes of the committed FRI layers. STARK: the DEEP codeword and every fold input before the
final (rounds `0 … m−1`). Trace-codeword FRI: the fold outputs `1 … m` (layer 0 is the trace tree). -/
def Params.friLayerLogs (p : Params) (s : Shape) : List ℕ :=
  let a := max 1 p.logArity
  if p.deep then (List.range (p.rounds s)).map fun j => p.logN s - j * a
  else (List.range (p.rounds s)).map fun j => p.logN s - (j + 1) * a

/-- Base columns opened per query on the trace and quotient trees. -/
def Shape.quotCols (s : Shape) (p : Params) : ℕ := if p.deep then 2 ^ s.logQuot * p.extDeg else 0

/-- The transcript's fixed absorptions: one per commitment, plus the out-of-domain values. -/
def transcriptPerms (p : Params) (s : Shape) : ℕ :=
  let eb := p.field.elemBytes
  2 + (p.friLayerLogs s).length + p.hash.absorbPerms ((s.width + s.quotCols p) * p.extDeg * eb * 2)

/-- **The prover's schedule, query-independent part**, as named phases of kernels. -/
def proverPhases (bm : ByteModel) (p : Params) (s : Shape) : List (String × List Kernel) :=
  let eb := p.field.elemBytes
  let n := 2 ^ p.logN s
  let R := 2 ^ s.logRows
  let a := max 1 p.logArity
  let qcols := s.quotCols p
  let traceLeaves := n
  let lde := ldeKernels bm p.field.ntt s.width s.logRows p.logBlowup
  let quotient : List Kernel :=
    if p.deep then
      [{ extMuls := s.constraintMulsPerRow * (R * 2 ^ s.logQuot) }] ++
        ldeKernels bm p.field.ntt qcols s.logRows p.logBlowup ++
        -- DEEP: out-of-domain evaluation (barycentric over R) and the combined codeword over n
        [{ extMuls := (s.width + qcols) * R,
           baseMuls := (s.width + qcols) * n * p.extDeg }]
    else []
  let merkle : List Kernel :=
    [{ perms := merklePerms p.hash traceLeaves (s.width * eb),
       memBytes := bm.merklePerLeaf * traceLeaves }] ++
    (if p.deep then [{ perms := merklePerms p.hash n (qcols * eb), memBytes := bm.merklePerLeaf * n }]
     else [])
  let folds : List Kernel :=
    (p.friLayerLogs s).map fun l =>
      let size := if p.deep then 2 ^ l else 2 ^ (l + a)
      let muls := size - size / 2 ^ a
      { extMuls := muls, memBytes := bm.foldPerMul * muls }
  let friMerkle : List Kernel :=
    (p.friLayerLogs s).map fun l =>
      let leaves := 2 ^ l / 2 ^ p.foldLeafLog
      { perms := merklePerms p.hash leaves (2 ^ p.foldLeafLog * p.extDeg * eb),
        memBytes := bm.merklePerLeaf * leaves }
  let grind : List Kernel :=
    [{ perms := 2 ^ p.powBits + (p.rounds s) * 2 ^ p.commitPowBits + transcriptPerms p s }]
  [("lde", lde), ("quotient", quotient), ("merkle", merkle), ("folds", folds),
   ("fri-merkle", friMerkle), ("grind+transcript", grind)]

/-- Per query, the prover samples an index and copies the openings: one permutation of transcript
and the opened bytes. -/
def proverPerQuery (p : Params) (s : Shape) : Kernel :=
  { perms := 1, memBytes := verifierPerQueryBytes p s }
where
  verifierPerQueryBytes (p : Params) (s : Shape) : ℕ :=
    let eb := p.field.elemBytes
    let opened := s.width * eb + s.quotCols p * eb +
      (p.friLayerLogs s).length * (2 ^ p.foldLeafLog * p.extDeg * eb)
    let depths := p.logN s * (if p.deep then 2 else 1) +
      ((p.friLayerLogs s).map fun l => l - p.foldLeafLog).sum
    opened + depths * p.hash.digestBytes

/-- Sum a kernel list into counts. -/
def Kernel.toCounts (k : Kernel) : Counts := ⟨k.baseMuls, k.extMuls, k.perms, 0, 0, k.memBytes⟩

def sumKernels (ks : List Kernel) : Counts := (ks.map Kernel.toCounts).foldr (· + ·) 0

/-- The opened bytes and Merkle path bytes for one query (the proof's per-query payload). -/
def perQueryProofBytes (p : Params) (s : Shape) : ℕ := proverPerQuery.verifierPerQueryBytes p s

/-- Proof bytes that do not depend on the query count: roots, out-of-domain values, final polynomial,
PoW witnesses. -/
def fixedProofBytes (p : Params) (s : Shape) : ℕ :=
  let eb := p.field.elemBytes
  let roots := (if p.deep then 2 else 1) + (p.friLayerLogs s).length
  roots * p.hash.digestBytes + (s.width + s.quotCols p) * p.extDeg * eb * 2 +
    2 ^ (p.logFinal - min p.logFinal p.logBlowup) * p.extDeg * eb + 8 * (1 + p.rounds s)

/-- **Prover counts, query-independent part.** -/
def proverFixed (bm : ByteModel) (p : Params) (s : Shape) : Counts :=
  sumKernels ((proverPhases bm p s).flatMap Prod.snd) + ⟨0, 0, 0, 0, fixedProofBytes p s, 0⟩

/-- **Prover counts, per query.** -/
def proverPerQueryCounts (p : Params) (s : Shape) : Counts :=
  ⟨0, 0, 1, 1, perQueryProofBytes p s, perQueryProofBytes p s⟩

/-- **THE PROVER COUNT FUNCTION.** Total: every knob combination returns a number. -/
def proverCounts (bm : ByteModel) (p : Params) (s : Shape) : Counts :=
  proverFixed bm p s + p.numQueries • proverPerQueryCounts p s

/-- Verifier, query-independent part: the transcript, the constraint check at the out-of-domain point,
the PoW checks. -/
def verifierFixed (p : Params) (s : Shape) : Counts :=
  ⟨0, s.constraintMulsPerRow + (s.width + s.quotCols p), transcriptPerms p s + 1 + p.rounds s, 0,
    fixedProofBytes p s, fixedProofBytes p s⟩

/-- Verifier, per query: every leaf hash and path compression, the folds, the DEEP check, and the
final-polynomial evaluation. -/
def verifierPerQuery (p : Params) (s : Shape) : Counts :=
  let eb := p.field.elemBytes
  let a := max 1 p.logArity
  let traceHash := p.hash.absorbPerms (s.width * eb) + p.logN s
  let quotHash := if p.deep then p.hash.absorbPerms (s.quotCols p * eb) + p.logN s else 0
  let friHash := ((p.friLayerLogs s).map fun l =>
    p.hash.absorbPerms (2 ^ p.foldLeafLog * p.extDeg * eb) + (l - p.foldLeafLog)).sum
  ⟨(s.width + s.quotCols p) * p.extDeg,
    (p.friLayerLogs s).length * 2 ^ a + 2 ^ (p.logFinal - min p.logFinal p.logBlowup),
    1 + traceHash + quotHash + friHash, 1, perQueryProofBytes p s, perQueryProofBytes p s⟩

/-- **THE VERIFIER COUNT FUNCTION** (native verifier, one proof). -/
def verifierCounts (p : Params) (s : Shape) : Counts :=
  verifierFixed p s + p.numQueries • verifierPerQuery p s

/-- **One recursion / PCD step** verifying `fanIn` children of shape `child`, in native counts. -/
def recursionStepCounts (fanIn : ℕ) (p : Params) (child : Shape) : Counts :=
  fanIn • verifierCounts p child

/-- In-circuit rates: how many rows one native operation costs in the recursion circuit. Calibration
constants (the generator lane's descriptor counts fill them). -/
structure CircuitRates where
  rowsPerPerm : ℚ
  rowsPerExtMul : ℚ
  rowsPerBaseMul : ℚ

def inCircuitRows (r : CircuitRates) (c : Counts) : ℚ :=
  r.rowsPerPerm * c.perms + r.rowsPerExtMul * c.extMuls + r.rowsPerBaseMul * c.baseMuls

/-! ## §3 Security: unique decoding, in the name and the type -/

/-- **The UDR query column**, exactly: `((1 + ρ)/2)^q / 2^g`. At unique decoding `1 − θ` is rational,
so no square is needed here. -/
def udrQueryErr (c : FriQueryCfg) : ℚ :=
  ((1 + c.rate) / 2) ^ c.numQueries / 2 ^ c.powBits

/-- **The same number as TwoRegimeQueryBudget's typed error**: its square is `(queryErr .UDR c).errSq`. -/
theorem udrQueryErr_sq (c : FriQueryCfg) : udrQueryErr c ^ 2 = (queryErr .UDR c).errSq := by
  unfold udrQueryErr queryErr survivalSq
  rw [div_pow, ← pow_mul, ← pow_mul, mul_comm c.numQueries 2, mul_comm c.powBits 2, pow_mul, pow_mul]
  norm_num

/-- The query-column knobs of a parameter set. -/
def Params.queryCfg (p : Params) : FriQueryCfg :=
  { logBlowup := p.logBlowup, numQueries := p.numQueries, powBits := p.powBits }

/-- The adversary and accumulation model of `Assurance.ErrorBudget`: oracle budget `t`, chain depth `k`,
sumcheck rounds/degree, hash budget and range. -/
structure Adversary where
  queries : ℕ
  depth : ℕ
  scRounds : ℕ
  scDegree : ℕ
  hashQueries : ℕ
  hashBits : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- ErrorBudget's deployed threat model: `t = q = 2^40`, `k = 2^8`, sumcheck `20 × 3`, `2^248`. -/
def deployedAdversary : Adversary :=
  { queries := 2 ^ 40, depth := 2 ^ 8, scRounds := 20, scDegree := 3, hashQueries := 2 ^ 40,
    hashBits := 248 }

/-- The challenge field's cardinality. -/
def Params.challengeCard (p : Params) : ℕ := p.field.card ^ p.extDeg

/-- **The algebraic (field-size) wall**, a computable rational mirror of `soundnessErrorPoW`. -/
def algErr (A : Adversary) (p : Params) (s : Shape) : ℚ :=
  let F : ℚ := p.challengeCard
  let n : ℚ := (2 : ℚ) ^ p.logN s
  ((A.queries + A.depth : ℚ) * (A.depth * (n / F + 1 / F))) / 2 ^ p.commitPowBits
    + A.depth * (A.scRounds * (A.scDegree / F))
    + A.hashQueries * ((A.hashQueries : ℚ) - 1) / 2 ^ (A.hashBits + 1)
    + n / F

/-- The PoW soundness parameters this knob set instantiates in `Assurance.ErrorBudget120`. -/
noncomputable def toPoWParams (A : Adversary) (p : Params) (s : Shape) : PoWSoundnessParams where
  toSoundnessParams :=
    { fieldCard := p.challengeCard
      codeLen := 2 ^ p.logN s
      degree := 2 ^ s.logRows
      delta := 0
      queries := A.queries
      depth := A.depth
      scRounds := A.scRounds
      scDegree := A.scDegree
      hashQueries := A.hashQueries
      hashBits := A.hashBits
      secparam := 0 }
  powBits := p.commitPowBits

/-- **The algebraic wall is ErrorBudget's landed expression**, not a re-derivation. -/
theorem algErr_eq_soundnessErrorPoW (A : Adversary) (p : Params) (s : Shape) :
    ((algErr A p s : ℚ) : ℝ) = soundnessErrorPoW (toPoWParams A p s) := by
  simp only [algErr, soundnessErrorPoW, grindingTermPoW, grindingTerm, sumcheckTerm, crTerm,
    proximityTerm, errStarUD, toPoWParams]
  push_cast
  ring

/-- **The FRI commit phase at unique decoding**: per fold round, an affine curve of degree `2^a − 1`
through the batched codeword lands in the proximity-gap failure set with probability
`≤ (2^a − 1)·(n + 1)/|F|`, discounted by the commit grinding. Proved in-tree for lines only (`a = 1`,
`Selvage.ProximityGapUD`); BCIKS20's curve version above that. -/
def commitErr (p : Params) (s : Shape) : ℚ :=
  (p.rounds s : ℚ) * ((2 : ℚ) ^ max 1 p.logArity - 1) * (((2 : ℚ) ^ p.logN s + 1) / p.challengeCard)
    / 2 ^ p.commitPowBits

/-- The LogUp wall over the challenge field (rows of trace plus table). -/
def lookupErr (p : Params) (s : Shape) : ℚ :=
  if s.lookups = 0 then 0
  else logupErr p.challengeCard
    { numLookups := s.lookups, rows := 2 * 2 ^ s.logRows, colFactor := s.lookupArity, grindBits := 0 }

/-- **THE COMPOSED ERROR, AT UNIQUE DECODING.** The union bound over the four walls. There is no JBR or
CBR entry point in this file: a configuration's security here is a UDR number by construction. -/
def udrErr (A : Adversary) (p : Params) (s : Shape) : ℚ :=
  algErr A p s + commitErr p s + udrQueryErr p.queryCfg + lookupErr p s

/-- Two-sided bits of a rational error: `⌊log₂ (1/e)⌋`. -/
def bitsOf (e : ℚ) : ℕ := Nat.log 2 ⌊e⁻¹⌋₊

/-- **`bitsOf` is the two-sided bit count**: the promise and the refutation of the next bit. -/
theorem bitsOf_spec {e : ℚ} (h0 : 0 < e) (h1 : e ≤ 1) :
    e ≤ 1 / 2 ^ bitsOf e ∧ 1 / 2 ^ (bitsOf e + 1) < e := by
  have hinv : 1 ≤ e⁻¹ := by rw [le_inv_comm₀ (by norm_num) h0]; simpa using h1
  have hN : ⌊e⁻¹⌋₊ ≠ 0 := by
    have := Nat.floor_pos.mpr hinv; omega
  set N := ⌊e⁻¹⌋₊ with hNdef
  have hlo : (2 : ℚ) ^ Nat.log 2 N ≤ e⁻¹ := by
    calc (2 : ℚ) ^ Nat.log 2 N = ((2 ^ Nat.log 2 N : ℕ) : ℚ) := by push_cast; rfl
      _ ≤ (N : ℚ) := by exact_mod_cast Nat.pow_log_le_self 2 hN
      _ ≤ e⁻¹ := Nat.floor_le (by positivity)
  have hhi : e⁻¹ < (2 : ℚ) ^ (Nat.log 2 N + 1) := by
    calc e⁻¹ < (N : ℚ) + 1 := Nat.lt_floor_add_one _
      _ ≤ ((2 ^ (Nat.log 2 N + 1) : ℕ) : ℚ) := by
          exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
      _ = (2 : ℚ) ^ (Nat.log 2 N + 1) := by push_cast; rfl
  unfold bitsOf
  rw [← hNdef]
  constructor
  · rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hlo h0.le
    rw [mul_inv_cancel₀ h0.ne'] at this
    linarith [mul_comm e ((2 : ℚ) ^ Nat.log 2 N)]
  · rw [div_lt_iff₀ (by positivity)]
    have := mul_lt_mul_of_pos_left hhi h0
    rw [mul_inv_cancel₀ h0.ne'] at this
    linarith [mul_comm e ((2 : ℚ) ^ (Nat.log 2 N + 1))]

/-- **`bitsOf` is antitone**: a smaller error never reads fewer bits. -/
theorem bitsOf_antitone {e e' : ℚ} (h0 : 0 < e) (h : e ≤ e') : bitsOf e' ≤ bitsOf e := by
  unfold bitsOf
  apply Nat.log_mono_right
  apply Nat.floor_le_floor
  exact inv_anti₀ h0 h

/-- **The security function.** -/
def udrBits (A : Adversary) (p : Params) (s : Shape) : ℕ := bitsOf (udrErr A p s)

theorem udrQueryErr_pos (c : FriQueryCfg) : 0 < udrQueryErr c := by
  have := c.rate_pos
  unfold udrQueryErr; positivity

theorem udrErr_pos (A : Adversary) (p : Params) (s : Shape) (hA : 1 ≤ A.hashQueries) :
    0 < udrErr A p s := by
  have hq := udrQueryErr_pos p.queryCfg
  have hF : (0 : ℚ) ≤ p.challengeCard := by positivity
  have ha : (0 : ℚ) ≤ algErr A p s := by
    unfold algErr
    have : (0 : ℚ) ≤ (A.hashQueries : ℚ) - 1 := by
      have : (1 : ℚ) ≤ A.hashQueries := by exact_mod_cast hA
      linarith
    positivity
  have hc : (0 : ℚ) ≤ commitErr p s := by
    unfold commitErr
    have : (1 : ℚ) ≤ (2 : ℚ) ^ max 1 p.logArity := one_le_pow₀ (by norm_num)
    have : (0 : ℚ) ≤ (2 : ℚ) ^ max 1 p.logArity - 1 := by linarith
    positivity
  have hl : (0 : ℚ) ≤ lookupErr p s := by
    unfold lookupErr logupErr; split_ifs <;> positivity
  unfold udrErr; linarith

/-- **`udrBits` is two-sided**, whenever the error is a probability. -/
theorem udrBits_spec (A : Adversary) (p : Params) (s : Shape) (hA : 1 ≤ A.hashQueries)
    (h1 : udrErr A p s ≤ 1) :
    udrErr A p s ≤ 1 / 2 ^ udrBits A p s ∧ 1 / 2 ^ (udrBits A p s + 1) < udrErr A p s :=
  bitsOf_spec (udrErr_pos A p s hA) h1

/-- **More queries never cost bits**: the composed UDR error is antitone in `numQueries`. -/
theorem udrErr_antitone_queries (A : Adversary) (p : Params) (s : Shape) {q q' : ℕ} (h : q ≤ q') :
    udrErr A { p with numQueries := q' } s ≤ udrErr A { p with numQueries := q } s := by
  have hr := (p.queryCfg).rate_pos
  have hr1 : p.queryCfg.rate ≤ 1 := by
    unfold FriQueryCfg.rate
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hb0 : 0 ≤ (1 + p.queryCfg.rate) / 2 := by positivity
  have hb1 : (1 + p.queryCfg.rate) / 2 ≤ 1 := by linarith
  unfold udrErr
  have : udrQueryErr { p with numQueries := q' }.queryCfg
      ≤ udrQueryErr { p with numQueries := q }.queryCfg := by
    unfold udrQueryErr Params.queryCfg FriQueryCfg.rate at *
    simp only at *
    gcongr ?_ / _
    exact pow_le_pow_of_le_one hb0 hb1 h
  have e1 : algErr A { p with numQueries := q' } s = algErr A { p with numQueries := q } s := rfl
  have e2 : commitErr { p with numQueries := q' } s = commitErr { p with numQueries := q } s := rfl
  have e3 : lookupErr { p with numQueries := q' } s = lookupErr { p with numQueries := q } s := rfl
  linarith

/-! ## §4 Machines: counts to seconds through named calibration constants -/

/-- A machine: rates per operation class and bandwidth. Calibration constants, never the model. -/
structure Machine where
  /-- Base-field multiplications per second. -/
  mulRate : ℚ
  /-- Extension multiplications per second. -/
  extMulRate : ℚ
  /-- Hash permutations per second. -/
  permRate : ℚ
  /-- Memory bandwidth, bytes per second (read plus write). -/
  copyBw : ℚ

/-- A kernel's time: `max(arith, bytes / bw)`. -/
def Machine.kernelTime (m : Machine) (k : Kernel) : ℚ :=
  max (k.baseMuls / m.mulRate + k.extMuls / m.extMulRate + k.perms / m.permRate)
    (k.memBytes / m.copyBw)

/-- A schedule's time on one stream: the sum of its kernels' times. -/
def Machine.scheduleTime (m : Machine) (ks : List Kernel) : ℚ := (ks.map m.kernelTime).sum

/-- **Prover seconds**: the fixed schedule plus `q` query kernels. -/
def proverTime (m : Machine) (bm : ByteModel) (p : Params) (s : Shape) : ℚ :=
  m.scheduleTime ((proverPhases bm p s).flatMap Prod.snd) +
    p.numQueries * m.kernelTime (proverPerQuery p s)

/-- **Verifier seconds** (native). -/
def verifierTime (m : Machine) (p : Params) (s : Shape) : ℚ :=
  let c := verifierCounts p s
  c.baseMuls / m.mulRate + c.extMuls / m.extMulRate + c.perms / m.permRate

/-! ## §5 The deployed IR-v2 point, read through the function -/

/-- The deployed IR-v2 descriptor-batch knobs (`circuit/src/descriptor_ir2.rs:7269-7273`,
`IR2_FRI_COMMIT_POW_BITS = 0`, `IR2_FRI_MAX_LOG_ARITY = 3`, `IR2_FRI_LOG_FINAL_POLY_LEN = 0`). -/
def ir2Params : Params :=
  { field := .babyBear, extDeg := 4, logBlowup := 6, numQueries := 19, powBits := 16,
    commitPowBits := 0, hash := .poseidon2W16, logArity := 3, foldLeafLog := 3, logFinal := 6,
    deep := true }

/-- A reference leaf: `2^16` rows of the 386-column chip (`CHIP_WIDTH`), degree-7 constraints
(`log2_ceil 6 = 3`), one LogUp argument at the admitted arity 97. `constraintMulsPerRow` is a placeholder
of 1000 until the generator lane's descriptor counts replace it; the quotient phase is a few percent of
the prover, so the ranking below does not turn on it. -/
def refLeaf : Shape :=
  { logRows := 16, width := 386, logQuot := 3, constraintMulsPerRow := 1000, lookups := 1,
    lookupArity := 97 }

/-- The query column of `ir2Params` is TwoRegimeQueryBudget's `ir2`. -/
theorem ir2Params_queryCfg : ir2Params.queryCfg = ir2 := rfl

/-- **The deployed point reads 34 bits through the composed function**: the query column binds
(`ir2_three_regimes`), the field wall does not. -/
theorem ir2_reads_34 : udrBits deployedAdversary ir2Params refLeaf = 34 := by native_decide

/-! ## §7 The Pareto front over a finite grid -/

/-- The reference CPU: the measured exchange rate `Y = t_perm / t_mul = 890` (`COST-MODEL.md`, 16 MB
working set) with time in permutation units; an extension multiplication costs `extDeg²` base
multiplications (schoolbook); memory is not the binding resource on the CPU prover. -/
def cpuRef (extDeg : ℕ) : Machine :=
  { mulRate := 890, extMulRate := 890 / (extDeg ^ 2 : ℚ), permRate := 1, copyBw := 10 ^ 15 }

/-- The three objectives: prover time, verifier time (both in permutation units on `cpuRef`) and
proof bytes. Every one is `fixed + q · perQuery`. -/
def objectives (p : Params) (s : Shape) : ℚ × ℚ × ℚ :=
  let m := cpuRef p.extDeg
  (proverTime m (ByteModel.compulsory p.field.elemBytes) p s, verifierTime m p s,
    ((proverCounts (ByteModel.compulsory p.field.elemBytes) p s).proofBytes : ℚ))

/-- Weak Pareto dominance: no worse in every objective and better in one. -/
def dominates (a b : ℚ × ℚ × ℚ) : Bool :=
  a.1 ≤ b.1 && a.2.1 ≤ b.2.1 && a.2.2 ≤ b.2.2 && (a.1 < b.1 || a.2.1 < b.2.1 || a.2.2 < b.2.2)

/-- Feasible at target `T`: the composed UDR error is at most `2^-T`. -/
def feasible (T : ℕ) (A : Adversary) (p : Params) (s : Shape) : Bool := udrErr A p s ≤ 1 / 2 ^ T

/-- First `q ≥ q₀` (within `fuel` steps) at which a predicate holds. -/
def firstFrom (P : ℕ → Bool) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, q => if P q then some q else firstFrom P fuel (q + 1)

theorem firstFrom_spec (P : ℕ → Bool) :
    ∀ (fuel q r : ℕ), firstFrom P fuel q = some r →
      P r = true ∧ q ≤ r ∧ ∀ q', q ≤ q' → q' < r → P q' = false := by
  intro fuel
  induction fuel with
  | zero => intro q r h; simp [firstFrom] at h
  | succ f ih =>
    intro q r h
    simp only [firstFrom] at h
    split_ifs at h with hP
    · cases h; exact ⟨hP, le_refl _, fun q' h1 h2 => absurd h2 (by omega)⟩
    · obtain ⟨h1, h2, h3⟩ := ih (q + 1) r h
      refine ⟨h1, by omega, fun q' hq hr => ?_⟩
      rcases Nat.eq_or_lt_of_le hq with e | lt
      · subst e; simpa using hP
      · exact h3 q' (by omega) hr

/-- The least feasible query count, searched up to `qMax`. -/
def minQueries (T : ℕ) (A : Adversary) (p : Params) (s : Shape) (qMax : ℕ) : Option ℕ :=
  firstFrom (fun q => feasible T A { p with numQueries := q } s) (qMax + 1) 0

/-- The grid's non-query knobs over the given fold arities, BabyBear and Poseidon2-16 throughout. -/
def gridKnobs (arities : List ℕ) : List Params := Id.run do
  let mut out := #[]
  for e in [4, 5, 6, 8] do
    for lb in [1, 2, 3, 4, 5, 6] do
      for g in [0, 8, 12, 16, 20] do
        for cg in [0, 10, 20] do
          for a in arities do
            out := out.push
              { field := .babyBear, extDeg := e, logBlowup := lb, numQueries := 0, powBits := g,
                commitPowBits := cg, hash := .poseidon2W16, logArity := a, foldLeafLog := a,
                logFinal := lb, deep := true }
  return out.toList

/-- The grid with each point at its least feasible query count (infeasible points dropped). -/
def feasibleGrid (ar : List ℕ) (T : ℕ) (A : Adversary) (s : Shape) (qMax : ℕ) : List Params :=
  (gridKnobs ar).filterMap fun p => (minQueries T A p s qMax).map fun q => { p with numQueries := q }

/-- **The compiled Pareto check**: `c` is feasible and no feasible grid point dominates it. -/
def paretoCheck (ar : List ℕ) (T : ℕ) (A : Adversary) (s : Shape) (qMax : ℕ) (c : Params) : Bool :=
  feasible T A c s && (feasibleGrid ar T A s qMax).all fun p => !dominates (objectives p s) (objectives c s)


/-! ## §8 The grid check is sound over EVERY query count

`paretoCheck` enumerates each grid point only at its least feasible query count. That is sufficient,
not a sampling: every objective is `fixed + q · perQuery` with nonnegative coefficients, so a point at
any larger feasible `q` is no better in any objective than the same point at the least one, and could
dominate only if the least one already did. -/

theorem proverPhases_q (bm : ByteModel) (p : Params) (s : Shape) (q : ℕ) :
    proverPhases bm { p with numQueries := q } s = proverPhases bm p s := rfl
theorem proverPerQuery_q (p : Params) (s : Shape) (q : ℕ) :
    proverPerQuery { p with numQueries := q } s = proverPerQuery p s := rfl
theorem verifierFixed_q (p : Params) (s : Shape) (q : ℕ) :
    verifierFixed { p with numQueries := q } s = verifierFixed p s := rfl
theorem verifierPerQuery_q (p : Params) (s : Shape) (q : ℕ) :
    verifierPerQuery { p with numQueries := q } s = verifierPerQuery p s := rfl
theorem proverFixed_q (bm : ByteModel) (p : Params) (s : Shape) (q : ℕ) :
    proverFixed bm { p with numQueries := q } s = proverFixed bm p s := rfl
theorem proverPerQueryCounts_q (p : Params) (s : Shape) (q : ℕ) :
    proverPerQueryCounts { p with numQueries := q } s = proverPerQueryCounts p s := rfl

private theorem lin_mono {a b : ℕ} {r : ℚ} (hr : 0 ≤ r) {q q' : ℕ} (h : q ≤ q') :
    ((a + q * b : ℕ) : ℚ) / r ≤ ((a + q' * b : ℕ) : ℚ) / r := by
  apply div_le_div_of_nonneg_right _ hr
  exact_mod_cast Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem Machine.kernelTime_nonneg (m : Machine) (hb : 0 ≤ m.copyBw) (k : Kernel) :
    0 ≤ m.kernelTime k :=
  le_max_of_le_right (by positivity)

/-- **Every objective is monotone in the query count.** -/
theorem objectives_mono_queries (p : Params) (s : Shape) {q q' : ℕ} (h : q ≤ q') :
    (objectives { p with numQueries := q } s).1 ≤ (objectives { p with numQueries := q' } s).1 ∧
    (objectives { p with numQueries := q } s).2.1 ≤ (objectives { p with numQueries := q' } s).2.1 ∧
    (objectives { p with numQueries := q } s).2.2 ≤ (objectives { p with numQueries := q' } s).2.2 := by
  have hk := Machine.kernelTime_nonneg (cpuRef p.extDeg) (by unfold cpuRef; positivity)
    (proverPerQuery p s)
  have hq : (q : ℚ) ≤ q' := by exact_mod_cast h
  refine ⟨?_, ?_, ?_⟩
  · have e : ∀ n : ℕ, (objectives { p with numQueries := n } s).1 =
        (cpuRef p.extDeg).scheduleTime
            ((proverPhases (ByteModel.compulsory p.field.elemBytes) p s).flatMap Prod.snd) +
          n * (cpuRef p.extDeg).kernelTime (proverPerQuery p s) := fun _ => rfl
    rw [e, e]
    have := mul_le_mul_of_nonneg_right hq hk
    linarith
  · have e : ∀ n : ℕ, (objectives { p with numQueries := n } s).2.1 =
        (((verifierFixed p s).baseMuls + n * (verifierPerQuery p s).baseMuls : ℕ) : ℚ)
            / (cpuRef p.extDeg).mulRate
          + (((verifierFixed p s).extMuls + n * (verifierPerQuery p s).extMuls : ℕ) : ℚ)
            / (cpuRef p.extDeg).extMulRate
          + (((verifierFixed p s).perms + n * (verifierPerQuery p s).perms : ℕ) : ℚ)
            / (cpuRef p.extDeg).permRate := fun _ => rfl
    rw [e, e]
    have h1 := lin_mono (a := (verifierFixed p s).baseMuls) (b := (verifierPerQuery p s).baseMuls)
      (r := (cpuRef p.extDeg).mulRate) (by unfold cpuRef; positivity) h
    have h2 := lin_mono (a := (verifierFixed p s).extMuls) (b := (verifierPerQuery p s).extMuls)
      (r := (cpuRef p.extDeg).extMulRate) (by unfold cpuRef; positivity) h
    have h3 := lin_mono (a := (verifierFixed p s).perms) (b := (verifierPerQuery p s).perms)
      (r := (cpuRef p.extDeg).permRate) (by unfold cpuRef; positivity) h
    linarith
  · have e : ∀ n : ℕ, (objectives { p with numQueries := n } s).2.2 =
        (((proverFixed (ByteModel.compulsory p.field.elemBytes) p s).proofBytes
          + n * (proverPerQueryCounts p s).proofBytes : ℕ) : ℚ) := fun _ => rfl
    rw [e, e]
    exact_mod_cast Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem dominates_of_le {a a' c : ℚ × ℚ × ℚ}
    (h1 : a.1 ≤ a'.1) (h2 : a.2.1 ≤ a'.2.1) (h3 : a.2.2 ≤ a'.2.2)
    (hd : dominates a' c = true) : dominates a c = true := by
  unfold dominates at *
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at *
  obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := hd
  refine ⟨⟨⟨le_trans h1 g1, le_trans h2 g2⟩, le_trans h3 g3⟩, ?_⟩
  rcases g4 with (g | g) | g
  · exact Or.inl (Or.inl (lt_of_le_of_lt h1 g))
  · exact Or.inl (Or.inr (lt_of_le_of_lt h2 g))
  · exact Or.inr (lt_of_le_of_lt h3 g)

theorem firstFrom_some_of (P : ℕ → Bool) :
    ∀ (fuel q₀ q' : ℕ), q₀ ≤ q' → q' < q₀ + fuel → P q' = true →
      ∃ r, firstFrom P fuel q₀ = some r ∧ r ≤ q' := by
  intro fuel
  induction fuel with
  | zero => intro q₀ q' h1 h2 _; omega
  | succ f ih =>
    intro q₀ q' h1 h2 hP
    by_cases h0 : P q₀ = true
    · exact ⟨q₀, by simp [firstFrom, h0], h1⟩
    · have hne : q₀ ≠ q' := fun e => h0 (e ▸ hP)
      obtain ⟨r, hr, hrq⟩ := ih (q₀ + 1) q' (by omega) (by omega) hP
      refine ⟨r, ?_, hrq⟩
      simpa [firstFrom, h0] using hr

/-- ⚑ **THE GRID CHECK IS SOUND OVER ALL QUERY COUNTS.** If `paretoCheck` passes, then `c` is feasible
and no grid point, at ANY query count up to `qMax` at which it is feasible, dominates `c`. The compiled
check enumerates `|grid|` points; this theorem is what makes that the whole `|grid| × (qMax + 1)`
space. -/
theorem paretoCheck_sound {ar : List ℕ} {T : ℕ} {A : Adversary} {s : Shape} {qMax : ℕ} {c : Params}
    (h : paretoCheck ar T A s qMax c = true) :
    feasible T A c s = true ∧
      ∀ p ∈ gridKnobs ar, ∀ q ≤ qMax, feasible T A { p with numQueries := q } s = true →
        dominates (objectives { p with numQueries := q } s) (objectives c s) = false := by
  unfold paretoCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hc, hall⟩ := h
  refine ⟨hc, fun p hp q hq hf => ?_⟩
  obtain ⟨r, hr, hrq⟩ := firstFrom_some_of (fun q => feasible T A { p with numQueries := q } s)
    (qMax + 1) 0 q (Nat.zero_le _) (by omega) hf
  have hmem : { p with numQueries := r } ∈ feasibleGrid ar T A s qMax := by
    unfold feasibleGrid
    exact List.mem_filterMap.mpr ⟨p, hp, by simp [minQueries, hr]⟩
  have hnd := hall _ hmem
  have hm := objectives_mono_queries p s hrq
  cases hd : dominates (objectives { p with numQueries := q } s) (objectives c s)
  · rfl
  · exact absurd (dominates_of_le hm.1 hm.2.1 hm.2.2 hd) (by simp [hnd])

/-! ## §9 The verdicts, as compiled checks over the grid

Concrete data, so these are `native_decide` with the axiom footprint pinned below
(`Lean.ofReduceBool` is the compiled evaluator; nothing else enters). -/

/-- ⚑ **The deployed point is Pareto-DOMINATED at its own 34 bits.** Same field, same arity, rate 1/4
with 21 queries and 20 grinding bits reads the same 34 UDR bits on the reference leaf and is no worse on
any objective — the prover by about 10× (the blowup), and the verifier and proof also shrink. -/
def ir2Dominator : Params := { ir2Params with logBlowup := 2, numQueries := 21, powBits := 20, logFinal := 2 }

theorem ir2_is_dominated :
    udrBits deployedAdversary ir2Dominator refLeaf = 34 ∧
      dominates (objectives ir2Dominator refLeaf) (objectives ir2Params refLeaf) = true ∧
      paretoCheck [1, 2, 3] 34 deployedAdversary refLeaf 1000 ir2Params = false := by
  native_decide

/-- **The proposed 100-bit configuration** (directive 5). BabyBear trace, **BabyBear⁶** challenges,
**rate 1/4**, **124 queries**, the deployed 16 query-grinding bits, **no** commit grinding, **fold by 2**
(the arity at which every term is proved in this tree). Relative to the deployed point it moves four
knobs: `extDeg 4 → 6`, `logBlowup 6 → 2`, `numQueries 19 → 124`, `logArity 3 → 1`. -/
def ud100 : Params :=
  { field := .babyBear, extDeg := 6, logBlowup := 2, numQueries := 124, powBits := 16,
    commitPowBits := 0, hash := .poseidon2W16, logArity := 1, foldLeafLog := 1, logFinal := 2,
    deep := true }

/-- The 120-bit companion: 154 queries and 10 commit-grinding bits (BabyBear⁶ alone reads 119 on the
field wall at this domain). -/
def ud120 : Params := { ud100 with numQueries := 154, commitPowBits := 10 }

/-- ⚑ **ud100 is a proven 100-bit configuration, two-sided, at unique decoding**: the composed error
lies in `(2^-101, 2^-100]`. -/
theorem ud100_two_sided :
    udrErr deployedAdversary ud100 refLeaf ≤ 1 / 2 ^ 100 ∧
      1 / 2 ^ 101 < udrErr deployedAdversary ud100 refLeaf := by
  native_decide

theorem ud120_two_sided :
    udrErr deployedAdversary ud120 refLeaf ≤ 1 / 2 ^ 120 ∧
      1 / 2 ^ 121 < udrErr deployedAdversary ud120 refLeaf := by
  native_decide

/-- **124 is the least query count** that reaches 100 bits with the other knobs fixed. -/
theorem ud100_queries_minimal : minQueries 100 deployedAdversary ud100 refLeaf 1000 = some 124 := by
  native_decide

/-- ⚑ **ud100 is Pareto-minimal over the in-tree-proved grid** at 100 bits: extension `{4,5,6,8}`,
blowup `1…6`, query grinding `{0,8,12,16,20}`, commit grinding `{0,10,20}`, fold by 2, and (by
`paretoCheck_sound`) every query count up to 1000. -/
theorem ud100_pareto : paretoCheck [1] 100 deployedAdversary refLeaf 1000 ud100 = true := by
  native_decide

theorem ud120_pareto : paretoCheck [1] 120 deployedAdversary refLeaf 1000 ud120 = true := by
  native_decide

/-- The Pareto statement for ud100, in the form a reader checks: no grid point at any feasible query
count dominates it. -/
theorem ud100_pareto_minimal :
    feasible 100 deployedAdversary ud100 refLeaf = true ∧
      ∀ p ∈ gridKnobs [1], ∀ q ≤ 1000,
        feasible 100 deployedAdversary { p with numQueries := q } refLeaf = true →
          dominates (objectives { p with numQueries := q } refLeaf) (objectives ud100 refLeaf) = false :=
  paretoCheck_sound ud100_pareto

/-- ⚑ **And it is NOT Pareto-minimal once arity 4 and 8 are admitted**: folding by 8 at BabyBear⁵ with
20 commit-grinding bits beats it on every objective. That point rests on BCIKS20's unique-decoding
CURVE bound, which this tree has not formalized; the gap between the two fronts is the price of
formalizing it. -/
def ud100Arity8 : Params :=
  { ud100 with extDeg := 5, commitPowBits := 20, logArity := 3, foldLeafLog := 3 }

theorem ud100_dominated_once_curves_admitted :
    feasible 100 deployedAdversary ud100Arity8 refLeaf = true ∧
      dominates (objectives ud100Arity8 refLeaf) (objectives ud100 refLeaf) = true := by
  native_decide

/--
info: 'Minidregg.Assurance.Cost.ud100_pareto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ud100_pareto._native.native_decide.ax_1_1]
-/
#guard_msgs in #print axioms ud100_pareto
/--
info: 'Minidregg.Assurance.Cost.ir2_reads_34' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ir2_reads_34._native.native_decide.ax_1_1]
-/
#guard_msgs in #print axioms ir2_reads_34

end Minidregg.Assurance.Cost
