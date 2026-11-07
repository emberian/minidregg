/-
# Assurance.CostCalibration: measured hardware facts as named constants, and what the model predicts

`Assurance.CostModel` is the model: counts, as exact functions of the knobs. This file holds the
hardware facts measured on 2026-11-06/07 as named calibration constants, each with its source, and the
predictions the model makes from them. Measurement calibrates the model; it does not stand in for it.

Sources:
* `zkml-research/notes/accelerator-readiness/TOWER256-SCHEDULE.md` §1, §6 (`accel-tower-e2e-01`, Kaggle
  T4): rates, per-element kernel bytes, measured per-proof times;
* `zkml-research/notes/tensor-core-holography/ROTATION.md` §2(b) (`accel-towermul-vs-table-01`): bytes per
  element of the T4 INT8 fixed-r route, and its binding resource;
* `zkml-research/notes/tpu-perf/STYLE.md` page 1 and the s3 measurement table: the v5e peaks and the int8
  GEMM rule.
-/
import Assurance.CostModel

namespace Minidregg.Assurance.Cost.Calibration

open Minidregg.Assurance.Cost

/-! ## §1 Tower256 on T4: the constants -/

/-- **Per-element bytes of the Tower256 GPU kernels** (32-byte elements; `tower256_schedule_model.py`
`counts`): scale 96 B per coefficient per depth, Taylor 40 B per coefficient per pass, deinterleave 64 B,
butterfly 80 B per point per depth, final write 32 B per point, Merkle 160 B per leaf, fold 128 B per
multiply. -/
def tower256Bytes : ByteModel :=
  { scale := 96, taylor := 40, deinterleave := 64, butterfly := 80, final := 32, merklePerLeaf := 160,
    foldPerMul := 128 }

/-- T4 device copy bandwidth, read plus write: 234 GB/s (`accel-mma-t4-runbook-03`). -/
def t4CopyBw : ℚ := 234 * 10 ^ 9

/-- The T4 table multiply's measured session-to-session range, 2.9e8–5.4e8 per second (TOWER256.md
§4, §8). -/
def t4MulLo : ℚ := 29 * 10 ^ 7
def t4MulHi : ℚ := 54 * 10 ^ 7

/-- Keccak-f[1600] on T4, batched Merkle build: 4.35e8–6.9e8 per second. -/
def t4KeccakLo : ℚ := 435 * 10 ^ 6
def t4KeccakHi : ℚ := 69 * 10 ^ 7

/-- The `accel-tower-e2e-01` session's own rates: multiply 3.2e8/s (from the encode phase), Keccak
5.9e8/s (from the Merkle phase). -/
def t4SessionMul : ℚ := 32 * 10 ^ 7
def t4SessionKeccak : ℚ := 59 * 10 ^ 7

/-- Host-to-device upload, pageable PCIe: 6 GB/s (the model's figure; the session measured about
1 GB/s, see §2). -/
def t4Pcie : ℚ := 6 * 10 ^ 9

def t4At (mul keccak : ℚ) : Machine :=
  { mulRate := mul, extMulRate := mul, permRate := keccak, copyBw := t4CopyBw }

/-- **The Tower256 production knobs**: rate 1/4, 148 queries, no grinding, Keccak, fold by 2 with one
element per leaf, final domain `2^4`, FRI on the trace codeword itself. -/
def tower256Params : Params :=
  { field := .tower256, extDeg := 1, logBlowup := 2, numQueries := 148, powBits := 0,
    commitPowBits := 0, hash := .keccakF1600, logArity := 1, foldLeafLog := 0, logFinal := 4,
    deep := false }

/-- One Tower256 column with `2^(ell - 2)` coefficients, encoded to `2^ell` points. -/
def tower256Shape (ell : ℕ) : Shape :=
  { logRows := ell - 2, width := 1, logQuot := 0, constraintMulsPerRow := 0, lookups := 0,
    lookupArity := 0 }

/-- **The model's device bound per proof**: the prover schedule from `CostModel` on the T4 at the given
rates, plus the upload of the `32·L`-byte word. -/
def tower256DeviceBound (mul keccak : ℚ) (ell : ℕ) : ℚ :=
  proverTime (t4At mul keccak) tower256Bytes tower256Params (tower256Shape ell)
    + 32 * 2 ^ (ell - 2) / t4Pcie

/-- **Measured**, two streams, ms per proof amortized over the batch (64 / 16 / 4 leaves):
16.9 / 67.0 / 303.5 (`accel-tower-e2e-01`), as seconds. -/
def t4Measured : List (ℕ × ℚ) := [(18, 169 / 10000), (20, 670 / 10000), (22, 3035 / 10000)]

/-! ## §2 What the model predicts, and how close it gets -/

/-- **The encode's multiply count is the Tower256 schedule's**: `ℓ·L + ℓ·n/2 + 2L` at `ell = 20` is
14,680,064, the "14.7M multiplies" of TOWER256-SCHEDULE §2. -/
theorem tower256_encode_mults_ell20 :
    (sumKernels (ldeKernels tower256Bytes .additive 1 18 2)).baseMuls = 14680064 := by native_decide

/-- **The Merkle count is the schedule's**: 4,194,255 Keccak-f per proof at `ell = 20` (§2: 4.19M),
the trace tree plus the sixteen fold layers. -/
theorem tower256_merkle_perms_ell20 :
    ((proverPhases tower256Bytes tower256Params (tower256Shape 20)).filter
        (fun x => x.1 = "merkle" || x.1 = "fri-merkle")).foldr
      (fun x acc => acc + (sumKernels x.2).perms) 0 = 4194255 := by native_decide

/-- ⚑ **At the session's own rates the model predicts every measured time to within 15%, from below.**
For each of `ell = 18, 20, 22`: `1 ≤ measured / predicted ≤ 1.15`. The model's numbers are 14.8 / 65.9 /
290.6 ms against 16.9 / 67.0 / 303.5 ms: ratios 1.14 / 1.02 / 1.04. The gap is largest at `ell = 18`,
where the per-proof host work (~2 ms of challenges and framing, and the 8.2 ms upload the model prices at
1.4 ms) is the largest share and two streams hide it least. -/
theorem tower256_t4_session_prediction :
    ∀ x ∈ t4Measured,
      tower256DeviceBound t4SessionMul t4SessionKeccak x.1 ≤ x.2 ∧
        x.2 ≤ 115 / 100 * tower256DeviceBound t4SessionMul t4SessionKeccak x.1 := by
  native_decide

/-- **From the datasheet-free calibration range alone** (no session rate), the model brackets the
measurement at `ell = 20` and `22` and misses `ell = 18` by 2% above the slow end: 16.9 ms against a
predicted 10.0–16.6 ms. That miss is the host term again. -/
theorem tower256_t4_range_bracket :
    tower256DeviceBound t4MulHi t4KeccakHi 20 ≤ 670 / 10000 ∧
      670 / 10000 ≤ tower256DeviceBound t4MulLo t4KeccakLo 20 ∧
      tower256DeviceBound t4MulHi t4KeccakHi 22 ≤ 3035 / 10000 ∧
      3035 / 10000 ≤ tower256DeviceBound t4MulLo t4KeccakLo 22 ∧
      tower256DeviceBound t4MulLo t4KeccakLo 18 < 169 / 10000 := by
  native_decide

/-- **The binding resource of the T4 encode is the multiply, not memory**: the multiply kernels'
arithmetic time exceeds their own traffic time by more than 5× at `ell = 20` (45.9 ms of multiplies
against 8.4 ms of bytes). This is ROTATION §2(c)'s "the prover is multiply-bound on SIMT", derived. -/
theorem tower256_encode_multiply_bound :
    let k := (ldeKernels tower256Bytes .additive 1 18 2).head!
    5 * (k.memBytes / t4CopyBw) < k.baseMuls / t4SessionMul := by
  native_decide

/-- **The Tower256 production shape reads 100 bits at unique decoding** through the same security
function: 148 queries at rate 1/4 is exactly the UD-100 query count, and the 256-bit field puts the
algebraic wall out of reach. -/
theorem tower256_reads_100 : udrBits deployedAdversary tower256Params (tower256Shape 20) = 100 := by
  native_decide

/-! ## §3 ROTATION: per-element bytes and the binding resource of the INT8 route -/

/-- Bytes moved per element by the unfused T4 INT8 fixed-r Tower256 route: 256 unpacked operand bytes
written and read, 256 four-byte counts written and read, plus 64 B in and out (ROTATION §2(b)). -/
def t4Int8UnfusedBytes : ℕ := 2624

/-- The fused route's bytes per element: 32 B in, 32 B operand share, 32 B out. -/
def t4FusedBytes : ℕ := 96

/-- The T4 table multiply, measured in the same session: 1.85 ns per element. -/
def t4TableMul : ℚ := 185 / (100 * 10 ^ 9)

/-- The unfused INT8 route, measured end to end: 21.4 ns per element. -/
def t4Int8RouteMeasured : ℚ := 214 / (10 * 10 ^ 9)

/-- ⚑ **The unfused INT8 route was predictably a loss.** Its HBM floor alone, 2,624 B over 234 GB/s =
11.2 ns, is six times the table multiply, so no tensor rate could have rescued it; the measured 21.4 ns
sits above the floor, as a floor must. The fused route's floor is 0.41 ns, under the table: the win
exists only fused. -/
theorem rotation_unfused_route_loses_on_t4 :
    6 * t4TableMul < t4Int8UnfusedBytes / t4CopyBw ∧
      (t4Int8UnfusedBytes : ℚ) / t4CopyBw ≤ t4Int8RouteMeasured ∧
      (t4FusedBytes : ℚ) / t4CopyBw < t4TableMul := by
  native_decide

/-! ## §4 TPU v5e: the rules in STYLE.md, derived from the peaks -/

/-- v5e int8 MXU peak, 3.94e14 op/s, and HBM bandwidth 8.2e11 B/s (scaling-book, STYLE.md). -/
def v5eInt8 : ℚ := 394 * 10 ^ 12
def v5eHbm : ℚ := 82 * 10 ^ 10

/-- The roofline ridge: ops per byte at which the int8 MXU and HBM bind equally. -/
def v5eRidge : ℚ := v5eInt8 / v5eHbm

/-- An `n × n × n` int8 matmul with an int32 output: `2n³` ops over `n² + n² + 4n²` bytes. -/
def int8GemmIntensity (n : ℕ) : ℚ := 2 * (n : ℚ) ^ 3 / (6 * (n : ℚ) ^ 2)

theorem int8GemmIntensity_eq {n : ℕ} (hn : 0 < n) : int8GemmIntensity n = n / 3 := by
  have : (0 : ℚ) < n := by exact_mod_cast hn
  unfold int8GemmIntensity
  field_simp
  ring

/-- ⚑ **STYLE.md's "an int8 GEMM is HBM-bound until M, N, K are all well above ~1500", derived**: a
square int8 GEMM with int32 output is HBM-bound on v5e exactly when `n < 3 × ridge ≈ 1441.5`. -/
theorem int8Gemm_hbm_bound_iff {n : ℕ} (hn : 0 < n) :
    int8GemmIntensity n < v5eRidge ↔ (n : ℚ) < 3 * v5eRidge := by
  rw [int8GemmIntensity_eq hn]
  constructor <;> intro h <;> linarith

theorem three_ridge_value : 1441 < 3 * v5eRidge ∧ 3 * v5eRidge < 1442 := by
  unfold v5eRidge v5eInt8 v5eHbm; norm_num

/-- **STYLE.md page 1, rule 2, as arithmetic**: at `n = 1024` the HBM time (6 MiB at 820 GB/s, 7.67 µs)
exceeds the compute time (`2^31` ops at 394 TOPS, 5.45 µs), so the bound is 7.7 µs, not 5.45. -/
theorem int8Gemm_1024_bound :
    2 * (1024 : ℚ) ^ 3 / v5eInt8 < 6 * 1024 ^ 2 / v5eHbm ∧
      6 * (1024 : ℚ) ^ 2 / v5eHbm < 77 / (10 * 10 ^ 6) := by
  unfold v5eInt8 v5eHbm; norm_num

/--
info: 'Minidregg.Assurance.Cost.Calibration.tower256_t4_session_prediction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tower256_t4_session_prediction._native.native_decide.ax_1_1]
-/
#guard_msgs in #print axioms tower256_t4_session_prediction

end Minidregg.Assurance.Cost.Calibration
