//! `[PROVER-sumcheck-gates]` — the descriptor's gate system AS the sumcheck claim.
//!
//! Substrate, said out loud: UNVERIFIED COMPUTE following the verified emit seam.
//! This file encodes the emitted `ConstraintDescriptor`'s gates into the hypercube
//! claim table whose sumcheck the Lean side PROVED sound, so `prove_sumcheck` runs
//! on the ACTUAL gate system, not an abstract table. There is no formal semantics
//! of Rust: the agreement with the Lean encoding is kept honest by conformance
//! vectors (kernel-decided values from `Assurance/AirSumcheck(Quadratic).lean`
//! reproduced in the tests) — never called refinement or verification.
//!
//! **The encoding, matched to the Lean by name.** Entry `k` of the defect table is
//! the satisfaction residual (`trueSum − target`) of the `k`-th encoded constraint:
//!
//! * ADD gate `a + b = out` → `wire(a) + wire(b) − wire(out)` — the residual of
//!   `Assurance/AirSumcheck.lean`'s `addGateLin` (faithful by `addGateLin_iff`:
//!   residual `= 0` IS `Gate.holds`);
//! * MUL gate `a · b = out` → `wire(a)·wire(b) − wire(out)` — the corner value of
//!   `Assurance/AirSumcheckQuadratic.lean`'s `defectWord`
//!   `D(j) = gateTableA·gateTableB − gateTableC` (by `defectWord_read`; the
//!   per-gate indicator claim is `mulConstraint`, faithful by `mulConstraint_iff`);
//! * zero-check (root pin) `w = 0` → `wire(w)` — the residual of `rootZero`
//!   (faithful by `rootZero_iff`);
//! * padding up to `2^m` → `0` — the Lean's `enc : Fin t ↪ (Fin m → Bool)`
//!   hypothesis instantiated at the LSB-first binary encoding `enc k = bits(k)`
//!   (`bitsToIdx`, the convention `sumcheck.rs` pins); off-image corners read `0`,
//!   exactly as `defectWord` does at padding corners.
//!
//! The table is all-zero iff the trace satisfies every gate and zero-check — the
//! composition of the three faithfulness iffs, mirrored here as
//! `gate_defect_table(d, w).all(zero) == descriptor_holds(d, w)` and CHECKED on
//! vectors (the demo descriptor, every single-wire tamper), not proved.
//!
//! **The batched claim.** `batch_defect_table` weights entry `k` by `γ^k` — the
//! γ-power combination of `Loom/ConstrainedCode.lean`'s `batchConstraint`
//! (`batchWt_eq_sum`). Since each entry is a constraint's residual, the batched
//! table's SUM is the batched constraint's own residual: zero for EVERY γ when all
//! gates hold (`list_as_single_sumcheck`; rendered for the gate system by
//! `airSumcheck_batch_complete` and `airMulSumcheck_batch_complete`).
//!
//! **The honest shape of what `prove_gates` proves.** It runs `prove_sumcheck` on
//! the γ-batched defect table, so the transcript establishes the ZERO-SUM of that
//! table (`claim = 0` for an honest trace) — the completeness direction "all gates
//! hold ⟹ the constraint claim holds". The soundness direction — a violated gate
//! survives the γ round for `≤ (t−1)/|F|` of γ and the sumcheck on a surviving γ
//! for `≤ v·d/|F|` (linear face) resp. `m·2/|F|` (quadratic face) — is what the
//! Lean PROVED: `airGateSystem_sound` (both horns, via `airSumcheck_retires_batch`
//! and `mulBatch_retired`), about ITS objects, at those bounds. Nothing here
//! re-derives or inherits that; a tamper being caught in the tests below is a
//! conformance vector for the encoding's teeth, not a soundness proof.
//!
//! Oracle-side caveat, stated: this rung's terminal check opens the batched defect
//! table's OWN multilinear extension (degree-≤1 rounds). The deployed factored
//! form — degree-2 rounds walking `(wt·Â)·B̂ − (wt·Ĉ)` against wire-word openings
//! (`quadHonest`'s shape), and the table-evaluation-to-wire-word linearization the
//! Lean names `[AIR-quadratic-selectors]` — is later plumbing, toward
//! `[PROVER-fri]`/`[PROVER-e2e]`. γ and the round challenges are CALLER-SUPPLIED;
//! drawing them from the transcript is `[PROVER-fs]`.

use crate::descriptor::{Descriptor, Fp, Gate, GateOp, Wire};
use crate::sumcheck::{add_mod, mul_mod, prove_sumcheck, sub_mod, verify_sumcheck, SumcheckProof};

/// Read a wire operand against the trace. Precondition: the descriptor passed
/// `validate()` and `wires.len() == nWires`, so every index is in range
/// (`emit_wellFormed` proved the Lean-emitted descriptor satisfies this); an
/// out-of-range read panics loudly rather than fabricating a defect.
fn read(wires: &[Fp], w: &Wire, p: u64) -> Fp {
    match *w {
        Wire::Const(c) => c % p,
        Wire::Wire(n) => *wires
            .get(n as usize)
            .unwrap_or_else(|| panic!("wire index {n} out of range — descriptor not validated?"))
            % p,
    }
}

/// One gate's defect: `a + b − out` (ADD, the `addGateLin` residual) or
/// `a·b − out` (MUL, the `defectWord` corner value).
fn gate_defect(g: &Gate, wires: &[Fp], p: u64) -> Fp {
    let a = read(wires, &g.a, p);
    let b = read(wires, &g.b, p);
    let out = *wires
        .get(g.out as usize)
        .unwrap_or_else(|| panic!("gate output {} out of range — descriptor not validated?", g.out))
        % p;
    match g.op {
        GateOp::Add => sub_mod(add_mod(a, b, p), out, p),
        GateOp::Mul => sub_mod(mul_mod(a, b, p), out, p),
    }
}

/// The claim table's length: gates + zero-checks, padded to the next power of two
/// (the hypercube the Lean's `enc` embedding targets; `t ≤ 2^m` is the padding
/// bookkeeping the Lean carries as a hypothesis). An empty system pads to `[0]`.
pub fn gate_claim_len(d: &Descriptor) -> usize {
    (d.gates.len() + d.zeros.len()).next_power_of_two()
}

/// The cube dimension `m` of the gate claim (`2^m = gate_claim_len`), i.e. the
/// number of sumcheck rounds / challenges `prove_gates` needs.
pub fn gate_cube_dim(d: &Descriptor) -> usize {
    gate_claim_len(d).trailing_zeros() as usize
}

/// The defect table of the gate system on a trace, over the gate-index hypercube:
/// entry `k < gates.len()` is gate `k`'s defect, the following entries are the
/// zero-checks' read values, the rest zero padding. All entries canonical mod
/// `d.p`. All-zero iff `descriptor_holds(d, wires)` — the mirror of the Lean
/// faithfulness iffs (`addGateLin_iff` / `mulConstraint_iff` / `rootZero_iff`),
/// cross-checked by the tests.
pub fn gate_defect_table(d: &Descriptor, wires: &[Fp]) -> Vec<Fp> {
    assert_eq!(
        wires.len(),
        d.n_wires as usize,
        "trace length must be nWires = {}",
        d.n_wires
    );
    let mut table = Vec::with_capacity(gate_claim_len(d));
    for g in &d.gates {
        table.push(gate_defect(g, wires, d.p));
    }
    for z in &d.zeros {
        table.push(read(wires, z, d.p));
    }
    table.resize(gate_claim_len(d), 0);
    table
}

/// γ-batch a defect table: entry `k` ↦ `γ^k · entry_k` — the γ-power combination
/// of `batchConstraint` (`batchWt_eq_sum`), applied residual-wise. The batched
/// table's sum is the batched constraint's residual: `0` for every γ on an honest
/// trace; a violating table survives as `0` for at most `(t−1)/|F|` of uniform γ
/// (`batch_survives_prob_le`, the Lean's γ-round bound — cited, not re-derived).
pub fn batch_defect_table(table: &[Fp], gamma: Fp, p: u64) -> Vec<Fp> {
    assert!(gamma < p, "batching challenge must be canonical mod p");
    let mut out = Vec::with_capacity(table.len());
    let mut pow: Fp = 1 % p;
    for &v in table {
        out.push(mul_mod(pow, v, p));
        pow = mul_mod(pow, gamma, p);
    }
    out
}

/// The gate-system sumcheck: `prove_sumcheck` on the γ-batched defect table. On an
/// honest trace the claim is `0` — the batched gate claim holds (the completeness
/// direction, `list_as_single_sumcheck`). The soundness that a violated gate is
/// CAUGHT at the proven bound is the Lean's `airGateSystem_sound`; this function
/// only computes the claim object it prices. `gamma` and `challenges`
/// (`gate_cube_dim(d)` of them) are caller-supplied until `[PROVER-fs]`.
pub fn prove_gates(d: &Descriptor, wires: &[Fp], gamma: Fp, challenges: &[Fp]) -> SumcheckProof {
    assert_eq!(
        challenges.len(),
        gate_cube_dim(d),
        "need gate_cube_dim(d) = {} round challenges",
        gate_cube_dim(d)
    );
    let table = batch_defect_table(&gate_defect_table(d, wires), gamma, d.p);
    prove_sumcheck(&table, challenges, d.p)
}

/// The gate-claim verifier: the batched defect table sums to ZERO (`claim == 0` —
/// the gate system's actual claim, target `0` throughout) and the sumcheck
/// transcript checks out against the batched table's MLE oracle (in deployment, an
/// opening of the committed table; here typically `|pt| mle_eval(&batched, pt, p)`).
/// Runs; does not verify in the formal sense — no Rust semantics.
pub fn verify_gates(proof: &SumcheckProof, batched_oracle: impl Fn(&[Fp]) -> Fp, p: u64) -> bool {
    proof.claim == 0 && verify_sumcheck(proof, batched_oracle, p)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sumcheck::mle_eval;
    use crate::trace::{descriptor_holds, generate_trace};

    /// The descriptor of `Compiler/AirFlatten.lean`'s `exFlat` example, `(x+2)·x`
    /// over ZMod 7 — the object `Assurance/AirSumcheck(Quadratic)`'s keystones
    /// compute on: gates `[x + 2 = aux₀, aux₀ · x = aux₁]`, root pin on `aux₁`.
    fn exflat() -> Descriptor {
        let d = Descriptor {
            p: 7,
            n_public: 1,
            n_vars: 1,
            n_wires: 3,
            gates: vec![
                Gate { op: GateOp::Add, a: Wire::Wire(0), b: Wire::Const(2), out: 1 },
                Gate { op: GateOp::Mul, a: Wire::Wire(1), b: Wire::Wire(0), out: 2 },
            ],
            zeros: vec![Wire::Wire(2)],
        };
        d.validate().expect("exflat well-formed");
        d
    }

    #[test]
    fn honest_trace_all_zero_table() {
        // x = 5: (5+2)·5 = 0 over ZMod 7 — accepted; the whole table vanishes.
        let d = exflat();
        let w = generate_trace(&d, &[5]);
        assert_eq!(gate_defect_table(&d, &w), vec![0, 0, 0, 0]);
        assert!(descriptor_holds(&d, &w));
    }

    #[test]
    fn mul_cheat_matches_lean_decided_defect() {
        // AirSumcheckQuadratic's exMulCheat: x = 3, aux₀ = 5 (add gate honest),
        // aux₁ = 0 (mul gate CHEATED). The Lean KERNEL-DECIDED the violated
        // claim's true defect: 5·3 − 0 = 1 (exMulCheat_trueSum). And the linear
        // face is blind to it (exMulCheat_shows_residual_real): add-gate and
        // root-pin entries are 0 — only the mul entry is hot.
        let d = exflat();
        let w = [3, 5, 0];
        assert_eq!(gate_defect_table(&d, &w), vec![0, 1, 0, 0]);
        assert!(!descriptor_holds(&d, &w));
    }

    #[test]
    fn wrong_aux_matches_lean_decided_residual() {
        // AirSumcheck's exWrong: x = 3, aux₀ = 4 (forced value 5), aux₁ = 1.
        // The Lean decided the add-gate claim's trueSum = 6 against target 5
        // (exWrong_trueSum): residual 6 − 5 = 1 = our add entry. Mul defect
        // 4·3 − 1 = 4; root pin reads 1.
        let d = exflat();
        let w = [3, 4, 1];
        assert_eq!(gate_defect_table(&d, &w), vec![1, 4, 1, 0]);
        assert!(!descriptor_holds(&d, &w));
    }

    #[test]
    fn table_zero_iff_descriptor_holds_on_all_single_tampers() {
        // The load-bearing mirror: all-zero table ⟺ descriptorHolds, exercised
        // on the honest trace and every single-wire tamper of it.
        let d = exflat();
        let honest = generate_trace(&d, &[5]);
        for wi in 0..honest.len() {
            for delta in 1..d.p {
                let mut w = honest.clone();
                w[wi] = (w[wi] + delta) % d.p;
                assert_eq!(
                    gate_defect_table(&d, &w).iter().all(|&v| v == 0),
                    descriptor_holds(&d, &w),
                    "wire {wi} += {delta}"
                );
            }
        }
    }

    #[test]
    fn batch_is_gamma_powers() {
        // batchWt_eq_sum's γ-power combination, on the nose.
        assert_eq!(batch_defect_table(&[1, 1, 1, 1], 2, 97), vec![1, 2, 4, 8]);
        assert_eq!(batch_defect_table(&[0, 1, 0, 0], 3, 7), vec![0, 3, 0, 0]);
    }

    #[test]
    fn prove_gates_honest_round_trip() {
        let d = exflat();
        let w = generate_trace(&d, &[5]);
        let (gamma, chal) = (3, [2, 6]);
        let proof = prove_gates(&d, &w, gamma, &chal);
        assert_eq!(proof.claim, 0, "honest trace: the batched gate claim is 0");
        let batched = batch_defect_table(&gate_defect_table(&d, &w), gamma, d.p);
        assert!(verify_gates(&proof, |pt| mle_eval(&batched, pt, d.p), d.p));
    }

    #[test]
    fn mul_cheat_claim_nonzero_and_rejected() {
        // The exMulCheat tamper the linear face cannot see: the batched claim is
        // γ^1·1 = γ ≠ 0 for every nonzero γ, and verify_gates rejects.
        let d = exflat();
        let w = [3, 5, 0];
        for gamma in 1..d.p {
            let proof = prove_gates(&d, &w, gamma, &[2, 6]);
            assert_eq!(proof.claim, gamma, "batched sum is γ·defect = γ·1");
            let batched = batch_defect_table(&gate_defect_table(&d, &w), gamma, d.p);
            assert!(!verify_gates(&proof, |pt| mle_eval(&batched, pt, d.p), d.p));
        }
    }

    #[test]
    fn gamma_round_teeth_and_survivor_bound() {
        // exWrong's table [1,4,1,0]: Σ γ^k·defect_k = 1 + 4γ + γ². A violating
        // table can survive SOME γ (the roots) — the Lean prices this at
        // ≤ (t−1)/|F| of γ (batch_survives_prob_le). Count the survivors: the
        // quadratic has ≤ 2 roots over ZMod 7, and t − 1 = 3 bounds it.
        let d = exflat();
        let table = gate_defect_table(&d, &[3, 4, 1]);
        let survivors = (0..d.p)
            .filter(|&g| batch_defect_table(&table, g, d.p).iter().fold(0, |a, &v| add_mod(a, v, d.p)) == 0)
            .count();
        assert!(survivors <= 3, "γ-round survivors {survivors} exceed t−1 = 3");
        assert!(survivors < d.p as usize, "some γ must catch the violation");
    }

    #[test]
    fn forged_zero_claim_on_violating_table_fails_sumcheck() {
        // A lying prover forging claim = 0 over the cheat's nonzero-sum table is
        // caught by the round-0 boolean check — the transcript has teeth even
        // before the oracle.
        let d = exflat();
        let w = [3, 5, 0];
        let gamma = 3;
        let mut proof = prove_gates(&d, &w, gamma, &[2, 6]);
        proof.claim = 0;
        let batched = batch_defect_table(&gate_defect_table(&d, &w), gamma, d.p);
        assert!(!verify_gates(&proof, |pt| mle_eval(&batched, pt, d.p), d.p));
    }

    #[test]
    fn empty_system_trivially_holds() {
        let d = Descriptor { p: 7, n_public: 0, n_vars: 0, n_wires: 0, gates: vec![], zeros: vec![] };
        d.validate().expect("empty descriptor well-formed");
        assert_eq!(gate_defect_table(&d, &[]), vec![0]);
        assert_eq!(gate_cube_dim(&d), 0);
        let proof = prove_gates(&d, &[], 3, &[]);
        assert!(verify_gates(&proof, |pt| mle_eval(&[0], pt, d.p), d.p));
    }
}
