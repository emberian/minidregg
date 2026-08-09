//! `[PROVER-commit]` half 1 — the Poseidon2-style permutation, mirroring
//! `Compiler/AirHash.lean`'s EXECUTOR `permExec`.
//!
//! Substrate, said out loud: this is UNVERIFIED COMPUTE following the verified emit
//! seam. The Lean side proved `permGadget_eval` — circuit ⟺ executor — about ITS
//! objects; this file re-implements the executor's arithmetic in Rust so the
//! prover's commitment hash is (on the tested vectors) the hash the Lean proved
//! things about. There is no formal semantics of Rust, so the agreement is
//! established by CONFORMANCE VECTORS (`prover/testdata/poseidon_conformance.json`,
//! written by the Lean `#eval` in `Compiler/EmitSerialize.lean`; plus the
//! kernel-decided `ZMod 13` example of `Compiler/AirHash.lean` §6) — never called
//! refinement or verification. Agreement on vectors is all it establishes.
//!
//! The mirrored semantics (`AirHash` §3, `roundExec`):
//! one round = add round constants (ALL wires, full and partial alike) → S-box
//! `x ^ α` (full round: every wire; partial round: wire 0 only) → linear layer
//! (`out[i] = Σⱼ M[i][j] · sboxed[j]`, row-times-vector). `permExec` folds the
//! round schedule left-to-right; `hashExec` is output wire 0 (sponge-style squeeze
//! of one element).
//!
//! Parameter status: `demo_spec` below is a CONFORMANCE instantiation (small,
//! concrete, chosen so the vector pins the wiring — non-symmetric matrices catch a
//! transposed linear layer, distinct per-round matrices catch schedule mix-ups).
//! The deployed BabyBear Poseidon2 constant set — real round counts from the
//! security analysis, published round constants and MDS/internal matrices — is
//! `[PROVER-poseidon-params]` (matching the Lean side's `[AIR-poseidon-params]`):
//! NAMED, not invented here.

use serde::Deserialize;

use crate::descriptor::Fp;

/// Mirror of `AirHash.Round`: one round's constants, full/partial flag, and linear
/// layer. `m[i][j]` is row `i`, column `j` — the executor computes
/// `out[i] = Σⱼ m[i][j] · sboxed[j]`.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Round {
    /// Round constants, one per wire (length = width).
    pub rc: Vec<Fp>,
    /// `true`: full round (S-box every wire); `false`: partial (wire 0 only).
    pub full: bool,
    /// The linear layer, row-major: `m[i][j]` multiplies sboxed wire `j` into
    /// output wire `i`.
    pub m: Vec<Vec<Fp>>,
}

/// Mirror of `AirHash.PermSpec`: S-box exponent, width, round schedule (in
/// application order). The width is explicit here (Lean carries it as the type
/// index `w`).
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PermSpec {
    /// The S-box exponent (`α = 5` typical).
    pub alpha: u64,
    /// The state width `w`.
    pub width: usize,
    /// The round schedule, applied left to right.
    pub rounds: Vec<Round>,
}

impl PermSpec {
    /// Shape check: every round's `rc` and `m` sized to `width`, all entries
    /// canonical mod `p`. A reader-side input contract (the Lean writer emits
    /// well-shaped specs by construction), not a proof.
    pub fn validate(&self, p: u64) -> Result<(), String> {
        if self.width == 0 {
            return Err("width 0: no wire 0 to squeeze".into());
        }
        for (ri, r) in self.rounds.iter().enumerate() {
            if r.rc.len() != self.width {
                return Err(format!(
                    "round {ri}: rc has {} entries, width {}",
                    r.rc.len(),
                    self.width
                ));
            }
            if r.m.len() != self.width || r.m.iter().any(|row| row.len() != self.width) {
                return Err(format!("round {ri}: m is not {0}x{0}", self.width));
            }
            for &c in r.rc.iter().chain(r.m.iter().flatten()) {
                if c >= p {
                    return Err(format!("round {ri}: non-canonical constant {c} (mod {p})"));
                }
            }
        }
        Ok(())
    }
}

/// `x ^ e` mod `p` by square-and-multiply. `e = 0` gives `1` (including `0^0 = 1`,
/// matching Lean's `Monoid.npow` and `sbox 0 = cst 1`).
pub fn pow_mod(x: Fp, e: u64, p: u64) -> Fp {
    let mut base = x % p;
    let mut e = e;
    let mut acc: u64 = 1 % p;
    while e > 0 {
        if e & 1 == 1 {
            acc = ((acc as u128 * base as u128) % p as u128) as u64;
        }
        base = ((base as u128 * base as u128) % p as u128) as u64;
        e >>= 1;
    }
    acc
}

fn add_mod(a: Fp, b: Fp, p: u64) -> Fp {
    ((a as u128 + b as u128) % p as u128) as u64
}

fn mul_mod(a: Fp, b: Fp, p: u64) -> Fp {
    ((a as u128 * b as u128) % p as u128) as u64
}

/// One round, mirroring `AirHash.roundExec`:
/// `out[i] = Σⱼ m[i][j] · sboxLayer(state[j] + rc[j])` where the S-box applies to
/// every wire in a full round and to wire 0 only in a partial round. Round
/// constants are added to ALL wires in both kinds.
fn round_exec(alpha: u64, r: &Round, state: &[Fp], p: u64) -> Vec<Fp> {
    let sboxed: Vec<Fp> = state
        .iter()
        .enumerate()
        .map(|(j, &x)| {
            let x = add_mod(x, r.rc[j], p);
            if r.full || j == 0 {
                pow_mod(x, alpha, p)
            } else {
                x
            }
        })
        .collect();
    (0..state.len())
        .map(|i| {
            sboxed.iter().enumerate().fold(0u64, |acc, (j, &s)| {
                add_mod(acc, mul_mod(r.m[i][j], s, p), p)
            })
        })
        .collect()
}

/// The permutation, mirroring `AirHash.permExec`: the round schedule folded left
/// to right over the state. `state` must have length `spec.width`, entries
/// canonical mod `p`.
pub fn perm(spec: &PermSpec, state: &[Fp], p: u64) -> Vec<Fp> {
    assert_eq!(
        state.len(),
        spec.width,
        "state length must equal the spec width"
    );
    assert!(
        state.iter().all(|&x| x < p),
        "state entries must be canonical mod p"
    );
    spec.rounds
        .iter()
        .fold(state.to_vec(), |st, r| round_exec(spec.alpha, r, &st, p))
}

/// The hash, mirroring `AirHash.hashExec`: the permutation's output wire 0
/// (sponge-style squeeze of one element; rate/capacity discipline is
/// `[PROVER-poseidon-params]` territory).
pub fn hash(spec: &PermSpec, input: &[Fp], p: u64) -> Fp {
    perm(spec, input, p)[0]
}

/// **The fixed conformance spec** over BabyBear (`[PROVER-field]`,
/// `p = 2013265921`): width 2, `α = 5`, three rounds (full · partial · full) with
/// non-symmetric, per-round-distinct matrices so the conformance vector pins the
/// row/column orientation and the schedule wiring. The SAME spec is instantiated
/// at `Compiler/EmitSerialize.lean` §6 (`proverPermSpec`), where the Lean
/// `permExec` output is kernel-decided and written to
/// `prover/testdata/poseidon_conformance.json`; the integration test asserts this
/// function equals the parsed spec, then that `perm` reproduces the Lean output.
/// A DEMO instantiation — the deployed constant set is `[PROVER-poseidon-params]`.
pub fn demo_spec() -> PermSpec {
    let m1 = vec![vec![2, 1], vec![4, 3]]; // det 2, non-symmetric
    let m2 = vec![vec![1, 5], vec![2, 3]]; // det -7, non-symmetric
    PermSpec {
        alpha: 5,
        width: 2,
        rounds: vec![
            Round {
                rc: vec![3, 5],
                full: true,
                m: m1.clone(),
            },
            Round {
                rc: vec![1, 7],
                full: false,
                m: m2,
            },
            Round {
                rc: vec![2, 4],
                full: true,
                m: m1,
            },
        ],
    }
}

/// The BabyBear modulus, `[PROVER-field]`.
pub const BABY_BEAR_P: u64 = 2_013_265_921;

#[cfg(test)]
mod tests {
    use super::*;

    /// The `ZMod 13` demo of `Compiler/AirHash.lean` §6 — `permExec demoSpec
    /// ![4, 9] = ![4, 3]`, KERNEL-DECIDED there (`by decide`). The matrix is
    /// symmetric, so this vector alone does not pin orientation; the BabyBear
    /// vector (integration test) does.
    #[test]
    fn matches_airhash_zmod13_decided_example() {
        let m = vec![vec![2, 1], vec![1, 3]];
        let spec = PermSpec {
            alpha: 5,
            width: 2,
            rounds: vec![
                Round {
                    rc: vec![3, 5],
                    full: true,
                    m: m.clone(),
                },
                Round {
                    rc: vec![1, 7],
                    full: false,
                    m: m.clone(),
                },
                Round {
                    rc: vec![2, 4],
                    full: true,
                    m,
                },
            ],
        };
        spec.validate(13).unwrap();
        assert_eq!(perm(&spec, &[4, 9], 13), vec![4, 3]);
        assert_eq!(hash(&spec, &[4, 9], 13), 4);
    }

    #[test]
    fn pow_mod_edge_cases() {
        assert_eq!(pow_mod(0, 0, 13), 1, "0^0 = 1 (Lean Monoid.npow)");
        assert_eq!(pow_mod(7, 0, 13), 1);
        assert_eq!(pow_mod(0, 5, 13), 0);
        assert_eq!(pow_mod(2, 5, 13), 32 % 13);
        assert_eq!(pow_mod(BABY_BEAR_P - 1, 2, BABY_BEAR_P), 1, "(-1)^2 = 1");
    }

    /// A partial round S-boxes wire 0 ONLY, but adds rc to every wire.
    #[test]
    fn partial_round_sboxes_wire_zero_only() {
        let id = vec![vec![1, 0], vec![0, 1]];
        let spec = PermSpec {
            alpha: 3,
            width: 2,
            rounds: vec![Round {
                rc: vec![1, 1],
                full: false,
                m: id,
            }],
        };
        // wire 0: (2+1)^3 = 27 mod 97; wire 1: 4+1 = 5, no S-box.
        assert_eq!(perm(&spec, &[2, 4], 97), vec![27, 5]);
    }

    #[test]
    fn demo_spec_is_well_shaped() {
        demo_spec().validate(BABY_BEAR_P).unwrap();
    }
}
