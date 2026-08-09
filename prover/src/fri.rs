//! `[PROVER-fri-fold]` — a native CPU implementation of one FRI fold formula.
//!
//! This is UNVERIFIED COMPUTE. Rust selects the field representation, domain
//! order, pair order, twiddle convention, and beta-squaring schedule used here.
//! No compiled generated adapter currently pins those choices or connects this
//! module to Lean-owned control. The per-pair formula is the one also used by
//! breadstuffs' `hidingfri_fold_ext4.wgsl` experiment:
//!
//! ```text
//! folded = halve(lo + hi) + base_mul(mul(sub(lo, hi), beta), twiddle)
//! ```
//!
//! Algebraically, that formula is intended to correspond to
//! `Loom/Proximity.lean`'s `Fold(f, beta)(x^2) = (f(x) + f(-x))/2 +
//! beta * (f(x) - f(-x))/(2x)` under the stated conventions. There is no
//! refinement theorem or semantic relation for this Rust. The only
//! cross-language evidence is agreement on the captured values in
//! `prover/testdata/fri_conformance.json`.
//!
//! Layout: NATURAL order — element `j` is `f(g^j)`, pairs are `(j, j + n/2)`,
//! twiddle `j` is `1/2 * g^{-j}`. The bundled WGSL instead selects bit-reversed
//! storage (pairs adjacent, twiddle table bit-reversed). A native Rust test
//! compares the two layouts for exercised inputs; it is not a proof that either
//! layout implements a Lean profile. This module has no wgpu dependency.

use crate::field4::{binv, bmul, two_adic_generator, Ext4, HALF, TWO_ADIC_BITS};

/// The fold twiddles in NATURAL order: `twiddle[j] = 1/2 * g^{-j}` for
/// `j < n/2`, `g` the canonical generator of order `n = 2^log_n` (the
/// evaluation-domain generator; the codeword length).
pub fn halve_inv_powers(log_n: u32) -> Vec<u64> {
    assert!(log_n >= 1 && log_n <= TWO_ADIC_BITS);
    let half_n = 1usize << (log_n - 1);
    let g_inv = binv(two_adic_generator(log_n));
    let mut out = Vec::with_capacity(half_n);
    let mut cur = HALF;
    for _ in 0..half_n {
        out.push(cur);
        cur = bmul(cur, g_inv);
    }
    out
}

/// The same table in the bundled WGSL's selected BIT-REVERSED layout
/// (`table[j] = 1/2 * g^{-bitrev(j)}`). Provided for `[PROVER-fri-wgsl]`; the
/// CPU implementation below works in natural order.
pub fn halve_inv_powers_bitrev(log_n: u32) -> Vec<u64> {
    bit_reverse_permute(&halve_inv_powers(log_n))
}

/// Reverse the low `bits` bits of `i`.
#[inline]
pub fn bit_reverse(i: usize, bits: u32) -> usize {
    if bits == 0 {
        0
    } else {
        i.reverse_bits() >> (usize::BITS - bits)
    }
}

/// Permute a power-of-two-length slice into bit-reversed order (an involution).
pub fn bit_reverse_permute<T: Copy>(v: &[T]) -> Vec<T> {
    assert!(v.len().is_power_of_two());
    let bits = v.len().trailing_zeros();
    (0..v.len()).map(|i| v[bit_reverse(i, bits)]).collect()
}

/// One native 2-to-1 fold round at challenge `beta`: length `n -> n/2`, pairing
/// `(j, j + n/2)`. The formula is intended to mirror Loom's fold after the
/// Rust-selected domain and representation conventions; no adapter establishes
/// that correspondence.
pub fn fold_once(codeword: &[Ext4], beta: Ext4) -> Vec<Ext4> {
    let n = codeword.len();
    assert!(
        n >= 2 && n.is_power_of_two(),
        "fold_once: length must be a power of two >= 2"
    );
    let log_n = n.trailing_zeros();
    assert!(
        log_n <= TWO_ADIC_BITS,
        "fold_once: domain exceeds BabyBear 2-adicity"
    );
    let twiddles = halve_inv_powers(log_n);
    let half = n / 2;
    (0..half)
        .map(|j| {
            let lo = codeword[j];
            let hi = codeword[j + half];
            lo.add(hi)
                .halve()
                .add(lo.sub(hi).mul(beta).base_mul(twiddles[j]))
        })
        .collect()
}

/// The arity-`2^log_arity` native fold: `log_arity` pairwise rounds, squaring
/// the challenge each round (`beta, beta^2, beta^4, ...`). This is a
/// Rust-selected schedule intended to resemble Loom's iterated fold; no
/// generated suite currently pins it. `log_arity = 0` is the identity.
pub fn fold(codeword: &[Ext4], beta: Ext4, log_arity: usize) -> Vec<Ext4> {
    assert!(codeword.len().is_power_of_two());
    assert!(
        (log_arity as u32) <= codeword.len().trailing_zeros(),
        "fold: arity exceeds codeword length"
    );
    let mut word = codeword.to_vec();
    let mut b = beta;
    for _ in 0..log_arity {
        word = fold_once(&word, b);
        b = b.square();
    }
    word
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field4::P;

    fn prng(seed: &mut u64) -> u64 {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (*seed >> 16) % P
    }

    fn prng_word(seed: &mut u64, n: usize) -> Vec<Ext4> {
        (0..n)
            .map(|_| Ext4 {
                c: [prng(seed), prng(seed), prng(seed), prng(seed)],
            })
            .collect()
    }

    #[test]
    fn fold_halves_the_length_per_round() {
        let mut seed = 3u64;
        let cw = prng_word(&mut seed, 16);
        let beta = Ext4 {
            c: [
                prng(&mut seed),
                prng(&mut seed),
                prng(&mut seed),
                prng(&mut seed),
            ],
        };
        for k in 0..=4 {
            assert_eq!(fold(&cw, beta, k).len(), 16 >> k);
        }
    }

    #[test]
    fn arity_fold_is_iterated_pairwise_with_beta_squaring() {
        let mut seed = 9u64;
        let cw = prng_word(&mut seed, 16);
        let beta = Ext4 {
            c: [
                prng(&mut seed),
                prng(&mut seed),
                prng(&mut seed),
                prng(&mut seed),
            ],
        };
        let two_rounds = fold_once(&fold_once(&cw, beta), beta.square());
        assert_eq!(fold(&cw, beta, 2), two_rounds);
        let three = fold_once(&two_rounds, beta.square().square());
        assert_eq!(fold(&cw, beta, 3), three);
    }

    #[test]
    fn constant_word_folds_to_itself() {
        // a constant word is a degree-<1 codeword: (c+c)/2 + beta*(c-c)*tw = c,
        // for EVERY beta (fold_preserves_code at the base of the tower).
        let mut seed = 11u64;
        let c = Ext4 {
            c: [
                prng(&mut seed),
                prng(&mut seed),
                prng(&mut seed),
                prng(&mut seed),
            ],
        };
        let beta = Ext4 {
            c: [
                prng(&mut seed),
                prng(&mut seed),
                prng(&mut seed),
                prng(&mut seed),
            ],
        };
        let cw = vec![c; 8];
        assert_eq!(fold(&cw, beta, 3), vec![c]);
    }

    #[test]
    fn tampered_element_changes_the_fold() {
        let mut seed = 5u64;
        let cw = prng_word(&mut seed, 16);
        let beta = Ext4 {
            c: [
                prng(&mut seed),
                prng(&mut seed),
                prng(&mut seed),
                prng(&mut seed),
            ],
        };
        let reference = fold(&cw, beta, 1);
        for j in 0..16 {
            let mut bad = cw.clone();
            bad[j].c[0] = (bad[j].c[0] + 1) % P;
            assert_ne!(
                fold(&bad, beta, 1),
                reference,
                "tampering element {j} must show"
            );
        }
    }

    #[test]
    fn bitrev_layout_matches_natural_fold() {
        // The deployed kernel's working layout: input stored bit-reversed
        // (pairs ADJACENT: (2j, 2j+1)), twiddle table bit-reversed
        // (halve_inv_powers_bitrev). Same per-pair algebra; the output is the
        // bit-reversal of our natural-order fold.
        let mut seed = 17u64;
        let cw = prng_word(&mut seed, 16);
        let beta = Ext4 {
            c: [
                prng(&mut seed),
                prng(&mut seed),
                prng(&mut seed),
                prng(&mut seed),
            ],
        };

        let natural = fold_once(&cw, beta);

        let cw_rev = bit_reverse_permute(&cw);
        let tw_rev = halve_inv_powers_bitrev(4);
        let folded_rev: Vec<Ext4> = (0..8)
            .map(|j| {
                let lo = cw_rev[2 * j];
                let hi = cw_rev[2 * j + 1];
                lo.add(hi)
                    .halve()
                    .add(lo.sub(hi).mul(beta).base_mul(tw_rev[j]))
            })
            .collect();

        assert_eq!(folded_rev, bit_reverse_permute(&natural));
    }

    #[test]
    fn twiddle_tables_agree_under_bit_reversal() {
        for log_n in [1u32, 2, 3, 4, 5] {
            let nat = halve_inv_powers(log_n);
            let rev = halve_inv_powers_bitrev(log_n);
            assert_eq!(bit_reverse_permute(&rev), nat);
            assert_eq!(nat[0], HALF, "twiddle 0 is 1/2 (g^0 = 1)");
        }
    }
}
