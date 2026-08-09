//! `[PROVER-fri-fold]` field layer: BabyBear and its degree-4 extension (X^4 = 11)
//! — the arithmetic under the adopted FRI fold kernel.
//!
//! Substrate, said out loud: UNVERIFIED COMPUTE following the verified emit seam.
//! This module ADOPTS the field math of breadstuffs' deployed
//! `hidingfri_fold_ext4.wgsl` kernel (BabyBear^4 as four canonical `u64` lanes,
//! X^4 = 11; the wgsl's Montgomery form is a GPU optimization this CPU reference
//! does not need) into OUR crate — it never inherits the Plonky3 stack. The
//! extension-multiplication FORMULA is theorem-tied on the Lean side
//! (`Compiler/FriConformance.lean`'s `ext4Mul_correct`: the formula IS
//! multiplication in `BabyBear[X]/(X^4 - 11)`), and this module reproduces the
//! Lean-computed vectors (`prover/testdata/fri_conformance.json`) as diagnostic
//! arithmetic data. Rust has no semantic relation to Lean.
//!
//! NOT claimed anywhere: irreducibility of `X^4 - 11` over BabyBear (that the
//! quotient is a FIELD, so the `|F| = p^4` soundness pricing of
//! `Loom/SmallField.lean` applies to THIS concrete quotient) — named residual
//! `[PROVER-field-ext4-irred]`. `Ext4` deliberately implements no inversion.

/// The BabyBear prime `p = 2^31 - 2^27 + 1` — the deployed base field
/// (`[PROVER-field]`, proved prime on the Lean side in `Compiler/EmitSerialize`).
pub const P: u64 = 2013265921;

/// The extension constant: `BabyBear^4 = BabyBear[X]/(X^4 - EXT_W)`.
pub const EXT_W: u64 = 11;

/// `2^{-1} mod p` — the halving constant of the fold (`(p + 1)/2`).
pub const HALF: u64 = (P + 1) / 2;

/// The 2-adicity of BabyBear: `p - 1 = 15 * 2^27`.
pub const TWO_ADIC_BITS: u32 = 27;

/// The canonical generator of the order-`2^27` subgroup: `31^15 mod p`
/// (31 generates the full multiplicative group). Pinned by tests below and
/// against the Lean conformance domain.
pub const TWO_ADIC_GENERATOR: u64 = 440564289;

/// Base-field addition on canonical representatives.
#[inline]
pub fn badd(a: u64, b: u64) -> u64 {
    debug_assert!(a < P && b < P);
    let s = a + b;
    if s >= P {
        s - P
    } else {
        s
    }
}

/// Base-field subtraction on canonical representatives.
#[inline]
pub fn bsub(a: u64, b: u64) -> u64 {
    debug_assert!(a < P && b < P);
    if a >= b {
        a - b
    } else {
        a + P - b
    }
}

/// Base-field multiplication (u128 intermediate, exact).
#[inline]
pub fn bmul(a: u64, b: u64) -> u64 {
    debug_assert!(a < P && b < P);
    ((a as u128 * b as u128) % P as u128) as u64
}

/// Base-field exponentiation by squaring.
pub fn bpow(mut base: u64, mut exp: u64) -> u64 {
    debug_assert!(base < P);
    let mut acc = 1u64;
    while exp > 0 {
        if exp & 1 == 1 {
            acc = bmul(acc, base);
        }
        base = bmul(base, base);
        exp >>= 1;
    }
    acc
}

/// Base-field inverse via Fermat: `a^{p-2}`. Panics on zero.
pub fn binv(a: u64) -> u64 {
    assert!(a != 0 && a < P, "binv: not an invertible canonical element");
    bpow(a, P - 2)
}

/// The canonical generator of the order-`2^bits` subgroup: repeated squaring of
/// `TWO_ADIC_GENERATOR` — the same descent the Lean conformance domain uses
/// (`g_bits = g_27^(2^(27-bits))`).
pub fn two_adic_generator(bits: u32) -> u64 {
    assert!(bits <= TWO_ADIC_BITS, "two_adic_generator: bits > 27");
    let mut g = TWO_ADIC_GENERATOR;
    for _ in bits..TWO_ADIC_BITS {
        g = bmul(g, g);
    }
    g
}

/// An element of BabyBear^4 = `BabyBear[X]/(X^4 - 11)`: four canonical
/// coefficient lanes `c[0] + c[1] X + c[2] X^2 + c[3] X^3`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ext4 {
    pub c: [u64; 4],
}

impl Ext4 {
    pub const ZERO: Ext4 = Ext4 { c: [0, 0, 0, 0] };
    pub const ONE: Ext4 = Ext4 { c: [1, 0, 0, 0] };

    /// Embed a base-field element (lane 0).
    #[inline]
    pub fn from_base(x: u64) -> Ext4 {
        debug_assert!(x < P);
        Ext4 { c: [x, 0, 0, 0] }
    }

    /// Componentwise addition.
    #[inline]
    pub fn add(self, o: Ext4) -> Ext4 {
        Ext4 {
            c: [
                badd(self.c[0], o.c[0]),
                badd(self.c[1], o.c[1]),
                badd(self.c[2], o.c[2]),
                badd(self.c[3], o.c[3]),
            ],
        }
    }

    /// Componentwise subtraction.
    #[inline]
    pub fn sub(self, o: Ext4) -> Ext4 {
        Ext4 {
            c: [
                bsub(self.c[0], o.c[0]),
                bsub(self.c[1], o.c[1]),
                bsub(self.c[2], o.c[2]),
                bsub(self.c[3], o.c[3]),
            ],
        }
    }

    /// The adopted extension multiplication, `X^4 = 11` (the deployed kernel's
    /// formula; proved to be the quotient-ring multiplication on the Lean side,
    /// `ext4Mul_correct`).
    pub fn mul(self, o: Ext4) -> Ext4 {
        let a = &self.c;
        let b = &o.c;
        let w = EXT_W;
        let c0 = badd(
            bmul(a[0], b[0]),
            bmul(
                w,
                badd(badd(bmul(a[1], b[3]), bmul(a[2], b[2])), bmul(a[3], b[1])),
            ),
        );
        let c1 = badd(
            badd(bmul(a[0], b[1]), bmul(a[1], b[0])),
            bmul(w, badd(bmul(a[2], b[3]), bmul(a[3], b[2]))),
        );
        let c2 = badd(
            badd(badd(bmul(a[0], b[2]), bmul(a[1], b[1])), bmul(a[2], b[0])),
            bmul(w, bmul(a[3], b[3])),
        );
        let c3 = badd(
            badd(badd(bmul(a[0], b[3]), bmul(a[1], b[2])), bmul(a[2], b[1])),
            bmul(a[3], b[0]),
        );
        Ext4 {
            c: [c0, c1, c2, c3],
        }
    }

    /// `self * self` — the beta-squaring step of the arity-`2^k` fold.
    #[inline]
    pub fn square(self) -> Ext4 {
        self.mul(self)
    }

    /// Scale by a base-field scalar (the twiddle multiplication of the fold).
    #[inline]
    pub fn base_mul(self, s: u64) -> Ext4 {
        Ext4 {
            c: [
                bmul(self.c[0], s),
                bmul(self.c[1], s),
                bmul(self.c[2], s),
                bmul(self.c[3], s),
            ],
        }
    }

    /// Divide by 2 (`x * 2^{-1}`) — the even-component halving of the fold.
    #[inline]
    pub fn halve(self) -> Ext4 {
        self.base_mul(HALF)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Deterministic pseudorandom canonical elements (tiny LCG; test-only).
    fn prng(seed: &mut u64) -> u64 {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (*seed >> 16) % P
    }

    fn prng_ext(seed: &mut u64) -> Ext4 {
        Ext4 {
            c: [prng(seed), prng(seed), prng(seed), prng(seed)],
        }
    }

    #[test]
    fn two_adic_generator_is_31_pow_15_of_order_2_pow_27() {
        assert_eq!(bpow(31, 15), TWO_ADIC_GENERATOR);
        assert_eq!(bpow(TWO_ADIC_GENERATOR, 1 << 26), P - 1, "g^(2^26) = -1");
        // descent: each two_adic_generator(b) has exact order 2^b
        for b in [1u32, 2, 4, 27] {
            let g = two_adic_generator(b);
            assert_eq!(bpow(g, 1 << (b - 1)), P - 1, "order exactly 2^{b}");
        }
        assert_eq!(two_adic_generator(0), 1);
    }

    #[test]
    fn half_is_inverse_of_two() {
        assert_eq!(HALF, binv(2));
        assert_eq!(bmul(HALF, 2), 1);
    }

    #[test]
    fn binv_on_samples() {
        let mut seed = 1u64;
        for _ in 0..16 {
            let a = prng(&mut seed);
            if a != 0 {
                assert_eq!(bmul(a, binv(a)), 1);
            }
        }
    }

    #[test]
    fn x_pow_4_is_11() {
        let x = Ext4 { c: [0, 1, 0, 0] };
        assert_eq!(x.mul(x).mul(x).mul(x), Ext4::from_base(EXT_W));
        // and X^2 * X^2 agrees
        assert_eq!(x.square().square(), Ext4::from_base(EXT_W));
    }

    #[test]
    fn ext_ring_laws_on_samples() {
        let mut seed = 42u64;
        for _ in 0..8 {
            let a = prng_ext(&mut seed);
            let b = prng_ext(&mut seed);
            let c = prng_ext(&mut seed);
            assert_eq!(a.mul(b), b.mul(a), "commutativity");
            assert_eq!(a.mul(b).mul(c), a.mul(b.mul(c)), "associativity");
            assert_eq!(a.mul(b.add(c)), a.mul(b).add(a.mul(c)), "distributivity");
            assert_eq!(a.mul(Ext4::ONE), a);
            assert_eq!(a.mul(Ext4::ZERO), Ext4::ZERO);
            assert_eq!(a.sub(b).add(b), a);
            assert_eq!(a.halve().add(a.halve()), a, "halve is division by 2");
            assert_eq!(a.halve().base_mul(2), a);
        }
    }

    #[test]
    fn from_base_is_a_ring_embedding_on_samples() {
        let mut seed = 7u64;
        for _ in 0..16 {
            let a = prng(&mut seed);
            let b = prng(&mut seed);
            assert_eq!(
                Ext4::from_base(a).mul(Ext4::from_base(b)),
                Ext4::from_base(bmul(a, b))
            );
            assert_eq!(
                Ext4::from_base(a).add(Ext4::from_base(b)),
                Ext4::from_base(badd(a, b))
            );
            assert_eq!(Ext4::from_base(a).base_mul(b), Ext4::from_base(bmul(a, b)));
        }
    }
}
