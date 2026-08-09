//! Scalar BabyBear arithmetic used by the live Ext6 and MLE kernels.

/// BabyBear modulus `2^31 - 2^27 + 1`.
pub const P: u64 = 2_013_265_921;

/// `2^{-1} mod P`.
pub const HALF: u64 = (P + 1) / 2;

/// The 2-adicity of `P - 1 = 15 * 2^27`.
pub const TWO_ADIC_BITS: u32 = 27;

/// Generator of the order-`2^27` subgroup.
pub const TWO_ADIC_GENERATOR: u64 = 440_564_289;

#[inline]
pub fn badd(a: u64, b: u64) -> u64 {
    debug_assert!(a < P && b < P);
    let sum = a + b;
    if sum >= P {
        sum - P
    } else {
        sum
    }
}

#[inline]
pub fn bsub(a: u64, b: u64) -> u64 {
    debug_assert!(a < P && b < P);
    if a >= b {
        a - b
    } else {
        a + P - b
    }
}

#[inline]
pub fn bmul(a: u64, b: u64) -> u64 {
    debug_assert!(a < P && b < P);
    ((a as u128 * b as u128) % P as u128) as u64
}

pub fn bpow(mut base: u64, mut exponent: u64) -> u64 {
    debug_assert!(base < P);
    let mut accumulator = 1;
    while exponent > 0 {
        if exponent & 1 == 1 {
            accumulator = bmul(accumulator, base);
        }
        base = bmul(base, base);
        exponent >>= 1;
    }
    accumulator
}

pub fn binv(value: u64) -> u64 {
    assert!(value != 0 && value < P, "non-invertible BabyBear value");
    bpow(value, P - 2)
}

pub fn two_adic_generator(bits: u32) -> u64 {
    assert!(bits <= TWO_ADIC_BITS, "two-adic domain exceeds BabyBear");
    let mut generator = TWO_ADIC_GENERATOR;
    for _ in bits..TWO_ADIC_BITS {
        generator = bmul(generator, generator);
    }
    generator
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scalar_constants_and_inverse_are_consistent() {
        assert_eq!(bpow(31, 15), TWO_ADIC_GENERATOR);
        assert_eq!(bmul(HALF, 2), 1);
        assert_eq!(bmul(17, binv(17)), 1);
        assert_eq!(two_adic_generator(0), 1);
    }
}
