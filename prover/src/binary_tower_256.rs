//! Fixed-width `GF(2^256)` coordinates for wide Fiat--Shamir challenges.
//!
//! The representation is level eight of the same explicit Fan--Paar tower as
//! [`crate::binary_tower`]:
//!
//! ```text
//! T_0 = GF(2)
//! T_{k+1} = T_k[y_k] / (y_k^2 + g_k y_k + 1),
//! g_0 = 1, g_{k+1} = y_k.
//! ```
//!
//! Four little-endian `u64` limbs hold the recursive basis coordinates.  The
//! low 128 bits are the constant coordinate in `T_7`; the high 128 bits are
//! the coefficient of `y_7`.  Recursing gives the existing `T_6 = GF(2^64)`
//! representation in the low limb.  Addition is XOR, and multiplication is
//! the exact three-product Fan--Paar/Karatsuba step at every level.
//!
//! `Theory.BinaryTowerFanPaar` proves `fpGen_quadratic`,
//! `towerPack_towerMulStep`, and `towerMul_eq_mul` at all levels;
//! `Theory.BinaryTowerTrace.fanPaarRecursion_holds` closes the required
//! generation fact. `[BTOWER256-RUST-UNVERIFIED]` is the honest seam: Rust's
//! four-limb operations are unverified compute, not a refinement of Lean
//! definitions, whose field elements and generators are choice-selected.

use core::fmt;

use crate::binary_tower::TowerElem;

/// The recursive tower level represented by [`Tower256`].
pub const TOWER_256_LEVEL: u8 = 8;

/// The existing runtime tower level embedded in the low limb.
pub const EMBEDDED_GF2_64_LEVEL: u8 = 6;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tower256Error {
    WrongEmbeddedLevel(u8),
    GeneratorLevelTooLarge(u8),
    EncodedLength(usize),
    DivisionByZero,
}

impl fmt::Display for Tower256Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongEmbeddedLevel(level) => write!(
                f,
                "expected a GF(2^64) tower element at level {EMBEDDED_GF2_64_LEVEL}, got level {level}"
            ),
            Self::GeneratorLevelTooLarge(level) => write!(
                f,
                "Fan--Paar generator y_{level} does not fit in GF(2^256)"
            ),
            Self::EncodedLength(length) => {
                write!(f, "GF(2^256) encoding has length {length}, expected 32")
            }
            Self::DivisionByZero => write!(f, "division by zero in GF(2^256)"),
        }
    }
}

impl std::error::Error for Tower256Error {}

/// An element of level-eight `T_8 = GF(2^256)` in recursive Fan--Paar basis.
///
/// Every 256-bit string is a canonical element, so the exact 32-byte decoder
/// is infallible.  The slice decoder rejects every non-32-byte encoding.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Tower256 {
    limbs: [u64; 4],
}

impl Tower256 {
    pub const ZERO: Self = Self { limbs: [0; 4] };
    pub const ONE: Self = Self {
        limbs: [1, 0, 0, 0],
    };

    pub const fn from_limbs(limbs: [u64; 4]) -> Self {
        Self { limbs }
    }

    pub const fn limbs(&self) -> &[u64; 4] {
        &self.limbs
    }

    pub const fn is_zero(self) -> bool {
        self.limbs[0] == 0 && self.limbs[1] == 0 && self.limbs[2] == 0 && self.limbs[3] == 0
    }

    /// Embed the existing level-six [`TowerElem`] as the constant coordinates
    /// of levels seven and eight.
    pub fn embed_gf2_64(value: TowerElem) -> Result<Self, Tower256Error> {
        if value.level() != EMBEDDED_GF2_64_LEVEL {
            return Err(Tower256Error::WrongEmbeddedLevel(value.level()));
        }
        Ok(Self::from_limbs([value.bits(), 0, 0, 0]))
    }

    /// `y_k = fpGen k`, embedded into `T_8`.  Generator `y_7` is the top
    /// generator; its coordinate is bit 128.
    pub fn fp_generator(k: u8) -> Result<Self, Tower256Error> {
        if k >= TOWER_256_LEVEL {
            return Err(Tower256Error::GeneratorLevelTooLarge(k));
        }
        let bit = 1usize << k;
        let mut limbs = [0u64; 4];
        limbs[bit / 64] = 1u64 << (bit % 64);
        Ok(Self::from_limbs(limbs))
    }

    /// Characteristic-two addition (and subtraction).
    #[inline]
    pub const fn add(self, rhs: Self) -> Self {
        Self::from_limbs([
            self.limbs[0] ^ rhs.limbs[0],
            self.limbs[1] ^ rhs.limbs[1],
            self.limbs[2] ^ rhs.limbs[2],
            self.limbs[3] ^ rhs.limbs[3],
        ])
    }

    /// Recursive three-product Fan--Paar multiplication through level eight.
    #[inline]
    pub fn mul(self, rhs: Self) -> Self {
        Self::from_limbs(mul_level8(self.limbs, rhs.limbs))
    }

    #[inline]
    pub fn square(self) -> Self {
        self.mul(self)
    }

    /// Multiply by the top-level generator `y_7` using only the recursive
    /// linear reduction map.
    pub fn mul_by_generator(self) -> Self {
        let low = [self.limbs[0], self.limbs[1]];
        let high = [self.limbs[2], self.limbs[3]];
        let reduced_high = xor2(low, mul_by_generator_level7(high));
        Self::from_limbs([high[0], high[1], reduced_high[0], reduced_high[1]])
    }

    /// Multiplicative inverse by the fixed field exponent `2^256 - 2`.
    ///
    /// After iteration `i`, `acc = self^(2^(i+1)-1)`; the final square gives
    /// `self^(2^256-2)`.  The field property is supplied abstractly by Loom's
    /// all-level binary-tower development and tested here against this runtime
    /// representation pending generated Lean authority; this Rust is unverified compute.
    pub fn inverse(self) -> Result<Self, Tower256Error> {
        if self.is_zero() {
            return Err(Tower256Error::DivisionByZero);
        }
        let mut acc = self;
        for _ in 1..255 {
            acc = acc.square().mul(self);
        }
        Ok(acc.square())
    }

    pub fn div(self, rhs: Self) -> Result<Self, Tower256Error> {
        Ok(self.mul(rhs.inverse()?))
    }

    /// Canonical little-endian coordinate encoding, exactly 32 bytes.
    pub fn to_le_bytes(self) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        for (chunk, limb) in bytes.chunks_exact_mut(8).zip(self.limbs) {
            chunk.copy_from_slice(&limb.to_le_bytes());
        }
        bytes
    }

    /// Decode an exact canonical little-endian coordinate encoding.
    pub fn from_le_bytes(bytes: [u8; 32]) -> Self {
        let mut limbs = [0u64; 4];
        for (limb, chunk) in limbs.iter_mut().zip(bytes.chunks_exact(8)) {
            *limb = u64::from_le_bytes(chunk.try_into().expect("chunk length is eight"));
        }
        Self::from_limbs(limbs)
    }

    /// Decode a byte slice while rejecting non-canonical encoded lengths.
    pub fn try_from_le_slice(bytes: &[u8]) -> Result<Self, Tower256Error> {
        let exact: [u8; 32] = bytes
            .try_into()
            .map_err(|_| Tower256Error::EncodedLength(bytes.len()))?;
        Ok(Self::from_le_bytes(exact))
    }
}

#[inline]
const fn xor2(left: [u64; 2], right: [u64; 2]) -> [u64; 2] {
    [left[0] ^ right[0], left[1] ^ right[1]]
}

/// Multiply in `T_8`, viewing each operand as two `T_7` coordinates.
fn mul_level8(left: [u64; 4], right: [u64; 4]) -> [u64; 4] {
    let a0 = [left[0], left[1]];
    let a1 = [left[2], left[3]];
    let b0 = [right[0], right[1]];
    let b1 = [right[2], right[3]];

    let p0 = mul_level7(a0, b0);
    let p1 = mul_level7(a1, b1);
    let mixed = xor2(xor2(mul_level7(xor2(a0, a1), xor2(b0, b1)), p0), p1);
    let low = xor2(p0, p1);
    let high = xor2(mixed, mul_by_generator_level7(p1));
    [low[0], low[1], high[0], high[1]]
}

/// Multiply in `T_7`, viewing each operand as two `T_6` coordinates.
fn mul_level7(left: [u64; 2], right: [u64; 2]) -> [u64; 2] {
    let p0 = mul_small(6, left[0], right[0]);
    let p1 = mul_small(6, left[1], right[1]);
    let mixed = mul_small(6, left[0] ^ left[1], right[0] ^ right[1]) ^ p0 ^ p1;
    let low = p0 ^ p1;
    let high = mixed ^ mul_by_generator_small(6, p1);
    [low, high]
}

/// Multiply a `T_7` element by `y_6`.
fn mul_by_generator_level7(value: [u64; 2]) -> [u64; 2] {
    [value[1], value[0] ^ mul_by_generator_small(6, value[1])]
}

/// Existing single-word recursion, repeated locally so [`TowerElem`]
/// semantics and visibility remain untouched.
fn mul_small(level: u8, left: u64, right: u64) -> u64 {
    if level == 0 {
        return left & right & 1;
    }
    let child = level - 1;
    let width = 1usize << child;
    let mask = if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let a0 = left & mask;
    let a1 = (left >> width) & mask;
    let b0 = right & mask;
    let b1 = (right >> width) & mask;

    let p0 = mul_small(child, a0, b0);
    let p1 = mul_small(child, a1, b1);
    let mixed = mul_small(child, a0 ^ a1, b0 ^ b1) ^ p0 ^ p1;
    let p1_times_coeff = if child == 0 {
        p1
    } else {
        mul_by_generator_small(child, p1)
    };
    p0 ^ p1 | ((mixed ^ p1_times_coeff) << width)
}

/// Multiply a `T_level` single-word element by `y_(level-1)`.
fn mul_by_generator_small(level: u8, value: u64) -> u64 {
    debug_assert!(level > 0 && level <= EMBEDDED_GF2_64_LEVEL);
    let child = level - 1;
    let width = 1usize << child;
    let mask = if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let low = value & mask;
    let high = (value >> width) & mask;
    let reduced_high = if child == 0 {
        low ^ high
    } else {
        low ^ mul_by_generator_small(child, high)
    };
    high | (reduced_high << width)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary_tower::TowerElem;

    #[test]
    fn gf2_256_tower_arithmetic_smoke() {
        let one = Tower256::ONE;
        let y5 = Tower256::fp_generator(5).unwrap();
        let y6 = Tower256::fp_generator(6).unwrap();
        let y7 = Tower256::fp_generator(7).unwrap();

        // The generators adjoining T_7 and T_8 obey the same all-level Lean
        // relation y_k^2 = y_(k-1)*y_k + 1.
        assert_eq!(y6.square(), y5.mul(y6).add(one));
        assert_eq!(y7.square(), y6.mul(y7).add(one));
        assert_eq!(y7.mul_by_generator(), y7.mul(y7));

        let a = Tower256::from_limbs([
            0x0123_4567_89ab_cdef,
            0xfedc_ba98_7654_3210,
            0x0f0f_f0f0_55aa_aa55,
            0x8000_0000_0000_0001,
        ]);
        let b = Tower256::from_limbs([
            0xdead_beef_cafe_babe,
            0x1122_3344_5566_7788,
            0xaaaa_5555_ffff_0000,
            0x0102_0304_0506_0708,
        ]);
        let c = Tower256::from_limbs([
            0x1357_9bdf_2468_ace0,
            0xffff_0000_ffff_0000,
            0x3141_5926_5358_9793,
            0x2718_2818_2845_9045,
        ]);
        assert_eq!(a.mul(b.add(c)), a.mul(b).add(a.mul(c)));
        assert_eq!(a.mul(a.inverse().unwrap()), one);
        assert_eq!(Tower256::from_le_bytes(a.to_le_bytes()), a);
        assert!(matches!(
            Tower256::try_from_le_slice(&a.to_le_bytes()[..31]),
            Err(Tower256Error::EncodedLength(31))
        ));

        let small_a = TowerElem::new(6, 0x0123_4567_89ab_cdef).unwrap();
        let small_b = TowerElem::new(6, 0xfedc_ba98_7654_3210).unwrap();
        assert_eq!(
            Tower256::embed_gf2_64(small_a.mul(small_b).unwrap()).unwrap(),
            Tower256::embed_gf2_64(small_a)
                .unwrap()
                .mul(Tower256::embed_gf2_64(small_b).unwrap())
        );

    }
}
