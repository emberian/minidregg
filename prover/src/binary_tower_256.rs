//! Fixed-width coordinates intended to represent `GF(2^256)` values.
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
//! representation in the low limb. Addition is XOR.
//!
//! Every level from `T_4` to `T_8` uses the same formulas: the selected three-product Fan--Paar/Karatsuba product, the
//! Frobenius split `(a + b y)^2 = (a^2 + b^2) + g b^2 y` for squaring, and the
//! tower norm `N(a + b y) = a^2 + g a b + b^2` for inversion,
//! `(a + b y)^-1 = ((a + g b) + b y) N^-1`, with one inversion one level down.
//! The recursion stops at `T_3 = GF(2^8)`, where four tables built at compile
//! time from a generator's power table answer products, `y_2`-multiples,
//! squares and inverses: a product is 3^5 = 243 lookups in a 64 KiB table
//! instead of 3^8 = 6,561 single-bit products. The coordinates are untouched:
//! no basis change happens anywhere, and the bit-level recursion this replaced
//! survives only as the test reference `mul_reference_bit_recursive`, which
//! the tests compare against on every operation.
//!
//! `Theory.BinaryTowerFanPaar` and `Theory.BinaryTowerTrace` prove analogous
//! identities for Lean's abstract tower. They do not prove this four-limb code
//! as a refinement. `[BTOWER256-RUST-UNVERIFIED]` remains the honest seam: the
//! Lean-generated native catalog now pins and invokes one byte-only dot-product
//! adapter, but Lean's canonical decoder and selected checker retain all
//! acceptance authority over its returned bytes.

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

/// A Rust-selected level-eight `T_8` coordinate in recursive Fan--Paar basis,
/// intended to represent an element of `GF(2^256)`.
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

    /// The three-product Fan--Paar multiplication at every level through
    /// level eight, with the `T_3` products read from the compile-time table.
    #[inline]
    pub fn mul(self, rhs: Self) -> Self {
        Self::from_limbs(mul256(self.limbs, rhs.limbs))
    }

    /// `x^2` by the Frobenius split at every level: two squarings and one
    /// generator multiple one level down, never a general product.
    #[inline]
    pub fn square(self) -> Self {
        Self::from_limbs(square256(self.limbs))
    }

    /// Multiply by the top-level generator `y_7` using only the recursive
    /// linear reduction map.
    #[inline]
    pub fn mul_by_generator(self) -> Self {
        let (low, high) = split256(self.limbs);
        Self::from_limbs(join256(high, low ^ gen128(high)))
    }

    /// Multiplicative inverse by the tower norm: for `x = a + b y_7`,
    /// `N(x) = a^2 + y_6 a b + b^2` lies in `T_7` and `x^-1 = ((a + y_6 b) + b y_7) N(x)^-1`,
    /// recursively down to the `T_3` inverse table. The result is the unique
    /// inverse, so it equals the fixed exponent `x^(2^256-2)` the previous
    /// implementation computed; the tests compare the two. Lean proves a field
    /// property for its abstract tower; that does not establish the property
    /// for this Rust-selected coordinate implementation. Native tests provide
    /// only exercised-input evidence.
    pub fn inverse(self) -> Result<Self, Tower256Error> {
        if self.is_zero() {
            return Err(Tower256Error::DivisionByZero);
        }
        Ok(Self::from_limbs(inverse256(self.limbs)))
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

/* ---------------------------------------------------------------------------------------- */
/* T_3 = GF(2^8): the tables every higher level bottoms out in                               */
/* ---------------------------------------------------------------------------------------- */

/// The three-product recursion inside one byte, `level <= 3`. Compile time
/// only: it derives the tables below, and nothing at run time calls it.
const fn t3_mul_bits(level: u8, left: u8, right: u8) -> u8 {
    if level == 0 {
        return left & right & 1;
    }
    let child = level - 1;
    let width = 1u32 << child;
    let mask = ((1u16 << width) - 1) as u8;
    let (a0, a1) = (left & mask, (left >> width) & mask);
    let (b0, b1) = (right & mask, (right >> width) & mask);
    let p0 = t3_mul_bits(child, a0, b0);
    let p1 = t3_mul_bits(child, a1, b1);
    let mixed = t3_mul_bits(child, a0 ^ a1, b0 ^ b1) ^ p0 ^ p1;
    let p1_times_coeff = if child == 0 {
        p1
    } else {
        t3_gen_bits(child, p1)
    };
    (p0 ^ p1) | ((mixed ^ p1_times_coeff) << width)
}

/// `value * y_(level-1)` inside one byte, `1 <= level <= 3`. Compile time only.
const fn t3_gen_bits(level: u8, value: u8) -> u8 {
    let child = level - 1;
    let width = 1u32 << child;
    let mask = ((1u16 << width) - 1) as u8;
    let (low, high) = (value & mask, (value >> width) & mask);
    let reduced_high = if child == 0 {
        low ^ high
    } else {
        low ^ t3_gen_bits(child, high)
    };
    high | (reduced_high << width)
}

/// `y_2`, the generator adjoining `T_3` to `T_2`, as a `T_3` coordinate.
const T3_Y2: u8 = 1 << 4;

struct T3Tables {
    /// `mul[(a << 8) | b] = a * b`.
    mul: [u8; 1 << 16],
    /// `gen[v] = v * y_2`, the coefficient multiple the `T_4` level needs.
    gen: [u8; 256],
    square: [u8; 256],
    /// `inverse[0] = 0`; the public API refuses zero before it gets here.
    inverse: [u8; 256],
}

/// Build the `T_3` tables from the powers of the first generator of the
/// multiplicative group (order 255), found and powered with [`t3_mul_bits`].
const fn build_t3_tables() -> T3Tables {
    let mut generator = 2u8;
    loop {
        let mut power = generator;
        let mut order = 1u32;
        // bounded: if the recursion were not a field, a power could cycle without reaching 1
        while power != 1 && order <= 255 {
            power = t3_mul_bits(3, power, generator);
            order += 1;
        }
        if order == 255 {
            break;
        }
        assert!(
            generator < u8::MAX,
            "T_3 has no element of order 255: the byte recursion is not a field"
        );
        generator += 1;
    }
    let mut exp = [0u8; 255];
    let mut log = [0u8; 256];
    let mut power = 1u8;
    let mut k = 0usize;
    while k < 255 {
        exp[k] = power;
        log[power as usize] = k as u8;
        power = t3_mul_bits(3, power, generator);
        k += 1;
    }
    let mut mul = [0u8; 1 << 16];
    let mut a = 1usize;
    while a < 256 {
        let mut b = 1usize;
        while b < 256 {
            mul[(a << 8) | b] = exp[(log[a] as usize + log[b] as usize) % 255];
            b += 1;
        }
        a += 1;
    }
    let mut gen = [0u8; 256];
    let mut square = [0u8; 256];
    let mut inverse = [0u8; 256];
    let mut v = 0usize;
    while v < 256 {
        gen[v] = mul[(v << 8) | T3_Y2 as usize];
        square[v] = mul[(v << 8) | v];
        if v != 0 {
            inverse[v] = exp[(255 - log[v] as usize) % 255];
        }
        v += 1;
    }
    T3Tables {
        mul,
        gen,
        square,
        inverse,
    }
}

static T3: T3Tables = build_t3_tables();

/// A `T_3` product, its two operands carried as one table index `(a << 8) | b`.
#[inline(always)]
fn imul8(index: u16) -> u8 {
    T3.mul[usize::from(index)]
}

/// `v * y_2` in `T_3`.
#[inline(always)]
fn gen8(v: u8) -> u8 {
    T3.gen[usize::from(v)]
}

#[inline(always)]
fn square8(v: u8) -> u8 {
    T3.square[usize::from(v)]
}

#[inline(always)]
fn inverse8(v: u8) -> u8 {
    T3.inverse[usize::from(v)]
}

/* ---------------------------------------------------------------------------------------- */
/* Interleaved operands: a product's two operands travel as one word                         */
/* ---------------------------------------------------------------------------------------- */
//
// A product's operands `a` and `b` are carried as one word whose byte `2i` is `b`'s byte `i` and
// whose byte `2i + 1` is `a`'s: every 16-bit lane is then a `T_3` table index `(a_i << 8) | b_i`.
// Interleaving is bitwise, so it commutes with the recursion: the low and high halves of the word
// are the interleaved low and high coordinates, and their XOR is the interleaved Karatsuba sum
// `(a0 + a1, b0 + b1)`. Operands are interleaved once per product, at its top, and every leaf
// index below is a lane of a word already in a register.

/// Spread the bytes of `x` into the even bytes of a word twice as wide.
#[inline(always)]
fn spread16(x: u8) -> u16 {
    u16::from(x)
}

#[inline(always)]
fn spread32(x: u16) -> u32 {
    let x = u32::from(x);
    (x | (x << 8)) & 0x00ff_00ff
}

#[inline(always)]
fn spread64(x: u32) -> u64 {
    let x = u64::from(x);
    let x = (x | (x << 16)) & 0x0000_ffff_0000_ffff;
    (x | (x << 8)) & 0x00ff_00ff_00ff_00ff
}

#[inline(always)]
fn spread128(x: u64) -> u128 {
    u128::from(spread64(x as u32)) | (u128::from(spread64((x >> 32) as u32)) << 64)
}

#[inline(always)]
fn interleave16(a: u8, b: u8) -> u16 {
    (spread16(a) << 8) | spread16(b)
}

#[inline(always)]
fn interleave32(a: u16, b: u16) -> u32 {
    (spread32(a) << 8) | spread32(b)
}

#[inline(always)]
fn interleave64(a: u32, b: u32) -> u64 {
    (spread64(a) << 8) | spread64(b)
}

#[inline(always)]
fn interleave128(a: u64, b: u64) -> u128 {
    (spread128(a) << 8) | spread128(b)
}

#[inline(always)]
fn interleave256(a: u128, b: u128) -> (u128, u128) {
    (
        interleave128(a as u64, b as u64),
        interleave128((a >> 64) as u64, (b >> 64) as u64),
    )
}

#[inline(always)]
fn split32(j: u32) -> (u16, u16) {
    (j as u16, (j >> 16) as u16)
}

#[inline(always)]
fn split64(j: u64) -> (u32, u32) {
    (j as u32, (j >> 32) as u32)
}

#[inline(always)]
fn split128(j: u128) -> (u64, u64) {
    (j as u64, (j >> 64) as u64)
}

#[inline(always)]
fn split_pair(j: (u128, u128)) -> (u128, u128) {
    j
}

/* ---------------------------------------------------------------------------------------- */
/* T_4 .. T_7: one formula per level                                                         */
/* ---------------------------------------------------------------------------------------- */

/// One tower level `T_{k+1} = T_k[y_k]` on the word `$full`, whose low and high
/// halves (`$half`, `$bits` wide) are the coordinates `a + b y_k`; a product's
/// operands arrive interleaved as one `$wide` word, halved by `$split`. The
/// coefficient `g_k = y_(k-1)` is the half level's generator multiple `$hgen`.
macro_rules! tower_level {
    (
        $full:ty, $half:ty, $bits:expr, $wide:ty, $split:ident,
        mul: $imul:ident, gen: $gen:ident, square: $square:ident, inverse: $inverse:ident,
        half: $himul:ident, $hinterleave:ident, $hgen:ident, $hsquare:ident, $hinverse:ident
    ) => {
        /// `v * y_k`: `(a + b y_k) y_k = b + (a + g_k b) y_k`.
        #[inline(always)]
        fn $gen(v: $full) -> $full {
            let (a, b) = (v as $half, (v >> $bits) as $half);
            <$full>::from(b) | (<$full>::from(a ^ $hgen(b)) << $bits)
        }

        /// The three-product Fan--Paar formula: with `p0 = a0 b0`, `p1 = a1 b1`,
        /// the product is `(p0 + p1) + ((a0 + a1)(b0 + b1) + p0 + p1 + g_k p1) y_k`.
        #[inline(always)]
        fn $imul(operands: $wide) -> $full {
            let (j0, j1) = $split(operands);
            let p0 = $himul(j0);
            let p1 = $himul(j1);
            let low = p0 ^ p1;
            let high = $himul(j0 ^ j1) ^ low ^ $hgen(p1);
            <$full>::from(low) | (<$full>::from(high) << $bits)
        }

        /// `(a + b y_k)^2 = (a^2 + b^2) + g_k b^2 y_k`.
        #[inline(always)]
        fn $square(v: $full) -> $full {
            let (a, b) = ($hsquare(v as $half), $hsquare((v >> $bits) as $half));
            <$full>::from(a ^ b) | (<$full>::from($hgen(b)) << $bits)
        }

        /// `(a + b y_k)^-1 = ((a + g_k b) + b y_k) / (a^2 + g_k a b + b^2)`.
        #[inline(always)]
        fn $inverse(v: $full) -> $full {
            let (a, b) = (v as $half, (v >> $bits) as $half);
            let norm = $hsquare(a) ^ $hsquare(b) ^ $hgen($himul($hinterleave(a, b)));
            let norm_inverse = $hinverse(norm);
            <$full>::from($himul($hinterleave(a ^ $hgen(b), norm_inverse)))
                | (<$full>::from($himul($hinterleave(b, norm_inverse))) << $bits)
        }
    };
}

tower_level!(u16, u8, 8, u32, split32,
    mul: imul16, gen: gen16, square: square16, inverse: inverse16,
    half: imul8, interleave16, gen8, square8, inverse8);
tower_level!(u32, u16, 16, u64, split64,
    mul: imul32, gen: gen32, square: square32, inverse: inverse32,
    half: imul16, interleave32, gen16, square16, inverse16);
tower_level!(u64, u32, 32, u128, split128,
    mul: imul64, gen: gen64, square: square64, inverse: inverse64,
    half: imul32, interleave64, gen32, square32, inverse32);
tower_level!(u128, u64, 64, (u128, u128), split_pair,
    mul: imul128, gen: gen128, square: square128, inverse: inverse128,
    half: imul64, interleave128, gen64, square64, inverse64);

/* ---------------------------------------------------------------------------------------- */
/* T_8: the same formula over two T_7 words                                                  */
/* ---------------------------------------------------------------------------------------- */

#[inline(always)]
fn split256(limbs: [u64; 4]) -> (u128, u128) {
    (
        u128::from(limbs[0]) | (u128::from(limbs[1]) << 64),
        u128::from(limbs[2]) | (u128::from(limbs[3]) << 64),
    )
}

#[inline(always)]
fn join256(low: u128, high: u128) -> [u64; 4] {
    [
        low as u64,
        (low >> 64) as u64,
        high as u64,
        (high >> 64) as u64,
    ]
}

fn mul256(left: [u64; 4], right: [u64; 4]) -> [u64; 4] {
    let j0 = (
        interleave128(left[0], right[0]),
        interleave128(left[1], right[1]),
    );
    let j1 = (
        interleave128(left[2], right[2]),
        interleave128(left[3], right[3]),
    );
    let p0 = imul128(j0);
    let p1 = imul128(j1);
    let low = p0 ^ p1;
    let high = imul128((j0.0 ^ j1.0, j0.1 ^ j1.1)) ^ low ^ gen128(p1);
    join256(low, high)
}

fn square256(value: [u64; 4]) -> [u64; 4] {
    let (a, b) = split256(value);
    let (a, b) = (square128(a), square128(b));
    join256(a ^ b, gen128(b))
}

fn inverse256(value: [u64; 4]) -> [u64; 4] {
    let (a, b) = split256(value);
    let norm = square128(a) ^ square128(b) ^ gen128(imul128(interleave256(a, b)));
    let norm_inverse = inverse128(norm);
    join256(
        imul128(interleave256(a ^ gen128(b), norm_inverse)),
        imul128(interleave256(b, norm_inverse)),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary_tower::TowerElem;

    /// The implementation the tables replaced, verbatim: the three-product
    /// recursion carried all the way down to single bits (`T_0`). It is the
    /// reference every fast operation is compared against.
    mod reference {
        use super::super::EMBEDDED_GF2_64_LEVEL;

        #[inline]
        const fn xor2(left: [u64; 2], right: [u64; 2]) -> [u64; 2] {
            [left[0] ^ right[0], left[1] ^ right[1]]
        }

        /// Multiply in `T_8`, viewing each operand as two `T_7` coordinates.
        pub(super) fn mul_reference_bit_recursive(left: [u64; 4], right: [u64; 4]) -> [u64; 4] {
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
        pub(super) fn mul_level7(left: [u64; 2], right: [u64; 2]) -> [u64; 2] {
            let p0 = mul_small(6, left[0], right[0]);
            let p1 = mul_small(6, left[1], right[1]);
            let mixed = mul_small(6, left[0] ^ left[1], right[0] ^ right[1]) ^ p0 ^ p1;
            let low = p0 ^ p1;
            let high = mixed ^ mul_by_generator_small(6, p1);
            [low, high]
        }

        /// Multiply a `T_7` element by `y_6`.
        pub(super) fn mul_by_generator_level7(value: [u64; 2]) -> [u64; 2] {
            [value[1], value[0] ^ mul_by_generator_small(6, value[1])]
        }

        /// The single-word recursion, down to `T_0`.
        pub(super) fn mul_small(level: u8, left: u64, right: u64) -> u64 {
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
        pub(super) fn mul_by_generator_small(level: u8, value: u64) -> u64 {
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

        /// The previous inverse, verbatim: `x^(2^256-2)` by 254 square-and-multiply
        /// steps over the reference product.
        pub(super) fn inverse_reference(x: [u64; 4]) -> [u64; 4] {
            let mut acc = x;
            for _ in 1..255 {
                acc = mul_reference_bit_recursive(mul_reference_bit_recursive(acc, acc), x);
            }
            mul_reference_bit_recursive(acc, acc)
        }
    }

    use reference::{
        inverse_reference, mul_by_generator_small, mul_level7, mul_reference_bit_recursive,
        mul_small,
    };

    /// The randomized comparisons run 100,000 cases in a release build; a debug
    /// build (where the reference is roughly forty times slower) runs 2,000.
    const RANDOM_CASES: usize = if cfg!(debug_assertions) {
        2_000
    } else {
        100_000
    };

    fn splitmix(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn random_limbs(state: &mut u64) -> [u64; 4] {
        [
            splitmix(state),
            splitmix(state),
            splitmix(state),
            splitmix(state),
        ]
    }

    /// Zero, one, all ones, every half and limb boundary, single bits at every
    /// limb and sub-level edge, the eight generators, and the alternating
    /// patterns that exercise every `a0 + a1` Karatsuba operand.
    fn edge_limbs() -> Vec<[u64; 4]> {
        let mut edges = vec![
            [0; 4],
            [1, 0, 0, 0],
            [u64::MAX; 4],
            [u64::MAX, 0, 0, 0],
            [u64::MAX, u64::MAX, 0, 0],
            [0, 0, u64::MAX, u64::MAX],
            [0, u64::MAX, 0, u64::MAX],
            [0xaaaa_aaaa_aaaa_aaaa; 4],
            [0x5555_5555_5555_5555; 4],
            [0xff00_ff00_ff00_ff00; 4],
            [0x00ff_00ff_00ff_00ff, 0, 0xffff_0000_ffff_0000, 0],
            [
                0x8000_0000_0000_0001,
                0x8000_0000_0000_0001,
                0x8000_0000_0000_0001,
                0x8000_0000_0000_0001,
            ],
        ];
        for bit in [
            0usize, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 65, 127, 128, 129, 191, 192, 254, 255,
        ] {
            let mut limbs = [0u64; 4];
            limbs[bit / 64] = 1u64 << (bit % 64);
            edges.push(limbs);
        }
        for k in 0..TOWER_256_LEVEL {
            edges.push(*Tower256::fp_generator(k).unwrap().limbs());
        }
        edges
    }

    #[test]
    fn t3_tables_are_the_bit_recursion_on_every_input() {
        for a in 0..256u64 {
            for b in 0..256u64 {
                assert_eq!(
                    u64::from(imul8(interleave16(a as u8, b as u8))),
                    mul_small(3, a, b),
                    "T_3 product table at ({a}, {b})"
                );
            }
            assert_eq!(
                u64::from(gen8(a as u8)),
                mul_by_generator_small(3, a),
                "y_2 table at {a}"
            );
            assert_eq!(
                u64::from(square8(a as u8)),
                mul_small(3, a, a),
                "square table at {a}"
            );
            if a != 0 {
                assert_eq!(
                    mul_small(3, a, u64::from(inverse8(a as u8))),
                    1,
                    "inverse table at {a}"
                );
            }
        }
    }

    #[test]
    fn every_level_matches_the_bit_recursion_on_random_words() {
        let mut state = 0x0123_4567_89ab_cdef;
        for _ in 0..RANDOM_CASES {
            let (a, b) = (splitmix(&mut state), splitmix(&mut state));
            assert_eq!(
                u64::from(imul16(interleave32(a as u16, b as u16))),
                mul_small(4, a & 0xffff, b & 0xffff)
            );
            assert_eq!(
                u64::from(imul32(interleave64(a as u32, b as u32))),
                mul_small(5, a & 0xffff_ffff, b & 0xffff_ffff)
            );
            assert_eq!(
                imul64(interleave128(a, b)),
                mul_small(6, a, b),
                "T_6 product of {a:#x} and {b:#x}"
            );
            assert_eq!(gen64(a), mul_by_generator_small(6, a));
            let (c, d) = (splitmix(&mut state), splitmix(&mut state));
            let fast = imul128(interleave256(
                u128::from(a) | (u128::from(c) << 64),
                u128::from(b) | (u128::from(d) << 64),
            ));
            assert_eq!(
                [fast as u64, (fast >> 64) as u64],
                mul_level7([a, c], [b, d])
            );
        }
    }

    #[test]
    fn mul_matches_bit_recursive_reference() {
        let edges = edge_limbs();
        for &a in &edges {
            for &b in &edges {
                assert_eq!(
                    *Tower256::from_limbs(a).mul(Tower256::from_limbs(b)).limbs(),
                    mul_reference_bit_recursive(a, b),
                    "edge product {a:x?} * {b:x?}"
                );
            }
        }
        let mut state = 0xfeed_face_dead_beef;
        for _ in 0..RANDOM_CASES {
            let a = random_limbs(&mut state);
            let b = random_limbs(&mut state);
            assert_eq!(
                *Tower256::from_limbs(a).mul(Tower256::from_limbs(b)).limbs(),
                mul_reference_bit_recursive(a, b),
                "random product {a:x?} * {b:x?}"
            );
        }
    }

    #[test]
    fn square_matches_bit_recursive_reference() {
        let mut state = 0x5eed_0000_0000_0001;
        let cases = edge_limbs()
            .into_iter()
            .chain((0..RANDOM_CASES).map(|_| random_limbs(&mut state)));
        for a in cases {
            assert_eq!(
                *Tower256::from_limbs(a).square().limbs(),
                mul_reference_bit_recursive(a, a),
                "square of {a:x?}"
            );
        }
    }

    #[test]
    fn inverse_matches_the_exponent_chain() {
        // The full previous algorithm (254 square-and-multiply steps over the
        // reference product) on every nonzero edge case and a random sample.
        let mut state = 0x1e55_0000_0000_0042;
        let sampled = if cfg!(debug_assertions) { 2 } else { 24 };
        let exponent_cases = edge_limbs()
            .into_iter()
            .filter(|limbs| *limbs != [0; 4])
            .chain((0..sampled).map(|_| random_limbs(&mut state)));
        for a in exponent_cases {
            assert_eq!(
                *Tower256::from_limbs(a).inverse().unwrap().limbs(),
                inverse_reference(a),
                "inverse of {a:x?}"
            );
        }
        // Every random case: the reference product of x and its inverse is one.
        for _ in 0..RANDOM_CASES {
            let a = random_limbs(&mut state);
            let inverse = Tower256::from_limbs(a).inverse().unwrap();
            assert_eq!(
                mul_reference_bit_recursive(a, *inverse.limbs()),
                [1, 0, 0, 0],
                "x * x^-1 for x = {a:x?}"
            );
        }
        assert_eq!(Tower256::ZERO.inverse(), Err(Tower256Error::DivisionByZero));
    }

    #[test]
    fn mul_by_generator_matches_bit_recursive_reference() {
        let y7 = *Tower256::fp_generator(7).unwrap().limbs();
        let mut state = 0x9e9e_9e9e_0000_0007;
        let cases = edge_limbs()
            .into_iter()
            .chain((0..RANDOM_CASES).map(|_| random_limbs(&mut state)));
        for a in cases {
            assert_eq!(
                *Tower256::from_limbs(a).mul_by_generator().limbs(),
                mul_reference_bit_recursive(a, y7),
                "y_7 multiple of {a:x?}"
            );
        }
    }

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
