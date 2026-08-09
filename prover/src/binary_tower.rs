//! A narrow executable coordinate model of Loom's Fan--Paar binary tower.
//!
//! This is **unverified compute**, and deliberately not a prover backend.  It
//! chooses the explicit basis
//!
//! ```text
//! T_0 = GF(2)
//! T_{k+1} = T_k[y_k] / (y_k^2 + g_k y_k + 1),
//! g_0 = 1, g_{k+1} = y_k,
//! ```
//!
//! and stores `a + b*y_k` as the low and high halves of one `u64`.  This is
//! the coordinate presentation certified abstractly by the Lean theorems
//! `fpGen_quadratic`, `towerPack_towerMulStep`, `fpGen_not_mem_range_all`, and
//! `towerMul_eq_mul`.  Addition is XOR.  Multiplication is the exact
//! three-submultiply Fan--Paar/Karatsuba step, with multiplication by the
//! reduction generator implemented as a linear recursion.
//!
//! The distinction matters: Lean's `binaryTowerEmbed` and `fpGen` are selected
//! noncomputably by `Classical.choice`, so there is no canonical bit pattern to
//! compare against.  The tests pin this explicit presentation to the same
//! equations (GF(4), GF(16), all generator relations, trace separation), not
//! to the identity of choice-selected Lean values.
//!
//! One additive fold pair is included because its formula is already proved in
//! `Theory.AdditiveNTT`: `friFold`, `friFold_coset_invariant`, and
//! `friFold_eval_poly`.  It is a field operation only; there are no commitments,
//! transcript, query schedule, or low-degree-test protocol here.
//!
//! Status and honest residuals:
//! * `[BTOWER-RUST-UNVERIFIED]`: this Rust representation has no formal
//!   semantics or refinement theorem; it is unverified compute behind a
//!   future Lean-emitted interface
//!   to the choice-selected Lean field (Rust has no formal semantics today).
//! * `[ANTT-butterfly-runtime]`: implemented by the sibling
//!   `additive_ntt.rs` fast forward/inverse schedule, with a dense oracle.
//! * `[ANTT-protocol-runtime]`: additive commitments, transcript, queries, and
//!   multi-round FRI integration.  Until those land, this module is arithmetic,
//!   never an "additive backend".

use core::fmt;

/// `T_6 = GF(2^64)` fills the entire storage word.  Larger levels require a
/// wider representation and are rejected rather than silently truncated.
pub const MAX_LEVEL: u8 = 6;

/// Temporary native payload used by legacy prototype modules while their
/// framing is moved into Lean-emitted control.  This function has no authority
/// to select a transcript or commitment format.
pub const fn tower_leaf_payload(value: TowerElem) -> [u8; 13] {
    let mut payload = [0u8; 13];
    payload[0] = b'B';
    payload[1] = b'T';
    payload[2] = b'L';
    payload[3] = b'1';
    payload[4] = value.level();
    let bits = value.bits().to_le_bytes();
    let mut i = 0;
    while i < 8 {
        payload[5 + i] = bits[i];
        i += 1;
    }
    payload
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TowerError {
    LevelTooLarge(u8),
    NonCanonical { level: u8, bits: u64 },
    LevelMismatch { left: u8, right: u8 },
    NoPreviousLevel,
    DivisionByZero,
}

impl fmt::Display for TowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LevelTooLarge(level) => {
                write!(f, "binary-tower level {level} exceeds {MAX_LEVEL}")
            }
            Self::NonCanonical { level, bits } => {
                write!(
                    f,
                    "0x{bits:x} is not canonical at binary-tower level {level}"
                )
            }
            Self::LevelMismatch { left, right } => {
                write!(f, "binary-tower level mismatch: {left} versus {right}")
            }
            Self::NoPreviousLevel => write!(f, "GF(2) has no lower tower level"),
            Self::DivisionByZero => write!(f, "division by zero in the binary tower"),
        }
    }
}

impl std::error::Error for TowerError {}

/// An element of `T_level = GF(2^(2^level))` in recursive Fan--Paar basis.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TowerElem {
    level: u8,
    bits: u64,
}

impl TowerElem {
    pub fn new(level: u8, bits: u64) -> Result<Self, TowerError> {
        check_level(level)?;
        if bits & !level_mask(level) != 0 {
            return Err(TowerError::NonCanonical { level, bits });
        }
        Ok(Self { level, bits })
    }

    #[inline]
    fn from_bits(level: u8, bits: u64) -> Self {
        debug_assert!(level <= MAX_LEVEL);
        debug_assert_eq!(bits & !level_mask(level), 0);
        Self { level, bits }
    }

    pub const fn level(self) -> u8 {
        self.level
    }

    pub const fn bits(self) -> u64 {
        self.bits
    }

    pub fn zero(level: u8) -> Result<Self, TowerError> {
        check_level(level)?;
        Ok(Self::from_bits(level, 0))
    }

    pub fn one(level: u8) -> Result<Self, TowerError> {
        check_level(level)?;
        Ok(Self::from_bits(level, 1))
    }

    pub const fn is_zero(self) -> bool {
        self.bits == 0
    }

    /// The explicit generator `y_k = fpGen k` as an element of `T_{k+1}`.
    pub fn fp_generator(k: u8) -> Result<Self, TowerError> {
        let level = k.checked_add(1).ok_or(TowerError::LevelTooLarge(k))?;
        check_level(level)?;
        let high_bit = 1usize << k;
        Ok(Self::from_bits(level, 1u64 << high_bit))
    }

    /// The Lean coefficient `towerMulCoeff k : T_k`: `1` at the bottom and
    /// `fpGen (k-1)` thereafter.
    pub fn mul_coefficient(k: u8) -> Result<Self, TowerError> {
        if k == 0 {
            Self::one(0)
        } else {
            Self::fp_generator(k - 1)
        }
    }

    /// The canonical one-level embedding `T_k -> T_{k+1}` for this explicit
    /// presentation: place the element in the low coordinate.
    pub fn embed(self) -> Result<Self, TowerError> {
        let target = self
            .level
            .checked_add(1)
            .ok_or(TowerError::LevelTooLarge(self.level))?;
        check_level(target)?;
        Ok(Self::from_bits(target, self.bits))
    }

    pub fn embed_to(self, target: u8) -> Result<Self, TowerError> {
        check_level(target)?;
        if target < self.level {
            return Err(TowerError::LevelMismatch {
                left: self.level,
                right: target,
            });
        }
        Ok(Self::from_bits(target, self.bits))
    }

    /// Pack `(a,b) in T_k^2` as `a + b*y_k in T_{k+1}`.
    pub fn pack(low: Self, high: Self) -> Result<Self, TowerError> {
        same_level(low, high)?;
        let target = low
            .level
            .checked_add(1)
            .ok_or(TowerError::LevelTooLarge(low.level))?;
        check_level(target)?;
        let width = level_width(low.level);
        Ok(Self::from_bits(target, low.bits | (high.bits << width)))
    }

    /// Inverse of [`pack`](Self::pack) in this explicit coordinate model.
    pub fn unpack(self) -> Result<(Self, Self), TowerError> {
        if self.level == 0 {
            return Err(TowerError::NoPreviousLevel);
        }
        let child = self.level - 1;
        let width = level_width(child);
        let mask = level_mask(child);
        Ok((
            Self::from_bits(child, self.bits & mask),
            Self::from_bits(child, (self.bits >> width) & mask),
        ))
    }

    /// Characteristic-two addition/subtraction.
    pub fn add(self, rhs: Self) -> Result<Self, TowerError> {
        same_level(self, rhs)?;
        Ok(Self::from_bits(self.level, self.bits ^ rhs.bits))
    }

    /// Fan--Paar multiplication, equal to the recursive `towerMulStep` formula.
    pub fn mul(self, rhs: Self) -> Result<Self, TowerError> {
        same_level(self, rhs)?;
        Ok(Self::from_bits(
            self.level,
            mul_bits(self.level, self.bits, rhs.bits),
        ))
    }

    pub fn square(self) -> Self {
        Self::from_bits(self.level, mul_bits(self.level, self.bits, self.bits))
    }

    pub fn pow_u64(self, mut exponent: u64) -> Self {
        let mut base = self;
        let mut acc = Self::from_bits(self.level, 1);
        while exponent != 0 {
            if exponent & 1 == 1 {
                acc = Self::from_bits(self.level, mul_bits(self.level, acc.bits, base.bits));
            }
            exponent >>= 1;
            if exponent != 0 {
                base = base.square();
            }
        }
        acc
    }

    /// Multiplicative inverse via `a^(|T_k|-2)`.  Lean proves each tower level
    /// is a field; the runtime field-law tests exercise the concrete model.
    pub fn inverse(self) -> Result<Self, TowerError> {
        if self.is_zero() {
            return Err(TowerError::DivisionByZero);
        }
        let width = level_width(self.level);
        let exponent = if width == 64 {
            u64::MAX - 1
        } else {
            (1u64 << width) - 2
        };
        Ok(self.pow_u64(exponent))
    }

    pub fn div(self, rhs: Self) -> Result<Self, TowerError> {
        same_level(self, rhs)?;
        self.mul(rhs.inverse()?)
    }

    /// Absolute Frobenius-orbit trace, mirroring Lean's `bTrace`.
    pub fn absolute_trace(self) -> Self {
        let mut term = self;
        let mut acc = Self::from_bits(self.level, 0);
        for _ in 0..level_width(self.level) {
            acc.bits ^= term.bits;
            term = term.square();
        }
        acc
    }

    /// Multiplication by the level's Fan--Paar generator.  This is linear and
    /// recursive, so the general multiply uses three recursive multiplications,
    /// not four.
    pub fn mul_by_generator(self) -> Result<Self, TowerError> {
        if self.level == 0 {
            return Err(TowerError::NoPreviousLevel);
        }
        Ok(Self::from_bits(
            self.level,
            mul_by_generator_bits(self.level, self.bits),
        ))
    }
}

/// `q_beta(x) = x^2 + beta*x`, the two-to-one additive-domain map.
pub fn additive_fold_map(beta: TowerElem, x: TowerElem) -> Result<TowerElem, TowerError> {
    same_level(beta, x)?;
    x.square().add(beta.mul(x)?)
}

/// One representative-independent additive FRI pair fold:
///
/// `f(x) + (x+lambda) * (f(x)+f(x+beta)) / beta`.
pub fn additive_fold_pair(
    beta: TowerElem,
    lambda: TowerElem,
    x: TowerElem,
    fx: TowerElem,
    fx_plus_beta: TowerElem,
) -> Result<TowerElem, TowerError> {
    same_level(beta, lambda)?;
    same_level(beta, x)?;
    same_level(beta, fx)?;
    same_level(beta, fx_plus_beta)?;
    let odd = fx.add(fx_plus_beta)?.div(beta)?;
    fx.add(x.add(lambda)?.mul(odd)?)
}

#[inline]
fn check_level(level: u8) -> Result<(), TowerError> {
    if level > MAX_LEVEL {
        Err(TowerError::LevelTooLarge(level))
    } else {
        Ok(())
    }
}

#[inline]
const fn level_width(level: u8) -> usize {
    1usize << level
}

#[inline]
const fn level_mask(level: u8) -> u64 {
    let width = level_width(level);
    if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

#[inline]
fn same_level(left: TowerElem, right: TowerElem) -> Result<(), TowerError> {
    if left.level == right.level {
        Ok(())
    } else {
        Err(TowerError::LevelMismatch {
            left: left.level,
            right: right.level,
        })
    }
}

/// Multiply an element of `T_level` by its generator `y_{level-1}`.
fn mul_by_generator_bits(level: u8, value: u64) -> u64 {
    debug_assert!(level > 0);
    let child = level - 1;
    let width = level_width(child);
    let mask = level_mask(child);
    let low = value & mask;
    let high = (value >> width) & mask;
    let reduced_high = if child == 0 {
        low ^ high
    } else {
        low ^ mul_by_generator_bits(child, high)
    };
    high | (reduced_high << width)
}

/// The recursive three-product Fan--Paar/Karatsuba formula.
fn mul_bits(level: u8, left: u64, right: u64) -> u64 {
    if level == 0 {
        return left & right & 1;
    }
    let child = level - 1;
    let width = level_width(child);
    let mask = level_mask(child);
    let a0 = left & mask;
    let a1 = (left >> width) & mask;
    let b0 = right & mask;
    let b1 = (right >> width) & mask;

    let p0 = mul_bits(child, a0, b0);
    let p1 = mul_bits(child, a1, b1);
    let mixed = mul_bits(child, a0 ^ a1, b0 ^ b1) ^ p0 ^ p1;
    let p1_times_coeff = if child == 0 {
        p1
    } else {
        mul_by_generator_bits(child, p1)
    };
    let low = p0 ^ p1;
    let high = mixed ^ p1_times_coeff;
    low | (high << width)
}
