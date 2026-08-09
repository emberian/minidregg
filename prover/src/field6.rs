//! Native six-lane BabyBear quotient-ring arithmetic for candidate challenges.
//!
//! The carrier is `BabyBear[u] / (u⁶ - 31)`, in little-endian coefficient
//! order. This Rust module selects the reduction constant and lane codec.
//! `Compiler/Ext6Conformance.lean` proves irreducibility and multiplication
//! facts in Lean's own model; those theorems do not prove this Rust code or pin
//! its representation. Native gate and MLE kernels use this type directly, but
//! no compiled generated adapter currently maps it to a Lean carrier or shared
//! protocol profile.

use crate::babybear::{badd, bmul, bsub, P};

/// The Rust-selected reduction relation is `u⁶ = 31`.
pub const EXT6_W: u64 = 31;

/// Rejection reason for a non-canonical coefficient lane.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ext6Error {
    pub lane: usize,
    pub value: u64,
}

/// One canonical element of `BabyBear[u] / (u⁶ - 31)`.
///
/// Coefficients are private so malformed representatives cannot enter through a
/// struct literal.  Native buffer decoding must use [`Ext6::try_from_limbs`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ext6 {
    limbs: [u64; 6],
}

impl Ext6 {
    pub const ZERO: Ext6 = Ext6 { limbs: [0; 6] };
    pub const ONE: Ext6 = Ext6 {
        limbs: [1, 0, 0, 0, 0, 0],
    };

    /// Parse six canonical BabyBear coefficients.
    pub fn try_from_limbs(limbs: [u64; 6]) -> Result<Ext6, Ext6Error> {
        if let Some((lane, &value)) = limbs.iter().enumerate().find(|(_, value)| **value >= P) {
            Err(Ext6Error { lane, value })
        } else {
            Ok(Ext6 { limbs })
        }
    }

    /// Embed one canonical base-field element into lane zero.
    pub fn try_from_base(value: u64) -> Result<Ext6, Ext6Error> {
        if value >= P {
            Err(Ext6Error { lane: 0, value })
        } else {
            Ok(Ext6 {
                limbs: [value, 0, 0, 0, 0, 0],
            })
        }
    }

    /// The canonical little-endian coefficient encoding.
    pub fn limbs(&self) -> &[u64; 6] {
        &self.limbs
    }

    pub fn is_zero(self) -> bool {
        self == Ext6::ZERO
    }

    #[inline]
    pub fn add(self, rhs: Ext6) -> Ext6 {
        let mut out = [0; 6];
        for (dst, (&a, &b)) in out.iter_mut().zip(self.limbs.iter().zip(rhs.limbs.iter())) {
            *dst = badd(a, b);
        }
        Ext6 { limbs: out }
    }

    #[inline]
    pub fn sub(self, rhs: Ext6) -> Ext6 {
        let mut out = [0; 6];
        for (dst, (&a, &b)) in out.iter_mut().zip(self.limbs.iter().zip(rhs.limbs.iter())) {
            *dst = bsub(a, b);
        }
        Ext6 { limbs: out }
    }

    /// Schoolbook convolution followed by the single-wrap reduction `u⁶ = 31`.
    /// Products have degree at most ten, so no second reduction pass is needed.
    pub fn mul(self, rhs: Ext6) -> Ext6 {
        let mut convolution = [0u64; 11];
        for i in 0..6 {
            for j in 0..6 {
                convolution[i + j] = badd(convolution[i + j], bmul(self.limbs[i], rhs.limbs[j]));
            }
        }
        let mut out = [0u64; 6];
        out.copy_from_slice(&convolution[..6]);
        for degree in 6..=10 {
            out[degree - 6] = badd(out[degree - 6], bmul(EXT6_W, convolution[degree]));
        }
        Ext6 { limbs: out }
    }

    #[inline]
    pub fn square(self) -> Ext6 {
        self.mul(self)
    }

    /// Scale by one canonical base-field element.
    #[inline]
    pub fn base_mul(self, scalar: u64) -> Ext6 {
        debug_assert!(scalar < P);
        let mut out = [0; 6];
        for (dst, &coefficient) in out.iter_mut().zip(self.limbs.iter()) {
            *dst = bmul(coefficient, scalar);
        }
        Ext6 { limbs: out }
    }

    /// Binary exponentiation.  The exponent fits `u64` for every Frobenius
    /// certificate used by the conformance tests (`q = P`).
    pub fn pow(self, mut exponent: u64) -> Ext6 {
        let mut base = self;
        let mut out = Ext6::ONE;
        while exponent > 0 {
            if exponent & 1 == 1 {
                out = out.mul(base);
            }
            base = base.square();
            exponent >>= 1;
        }
        out
    }
}
