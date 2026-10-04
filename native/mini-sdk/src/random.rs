//! The ONE source of operating-system randomness: `/dev/urandom`, read exactly.
//!
//! A short read or a failure to open is an error; no caller ever proceeds with a zero or partly
//! filled buffer.
use std::fs::File;
use std::io::{self, Read};

/// Fill `out` completely from `/dev/urandom`.
pub fn fill(out: &mut [u8]) -> io::Result<()> {
    fill_from(&mut File::open("/dev/urandom")?, out)
}

fn fill_from(source: &mut impl Read, out: &mut [u8]) -> io::Result<()> {
    source.read_exact(out)
}

/// `N` fresh random bytes.
pub fn bytes<const N: usize>() -> io::Result<[u8; N]> {
    let mut out = [0u8; N];
    fill(&mut out)?;
    Ok(out)
}

/// A fresh 128-bit nonce as a canonical decimal (the big-endian value of 16 random bytes).
pub fn decimal_nonce() -> io::Result<String> {
    Ok(u128::from_be_bytes(bytes::<16>()?).to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn draws_are_filled_and_independent() {
        let a = bytes::<32>().unwrap();
        let b = bytes::<32>().unwrap();
        assert_ne!(a, [0u8; 32], "a draw is never the unfilled buffer");
        assert_ne!(a, b, "two draws differ");
        let mut wide = [0u8; 4096];
        fill(&mut wide).unwrap();
        assert!(wide.iter().any(|b| *b != 0) && wide[..2048] != wide[2048..], "the whole buffer is filled");
    }

    #[test]
    fn nonces_are_canonical_decimals_that_differ() {
        let a = decimal_nonce().unwrap();
        let b = decimal_nonce().unwrap();
        assert_ne!(a, b);
        for n in [&a, &b] {
            assert_eq!(n.parse::<u128>().unwrap().to_string(), **n, "canonical");
        }
    }

    #[test]
    fn a_short_source_is_an_error_never_a_partial_fill() {
        let mut short: &[u8] = &[1, 2, 3];
        let mut out = [0u8; 8];
        assert!(fill_from(&mut short, &mut out).is_err());
        let mut exact: &[u8] = &[7; 8];
        fill_from(&mut exact, &mut out).unwrap();
        assert_eq!(out, [7; 8]);
    }
}
