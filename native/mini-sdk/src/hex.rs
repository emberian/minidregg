//! Lowercase hex, strict on decode (the Host's canonical hex is lowercase).
use crate::{Error, Result};

pub fn encode(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        out.push(DIGITS[(b >> 4) as usize] as char);
        out.push(DIGITS[(b & 15) as usize] as char);
    }
    out
}

pub fn decode(text: &str) -> Result<Vec<u8>> {
    let digit = |c: u8| -> Result<u8> {
        match c {
            b'0'..=b'9' => Ok(c - b'0'),
            b'a'..=b'f' => Ok(c - b'a' + 10),
            _ => Err(Error("hex must be canonical lowercase".into())),
        }
    };
    let bytes = text.as_bytes();
    if bytes.len() % 2 != 0 {
        return Err("hex has odd length".into());
    }
    bytes.chunks(2).map(|p| Ok(digit(p[0])? << 4 | digit(p[1])?)).collect()
}

/// Hex of either case (what a person or another tool may type); the value is the same bytes.
/// Prefer [`decode`] wherever the spelling is part of the contract.
pub fn decode_any_case(text: &str) -> Result<Vec<u8>> {
    let digit = |c: u8| -> Result<u8> {
        match c {
            b'0'..=b'9' => Ok(c - b'0'),
            b'a'..=b'f' => Ok(c - b'a' + 10),
            b'A'..=b'F' => Ok(c - b'A' + 10),
            _ => Err(Error("invalid ASCII hex".into())),
        }
    };
    let bytes = text.as_bytes();
    if bytes.len() % 2 != 0 {
        return Err("hex has odd length".into());
    }
    bytes.chunks_exact(2).map(|p| Ok(digit(p[0])? << 4 | digit(p[1])?)).collect()
}

/// Every byte of `text` is a lowercase hex digit (the empty string passes).
pub fn is_lower(text: &str) -> bool {
    text.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// Canonical lowercase hex of a non-empty even number of digits: what [`decode`] accepts and
/// [`encode`] produces.
pub fn is_canonical(text: &str) -> bool {
    !text.is_empty() && text.len() % 2 == 0 && is_lower(text)
}

/// Canonical lowercase hex of exactly `bytes` bytes.
pub fn is_canonical_len(text: &str, bytes: usize) -> bool {
    text.len() == bytes * 2 && is_lower(text)
}

#[cfg(test)]
mod tests {
    #[test]
    fn hex_round_trip_and_strictness() {
        assert_eq!(super::encode(&[0, 171, 255]), "00abff");
        assert_eq!(super::decode("00abff").unwrap(), vec![0, 171, 255]);
        assert!(super::decode("AB").is_err());
        assert!(super::decode("abc").is_err());
        assert_eq!(super::decode_any_case("00AbFf").unwrap(), vec![0, 171, 255]);
        assert!(super::decode_any_case("0x").is_err() && super::decode_any_case("+1").is_err() && super::decode_any_case("é1").is_err());
        assert!(super::is_canonical("00abff") && !super::is_canonical("") && !super::is_canonical("AB") && !super::is_canonical("abc"));
        assert!(super::is_canonical_len("abcd", 2) && !super::is_canonical_len("abcd", 3) && super::is_lower(""));
    }
}
