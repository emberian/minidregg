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

/// A canonical decimal natural (Mini's wire spelling of every native id): ASCII digits, no
/// leading zero except "0" itself.
pub fn is_decimal(text: &str) -> bool {
    !text.is_empty()
        && text.bytes().all(|b| b.is_ascii_digit())
        && (text.len() == 1 || !text.starts_with('0'))
}

#[cfg(test)]
mod tests {
    #[test]
    fn hex_round_trip_and_strictness() {
        assert_eq!(super::encode(&[0, 171, 255]), "00abff");
        assert_eq!(super::decode("00abff").unwrap(), vec![0, 171, 255]);
        assert!(super::decode("AB").is_err());
        assert!(super::decode("abc").is_err());
        assert!(super::is_decimal("0") && super::is_decimal("8501"));
        assert!(!super::is_decimal("01") && !super::is_decimal("") && !super::is_decimal("-1"));
    }
}
