//! Mini's decimal naturals: every native id, height and amount is a canonical decimal STRING
//! (ASCII digits, no leading zero except "0" itself, any width). This is the one place that
//! validates, orders, steps and renders them.
use std::cmp::Ordering;

use crate::{Error, Result};

/// The width bound the wire gives a 256-bit-class natural in its decimal spelling.
pub const MAX_DIGITS: usize = 80;

/// Non-empty ASCII digits; leading zeros allowed (a digit string, not yet a canonical natural).
pub fn is_digits(text: &str) -> bool {
    !text.is_empty() && text.bytes().all(|b| b.is_ascii_digit())
}

/// A canonical decimal natural of any width.
pub fn is_canonical(text: &str) -> bool {
    is_digits(text) && (text.len() == 1 || !text.starts_with('0'))
}

/// A canonical decimal natural of at most `max_digits` digits.
pub fn is_canonical_max(text: &str, max_digits: usize) -> bool {
    text.len() <= max_digits && is_canonical(text)
}

/// A canonical signed decimal: a canonical natural, or `-` and a canonical NONZERO natural.
pub fn is_canonical_signed_max(text: &str, max_digits: usize) -> bool {
    match text.strip_prefix('-') {
        Some(magnitude) => magnitude != "0" && is_canonical_max(magnitude, max_digits),
        None => is_canonical_max(text, max_digits),
    }
}

fn natural(text: &str) -> Result<&str> {
    if is_canonical(text) {
        Ok(text)
    } else {
        Err(Error(format!("{text:?} is not a canonical decimal")))
    }
}

/// Numeric order of two canonical decimals (shorter is smaller; equal widths compare as text).
pub fn compare(left: &str, right: &str) -> Ordering {
    left.len().cmp(&right.len()).then_with(|| left.cmp(right))
}

/// `left <= right` for canonical decimals.
pub fn leq(left: &str, right: &str) -> bool {
    compare(left, right) != Ordering::Greater
}

/// The larger of two canonical decimals.
pub fn max<'a>(left: &'a str, right: &'a str) -> &'a str {
    if leq(left, right) {
        right
    } else {
        left
    }
}

/// `left + right`, exact at any width.
pub fn add(left: &str, right: &str) -> Result<String> {
    let (left, right) = (natural(left)?, natural(right)?);
    let mut a = left.bytes().rev();
    let mut b = right.bytes().rev();
    let mut carry = 0u8;
    let mut digits = Vec::with_capacity(left.len().max(right.len()) + 1);
    loop {
        let (x, y) = (a.next(), b.next());
        if x.is_none() && y.is_none() && carry == 0 {
            break;
        }
        let n = x.map_or(0, |v| v - b'0') + y.map_or(0, |v| v - b'0') + carry;
        digits.push(b'0' + n % 10);
        carry = n / 10;
    }
    digits.reverse();
    Ok(String::from_utf8(digits).expect("ASCII digits"))
}

/// `value + 1`.
pub fn successor(value: &str) -> Result<String> {
    add(natural(value)?, "1")
}

/// `value - 1` of a positive natural; `0` has no predecessor.
pub fn predecessor(value: &str) -> Result<String> {
    if natural(value)? == "0" {
        return Err("zero has no predecessor".into());
    }
    let mut digits = value.as_bytes().to_vec();
    for digit in digits.iter_mut().rev() {
        if *digit == b'0' {
            *digit = b'9';
        } else {
            *digit -= 1;
            break;
        }
    }
    let first = digits.iter().position(|d| *d != b'0').unwrap_or(digits.len() - 1);
    Ok(String::from_utf8(digits[first..].to_vec()).expect("ASCII digits"))
}

/// A big-endian unsigned integer as its canonical decimal (`[]` and zeros are `"0"`).
pub fn from_be_bytes(bytes: &[u8]) -> String {
    let mut n: Vec<u8> = bytes.iter().copied().skip_while(|b| *b == 0).collect();
    let mut digits = Vec::new();
    while !n.is_empty() {
        let mut rem = 0u32;
        let mut next = Vec::with_capacity(n.len());
        for byte in &n {
            let acc = rem * 256 + u32::from(*byte);
            let q = acc / 10;
            rem = acc % 10;
            if !(next.is_empty() && q == 0) {
                next.push(q as u8);
            }
        }
        digits.push(b'0' + rem as u8);
        n = next;
    }
    if digits.is_empty() {
        return "0".into();
    }
    digits.reverse();
    String::from_utf8(digits).expect("ASCII digits")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn predicates_pin_the_canonical_spelling() {
        assert!(is_canonical("0") && is_canonical("8501"));
        assert!(!is_canonical("01") && !is_canonical("") && !is_canonical("-1") && !is_canonical("1 "));
        assert!(is_digits("007") && !is_digits(""));
        assert!(is_canonical_max(&"9".repeat(80), MAX_DIGITS) && !is_canonical_max(&"9".repeat(81), MAX_DIGITS));
        assert!(is_canonical_signed_max("-5", 80) && is_canonical_signed_max("0", 80));
        assert!(!is_canonical_signed_max("-0", 80) && !is_canonical_signed_max("-", 80) && !is_canonical_signed_max("-05", 80));
    }

    #[test]
    fn order_and_arithmetic_are_exact_beyond_machine_words() {
        let big = "99999999999999999999999999999999";
        assert_eq!(successor(big).unwrap(), "100000000000000000000000000000000");
        assert_eq!(successor("0").unwrap(), "1");
        assert_eq!(add("999", "1").unwrap(), "1000");
        assert_eq!(add(big, big).unwrap(), "199999999999999999999999999999998");
        assert_eq!(predecessor("1000").unwrap(), "999");
        assert_eq!(predecessor("1").unwrap(), "0");
        assert!(predecessor("0").is_err() && predecessor("01").is_err() && add("1", "x").is_err());
        assert_eq!(compare("9", "10"), Ordering::Less);
        assert_eq!(compare("10", "9"), Ordering::Greater);
        assert_eq!(compare("123", "123"), Ordering::Equal);
        assert!(leq("9", "10") && leq("10", "10") && !leq("11", "10"));
        assert_eq!(max("9", "10"), "10");
        // Agreement with u128 across a carry-heavy sweep.
        for a in [0u128, 1, 9, 10, 99, 100, 12345, u64::MAX as u128, u64::MAX as u128 + 1] {
            for b in [0u128, 1, 9, 10, 99, 100, 99999, u64::MAX as u128] {
                assert_eq!(add(&a.to_string(), &b.to_string()).unwrap(), (a + b).to_string());
                assert_eq!(compare(&a.to_string(), &b.to_string()), a.cmp(&b));
            }
        }
    }

    #[test]
    fn big_endian_bytes_render_as_decimal() {
        assert_eq!(from_be_bytes(&[]), "0");
        assert_eq!(from_be_bytes(&[0, 0]), "0");
        assert_eq!(from_be_bytes(&[1, 0]), "256");
        assert_eq!(from_be_bytes(&[0, 0, 255]), "255");
        assert_eq!(from_be_bytes(&u128::MAX.to_be_bytes()), u128::MAX.to_string());
        assert_eq!(from_be_bytes(&[0xff; 32]), "115792089237316195423570985008687907853269984665640564039457584007913129639935");
    }
}
