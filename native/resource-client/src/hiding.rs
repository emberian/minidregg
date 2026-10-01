//! K-NARROW-HIDE: the client side of the salted store root.
//!
//! The Host roots a cell over salted per-entry leaves (`Compiler/StoreCodec.lean`,
//! "The hiding root"):
//!
//! ```text
//! salt  = KMAC256(blinding bytes, entry bytes, 256, "DREGG.STORE.SALT/v1")
//! leaf  = cSHAKE256("DREGG.STORE.LEAF/v1", bytes(salt) ++ entry bytes)
//! root  = cSHAKE256("DREGG.STORE.ROOT/v2", frame ++ leaf_1 ++ ... ++ leaf_n)
//! ```
//!
//! Custody.  The cell's blinding is derived by the OWNER's client from its own
//! seed and the cell id, and sent once, in the birth:
//!
//! ```text
//! blinding key  = cSHAKE256("DREGG.CLIENT.BLIND/v1", seed)            (one per key)
//! cell blinding = KMAC256(blinding key, nat(cell id), 256, "DREGG.STORE.CELL-BLINDING/v1")
//! ```
//!
//! So the owner, or anyone the owner hands the blinding key to (escrow, a
//! co-owner: `mini key --action export-blinding`), recomputes every salt of
//! every cell it birthed without storing one.  The blinding key is not the
//! signing key: handing it over shares the openings, not the power to sign.
//! The Host holds each cell's blinding (it must, to serve openings), so the
//! salts hide uncovered entries from OTHER READERS, not from the operator.
//!
//! A view carries the root and its opening (`{frame, items}`); `verify_view`
//! recomputes every opened leaf and the root, and checks that every declared
//! entry the view displays is one of the opened entries.

use std::fs;
use std::path::Path;

use serde_json::{json, Value};
use sha3::digest::{core_api::CoreWrapper, ExtendableOutput, Update, XofReader};
use sha3::CShake256Core;

type Result<T> = std::result::Result<T, String>;

const BLIND_LABEL: &[u8] = b"DREGG.CLIENT.BLIND/v1";
const CELL_BLINDING: &[u8] = b"DREGG.STORE.CELL-BLINDING/v1";
const SALT: &[u8] = b"DREGG.STORE.SALT/v1";
const LEAF: &[u8] = b"DREGG.STORE.LEAF/v1";
const ROOT: &[u8] = b"DREGG.STORE.ROOT/v2";
const RATE: usize = 136;

/// The custody text printed with every blinding-key export.
pub(crate) const BLINDING_NOTICE: &str = "This is your blinding key. It opens every field of every \
cell you created: whoever holds it can recompute each salt and test guesses against the roots \
readers hold. It does not sign. Hand it only to an escrow or a co-owner you would show every \
field to. It is derived from your signing seed, so losing the seed loses it; the Host keeps each \
cell's blinding, so a lost key loses no existing opening, only the ability to blind new cells \
from this seed.";

fn cshake(function: &[u8], customization: &[u8], input: &[u8]) -> [u8; 32] {
    let core = if function.is_empty() {
        CShake256Core::new(customization)
    } else {
        CShake256Core::new_with_function_name(function, customization)
    };
    let mut hasher = CoreWrapper::from_core(core);
    hasher.update(input);
    let mut output = [0u8; 32];
    XofReader::read(&mut hasher.finalize_xof(), &mut output);
    output
}

fn left_encode(value: usize) -> Vec<u8> {
    let mut digits: Vec<u8> = value.to_be_bytes().into_iter().skip_while(|byte| *byte == 0).collect();
    if digits.is_empty() {
        digits.push(0);
    }
    let mut out = vec![digits.len() as u8];
    out.extend(digits);
    out
}

fn right_encode(value: usize) -> Vec<u8> {
    let mut digits: Vec<u8> = value.to_be_bytes().into_iter().skip_while(|byte| *byte == 0).collect();
    if digits.is_empty() {
        digits.push(0);
    }
    let count = digits.len() as u8;
    digits.push(count);
    digits
}

fn encode_string(bytes: &[u8]) -> Vec<u8> {
    let mut out = left_encode(bytes.len() * 8);
    out.extend_from_slice(bytes);
    out
}

fn bytepad(bytes: &[u8], width: usize) -> Vec<u8> {
    let mut out = left_encode(width);
    out.extend_from_slice(bytes);
    while out.len() % width != 0 {
        out.push(0);
    }
    out
}

/// SP 800-185 KMAC256 with a 32-byte tag (`Compiler/Sp800185Kmac256.lean`).
pub(crate) fn kmac256(key: &[u8], customization: &[u8], input: &[u8]) -> [u8; 32] {
    let mut x = bytepad(&encode_string(key), RATE);
    x.extend_from_slice(input);
    x.extend(right_encode(256));
    cshake(b"KMAC", customization, &x)
}

/// An unsigned big natural, little-endian 32-bit limbs.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Nat(Vec<u32>);

impl Nat {
    fn zero() -> Self {
        Nat(Vec::new())
    }
    fn normalize(mut self) -> Self {
        while self.0.last() == Some(&0) {
            self.0.pop();
        }
        self
    }
    fn is_zero(&self) -> bool {
        self.0.iter().all(|limb| *limb == 0)
    }
    fn from_le_bytes(bytes: &[u8]) -> Self {
        let mut limbs = Vec::new();
        for chunk in bytes.chunks(4) {
            let mut limb = [0u8; 4];
            limb[..chunk.len()].copy_from_slice(chunk);
            limbs.push(u32::from_le_bytes(limb));
        }
        Nat(limbs).normalize()
    }
    fn mul_add(&self, factor: u32, addend: u32) -> Self {
        let mut carry = addend as u64;
        let mut limbs = Vec::with_capacity(self.0.len() + 1);
        for limb in &self.0 {
            let value = *limb as u64 * factor as u64 + carry;
            limbs.push(value as u32);
            carry = value >> 32;
        }
        if carry != 0 {
            limbs.push(carry as u32);
        }
        Nat(limbs).normalize()
    }
    fn divmod(&self, divisor: u32) -> (Self, u32) {
        let mut remainder = 0u64;
        let mut limbs = vec![0u32; self.0.len()];
        for index in (0..self.0.len()).rev() {
            let value = (remainder << 32) | self.0[index] as u64;
            limbs[index] = (value / divisor as u64) as u32;
            remainder = value % divisor as u64;
        }
        (Nat(limbs).normalize(), remainder as u32)
    }
    /// `self - 1` for a positive natural.
    fn minus_one(&self) -> Self {
        let mut limbs = self.0.clone();
        for limb in limbs.iter_mut() {
            if *limb > 0 {
                *limb -= 1;
                break;
            }
            *limb = u32::MAX;
        }
        Nat(limbs).normalize()
    }
    fn from_decimal(text: &str) -> Result<Self> {
        if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err(format!("not a decimal natural: {text:?}"));
        }
        let mut value = Nat::zero();
        for byte in text.bytes() {
            value = value.mul_add(10, (byte - b'0') as u32);
        }
        Ok(value)
    }
    fn to_decimal(&self) -> String {
        if self.is_zero() {
            return "0".to_owned();
        }
        let mut digits = Vec::new();
        let mut value = self.clone();
        while !value.is_zero() {
            let (quotient, digit) = value.divmod(10);
            digits.push(b'0' + digit as u8);
            value = quotient;
        }
        digits.reverse();
        String::from_utf8(digits).expect("ascii digits")
    }
    /// `StreamCodec.nat`: base-255 little-endian digits, then the terminator 255.
    fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        let mut value = self.clone();
        while !value.is_zero() {
            let (quotient, digit) = value.divmod(255);
            out.push(digit as u8);
            value = quotient;
        }
        out.push(255);
        out
    }
}

fn nat_bytes(value: u64) -> Vec<u8> {
    Nat::from_le_bytes(&value.to_le_bytes()).encode()
}

fn decimal_bytes(text: &str) -> Result<Vec<u8>> {
    Ok(Nat::from_decimal(text)?.encode())
}

/// `bytesStream`: the length as a natural, then the bytes.
fn bytes_stream(bytes: &[u8]) -> Vec<u8> {
    let mut out = nat_bytes(bytes.len() as u64);
    out.extend_from_slice(bytes);
    out
}

/// `intStream`: the zigzag natural of a signed decimal.
fn int_bytes(text: &str) -> Result<Vec<u8>> {
    let (negative, magnitude) = match text.strip_prefix('-') {
        Some(rest) => (true, Nat::from_decimal(rest)?),
        None => (false, Nat::from_decimal(text)?),
    };
    let zigzag = if negative {
        // -m (m >= 1) is negSucc (m - 1), coded 2 (m - 1) + 1 = 2m - 1.
        if magnitude.is_zero() {
            return Err("-0 is not a canonical integer".to_owned());
        }
        magnitude.mul_add(2, 0).minus_one()
    } else {
        magnitude.mul_add(2, 0)
    };
    Ok(zigzag.encode())
}

pub(crate) fn read_seed(path: &Path) -> Result<[u8; 32]> {
    let bytes = fs::read(path)
        .map_err(|error| format!("cannot read signing key {}: {error}", path.display()))?;
    bytes.try_into().map_err(|_| {
        format!("signing key {} must contain exactly 32 raw bytes", path.display())
    })
}

/// The owner's blinding key, derived from its signing seed.
pub(crate) fn blinding_key(seed: &[u8; 32]) -> [u8; 32] {
    cshake(b"", BLIND_LABEL, seed)
}

/// The blinding of one cell, as the decimal the birth carries.
pub(crate) fn cell_blinding(blinding_key: &[u8; 32], cell: &str) -> Result<String> {
    let tag = kmac256(blinding_key, CELL_BLINDING, &decimal_bytes(cell)?);
    let value = Nat::from_le_bytes(&tag);
    if value.is_zero() {
        return Err("derived cell blinding is zero".to_owned());
    }
    Ok(value.to_decimal())
}

/// The KMAC key bytes the Host salts with: the blinding's canonical value
/// bytes (`intStream` for declared cells, `digestStream` for content cells).
fn salt_key(kind: &str, blinding: &str) -> Result<Vec<u8>> {
    match kind {
        "declared" => int_bytes(blinding),
        "content" => decimal_bytes(blinding),
        other => Err(format!("no blinding for storage {other}")),
    }
}

/// The salt of one entry of a cell this key blinded: what the owner
/// recomputes without asking the Host.
pub(crate) fn owner_salt(seed: &[u8; 32], kind: &str, cell: &str, entry: &[u8]) -> Result<[u8; 32]> {
    let blinding = cell_blinding(&blinding_key(seed), cell)?;
    Ok(kmac256(&salt_key(kind, &blinding)?, SALT, entry))
}

fn leaf(salt: &[u8], entry: &[u8]) -> [u8; 32] {
    let mut preimage = bytes_stream(salt);
    preimage.extend_from_slice(entry);
    cshake(b"", LEAF, &preimage)
}

fn decode_hex(value: &str) -> Result<Vec<u8>> {
    if value.len() % 2 != 0 {
        return Err("hex must have an even length".to_owned());
    }
    (0..value.len())
        .step_by(2)
        .map(|index| {
            u8::from_str_radix(&value[index..index + 2], 16).map_err(|_| "invalid hex".to_owned())
        })
        .collect()
}

/// The canonical entry bytes of one displayed declared entry.
fn declared_entry_bytes(entry: &Value) -> Result<Vec<u8>> {
    let key = entry.get("key").ok_or("declared entry lacks key")?;
    let text = |name: &str| -> Result<String> {
        key.get(name)
            .and_then(Value::as_str)
            .map(str::to_owned)
            .ok_or_else(|| format!("declared key lacks {name}"))
    };
    let mut bytes = match key.get("type").and_then(Value::as_str) {
        Some("object") => {
            let mut b = vec![0u8];
            b.extend(decimal_bytes(&text("resource")?)?);
            b.extend(decimal_bytes(&text("field")?)?);
            b
        }
        Some("account") => {
            let mut b = vec![1u8];
            b.extend(decimal_bytes(&text("resource")?)?);
            b.extend(decimal_bytes(&text("field")?)?);
            b
        }
        Some("program") => {
            let mut b = vec![2u8];
            b.extend(decimal_bytes(&text("resource")?)?);
            b
        }
        other => return Err(format!("declared entry of unknown key type {other:?}")),
    };
    let value = entry
        .get("value")
        .and_then(Value::as_str)
        .ok_or("declared entry lacks value")?;
    bytes.extend(int_bytes(value)?);
    Ok(bytes)
}

/// Verify a resource (or at-height) view against its own root: every opened
/// leaf and the root are recomputed from the opening alone, and every declared
/// entry the view displays must be an opened entry.  Returns the summary the
/// client prints beside the view.
pub(crate) fn verify_view(view: &Value) -> Result<Value> {
    let resource = if view.get("opening").is_some() {
        view
    } else if let Some(inner) = view.get("resource") {
        inner
    } else {
        return Ok(json!({"verified": false, "reason": "view carries no opening"}));
    };
    let opening = resource.get("opening").ok_or("view lacks opening")?;
    let frame = decode_hex(opening.get("frame").and_then(Value::as_str).ok_or("opening lacks frame")?)?;
    if frame.is_empty() {
        return Ok(json!({"verified": false, "reason": "this kind has no store opening"}));
    }
    let items = opening
        .get("items")
        .and_then(Value::as_array)
        .ok_or("opening lacks items")?;
    let mut preimage = frame;
    let mut opened = Vec::new();
    let mut sealed = 0usize;
    for item in items {
        if let Some(salt) = item.get("salt").and_then(Value::as_str) {
            let salt = decode_hex(salt)?;
            let entry = decode_hex(item.get("entry").and_then(Value::as_str).ok_or("opened item lacks entry")?)?;
            preimage.extend(leaf(&salt, &entry));
            opened.push(entry);
        } else {
            let sealed_leaf = decode_hex(item.get("leaf").and_then(Value::as_str).ok_or("item lacks leaf")?)?;
            if sealed_leaf.len() != 32 {
                return Err("a sealed leaf is not 32 bytes".to_owned());
            }
            preimage.extend(sealed_leaf);
            sealed += 1;
        }
    }
    let computed = Nat::from_le_bytes(&cshake(b"", ROOT, &preimage)).to_decimal();
    let claimed = resource
        .get("cell")
        .and_then(|cell| cell.get("root"))
        .and_then(Value::as_str)
        .ok_or("view lacks cell.root")?;
    if computed != claimed {
        return Err(format!(
            "view refused: its opening recomputes root {computed}, the view claims {claimed}"
        ));
    }
    let entries = resource
        .get("cell")
        .and_then(|cell| cell.get("entries"))
        .and_then(Value::as_array);
    let declared = entries.is_some_and(|list| {
        list.iter().all(|entry| {
            matches!(
                entry.get("key").and_then(|key| key.get("type")).and_then(Value::as_str),
                Some("object" | "account" | "program")
            )
        })
    });
    let mut checked = false;
    if let (Some(list), true) = (entries, declared) {
        if list.len() != opened.len() {
            return Err(format!(
                "view refused: it displays {} entries and opens {}",
                list.len(),
                opened.len()
            ));
        }
        for entry in list {
            let bytes = declared_entry_bytes(entry)?;
            if !opened.contains(&bytes) {
                return Err("view refused: a displayed entry is not an opened entry".to_owned());
            }
        }
        checked = true;
    }
    Ok(json!({"verified": true, "root": computed, "opened": opened.len(),
        "sealed": sealed, "entriesChecked": checked}))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    /// The Lean core's conformance vector (`kmac256_conforms_tagged`).
    #[test]
    fn kmac_matches_the_lean_conformance_vector() {
        let key: Vec<u8> = (0x40u8..0x60).collect();
        assert_eq!(
            hex(&kmac256(&key, b"My Tagged Application", &[0, 1, 2, 3])),
            "f2d95c33c9a201eb10c524b9084b4bacae0092f869122df7d7870b92c842e05b"
        );
        assert_eq!(
            hex(&kmac256(&key, b"DREGG/NATIVE-HOST/CHECKPOINT-MAC/v1", b"abc")),
            "b1862dc66901cf8ad0de93235e93a487ec110f46a668a9b5122e0dcb1efa711f"
        );
    }

    #[test]
    fn nat_codec_is_base_255_little_endian() {
        assert_eq!(nat_bytes(0), vec![255]);
        assert_eq!(nat_bytes(3), vec![3, 255]);
        assert_eq!(nat_bytes(255), vec![0, 1, 255]);
        assert_eq!(decimal_bytes("1000").unwrap(), vec![235, 3, 255]);
        assert_eq!(int_bytes("3").unwrap(), vec![6, 255]);
        assert_eq!(int_bytes("-1").unwrap(), vec![1, 255]);
        assert_eq!(int_bytes("-2").unwrap(), vec![3, 255]);
    }

    #[test]
    fn decimal_round_trips_at_256_bits() {
        let bytes = [0xffu8; 32];
        let value = Nat::from_le_bytes(&bytes);
        assert_eq!(Nat::from_decimal(&value.to_decimal()).unwrap(), value);
    }

    #[test]
    fn cell_blinding_is_per_key_and_per_cell() {
        let a = blinding_key(&[1u8; 32]);
        let b = blinding_key(&[2u8; 32]);
        assert_ne!(cell_blinding(&a, "7").unwrap(), cell_blinding(&b, "7").unwrap());
        assert_ne!(cell_blinding(&a, "7").unwrap(), cell_blinding(&a, "8").unwrap());
        assert_eq!(cell_blinding(&a, "7").unwrap(), cell_blinding(&a, "7").unwrap());
        assert_ne!(a, [1u8; 32]);
    }
}
