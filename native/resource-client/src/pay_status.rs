//! Typed decoder for the exact Host.PayClaims status181 JSON projection.
//! Payment state comes only from the exact source index. Membership, a journal
//! marker, or matching text never substitutes for a consumed origin.
use crate::{decode_hex, hex, Result};
use serde_json::Value;
use std::cmp::Ordering;

const MAX_NAT: &str =
    "115792089237316195423570985008687907853269984665640564039457584007913129639935";

/// Source Response.small uses 256-bit naturals, including coordinates. Keep the
/// exact decimal without narrowing until an actual caller requires u64/u128.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Nat(String);
impl Nat {
    /// Operator configs may encode a natural as a JSON number; source replies
    /// use decimal strings. Both retain the exact 256-bit integer representation.
    pub(crate) fn from_json(value: &Value) -> Result<Self> {
        match value {
            Value::String(text) => Self::parse(text),
            Value::Number(number) => Self::parse(&number.to_string()),
            _ => Err("paid natural requires a decimal string or exact JSON number".into()),
        }
    }
    pub(crate) fn parse(text: &str) -> Result<Self> {
        if text.is_empty()
            || !text.bytes().all(|b| b.is_ascii_digit())
            || (text.len() > 1 && text.starts_with('0'))
            || text.len() > MAX_NAT.len()
            || (text.len() == MAX_NAT.len() && text > MAX_NAT)
        {
            return Err("paid status requires canonical decimal below 2^256".into());
        }
        Ok(Self(text.into()))
    }
    pub(crate) fn as_str(&self) -> &str {
        &self.0
    }
    pub(crate) fn to_u64(&self) -> Result<u64> {
        self.0
            .parse()
            .map_err(|_| "paid status value exceeds u64".into())
    }
    pub(crate) fn to_u128(&self) -> Result<u128> {
        self.0
            .parse()
            .map_err(|_| "paid status value exceeds u128".into())
    }
    pub(crate) fn matches_u64(&self, value: u64) -> bool {
        self.0 == value.to_string()
    }
    pub(crate) fn matches_u128(&self, value: u128) -> bool {
        self.0 == value.to_string()
    }
    fn zero(&self) -> bool {
        self.0 == "0"
    }
    fn divided_by(&self, divisor: u32) -> Self {
        let mut remainder = 0u32;
        let mut result = String::new();
        for digit in self.0.bytes() {
            let value = remainder * 10 + u32::from(digit - b'0');
            let quotient = value / divisor;
            if quotient != 0 || !result.is_empty() {
                result.push(char::from(b'0' + quotient as u8));
            }
            remainder = value % divisor;
        }
        if result.is_empty() {
            result.push('0');
        }
        Self(result)
    }
    fn add(&self, other: &Self) -> Result<Self> {
        let mut a = self.0.bytes().rev();
        let mut b = other.0.bytes().rev();
        let mut digits = Vec::new();
        let mut carry = 0u8;
        loop {
            let x = a.next();
            let y = b.next();
            if x.is_none() && y.is_none() && carry == 0 {
                break;
            }
            let n = x.map(|v| v - b'0').unwrap_or(0) + y.map(|v| v - b'0').unwrap_or(0) + carry;
            digits.push(b'0' + n % 10);
            carry = n / 10;
        }
        digits.reverse();
        Self::parse(std::str::from_utf8(&digits).map_err(|_| "internal decimal sum")?)
    }
}
impl Ord for Nat {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0
            .len()
            .cmp(&other.0.len())
            .then_with(|| self.0.cmp(&other.0))
    }
}
impl PartialOrd for Nat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl std::fmt::Display for Nat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Freshness {
    Fresh,
    Missing,
    Malformed,
    Future,
    Stale,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LeaseState {
    Active,
    Expired,
    NotEnrolled,
}
impl LeaseState {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Active => "active",
            Self::Expired => "expired",
            Self::NotEnrolled => "notEnrolled",
        }
    }
}
impl Freshness {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Fresh => "fresh",
            Self::Missing => "missing",
            Self::Malformed => "malformed",
            Self::Future => "future",
            Self::Stale => "stale",
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PendingReason {
    TermsStale,
    Expired,
    AuthStale,
}
impl PendingReason {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::TermsStale => "termsStale",
            Self::Expired => "expired",
            Self::AuthStale => "authStale",
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Mode {
    Enrol,
    Renew,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Authorization {
    OriginalMemo,
    AcceptCurrentQuote,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Locator {
    pub signature: [u8; 64],
    pub original_recipient: [u8; 32],
    pub claim_id: [u8; 102],
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ChainTip {
    pub slot: Nat,
    pub block_time: Nat,
    pub hour: Nat,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Entry {
    pub subject: Nat,
    pub account: Nat,
    pub ssh_blob: Vec<u8>,
    pub index: Option<Nat>,
    pub lease_until: Nat,
    pub enrolled_slot: Nat,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Coordinates {
    pub amount_atomic: Nat,
    pub slot: Nat,
    pub index: Nat,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Pending {
    pub coordinates: Coordinates,
    pub reason: PendingReason,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Consumed {
    pub coordinates: Coordinates,
    pub mode: Mode,
    pub weeks: Nat,
    pub minted_credit: Nat,
    pub birth_fee: Nat,
    pub membership_credit: Nat,
    pub credited_remainder: Nat,
    pub pricing_commitment: [u8; 32],
    pub authorization: Authorization,
    pub accepted_request: Option<Vec<u8>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct JournalNegative {
    pub coordinates: Coordinates,
    pub reason_code: u8,
    pub reason: String,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Payment {
    NotRequested,
    Unknown,
    Pending(Pending),
    Consumed(Consumed),
    JournalNegative(JournalNegative),
}
impl Payment {
    pub(crate) fn coordinates(&self) -> Option<&Coordinates> {
        match self {
            Self::NotRequested | Self::Unknown => None,
            Self::Pending(v) => Some(&v.coordinates),
            Self::Consumed(v) => Some(&v.coordinates),
            Self::JournalNegative(v) => Some(&v.coordinates),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Status {
    pub raw: Value,
    pub identity_key: [u8; 32],
    pub locator: Option<Locator>,
    pub clock_hour: Nat,
    pub as_of: Option<ChainTip>,
    pub chain_freshness: Freshness,
    pub lease_state: LeaseState,
    pub entry: Option<Entry>,
    pub payment: Payment,
}
impl Status {
    pub(crate) fn pending_message(&self) -> Option<String> {
        match (&self.payment,&self.locator) {
            (Payment::Pending(p),Some(locator))=>Some(format!(
                "payment received; admission pending; request current quote; do not pay again (claim {}, {}, {} atomic units)",
                hex(&locator.claim_id),p.reason.as_str(),p.coordinates.amount_atomic)),
            _=>None,
        }
    }
}
fn need(condition: bool, message: &str) -> Result<()> {
    if condition {
        Ok(())
    } else {
        Err(message.into())
    }
}
fn object(value: &Value, required: &[&str], optional: &[&str]) -> Result<()> {
    let object = value.as_object().ok_or("paid status object expected")?;
    need(
        required.iter().all(|key| object.contains_key(*key))
            && object
                .keys()
                .all(|key| required.contains(&key.as_str()) || optional.contains(&key.as_str())),
        "paid status missing or unknown fields",
    )
}
fn string<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("paid status missing string {key}"))
}
fn nat(value: &Value, key: &str) -> Result<Nat> {
    Nat::parse(string(value, key)?)
}
fn bytes(value: &Value, key: &str, max: usize) -> Result<Vec<u8>> {
    let text = string(value, key)?;
    need(
        text.len() <= max * 2
            && text.len() % 2 == 0
            && mini_sdk::hex::is_lower(text),
        "paid status requires bounded lowercase hexadecimal",
    )?;
    decode_hex(text)
}
fn fixed<const N: usize>(value: &Value, key: &str) -> Result<[u8; N]> {
    bytes(value, key, N)?
        .try_into()
        .map_err(|_| format!("paid status {key} must be {N} bytes"))
}
fn request_fixed<const N: usize>(value: &Value, key: &str) -> Result<[u8; N]> {
    let text = string(value, key)?;
    need(
        text.len() == N * 2 && text.bytes().all(|b| b.is_ascii_hexdigit()),
        "status request hexadecimal width",
    )?;
    decode_hex(text)?
        .try_into()
        .map_err(|_| "status request hexadecimal width".into())
}
fn coordinates(value: &Value) -> Result<Coordinates> {
    Ok(Coordinates {
        amount_atomic: nat(value, "amountAtomic")?,
        slot: nat(value, "slot")?,
        index: nat(value, "index")?,
    })
}
fn payment(value: &Value) -> Result<Payment> {
    Ok(match string(value, "state")? {
        "notRequested" => {
            object(value, &["state"], &[])?;
            Payment::NotRequested
        }
        "unobservedOrUnknownPositiveV1" => {
            object(value, &["state"], &[])?;
            Payment::Unknown
        }
        "pendingV2" => {
            object(
                value,
                &["state", "amountAtomic", "slot", "index", "reason"],
                &[],
            )?;
            let reason = match string(value, "reason")? {
                "termsStale" => PendingReason::TermsStale,
                "expired" => PendingReason::Expired,
                "authStale" => PendingReason::AuthStale,
                _ => return Err("unknown pending reason".into()),
            };
            Payment::Pending(Pending {
                coordinates: coordinates(value)?,
                reason,
            })
        }
        "consumedV2" => {
            object(
                value,
                &[
                    "state",
                    "amountAtomic",
                    "slot",
                    "index",
                    "mode",
                    "weeks",
                    "mintedCredit",
                    "birthFee",
                    "membershipCredit",
                    "creditedRemainder",
                    "pricingCommitment",
                    "authorization",
                    "acceptedRequest",
                ],
                &[],
            )?;
            let mode = match string(value, "mode")? {
                "enrol" => Mode::Enrol,
                "renew" => Mode::Renew,
                _ => return Err("unknown consumed economic mode".into()),
            };
            let authorization = match string(value, "authorization")? {
                "originalMemo" => Authorization::OriginalMemo,
                "acceptCurrentQuote" => Authorization::AcceptCurrentQuote,
                _ => return Err("unknown consumption authorization".into()),
            };
            let accepted_request = if value["acceptedRequest"].is_null() {
                None
            } else {
                let bytes = bytes(value, "acceptedRequest", 2048)?;
                need(!bytes.is_empty(), "empty accepted request")?;
                Some(bytes)
            };
            need(
                (authorization == Authorization::OriginalMemo) == accepted_request.is_none(),
                "consumption authorization and accepted request disagree",
            )?;
            let v = Consumed {
                coordinates: coordinates(value)?,
                mode,
                authorization,
                accepted_request,
                weeks: nat(value, "weeks")?,
                minted_credit: nat(value, "mintedCredit")?,
                birth_fee: nat(value, "birthFee")?,
                membership_credit: nat(value, "membershipCredit")?,
                credited_remainder: nat(value, "creditedRemainder")?,
                pricing_commitment: fixed(value, "pricingCommitment")?,
            };
            need(!v.weeks.zero(), "consumed weeks must be positive")?;
            need(
                v.mode != Mode::Renew || v.birth_fee.zero(),
                "renewal consumption has a birth fee",
            )?;
            need(
                v.birth_fee
                    .add(&v.membership_credit)?
                    .add(&v.credited_remainder)?
                    == v.minted_credit,
                "consumed source split does not conserve minted credit",
            )?;
            Payment::Consumed(v)
        }
        "journalV1Negative" => {
            object(
                value,
                &[
                    "state",
                    "amountAtomic",
                    "slot",
                    "index",
                    "reasonCode",
                    "reason",
                ],
                &[],
            )?;
            let code = nat(value, "reasonCode")?.to_u64()?;
            need(
                code <= 8 || (100..=105).contains(&code),
                "unknown negative journal reason code",
            )?;
            let reason = string(value, "reason")?;
            need(
                !reason.is_empty() && reason.len() <= 512,
                "invalid negative journal reason display",
            )?;
            Payment::JournalNegative(JournalNegative {
                coordinates: coordinates(value)?,
                reason_code: code as u8,
                reason: reason.into(),
            })
        }
        _ => return Err("unknown source paid status state".into()),
    })
}

pub(crate) fn parse(value: &Value, request: &Value) -> Result<Status> {
    need(
        serde_json::to_vec(value).map_err(|e| e.to_string())?.len() <= 8192,
        "paid status exceeds source JSON bound",
    )?;
    object(
        request,
        &["identityKey"],
        &["signature", "originalRecipient"],
    )?;
    let expected_identity = request_fixed::<32>(request, "identityKey")?;
    let expected_locator = match (request.get("signature"), request.get("originalRecipient")) {
        (None, None) => None,
        (Some(_), Some(_)) => Some((
            request_fixed::<64>(request, "signature")?,
            request_fixed::<32>(request, "originalRecipient")?,
        )),
        _ => return Err("status signature and originalRecipient must be supplied together".into()),
    };
    object(
        value,
        &[
            "type",
            "identityKey",
            "paymentLocator",
            "clockHour",
            "asOf",
            "chainFreshness",
            "leaseState",
            "entry",
            "payment",
        ],
        &[],
    )?;
    need(
        string(value, "type")? == "payStatus",
        "source payStatus type required",
    )?;
    let identity_key = fixed(value, "identityKey")?;
    need(
        identity_key == expected_identity,
        "source status identity mismatch",
    )?;
    let locator = match expected_locator {
        None => {
            need(
                value["paymentLocator"].is_null(),
                "unsolicited payment locator",
            )?;
            None
        }
        Some((signature, recipient)) => {
            let v = &value["paymentLocator"];
            object(v, &["signature", "originalRecipient", "claimId"], &[])?;
            let locator = Locator {
                signature: fixed(v, "signature")?,
                original_recipient: fixed(v, "originalRecipient")?,
                claim_id: fixed(v, "claimId")?,
            };
            need(
                locator.signature == signature && locator.original_recipient == recipient,
                "source status payment locator mismatch",
            )?;
            need(
                &locator.claim_id[..6] == b"soltx:"
                    && locator.claim_id[6..70] == signature
                    && locator.claim_id[70..] == recipient,
                "source claim id differs from exact payment locator",
            )?;
            Some(locator)
        }
    };
    let clock_hour = nat(value, "clockHour")?;
    let as_of = if value["asOf"].is_null() {
        None
    } else {
        let v = &value["asOf"];
        object(v, &["slot", "blockTime", "hour"], &[])?;
        let tip = ChainTip {
            slot: nat(v, "slot")?,
            block_time: nat(v, "blockTime")?,
            hour: nat(v, "hour")?,
        };
        need(
            tip.hour == tip.block_time.divided_by(3600),
            "source chain hour differs from block time",
        )?;
        Some(tip)
    };
    let chain_freshness = match string(value, "chainFreshness")? {
        "fresh" => Freshness::Fresh,
        "missing" => Freshness::Missing,
        "malformed" => Freshness::Malformed,
        "future" => Freshness::Future,
        "stale" => Freshness::Stale,
        _ => return Err("unknown source chain freshness".into()),
    };
    need(
        (chain_freshness == Freshness::Missing) == as_of.is_none(),
        "source freshness and chain evidence disagree",
    )?;
    if let Some(tip) = &as_of {
        let shaped =
            tip.slot.to_u64().is_ok_and(|n| n > 0) && tip.block_time.to_u64().is_ok_and(|n| n > 0);
        need(
            (chain_freshness == Freshness::Malformed) != shaped,
            "source malformed evidence diagnostic disagrees with coordinates",
        )?;
    }
    let entry = if value["entry"].is_null() {
        None
    } else {
        let v = &value["entry"];
        object(
            v,
            &[
                "subject",
                "account",
                "sshBlob",
                "index",
                "leaseUntil",
                "enrolledSlot",
            ],
            &[],
        )?;
        Some(Entry {
            subject: nat(v, "subject")?,
            account: nat(v, "account")?,
            ssh_blob: bytes(v, "sshBlob", 51)?,
            index: if v["index"].is_null() {
                None
            } else {
                Some(nat(v, "index")?)
            },
            lease_until: nat(v, "leaseUntil")?,
            enrolled_slot: nat(v, "enrolledSlot")?,
        })
    };
    let lease_state = match string(value, "leaseState")? {
        "active" => LeaseState::Active,
        "expired" => LeaseState::Expired,
        "notEnrolled" => LeaseState::NotEnrolled,
        _ => return Err("unknown source lease state".into()),
    };
    let expected_lease = match &entry {
        None => LeaseState::NotEnrolled,
        Some(e) if e.lease_until > clock_hour => LeaseState::Active,
        Some(_) => LeaseState::Expired,
    };
    need(
        lease_state == expected_lease,
        "source lease state and entry coordinates disagree",
    )?;
    let payment = payment(&value["payment"])?;
    need(
        matches!(payment, Payment::NotRequested) == locator.is_none(),
        "source payment state and requested locator disagree",
    )?;
    Ok(Status {
        raw: value.clone(),
        identity_key,
        locator,
        clock_hour,
        as_of,
        chain_freshness,
        lease_state,
        entry,
        payment,
    })
}

#[cfg(test)]
pub(crate) fn fixture(request: &Value, payment: Value) -> Value {
    use serde_json::json;
    let locator = if request.get("signature").is_some() {
        let signature = decode_hex(request["signature"].as_str().unwrap()).unwrap();
        let recipient = decode_hex(request["originalRecipient"].as_str().unwrap()).unwrap();
        json!({"signature":request["signature"],"originalRecipient":request["originalRecipient"],"claimId":hex(&[b"soltx:".as_slice(),&signature,&recipient].concat())})
    } else {
        Value::Null
    };
    json!({"type":"payStatus","identityKey":request["identityKey"],"paymentLocator":locator,
        "clockHour":"1000","asOf":{"slot":"99","blockTime":"3600000","hour":"1000"},
        "chainFreshness":"fresh","leaseState":"notEnrolled","entry":null,"payment":payment})
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    fn request() -> Value {
        json!({"identityKey":hex(&[1;32]),"signature":hex(&[2;64]),"originalRecipient":hex(&[3;32])})
    }
    fn pending() -> Value {
        json!({"state":"pendingV2","amountAtomic":"522","slot":"99","index":"0","reason":"termsStale"})
    }
    fn consumed() -> Value {
        json!({"state":"consumedV2","amountAtomic":"522","slot":"99","index":"0","mode":"enrol","weeks":"1","mintedCredit":"522","birthFee":"7","membershipCredit":"168","creditedRemainder":"347","pricingCommitment":hex(&[4;32]),"authorization":"originalMemo","acceptedRequest":null})
    }
    #[test]
    fn exact_origin_states_and_current_quote_are_distinct() {
        let req = request();
        let v = fixture(&req, pending());
        let parsed = parse(&v, &req).unwrap();
        assert_eq!(parsed.raw, v);
        assert!(parsed
            .pending_message()
            .unwrap()
            .contains("do not pay again"));
        assert!(parsed
            .payment
            .coordinates()
            .unwrap()
            .amount_atomic
            .matches_u128(522));
        let mut v = fixture(&req, consumed());
        assert!(matches!(
            parse(&v, &req).unwrap().payment,
            Payment::Consumed(Consumed {
                authorization: Authorization::OriginalMemo,
                ..
            })
        ));
        v["payment"]["authorization"] = json!("acceptCurrentQuote");
        assert!(parse(&v, &req).is_err());
        v["payment"]["acceptedRequest"] = json!("010203");
        assert!(matches!(
            parse(&v, &req).unwrap().payment,
            Payment::Consumed(Consumed {
                authorization: Authorization::AcceptCurrentQuote,
                ..
            })
        ));
        let req = json!({"identityKey":hex(&[1;32])});
        assert!(matches!(
            parse(&fixture(&req, json!({"state":"notRequested"})), &req)
                .unwrap()
                .payment,
            Payment::NotRequested
        ));
    }
    #[test]
    fn every_locator_coordinate_is_bound_and_states_are_closed() {
        let req = request();
        let base = fixture(&req, pending());
        for (key, value) in [
            ("signature", json!(hex(&[8; 64]))),
            ("originalRecipient", json!(hex(&[8; 32]))),
            ("claimId", json!(hex(&[8; 102]))),
        ] {
            let mut v = base.clone();
            v["paymentLocator"][key] = value;
            assert!(parse(&v, &req).is_err(), "{key}");
        }
        for (key, value) in [
            ("identityKey", json!(hex(&[8; 32]))),
            ("clockHour", json!("01000")),
            ("leaseState", json!("paid")),
            ("chainFreshness", json!("unknown")),
        ] {
            let mut v = base.clone();
            v[key] = value;
            assert!(parse(&v, &req).is_err(), "{key}");
        }
        for key in ["amountAtomic", "slot", "index", "reason"] {
            let mut v = base.clone();
            v["payment"].as_object_mut().unwrap().remove(key);
            assert!(parse(&v, &req).is_err(), "{key}");
        }
        let mut v = base.clone();
        v["payment"]["state"] = json!("enrolled");
        assert!(parse(&v, &req).is_err());
        let mut v = base.clone();
        v["payment"]["reason"] = json!("retry");
        assert!(parse(&v, &req).is_err());
        let mut v = base;
        v["payment"]["extra"] = json!(true);
        assert!(parse(&v, &req).is_err());
        let mut v = fixture(&req, consumed());
        v["payment"]["mintedCredit"] = json!("523");
        assert!(parse(&v, &req).is_err());
        let mut v = fixture(&req, consumed());
        v["payment"]["acceptedRequest"] = json!("01");
        assert!(parse(&v, &req).is_err());
        v["payment"]["authorization"] = json!("acceptCurrentQuote");
        for bad in [String::new(), "Ff".into(), "0".into(), "01".repeat(2049)] {
            v["payment"]["acceptedRequest"] = json!(bad);
            assert!(parse(&v, &req).is_err());
        }
    }
    #[test]
    fn membership_is_independent_of_payment_and_diagnostics_remain_useful() {
        let req = request();
        let mut v = fixture(&req, json!({"state":"unobservedOrUnknownPositiveV1"}));
        v["entry"] = json!({"subject":"12","account":"13","sshBlob":"","index":null,"leaseUntil":"1001","enrolledSlot":"98"});
        v["leaseState"] = json!("active");
        assert!(matches!(parse(&v, &req).unwrap().payment, Payment::Unknown));
        v["chainFreshness"] = json!("stale");
        assert_eq!(parse(&v, &req).unwrap().chain_freshness, Freshness::Stale);
        v["asOf"] = Value::Null;
        v["chainFreshness"] = json!("missing");
        assert!(parse(&v, &req).is_ok());
        v["chainFreshness"] = json!("fresh");
        assert!(parse(&v, &req).is_err());
        v["chainFreshness"] = json!("missing");
        v["clockHour"] = json!("1001");
        assert!(parse(&v, &req).is_err());
        v["leaseState"] = json!("expired");
        assert!(parse(&v, &req).is_ok());
    }
    #[test]
    fn source_naturals_are_exact_at_256_bits_and_narrow_only_on_request() {
        let n = Nat::parse(MAX_NAT).unwrap();
        assert!(n.to_u128().is_err());
        assert!(n.to_u64().is_err());
        assert!(n > Nat::parse("999").unwrap());
        assert_eq!(
            Nat::parse("3600000").unwrap().divided_by(3600).as_str(),
            "1000"
        );
        for bad in [
            "",
            "00",
            "01",
            "+1",
            "-1",
            "1.0",
            "115792089237316195423570985008687907853269984665640564039457584007913129639936",
        ] {
            assert!(Nat::parse(bad).is_err(), "{bad}");
        }
        let req = request();
        let mut v = fixture(&req, pending());
        v["payment"]["amountAtomic"] = json!(MAX_NAT);
        assert_eq!(
            parse(&v, &req)
                .unwrap()
                .payment
                .coordinates()
                .unwrap()
                .amount_atomic,
            n
        );
    }
}
