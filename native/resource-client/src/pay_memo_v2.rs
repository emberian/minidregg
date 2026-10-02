//! Exact consumer of Kernel.PayEnrolMemoV2 and Host.PayClaims purchase quotes.
//! No transfer submission, real-key loading, or client pricing is performed here.
//! Quote validation precedes signing. Source amounts are checked for conservation,
//! never reconstructed from a parallel tariff formula.

use crate::join_solana::{
    b64_decode, b64_encode, ssh_blob, sshsig_raw_signature_for, sshsig_signed_data_for,
};
use crate::{decode_hex, hex, Result};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use serde_json::Value;

pub(crate) const UNSIGNED_LENGTH: usize = 229;
pub(crate) const BINARY_LENGTH: usize = 357;
pub(crate) const MEMO_LENGTH: usize = 485;
pub(crate) const SSH_NAMESPACE: &str = "dregg-enrol@v2";
const PREFIX: &str = "enrol:v2:";
const TAG: &[u8] = b"DREGG/PAY/ENROL/POSSESSION/v2";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PurchaseMode {
    Enrol,
    Renew,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Context {
    pub mint: [u8; 32],
    pub token_program: [u8; 32],
    pub recipient: [u8; 32],
}

/// The locally intended signer/custody and pinned receiving context. The quote
/// may author prices, but may not replace the requested purchase or either key.
#[derive(Clone, Debug)]
pub(crate) struct ExpectedPurchase {
    pub identity_key: [u8; 32],
    pub current_key: [u8; 32],
    pub authority_epoch: u64,
    pub ssh_key: [u8; 32],
    pub next_digest: Option<[u8; 32]>,
    pub mode: PurchaseMode,
    pub weeks: u32,
    pub starter: u64,
    pub expiry_hour: u64,
    pub context: Context,
    pub deployment_commitment: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Unsigned {
    pub mode: u8,
    pub deployment_commitment: [u8; 32],
    pub pricing_commitment: [u8; 32],
    pub identity_key: [u8; 32],
    pub authorizing_key: [u8; 32],
    pub authority_epoch: u64,
    pub ssh_key: [u8; 32],
    pub next_digest: [u8; 32],
    pub weeks: u32,
    pub starter: u64,
    pub expiry_hour: u64,
    pub amount_atomic: u64,
}

impl Unsigned {
    pub(crate) fn validate(&self) -> Result<()> {
        if self.authority_epoch == 0 || self.weeks == 0 {
            return Err("v2 epoch and weeks must be positive".into());
        }
        match self.mode {
            1 if self.authorizing_key == self.identity_key && self.authority_epoch == 1 => Ok(()),
            2 => Ok(()),
            3 if self.next_digest == [0; 32] => Ok(()),
            _ => Err("invalid v2 mode/initial authority/NEXT shape".into()),
        }
    }

    pub(crate) fn declared_next(&self) -> Option<[u8; 32]> {
        if self.mode == 3 {
            None
        } else {
            Some(self.next_digest)
        }
    }

    pub(crate) fn encode(&self) -> Result<[u8; UNSIGNED_LENGTH]> {
        self.validate()?;
        let mut out = Vec::with_capacity(UNSIGNED_LENGTH);
        out.push(self.mode);
        out.extend(self.deployment_commitment);
        out.extend(self.pricing_commitment);
        out.extend(self.identity_key);
        out.extend(self.authorizing_key);
        out.extend(self.authority_epoch.to_le_bytes());
        out.extend(self.ssh_key);
        out.extend(self.next_digest);
        out.extend(self.weeks.to_le_bytes());
        out.extend(self.starter.to_le_bytes());
        out.extend(self.expiry_hour.to_le_bytes());
        out.extend(self.amount_atomic.to_le_bytes());
        out.try_into()
            .map_err(|_| "internal v2 unsigned width".into())
    }

    pub(crate) fn decode(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != UNSIGNED_LENGTH {
            return Err("v2 unsigned must be 229 bytes".into());
        }
        let mut at = 0;
        fn take<const N: usize>(bytes: &[u8], at: &mut usize) -> [u8; N] {
            let value = bytes[*at..*at + N]
                .try_into()
                .expect("fixed v2 width checked");
            *at += N;
            value
        }
        let value = Self {
            mode: take::<1>(bytes, &mut at)[0],
            deployment_commitment: take(bytes, &mut at),
            pricing_commitment: take(bytes, &mut at),
            identity_key: take(bytes, &mut at),
            authorizing_key: take(bytes, &mut at),
            authority_epoch: u64::from_le_bytes(take(bytes, &mut at)),
            ssh_key: take(bytes, &mut at),
            next_digest: take(bytes, &mut at),
            weeks: u32::from_le_bytes(take(bytes, &mut at)),
            starter: u64::from_le_bytes(take(bytes, &mut at)),
            expiry_hour: u64::from_le_bytes(take(bytes, &mut at)),
            amount_atomic: u64::from_le_bytes(take(bytes, &mut at)),
        };
        value.validate()?;
        Ok(value)
    }

    pub(crate) fn frame(&self, context: &Context) -> Result<Vec<u8>> {
        Ok([
            TAG,
            &self.encode()?,
            &context.mint,
            &context.token_program,
            &context.recipient,
        ]
        .concat())
    }
}

/// Bounded unsigned arithmetic solely for conservation of source-authored split.
/// Four little-endian limbs match the source's < 2^256 metadata bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Uint256([u64; 4]);
impl Uint256 {
    fn from_u64(n: u64) -> Self {
        Self([n, 0, 0, 0])
    }
    fn parse(text: &str) -> Result<Self> {
        if text.is_empty()
            || text.len() > 78
            || (text.len() > 1 && text.starts_with('0'))
            || !text.bytes().all(|b| b.is_ascii_digit())
        {
            return Err("canonical decimal string required".into());
        }
        let mut out = Self([0; 4]);
        for digit in text.bytes() {
            let mut carry = u128::from(digit - b'0');
            for limb in &mut out.0 {
                let next = u128::from(*limb) * 10 + carry;
                *limb = next as u64;
                carry = next >> 64;
            }
            if carry != 0 {
                return Err("source credit exceeds 256 bits".into());
            }
        }
        Ok(out)
    }
    fn add(self, rhs: Self) -> Result<Self> {
        let mut out = [0; 4];
        let mut carry = 0u128;
        for (i, limb) in out.iter_mut().enumerate() {
            let sum = u128::from(self.0[i]) + u128::from(rhs.0[i]) + carry;
            *limb = sum as u64;
            carry = sum >> 64;
        }
        if carry != 0 {
            return Err("source credit partition overflows 256 bits".into());
        }
        Ok(Self(out))
    }
    fn ge(self, rhs: Self) -> bool {
        self.0.iter().rev().cmp(rhs.0.iter().rev()).is_ge()
    }
    pub(crate) fn decimal(self) -> String {
        if self == Self([0; 4]) {
            return "0".into();
        }
        let mut limbs = self.0;
        let mut digits = Vec::new();
        while limbs != [0; 4] {
            let mut remainder = 0u128;
            for limb in limbs.iter_mut().rev() {
                let current = (remainder << 64) | u128::from(*limb);
                *limb = (current / 10) as u64;
                remainder = current % 10;
            }
            digits.push(b'0' + remainder as u8);
        }
        digits.reverse();
        String::from_utf8(digits).expect("decimal ASCII")
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Split {
    pub amount_atomic: u64,
    pub minted_credit: Uint256,
    pub birth_fee: Uint256,
    pub membership_credit: Uint256,
    pub credited_remainder: Uint256,
}

#[derive(Clone, Debug)]
pub(crate) struct ValidatedQuote {
    unsigned: Unsigned,
    context: Context,
    split: Split,
    authority_root: [u8; 32],
    pay_root: [u8; 32],
    as_of_slot: u64,
    as_of_block_time: u64,
    index: u64,
}
impl ValidatedQuote {
    pub(crate) fn unsigned(&self) -> &Unsigned {
        &self.unsigned
    }
    pub(crate) fn context(&self) -> &Context {
        &self.context
    }
    pub(crate) fn split(&self) -> &Split {
        &self.split
    }
    pub(crate) fn authority_root(&self) -> &[u8; 32] {
        &self.authority_root
    }
    pub(crate) fn pay_root(&self) -> &[u8; 32] {
        &self.pay_root
    }
    pub(crate) fn as_of(&self) -> (u64, u64) {
        (self.as_of_slot, self.as_of_block_time)
    }
    pub(crate) fn index(&self) -> u64 {
        self.index
    }
    pub(crate) fn signing_message(&self) -> Result<Vec<u8>> {
        self.unsigned.frame(&self.context)
    }
}

fn keys(value: &Value, names: &[&str]) -> Result<()> {
    let object = value.as_object().ok_or("quote object expected")?;
    if object.len() != names.len() || names.iter().any(|name| !object.contains_key(*name)) {
        return Err(format!(
            "quote fields differ from source schema: wanted {names:?}"
        ));
    }
    Ok(())
}
fn text<'a>(value: &'a Value, name: &str) -> Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("quote {name} must be a string"))
}
fn nat(value: &Value, name: &str) -> Result<u64> {
    let string = text(value, name)?;
    if string.is_empty()
        || (string.len() > 1 && string.starts_with('0'))
        || !string.bytes().all(|b| b.is_ascii_digit())
    {
        return Err(format!("quote {name} must be a canonical decimal string"));
    }
    string
        .parse()
        .map_err(|_| format!("quote {name} exceeds u64"))
}
fn fixed<const N: usize>(value: &Value, name: &str) -> Result<[u8; N]> {
    let s = text(value, name)?;
    if s.len() != 2 * N {
        return Err(format!("quote {name} must be {N} bytes"));
    }
    let bytes = decode_hex(s)?;
    if hex(&bytes) != s {
        return Err(format!("quote {name} must be canonical lowercase hex"));
    }
    bytes.try_into().map_err(|_| format!("quote {name} width"))
}
fn next(value: &Value, name: &str) -> Result<Option<[u8; 32]>> {
    if value.get(name) == Some(&Value::Null) {
        Ok(None)
    } else {
        fixed(value, name).map(Some)
    }
}
fn same<T: PartialEq>(actual: T, expected: T, name: &str) -> Result<()> {
    if actual == expected {
        Ok(())
    } else {
        Err(format!("source quote {name} mismatch"))
    }
}
fn credit(value: &Value, name: &str) -> Result<Uint256> {
    Uint256::parse(text(value, name)?)
}

/// Validate the source presentation and every signed field against local intent.
/// The caller must obtain this JSON through its pinned/authenticated Host path.
/// Hash commitments are copied, never recomputed using a native price formula.
pub(crate) fn validate_purchase_quote(
    value: &Value,
    expected: &ExpectedPurchase,
) -> Result<ValidatedQuote> {
    if serde_json::to_vec(value).map_err(|e| e.to_string())?.len() > 8192 {
        return Err("quote exceeds source JSON bound".into());
    }
    keys(
        value,
        &[
            "type",
            "authorityRoot",
            "payRoot",
            "asOf",
            "priceReserved",
            "maxQuoteLifetimeHours",
            "settlement",
            "owner",
            "split",
            "signing",
        ],
    )?;
    same(text(value, "type")?, "payQuote", "type")?;
    same(
        value.get("priceReserved"),
        Some(&Value::Bool(false)),
        "priceReserved",
    )?;
    same(
        nat(value, "maxQuoteLifetimeHours")?,
        1,
        "source quote lifetime",
    )?;
    let authority_root = fixed(value, "authorityRoot")?;
    let pay_root = fixed(value, "payRoot")?;
    let as_of = &value["asOf"];
    keys(as_of, &["slot", "blockTime", "hour"])?;
    let as_of_slot = nat(as_of, "slot")?;
    let as_of_block_time = nat(as_of, "blockTime")?;
    if as_of_slot == 0 || as_of_block_time == 0 {
        return Err("malformed source chain tip".into());
    }
    let hour = as_of_block_time / 3600;
    same(nat(as_of, "hour")?, hour, "chain hour")?;
    if expected.expiry_hour < hour || expected.expiry_hour > hour.saturating_add(1) {
        return Err("quote outside source expiry window".into());
    }
    let settlement = &value["settlement"];
    keys(settlement, &["index", "recipient", "mint", "tokenProgram"])?;
    let context = Context {
        mint: fixed(settlement, "mint")?,
        token_program: fixed(settlement, "tokenProgram")?,
        recipient: fixed(settlement, "recipient")?,
    };
    same(&context, &expected.context, "receiving context")?;
    if context.mint == [0; 32] || context.token_program == [0; 32] || context.recipient == [0; 32] {
        return Err("zero receiving context key".into());
    }
    let index = nat(settlement, "index")?;
    let owner = &value["owner"];
    keys(
        owner,
        &[
            "identityKey",
            "authorizingKey",
            "authorityEpoch",
            "nextKeyDigest",
        ],
    )?;
    same(
        fixed::<32>(owner, "identityKey")?,
        expected.identity_key,
        "owner identity",
    )?;
    same(
        fixed::<32>(owner, "authorizingKey")?,
        expected.current_key,
        "current owner key",
    )?;
    same(
        nat(owner, "authorityEpoch")?,
        expected.authority_epoch,
        "current owner epoch",
    )?;
    same(
        next(owner, "nextKeyDigest")?,
        expected.next_digest,
        "current NEXT",
    )?;
    let signing = &value["signing"];
    keys(
        signing,
        &[
            "kind",
            "unsigned",
            "unsignedCanonical",
            "miniMessage",
            "sshMessage",
            "sshNamespace",
        ],
    )?;
    same(text(signing, "kind")?, "purchase", "signing kind")?;
    same(
        text(signing, "sshNamespace")?,
        SSH_NAMESPACE,
        "SSH namespace",
    )?;
    let fields = &signing["unsigned"];
    keys(
        fields,
        &[
            "wireMode",
            "deploymentCommitment",
            "pricingCommitment",
            "identityKey",
            "authorizingKey",
            "authorityEpoch",
            "sshKey",
            "nextKeyDigest",
            "declaredNext",
            "weeks",
            "minimumStarterCredit",
            "expiryHour",
            "amountAtomic",
        ],
    )?;
    let unsigned = Unsigned {
        mode: u8::try_from(nat(fields, "wireMode")?).map_err(|_| "wire mode overflow")?,
        deployment_commitment: fixed(fields, "deploymentCommitment")?,
        pricing_commitment: fixed(fields, "pricingCommitment")?,
        identity_key: fixed(fields, "identityKey")?,
        authorizing_key: fixed(fields, "authorizingKey")?,
        authority_epoch: nat(fields, "authorityEpoch")?,
        ssh_key: fixed(fields, "sshKey")?,
        next_digest: fixed(fields, "nextKeyDigest")?,
        weeks: u32::try_from(nat(fields, "weeks")?).map_err(|_| "weeks overflow")?,
        starter: nat(fields, "minimumStarterCredit")?,
        expiry_hour: nat(fields, "expiryHour")?,
        amount_atomic: nat(fields, "amountAtomic")?,
    };
    unsigned.validate()?;
    if unsigned.amount_atomic == 0 {
        return Err("source quote amount must be positive".into());
    }
    let wanted_mode = match (expected.mode, expected.next_digest) {
        (PurchaseMode::Enrol, Some(_)) => 1,
        (PurchaseMode::Enrol, None) => {
            return Err("initial enrollment requires a real NEXT commitment".into())
        }
        (PurchaseMode::Renew, Some(_)) => 2,
        (PurchaseMode::Renew, None) => 3,
    };
    same(unsigned.mode, wanted_mode, "wire/economic mode")?;
    same(
        unsigned.identity_key,
        expected.identity_key,
        "signed identity",
    )?;
    same(
        unsigned.authorizing_key,
        expected.current_key,
        "signed current key",
    )?;
    same(
        unsigned.authority_epoch,
        expected.authority_epoch,
        "signed epoch",
    )?;
    same(unsigned.ssh_key, expected.ssh_key, "SSH key")?;
    same(
        unsigned.deployment_commitment,
        expected.deployment_commitment,
        "deployment commitment",
    )?;
    same(
        unsigned.declared_next(),
        expected.next_digest,
        "signed NEXT",
    )?;
    same(
        next(fields, "declaredNext")?,
        expected.next_digest,
        "declared NEXT display",
    )?;
    same(unsigned.weeks, expected.weeks, "weeks")?;
    same(unsigned.starter, expected.starter, "starter")?;
    same(unsigned.expiry_hour, expected.expiry_hour, "expiry")?;
    same(
        fixed::<UNSIGNED_LENGTH>(signing, "unsignedCanonical")?,
        unsigned.encode()?,
        "canonical unsigned bytes",
    )?;
    let frame = unsigned.frame(&context)?;
    for name in ["miniMessage", "sshMessage"] {
        let message = text(signing, name)?;
        same(message, hex(&frame).as_str(), name)?;
    }
    let fields = &value["split"];
    keys(
        fields,
        &[
            "amountAtomic",
            "mintedCredit",
            "birthFee",
            "weeks",
            "membershipCredit",
            "creditedRemainder",
            "minimumStarterCredit",
        ],
    )?;
    let split = Split {
        amount_atomic: nat(fields, "amountAtomic")?,
        minted_credit: credit(fields, "mintedCredit")?,
        birth_fee: credit(fields, "birthFee")?,
        membership_credit: credit(fields, "membershipCredit")?,
        credited_remainder: credit(fields, "creditedRemainder")?,
    };
    same(split.amount_atomic, unsigned.amount_atomic, "split amount")?;
    same(
        nat(fields, "weeks")?,
        u64::from(expected.weeks),
        "split weeks",
    )?;
    same(
        nat(fields, "minimumStarterCredit")?,
        expected.starter,
        "split starter",
    )?;
    same(
        split
            .birth_fee
            .add(split.membership_credit)?
            .add(split.credited_remainder)?,
        split.minted_credit,
        "source credit conservation",
    )?;
    if !split
        .credited_remainder
        .ge(Uint256::from_u64(expected.starter))
    {
        return Err("source split fails requested starter".into());
    }
    if split.membership_credit == Uint256::from_u64(0)
        || split.minted_credit == Uint256::from_u64(0)
    {
        return Err("zero source membership credit".into());
    }
    if expected.mode == PurchaseMode::Renew {
        same(split.birth_fee, Uint256::from_u64(0), "renewal birth fee")?;
    }
    Ok(ValidatedQuote {
        unsigned,
        context,
        split,
        authority_root,
        pay_root,
        as_of_slot,
        as_of_block_time,
        index,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SignedMemo {
    pub unsigned: Unsigned,
    pub mini_signature: [u8; 64],
    pub ssh_signature: [u8; 64],
}
impl SignedMemo {
    pub(crate) fn verify(&self, context: &Context) -> Result<()> {
        let frame = self.unsigned.frame(context)?;
        VerifyingKey::from_bytes(&self.unsigned.authorizing_key)
            .map_err(|e| e.to_string())?
            .verify_strict(&frame, &Signature::from_bytes(&self.mini_signature))
            .map_err(|_| "miniSigInvalid".to_owned())?;
        VerifyingKey::from_bytes(&self.unsigned.ssh_key)
            .map_err(|e| e.to_string())?
            .verify_strict(
                &sshsig_signed_data_for(SSH_NAMESPACE, &frame),
                &Signature::from_bytes(&self.ssh_signature),
            )
            .map_err(|_| "sshSigInvalid".to_owned())
    }
    pub(crate) fn binary(&self) -> Result<[u8; BINARY_LENGTH]> {
        let bytes = [
            &self.unsigned.encode()?[..],
            &self.mini_signature,
            &self.ssh_signature,
        ]
        .concat();
        bytes
            .try_into()
            .map_err(|_| "internal v2 binary width".into())
    }
    pub(crate) fn encode(&self) -> Result<String> {
        Ok(format!("{PREFIX}{}", b64_encode(&self.binary()?)))
    }
    pub(crate) fn parse(text: &str) -> Result<Self> {
        if text.len() != MEMO_LENGTH
            || !text.starts_with(PREFIX)
            || !text.is_ascii()
            || text.contains('=')
        {
            return Err("canonical v2 memo must be 485 ASCII bytes".into());
        }
        let bytes = b64_decode(&text[PREFIX.len()..])?;
        if bytes.len() != BINARY_LENGTH {
            return Err("v2 memo binary must be 357 bytes".into());
        }
        let memo = Self {
            unsigned: Unsigned::decode(&bytes[..UNSIGNED_LENGTH])?,
            mini_signature: bytes[UNSIGNED_LENGTH..UNSIGNED_LENGTH + 64]
                .try_into()
                .unwrap(),
            ssh_signature: bytes[UNSIGNED_LENGTH + 64..].try_into().unwrap(),
        };
        same(memo.encode()?.as_str(), text, "canonical memo spelling")?;
        Ok(memo)
    }
    pub(crate) fn parse_and_verify(text: &str, context: &Context) -> Result<Self> {
        let memo = Self::parse(text)?;
        memo.verify(context)?;
        Ok(memo)
    }
}

// Canonical, bounded armour envelope around the shared strict SSHSIG structure
// parser. Its legacy entry point permits trailing prose; paid-v2 assembly does not.
fn check_armour(armoured: &str) -> Result<()> {
    if armoured.len() > 4096 {
        return Err("SSHSIG armour exceeds 4096 bytes".into());
    }
    let lines: Vec<_> = armoured
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect();
    if lines.first().copied() != Some("-----BEGIN SSH SIGNATURE-----")
        || lines.last().copied() != Some("-----END SSH SIGNATURE-----")
        || lines.len() < 3
    {
        return Err("SSHSIG armour must contain exactly one signed envelope".into());
    }
    let body = lines[1..lines.len() - 1].concat();
    let raw = b64_decode(&body)?;
    same(b64_encode(&raw), body, "canonical SSHSIG base64")
}

/// Sign only a previously validated quote, and reject a different local Mini
/// key before signing. The SSHSIG parser is shared with v1 with exact namespace.
pub(crate) fn sign_and_assemble(
    quote: &ValidatedQuote,
    mini: &SigningKey,
    ssh_armoured: &str,
) -> Result<SignedMemo> {
    same(
        mini.verifying_key().to_bytes(),
        quote.unsigned.authorizing_key,
        "local Mini signer",
    )?;
    let frame = quote.signing_message()?;
    check_armour(ssh_armoured)?;
    let ssh_signature = sshsig_raw_signature_for(
        ssh_armoured,
        &ssh_blob(&quote.unsigned.ssh_key),
        SSH_NAMESPACE,
    )?;
    // Validate SSH possession before making the second local signature.
    VerifyingKey::from_bytes(&quote.unsigned.ssh_key)
        .map_err(|e| e.to_string())?
        .verify_strict(
            &sshsig_signed_data_for(SSH_NAMESPACE, &frame),
            &Signature::from_bytes(&ssh_signature),
        )
        .map_err(|_| "sshSigInvalid".to_owned())?;
    let memo = SignedMemo {
        unsigned: quote.unsigned.clone(),
        mini_signature: mini.sign(&frame).to_bytes(),
        ssh_signature,
    };
    memo.verify(&quote.context)?;
    Ok(memo)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn fixture(
        mode: PurchaseMode,
        next_digest: Option<[u8; 32]>,
    ) -> (Value, ExpectedPurchase, SigningKey, SigningKey) {
        let mini = SigningKey::from_bytes(&[42; 32]);
        let ssh = SigningKey::from_bytes(&[43; 32]);
        let expected = ExpectedPurchase {
            identity_key: mini.verifying_key().to_bytes(),
            current_key: mini.verifying_key().to_bytes(),
            authority_epoch: 1,
            ssh_key: ssh.verifying_key().to_bytes(),
            next_digest,
            mode,
            weeks: 1,
            starter: 347,
            expiry_hour: 1001,
            context: Context {
                mint: [8; 32],
                token_program: [9; 32],
                recipient: [10; 32],
            },
            deployment_commitment: [11; 32],
        };
        let wire_mode = if mode == PurchaseMode::Enrol {
            1
        } else if next_digest.is_some() {
            2
        } else {
            3
        };
        let birth = if mode == PurchaseMode::Enrol { 7 } else { 0 };
        let amount = birth + 168 + 347;
        let unsigned = Unsigned {
            mode: wire_mode,
            deployment_commitment: expected.deployment_commitment,
            pricing_commitment: [12; 32],
            identity_key: expected.identity_key,
            authorizing_key: expected.current_key,
            authority_epoch: 1,
            ssh_key: expected.ssh_key,
            next_digest: next_digest.unwrap_or([0; 32]),
            weeks: 1,
            starter: 347,
            expiry_hour: 1001,
            amount_atomic: amount,
        };
        let frame = unsigned.frame(&expected.context).unwrap();
        let value = json!({"type":"payQuote", "authorityRoot":hex(&[13;32]), "payRoot":hex(&[14;32]),
            "asOf":{"slot":"9000","blockTime":"3600000","hour":"1000"}, "priceReserved":false,"maxQuoteLifetimeHours":"1",
            "settlement":{"index":"0","recipient":hex(&expected.context.recipient),"mint":hex(&expected.context.mint),"tokenProgram":hex(&expected.context.token_program)},
            "owner":{"identityKey":hex(&expected.identity_key),"authorizingKey":hex(&expected.current_key),"authorityEpoch":"1","nextKeyDigest":next_digest.map(|v|hex(&v))},
            "split":{"amountAtomic":amount.to_string(),"mintedCredit":amount.to_string(),"birthFee":birth.to_string(),"weeks":"1","membershipCredit":"168","creditedRemainder":"347","minimumStarterCredit":"347"},
            "signing":{"kind":"purchase","unsigned":{"wireMode":wire_mode.to_string(),"deploymentCommitment":hex(&unsigned.deployment_commitment),"pricingCommitment":hex(&unsigned.pricing_commitment),
                "identityKey":hex(&unsigned.identity_key),"authorizingKey":hex(&unsigned.authorizing_key),"authorityEpoch":"1","sshKey":hex(&unsigned.ssh_key),"nextKeyDigest":hex(&unsigned.next_digest),
                "declaredNext":next_digest.map(|v|hex(&v)),"weeks":"1","minimumStarterCredit":"347","expiryHour":"1001","amountAtomic":amount.to_string()},
                "unsignedCanonical":hex(&unsigned.encode().unwrap()),"miniMessage":hex(&frame),"sshMessage":hex(&frame),"sshNamespace":SSH_NAMESPACE}});
        (value, expected, mini, ssh)
    }
    fn ssh_string(bytes: &[u8]) -> Vec<u8> {
        [(bytes.len() as u32).to_be_bytes().as_slice(), bytes].concat()
    }
    fn armour(key: &SigningKey, namespace: &str, message: &[u8]) -> String {
        let sig = key
            .sign(&sshsig_signed_data_for(namespace, message))
            .to_bytes();
        let inner = [ssh_string(b"ssh-ed25519"), ssh_string(&sig)].concat();
        let body = [
            b"SSHSIG".to_vec(),
            1u32.to_be_bytes().to_vec(),
            ssh_string(&ssh_blob(&key.verifying_key().to_bytes())),
            ssh_string(namespace.as_bytes()),
            ssh_string(&[]),
            ssh_string(b"sha512"),
            ssh_string(&inner),
        ]
        .concat();
        format!(
            "-----BEGIN SSH SIGNATURE-----\n{}\n-----END SSH SIGNATURE-----\n",
            b64_encode(&body)
        )
    }
    fn signed() -> (SignedMemo, Context) {
        let (value, expected, mini, ssh) = fixture(PurchaseMode::Enrol, Some([5; 32]));
        let quote = validate_purchase_quote(&value, &expected).unwrap();
        let armour = armour(&ssh, SSH_NAMESPACE, &quote.signing_message().unwrap());
        (
            sign_and_assemble(&quote, &mini, &armour).unwrap(),
            expected.context,
        )
    }

    #[test]
    fn source_literal_wire_vector_matches() {
        // Literal from Kernel/PayEnrolMemoV2.lean; structural fixture, not valid signatures.
        let text = "enrol:v2:AQEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAQAAAAAAAAAEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAUAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAAAF4AAAAAAAAAXJcHAAAAAAANAQAAAAAAAAYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcH";
        let memo = SignedMemo::parse(text).unwrap();
        assert_eq!(memo.unsigned.mode, 1);
        assert_eq!(memo.unsigned.deployment_commitment, {
            let mut d = [0; 32];
            d[0] = 1;
            d
        });
        assert_eq!(memo.unsigned.identity_key, [3; 32]);
        assert_eq!(memo.unsigned.authority_epoch, 1);
        assert_eq!(memo.unsigned.starter, 94);
        assert_eq!(memo.unsigned.expiry_hour, 497500);
        assert_eq!(memo.unsigned.amount_atomic, 269);
        assert_eq!(memo.mini_signature, [6; 64]);
        assert_eq!(memo.ssh_signature, [7; 64]);
        assert_eq!(memo.encode().unwrap(), text);
    }
    #[test]
    fn both_possessions_exact_lengths_and_roundtrip() {
        let (memo, context) = signed();
        assert_eq!(memo.unsigned.encode().unwrap().len(), 229);
        assert_eq!(memo.binary().unwrap().len(), 357);
        let text = memo.encode().unwrap();
        assert_eq!(text.len(), 485);
        assert!(!text.contains('='));
        assert_eq!(SignedMemo::parse_and_verify(&text, &context).unwrap(), memo);
        for wrong in [
            format!("{text}="),
            text.replace("enrol:v2:", "enrol:v1:"),
            format!(" {text}"),
            text[..484].to_owned(),
        ] {
            assert!(SignedMemo::parse(&wrong).is_err());
        }
        let mut bad = memo.clone();
        bad.mini_signature[0] ^= 1;
        assert!(bad.verify(&context).is_err());
        let mut bad = memo.clone();
        bad.ssh_signature[0] ^= 1;
        assert!(bad.verify(&context).is_err());
    }
    #[test]
    fn quote_tamper_every_binding() {
        let (value, expected, _, _) = fixture(PurchaseMode::Enrol, Some([5; 32]));
        validate_purchase_quote(&value, &expected).unwrap();
        let mutations = vec![
            ("/type", json!("other")),
            ("/priceReserved", json!(true)),
            ("/maxQuoteLifetimeHours", json!("2")),
            ("/authorityRoot", json!("00")),
            ("/payRoot", json!("00")),
            ("/asOf/slot", json!("0")),
            ("/asOf/blockTime", json!("3603600")),
            ("/asOf/hour", json!("1001")),
            ("/settlement/mint", json!(hex(&[4; 32]))),
            ("/settlement/tokenProgram", json!(hex(&[4; 32]))),
            ("/settlement/recipient", json!(hex(&[4; 32]))),
            ("/owner/identityKey", json!(hex(&[4; 32]))),
            ("/owner/authorizingKey", json!(hex(&[4; 32]))),
            ("/owner/authorityEpoch", json!("2")),
            ("/owner/nextKeyDigest", Value::Null),
            ("/signing/kind", json!("claim")),
            ("/signing/sshNamespace", json!("dregg-enrol@v1")),
            ("/signing/unsigned/wireMode", json!("2")),
            (
                "/signing/unsigned/deploymentCommitment",
                json!(hex(&[4; 32])),
            ),
            ("/signing/unsigned/pricingCommitment", json!(hex(&[4; 32]))),
            ("/signing/unsigned/identityKey", json!(hex(&[4; 32]))),
            ("/signing/unsigned/authorizingKey", json!(hex(&[4; 32]))),
            ("/signing/unsigned/authorityEpoch", json!("2")),
            ("/signing/unsigned/sshKey", json!(hex(&[4; 32]))),
            ("/signing/unsigned/nextKeyDigest", json!(hex(&[4; 32]))),
            ("/signing/unsigned/declaredNext", Value::Null),
            ("/signing/unsigned/weeks", json!("2")),
            ("/signing/unsigned/minimumStarterCredit", json!("348")),
            ("/signing/unsigned/expiryHour", json!("1002")),
            ("/signing/unsigned/amountAtomic", json!("523")),
            ("/signing/unsignedCanonical", json!("00")),
            ("/signing/miniMessage", json!("00")),
            ("/signing/sshMessage", json!("00")),
            ("/split/amountAtomic", json!("523")),
            ("/split/mintedCredit", json!("523")),
            ("/split/birthFee", json!("8")),
            ("/split/membershipCredit", json!("169")),
            ("/split/creditedRemainder", json!("348")),
            ("/split/weeks", json!("2")),
            ("/split/minimumStarterCredit", json!("348")),
        ];
        for (path, replacement) in mutations {
            let mut altered = value.clone();
            *altered.pointer_mut(path).unwrap() = replacement;
            assert!(
                validate_purchase_quote(&altered, &expected).is_err(),
                "accepted mutation {path}"
            );
        }
        let mut extra = value.clone();
        extra["callerPrice"] = json!(1);
        assert!(validate_purchase_quote(&extra, &expected).is_err());
        let mut noncanonical = value.clone();
        noncanonical["split"]["weeks"] = json!("01");
        assert!(validate_purchase_quote(&noncanonical, &expected).is_err());
        let mut wrong = expected.clone();
        wrong.ssh_key = [4; 32];
        assert!(validate_purchase_quote(&value, &wrong).is_err());
    }
    #[test]
    fn none_and_some_zero_are_different_modes() {
        for (next, wanted) in [(None, 3), (Some([0; 32]), 2)] {
            let (value, expected, mini, ssh) = fixture(PurchaseMode::Renew, next);
            let quote = validate_purchase_quote(&value, &expected).unwrap();
            assert_eq!(quote.unsigned.mode, wanted);
            let memo = sign_and_assemble(
                &quote,
                &mini,
                &armour(&ssh, SSH_NAMESPACE, &quote.signing_message().unwrap()),
            )
            .unwrap();
            assert_eq!(
                SignedMemo::parse_and_verify(&memo.encode().unwrap(), &expected.context)
                    .unwrap()
                    .unsigned
                    .declared_next(),
                next
            );
            let mut wrong = expected.clone();
            wrong.next_digest = if next.is_none() { Some([0; 32]) } else { None };
            assert!(validate_purchase_quote(&value, &wrong).is_err());
        }
    }
    #[test]
    fn all_unsigned_and_context_fields_are_cryptographically_bound() {
        let (value, expected, mini, ssh) = fixture(PurchaseMode::Renew, Some([5; 32]));
        let quote = validate_purchase_quote(&value, &expected).unwrap();
        let memo = sign_and_assemble(
            &quote,
            &mini,
            &armour(&ssh, SSH_NAMESPACE, &quote.signing_message().unwrap()),
        )
        .unwrap();
        let raw = memo.unsigned.encode().unwrap();
        // First byte of each of the twelve exact wire fields.
        for offset in [0, 1, 33, 65, 97, 129, 137, 169, 201, 205, 213, 221] {
            let mut bytes = raw;
            bytes[offset] ^= 1;
            match Unsigned::decode(&bytes) {
                Err(_) => {}
                Ok(unsigned) => {
                    let mut bad = memo.clone();
                    bad.unsigned = unsigned;
                    assert!(
                        bad.verify(&expected.context).is_err(),
                        "field offset {offset}"
                    );
                }
            }
        }
        for which in 0..3 {
            let mut context = expected.context.clone();
            match which {
                0 => context.mint[0] ^= 1,
                1 => context.token_program[0] ^= 1,
                _ => context.recipient[0] ^= 1,
            };
            assert!(memo.verify(&context).is_err());
        }
    }
    #[test]
    fn wrong_mini_key_ssh_key_namespace_and_message_refuse() {
        let (value, expected, mini, ssh) = fixture(PurchaseMode::Enrol, Some([5; 32]));
        let quote = validate_purchase_quote(&value, &expected).unwrap();
        let frame = quote.signing_message().unwrap();
        let good = armour(&ssh, SSH_NAMESPACE, &frame);
        assert!(sign_and_assemble(&quote, &SigningKey::from_bytes(&[44; 32]), &good).is_err());
        assert!(sign_and_assemble(
            &quote,
            &mini,
            &armour(&SigningKey::from_bytes(&[44; 32]), SSH_NAMESPACE, &frame)
        )
        .is_err());
        assert!(sign_and_assemble(&quote, &mini, &armour(&ssh, "dregg-enrol@v1", &frame)).is_err());
        assert!(sign_and_assemble(
            &quote,
            &mini,
            &armour(&ssh, SSH_NAMESPACE, b"different message")
        )
        .is_err());
        assert!(sign_and_assemble(&quote, &mini, &format!("{good}unexpected suffix")).is_err());
        assert!(sign_and_assemble(&quote, &mini, &format!("{good}{good}")).is_err());
        assert!(check_armour(&"A".repeat(4097)).is_err());
    }
    #[test]
    fn bounded_credit_conservation_is_not_a_price_formula() {
        let maximum =
            "115792089237316195423570985008687907853269984665640564039457584007913129639935";
        let max = Uint256::parse(maximum).unwrap();
        assert_eq!(max.decimal(), maximum);
        assert!(max.add(Uint256::from_u64(1)).is_err());
        assert!(Uint256::parse(
            "115792089237316195423570985008687907853269984665640564039457584007913129639936"
        )
        .is_err());
        for bad in ["", "01", "-1", "+1", "1.0", " 1"] {
            assert!(Uint256::parse(bad).is_err());
        }
        let (mut value, expected, _, _) = fixture(PurchaseMode::Enrol, Some([5; 32]));
        // Credits above u128 remain exactly conserved; no rate or rounding is recomputed.
        value["split"]["membershipCredit"] = json!("340282366920938463463374607431768211456");
        value["split"]["mintedCredit"] = json!("340282366920938463463374607431768211810");
        assert!(validate_purchase_quote(&value, &expected).is_ok());
    }

    // Actual signed official-SDK packets from transaction-sizing/evidence-485.
    // Synthetic fixture wallets; the Memo payload is a 485-byte length fixture,
    // not a valid paid-entry statement. We reverify packet signatures here.
    fn take_packet<'a>(bytes: &'a [u8], at: &mut usize, n: usize) -> &'a [u8] {
        let out = bytes.get(*at..*at + n).expect("fixture packet bounds");
        *at += n;
        out
    }
    fn shortvec(bytes: &[u8], at: &mut usize) -> usize {
        let mut n = 0;
        let mut shift = 0;
        loop {
            let b = take_packet(bytes, at, 1)[0];
            n |= usize::from(b & 127) << shift;
            if b & 128 == 0 {
                return n;
            }
            shift += 7;
            assert!(shift <= 14);
        }
    }
    fn verify_packet(bytes: &[u8], versioned: bool) {
        let mut at = 0;
        let signatures = shortvec(bytes, &mut at);
        let sigs = take_packet(bytes, &mut at, 64 * signatures);
        let message = &bytes[at..];
        if versioned {
            assert_eq!(take_packet(bytes, &mut at, 1), [128]);
        }
        let header = take_packet(bytes, &mut at, 3);
        assert_eq!(usize::from(header[0]), signatures);
        let accounts = shortvec(bytes, &mut at);
        let keys = take_packet(bytes, &mut at, 32 * accounts);
        for i in 0..signatures {
            VerifyingKey::from_bytes(keys[i * 32..(i + 1) * 32].try_into().unwrap())
                .unwrap()
                .verify_strict(
                    message,
                    &Signature::from_slice(&sigs[i * 64..(i + 1) * 64]).unwrap(),
                )
                .unwrap();
        }
        take_packet(bytes, &mut at, 32);
        let instructions = shortvec(bytes, &mut at);
        let mut found = false;
        let memo_program = bs58::decode("MemoSq4gqABAXKb96qnH8TysNcWxMyWCqXgDLGmfcHr")
            .into_vec()
            .unwrap();
        for _ in 0..instructions {
            let program = usize::from(take_packet(bytes, &mut at, 1)[0]);
            assert!(program < accounts);
            let count = shortvec(bytes, &mut at);
            take_packet(bytes, &mut at, count);
            let size = shortvec(bytes, &mut at);
            let data = take_packet(bytes, &mut at, size);
            if keys[program * 32..(program + 1) * 32] == memo_program {
                assert_eq!(data.len(), MEMO_LENGTH);
                found = true;
            }
        }
        if versioned {
            assert_eq!(shortvec(bytes, &mut at), 0);
        }
        assert!(found);
        assert_eq!(at, bytes.len());
    }
    #[test]
    fn actual_signed_legacy_v0_packets_fit_and_overflow_at_documented_boundary() {
        // transfer_memo-legacy: 800 bytes.
        let packet=decode_hex(concat!(
            "0133e32e38856d9ab4600eea3041409c43194b05eb5859d281bf74f1e99ac780de6866523f0e8ab57ed00aae7cdee561e79caba3fbd4c7a2e35cd49f",
            "57d34a5a09010003068a88e3dd7409f195fd52db2d3cba5d72ca6709bf1d94121bf3748801b40f6f5cd62ba9c23511df0f38ab5c29baf362aa23ee92",
            "fb763ca2e97962eae77cbfb34dfe44412be60eefe0a18d479a7141acbc126071c03eff8a504ecb3b0781d7df82054a535a992921064d24e87160da38",
            "7c7c35b5ddbc92bb81e41fa8404105448d060606060606060606060606060606060606060606060606060606060606060606ddf6e1ee758fde18425d",
            "bce46ccddab61afc4d83b90d27febdf928d8a18bfc070707070707070707070707070707070707070707070707070707070707070702050401040200",
            "0a0ce0aebb0000000000060300e503656e726f6c3a76323a414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "4141414141414141414141414141414141414141",
        )).unwrap();
        verify_packet(&packet, false);
        assert_eq!(packet.len(), 800);
        assert_eq!(packet.len() <= 1232, true);
        // transfer_memo-v0: 802 bytes.
        let packet=decode_hex(concat!(
            "016bebb14a8f7e8835cff2bd84e6b26b55b87ab407d10d2636b497e806b88f3b9a4bb667f4ceaf7181f5a5c8bae91f308a7f31b7f7b617822b762436",
            "88ed28c50b80010003068a88e3dd7409f195fd52db2d3cba5d72ca6709bf1d94121bf3748801b40f6f5cd62ba9c23511df0f38ab5c29baf362aa23ee",
            "92fb763ca2e97962eae77cbfb34dfe44412be60eefe0a18d479a7141acbc126071c03eff8a504ecb3b0781d7df82054a535a992921064d24e87160da",
            "387c7c35b5ddbc92bb81e41fa8404105448d060606060606060606060606060606060606060606060606060606060606060606ddf6e1ee758fde1842",
            "5dbce46ccddab61afc4d83b90d27febdf928d8a18bfc0707070707070707070707070707070707070707070707070707070707070707020504010402",
            "000a0ce0aebb0000000000060300e503656e726f6c3a76323a4141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "41414141414141414141414141414141414141414100",
        )).unwrap();
        verify_packet(&packet, true);
        assert_eq!(packet.len(), 802);
        assert_eq!(packet.len() <= 1232, true);
        // ata_budget_separate_payer_two_extra_signers-legacy: 1248 bytes.
        let packet=decode_hex(concat!(
            "04dcd713cd8c58cbd9c772f56182ede51807d39f102b213c9376ad0b24197857e9f4e45c07511fa7bb4467a9367db2bd2096b0688a0dee60f8b299cd",
            "d9d2319c06adfd89d73364c8510d9cf8acdc68a74717602a0ad4069564df4ef7b50bae127acc437c5e9ba42ae4d8ea151e793c03dfbdb5a63dbf26a4",
            "eb135d29bc63e0b209b7bd8fd96535c6f14fba0237263d5f991b42cdc35941e518f0f2f8e33b168d13ad0478c7eee06ba25887ed02cf954292d933cf",
            "be5a439d9830ef9161337b0f0f036b336dcc4bf011eba55b033a1f49aab461d2377acf5fa68fdc3e51a863f101191d71072f63e6129ffb76c1bd72dc",
            "3f4ae3365d06a3d2d71ee43c7489a156010403070d8139770ea87d175f56a35466c34c7ecccb8d8a91b4ee37a25df60f5b8fc9b3948a88e3dd7409f1",
            "95fd52db2d3cba5d72ca6709bf1d94121bf3748801b40f6f5cca93ac1705187071d67b83c7ff0efe8108e8ec4530575d7726879333dbdabe7ced4928",
            "c628d1c2c6eae90338905995612959273a5c63f93636c14614ac8737d1d62ba9c23511df0f38ab5c29baf362aa23ee92fb763ca2e97962eae77cbfb3",
            "4dfe44412be60eefe0a18d479a7141acbc126071c03eff8a504ecb3b0781d7df82000000000000000000000000000000000000000000000000000000",
            "00000000000306466fe5211732ffecadba72c39be7bc8ce5bbc5f7126b2c439b3a40000000054a535a992921064d24e87160da387c7c35b5ddbc92bb",
            "81e41fa8404105448d060606060606060606060606060606060606060606060606060606060606060606ddf6e1ee758fde18425dbce46ccddab61afc",
            "4d83b90d27febdf928d8a18bfc6e7a1cdd29b0b78fd13af4c5598feff4ef2a97166e3ca6f2e4fbfccd80505bf18c97258f4e2489f1bb3d1029148e0d",
            "830b5a1399daff1084048e7bd8dbe9f85907070707070707070707070707070707070707070707070707070707070707070507000502e09304000700",
            "0903e8030000000000000c0600050b09060a01010a04040905010a0ce0aebb00000000000608020302e503656e726f6c3a76323a4141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
        )).unwrap();
        verify_packet(&packet, false);
        assert_eq!(packet.len(), 1248);
        assert_eq!(packet.len() <= 1232, false);
        // ata_budget_separate_payer_two_extra_signers-v0: 1250 bytes.
        let packet=decode_hex(concat!(
            "04987442c165be74dc2c9e62169004442f508f471b45d7640e07406981ebfefea96321ded67b1959a7dc8adc8a6e16988ae406f6f294e3bd97b1af91",
            "15bfbd5d043f4ed6f9c1c6fdd458b8ab1af9e27b1339ecbd6c2b4b17022ed98b7074fc5485b4470b071cffff5010e509fd4b0fb8174d2771ac65472d",
            "4c608fd236a1dce20e93223af575a27ec4877b8778be8e71f636c51f7abf203fb6201edb6ad55319ff6411109e6f80566dcd0b778915fa764737cf97",
            "5b7d273cc57d8d28adb7e7e70e68e398086ea74c82bb1e81c81e4736abec2f5227cb863902ee723aed8679a829e5b5472e50a4b54d7b8beab014bfae",
            "d4c690906573cfa6d03508498f44036900800403070d8139770ea87d175f56a35466c34c7ecccb8d8a91b4ee37a25df60f5b8fc9b3948a88e3dd7409",
            "f195fd52db2d3cba5d72ca6709bf1d94121bf3748801b40f6f5cca93ac1705187071d67b83c7ff0efe8108e8ec4530575d7726879333dbdabe7ced49",
            "28c628d1c2c6eae90338905995612959273a5c63f93636c14614ac8737d1d62ba9c23511df0f38ab5c29baf362aa23ee92fb763ca2e97962eae77cbf",
            "b34dfe44412be60eefe0a18d479a7141acbc126071c03eff8a504ecb3b0781d7df820000000000000000000000000000000000000000000000000000",
            "0000000000000306466fe5211732ffecadba72c39be7bc8ce5bbc5f7126b2c439b3a40000000054a535a992921064d24e87160da387c7c35b5ddbc92",
            "bb81e41fa8404105448d060606060606060606060606060606060606060606060606060606060606060606ddf6e1ee758fde18425dbce46ccddab61a",
            "fc4d83b90d27febdf928d8a18bfc6e7a1cdd29b0b78fd13af4c5598feff4ef2a97166e3ca6f2e4fbfccd80505bf18c97258f4e2489f1bb3d1029148e",
            "0d830b5a1399daff1084048e7bd8dbe9f85907070707070707070707070707070707070707070707070707070707070707070507000502e093040007",
            "000903e8030000000000000c0600050b09060a01010a04040905010a0ce0aebb00000000000608020302e503656e726f6c3a76323a41414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141",
            "4141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414100",
        )).unwrap();
        verify_packet(&packet, true);
        assert_eq!(packet.len(), 1250);
        assert_eq!(packet.len() <= 1232, false);
    }
}
