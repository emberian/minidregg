//! Operator-fixed paid agent selectors and exact source signing slots.
//! Mini authors the context, nonce, request digest, and headers. This module
//! only compares them with startup pins before opening any private seed.
#![allow(dead_code)] // Resident listener is enabled only with the reverse v2 reserve client.

use crate::agent_api_wire::Request;
use crate::dispatch_author::{private_signing_key, SignerPin};
use ed25519_dalek::{Signature, Signer, Verifier, VerifyingKey};
use serde::Deserialize;
use serde_json::{json, Value};
use std::io;

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

fn decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn unhex(value: &str) -> io::Result<Vec<u8>> {
    if !value.len().is_multiple_of(2)
        || !value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(invalid("noncanonical source hex"));
    }
    value
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            u8::from_str_radix(
                std::str::from_utf8(pair).map_err(|_| invalid("source hex UTF-8"))?,
                16,
            )
            .map_err(|_| invalid("source hex byte"))
        })
        .collect()
}

fn field<'a>(object: &'a Value, name: &str) -> io::Result<&'a str> {
    object
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("source inspection field absent"))
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct AgentCustody {
    pub protocol: String,
    pub app: String,
    pub app_generation: String,
    pub session: String,
    pub session_generation: String,
    pub subject: String,
    pub ticket_resource: String,
    pub parent_task: String,
    pub parent_generation: String,
    pub purse_task: String,
    pub purse_generation: String,
    pub issue_index: String,
    pub package_manifest: String,
    pub snapshot_manifest: String,
    pub session_observe: String,
    pub manifest_observe: String,
    pub enrollment_observe: String,
    pub parent_capability: String,
    pub parent_observe: String,
    pub purse_capability: String,
    pub purse_observe: String,
    pub payer_subject: String,
    pub reserve_amount: String,
    pub maximum_charge: String,
    pub app_signers: Vec<SignerPin>,
    pub payer_pins: Vec<PayerPin>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct PayerPin {
    pub role: String,
    pub index: String,
    pub key_id: String,
    pub key_epoch: String,
    pub public_key_hex: String,
}

impl AgentCustody {
    pub(crate) fn validate(&self) -> io::Result<()> {
        if self.protocol != "mini-spk-agent-dispatch-custody-v2"
            || ![
                &self.app,
                &self.app_generation,
                &self.session,
                &self.session_generation,
                &self.subject,
                &self.ticket_resource,
                &self.parent_task,
                &self.parent_generation,
                &self.purse_task,
                &self.purse_generation,
                &self.issue_index,
                &self.package_manifest,
                &self.snapshot_manifest,
                &self.session_observe,
                &self.manifest_observe,
                &self.enrollment_observe,
                &self.parent_capability,
                &self.parent_observe,
                &self.purse_capability,
                &self.purse_observe,
                &self.payer_subject,
                &self.reserve_amount,
                &self.maximum_charge,
            ]
            .iter()
            .all(|value| decimal(value))
            || self.parent_task == self.purse_task
            || self.reserve_amount.parse::<u128>().ok().is_none()
            || self.maximum_charge.parse::<u128>().ok().is_none()
            || self.maximum_charge.parse::<u128>().unwrap()
                > self.reserve_amount.parse::<u128>().unwrap()
            || self.app_signers.is_empty()
            || self.payer_pins.is_empty()
        {
            return Err(invalid("fixed agent custody refused"));
        }
        for pins in [&self.app_signers] {
            if pins.len() > 64 {
                return Err(invalid("agent signer count refused"));
            }
            for (index, pin) in pins.iter().enumerate() {
                if ![&pin.role, &pin.index, &pin.key_id, &pin.key_epoch]
                    .iter()
                    .all(|s| decimal(s))
                    || pin.public_key_hex.len() != 64
                    || unhex(&pin.public_key_hex).is_err()
                    || !pin.seed_path.is_absolute()
                    || pins[..index]
                        .iter()
                        .any(|earlier| earlier.role == pin.role && earlier.index == pin.index)
                {
                    return Err(invalid("agent signer pin refused"));
                }
            }
        }
        if self.payer_pins.len() > 64 {
            return Err(invalid("payer signer count refused"));
        }
        for (index, pin) in self.payer_pins.iter().enumerate() {
            if ![&pin.role, &pin.index, &pin.key_id, &pin.key_epoch]
                .iter()
                .all(|s| decimal(s))
                || pin.public_key_hex.len() != 64
                || unhex(&pin.public_key_hex).is_err()
                || self.payer_pins[..index]
                    .iter()
                    .any(|prior| prior.role == pin.role && prior.index == pin.index)
            {
                return Err(invalid("payer signer pin refused"));
            }
        }
        Ok(())
    }

    fn fixed_selectors(&self) -> Value {
        json!({"issueIndex":self.issue_index,"ticketResource":self.ticket_resource,
            "packageManifest":self.package_manifest,"snapshotManifest":self.snapshot_manifest,
            "sessionObserve":self.session_observe,"manifestObserve":self.manifest_observe,
            "enrollmentObserve":self.enrollment_observe,"parentTask":self.parent_task,
            "parentCapability":self.parent_capability,"parentObserve":self.parent_observe,
            "purseTask":self.purse_task,"purseCapability":self.purse_capability,
            "purseObserve":self.purse_observe,"payerSubject":self.payer_subject,
            "reserveAmount":self.reserve_amount,"maximumCharge":self.maximum_charge})
    }

    pub(crate) fn reserve_request(
        &self,
        request: &Request,
        reserve_id: &str,
        app_path: &str,
    ) -> io::Result<Value> {
        self.validate()?;
        if !decimal(reserve_id) {
            return Err(invalid("reserve operation ID refused"));
        }
        let Request::Dispatch {
            operation_id,
            method,
            query,
            headers,
            body_hex,
            ..
        } = request
        else {
            return Err(invalid("dispatch request required"));
        };
        if !decimal(operation_id) {
            return Err(invalid("HTTP operation ID refused"));
        }
        let projected_headers: Vec<_> = headers.iter().map(|header| json!({
            "nameHex":hex(header.name.as_bytes()),"valueHex":hex(header.value.as_bytes()),"generated":false
        })).collect();
        Ok(
            json!({"base":{"issueIndex":self.issue_index,"ticketResource":self.ticket_resource,
            "packageManifest":self.package_manifest,"snapshotManifest":self.snapshot_manifest,
            "sessionObserveCapability":self.session_observe,
            "manifestObserveCapability":self.manifest_observe,
            "enrollmentObserveCapability":self.enrollment_observe,
            "http":{"operationId":operation_id,"methodHex":hex(method.as_bytes()),
                "pathHex":hex(app_path.as_bytes()),"queryHex":hex(query.as_bytes()),
                "headers":projected_headers,"bodyHex":body_hex}},
            "parentTask":self.parent_task,"parentCapability":self.parent_capability,
            "parentObserve":self.parent_observe,"purseTask":self.purse_task,
            "purseCapability":self.purse_capability,"purseObserve":self.purse_observe,
            "payerSubject":self.payer_subject,"reserveAmount":self.reserve_amount,
            "maximumCharge":self.maximum_charge,"reserveOperationId":reserve_id}),
        )
    }

    pub(crate) fn sign_slots(
        &self,
        inspection: &Value,
        plan: &[u8],
        slots_key: &str,
        pins: &[SignerPin],
    ) -> io::Result<Value> {
        if field(inspection, "canonicalPlanHex")? != hex(plan)
            || inspection.get("fixedSelectors") != Some(&self.fixed_selectors())
            || field(inspection, "type")? != "application-agent-paid-dispatch-plan-v2"
            || unhex(field(inspection, "compactSelectorRequestHex")?)?.is_empty()
            || unhex(field(inspection, "canonicalHttpHex")?)?.is_empty()
        {
            return Err(invalid("source agent plan differs from fixed request"));
        }
        let slots = inspection
            .get(slots_key)
            .and_then(Value::as_array)
            .ok_or_else(|| invalid("source agent signing slots absent"))?;
        if slots.len() != pins.len() {
            return Err(invalid("source agent signer slot count drift"));
        }
        let mut signatures = Vec::with_capacity(slots.len());
        for (slot, pin) in slots.iter().zip(pins) {
            let signing = slot
                .get("signing")
                .ok_or_else(|| invalid("source signing header absent"))?;
            let header_hex = field(slot, "headerHex")?;
            if field(slot, "role")? != pin.role
                || field(slot, "index")? != pin.index
                || signing.get("decoded").and_then(Value::as_bool) != Some(true)
                || field(signing, "keyId")? != pin.key_id
                || field(signing, "keyEpoch")? != pin.key_epoch
                || field(signing, "algorithm")? != "1"
            {
                return Err(invalid("source signing header differs from fixed key"));
            }
            let header = unhex(header_hex)?;
            if header.is_empty() || header.len() > 65_536 {
                return Err(invalid("source signing header bound"));
            }
            let key = private_signing_key(&pin.seed_path)?;
            if hex(&key.verifying_key().to_bytes()) != pin.public_key_hex {
                return Err(invalid("agent seed differs from enrolled public key"));
            }
            signatures.push(Value::String(hex(&key.sign(&header).to_bytes())));
        }
        Ok(Value::Array(signatures))
    }

    /// Controller alone signs the fresh purse no-op. The resident checks each
    /// detached signature against its fixed enrolled public key and Mini's
    /// exact source-inspected header before handing it to op49.
    pub(crate) fn verify_payer_slots(
        &self,
        inspection: &Value,
        plan: &[u8],
        signatures: &Value,
    ) -> io::Result<()> {
        if field(inspection, "canonicalPlanHex")? != hex(plan)
            || inspection.get("fixedSelectors") != Some(&self.fixed_selectors())
            || field(inspection, "type")? != "application-agent-paid-dispatch-plan-v2"
            || unhex(field(inspection, "compactSelectorRequestHex")?)?.is_empty()
            || unhex(field(inspection, "canonicalHttpHex")?)?.is_empty()
        {
            return Err(invalid("payer plan differs from fixed request"));
        }
        let slots = inspection
            .get("payerSlots")
            .and_then(Value::as_array)
            .ok_or_else(|| invalid("payer slots absent"))?;
        let signatures = signatures
            .as_array()
            .ok_or_else(|| invalid("payer signatures not array"))?;
        if slots.len() != self.payer_pins.len() || signatures.len() != slots.len() {
            return Err(invalid("payer slot/signature count drift"));
        }
        for ((slot, pin), signature) in slots.iter().zip(&self.payer_pins).zip(signatures) {
            let signing = slot
                .get("signing")
                .ok_or_else(|| invalid("payer signing absent"))?;
            if field(slot, "role")? != pin.role
                || field(slot, "index")? != pin.index
                || signing.get("decoded").and_then(Value::as_bool) != Some(true)
                || field(signing, "keyId")? != pin.key_id
                || field(signing, "keyEpoch")? != pin.key_epoch
                || field(signing, "algorithm")? != "1"
            {
                return Err(invalid("payer source header differs from fixed pin"));
            }
            let header = unhex(field(slot, "headerHex")?)?;
            if header.is_empty() || header.len() > 65_536 {
                return Err(invalid("payer header bound"));
            }
            let key: [u8; 32] = unhex(&pin.public_key_hex)?
                .try_into()
                .map_err(|_| invalid("payer public key width"))?;
            let key =
                VerifyingKey::from_bytes(&key).map_err(|_| invalid("payer public key invalid"))?;
            let signature = signature
                .as_str()
                .ok_or_else(|| invalid("payer signature not hex"))?;
            let signature = Signature::from_slice(&unhex(signature)?)
                .map_err(|_| invalid("payer signature width"))?;
            key.verify(&header, &signature)
                .map_err(|_| invalid("payer signature does not approve header"))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn controller_payer_signature_must_cover_exact_current_source_header() {
        let key = ed25519_dalek::SigningKey::from_bytes(&[7u8; 32]);
        let custody: AgentCustody = serde_json::from_value(json!({
            "protocol":"mini-spk-agent-dispatch-custody-v2", "app":"6100", "appGeneration":"2",
            "session":"6209","sessionGeneration":"3","subject":"8","ticketResource":"6408",
            "parentTask":"6500","parentGeneration":"4","purseTask":"6600","purseGeneration":"5",
            "issueIndex":"1","packageManifest":"6101","snapshotManifest":"6102",
            "sessionObserve":"11","manifestObserve":"12","enrollmentObserve":"13",
            "parentCapability":"14","parentObserve":"15","purseCapability":"16",
            "purseObserve":"17","payerSubject":"8","reserveAmount":"20","maximumCharge":"10",
            "appSigners":[],"payerPins":[{"role":"8","index":"0","keyId":"18",
                "keyEpoch":"1","publicKeyHex":hex(&key.verifying_key().to_bytes())}]
        }))
        .unwrap();
        let header = b"Mini source payer header";
        let signature = key.sign(header);
        let mut inspection = json!({"type":"application-agent-paid-dispatch-plan-v2",
            "canonicalPlanHex":"aa","compactSelectorRequestHex":"bb","canonicalHttpHex":"cc",
            "fixedSelectors":custody.fixed_selectors(),
            "payerSlots":[{"role":"8","index":"0","headerHex":hex(header),
                "signing":{"decoded":true,"keyId":"18","keyEpoch":"1","algorithm":"1"}}]});
        let signatures = json!([hex(&signature.to_bytes())]);
        assert!(custody
            .verify_payer_slots(&inspection, &[0xaa], &signatures)
            .is_ok());
        inspection["payerSlots"][0]["headerHex"] = json!(hex(b"different header"));
        assert!(custody
            .verify_payer_slots(&inspection, &[0xaa], &signatures)
            .is_err());
    }
}
