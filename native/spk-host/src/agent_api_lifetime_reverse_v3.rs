//! One-way controller reserve bridge for lifetime dispatch. The controller
//! owns the purse key; the resident re-inspects its exact source plan before
//! accepting per-operation current claims. No reply is a delivery permit.
#![allow(dead_code)] // The shared v3 listener is enabled in a later cut.

use crate::agent_api_lifetime_v3::{
    match_reserve_plan, operation_fingerprint, CurrentClaims, LifetimeBinding, ReceiptPin,
};
use crate::agent_api_native::ReverseCustodyClient;
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::io;
use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

const MAX_SOURCE_FRAME: usize = 12_102_759;

fn refused(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn index_precedes_count(index: &str, count: &str) -> bool {
    if !decimal(index) || !decimal(count) {
        return false;
    }
    let mut digits = index.as_bytes().to_vec();
    let mut carry = true;
    for digit in digits.iter_mut().rev() {
        if !carry {
            break;
        }
        if *digit == b'9' {
            *digit = b'0';
        } else {
            *digit += 1;
            carry = false;
        }
    }
    if carry {
        digits.insert(0, b'1');
    }
    digits == count.as_bytes()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn unhex(value: &str) -> io::Result<Vec<u8>> {
    if !value.len().is_multiple_of(2)
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        || value.len() > MAX_SOURCE_FRAME * 2
    {
        return Err(refused("lifetime source frame hex refused"));
    }
    value
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            u8::from_str_radix(
                std::str::from_utf8(pair).map_err(|_| refused("lifetime hex UTF-8"))?,
                16,
            )
            .map_err(|_| refused("lifetime hex byte"))
        })
        .collect()
}

fn field<'a>(value: &'a Value, name: &str) -> io::Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| refused("lifetime source inspection field absent"))
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ReservedReply {
    #[serde(rename = "type")]
    kind: String,
    attempt_id: String,
    http_operation_id: String,
    binding_sha256: String,
    operation_fingerprint: String,
    current_claims: CurrentClaims,
    reserve_operation_id: String,
    fixed_request_hex: String,
    reserve_plan_hex: String,
    context_hex: String,
    reserve_index: String,
    reserve_receipt: ReceiptPin,
    effective_worker_wall_seconds: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct PayerReply {
    #[serde(rename = "type")]
    kind: String,
    attempt_id: String,
    binding_sha256: String,
    operation_fingerprint: String,
    plan_sha256: String,
    signed_post_reserve_purse_physical_root: String,
    signatures: Vec<String>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SendMarkedReply {
    #[serde(rename = "type")]
    kind: String,
    attempt_id: String,
    binding_sha256: String,
    operation_fingerprint: String,
    request_sha256: String,
    ingress_sha256: String,
    committed_frame_sha256: String,
    receipt: ReceiptPin,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SettledReply {
    #[serde(rename = "type")]
    kind: String,
    attempt_id: String,
    response_sha256: String,
    charge: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SettlementInspection {
    #[serde(rename = "type")]
    kind: String,
    attempt_id: Option<String>,
    binding_sha256: Option<String>,
    operation_fingerprint: Option<String>,
    response_sha256: Option<String>,
    committed_receipt: Option<ReceiptPin>,
}

pub(crate) struct VerifiedSettlementV3 {
    response_sha256: String,
    committed_receipt: ReceiptPin,
}

impl VerifiedSettlementV3 {
    pub(crate) fn response_sha256(&self) -> &str {
        &self.response_sha256
    }

    pub(crate) fn committed_receipt(&self) -> &ReceiptPin {
        &self.committed_receipt
    }

    #[cfg(test)]
    pub(crate) fn test_only() -> Self {
        Self {
            response_sha256: "c".repeat(64),
            committed_receipt: ReceiptPin {
                transaction_id: "2".repeat(64),
                event_id: "3".repeat(64),
                accepted_count: "13".into(),
                world_root: "14".into(),
            },
        }
    }

    #[cfg(test)]
    pub(crate) fn test_only_wrong_receipt() -> Self {
        let mut witness = Self::test_only();
        witness.committed_receipt.event_id = "4".repeat(64);
        witness
    }
}

pub(crate) struct PayerSignaturesV3 {
    pub signatures: Vec<String>,
    pub signed_post_reserve_purse_physical_root: String,
}

pub(crate) struct RetainedReserveV3 {
    pub attempt_id: String,
    pub http_operation_id: String,
    pub binding_sha256: String,
    pub operation_fingerprint: String,
    pub current_claims: CurrentClaims,
    pub reserve_operation_id: String,
    pub reserve_index: String,
    pub reserve_receipt: ReceiptPin,
    pub request_bytes: Vec<u8>,
    pub plan_bytes: Vec<u8>,
    pub context_bytes: Vec<u8>,
    pub request_sha256: String,
    pub effective_worker_wall_seconds: String,
}

pub(crate) struct LifetimeReverseClient {
    transport: ReverseCustodyClient,
}

pub(crate) struct ReserveV3Input<'a> {
    pub operator: &'a PrivateOperator,
    pub binding: &'a LifetimeBinding,
    pub forward_operation_id: &'a str,
    pub fixed_request: &'a Value,
    pub decoded_http: &'a Value,
    pub attempt_dir: &'a Path,
    pub deadline: Instant,
    pub worker_wall_seconds: u64,
}

impl LifetimeReverseClient {
    pub(crate) fn new(transport: ReverseCustodyClient) -> Self {
        Self { transport }
    }

    /// Receipt-only controller inspection. This can establish settlement of
    /// an already executed fd3 response after an ACK loss; it never settles,
    /// marks a send, or authorizes another fd3 call.
    pub(crate) fn inspect_settlement(
        &self,
        attempt_id: &str,
        binding_sha256: &str,
        operation_fingerprint: &str,
        cancelled: &AtomicBool,
        deadline: Instant,
    ) -> io::Result<Option<VerifiedSettlementV3>> {
        let response = self.transport.exchange_until(
            &json!({"type":"inspect-settlement-v3", "attempt_id":attempt_id,
                "binding_sha256":binding_sha256,
                "operation_fingerprint":operation_fingerprint}),
            cancelled,
            deadline,
        )?;
        let reply: SettlementInspection = serde_json::from_value(response)?;
        if reply.kind == "dispatch-settlement-uncertain-v3" {
            if reply.response_sha256.is_some()
                || reply.committed_receipt.is_some()
                || reply
                    .attempt_id
                    .as_deref()
                    .is_some_and(|value| value != attempt_id)
                || reply
                    .binding_sha256
                    .as_deref()
                    .is_some_and(|value| value != binding_sha256)
                || reply
                    .operation_fingerprint
                    .as_deref()
                    .is_some_and(|value| value != operation_fingerprint)
            {
                return Err(refused("uncertain settlement carried a definite result"));
            }
            return Ok(None);
        }
        if reply.kind != "settled-v3"
            || reply.attempt_id.as_deref() != Some(attempt_id)
            || reply.binding_sha256.as_deref() != Some(binding_sha256)
            || reply.operation_fingerprint.as_deref() != Some(operation_fingerprint)
        {
            return Err(refused("lifetime settlement inspection identity drift"));
        }
        let sha = reply
            .response_sha256
            .ok_or_else(|| refused("lifetime settlement digest absent"))?;
        if sha.len() != 64
            || !sha
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(refused("lifetime settlement digest refused"));
        }
        let receipt = reply
            .committed_receipt
            .ok_or_else(|| refused("lifetime settlement receipt absent"))?;
        receipt.validate()?;
        Ok(Some(VerifiedSettlementV3 {
            response_sha256: sha,
            committed_receipt: receipt,
        }))
    }

    /// Controller must durably join the exact fresh op76 payload and ingress
    /// before a resident may queue one fd3 call. A lost ACK is uncertainty.
    pub(crate) fn mark_send_once(
        &self,
        reserve: &RetainedReserveV3,
        ingress: &[u8],
        committed_frame: &[u8],
        receipt: &ReceiptPin,
        cancelled: &AtomicBool,
        deadline: Instant,
    ) -> io::Result<()> {
        receipt.validate()?;
        if ingress.is_empty() || committed_frame.is_empty() {
            return Err(refused("lifetime send marker frames absent"));
        }
        let ingress_sha256 = hex(&Sha256::digest(ingress));
        let committed_frame_sha256 = hex(&Sha256::digest(committed_frame));
        let response = self.transport.exchange_until(
            &json!({
                "type":"mark-send-v3",
                "attempt_id":reserve.attempt_id,
                "binding_sha256":reserve.binding_sha256,
                "operation_fingerprint":reserve.operation_fingerprint,
                "request_sha256":reserve.request_sha256,
                "ingress_hex":hex(ingress),
                "committed_frame_hex":hex(committed_frame),
                "receipt":receipt,
            }),
            cancelled,
            deadline,
        )?;
        let reply: SendMarkedReply = serde_json::from_value(response)?;
        if reply.kind != "dispatch-send-marked-v3"
            || reply.attempt_id != reserve.attempt_id
            || reply.binding_sha256 != reserve.binding_sha256
            || reply.operation_fingerprint != reserve.operation_fingerprint
            || reply.request_sha256 != reserve.request_sha256
            || reply.ingress_sha256 != ingress_sha256
            || reply.committed_frame_sha256 != committed_frame_sha256
            || reply.receipt != *receipt
        {
            return Err(refused(
                "lifetime durable send marker differs from fresh permit",
            ));
        }
        Ok(())
    }

    /// A definite fd3 result is chargeable only after the controller has
    /// durably settled this exact response hash. No reply means no definite
    /// forward response, even though the app command may have completed.
    pub(crate) fn settle_definite_once(
        &self,
        reserve: &RetainedReserveV3,
        response_sha256: &str,
        cancelled: &AtomicBool,
        deadline: Instant,
    ) -> io::Result<()> {
        if response_sha256.len() != 64
            || !response_sha256
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(refused("lifetime definite response digest refused"));
        }
        let response = self.transport.exchange_until(
            &json!({"type":"settle-definite","attempt_id":reserve.attempt_id,
                "response_sha256":response_sha256}),
            cancelled,
            deadline,
        )?;
        let reply: SettledReply = serde_json::from_value(response)?;
        if reply.kind != "dispatch-settled-v1"
            || reply.attempt_id != reserve.attempt_id
            || reply.response_sha256 != response_sha256
            || !decimal(&reply.charge)
        {
            return Err(refused("lifetime definite settlement drift"));
        }
        Ok(())
    }

    /// The controller signs only its separately held payer slots. App and
    /// grant slots stay with the resident's fixed participant custodian.
    pub(crate) fn sign_payer_once(
        &self,
        reserve: &RetainedReserveV3,
        paid_plan: &[u8],
        source_inspection: &Value,
        cancelled: &AtomicBool,
        deadline: Instant,
    ) -> io::Result<PayerSignaturesV3> {
        if paid_plan.is_empty() || paid_plan.len() > MAX_SOURCE_FRAME {
            return Err(refused("lifetime paid plan bound refused"));
        }
        let plan_sha256 = hex(&Sha256::digest(paid_plan));
        let response = self.transport.exchange_until(
            &json!({"type":"sign-payer-v3",
                "route_name":self.transport.route_name,
                "forward_operation_id":reserve.http_operation_id,
                "attempt_id":reserve.attempt_id,
                "paid_plan_hex":hex(paid_plan),
                "source_inspection_json":source_inspection,
                "operation_fingerprint":reserve.operation_fingerprint}),
            cancelled,
            deadline,
        )?;
        let reply: PayerReply = serde_json::from_value(response)?;
        if reply.kind != "payer-signatures-v3"
            || reply.attempt_id != reserve.attempt_id
            || reply.binding_sha256 != reserve.binding_sha256
            || reply.operation_fingerprint != reserve.operation_fingerprint
            || reply.plan_sha256 != plan_sha256
            || !decimal(&reply.signed_post_reserve_purse_physical_root)
            || reply.signatures.is_empty()
            || reply.signatures.len() > 64
            || reply.signatures.iter().any(|signature| {
                signature.len() != 128
                    || !signature
                        .bytes()
                        .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
            })
        {
            return Err(refused("lifetime payer signatures differ from exact plan"));
        }
        Ok(PayerSignaturesV3 {
            signatures: reply.signatures,
            signed_post_reserve_purse_physical_root: reply.signed_post_reserve_purse_physical_root,
        })
    }

    /// The only reserve submit. On a lost reply, inspect-v3 is read-only;
    /// failure to recover the exact confirmed reserve remains uncertainty.
    pub(crate) fn reserve_once(
        &self,
        input: ReserveV3Input<'_>,
        cancelled: &AtomicBool,
    ) -> io::Result<RetainedReserveV3> {
        let ReserveV3Input {
            operator,
            binding,
            forward_operation_id,
            fixed_request,
            decoded_http,
            attempt_dir,
            deadline,
            worker_wall_seconds,
        } = input;
        if !decimal(forward_operation_id) || cancelled.load(Ordering::Acquire) {
            return Err(refused("lifetime forward operation refused"));
        }
        binding.validate()?;
        private_dir(attempt_dir)?;
        let binding_sha256 = binding.fingerprint()?;
        let request = json!({
            "type":"reserve-v3",
            "route_name":self.transport.route_name,
            "forward_operation_id":forward_operation_id,
            "binding_sha256":binding_sha256,
            "worker_wall_seconds":worker_wall_seconds,
            "fixed_request":fixed_request,
        });
        let reply = match self.transport.exchange_until(&request, cancelled, deadline) {
            Ok(reply) => reply,
            Err(error) => {
                if cancelled.load(Ordering::Acquire) {
                    return Err(error);
                }
                self.transport
                    .exchange_until(
                        &json!({"type":"inspect-v3",
                            "route_name":self.transport.route_name,
                            "forward_operation_id":forward_operation_id}),
                        cancelled,
                        deadline,
                    )
                    .map_err(|_| error)?
            }
        };
        self.accept_reserved_reply(
            ReserveV3Input {
                operator,
                binding,
                forward_operation_id,
                fixed_request,
                decoded_http,
                attempt_dir,
                deadline,
                worker_wall_seconds,
            },
            reply,
        )
    }

    fn accept_reserved_reply(
        &self,
        input: ReserveV3Input<'_>,
        reply: Value,
    ) -> io::Result<RetainedReserveV3> {
        let ReserveV3Input {
            operator,
            binding,
            forward_operation_id,
            decoded_http,
            attempt_dir,
            worker_wall_seconds,
            ..
        } = input;
        let reply: ReservedReply = serde_json::from_value(reply)?;
        if reply.kind != "dispatch-reserved-v3"
            || reply.http_operation_id != forward_operation_id
            || reply.binding_sha256 != binding.fingerprint()?
            || reply.effective_worker_wall_seconds != worker_wall_seconds.to_string()
            || ![
                &reply.attempt_id,
                &reply.reserve_operation_id,
                &reply.reserve_index,
                &reply.reserve_receipt.transaction_id,
                &reply.reserve_receipt.event_id,
                &reply.reserve_receipt.accepted_count,
                &reply.reserve_receipt.world_root,
            ]
            .into_iter()
            .all(|value| decimal(value))
            || !index_precedes_count(&reply.reserve_index, &reply.reserve_receipt.accepted_count)
        {
            return Err(refused("lifetime reserve reply coordinate drift"));
        }
        let request_bytes = unhex(&reply.fixed_request_hex)?;
        let plan_bytes = unhex(&reply.reserve_plan_hex)?;
        let context_bytes = unhex(&reply.context_hex)?;
        if request_bytes.is_empty() || plan_bytes.is_empty() || context_bytes.is_empty() {
            return Err(refused("lifetime reserve reply frame absent"));
        }
        let request_path = write_new(attempt_dir, "reserve-request-v3.bin", &request_bytes)?;
        let plan_path = write_new(attempt_dir, "reserve-plan-v3.bin", &plan_bytes)?;
        let inspected_request = operator.tool(
            "inspect",
            "application-agent-lifetime-reserve-request",
            &request_path,
            &attempt_dir.join("reserve-request-v3.json"),
        )?;
        let inspected_plan = operator.tool(
            "inspect",
            "application-agent-lifetime-reserve-plan",
            &plan_path,
            &attempt_dir.join("reserve-plan-v3.json"),
        )?;
        let request_view: Value = serde_json::from_slice(&inspected_request)?;
        let plan_view: Value = serde_json::from_slice(&inspected_plan)?;
        if field(&request_view, "canonicalRequestHex")? != reply.fixed_request_hex
            || field(&plan_view, "canonicalPlanHex")? != reply.reserve_plan_hex
            || field(
                plan_view
                    .get("context")
                    .ok_or_else(|| refused("lifetime reserve context absent"))?,
                "canonicalHex",
            )? != reply.context_hex
        {
            return Err(refused("lifetime source reserve frame drift"));
        }
        match_reserve_plan(
            binding,
            &reply.current_claims,
            &request_view,
            &plan_view,
            decoded_http,
        )?;
        let canonical_http = unhex(field(&plan_view, "canonicalHttpHex")?)?;
        let request_sha256 = hex(&Sha256::digest(&canonical_http));
        let operation_fingerprint = operation_fingerprint(
            binding,
            &reply.current_claims,
            forward_operation_id,
            &request_sha256,
        )?;
        if reply.operation_fingerprint != operation_fingerprint {
            return Err(refused("lifetime operation fingerprint drift"));
        }
        write_new(
            attempt_dir,
            "reserve-verified-v3.json",
            &serde_json::to_vec(&json!({
                "protocol":"mini-spk-lifetime-reserve-verified-v3",
                "attemptId":reply.attempt_id,
                "httpOperationId":reply.http_operation_id,
                "bindingSha256":reply.binding_sha256,
                "operationFingerprint":operation_fingerprint,
                "currentClaims":reply.current_claims,
                "reserveOperationId":reply.reserve_operation_id,
                "reserveIndex":reply.reserve_index,
                "reserveReceipt":reply.reserve_receipt,
                "effectiveWorkerWallSeconds":reply.effective_worker_wall_seconds,
                "requestSha256":request_sha256,
                "fixedRequestSha256":hex(&Sha256::digest(&request_bytes)),
                "reservePlanSha256":hex(&Sha256::digest(&plan_bytes)),
                "contextSha256":hex(&Sha256::digest(&context_bytes)),
            }))?,
        )?;
        Ok(RetainedReserveV3 {
            attempt_id: reply.attempt_id,
            http_operation_id: reply.http_operation_id,
            binding_sha256: reply.binding_sha256,
            operation_fingerprint,
            current_claims: reply.current_claims,
            reserve_operation_id: reply.reserve_operation_id,
            reserve_index: reply.reserve_index,
            reserve_receipt: reply.reserve_receipt,
            request_bytes,
            plan_bytes,
            context_bytes,
            request_sha256,
            effective_worker_wall_seconds: reply.effective_worker_wall_seconds,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::{self, DirBuilder};
    use std::io::{Read, Write};
    use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
    use std::os::unix::net::UnixListener;
    use std::thread;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn reserve_index_matches_full_decimal_receipt_count() {
        assert!(index_precedes_count("0", "1"));
        assert!(index_precedes_count(
            "340282366920938463463374607431768211455",
            "340282366920938463463374607431768211456"
        ));
        assert!(!index_precedes_count("4", "4"));
        assert!(!index_precedes_count("4", "6"));
        assert!(!index_precedes_count("04", "5"));
    }

    #[test]
    fn reverse_transport_accepts_bounded_double_frame_reply() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "mini-lifetime-reverse-{}-{nonce}",
            std::process::id()
        ));
        DirBuilder::new().mode(0o700).create(&directory).unwrap();
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
        let socket = directory.join("reverse.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        let server = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut length = [0u8; 4];
            stream.read_exact(&mut length).unwrap();
            let mut request = vec![0u8; u32::from_be_bytes(length) as usize];
            stream.read_exact(&mut request).unwrap();
            let request: Value = serde_json::from_slice(&request).unwrap();
            assert_eq!(request["type"], "inspect-v3");
            let response = serde_json::to_vec(&json!({
                "type":"dispatch-reserved-v3",
                "fixedRequestHex":"ab".repeat(65_536),
                "reservePlanHex":"cd".repeat(65_536),
                "contextHex":"ef",
            }))
            .unwrap();
            assert!(response.len() > 262_144 && response.len() < 1_048_576);
            stream
                .write_all(&(response.len() as u32).to_be_bytes())
                .unwrap();
            stream.write_all(&response).unwrap();
        });
        let client = ReverseCustodyClient::new(
            socket.clone(),
            unsafe { libc::geteuid() },
            "workroom-app".into(),
        )
        .unwrap();
        let reply = client
            .exchange(&json!({"type":"inspect-v3"}), &AtomicBool::new(false))
            .unwrap();
        assert_eq!(reply["fixedRequestHex"].as_str().unwrap().len(), 131_072);
        server.join().unwrap();
        fs::remove_file(socket).unwrap();
        fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn payer_callback_preserves_all_ordered_slots_and_operation_pins() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "mini-lifetime-payer-{}-{nonce}",
            std::process::id()
        ));
        DirBuilder::new().mode(0o700).create(&directory).unwrap();
        let socket = directory.join("reverse.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        let server = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut length = [0u8; 4];
            stream.read_exact(&mut length).unwrap();
            let mut request = vec![0u8; u32::from_be_bytes(length) as usize];
            stream.read_exact(&mut request).unwrap();
            let request: Value = serde_json::from_slice(&request).unwrap();
            assert_eq!(request["type"], "sign-payer-v3");
            assert_eq!(request["operation_fingerprint"], "b".repeat(64));
            assert_eq!(request["paid_plan_hex"], "0102");
            let response = serde_json::to_vec(&json!({
                "type":"payer-signatures-v3","attemptId":"41",
                "bindingSha256":"a".repeat(64),
                "operationFingerprint":"b".repeat(64),
                "planSha256":hex(&Sha256::digest([1, 2])),
                "signedPostReservePursePhysicalRoot":"204",
                "signatures":["c".repeat(128),"d".repeat(128),"e".repeat(128)],
            }))
            .unwrap();
            stream
                .write_all(&(response.len() as u32).to_be_bytes())
                .unwrap();
            stream.write_all(&response).unwrap();
        });
        let transport = ReverseCustodyClient::new(
            socket.clone(),
            unsafe { libc::geteuid() },
            "workroom-app".into(),
        )
        .unwrap();
        let client = LifetimeReverseClient::new(transport);
        let reserve = RetainedReserveV3 {
            attempt_id: "41".into(),
            http_operation_id: "17".into(),
            binding_sha256: "a".repeat(64),
            operation_fingerprint: "b".repeat(64),
            current_claims: CurrentClaims {
                app_generation: "1".into(),
                session_generation: "1".into(),
                parent_generation: "1".into(),
                purse_generation: "1".into(),
                app_physical_root: "1".into(),
                session_physical_root: "1".into(),
                parent_physical_root: "1".into(),
                purse_physical_root: "1".into(),
            },
            reserve_operation_id: "18".into(),
            reserve_index: "4".into(),
            reserve_receipt: ReceiptPin {
                transaction_id: "1".into(),
                event_id: "2".into(),
                accepted_count: "5".into(),
                world_root: "3".into(),
            },
            request_bytes: vec![1],
            plan_bytes: vec![2],
            context_bytes: vec![3],
            request_sha256: "e".repeat(64),
            effective_worker_wall_seconds: "1500".into(),
        };
        let signatures = client
            .sign_payer_once(
                &reserve,
                &[1, 2],
                &json!({"type":"plan"}),
                &AtomicBool::new(false),
                Instant::now() + std::time::Duration::from_secs(30),
            )
            .unwrap();
        assert_eq!(
            signatures.signatures,
            vec!["c".repeat(128), "d".repeat(128), "e".repeat(128)]
        );
        assert_eq!(signatures.signed_post_reserve_purse_physical_root, "204");
        server.join().unwrap();
        fs::remove_file(socket).unwrap();
        fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn initial_reserved_reply_requires_exact_source_plan_bytes() {
        let response = json!({
            "type":"dispatch-reserved-v3", "attemptId":"41", "httpOperationId":"17",
            "bindingSha256":"a".repeat(64),
            "operationFingerprint":"b".repeat(64),
            "currentClaims":{
                "appGeneration":"1","sessionGeneration":"2",
                "parentGeneration":"3","purseGeneration":"4",
                "appPhysicalRoot":"5","sessionPhysicalRoot":"6",
                "parentPhysicalRoot":"7","pursePhysicalRoot":"8"
            },
            "reserveOperationId":"19", "fixedRequestHex":"01",
            "reservePlanHex":"02", "contextHex":"03", "reserveIndex":"4",
            "effectiveWorkerWallSeconds":"1500",
            "reserveReceipt":{"transactionId":"9","eventId":"10",
                "acceptedCount":"5","worldRoot":"11"}
        });
        let parsed: ReservedReply = serde_json::from_value(response.clone()).unwrap();
        assert_eq!(parsed.reserve_plan_hex, "02");
        let mut missing = response;
        missing.as_object_mut().unwrap().remove("reservePlanHex");
        assert!(serde_json::from_value::<ReservedReply>(missing).is_err());
    }

    #[test]
    fn mark_send_and_settle_use_distinct_durable_controller_acks() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "mini-lifetime-mark-settle-{}-{nonce}",
            std::process::id()
        ));
        DirBuilder::new().mode(0o700).create(&directory).unwrap();
        let socket = directory.join("reverse.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        let receipt = ReceiptPin {
            transaction_id: "11".into(),
            event_id: "12".into(),
            accepted_count: "13".into(),
            world_root: "14".into(),
        };
        let expected_receipt = receipt.clone();
        let server = thread::spawn(move || {
            for expected in ["mark-send-v3", "settle-definite"] {
                let (mut stream, _) = listener.accept().unwrap();
                let mut length = [0u8; 4];
                stream.read_exact(&mut length).unwrap();
                let mut request = vec![0u8; u32::from_be_bytes(length) as usize];
                stream.read_exact(&mut request).unwrap();
                let request: Value = serde_json::from_slice(&request).unwrap();
                assert_eq!(request["type"], expected);
                assert_eq!(request["attempt_id"], "41");
                let response = if expected == "mark-send-v3" {
                    assert_eq!(request["ingress_hex"], "0102");
                    assert_eq!(request["committed_frame_hex"], "0304");
                    assert_eq!(request["receipt"], json!(expected_receipt));
                    json!({"type":"dispatch-send-marked-v3",
                        "attemptId":"41", "bindingSha256":"a".repeat(64),
                        "operationFingerprint":"b".repeat(64),
                        "requestSha256":"c".repeat(64),
                        "ingressSha256":hex(&Sha256::digest([1,2])),
                        "committedFrameSha256":hex(&Sha256::digest([3,4])),
                        "receipt":expected_receipt})
                } else {
                    assert_eq!(request["response_sha256"], "d".repeat(64));
                    json!({"type":"dispatch-settled-v1", "attemptId":"41",
                        "responseSha256":"d".repeat(64), "charge":"3"})
                };
                let bytes = serde_json::to_vec(&response).unwrap();
                stream
                    .write_all(&(bytes.len() as u32).to_be_bytes())
                    .unwrap();
                stream.write_all(&bytes).unwrap();
            }
        });
        let client = LifetimeReverseClient::new(
            ReverseCustodyClient::new(
                socket.clone(),
                unsafe { libc::geteuid() },
                "workroom-app".into(),
            )
            .unwrap(),
        );
        let reserve = RetainedReserveV3 {
            attempt_id: "41".into(),
            http_operation_id: "17".into(),
            binding_sha256: "a".repeat(64),
            operation_fingerprint: "b".repeat(64),
            current_claims: CurrentClaims {
                app_generation: "1".into(),
                session_generation: "1".into(),
                parent_generation: "1".into(),
                purse_generation: "1".into(),
                app_physical_root: "1".into(),
                session_physical_root: "1".into(),
                parent_physical_root: "1".into(),
                purse_physical_root: "1".into(),
            },
            reserve_operation_id: "18".into(),
            reserve_index: "4".into(),
            reserve_receipt: receipt.clone(),
            request_bytes: vec![1],
            plan_bytes: vec![2],
            context_bytes: vec![3],
            request_sha256: "c".repeat(64),
            effective_worker_wall_seconds: "1500".into(),
        };
        client
            .mark_send_once(
                &reserve,
                &[1, 2],
                &[3, 4],
                &receipt,
                &AtomicBool::new(false),
                Instant::now() + std::time::Duration::from_secs(30),
            )
            .unwrap();
        client
            .settle_definite_once(
                &reserve,
                &"d".repeat(64),
                &AtomicBool::new(false),
                Instant::now() + std::time::Duration::from_secs(30),
            )
            .unwrap();
        server.join().unwrap();
        fs::remove_file(socket).unwrap();
        fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn settlement_inspection_is_read_only_and_exactly_pinned() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "mini-lifetime-inspect-settlement-{}-{nonce}",
            std::process::id()
        ));
        DirBuilder::new().mode(0o700).create(&directory).unwrap();
        let socket = directory.join("reverse.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        let receipt = ReceiptPin {
            transaction_id: "11".into(),
            event_id: "12".into(),
            accepted_count: "13".into(),
            world_root: "14".into(),
        };
        let expected = receipt.clone();
        let server = thread::spawn(move || {
            for definite in [false, true] {
                let (mut stream, _) = listener.accept().unwrap();
                let mut length = [0u8; 4];
                stream.read_exact(&mut length).unwrap();
                let mut request = vec![0u8; u32::from_be_bytes(length) as usize];
                stream.read_exact(&mut request).unwrap();
                let request: Value = serde_json::from_slice(&request).unwrap();
                assert_eq!(request["type"], "inspect-settlement-v3");
                assert_eq!(request["attempt_id"], "41");
                assert_eq!(request["binding_sha256"], "a".repeat(64));
                assert_eq!(request["operation_fingerprint"], "b".repeat(64));
                let response = if definite {
                    json!({"type":"settled-v3", "attemptId":"41",
                        "bindingSha256":"a".repeat(64),
                        "operationFingerprint":"b".repeat(64),
                        "responseSha256":"c".repeat(64),
                        "committedReceipt":expected})
                } else {
                    json!({"type":"dispatch-settlement-uncertain-v3"})
                };
                let bytes = serde_json::to_vec(&response).unwrap();
                stream
                    .write_all(&(bytes.len() as u32).to_be_bytes())
                    .unwrap();
                stream.write_all(&bytes).unwrap();
            }
        });
        let client = LifetimeReverseClient::new(
            ReverseCustodyClient::new(
                socket.clone(),
                unsafe { libc::geteuid() },
                "workroom-app".into(),
            )
            .unwrap(),
        );
        for definite in [false, true] {
            let result = client
                .inspect_settlement(
                    "41",
                    &"a".repeat(64),
                    &"b".repeat(64),
                    &AtomicBool::new(false),
                    Instant::now() + std::time::Duration::from_secs(30),
                )
                .unwrap();
            assert_eq!(result.is_some(), definite);
            if let Some(result) = result {
                assert_eq!(result.response_sha256, "c".repeat(64));
                assert_eq!(result.committed_receipt, receipt);
            }
        }
        server.join().unwrap();
        fs::remove_file(socket).unwrap();
        fs::remove_dir(directory).unwrap();
    }
}
