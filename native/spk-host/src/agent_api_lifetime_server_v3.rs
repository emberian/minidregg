//! Resident lifetime agent API on the existing app's one RpcDriver. The
//! controller socket is transport identity; fresh op76 alone permits a send.

use crate::agent_api_lifetime_custody_v3::LifetimeCustodyV3;
use crate::agent_api_lifetime_dispatch_native_v3::{
    clear_retained_active_after_settlement, submit_fresh_once, FreshLifetimePermitV3,
};
use crate::agent_api_lifetime_paid_native_v3::{assemble_once, PaidAssemblyInput};
use crate::agent_api_lifetime_reverse_v3::{
    LifetimeReverseClient, ReserveV3Input, RetainedReserveV3,
};
use crate::agent_api_lifetime_v3::{LifetimeBinding, ReceiptPin};
use crate::agent_api_lifetime_wire_v3::{self as wire, OrdinaryHeader, Reply, Request};
use crate::agent_api_server::{
    digest_nat, read_private_recovery, unhex32, write_agent_delivery_marker, AgentApiListener,
    CallerWatch,
};
use crate::agent_api_wire;
use crate::dispatch_inspection::{app_route_path, HttpProjection, MatchedInspection, Route};
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::dispatch_web_input::physical_web_input;
use crate::hostd::{DispatchIdentity, Journal};
use crate::http_response;
use crate::rpc_adapter::RpcDriver;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::DirBuilder;
use std::io;
use std::os::fd::AsRawFd;
use std::os::unix::fs::DirBuilderExt;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

const MAX_APP_RESPONSE: usize = 65_536;
const MAX_SOURCE_INSPECTION: usize = 12_102_759;

fn refused(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn field<'a>(value: &'a Value, name: &str) -> io::Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| refused("lifetime committed source field absent"))
}

fn child<'a>(value: &'a Value, name: &str) -> io::Result<&'a Value> {
    value
        .get(name)
        .ok_or_else(|| refused("lifetime committed source object absent"))
}

fn unhex(value: &str) -> io::Result<Vec<u8>> {
    if !value.len().is_multiple_of(2)
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(refused("lifetime request hex refused"));
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

pub(crate) struct ResidentLifetimeAgent<'a> {
    pub operator: &'a PrivateOperator,
    pub custody: &'a LifetimeCustodyV3,
    pub journal: &'a Journal,
    pub rpc: &'a mut RpcDriver,
    pub reverse: &'a LifetimeReverseClient,
    pub signed_api_path: &'a str,
    pub display_name: &'a str,
    pub preferred_handle: &'a str,
    pub attempt_parent: &'a Path,
    pub reverse_timeout: Duration,
    pub controller_worker_wall_seconds: u64,
}

pub(crate) fn poll_once(
    listener: &AgentApiListener,
    resident: &mut ResidentLifetimeAgent<'_>,
) -> io::Result<bool> {
    let Some(mut stream) = listener.accept_authenticated()? else {
        return Ok(false);
    };
    let frame = match agent_api_wire::read_frame(&mut stream) {
        Ok(frame) => frame,
        Err(_) => return Ok(true),
    };
    let request = match Request::parse(&frame) {
        Ok(request) => request,
        Err(_) => return Ok(true),
    };
    let watch = match CallerWatch::start(&stream) {
        Ok(watch) => watch,
        Err(_) => return Ok(true),
    };
    // On a failed dispatch, close the socket. Before a source reserve, no
    // operation fingerprint exists; after it, an error may mean native or
    // physical uncertainty. A fabricated RefusedV3 would be unsafe.
    if let Ok(reply) = resident.handle_once(&stream, request, &watch.cancelled) {
        if let Ok(bytes) = serde_json::to_vec(&reply) {
            if bytes.len() <= wire::MAX_REPLY_FRAME {
                let _ = agent_api_wire::write_frame(&mut stream, &bytes);
            }
        }
    }
    Ok(true)
}

impl ResidentLifetimeAgent<'_> {
    fn binding(&self) -> io::Result<LifetimeBinding> {
        let record = self
            .journal
            .read()?
            .ok_or_else(|| refused("lifetime resident journal absent"))?;
        record.verify_running_instance()?;
        self.custody.binding(&record, self.signed_api_path)
    }

    fn handle_once(
        &mut self,
        stream: &UnixStream,
        request: Request,
        cancelled: &Arc<AtomicBool>,
    ) -> io::Result<Reply> {
        match request {
            Request::HelloV3 { .. } => {
                let binding = self.binding()?;
                let binding_sha256 = binding.fingerprint()?;
                Ok(Reply::BindingV3 {
                    protocol: wire::PROTOCOL.into(),
                    binding: Box::new(binding),
                    binding_sha256,
                })
            }
            Request::InspectV3 {
                operation_id,
                binding_sha256,
                operation_fingerprint,
                ..
            } => {
                self.recover_settlement(
                    &operation_id,
                    &binding_sha256,
                    operation_fingerprint.as_deref(),
                    cancelled,
                )?;
                inspect_saved(
                    self.attempt_parent,
                    &operation_id,
                    &binding_sha256,
                    operation_fingerprint.as_deref(),
                )
            }
            dispatch @ Request::DispatchV3 { .. } => {
                let binding = self.binding()?;
                self.dispatch_once(stream, dispatch, binding, cancelled)
            }
        }
    }

    fn dispatch_once(
        &mut self,
        stream: &UnixStream,
        request: Request,
        binding: LifetimeBinding,
        cancelled: &Arc<AtomicBool>,
    ) -> io::Result<Reply> {
        if cancelled.load(Ordering::Acquire) {
            return Err(refused("lifetime caller cancelled"));
        }
        let deadline = Instant::now() + self.reverse_timeout;
        let Request::DispatchV3 {
            ref operation_id,
            ref binding_sha256,
            ref method,
            ref path,
            ref query,
            ref headers,
            ref body_hex,
            ..
        } = request
        else {
            unreachable!()
        };
        if *binding_sha256 != binding.fingerprint()? {
            return Err(refused("lifetime dispatch stable binding drift"));
        }
        let body = unhex(body_hex)?;
        let ordered_headers: Vec<_> = headers
            .iter()
            .map(|header| (header.name.clone(), header.value.clone()))
            .collect();
        let path_and_query = if query.is_empty() {
            path.clone()
        } else {
            format!("{path}?{query}")
        };
        let http = HttpProjection {
            method,
            path_and_query: &path_and_query,
            ordered_headers: &ordered_headers,
            body: &body,
            route: Route::Api {
                signed_path: self.signed_api_path,
            },
        };
        let (app_path, _) = app_route_path(&http)?;
        private_dir(self.attempt_parent)?;
        let client_dir = self
            .attempt_parent
            .join(format!("agent-lifetime-client-op-{operation_id}"));
        DirBuilder::new().mode(0o700).create(&client_dir)?;
        let original_request = serde_json::to_vec(&request)?;
        write_new(&client_dir, "forward-request-v3.json", &original_request)?;
        write_new(
            &client_dir,
            "received-v3.json",
            &serde_json::to_vec(&json!({
                "protocol":wire::PROTOCOL,
                "operationId":operation_id,
                "bindingSha256":binding_sha256,
                "forwardSha256":hex(&Sha256::digest(&original_request)),
            }))?,
        )?;
        let native_dir = self
            .attempt_parent
            .join(format!("agent-lifetime-dispatch-op-{operation_id}"));
        DirBuilder::new().mode(0o700).create(&native_dir)?;
        let (fixed_request, decoded_http) = self
            .custody
            .fixed_reserve_request(&request, self.signed_api_path)?;
        let reserve = self.reverse.reserve_once(
            ReserveV3Input {
                operator: self.operator,
                binding: &binding,
                forward_operation_id: operation_id,
                fixed_request: &fixed_request,
                decoded_http: &decoded_http,
                attempt_dir: &native_dir,
                deadline,
                worker_wall_seconds: self.controller_worker_wall_seconds,
            },
            cancelled,
        )?;
        write_new(
            &client_dir,
            "source-verified-v3.json",
            &serde_json::to_vec(&json!({
                "bindingSha256":binding_sha256,
                "operationFingerprint":reserve.operation_fingerprint,
                "reserveAttemptId":reserve.attempt_id,
                "requestSha256":reserve.request_sha256,
            }))?,
        )?;
        let paid = assemble_once(PaidAssemblyInput {
            operator: self.operator,
            custody: self.custody,
            reverse: self.reverse,
            binding: &binding,
            reserve: &reserve,
            attempt_dir: &native_dir,
            cancelled,
            deadline,
        })?;
        let permit = submit_fresh_once(
            self.operator,
            &binding,
            &reserve,
            &paid,
            &decoded_http,
            &native_dir,
            cancelled,
        )?;
        write_new(&client_dir, "op76-fresh-v3.json", b"fresh-installed-op76")?;
        let matched = matched_v3(&permit, &reserve, method, &app_path, query)?;
        let physical =
            physical_web_input(&matched, &http, self.display_name, self.preferred_handle)?;
        caller_still_present(stream, cancelled)?;
        let record = self
            .journal
            .read()?
            .ok_or_else(|| refused("lifetime app journal absent"))?;
        record.verify_running_instance()?;
        let identity = DispatchIdentity {
            permit_sha256: hex(&Sha256::digest(permit.frame())),
            request_digest: matched.physical_request_digest,
            app: matched.app,
            app_generation: matched.app_generation,
            invocation_id: record
                .invocation_id()
                .ok_or_else(|| refused("lifetime host invocation absent"))?
                .to_owned(),
            operation_id: operation_id.clone(),
            session_resource: matched.session_resource,
            session_generation: matched.session_generation,
            dispatch_transaction: matched.dispatch_transaction,
            dispatch_event: matched.dispatch_event,
        };
        write_new(
            &client_dir,
            "dispatch-identity-v3.json",
            &serde_json::to_vec(&identity)?,
        )?;
        let prequeue = self.rpc.prepare_cancellable(identity.clone())?;
        if let Err(error) = self
            .journal
            .request_dispatch(identity.clone(), permit.frame())
        {
            let fence = prequeue.abort_no_enqueue();
            let _ = self
                .journal
                .finish_dispatch_uncertain_released(&identity, fence);
            return Err(error);
        }
        let prequeue =
            write_agent_delivery_marker(prequeue, self.journal, &identity, &client_dir, || {
                record.verify_running_instance()
            })?;
        // This is the final before-fd3 controller fence. A failed/lost ACK
        // consumes the linear no-enqueue guard and retains only this attempt's
        // uncertainty; it never queues or retries the physical request.
        if let Err(error) = self.reverse.mark_send_once(
            &reserve,
            &paid.ingress,
            permit.frame(),
            permit.receipt(),
            cancelled,
            deadline,
        ) {
            let fence = prequeue.abort_no_enqueue();
            let _ = self
                .journal
                .finish_dispatch_uncertain_released(&identity, fence);
            return Err(error);
        }
        let (web_reply, success_fence) = match prequeue.dispatch(
            physical.binding,
            physical.request,
            MAX_APP_RESPONSE,
            Duration::from_secs(30),
            Arc::clone(cancelled),
        ) {
            Ok(reply) => reply,
            Err(failure) => {
                let (error, fence) = failure.into_parts();
                if let Some(fence) = fence {
                    let _ = self
                        .journal
                        .finish_dispatch_uncertain_released(&identity, fence);
                } else {
                    let _ = self.journal.finish_dispatch(&identity, false);
                }
                return Err(error);
            }
        };
        let outcome: io::Result<Reply> = (|| {
            let response = http_response::serialize(&web_reply, method == "HEAD")?;
            let response_sha256 = hex(&Sha256::digest(&response));
            write_new(&client_dir, "app-response-v3.bin", &response)?;
            write_new(
                &client_dir,
                "app-response-v3.sha256",
                response_sha256.as_bytes(),
            )?;
            let reply = http_reply_v3(
                &response,
                operation_id,
                binding_sha256,
                &reserve.operation_fingerprint,
                &response_sha256,
                permit.receipt(),
            )?;
            let reply_bytes = serde_json::to_vec(&reply)?;
            self.reverse
                .settle_definite_once(&reserve, &response_sha256, cancelled, deadline)?;
            write_new(
                &client_dir,
                "settle-confirmed-v3.json",
                &serde_json::to_vec(&json!({
                    "attemptId":reserve.attempt_id,
                    "responseSha256":response_sha256,
                    "committedReceipt":permit.receipt(),
                }))?,
            )?;
            self.journal.finish_dispatch(&identity, true)?;
            permit.clear_active_after_settlement()?;
            write_new(&client_dir, "definite-v3.json", &reply_bytes)?;
            write_new(
                &client_dir,
                "definite-v3.sha256",
                hex(&Sha256::digest(&reply_bytes)).as_bytes(),
            )?;
            Ok(reply)
        })();
        match outcome {
            Ok(reply) => Ok(reply),
            Err(error) => {
                let _ = self
                    .journal
                    .finish_dispatch_uncertain_released(&identity, success_fence);
                Err(error)
            }
        }
    }

    fn recover_settlement(
        &self,
        operation_id: &str,
        binding_sha256: &str,
        operation_fingerprint: Option<&str>,
        cancelled: &AtomicBool,
    ) -> io::Result<()> {
        let client = self
            .attempt_parent
            .join(format!("agent-lifetime-client-op-{operation_id}"));
        let native = self
            .attempt_parent
            .join(format!("agent-lifetime-dispatch-op-{operation_id}"));
        if !client.join("app-response-v3.bin").exists()
            || (client.join("definite-v3.json").exists()
                && client.join("definite-v3.sha256").exists())
        {
            return Ok(());
        }
        private_dir(&client)?;
        private_dir(&native)?;
        let verified: Value = serde_json::from_slice(&read_private_recovery(
            &native.join("reserve-verified-v3.json"),
            4096,
        )?)?;
        let fingerprint =
            operation_fingerprint.ok_or_else(|| refused("lifetime recovery fingerprint absent"))?;
        if field(&verified, "httpOperationId")? != operation_id
            || field(&verified, "bindingSha256")? != binding_sha256
            || field(&verified, "operationFingerprint")? != fingerprint
        {
            return Err(refused("lifetime recovery reserve identity drift"));
        }
        let received: Value = serde_json::from_slice(&read_private_recovery(
            &client.join("received-v3.json"),
            4096,
        )?)?;
        let forward_bytes =
            read_private_recovery(&client.join("forward-request-v3.json"), wire::MAX_FRAME)?;
        if field(&received, "forwardSha256")? != hex(&Sha256::digest(&forward_bytes)) {
            return Err(refused("lifetime recovery forward digest drift"));
        }
        let forward = Request::parse(&forward_bytes)?;
        let Request::DispatchV3 {
            operation_id: saved_operation,
            binding_sha256: saved_binding,
            ..
        } = forward
        else {
            return Err(refused("lifetime recovery forward type drift"));
        };
        if saved_operation != operation_id || saved_binding != binding_sha256 {
            return Err(refused("lifetime recovery forward identity drift"));
        }
        if read_private_recovery(&client.join("op76-fresh-v3.json"), 128)?
            != b"fresh-installed-op76"
        {
            return Err(refused("lifetime recovery fresh op76 marker drift"));
        }
        let committed: Value = serde_json::from_slice(&read_private_recovery(
            &native.join("committed-v3.json"),
            MAX_SOURCE_INSPECTION,
        )?)?;
        let committed_bytes =
            read_private_recovery(&native.join("committed-v3.bin"), MAX_SOURCE_INSPECTION)?;
        let outer =
            read_private_recovery(&native.join("op76-frame-v3.bin"), MAX_SOURCE_INSPECTION + 5)?;
        if outer.len() < 6
            || u32::from_le_bytes(outer[..4].try_into().unwrap()) as usize + 4 != outer.len()
            || outer[4] != 76
            || &outer[5..] != committed_bytes.as_slice()
            || field(&committed, "frameHex")? != hex(&committed_bytes)
        {
            return Err(refused("lifetime recovered fresh op76 frame drift"));
        }
        let receipt: ReceiptPin =
            serde_json::from_value(child(&committed, "dispatchReceipt")?.clone())?;
        receipt.validate()?;
        let app_response =
            read_private_recovery(&client.join("app-response-v3.bin"), MAX_APP_RESPONSE * 2)?;
        let response_sha256 = hex(&Sha256::digest(&app_response));
        if String::from_utf8(read_private_recovery(
            &client.join("app-response-v3.sha256"),
            64,
        )?)
        .map_err(|_| refused("lifetime recovery response digest UTF-8"))?
            != response_sha256
        {
            return Err(refused("lifetime recovery app response digest drift"));
        }
        let Some(settled) = self.reverse.inspect_settlement(
            field(&verified, "attemptId")?,
            binding_sha256,
            fingerprint,
            cancelled,
            Instant::now() + self.reverse_timeout,
        )?
        else {
            return Ok(());
        };
        if settled.response_sha256() != response_sha256 || settled.committed_receipt() != &receipt {
            return Err(refused(
                "lifetime recovered settlement differs from retained response",
            ));
        }
        let settled_bytes = serde_json::to_vec(&json!({
            "attemptId":field(&verified, "attemptId")?,
            "responseSha256":response_sha256,
            "committedReceipt":receipt,
        }))?;
        write_new_or_same(&client, "settle-confirmed-v3.json", &settled_bytes)?;
        let identity: DispatchIdentity = serde_json::from_slice(&read_private_recovery(
            &client.join("dispatch-identity-v3.json"),
            4096,
        )?)?;
        self.journal
            .finish_dispatch_recovered(&identity, &settled)?;
        clear_retained_active_after_settlement(&native)?;
        let reply = http_reply_v3(
            &app_response,
            operation_id,
            binding_sha256,
            fingerprint,
            &response_sha256,
            settled.committed_receipt(),
        )?;
        let reply_bytes = serde_json::to_vec(&reply)?;
        write_new_or_same(&client, "definite-v3.json", &reply_bytes)?;
        write_new_or_same(
            &client,
            "definite-v3.sha256",
            hex(&Sha256::digest(&reply_bytes)).as_bytes(),
        )?;
        Ok(())
    }
}

fn write_new_or_same(directory: &Path, name: &str, bytes: &[u8]) -> io::Result<()> {
    let path = directory.join(name);
    if path.exists() {
        if read_private_recovery(&path, wire::MAX_REPLY_FRAME)? != bytes {
            return Err(refused("lifetime recovery retained artifact drift"));
        }
    } else {
        write_new(directory, name, bytes)?;
    }
    Ok(())
}

fn caller_still_present(stream: &UnixStream, cancelled: &AtomicBool) -> io::Result<()> {
    if cancelled.load(Ordering::Acquire) {
        return Err(refused("lifetime caller disconnected before delivery"));
    }
    let mut byte = [0u8; 1];
    let count = unsafe {
        libc::recv(
            stream.as_raw_fd(),
            byte.as_mut_ptr().cast(),
            1,
            libc::MSG_PEEK | libc::MSG_DONTWAIT,
        )
    };
    if count >= 0 {
        return Err(refused(
            "lifetime caller disconnected or sent trailing bytes",
        ));
    }
    let error = io::Error::last_os_error();
    if error.kind() != io::ErrorKind::WouldBlock {
        return Err(error);
    }
    Ok(())
}

fn matched_v3(
    permit: &FreshLifetimePermitV3,
    reserve: &RetainedReserveV3,
    method: &str,
    app_path: &str,
    query: &str,
) -> io::Result<MatchedInspection> {
    let view = permit.inspection();
    let app = child(view, "app")?;
    let session = child(view, "session")?;
    let request = child(view, "request")?;
    let current = child(view, "currentImage")?;
    let identity = child(view, "identity")?;
    let bits = child(view, "effectiveBits")?
        .as_array()
        .ok_or_else(|| refused("lifetime effective bits absent"))?
        .iter()
        .map(|bit| {
            bit.as_bool()
                .ok_or_else(|| refused("lifetime effective bit malformed"))
        })
        .collect::<io::Result<Vec<_>>>()?;
    if bits.len() > 128 {
        return Err(refused("lifetime effective permission width"));
    }
    let app_generation = field(app, "generation")?
        .parse::<u64>()
        .map_err(|_| refused("lifetime app generation host range"))?;
    let path_and_query = if query.is_empty() {
        app_path.to_owned()
    } else {
        format!("{app_path}?{query}")
    };
    Ok(MatchedInspection {
        app: field(app, "resource")?
            .parse()
            .map_err(|_| refused("lifetime app host range"))?,
        app_generation,
        session_resource: field(session, "resource")?.into(),
        session_generation: field(session, "generation")?.into(),
        subject: field(session, "subject")?.into(),
        operation_id: reserve.http_operation_id.clone(),
        physical_request_digest: field(request, "physicalDigest")?.into(),
        dispatch_transaction: permit.receipt().transaction_id.clone(),
        dispatch_event: permit.receipt().event_id.clone(),
        session_fingerprint: digest_nat(field(view, "sessionFingerprint")?)?,
        principal: unhex32(field(identity, "principalHex")?)?,
        before_image_boundary: field(current, "boundary")?.into(),
        after_image_boundary: permit.receipt().image_boundary.clone(),
        accepted_count: permit.receipt().accepted_count.clone(),
        effective_bits: bits,
        app_path_and_query: path_and_query,
        method: method.into(),
    })
}

fn http_reply_v3(
    bytes: &[u8],
    operation_id: &str,
    binding_sha256: &str,
    operation_fingerprint: &str,
    response_sha256: &str,
    receipt: &ReceiptPin,
) -> io::Result<Reply> {
    let boundary = bytes
        .windows(4)
        .position(|window| window == b"\r\n\r\n")
        .ok_or_else(|| refused("lifetime app response boundary absent"))?;
    let head = std::str::from_utf8(&bytes[..boundary])
        .map_err(|_| refused("lifetime app response header UTF-8"))?;
    let mut lines = head.split("\r\n");
    let status = lines
        .next()
        .and_then(|line| line.split_whitespace().nth(1))
        .and_then(|number| number.parse::<u16>().ok())
        .ok_or_else(|| refused("lifetime app response status"))?;
    let mut headers = Vec::new();
    for line in lines {
        let (name, value) = line
            .split_once(": ")
            .ok_or_else(|| refused("lifetime app response header"))?;
        headers.push(OrdinaryHeader {
            name: name.to_ascii_lowercase(),
            value: value.to_owned(),
        });
    }
    let reply = Reply::HttpV3 {
        protocol: wire::PROTOCOL.into(),
        operation_id: operation_id.into(),
        binding_sha256: binding_sha256.into(),
        operation_fingerprint: operation_fingerprint.into(),
        response_sha256: response_sha256.into(),
        committed_receipt: receipt.clone(),
        status,
        headers,
        body_hex: hex(&bytes[boundary + 4..]),
    };
    if serde_json::to_vec(&reply)?.len() > wire::MAX_REPLY_FRAME {
        return Err(refused("lifetime app response exceeds controller frame"));
    }
    Ok(reply)
}

fn inspect_saved(
    parent: &Path,
    operation_id: &str,
    binding_sha256: &str,
    operation_fingerprint: Option<&str>,
) -> io::Result<Reply> {
    private_dir(parent)?;
    let client = parent.join(format!("agent-lifetime-client-op-{operation_id}"));
    let native = parent.join(format!("agent-lifetime-dispatch-op-{operation_id}"));
    if !client.exists() {
        return Ok(Reply::InspectionV3 {
            protocol: wire::PROTOCOL.into(),
            operation_id: operation_id.into(),
            binding_sha256: binding_sha256.into(),
            operation_fingerprint: operation_fingerprint.map(str::to_owned),
            state: "not-seen".into(),
            definite_reply_sha256: None,
            definite_reply_json_hex: None,
            retention_error: None,
        });
    }
    private_dir(&client)?;
    let received: Value = serde_json::from_slice(&read_private_recovery(
        &client.join("received-v3.json"),
        4096,
    )?)?;
    if field(&received, "protocol")? != wire::PROTOCOL
        || field(&received, "operationId")? != operation_id
        || field(&received, "bindingSha256")? != binding_sha256
    {
        return Err(refused(
            "lifetime historical binding differs from received attempt",
        ));
    }
    let forward_bytes =
        read_private_recovery(&client.join("forward-request-v3.json"), wire::MAX_FRAME)?;
    if field(&received, "forwardSha256")? != hex(&Sha256::digest(&forward_bytes)) {
        return Err(refused("lifetime historical forward HTTP digest drift"));
    }
    let forward = Request::parse(&forward_bytes)?;
    if !matches!(forward, Request::DispatchV3 { operation_id: ref id, binding_sha256: ref pin, .. }
        if id == operation_id && pin == binding_sha256)
    {
        return Err(refused("lifetime historical forward HTTP coordinate drift"));
    }
    let verified_path = client.join("source-verified-v3.json");
    let reserve_path = native.join("reserve-verified-v3.json");
    let verified = if verified_path.exists() {
        Some(serde_json::from_slice::<Value>(&read_private_recovery(
            &verified_path,
            4096,
        )?)?)
    } else {
        None
    };
    let reserve = if reserve_path.exists() {
        private_dir(&native)?;
        Some(serde_json::from_slice::<Value>(&read_private_recovery(
            &reserve_path,
            4096,
        )?)?)
    } else {
        None
    };
    if let (Some(verified), Some(reserve)) = (&verified, &reserve) {
        if field(verified, "operationFingerprint")? != field(reserve, "operationFingerprint")?
            || field(verified, "bindingSha256")? != field(reserve, "bindingSha256")?
        {
            return Err(refused(
                "lifetime historical client/native reserve join drift",
            ));
        }
    }
    let saved_fingerprint = if let Some(verified) = verified.as_ref().or(reserve.as_ref()) {
        if field(verified, "bindingSha256")? != binding_sha256 {
            return Err(refused("lifetime historical verified binding drift"));
        }
        Some(field(verified, "operationFingerprint")?.to_owned())
    } else {
        None
    };
    if operation_fingerprint.is_some_and(|pin| Some(pin) != saved_fingerprint.as_deref()) {
        return Err(refused("lifetime historical operation fingerprint drift"));
    }
    let mut state = if saved_fingerprint.is_none() && !native.exists() {
        "received"
    } else {
        "uncertain"
    };
    let mut definite_reply_sha256 = None;
    let mut definite_reply_json_hex = None;
    let mut retention_error = None;
    if client.join("definite-v3.json").exists() {
        let recovered = (|| -> io::Result<(String, Vec<u8>)> {
            let bytes =
                read_private_recovery(&client.join("definite-v3.json"), wire::MAX_REPLY_FRAME)?;
            let sha = String::from_utf8(read_private_recovery(
                &client.join("definite-v3.sha256"),
                64,
            )?)
            .map_err(|_| refused("lifetime definite digest UTF-8"))?;
            if sha != hex(&Sha256::digest(&bytes)) {
                return Err(refused("lifetime definite reply digest drift"));
            }
            let reply: Reply = serde_json::from_slice(&bytes)?;
            let Reply::HttpV3 {
                protocol,
                operation_id: saved_operation,
                binding_sha256: saved_binding,
                operation_fingerprint: saved_fingerprint_in_reply,
                response_sha256,
                committed_receipt,
                ..
            } = reply
            else {
                return Err(refused("lifetime retained definite reply type drift"));
            };
            if protocol != wire::PROTOCOL
                || saved_operation != operation_id
                || saved_binding != binding_sha256
                || saved_fingerprint.as_deref() != Some(saved_fingerprint_in_reply.as_str())
            {
                return Err(refused("lifetime retained definite operation drift"));
            }
            let settled: Value = serde_json::from_slice(&read_private_recovery(
                &client.join("settle-confirmed-v3.json"),
                4096,
            )?)?;
            if field(&settled, "responseSha256")? != response_sha256
                || settled.get("committedReceipt")
                    != Some(&serde_json::to_value(committed_receipt)?)
            {
                return Err(refused("lifetime retained settlement drift"));
            }
            let app_response =
                read_private_recovery(&client.join("app-response-v3.bin"), MAX_APP_RESPONSE * 2)?;
            if hex(&Sha256::digest(&app_response)) != response_sha256 {
                return Err(refused("lifetime retained app response digest drift"));
            }
            Ok((sha, bytes))
        })();
        match recovered {
            Ok((sha, bytes)) => {
                state = "definite";
                definite_reply_sha256 = Some(sha);
                definite_reply_json_hex = Some(hex(&bytes));
            }
            Err(_) => {
                state = "uncertain";
                retention_error = Some("definite-reply-unverified".into());
            }
        }
    }
    Ok(Reply::InspectionV3 {
        protocol: wire::PROTOCOL.into(),
        operation_id: operation_id.into(),
        binding_sha256: binding_sha256.into(),
        operation_fingerprint: saved_fingerprint,
        state: state.into(),
        definite_reply_sha256,
        definite_reply_json_hex,
        retention_error,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn definite_http_hashes_exact_app_response_not_self_referential_json() {
        let response = b"HTTP/1.1 200 OK\r\ncontent-type: text/plain\r\n\r\nhello";
        let sha = hex(&Sha256::digest(response));
        let receipt = ReceiptPin {
            transaction_id: "1".into(),
            event_id: "2".into(),
            accepted_count: "3".into(),
            image_boundary: "4".into(),
        };
        let reply = http_reply_v3(
            response,
            "9",
            &"a".repeat(64),
            &"b".repeat(64),
            &sha,
            &receipt,
        )
        .unwrap();
        let Reply::HttpV3 {
            response_sha256,
            committed_receipt,
            body_hex,
            ..
        } = reply
        else {
            panic!("wrong reply")
        };
        assert_eq!(response_sha256, sha);
        assert_eq!(committed_receipt, receipt);
        assert_eq!(body_hex, "68656c6c6f");
    }

    #[test]
    fn historical_inspect_requires_original_http_binding_settlement_and_exact_saved_reply() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let parent = std::env::temp_dir().join(format!(
            "mini-lifetime-inspect-{}-{nonce}",
            std::process::id()
        ));
        DirBuilder::new().mode(0o700).create(&parent).unwrap();
        let client = parent.join("agent-lifetime-client-op-9");
        DirBuilder::new().mode(0o700).create(&client).unwrap();
        let binding = "a".repeat(64);
        let fingerprint = "b".repeat(64);
        let forward = Request::DispatchV3 {
            protocol: wire::PROTOCOL.into(),
            operation_id: "9".into(),
            binding_sha256: binding.clone(),
            method: "GET".into(),
            path: "info/refs".into(),
            query: "service=git-upload-pack".into(),
            headers: vec![],
            body_hex: String::new(),
        };
        let forward_bytes = serde_json::to_vec(&forward).unwrap();
        write_new(&client, "forward-request-v3.json", &forward_bytes).unwrap();
        write_new(
            &client,
            "received-v3.json",
            &serde_json::to_vec(&json!({
                "protocol":wire::PROTOCOL,
                "operationId":"9",
                "bindingSha256":binding,
                "forwardSha256":hex(&Sha256::digest(&forward_bytes)),
            }))
            .unwrap(),
        )
        .unwrap();
        let Reply::InspectionV3 { state, .. } =
            inspect_saved(&parent, "9", &binding, None).unwrap()
        else {
            panic!("wrong inspection")
        };
        assert_eq!(state, "received");
        write_new(
            &client,
            "source-verified-v3.json",
            &serde_json::to_vec(&json!({
                "bindingSha256":binding,
                "operationFingerprint":fingerprint,
            }))
            .unwrap(),
        )
        .unwrap();
        let Reply::InspectionV3 {
            state,
            definite_reply_json_hex,
            ..
        } = inspect_saved(&parent, "9", &binding, Some(&fingerprint)).unwrap()
        else {
            panic!("wrong inspection")
        };
        assert_eq!(state, "uncertain");
        assert!(definite_reply_json_hex.is_none());
        let response = b"HTTP/1.1 200 OK\r\ncontent-type: text/plain\r\n\r\nhello";
        let response_sha = hex(&Sha256::digest(response));
        let receipt = ReceiptPin {
            transaction_id: "11".into(),
            event_id: "12".into(),
            accepted_count: "13".into(),
            image_boundary: "14".into(),
        };
        let reply = http_reply_v3(
            response,
            "9",
            &binding,
            &fingerprint,
            &response_sha,
            &receipt,
        )
        .unwrap();
        let reply_bytes = serde_json::to_vec(&reply).unwrap();
        write_new(&client, "app-response-v3.bin", response).unwrap();
        write_new(
            &client,
            "settle-confirmed-v3.json",
            &serde_json::to_vec(&json!({
                "attemptId":"41", "responseSha256":response_sha,
                "committedReceipt":receipt,
            }))
            .unwrap(),
        )
        .unwrap();
        write_new(&client, "definite-v3.json", &reply_bytes).unwrap();
        write_new(
            &client,
            "definite-v3.sha256",
            hex(&Sha256::digest(&reply_bytes)).as_bytes(),
        )
        .unwrap();
        let Reply::InspectionV3 {
            state,
            definite_reply_json_hex,
            definite_reply_sha256,
            ..
        } = inspect_saved(&parent, "9", &binding, Some(&fingerprint)).unwrap()
        else {
            panic!("wrong inspection")
        };
        assert_eq!(state, "definite");
        assert_eq!(definite_reply_json_hex, Some(hex(&reply_bytes)));
        assert_eq!(
            definite_reply_sha256,
            Some(hex(&Sha256::digest(&reply_bytes)))
        );
        // Historical A remains readable after another request B occupies this
        // route's native marker. Inspect never treats B's marker as A's permit.
        write_new(&parent, "native-agent-lifetime-active.json", b"newer-B").unwrap();
        let Reply::InspectionV3 { state, .. } =
            inspect_saved(&parent, "9", &binding, Some(&fingerprint)).unwrap()
        else {
            panic!("wrong historical inspection")
        };
        assert_eq!(state, "definite");
        assert_eq!(
            fs::read(parent.join("native-agent-lifetime-active.json")).unwrap(),
            b"newer-B"
        );
        assert!(inspect_saved(&parent, "9", &"c".repeat(64), Some(&fingerprint)).is_err());
        assert!(inspect_saved(&parent, "9", &binding, Some(&"d".repeat(64))).is_err());
        fs::write(client.join("definite-v3.sha256"), "0".repeat(64)).unwrap();
        let Reply::InspectionV3 {
            state,
            definite_reply_json_hex,
            retention_error,
            ..
        } = inspect_saved(&parent, "9", &binding, Some(&fingerprint)).unwrap()
        else {
            panic!("wrong inspection")
        };
        assert_eq!(state, "uncertain");
        assert!(definite_reply_json_hex.is_none());
        assert_eq!(
            retention_error.as_deref(),
            Some("definite-reply-unverified")
        );
        fs::remove_dir_all(parent).unwrap();
    }
}
