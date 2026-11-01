//! Physical execution of the source-checked, bounded hosted descriptor.
//! Every invocation arrives through a fresh lifetime permit and one-shot retained send.
use crate::rpc_adapter::SessionBinding;
use minidregg_spk_rpc::{
    dispatch_web, open_web_socket, send_to_app, WebRequest, WebResponse, WebResult, WebSocketOpen,
    WebSocketSession,
};
use serde_json::{json, Value};
use std::collections::{HashMap, HashSet};
use std::io::{self, Read};
use std::path::PathBuf;
use std::time::{Duration, Instant};
mod vocabulary {
    include!("../../hosted-conversation.rs");
}
pub(crate) use vocabulary::METHOD;
pub(crate) fn descriptor(body: &[u8]) -> Result<Value, &'static str> {
    vocabulary::parse(body)
}
fn invalid(s: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, s)
}
#[derive(Clone)]
pub(crate) struct Custody {
    pub directory: PathBuf,
    pub api_prefix: Option<String>,
    operation: Vec<u8>,
    retained: Vec<u8>,
    admission: Vec<u8>,
    receipt: Value,
}
impl Custody {
    pub(crate) fn admitted(
        directory: PathBuf,
        api_prefix: Option<String>,
        operation: &str,
        body: &[u8],
        permit: &crate::agent_api_lifetime_dispatch_native_v3::FreshLifetimePermitV3,
    ) -> io::Result<Self> {
        crate::dispatch_native::write_new(&directory, "hosted-admitted-descriptor.bin", body)?;
        Ok(Self {
            directory,
            api_prefix,
            operation: operation.as_bytes().to_vec(),
            retained: body.to_vec(),
            admission: permit.frame().to_vec(),
            receipt: serde_json::to_value(permit.receipt())?,
        })
    }
    #[cfg(test)]
    fn fixture(directory: PathBuf, operation: &str, body: &[u8]) -> Self {
        crate::dispatch_native::write_new(&directory, "hosted-admitted-descriptor.bin", body)
            .unwrap();
        Self {
            directory,
            api_prefix: None,
            operation: operation.as_bytes().to_vec(),
            retained: body.to_vec(),
            admission: vec![1],
            receipt: Value::Null,
        }
    }
}
struct Channel {
    protocol: String,
    expires: Instant,
    socket: WebSocketSession,
    buffered: Vec<u8>,
    fragment: Vec<u8>,
    fragmenting: bool,
    ids: HashSet<String>,
    max_frames: usize,
    max_bytes: usize,
}
#[derive(Default)]
pub(crate) struct Pool {
    channels: HashMap<String, Option<Channel>>,
    lifecycle: HashMap<String, vocabulary::State>,
}
fn binding_bytes(binding: &SessionBinding, endpoint: &str) -> io::Result<Vec<u8>> {
    serde_json::to_vec(&json!({"app":binding.app,"appGeneration":binding.process_generation,
        "session":binding.session_resource,"sessionGeneration":binding.session_generation,"subject":binding.subject,
        "kind":if binding.kind==crate::rpc_adapter::SessionKind::Web {"web"} else {"api"},
        "projection":binding.projection_fingerprint,"principal":binding.params.identity_id,
        "origin":binding.params.base_path,"permissions":binding.params.permissions,"endpoint":endpoint})).map_err(io::Error::other)
}
fn number(v: &Value, k: &str) -> usize {
    v[k].as_u64().unwrap() as usize
}
fn string<'a>(v: &'a Value, k: &str) -> &'a str {
    v[k].as_str().unwrap()
}
fn frame(text: &str) -> io::Result<Vec<u8>> {
    let mut mask = [0; 4];
    std::fs::File::open("/dev/urandom")?.read_exact(&mut mask)?;
    let mut out = vec![0x81];
    let n = text.len();
    if n < 126 {
        out.push(0x80 | n as u8);
    } else {
        out.push(0x80 | 126);
        out.extend_from_slice(&(n as u16).to_be_bytes());
    }
    out.extend_from_slice(&mask);
    out.extend(text.bytes().enumerate().map(|(i, b)| b ^ mask[i % 4]));
    Ok(out)
}
impl Channel {
    fn send_preimage(&mut self, text: &str, custody: &Custody) -> io::Result<Vec<u8>> {
        if self.max_frames == 0 || text.len() > self.max_bytes {
            return Err(invalid("hosted cumulative channel budget exhausted"));
        }
        let value: Value = if self.protocol == "ddp-v1" {
            serde_json::from_str(text).map_err(|_| invalid("DDP text is not JSON"))?
        } else {
            Value::Null
        };
        if value["msg"] == "method" {
            let id = value["id"]
                .as_str()
                .ok_or_else(|| invalid("DDP method id absent"))?;
            if !self.ids.insert(id.to_owned()) {
                return Err(invalid("DDP method id already sent on this connection"));
            }
        }
        let bytes = frame(text)?;
        if bytes.len() > self.max_bytes {
            return Err(invalid("hosted wire byte budget exhausted"));
        }
        self.max_frames -= 1;
        self.max_bytes -= bytes.len();
        crate::dispatch_native::write_new(&custody.directory, "hosted-frame.bin", &bytes)?;
        Ok(bytes)
    }
    async fn next_text(
        &mut self,
        deadline: Instant,
        limit: usize,
        frame_limit: usize,
        keep: &dyn Fn(&str) -> bool,
    ) -> io::Result<String> {
        let mut frames = 0;
        let mut consumed = 0;
        // What the message being assembled has cost; charged to the channel only if it is kept.
        let (mut message_frames, mut message_bytes) = (0usize, 0usize);
        loop {
            if self.buffered.len() >= 2 {
                let first = self.buffered[0];
                let second = self.buffered[1];
                if first & 0x70 != 0 || second & 0x80 != 0 {
                    return Err(invalid("unsupported server WebSocket frame flags"));
                }
                let mut offset = 2;
                let size = match second & 0x7f {
                    126 => {
                        if self.buffered.len() < 4 {
                            None
                        } else {
                            offset = 4;
                            Some(u16::from_be_bytes([self.buffered[2], self.buffered[3]]) as usize)
                        }
                    }
                    127 => {
                        if self.buffered.len() < 10 {
                            None
                        } else {
                            offset = 10;
                            Some(
                                usize::try_from(u64::from_be_bytes(
                                    self.buffered[2..10].try_into().unwrap(),
                                ))
                                .map_err(|_| invalid("WebSocket frame length overflow"))?,
                            )
                        }
                    }
                    n => Some(n as usize),
                };
                if let Some(size) = size {
                    if size > limit || self.fragment.len().saturating_add(size) > limit {
                        return Err(invalid("hosted frame byte budget exceeded"));
                    }
                    if self.buffered.len() >= offset + size {
                        if self.max_frames <= message_frames
                            || frames + message_frames >= frame_limit
                            || message_bytes + offset + size > self.max_bytes
                            || consumed + message_bytes + offset + size > limit
                        {
                            return Err(invalid("hosted wire frame or byte budget exhausted"));
                        }
                        message_frames += 1;
                        message_bytes += offset + size;
                        let payload = self.buffered[offset..offset + size].to_vec();
                        self.buffered.drain(..offset + size);
                        match first & 0x0f {
                            1 if !self.fragmenting => {
                                self.fragment = payload;
                                self.fragmenting = true;
                            }
                            0 if self.fragmenting => self.fragment.extend(payload),
                            10 if first & 0x80 != 0 && size <= 125 => {
                                // An unsolicited pong is charged like any delivered frame.
                                frames += 1;
                                consumed += offset + size;
                                self.max_frames -= 1;
                                self.max_bytes -= offset + size;
                                message_frames -= 1;
                                message_bytes -= offset + size;
                                continue;
                            }
                            // RFC6455 control ping is an explicit closed-codec limit.
                            // DDP/EngineIO pings are text and returned to the SDK;
                            // no automatic unadmitted pong is sent.
                            9 => return Err(invalid(
                                "hosted RFC6455 ping control requires admitted control-frame codec",
                            )),
                            8 => return Err(invalid("hosted channel closed by app")),
                            _ => return Err(invalid("hosted protocol requires text frames")),
                        }
                        if first & 0x80 != 0 {
                            self.fragmenting = false;
                            let text = String::from_utf8(std::mem::take(&mut self.fragment))
                                .map_err(|_| invalid("hosted text is not UTF8"))?;
                            let cost = (std::mem::take(&mut message_frames), std::mem::take(&mut message_bytes));
                            // A message the receive did not ask for is drained and never delivered,
                            // so it is not charged; the receive's deadline bounds this work.
                            if !keep(&text) {
                                continue;
                            }
                            frames += cost.0;
                            consumed += cost.1;
                            self.max_frames -= cost.0;
                            self.max_bytes -= cost.1;
                            return Ok(text);
                        }
                        continue;
                    }
                }
            }
            let remaining = deadline
                .checked_duration_since(Instant::now())
                .ok_or_else(|| {
                    io::Error::new(io::ErrorKind::TimedOut, "hosted receive deadline")
                })?;
            let bytes = tokio::time::timeout(remaining, self.socket.from_app.recv())
                .await
                .map_err(|_| io::Error::new(io::ErrorKind::TimedOut, "hosted receive deadline"))?
                .ok_or_else(|| invalid("hosted app stream ended"))?;
            if self.buffered.len().saturating_add(bytes.len()) > limit + 64 * 14 {
                return Err(invalid("hosted raw frame budget exceeded"));
            }
            self.buffered.extend(bytes);
        }
    }
}
/// The event name of a socket.io event packet ("42[\"name\", ...]", optionally with a namespace
/// "42/ns,[...]" or an ack id "42 7[...]"), or None for any other packet.
fn socketio_event(text: &str) -> Option<String> {
    let rest = text.strip_prefix("42")?;
    let rest = match rest.strip_prefix('/') {
        Some(ns) => ns.split_once(',')?.1,
        None => rest,
    };
    let rest = rest.trim_start_matches(|c: char| c.is_ascii_digit());
    let packet: Value = serde_json::from_str(rest).ok()?;
    packet.as_array()?.first()?.as_str().map(str::to_owned)
}

/// True when a socket.io event packet is a bare empty-interval tick `42["name",[]]`
/// (such as Hummingbird's 200ms/500ms metric intervals when no event was recorded).
fn socketio_empty_tick(text: &str) -> bool {
    let Some(rest) = text.strip_prefix("42") else { return false };
    let rest = match rest.strip_prefix('/') {
        Some(ns) => match ns.split_once(',') {
            Some((_, tail)) => tail,
            None => return false,
        },
        None => rest,
    };
    let rest = rest.trim_start_matches(|c: char| c.is_ascii_digit());
    let Ok(Value::Array(packet)) = serde_json::from_str::<Value>(rest) else { return false };
    packet.len() == 2 && packet[0].is_string() && packet[1].as_array().is_some_and(Vec::is_empty)
}

fn response(value: Value) -> io::Result<WebResponse> {
    let body = serde_json::to_vec(&value)?;
    if body.len() > 65_536 {
        return Err(invalid("hosted response byte bound exceeded"));
    }
    Ok(WebResponse {
        result: WebResult::Content {
            status: 200,
            mime_type: "application/json".into(),
            encoding: String::new(),
            language: String::new(),
            etag: None,
            body,
            download_name: None,
        },
        headers: vec![],
        set_cookies: vec![],
    })
}
impl Pool {
    fn terminate(&mut self, id: &str) {
        if let Some(state) = self.lifecycle.get(id) {
            let op = vocabulary::Operation {
                phase: 2,
                command: 0,
                id: vec![],
                binding: vec![],
                preimage: vec![],
            };
            let ctx = vocabulary::Context {
                current: false,
                retained: false,
                budget: false,
                acknowledged: false,
                ended: true,
                response: vec![],
            };
            if let Ok(state) = vocabulary::derive(state, &ctx, &op) {
                self.lifecycle.insert(id.to_owned(), state);
            }
        }
        self.channels.insert(id.to_owned(), None);
    }
    fn purge_expired(&mut self) {
        let ids: Vec<_> = self
            .channels
            .iter()
            .filter_map(|(id, c)| {
                c.as_ref()
                    .filter(|c| Instant::now() >= c.expires)
                    .map(|_| id.clone())
            })
            .collect();
        for id in ids {
            self.terminate(&id);
        }
    }
    /// The existing RPC actor waits on the nearest custody expiry as well as
    /// its command queue. Idle channels therefore release capabilities without
    /// requiring another application request; terminal IDs remain retained.
    pub(crate) async fn receive_command<T>(
        &mut self,
        receiver: &mut tokio::sync::mpsc::Receiver<T>,
    ) -> Option<T> {
        loop {
            self.purge_expired();
            let next = self
                .channels
                .values()
                .filter_map(|c| c.as_ref().map(|c| c.expires))
                .min();
            match next {
                None => return receiver.recv().await,
                Some(deadline) => tokio::select! {
                    biased;
                    _=tokio::time::sleep_until(tokio::time::Instant::from_std(deadline))=>{},
                    command=receiver.recv()=>return command,
                },
            }
        }
    }

    fn acknowledge(
        &mut self,
        id: &str,
        operation: &vocabulary::Operation,
        custody: &Custody,
        result: &Value,
    ) -> io::Result<()> {
        let bytes =
            serde_json::to_vec(&json!({"nativeReceipt":custody.receipt,"response":result}))?;
        crate::dispatch_native::write_new(&custody.directory, "hosted-receipt.json", &bytes)?;
        let mut op = operation.clone();
        op.phase = 1;
        let ctx = vocabulary::Context {
            current: false,
            retained: true,
            budget: true,
            acknowledged: true,
            ended: false,
            response: bytes,
        };
        let state = self
            .lifecycle
            .get(id)
            .ok_or_else(|| invalid("hosted pending lifecycle absent"))?;
        let settled = vocabulary::derive(state, &ctx, &op).map_err(invalid)?;
        self.lifecycle.insert(id.to_owned(), settled);
        Ok(())
    }
    pub(crate) async fn execute(
        &mut self,
        session: &minidregg_spk_rpc::web_session_capnp::web_session::Client,
        binding: &SessionBinding,
        request: &WebRequest,
        custody: &Custody,
        deadline: Instant,
    ) -> io::Result<WebResponse> {
        let body = &request
            .body
            .as_ref()
            .ok_or_else(|| invalid("hosted descriptor body absent"))?
            .bytes;
        let parsed = descriptor(body).map_err(invalid)?;
        self.purge_expired();
        let id = string(&parsed, "channel").to_owned();
        let command = vocabulary::command(string(&parsed, "op")).map_err(invalid)?;
        let operation = vocabulary::Operation {
            phase: 0,
            command,
            id: custody.operation.clone(),
            binding: binding_bytes(binding, &request.path_and_query)?,
            preimage: body.clone(),
        };
        let is_open = string(&parsed, "op") == "open";
        let budget = if is_open {
            self.channels.values().filter(|c| c.is_some()).count() < vocabulary::MAX_CHANNELS
                && self.lifecycle.len() < vocabulary::MAX_CHANNEL_IDS
        } else {
            self.channels.get(&id).is_some_and(|c| c.is_some())
        };
        let ctx = vocabulary::Context {
            current: !custody.admission.is_empty(),
            retained: custody.retained == *body,
            budget,
            acknowledged: false,
            ended: false,
            response: vec![],
        };
        let state = self.lifecycle.get(&id).cloned().unwrap_or_default();
        let pending = match vocabulary::derive(&state, &ctx, &operation) {
            Ok(state) => state,
            Err(reason) => {
                if reason == "bindingIsolation" {
                    self.terminate(&id);
                }
                return Err(invalid(reason));
            }
        };
        let emitted = pending
            .emitted
            .clone()
            .ok_or_else(|| invalid("derived hosted emission absent"))?;
        self.lifecycle.insert(id.clone(), pending);
        let d = descriptor(&emitted.preimage).map_err(invalid)?;
        let op = vocabulary::command_name(emitted.command).map_err(invalid)?;
        if op == "open" {
            self.channels.insert(id.clone(), None);
            let left = Duration::from_millis(number(&d, "deadlineMs") as u64)
                .min(deadline.saturating_duration_since(Instant::now()));
            let opened = open_web_socket(
                session,
                &WebSocketOpen {
                    path_and_query: request.path_and_query.clone(),
                    context: request.context.clone(),
                    protocols: vec![],
                },
                left,
            )
            .await
            .map_err(io::Error::other)?;
            let result = json!({"version":1,"channel":id,"op":op,"frames":[]});
            self.acknowledge(&id, &operation, custody, &result)?;
            self.channels.insert(
                id.clone(),
                Some(Channel {
                    protocol: string(&d, "protocol").to_owned(),
                    expires: Instant::now()
                        + Duration::from_millis(vocabulary::CHANNEL_LIFETIME_MS),
                    socket: opened,
                    buffered: vec![],
                    fragment: vec![],
                    fragmenting: false,
                    ids: HashSet::new(),
                    max_frames: number(&d, "maxFrames"),
                    max_bytes: number(&d, "maxBytes"),
                }),
            );
            return response(result);
        }
        // Taking the channel makes every interrupted/uncertain command terminal.
        // No failed send, timeout or reconnect implicitly restores its socket.
        let channel = self
            .channels
            .get_mut(&id)
            .ok_or_else(|| invalid("hosted channel absent"))?;
        let mut channel = channel
            .take()
            .ok_or_else(|| invalid("hosted channel uncertain or closed"))?;
        if Instant::now() >= channel.expires {
            return Err(invalid("hosted channel lifetime exhausted"));
        }
        let deadline = deadline.min(channel.expires);
        let mut result = json!({"version":1,"channel":id,"op":op,"frames":[]});
        match op {
            "send" => {
                let bytes = channel.send_preimage(string(&d, "text"), custody)?;
                send_to_app(&channel.socket.to_app, &bytes)
                    .await
                    .map_err(io::Error::other)?;
            }
            "receive" => {
                let count = number(&d, "maxFrames").min(channel.max_frames);
                let limit = number(&d, "maxBytes").min(channel.max_bytes);
                let deadline = (Instant::now()
                    + Duration::from_millis(number(&d, "deadlineMs") as u64))
                .min(deadline);
                if count == 0 || limit == 0 {
                    return Err(invalid("hosted cumulative channel budget exhausted"));
                }
                // A socket.io receive may name the events it awaits: other event packets
                // ("42[name, ...]") are drained, never delivered; engine.io control and
                // connect/disconnect packets always pass.
                let events: Option<Vec<String>> = d["condition"]["events"].as_array().map(|a| {
                    a.iter().filter_map(Value::as_str).map(str::to_owned).collect()
                });
                let socketio = channel.protocol.starts_with("socket.io-");
                let keep = |text: &str| -> bool {
                    let (Some(events), true) = (events.as_ref(), socketio) else { return true };
                    !socketio_empty_tick(text)
                        && socketio_event(text).is_none_or(|name| events.iter().any(|e| *e == name))
                };
                let text = match channel.next_text(deadline, limit, count, &keep).await {
                    Ok(text) => Some(text),
                    Err(error) if error.kind() == io::ErrorKind::TimedOut => None,
                    Err(error) => return Err(error),
                };
                if let Some(text) = text {
                    result["frames"] = json!([text]);
                }
                // Early return: typed SDK correlation can issue a separately
                // admitted pong or continue within its remaining budget.
            }
            "rendezvous" => {
                let bytes = channel.send_preimage(string(&d, "text"), custody)?;
                let http = crate::dispatch_web_input::hosted_http(
                    &d["http"],
                    binding,
                    custody.api_prefix.as_deref(),
                )?;
                crate::dispatch_native::write_new(
                    &custody.directory,
                    "hosted-http.json",
                    &serde_json::to_vec(&d["http"])?,
                )?;
                let left = Duration::from_millis(number(&d, "deadlineMs") as u64)
                    .min(deadline.saturating_duration_since(Instant::now()));
                // Wait only for byte-stream delivery, never the DDP method result.
                // The pending login and HTTP half execute concurrently in the app;
                // registration bytes are released first to avoid a pre-registration POST.
                send_to_app(&channel.socket.to_app, &bytes)
                    .await
                    .map_err(io::Error::other)?;
                let reply = dispatch_web(session, &http, number(&d, "maxBytes"), left)
                    .await
                    .map_err(io::Error::other)?;
                let raw = crate::http_response::serialize(&reply, false)?;
                let boundary = raw
                    .windows(4)
                    .position(|w| w == b"\r\n\r\n")
                    .ok_or_else(|| invalid("hosted HTTP response framing"))?;
                let status = std::str::from_utf8(&raw[..boundary])
                    .ok()
                    .and_then(|s| s.split_whitespace().nth(1))
                    .and_then(|s| s.parse::<u16>().ok())
                    .ok_or_else(|| invalid("hosted HTTP response status"))?;
                result["httpStatus"] = json!(status);
                result["httpBodyHex"] = json!(crate::canonical::hex(&raw[boundary + 4..]));
            }
            "close" => {}
            _ => return Err(invalid("hosted operation absent from vocabulary")),
        }
        let response = response(result.clone())?;
        self.acknowledge(&id, &operation, custody, &result)?;
        if self.lifecycle.get(&id).is_some_and(vocabulary::socket_live) {
            self.channels.insert(id, Some(channel));
        }
        Ok(response)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::DirBuilderExt;
    #[test]
    fn descriptor_is_bounded_and_method_shape_is_closed() {
        let valid = br#"{"version":1,"op":"send","channel":"c-1","text":"{\"msg\":\"ping\"}"}"#;
        assert!(descriptor(valid).is_ok());
        let bad = String::from_utf8(valid.to_vec())
            .unwrap()
            .replace("\"send\"", "\"send-anything\"");
        assert!(descriptor(bad.as_bytes()).is_err());
        assert!(descriptor(br#"{"version":1,"op":"close","channel":"../other"}"#).is_err());
        assert!(descriptor(br#"{"version":1,"op":"close","channel":"c","subject":2}"#).is_err());
    }
    struct NoSession;
    impl minidregg_spk_rpc::grain_capnp::ui_session::Server for NoSession {}
    impl minidregg_spk_rpc::web_session_capnp::web_session::Server for NoSession {}
    struct FailingStream(std::sync::Arc<std::sync::atomic::AtomicUsize>);
    impl minidregg_spk_rpc::web_session_capnp::web_session::web_socket_stream::Server
        for FailingStream
    {
        async fn send_bytes(
            self: capnp::capability::Rc<Self>,
            _params: minidregg_spk_rpc::web_session_capnp::web_session::web_socket_stream::SendBytesParams,
        ) -> capnp::Result<()> {
            self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            Err(capnp::Error::failed("intentional lost send reply".into()))
        }
    }
    struct RegisterStream(std::sync::Arc<std::sync::atomic::AtomicBool>);
    impl minidregg_spk_rpc::web_session_capnp::web_session::web_socket_stream::Server
        for RegisterStream
    {
        async fn send_bytes(
            self: capnp::capability::Rc<Self>,
            _:minidregg_spk_rpc::web_session_capnp::web_session::web_socket_stream::SendBytesParams,
        ) -> capnp::Result<()> {
            self.0.store(true, std::sync::atomic::Ordering::SeqCst);
            Ok(())
        }
    }
    struct LoginSession(std::sync::Arc<std::sync::atomic::AtomicBool>);
    impl minidregg_spk_rpc::grain_capnp::ui_session::Server for LoginSession {}
    impl minidregg_spk_rpc::web_session_capnp::web_session::Server for LoginSession {
        async fn post(
            self: capnp::capability::Rc<Self>,
            params: minidregg_spk_rpc::web_session_capnp::web_session::PostParams,
            mut results: minidregg_spk_rpc::web_session_capnp::web_session::PostResults,
        ) -> capnp::Result<()> {
            assert!(self.0.load(std::sync::atomic::Ordering::SeqCst));
            let params = params.get()?;
            assert_eq!(params.get_path()?.to_str()?, ".sandstorm-login");
            assert_eq!(params.get_content()?.get_content()?, b"token");
            let mut content = results.get().init_content();
            content.set_status_code(
                minidregg_spk_rpc::web_session_capnp::web_session::response::SuccessCode::Ok,
            );
            content.set_mime_type("text/plain");
            content.init_body().set_bytes(b"ok");
            Ok(())
        }
    }
    fn binding() -> SessionBinding {
        SessionBinding {
            app: 1,
            process_generation: 2,
            session_resource: 3,
            session_generation: "4".into(),
            subject: 5,
            projection_fingerprint: [6; 32],
            ticket_resource: None,
            kind: crate::rpc_adapter::SessionKind::Web,
            params: minidregg_spk_rpc::SessionParameters {
                identity_id: [7; 32],
                display_name: "member".into(),
                preferred_handle: "member".into(),
                permissions: vec![true],
                tab_id: vec![],
                base_path: "https://member.example.test".into(),
                user_agent: "Mini".into(),
                acceptable_languages: vec![],
            },
        }
    }
    fn channel(
        _binding: SessionBinding,
        counter: std::sync::Arc<std::sync::atomic::AtomicUsize>,
    ) -> (Channel, tokio::sync::mpsc::Sender<Vec<u8>>) {
        let (tx, rx) = tokio::sync::mpsc::channel(16);
        (
            Channel {
                protocol: "ddp-v1".into(),
                expires: Instant::now() + Duration::from_secs(30),
                socket: WebSocketSession {
                    protocols: vec![],
                    to_app: capnp_rpc::new_client(FailingStream(counter)),
                    from_app: rx,
                },
                buffered: vec![],
                fragment: vec![],
                fragmenting: false,
                ids: HashSet::new(),
                max_frames: 64,
                max_bytes: 65536,
            },
            tx,
        )
    }
    fn request(value: Value) -> WebRequest {
        WebRequest {
            method: minidregg_spk_rpc::Method::HostedConversation,
            path_and_query: "websocket".into(),
            context: Default::default(),
            body: Some(minidregg_spk_rpc::Body {
                mime_type: "application/json".into(),
                encoding: String::new(),
                bytes: serde_json::to_vec(&value).unwrap(),
            }),
            dav: Default::default(),
        }
    }
    #[test]
    fn hosted_receiving_keeps_intervening_frames_and_refuses_changed_generation() {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        tokio::task::LocalSet::new().block_on(&runtime,async {
            let counter=std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
            let binding=binding();let (channel,tx)=channel(binding.clone(),counter.clone());
            let mut pool=Pool::default();
            pool.lifecycle.insert("c".into(),vocabulary::State {status:1,binding:binding_bytes(&binding,"websocket").unwrap(),..Default::default()});
            pool.channels.insert("c".into(),Some(channel));
            let first=r#"{"msg":"updated","methods":["m"]}"#;
            let second=r#"{"msg":"result","id":"m","result":null}"#;
            let mut raw=vec![0x81,first.len() as u8];raw.extend(first.as_bytes());
            raw.extend([0x81,second.len() as u8]);raw.extend(second.as_bytes());
            tx.send(raw[..3].to_vec()).await.unwrap();tx.send(raw[3..].to_vec()).await.unwrap();
            let req=request(json!({"version":1,"op":"receive","channel":"c","condition":{"msg":"any"},"maxFrames":64,"maxBytes":65536,"deadlineMs":100}));
            let root=std::env::temp_dir().join(format!("cx-hosted-receive-{}-{}",std::process::id(),std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
            std::fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
            let session=capnp_rpc::new_client(NoSession);
            for (index,expected) in [first,second].into_iter().enumerate() {
                let directory=root.join(index.to_string());std::fs::DirBuilder::new().mode(0o700).create(&directory).unwrap();
                let custody=Custody::fixture(directory,&index.to_string(),&req.body.as_ref().unwrap().bytes);
                let result=pool.execute(&session,&binding,&req,&custody,Instant::now()+Duration::from_secs(1)).await.unwrap();
                let WebResult::Content {body,..}=result.result else {panic!("content expected")};
                let body:Value=serde_json::from_slice(&body).unwrap();assert_eq!(body["frames"][0],expected);
                assert!(pool.lifecycle["c"].receipt.is_some());
            }
            let directory=root.join("changed");std::fs::DirBuilder::new().mode(0o700).create(&directory).unwrap();
            let custody=Custody::fixture(directory,"changed",&req.body.as_ref().unwrap().bytes);
            let mut changed=binding.clone();changed.session_generation="5".into();
            assert!(pool.execute(&session,&changed,&req,&custody,Instant::now()+Duration::from_secs(1)).await.is_err());
            assert!(pool.channels["c"].is_none());assert!(pool.lifecycle["c"].ended);
            assert_eq!(counter.load(std::sync::atomic::Ordering::SeqCst),0);
            std::fs::remove_dir_all(root).unwrap();
        });
    }

    #[test]
    fn hosted_derived_lifecycle_checks_authority_preimage_and_exact_receipt() {
        let state = vocabulary::State::default();
        let op = vocabulary::Operation {
            phase: 0,
            command: 0,
            id: vec![1],
            binding: vec![2],
            preimage: vec![3],
        };
        let mut ctx = vocabulary::Context {
            current: false,
            retained: true,
            budget: true,
            acknowledged: false,
            ended: false,
            response: vec![],
        };
        assert_eq!(
            vocabulary::derive(&state, &ctx, &op).unwrap_err(),
            "currentAuthority"
        );
        ctx.current = true;
        ctx.retained = false;
        assert_eq!(
            vocabulary::derive(&state, &ctx, &op).unwrap_err(),
            "exactPreimage"
        );
        ctx.retained = true;
        let pending = vocabulary::derive(&state, &ctx, &op).unwrap();
        assert_eq!(pending.emitted.as_ref(), Some(&op));
        assert!(pending.receipt.is_none());
        assert!(vocabulary::derive(&pending, &ctx, &op).is_err());
        let mut ack = op.clone();
        ack.phase = 1;
        assert_eq!(
            vocabulary::derive(&pending, &ctx, &ack).unwrap_err(),
            "uncertainCompletion"
        );
        ctx.acknowledged = true;
        ctx.response = vec![4];
        ack.preimage = vec![9];
        assert_eq!(
            vocabulary::derive(&pending, &ctx, &ack).unwrap_err(),
            "originalIntent"
        );
        ack.preimage = op.preimage;
        let settled = vocabulary::derive(&pending, &ctx, &ack).unwrap();
        assert!(vocabulary::socket_live(&settled));
        assert_eq!(settled.receipt.unwrap().bytes, vec![4]);
    }
    #[test]
    fn hosted_rendezvous_preadmits_both_legs_and_posts_without_waiting_ddp_result() {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        tokio::task::LocalSet::new().block_on(&runtime,async {
            let registered=std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
            let binding=binding();let (mut channel,_)=channel(binding.clone(),Default::default());
            channel.socket.to_app=capnp_rpc::new_client(RegisterStream(registered.clone()));
            let mut pool=Pool::default();pool.channels.insert("c".into(),Some(channel));
            pool.lifecycle.insert("c".into(),vocabulary::State {status:1,binding:binding_bytes(&binding,"websocket").unwrap(),..Default::default()});
            let req=request(json!({"version":1,"op":"rendezvous","channel":"c","text":"{\"msg\":\"method\",\"method\":\"loginWithSandstorm\",\"id\":\"login-1\",\"params\":[\"token\"]}",
                "http":{"method":"POST","path":".sandstorm-login","query":"","headers":[{"name":"content-type","value":"application/x-sandstorm-login-token"}],"bodyHex":"746f6b656e"},"maxFrames":64,"maxBytes":65536,"deadlineMs":1000}));
            let directory=std::env::temp_dir().join(format!("cx-hosted-login-{}-{}",std::process::id(),std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
            std::fs::DirBuilder::new().mode(0o700).create(&directory).unwrap();
            let custody=Custody::fixture(directory.clone(),"login-1",&req.body.as_ref().unwrap().bytes);
            let session=capnp_rpc::new_client(LoginSession(registered));
            let response=pool.execute(&session,&binding,&req,&custody,Instant::now()+Duration::from_secs(1)).await.unwrap();
            let WebResult::Content {body,..}=response.result else {panic!("content expected")};
            assert_eq!(serde_json::from_slice::<Value>(&body).unwrap()["httpStatus"],200);
            for name in ["hosted-admitted-descriptor.bin","hosted-frame.bin","hosted-http.json","hosted-receipt.json"] {assert!(directory.join(name).is_file());}
            std::fs::remove_dir_all(directory).unwrap();
        });
    }
    #[test]
    fn hosted_expiry_purges_socket_but_never_reuses_id() {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        tokio::task::LocalSet::new().block_on(&runtime, async {
            let b = binding();
            let (mut channel, _) = channel(b.clone(), Default::default());
            channel.expires = Instant::now() - Duration::from_secs(1);
            let mut pool = Pool::default();
            pool.channels.insert("expired".into(), Some(channel));
            pool.lifecycle.insert(
                "expired".into(),
                vocabulary::State {
                    status: 1,
                    binding: binding_bytes(&b, "websocket").unwrap(),
                    ..Default::default()
                },
            );
            pool.purge_expired();
            assert!(pool.channels["expired"].is_none());
            assert!(pool.lifecycle["expired"].ended);
            let op = vocabulary::Operation {
                phase: 0,
                command: 0,
                id: vec![1],
                binding: vec![2],
                preimage: vec![3],
            };
            let ctx = vocabulary::Context {
                current: true,
                retained: true,
                budget: true,
                acknowledged: false,
                ended: false,
                response: vec![],
            };
            assert!(vocabulary::derive(&pool.lifecycle["expired"], &ctx, &op).is_err());
        });
    }
    #[test]
    fn hosted_idle_actor_drops_expired_socket_without_a_request() {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        tokio::task::LocalSet::new().block_on(&runtime, async {
            let b = binding();
            let (mut channel, app_sender) = channel(b.clone(), Default::default());
            channel.expires = Instant::now() + Duration::from_millis(20);
            let mut pool = Pool::default();
            pool.channels.insert("idle".into(), Some(channel));
            pool.lifecycle.insert(
                "idle".into(),
                vocabulary::State {
                    status: 1,
                    binding: binding_bytes(&b, "websocket").unwrap(),
                    ..Default::default()
                },
            );
            let (_commands, mut queue) = tokio::sync::mpsc::channel::<()>(1);
            // No command is sent. Dropping the app receiver is direct evidence
            // that actor expiry released the physical socket capability.
            tokio::select! {
                _=pool.receive_command(&mut queue)=>panic!("queue unexpectedly ended"),
                _=tokio::time::timeout(Duration::from_secs(1),app_sender.closed())=>{},
            }
            assert!(app_sender.is_closed());
            assert!(pool.channels["idle"].is_none());
            assert!(pool.lifecycle["idle"].ended);
        });
    }
    #[test]
    fn hosted_wire_fragments_and_pong_noise_consume_budget() {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        tokio::task::LocalSet::new().block_on(&runtime, async {
            let (mut channel, tx) = channel(binding(), Default::default());
            channel.max_frames = 2;
            tx.send(vec![0x8a, 0, 0x8a, 0, 0x81, 2, b'{', b'}'])
                .await
                .unwrap();
            assert!(channel
                .next_text(Instant::now() + Duration::from_secs(1), 100, 64, &|_| true)
                .await
                .is_err());
            assert_eq!(channel.max_frames, 0);
            assert_eq!(channel.max_bytes, 65532);
        });
    }
    #[test]
    fn a_filtered_receive_drains_unawaited_events_without_charging_the_budget() {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        tokio::task::LocalSet::new().block_on(&runtime, async {
            let (mut channel, tx) = channel(binding(), Default::default());
            channel.max_frames = 1;
            let text_frame = |t: &str| [vec![0x81, t.len() as u8], t.as_bytes().to_vec()].concat();
            let mut wire = vec![];
            for _ in 0..5 {
                wire.extend(text_frame(r#"42["view_totals",3]"#));
            }
            wire.extend(text_frame(r#"42["locations",[{"event":"e"}]]"#));
            tx.send(wire).await.unwrap();
            let keep = |t: &str| socketio_event(t).is_none_or(|n| n == "locations");
            let text = channel
                .next_text(Instant::now() + Duration::from_secs(1), 1000, 64, &keep)
                .await
                .unwrap();
            assert_eq!(text, r#"42["locations",[{"event":"e"}]]"#);
            assert_eq!(channel.max_frames, 0);
        });
        assert_eq!(socketio_event(r#"42["hits",[]]"#).as_deref(), Some("hits"));
        assert!(socketio_empty_tick(r#"42["hits",[]]"#));
        assert!(!socketio_empty_tick(r#"42["hits",[{"timestamp":"t"}]]"#));
        assert!(!socketio_empty_tick(r#"42["view_totals",3]"#));
        assert_eq!(socketio_event(r#"42/admin,["x"]"#).as_deref(), Some("x"));
        assert_eq!(socketio_event(r#"427["ack",1]"#).as_deref(), Some("ack"));
        assert_eq!(socketio_event("40"), None);
        assert_eq!(socketio_event("2"), None);
    }
    #[test]
    fn hosted_uncertain_send_retains_exact_frame_and_never_replays() {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        tokio::task::LocalSet::new().block_on(&runtime, async {
            let counter = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
            let binding = binding();
            let (channel, _tx) = channel(binding.clone(), counter.clone());
            let mut pool = Pool::default();
            pool.lifecycle.insert(
                "c".into(),
                vocabulary::State {
                    status: 1,
                    binding: binding_bytes(&binding, "websocket").unwrap(),
                    ..Default::default()
                },
            );
            pool.channels.insert("c".into(), Some(channel));
            let text = r#"{"msg":"method","method":"write","id":"m","params":[]}"#;
            let req = request(json!({"version":1,"op":"send","channel":"c","text":text}));
            let directory = std::env::temp_dir().join(format!(
                "cx-hosted-send-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            std::fs::DirBuilder::new()
                .mode(0o700)
                .create(&directory)
                .unwrap();
            crate::dispatch_native::private_dir(&directory).unwrap();
            let custody = Custody::fixture(
                directory.clone(),
                "send-1",
                &req.body.as_ref().unwrap().bytes,
            );
            let session = capnp_rpc::new_client(NoSession);
            for _ in 0..2 {
                assert!(pool
                    .execute(
                        &session,
                        &binding,
                        &req,
                        &custody,
                        Instant::now() + Duration::from_secs(1)
                    )
                    .await
                    .is_err());
            }
            assert_eq!(counter.load(std::sync::atomic::Ordering::SeqCst), 1);
            assert!(pool.channels["c"].is_none());
            let frame = std::fs::read(directory.join("hosted-frame.bin")).unwrap();
            assert_eq!(frame[0], 0x81);
            let mask = &frame[2..6];
            let payload: Vec<_> = frame[6..]
                .iter()
                .enumerate()
                .map(|(i, b)| b ^ mask[i % 4])
                .collect();
            assert_eq!(payload, text.as_bytes());
            std::fs::remove_dir_all(directory).unwrap();
        });
    }
}
