//! Local transport lifecycle control, not a Host operation or public route.
//! A random process instance and exact config/image hashes pin each drain.
use crate::transport;
use ring::rand::{SecureRandom, SystemRandom};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs;
use std::io;
use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
use std::os::unix::net::UnixListener;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

const FORMAT: &str = "mini-operator-drain-v1";
const MAX_CONTROL_FRAME: usize = 4096;
fn nonce() -> Result<String, String> {
    let mut bytes = [0; 32];
    SystemRandom::new()
        .fill(&mut bytes)
        .map_err(|_| "cannot obtain process control nonce")?;
    Ok(crate::hex(&bytes))
}
fn digest(bytes: &[u8]) -> String {
    crate::hex(&Sha256::digest(bytes))
}
fn hex_digest(value: &str) -> bool {
    value.len() == 64
        && mini_sdk::hex::is_lower(value)
}

pub(crate) struct State {
    pub(crate) close: AtomicBool,
    pub(crate) admission_closed: AtomicBool,
    pub(crate) drained: AtomicBool,
    pub(crate) live: AtomicUsize,
    pub(crate) host_pid: AtomicU32,
    stop_control: AtomicBool,
    instance: String,
    config_sha256: String,
    host_sha256: String,
}
impl State {
    fn answer(&self, request: &Value) -> Result<Value, String> {
        let object = request
            .as_object()
            .ok_or("control request must be an object")?;
        let expected = [
            "format",
            "action",
            "instanceId",
            "processId",
            "configSha256",
            "hostSha256",
            "requestNonce",
        ];
        if object.len() != expected.len() || expected.iter().any(|key| !object.contains_key(*key)) {
            return Err("invalid control request fields".into());
        }
        let request_nonce = request["requestNonce"]
            .as_str()
            .filter(|s| hex_digest(s))
            .ok_or("invalid request nonce")?;
        if request["format"] != FORMAT
            || request["configSha256"] != self.config_sha256
            || request["hostSha256"] != self.host_sha256
        {
            return Err("operator control profile pin mismatch".into());
        }
        let action = request["action"].as_str().ok_or("invalid control action")?;
        if !matches!(action, "status" | "drain") {
            return Err("unknown operator control action".into());
        }
        let has_pin = !request["instanceId"].is_null() || !request["processId"].is_null();
        if (action == "drain" || has_pin)
            && (request["instanceId"] != self.instance
                || request["processId"].as_u64() != Some(std::process::id() as u64))
        {
            return Err("operator process instance pin mismatch".into());
        }
        if action == "drain" {
            self.close.store(true, Ordering::Release);
        }
        let drained = self.drained.load(Ordering::Acquire);
        let closed = self.admission_closed.load(Ordering::Acquire);
        let phase = if drained {
            "drained"
        } else if closed {
            "draining"
        } else if self.close.load(Ordering::Acquire) {
            "closing"
        } else {
            "serving"
        };
        Ok(json!({
            "format": FORMAT, "processId": std::process::id(), "instanceId": self.instance,
            "configSha256": self.config_sha256, "hostSha256": self.host_sha256,
            "requestNonce": request_nonce, "phase": phase, "admissionClosed": closed,
            "drained": drained, "unresolvedConnections": self.live.load(Ordering::Acquire),
            "acceptedConnections": if drained { Some(0) } else { None::<usize> },
            "queuedRequests": if drained { Some(0) } else { None::<usize> },
            "activeRequests": if drained { Some(0) } else { None::<usize> },
            "hostProcessId": self.host_pid.load(Ordering::Acquire)
        }))
    }
}

pub(crate) struct Control {
    pub(crate) state: Arc<State>,
    thread: Option<JoinHandle<Result<(), String>>>,
}
impl Control {
    pub(crate) fn start(
        socket: &Path,
        config: &[u8],
        host_hash: &[u8; 32],
        host_pid: u32,
    ) -> Result<Self, String> {
        let path = socket.with_extension("control");
        transport::clear_stale_socket(&path)?;
        let listener =
            UnixListener::bind(&path).map_err(|e| format!("cannot bind operator control: {e}"))?;
        let metadata = fs::symlink_metadata(&path).map_err(|e| e.to_string())?;
        let guard = SocketGuard(path, metadata.dev(), metadata.ino());
        fs::set_permissions(&guard.0, fs::Permissions::from_mode(0o600))
            .map_err(|e| e.to_string())?;
        listener.set_nonblocking(true).map_err(|e| e.to_string())?;
        let state = Arc::new(State {
            close: AtomicBool::new(false),
            admission_closed: AtomicBool::new(false),
            drained: AtomicBool::new(false),
            live: AtomicUsize::new(0),
            host_pid: AtomicU32::new(host_pid),
            stop_control: AtomicBool::new(false),
            instance: nonce()?,
            config_sha256: digest(config),
            host_sha256: crate::hex(host_hash),
        });
        let cloned = state.clone();
        let thread = std::thread::Builder::new().name("mini-operator-control".into()).stack_size(256 * 1024).spawn(move || {
            let _guard = guard;
            while !cloned.stop_control.load(Ordering::Acquire) {
                match listener.accept() {
                    Ok((mut stream, _)) => {
                        if transport::peer_uid(&stream).ok() != Some(mini_sdk::private::euid()) { continue; }
                        if stream.set_nonblocking(true).is_err() { continue; }
                        let request = transport::read_frame_bounded(&mut transport::DeadlinePipe { reader: &mut stream, deadline: Instant::now() + Duration::from_millis(200) }, MAX_CONTROL_FRAME);
                        let Ok(Some(bytes)) = request else { continue; };
                        let value = serde_json::from_slice::<Value>(&bytes);
                        let answer = match value {
                            Ok(value) => cloned.answer(&value).unwrap_or_else(|reason| json!({"format":FORMAT,"refused":reason,"requestNonce":value.get("requestNonce")})),
                            Err(_) => json!({"format":FORMAT,"refused":"invalid control JSON"}),
                        };
                        if let Ok(bytes) = serde_json::to_vec(&answer) {
                            let _ = transport::write_frame(&mut transport::DeadlinePipeWrite { writer: &mut stream, deadline: Instant::now() + Duration::from_millis(200) }, &bytes);
                        }
                    }
                    Err(e) if e.kind() == io::ErrorKind::WouldBlock => std::thread::sleep(Duration::from_millis(10)),
                    Err(e) if e.kind() == io::ErrorKind::Interrupted => {},
                    Err(e) => {
                        cloned.close.store(true, Ordering::Release);
                        return Err(format!("operator control accept failed: {e}"));
                    }
                }
            }
            Ok(())
        }).map_err(|e| format!("cannot start operator control: {e}"))?;
        Ok(Self {
            state,
            thread: Some(thread),
        })
    }
    /// The Host stays owned and alive while admission remains permanently
    /// closed. Only an explicit service restart opens a new process instance.
    pub(crate) fn hold_closed(&mut self) -> Result<(), String> {
        loop {
            if self.thread.as_ref().is_some_and(JoinHandle::is_finished) {
                return self
                    .thread
                    .take()
                    .unwrap()
                    .join()
                    .map_err(|_| "operator control panicked")?
                    .and(Err("operator control ended".into()));
            }
            std::thread::sleep(Duration::from_millis(100));
        }
    }
}
impl Drop for Control {
    fn drop(&mut self) {
        self.state.stop_control.store(true, Ordering::Release);
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}
struct SocketGuard(PathBuf, u64, u64);
impl Drop for SocketGuard {
    fn drop(&mut self) {
        if let Ok(metadata) = fs::symlink_metadata(&self.0) {
            if metadata.file_type().is_socket()
                && (metadata.dev(), metadata.ino()) == (self.1, self.2)
            {
                let _ = fs::remove_file(&self.0);
            }
        }
    }
}

fn request(socket: &Path, value: &Value) -> Result<Value, String> {
    let path = socket.with_extension("control");
    if !path.is_absolute() {
        return Err("operator control requires an absolute owner-private socket directory".into());
    }
    crate::fsio::check_private_socket(&path)?;
    let stopping = AtomicBool::new(false);
    let deadline = Instant::now() + Duration::from_secs(2);
    let mut stream = crate::public_proxy::connect(&path, &stopping, deadline)
        .map_err(|e| format!("operator control connect: {e}"))?;
    if transport::peer_uid(&stream)? != mini_sdk::private::euid() {
        return Err("operator control peer UID mismatch".into());
    }
    transport::write_frame(
        &mut transport::DeadlinePipeWrite {
            writer: &mut stream,
            deadline,
        },
        &serde_json::to_vec(value).map_err(|e| e.to_string())?,
    )
    .map_err(|e| format!("operator control request uncertain: {e}"))?;
    let response = transport::read_frame_bounded(
        &mut transport::DeadlinePipe {
            reader: &mut stream,
            deadline,
        },
        MAX_CONTROL_FRAME,
    )
    .map_err(|e| format!("operator control response uncertain: {e}"))?
    .ok_or("operator control closed without response")?;
    let response: Value = serde_json::from_slice(&response)
        .map_err(|e| format!("invalid operator control response: {e}"))?;
    if response["format"] != FORMAT || response["requestNonce"] != value["requestNonce"] {
        return Err("operator control response binding mismatch".into());
    }
    if let Some(reason) = response["refused"].as_str() {
        return Err(reason.to_string());
    }
    if response["configSha256"] != value["configSha256"]
        || response["hostSha256"] != value["hostSha256"]
    {
        return Err("operator control response profile mismatch".into());
    }
    if !value["instanceId"].is_null()
        && (response["instanceId"] != value["instanceId"]
            || response["processId"] != value["processId"])
    {
        return Err("operator control response process mismatch".into());
    }
    Ok(response)
}

pub(crate) fn command(
    socket: &Path,
    host: &Path,
    config: &Path,
    drain: Option<(&str, u32, u64)>,
) -> Result<(), String> {
    let config_bytes = transport::read_config(config)?;
    let host_hash = transport::host_image_sha256(host)?;
    if let Some((instance, _, timeout)) = drain {
        if !hex_digest(instance) || !(1..=3600).contains(&timeout) {
            return Err(
                "drain requires 64 lowercase hex instance and timeout-seconds 1..3600".into(),
            );
        }
    }
    let mut value = json!({
        "format":FORMAT, "action":if drain.is_some() {"drain"} else {"status"},
        "instanceId":drain.map(|d|d.0), "processId":drain.map(|d|d.1),
        "configSha256":digest(&config_bytes),"hostSha256":crate::hex(&host_hash),"requestNonce":nonce()?
    });
    let deadline = Instant::now() + Duration::from_secs(drain.map_or(0, |d| d.2));
    loop {
        let response = request(socket, &value)?;
        let drained = response["admissionClosed"] == true
            && response["drained"] == true
            && [
                "unresolvedConnections",
                "acceptedConnections",
                "queuedRequests",
                "activeRequests",
            ]
            .iter()
            .all(|field| response[*field].as_u64() == Some(0));
        if drain.is_none() || drained || Instant::now() >= deadline {
            println!(
                "{}",
                serde_json::to_string(&response).map_err(|e| e.to_string())?
            );
            return if drain.is_some() && !drained {
                Err("operator drain timed out; admission stays closed; retry this exact process instance".into())
            } else {
                Ok(())
            };
        }
        // The first drain stays effective even if later polling loses its
        // reply. Never select a new instance or reopen admission on timeout.
        value["action"] = json!("status");
        value["requestNonce"] = json!(nonce()?);
        std::thread::sleep(Duration::from_millis(50));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn state() -> State {
        State {
            close: AtomicBool::new(false),
            admission_closed: AtomicBool::new(false),
            drained: AtomicBool::new(false),
            live: AtomicUsize::new(2),
            host_pid: AtomicU32::new(99),
            stop_control: AtomicBool::new(false),
            instance: "a".repeat(64),
            config_sha256: "b".repeat(64),
            host_sha256: "c".repeat(64),
        }
    }
    fn request() -> Value {
        json!({"format":FORMAT,"action":"drain","instanceId":"a".repeat(64),"processId":std::process::id(),"configSha256":"b".repeat(64),"hostSha256":"c".repeat(64),"requestNonce":"d".repeat(64)})
    }
    #[test]
    fn wrong_control_pins_and_unknown_fields_never_close_admission() {
        for key in [
            "format",
            "action",
            "instanceId",
            "processId",
            "configSha256",
            "hostSha256",
            "requestNonce",
            "extra",
        ] {
            let state = state();
            let mut request = request();
            request[key] = json!("wrong");
            assert!(state.answer(&request).is_err(), "{key}");
            assert!(!state.close.load(Ordering::Acquire), "{key}");
        }
    }
    #[test]
    fn closed_is_not_drained_and_status_does_not_guess_empty_queue() {
        let state = state();
        let first = state.answer(&request()).unwrap();
        assert!(state.close.load(Ordering::Acquire));
        assert_eq!(first["phase"], "closing");
        assert_eq!(first["requestNonce"], "d".repeat(64));
        state.admission_closed.store(true, Ordering::Release);
        let second = state.answer(&request()).unwrap();
        assert_eq!(second["phase"], "draining");
        assert_eq!(second["unresolvedConnections"], 2);
        assert!(second["queuedRequests"].is_null());
        state.live.store(0, Ordering::Release);
        assert_eq!(
            state.answer(&request()).unwrap()["drained"],
            false,
            "zero connection snapshot alone cannot certify drain"
        );
        state.drained.store(true, Ordering::Release);
        let third = state.answer(&request()).unwrap();
        assert_eq!(third["phase"], "drained");
        for key in [
            "unresolvedConnections",
            "acceptedConnections",
            "queuedRequests",
            "activeRequests",
        ] {
            assert_eq!(third[key], 0);
        }
    }
    #[test]
    fn control_frame_bound_rejects_declared_large_frame_without_payload() {
        let bytes = 4097u32.to_le_bytes();
        let error =
            transport::read_frame_bounded(&mut bytes.as_slice(), MAX_CONTROL_FRAME).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    }
}
