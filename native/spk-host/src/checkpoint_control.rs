//! Physical checkpoint fencing at the resident's serialized receiving boundary.
//! This attenuates transport only; resume never mints participant authority.
use crate::hostd::Journal;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::UnixListener;
use std::path::{Path, PathBuf};
use std::time::Duration;

const PROTOCOL: &str = "mini-spk-checkpoint-control-v1";
fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}
fn digest(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Binding {
    pub app: String,
    pub generation: String,
    pub journal_dir: PathBuf,
    pub resident_config: PathBuf,
    pub resident_config_sha256: String,
    pub mini_config_sha256: String,
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Request {
    pub protocol: String,
    pub action: String,
    pub nonce_hex: String,
    pub binding: Binding,
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Intent {
    pub request: Request,
    pub journal_sha256: String,
}

fn retained(path: &Path) -> io::Result<Vec<u8>> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file()
        || meta.nlink() != 1
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.mode() & 0o777 != 0o600
        || meta.len() > 8192
    {
        return Err(invalid("checkpoint custody differs"));
    }
    let mut bytes = Vec::new();
    file.take(8193).read_to_end(&mut bytes)?;
    if bytes.len() > 8192 {
        return Err(invalid("checkpoint record grew"));
    }
    Ok(bytes)
}
fn publish(path: &Path, bytes: &[u8]) -> io::Result<()> {
    match retained(path) {
        Ok(old) if old == bytes => {
            return File::open(
                path.parent()
                    .ok_or_else(|| invalid("checkpoint parent absent"))?,
            )?
            .sync_all()
        }
        Ok(_) => return Err(invalid("checkpoint retry differs")),
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }
    // The exact prior bytes were checked while the same checkpoint lock is
    // held. Reuse hostd's atomic custody publication rather than another recipe.
    crate::hostd::atomic_write_locked(path, bytes)
}
pub(crate) fn checkpoint_lock(app_dir: &Path) -> io::Result<File> {
    let lock = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(app_dir.join(".checkpoint.lock"))?;
    let meta = lock.metadata()?;
    if !meta.is_file()
        || meta.nlink() != 1
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.mode() & 0o777 != 0o600
    {
        return Err(invalid("checkpoint lock custody differs"));
    }
    if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        return Err(io::Error::new(
            io::ErrorKind::WouldBlock,
            "checkpoint copy or resume already active",
        ));
    }
    Ok(lock)
}
pub(crate) fn refuse_retained_pause(journal: &Path) -> io::Result<()> {
    let parent = journal
        .parent()
        .ok_or_else(|| invalid("checkpoint app directory absent"))?;
    match fs::symlink_metadata(parent.join("checkpoint-pause.json")) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error),
        Ok(_) => Err(invalid(
            "retained app checkpoint pause requires exact recovery; no generation may reopen",
        )),
    }
}
pub(crate) struct CheckpointControl {
    listener: UnixListener,
    socket: PathBuf,
    binding: Binding,
    pause_path: PathBuf,
}
fn checkpoint_reply(status: &str, intent: &Intent) -> serde_json::Value {
    serde_json::json!({"protocol":PROTOCOL,"status":status,"intent":intent,"liveStreams":"closed; clients reopen under current Mini authority"})
}
impl CheckpointControl {
    pub fn bind(binding: Binding) -> io::Result<Self> {
        if !digest(&binding.resident_config_sha256) || !digest(&binding.mini_config_sha256) {
            return Err(invalid("checkpoint config pins invalid"));
        }
        let pause_path = binding
            .journal_dir
            .parent()
            .ok_or_else(|| invalid("checkpoint app directory absent"))?
            .join("checkpoint-pause.json");
        let socket = binding.journal_dir.join("checkpoint-control.sock");
        let listener = UnixListener::bind(&socket)?;
        fs::set_permissions(&socket, fs::Permissions::from_mode(0o600))?;
        Ok(Self {
            listener,
            socket,
            binding,
            pause_path,
        })
    }
    pub fn as_raw_fd(&self) -> libc::c_int {
        self.listener.as_raw_fd()
    }
    pub fn paused(&self) -> bool {
        fs::symlink_metadata(&self.pause_path).is_ok()
    }
    fn process(
        &self,
        request: Request,
        mut verify: impl FnMut() -> io::Result<()>,
        drain: impl FnOnce() -> io::Result<()>,
    ) -> io::Result<serde_json::Value> {
        if request.protocol != PROTOCOL
            || !digest(&request.nonce_hex)
            || request.binding != self.binding
            || !matches!(request.action.as_str(), "pause" | "resume")
        {
            return Err(invalid("checkpoint request binding differs"));
        }
        let _lock = checkpoint_lock(
            self.pause_path
                .parent()
                .ok_or_else(|| invalid("checkpoint parent absent"))?,
        )?;
        let path = self.binding.journal_dir.join(format!(
            "checkpoint-{}-{}.json",
            request.nonce_hex, request.action
        ));
        let mut pause_request = request.clone();
        pause_request.action = "pause".into();
        let resumed = self
            .binding
            .journal_dir
            .join(format!("checkpoint-{}-resume.json", request.nonce_hex));
        if request.action == "resume" {
            // A completed resume is historical acknowledgement. Later receiving
            // may advance the journal; it must not invalidate this exact retry.
            match retained(&self.pause_path) {
                Err(error) if error.kind() == io::ErrorKind::NotFound => {
                    let paused = self
                        .binding
                        .journal_dir
                        .join(format!("checkpoint-{}-pause.json", request.nonce_hex));
                    let bytes = retained(&paused)?;
                    let prior: Intent = serde_json::from_slice(&bytes)?;
                    if prior.request != pause_request || retained(&resumed)? != bytes {
                        return Err(invalid("checkpoint completed resume identity differs"));
                    }
                    File::open(
                        self.pause_path
                            .parent()
                            .ok_or_else(|| invalid("checkpoint parent absent"))?,
                    )?
                    .sync_all()?;
                    return Ok(checkpoint_reply("resumed", &prior));
                }
                Ok(_) => {}
                Err(error) => return Err(error),
            }
        } else if fs::symlink_metadata(&resumed).is_ok() {
            return Err(invalid("completed checkpoint nonce cannot pause again"));
        }
        verify()?;
        let record_hash = format!(
            "{:x}",
            Sha256::digest(retained(&self.binding.journal_dir.join("record.json"))?)
        );
        let intent = Intent {
            request: pause_request,
            journal_sha256: record_hash,
        };
        if request.action == "pause" {
            let bytes = serde_json::to_vec(&intent)?;
            publish(&self.pause_path, &bytes)?;
            // Marker survives a crash or unsuccessful drain before the receipt.
            drain()?;
            verify()?;
            publish(&path, &bytes)?;
        } else {
            let paused = self
                .binding
                .journal_dir
                .join(format!("checkpoint-{}-pause.json", request.nonce_hex));
            let bytes = retained(&paused)?;
            let prior: Intent = serde_json::from_slice(&bytes)?;
            if prior != intent {
                return Err(invalid("checkpoint journal changed during pause"));
            }
            match retained(&self.pause_path) {
                Ok(active) if active == bytes => {}
                Ok(_) => return Err(invalid("another checkpoint pause is active")),
                Err(error) => return Err(error),
            }
            // Exact acknowledgement is durable before releasing admission. A
            // crash in this gap keeps the app fenced until this exact retry.
            publish(&path, &bytes)?;
            fs::remove_file(&self.pause_path)?;
            File::open(
                self.pause_path
                    .parent()
                    .ok_or_else(|| invalid("checkpoint parent absent"))?,
            )?
            .sync_all()?;
        }
        Ok(checkpoint_reply(
            if request.action == "pause" {
                "paused"
            } else {
                "resumed"
            },
            &intent,
        ))
    }
    pub fn poll_once(
        &self,
        journal: &Journal,
        drain: impl FnOnce() -> io::Result<()>,
    ) -> io::Result<()> {
        let (mut stream, _) = self.listener.accept()?;
        if crate::http_entrance::peer_uid(&stream) != Some(unsafe { libc::geteuid() }) {
            return Ok(());
        }
        stream.set_read_timeout(Some(Duration::from_secs(2)))?;
        stream.set_write_timeout(Some(Duration::from_secs(2)))?;
        let result = (|| {
            let mut length = [0; 4];
            stream.read_exact(&mut length)?;
            let length = u32::from_le_bytes(length) as usize;
            if length == 0 || length > 4096 {
                return Err(invalid("checkpoint request exceeds bound"));
            }
            let mut bytes = vec![0; length];
            stream.read_exact(&mut bytes)?;
            self.process(
                serde_json::from_slice(&bytes)?,
                || journal.verify_dispatch_idle(),
                drain,
            )
        })();
        let reply = match result {
            Ok(reply) => reply,
            Err(error) => {
                serde_json::json!({"protocol":PROTOCOL,"status":"refused","reason":error.to_string(),"paused":self.paused()})
            }
        };
        let bytes = serde_json::to_vec(&reply)?;
        stream.write_all(&(bytes.len() as u32).to_le_bytes())?;
        stream.write_all(&bytes)
    }
}
impl Drop for CheckpointControl {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.socket);
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    fn fixture() -> (PathBuf, CheckpointControl, Request) {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root =
            std::env::temp_dir().join(format!("checkpoint-test-{}-{nonce}", std::process::id()));
        fs::create_dir(&root).unwrap();
        let journal = root.join("g7");
        fs::create_dir(&journal).unwrap();
        publish(&journal.join("record.json"), b"settled-native-record").unwrap();
        let binding = Binding {
            app: "500001".into(),
            generation: "7".into(),
            journal_dir: journal,
            resident_config: root.join("resident.json"),
            resident_config_sha256: "a".repeat(64),
            mini_config_sha256: "b".repeat(64),
        };
        let request = Request {
            protocol: PROTOCOL.into(),
            action: "pause".into(),
            nonce_hex: "c".repeat(64),
            binding: binding.clone(),
        };
        let control = CheckpointControl::bind(binding).unwrap();
        (root, control, request)
    }
    #[test]
    fn failed_drain_retains_fence_and_exact_retry_completes() {
        let (root, control, request) = fixture();
        assert!(control
            .process(request.clone(), || Ok(()), || Err(invalid("held stream")))
            .is_err());
        assert!(control.paused());
        assert!(refuse_retained_pause(&request.binding.journal_dir).is_err());
        let result = control
            .process(request.clone(), || Ok(()), || Ok(()))
            .unwrap();
        assert_eq!(result["status"], "paused");
        let mut resume = request.clone();
        resume.action = "resume".into();
        assert_eq!(
            control
                .process(
                    resume.clone(),
                    || Ok(()),
                    || panic!("resume drains no new streams")
                )
                .unwrap()["status"],
            "resumed"
        );
        assert!(!control.paused());
        assert_eq!(
            control.process(resume, || Ok(()), || Ok(())).unwrap()["status"],
            "resumed"
        );
        drop(control);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn resumed_receipt_before_unlink_recovers_exactly_and_cannot_clear_new_pause() {
        let (root, control, request) = fixture();
        control
            .process(request.clone(), || Ok(()), || Ok(()))
            .unwrap();
        let bytes = retained(&control.pause_path).unwrap();
        publish(
            &request
                .binding
                .journal_dir
                .join(format!("checkpoint-{}-resume.json", request.nonce_hex)),
            &bytes,
        )
        .unwrap();
        let mut resume = request.clone();
        resume.action = "resume".into();
        control
            .process(resume.clone(), || Ok(()), || Ok(()))
            .unwrap();
        let mut next = request;
        next.nonce_hex = "d".repeat(64);
        control.process(next, || Ok(()), || Ok(())).unwrap();
        assert!(control.process(resume, || Ok(()), || Ok(())).is_err());
        assert!(control.paused());
        drop(control);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn completed_resume_replays_after_new_receiving_without_repausing_nonce() {
        let (root, control, request) = fixture();
        control
            .process(request.clone(), || Ok(()), || Ok(()))
            .unwrap();
        let mut resume = request.clone();
        resume.action = "resume".into();
        let original = control
            .process(resume.clone(), || Ok(()), || Ok(()))
            .unwrap();
        fs::write(
            request.binding.journal_dir.join("record.json"),
            b"later accepted physical dispatch",
        )
        .unwrap();
        let replay = control
            .process(
                resume,
                || panic!("historical acknowledgement does not inspect later effects"),
                || panic!("no new drain"),
            )
            .unwrap();
        assert_eq!(original, replay);
        assert!(control.process(request, || Ok(()), || Ok(())).is_err());
        assert!(!control.paused());
        drop(control);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn changed_journal_binding_or_unsettled_effect_never_resumes() {
        let (root, control, request) = fixture();
        assert!(control
            .process(
                request.clone(),
                || Err(invalid("uncertain physical effect")),
                || panic!("no drain")
            )
            .is_err());
        assert!(!control.paused());
        control
            .process(request.clone(), || Ok(()), || Ok(()))
            .unwrap();
        let mut resume = request;
        resume.action = "resume".into();
        resume.binding.generation = "8".into();
        assert!(control
            .process(resume.clone(), || Ok(()), || Ok(()))
            .is_err());
        resume.binding.generation = "7".into();
        fs::write(resume.binding.journal_dir.join("record.json"), b"changed").unwrap();
        assert!(control.process(resume, || Ok(()), || Ok(())).is_err());
        assert!(control.paused());
        drop(control);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn atomic_publication_never_exposes_stage_or_accepts_changed_bytes() {
        let (root, control, _) = fixture();
        let path = root.join("complete.json");
        publish(&path, b"complete").unwrap();
        assert_eq!(fs::metadata(&path).unwrap().nlink(), 1);
        assert_eq!(retained(&path).unwrap(), b"complete");
        publish(&path, b"complete").unwrap();
        assert!(publish(&path, b"different").is_err());
        let _lock = checkpoint_lock(&root).unwrap();
        assert!(checkpoint_lock(&root).is_err());
        drop(control);
        fs::remove_dir_all(root).unwrap();
    }
}
