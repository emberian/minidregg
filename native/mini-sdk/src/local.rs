//! The member's two local Lean processes, selected by local custody (never by the operator):
//! the semantic Host image's storeless codec loop (`HOST SETTINGS codec`, `Host.Main.serveCodec`,
//! frames 7–11) and the consent provider ([`crate::consent`], `CONSENT SETTINGS stdio`). Both speak
//! `u32(len) ‖ op ‖ payload` on stdio and answer `u32(len) ‖ op' ‖ body`, where `op' = op` answers
//! and `op' = 255` refuses.
//!
//! This is the client's working path, moved here from `resource-client` (`client_consent.rs`):
//! one codec child per process, reused only under the same [`binding`], whose refusals the same
//! child decodes (`inspect outcome`), so the client never decodes a Host frame itself. The
//! session a [`Codec`] holds may instead be a connection to the binding's resident codec Host
//! ([`crate::consent::ResidentKind::Codec`], [`Codec::frame_with`]): one `HOST SETTINGS codec`
//! child for every process of this user under that binding, since the codec is pure.
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};

use serde_json::Value;

use crate::host_operations::{CALL_ASSEMBLE, INSPECT, OBSERVATION_ASSEMBLE, RESPONSE_HOST_OUTCOME, RESPONSE_NO_RECORD};
use crate::{Error, Result};

/// `FnEvidenceCodec.maxHostFrameBytes`: the bound of every local frame.
pub const CAP: usize = 12_102_760;

/// `u32(len(left)) ‖ left ‖ right`: the pair framing of codec and consent payloads.
pub fn pair(left: &[u8], right: &[u8]) -> Result<Vec<u8>> {
    let length: u32 = left.len().try_into().map_err(|_| "consent pair exceeds bound")?;
    let mut bytes = length.to_le_bytes().to_vec();
    bytes.extend_from_slice(left);
    bytes.extend_from_slice(right);
    if bytes.len() >= CAP {
        return Err("local consent pair exceeds frame bound".into());
    }
    Ok(bytes)
}

/// [`pair`] for a payload whose two components are both required (a plan and its signatures,
/// a signed request and its body): an empty one is refused before anything is framed.
pub fn pair_nonempty(left: &[u8], right: &[u8]) -> Result<Vec<u8>> {
    if left.is_empty() || right.is_empty() {
        return Err("pair has an empty component".into());
    }
    pair(left, right)
}

/// `u16(len(kind)) ‖ kind ‖ input`: the kind framing of codec frames 7 and 8.
pub fn kind(kind: &str, input: &[u8]) -> Result<Vec<u8>> {
    let width: u16 = kind.len().try_into().map_err(|_| "local codec kind exceeds bound")?;
    let mut payload = width.to_le_bytes().to_vec();
    payload.extend_from_slice(kind.as_bytes());
    payload.extend_from_slice(input);
    Ok(payload)
}

/// Read a settings file within the frame bound (a regular file, never through a symlink).
pub fn settings_bytes(path: &Path) -> Result<Vec<u8>> {
    crate::fsread::read_regular(path, 0, CAP).map_err(|e| Error(e.to_string()))
}

/// One local framed process (or a connection to a resident one).
pub struct Session {
    /// The child this process started; `None` when the frames go to a resident provider.
    pub(crate) child: Option<Child>,
    pub(crate) input: Box<dyn Write + Send>,
    pub(crate) output: Box<dyn Read + Send>,
    pub(crate) executable: PathBuf,
    pub(crate) settings_bytes: Vec<u8>,
    /// Where a consent provider's anchor is retained and what it is bound to; `None` for a
    /// codec child or a connection to a resident provider.
    pub(crate) anchor: Option<crate::consent::AnchorCustody>,
}

impl Drop for Session {
    fn drop(&mut self) {
        if let Some(child) = self.child.as_mut() {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

impl Session {
    /// Start `EXECUTABLE SETTINGS MODE` with piped stdio (`codec` or `stdio`).
    pub(crate) fn spawn(executable: PathBuf, settings: &Path, settings_bytes: Vec<u8>, mode: &str, what: &str) -> Result<Self> {
        let mut child = Command::new(&executable)
            .arg(settings)
            .arg(mode)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(|e| format!("cannot start {what}: {e}"))?;
        let input = child.stdin.take().ok_or("local process stdin missing")?;
        let output = child.stdout.take().ok_or("local process stdout missing")?;
        Ok(Session { child: Some(child), input: Box::new(input), output: Box::new(output), executable, settings_bytes, anchor: None })
    }

    /// A session over an already connected byte stream (tests, resident connections).
    pub fn over(input: Box<dyn Write + Send>, output: Box<dyn Read + Send>, executable: PathBuf, settings_bytes: Vec<u8>) -> Self {
        Session { child: None, input, output, executable, settings_bytes, anchor: None }
    }

    pub fn executable(&self) -> &Path {
        &self.executable
    }

    pub fn settings(&self) -> &[u8] {
        &self.settings_bytes
    }

    /// One frame out, one frame in: the reply's operation byte and its body, unjudged.
    pub fn exchange(&mut self, operation: u8, payload: &[u8]) -> Result<(u8, Vec<u8>)> {
        let size: u32 = (payload.len() + 1).try_into().map_err(|_| "consent frame exceeds bound")?;
        if size as usize > CAP {
            return Err("consent frame exceeds bound".into());
        }
        self.input
            .write_all(&size.to_le_bytes())
            .and_then(|_| self.input.write_all(&[operation]))
            .and_then(|_| self.input.write_all(payload))
            .and_then(|_| self.input.flush())
            .map_err(|e| format!("local process request failed: {e}"))?;
        let mut width = [0u8; 4];
        self.output.read_exact(&mut width).map_err(|e| format!("local process {} ended before answering: {e}", self.executable.display()))?;
        let size = u32::from_le_bytes(width) as usize;
        if size == 0 || size > CAP {
            return Err("local consent response frame refused".into());
        }
        let mut frame = vec![0; size];
        self.output.read_exact(&mut frame).map_err(|e| e.to_string())?;
        let body = frame.split_off(1);
        Ok((frame[0], body))
    }
}

/// The identity of a local process selection: the executable file (path and inode identity, size
/// and both times) and the exact settings bytes. A rebuilt, replaced or moved executable, or any
/// settings change, binds differently. A codec child or a resident is reused only under the same
/// binding; a retained consent anchor is bound by [`anchor_binding`] instead.
pub fn binding(executable: &Path, settings_bytes: &[u8]) -> Result<[u8; 32]> {
    use sha2::Digest;
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::fs::MetadataExt;
    let meta = std::fs::metadata(executable).map_err(|e| format!("local consent provider {}: {e}", executable.display()))?;
    let mut digest = sha2::Sha256::new();
    digest.update(b"MINI-CONSENT-ANCHOR-BINDING/v1\0");
    digest.update((executable.as_os_str().len() as u64).to_le_bytes());
    digest.update(executable.as_os_str().as_bytes());
    for value in [meta.dev(), meta.ino(), meta.size(), meta.mtime() as u64, meta.mtime_nsec() as u64,
        meta.ctime() as u64, meta.ctime_nsec() as u64] {
        digest.update(value.to_le_bytes());
    }
    digest.update(sha2::Sha256::digest(settings_bytes));
    Ok(digest.finalize().into())
}

/// The settings fields that name executables (`storageBinary`, `signatureBinary`): a ship moves
/// them to the new candidate's paths without changing what admission means.
const EXECUTABLE_SETTINGS: [&str; 2] = ["storageBinary", "signatureBinary"];

/// The binding of a retained consent anchor (CONSENT-STORE, `Kernel.ConsentAnchor`): the settings
/// as canonical JSON (keys sorted at every level) without the executable paths, never the
/// provider's own file. An anchor is a height, genesis log, chain and root of one Store; what it
/// is admitted under is named inside its bytes (`ConsentAnchor.epochTag`), and a provider of
/// another consent epoch sets it aside, so an anchor survives a ship that moves only binaries.
pub fn anchor_binding(settings_bytes: &[u8]) -> Result<[u8; 32]> {
    use sha2::Digest;
    let mut value: serde_json::Value = serde_json::from_slice(settings_bytes)
        .map_err(|e| format!("local consent settings are not JSON: {e}"))?;
    let object = value.as_object_mut().ok_or("local consent settings are not a JSON object")?;
    for name in EXECUTABLE_SETTINGS {
        object.remove(name);
    }
    let mut canonical = Vec::new();
    write_canonical(&value, &mut canonical);
    let mut digest = sha2::Sha256::new();
    digest.update(b"MINI-CONSENT-ANCHOR-BINDING/v2\0");
    digest.update(sha2::Sha256::digest(&canonical));
    Ok(digest.finalize().into())
}

/// JSON with every object's keys in byte order, whatever map order serde_json was built with.
fn write_canonical(value: &serde_json::Value, out: &mut Vec<u8>) {
    match value {
        serde_json::Value::Object(map) => {
            let mut entries: Vec<_> = map.iter().collect();
            entries.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
            out.push(b'{');
            for (i, (key, item)) in entries.into_iter().enumerate() {
                if i > 0 {
                    out.push(b',');
                }
                out.extend_from_slice(serde_json::Value::String(key.clone()).to_string().as_bytes());
                out.push(b':');
                write_canonical(item, out);
            }
            out.push(b'}');
        }
        serde_json::Value::Array(items) => {
            out.push(b'[');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(b',');
                }
                write_canonical(item, out);
            }
            out.push(b']');
        }
        other => out.extend_from_slice(other.to_string().as_bytes()),
    }
}

/// How a codec frame failed.
#[derive(Debug, Clone, PartialEq)]
pub enum CodecError {
    /// The Host image answered the frame with an outcome marker instead of its own byte
    /// (`marker`: `NO_RECORD` 253 or `HOST_OUTCOME` 255; frames 7–11 never append, so either way
    /// nothing changed). `encoded` is the frame's body; `decoded` is the same child's own `inspect
    /// outcome` of it, when it could decode it.
    Refused { marker: u8, encoded: Vec<u8>, decoded: Option<Value> },
    /// No decision: the child could not be started, died, answered out of turn, or the settings
    /// changed under it.
    Failed(String),
}

/// The storeless codec authority of one process: `HOST SETTINGS codec` answers frames 7–11 and
/// never opens a Store, so a member's own machine needs none. It never receives keys, and these
/// frames never mutate source.
///
/// The loop answers every frame, a refusal included (as a 255 frame), and keeps serving, so ONE
/// child serves the process. It holds no state between frames, so it is reused only under the
/// same [`binding`]: a Host image replaced in place, or other settings bytes, start a new child.
/// The settings PATH is not in the key: the child parses the bytes once at start, and a caller
/// may rename the attempt directory holding them between frames. A child that failed a frame,
/// answered out of turn, or could not decode its own refusal is dropped, and the next frame
/// starts a fresh one.
#[derive(Default)]
pub struct Codec {
    slot: Option<([u8; 32], Session)>,
    /// The settings and executable this process last bound, by file identity: a frame whose files
    /// still have those identities reuses the bytes and the binding (one `statx` each), instead of
    /// re-reading and re-hashing the settings twice per frame.
    seen: Option<Seen>,
}

struct Seen {
    settings: PathBuf,
    settings_identity: FileIdentity,
    settings_bytes: Vec<u8>,
    executable: PathBuf,
    executable_identity: FileIdentity,
    binding: [u8; 32],
}

/// A file's identity as the binding reads it: device, inode, size and both times. A rewrite in
/// place changes ctime; a replacement changes the inode.
type FileIdentity = [u64; 7];

fn file_identity(path: &Path) -> Result<FileIdentity> {
    use std::os::unix::fs::MetadataExt;
    let meta = std::fs::symlink_metadata(path).map_err(|e| format!("{}: {e}", path.display()))?;
    Ok([meta.dev(), meta.ino(), meta.size(), meta.mtime() as u64, meta.mtime_nsec() as u64,
        meta.ctime() as u64, meta.ctime_nsec() as u64])
}

impl Codec {
    pub const fn new() -> Self {
        Codec { slot: None, seen: None }
    }

    /// Drop the child (the next frame starts a fresh one).
    pub fn reset(&mut self) {
        self.slot = None;
    }

    /// One codec frame (7–11) to the image `executable` under `settings`; the answer's body. The
    /// session is this process's own `HOST SETTINGS codec` child.
    pub fn frame(&mut self, executable: &Path, settings: &Path, operation: u8, payload: &[u8]) -> std::result::Result<Vec<u8>, CodecError> {
        self.frame_with(executable, settings, operation, payload,
            &|executable, settings, settings_bytes| Session::spawn(executable, settings, settings_bytes, "codec", "local native codec"))
    }

    /// [`Codec::frame`] over a session `start` supplies for `(executable, settings, settings bytes)`
    /// when none is held under this binding: this process's own child, or a connection to the
    /// binding's resident codec Host ([`crate::consent::connect_resident_kind`]). Whichever it is,
    /// the reply bytes are the same pure function of the frame (`Host.Main.pureCodec` holds no
    /// state), and a session that fails a frame is dropped the same way: the next frame starts
    /// (or reconnects to) a fresh one.
    pub fn frame_with(&mut self, executable: &Path, settings: &Path, operation: u8, payload: &[u8],
        start: &dyn Fn(PathBuf, &Path, Vec<u8>) -> Result<Session>) -> std::result::Result<Vec<u8>, CodecError> {
        let failed = |e: Error| CodecError::Failed(e.0);
        if !(crate::host_operations::AUTHOR..=CALL_ASSEMBLE).contains(&operation) {
            return Err(CodecError::Failed("not a local codec opcode".into()));
        }
        if !settings.is_absolute() {
            return Err(CodecError::Failed("local native settings must be absolute".into()));
        }
        let settings_identity = file_identity(settings).map_err(failed)?;
        let executable_identity = file_identity(executable).map_err(failed)?;
        let fresh = self.seen.as_ref().is_none_or(|seen| seen.settings != settings
            || seen.settings_identity != settings_identity || seen.executable != executable
            || seen.executable_identity != executable_identity);
        if fresh {
            let settings_bytes = settings_bytes(settings).map_err(failed)?;
            let binding = binding(executable, &settings_bytes).map_err(failed)?;
            self.seen = Some(Seen { settings: settings.to_path_buf(), settings_identity, settings_bytes,
                executable: executable.to_path_buf(), executable_identity, binding });
        }
        let seen = self.seen.as_ref().expect("bound above");
        let binding = seen.binding;
        if self.slot.as_ref().is_some_and(|(bound, _)| bound != &binding) {
            self.slot = None;
        }
        if self.slot.is_none() {
            let session = start(executable.to_path_buf(), settings, seen.settings_bytes.clone()).map_err(failed)?;
            self.slot = Some((binding, session));
        }
        let session = &mut self.slot.as_mut().expect("codec child").1;
        let (answer, body) = match session.exchange(operation, payload) {
            Ok(reply) => reply,
            Err(error) => {
                self.slot = None;
                return Err(CodecError::Failed(format!("local native codec: {error}")));
            }
        };
        if file_identity(settings).ok() != Some(settings_identity) {
            self.slot = None;
            self.seen = None;
            return Err(CodecError::Failed("local native settings changed during codec operation".into()));
        }
        if answer == operation {
            return Ok(body);
        }
        if answer != RESPONSE_NO_RECORD && answer != RESPONSE_HOST_OUTCOME {
            self.slot = None;
            return Err(CodecError::Failed(format!("local native codec answered frame {answer} to frame {operation}")));
        }
        // A refusal: the same child decodes its own frame (`inspect outcome`), as a Host session
        // does; the client never decodes it itself. A decode exchange that fails, or is answered
        // out of turn, leaves a child that cannot be trusted with the next frame: drop it, and
        // report the refusal undecoded.
        let decoded = match kind("outcome", &body).and_then(|request| session.exchange(INSPECT, &request)) {
            Ok((INSPECT, json)) => serde_json::from_slice::<Value>(&json).ok(),
            Ok((RESPONSE_NO_RECORD | RESPONSE_HOST_OUTCOME, _)) => None,
            _ => {
                self.slot = None;
                None
            }
        };
        Err(CodecError::Refused { marker: answer, encoded: body, decoded })
    }

    /// Op 7: canonical bytes of the authoring source of `kind_name`.
    pub fn author(&mut self, executable: &Path, settings: &Path, kind_name: &str, source: &[u8]) -> std::result::Result<Vec<u8>, CodecError> {
        let payload = kind(kind_name, source).map_err(|e| CodecError::Failed(e.0))?;
        self.frame(executable, settings, crate::host_operations::AUTHOR, &payload)
    }

    /// Op 8: the image's own presentation of canonical bytes of `kind_name`.
    pub fn inspect(&mut self, executable: &Path, settings: &Path, kind_name: &str, bytes: &[u8]) -> std::result::Result<Vec<u8>, CodecError> {
        let payload = kind(kind_name, bytes).map_err(|e| CodecError::Failed(e.0))?;
        self.frame(executable, settings, INSPECT, &payload)
    }

    /// Op 9: the canonical signature list from its JSON spelling.
    pub fn signatures(&mut self, executable: &Path, settings: &Path, json: &[u8]) -> std::result::Result<Vec<u8>, CodecError> {
        self.frame(executable, settings, crate::host_operations::SIGNATURES, json)
    }

    /// Op 10: a signed observation from a challenge and its signatures.
    pub fn observe_assemble(&mut self, executable: &Path, settings: &Path, challenge: &[u8], signatures: &[u8]) -> std::result::Result<Vec<u8>, CodecError> {
        let payload = pair(challenge, signatures).map_err(|e| CodecError::Failed(e.0))?;
        self.frame(executable, settings, OBSERVATION_ASSEMBLE, &payload)
    }

    /// Op 11: the exact call from a plan and its signatures.
    pub fn assemble(&mut self, executable: &Path, settings: &Path, plan: &[u8], signatures: &[u8]) -> std::result::Result<Vec<u8>, CodecError> {
        let payload = pair(plan, signatures).map_err(|e| CodecError::Failed(e.0))?;
        self.frame(executable, settings, CALL_ASSEMBLE, &payload)
    }
}

#[cfg(test)]
pub(crate) mod fake {
    //! Scripted stand-in processes for unit tests: `/bin/sh` that replays fixed frames.
    //! Scripts keep the request pipe open with `exec 3<&0; cat <&3 >/dev/null &`: dash gives a
    //! background job /dev/null as stdin BEFORE applying its explicit redirections (so `<&0` would
    //! duplicate /dev/null), which closes the pipe before the client writes (EPIPE).
    use std::path::{Path, PathBuf};

    /// A stand-in `HOST SETTINGS codec` loop: appends a line to `<dir>/starts` when it starts, then
    /// answers frame i with the bytes of `<dir>/reply-i` (else `<dir>/reply`) until EOF.
    pub(crate) fn codec_stub(dir: &Path) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let path = dir.join("codec-host");
        std::fs::write(&path, format!("#!/bin/sh\necho start >> '{d}/starts'\ni=0\nwhile :; do\n  n=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 | tr -d ' \\n')\n  [ -n \"$n\" ] || exit 0\n  dd bs=1 count=\"$n\" of=/dev/null 2>/dev/null\n  i=$((i+1))\n  if [ -f '{d}/reply-'$i ]; then cat '{d}/reply-'$i; else cat '{d}/reply'; fi\ndone\n", d = dir.display())).unwrap();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
        path
    }

    /// The `ssh` stand-in used by the operator's ssh-route tests. It is run as
    /// `/bin/sh SCRIPT -T -v -o … -- DEST` and behaves by DEST (its last argument):
    ///
    /// * `hostkey` / `denied` / `refused` / `garbled` — ssh's own failure text on stderr, exit 255,
    ///   BEFORE the "Entering interactive session" line (no request can have been written);
    /// * `silent` — prints nothing and sleeps (the connect deadline names it);
    /// * `serve-…` — prints the session lines, then serves frames: each request is appended to
    ///   `$TMPDIR/mini-sdk-ssh-DEST.req` and answered by a canned reply: `serve-answer` (op 2 + "ok"),
    ///   `serve-refuse` (255 + "no"), `serve-reject` (254 + "x"), `serve-hangup` (reads one request,
    ///   exits 255), `serve-garbage` (a zero-length reply frame), `serve-mute` (reads, never answers),
    ///   `serve-oneshot` (answers one request, then the session ends).
    ///
    /// Frames are read with `dd`/`od` (no NULs enter a shell variable). `remote-…` is the same
    /// server WITHOUT the debug lines, for use as an sshd `RemoteCommand`.
    pub const SSH_STANDIN: &str = include_str!("../tests/fixtures/ssh-standin.sh");

    /// Returns `(/bin/sh, script)`: the script travels as an argument, so nothing freshly written
    /// is ever executed (executing a just-written file races a sibling test's fork on Linux: ETXTBSY).
    pub fn script(tag: &str, body: &str) -> (PathBuf, PathBuf) {
        let dir = std::env::temp_dir().join(format!("mini-sdk-{tag}-{}", std::process::id()));
        let _ = std::fs::create_dir_all(&dir);
        let script = dir.join("proc.sh");
        std::fs::write(&script, format!("{body}\n")).unwrap();
        (PathBuf::from("/bin/sh"), script)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::os::unix::fs::PermissionsExt;

    fn stub_dir(label: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("mini-sdk-local-{label}-{}-{}", std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir(&dir).unwrap();
        dir
    }
    fn framed(body: &[u8]) -> Vec<u8> {
        [(body.len() as u32).to_le_bytes().as_slice(), body].concat()
    }
    use super::fake::codec_stub;
    fn starts(dir: &Path) -> usize {
        fs::read_to_string(dir.join("starts")).unwrap_or_default().lines().count()
    }

    #[test]
    fn framing_is_the_consent_protocol() {
        assert_eq!(pair(b"intent", b"plan").unwrap(), [6u32.to_le_bytes().as_slice(), b"intent", b"plan"].concat());
        assert_eq!(kind("plan", b"x").unwrap(), [4u16.to_le_bytes().as_slice(), b"plan", b"x"].concat());
        assert!(pair(&vec![0; CAP], b"").is_err());
    }

    /// One child serves every frame of the same image and settings bytes, a refusal included;
    /// changed settings bytes or a replaced image start another; the settings path is not bound.
    #[test]
    fn one_codec_child_per_binding_names_its_refusals() {
        let dir = stub_dir("codec");
        fs::write(dir.join("settings.json"), b"{}").unwrap();
        fs::write(dir.join("reply"), framed(b"\x07ok")).unwrap();
        let host = codec_stub(&dir);
        let settings = dir.join("settings.json");
        let mut codec = Codec::new();
        for _ in 0..3 {
            assert_eq!(codec.frame(&host, &settings, crate::host_operations::AUTHOR, b"intent").unwrap(), b"ok");
        }
        assert_eq!(starts(&dir), 1);
        fs::rename(&settings, dir.join("moved.json")).unwrap();
        assert_eq!(codec.frame(&host, &dir.join("moved.json"), crate::host_operations::AUTHOR, b"intent").unwrap(), b"ok");
        assert_eq!(starts(&dir), 1, "the same bytes at another path keep the child");
        fs::write(dir.join("moved.json"), b"{ }").unwrap();
        codec.frame(&host, &dir.join("moved.json"), crate::host_operations::AUTHOR, b"intent").unwrap();
        assert_eq!(starts(&dir), 2);
        assert!(matches!(codec.frame(&host, &dir.join("moved.json"), crate::host_operations::FN_POLL, b""), Err(CodecError::Failed(_))));

        let other = stub_dir("codec-refusal");
        fs::write(other.join("settings.json"), b"{}").unwrap();
        fs::write(other.join("reply-1"), framed(&[255, 0xff, 0x00])).unwrap();
        fs::write(other.join("reply-2"), framed(&[b"\x08".as_slice(), br#"{"type":"refused","reason":"malformed"}"#].concat())).unwrap();
        fs::write(other.join("reply"), framed(b"\x07again")).unwrap();
        let refusing = codec_stub(&other);
        let mut codec = Codec::new();
        match codec.frame(&refusing, &other.join("settings.json"), crate::host_operations::AUTHOR, b"intent") {
            Err(CodecError::Refused { encoded, decoded: Some(v), .. }) => {
                assert_eq!(encoded, vec![0xff, 0x00]);
                assert_eq!(v["reason"], "malformed");
            }
            other => panic!("{other:?}"),
        }
        assert_eq!(codec.frame(&refusing, &other.join("settings.json"), crate::host_operations::AUTHOR, b"intent").unwrap(), b"again");
        assert_eq!(starts(&other), 1);
        let _ = fs::remove_dir_all(&dir);
        let _ = fs::remove_dir_all(&other);
    }

    /// A child that refuses and then dies cannot decode its refusal: the refusal is still reported
    /// (undecoded), and the dead child is dropped, so the next frame starts a fresh one.
    #[test]
    fn codec_child_that_dies_decoding_its_refusal_is_replaced() {
        let dir = stub_dir("codec-dies");
        let settings = dir.join("settings.json");
        fs::write(&settings, b"{}").unwrap();
        let host = dir.join("codec-host");
        fs::write(&host, format!("#!/bin/sh\necho start >> '{d}/starts'\nn=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 | tr -d ' \\n')\ndd bs=1 count=\"$n\" of=/dev/null 2>/dev/null\ncat '{d}/reply'\n",
            d = dir.display())).unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        fs::write(dir.join("reply"), framed(&[255, 0xff, 0x00])).unwrap();
        let mut codec = Codec::new();
        assert!(matches!(codec.frame(&host, &settings, crate::host_operations::AUTHOR, b"intent"), Err(CodecError::Refused { decoded: None, .. })));
        fs::write(dir.join("reply"), framed(b"\x07ok")).unwrap();
        assert_eq!(codec.frame(&host, &settings, crate::host_operations::AUTHOR, b"intent").unwrap(), b"ok");
        assert_eq!(starts(&dir), 2);
        let _ = fs::remove_dir_all(&dir);
    }
}

#[cfg(test)]
mod pair_tests {
    use super::*;

    #[test]
    fn pair_frames_left_length_and_refuses_what_the_host_would() {
        assert_eq!(pair(b"ab", b"c").unwrap(), [2, 0, 0, 0, b'a', b'b', b'c']);
        assert_eq!(pair(b"", b"").unwrap(), [0, 0, 0, 0]);
        assert!(pair(&vec![0; CAP], b"").is_err(), "a frame at the bound is refused");
        assert_eq!(pair_nonempty(b"plan", b"sig").unwrap(), pair(b"plan", b"sig").unwrap());
        for (left, right) in [(&b""[..], &b"sig"[..]), (b"plan", b"")] {
            assert!(pair_nonempty(left, right).unwrap_err().to_string().contains("empty component"));
        }
    }
}
