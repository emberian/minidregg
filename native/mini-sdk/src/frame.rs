//! The framed stdio protocol both local Lean processes speak (`Host/ClientConsentCore.lean`
//! `serve`): request `u32(len) ‖ op ‖ payload`, response `u32(len) ‖ op' ‖ body`, where
//! `op' = op` answers and `op' = 255` refuses with a UTF-8 reason. The process is started as
//! `EXECUTABLE SETTINGS stdio`, by local custody only, and kept warm: restarting a consent
//! provider would discard its independently verified frontier.
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

use crate::{Error, Result};

/// `FnEvidenceCodec.maxHostFrameBytes`, as `client_consent.rs` bounds it.
pub const CAP: usize = 12_102_760;

/// `u32(len(left)) ‖ left ‖ right` — the pair framing every consent operation uses.
pub fn pair(left: &[u8], right: &[u8]) -> Result<Vec<u8>> {
    let n: u32 = left.len().try_into().map_err(|_| "pair exceeds bound")?;
    let mut out = n.to_le_bytes().to_vec();
    out.extend_from_slice(left);
    out.extend_from_slice(right);
    if out.len() >= CAP {
        return Err("pair exceeds frame bound".into());
    }
    Ok(out)
}

/// `u16(len(kind)) ‖ kind ‖ input` — the kind framing of Host codec ops 7 and 8.
pub fn kind(kind: &str, input: &[u8]) -> Result<Vec<u8>> {
    let n: u16 = kind.len().try_into().map_err(|_| "kind too long")?;
    let mut out = n.to_le_bytes().to_vec();
    out.extend_from_slice(kind.as_bytes());
    out.extend_from_slice(input);
    Ok(out)
}

/// A local framed process. The executable and settings are absolute paths chosen by local
/// custody; the settings bytes are pinned for the life of the session.
pub struct Process {
    child: Child,
    input: ChildStdin,
    output: ChildStdout,
    pub executable: PathBuf,
    pub settings: PathBuf,
    settings_bytes: Vec<u8>,
}

impl Drop for Process {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn bounded(path: &Path) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    std::fs::File::open(path)
        .map_err(|e| format!("{}: {e}", path.display()))?
        .take((CAP + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() > CAP {
        return Err("settings exceed frame bound".into());
    }
    Ok(bytes)
}

impl Process {
    pub fn start(executable: &Path, settings: &Path) -> Result<Self> {
        if !executable.is_absolute() || !settings.is_absolute() {
            return Err("local executable and settings must be absolute paths".into());
        }
        let settings_bytes = bounded(settings)?;
        let mut child = Command::new(executable)
            .arg(settings)
            .arg("stdio")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(|e| format!("cannot start {}: {e}", executable.display()))?;
        let input = child.stdin.take().ok_or("child stdin missing")?;
        let output = child.stdout.take().ok_or("child stdout missing")?;
        Ok(Process { child, input, output, executable: executable.into(), settings: settings.into(), settings_bytes })
    }

    /// One request; `Err` carries the process's refusal (op 255) or a dead process.
    pub fn call(&mut self, op: u8, payload: &[u8]) -> Result<Vec<u8>> {
        if bounded(&self.settings)? != self.settings_bytes {
            return Err("local settings changed within this session".into());
        }
        let size: u32 = (payload.len() + 1).try_into().map_err(|_| "frame exceeds bound")?;
        if size as usize > CAP {
            return Err("frame exceeds bound".into());
        }
        self.input
            .write_all(&size.to_le_bytes())
            .and_then(|_| self.input.write_all(&[op]))
            .and_then(|_| self.input.write_all(payload))
            .and_then(|_| self.input.flush())
            .map_err(|e| format!("local request failed: {e}"))?;
        let mut width = [0u8; 4];
        self.output.read_exact(&mut width).map_err(|e| format!("local process ended before answering: {e}"))?;
        let size = u32::from_le_bytes(width) as usize;
        if size == 0 || size > CAP {
            return Err("local response frame refused".into());
        }
        let mut frame = vec![0; size];
        self.output.read_exact(&mut frame).map_err(|e| e.to_string())?;
        if frame[0] != op {
            return Err(Error(format!("local process refused op {op}: {}", String::from_utf8_lossy(&frame[1..]))));
        }
        frame.remove(0);
        Ok(frame)
    }
}

#[cfg(test)]
pub(crate) mod fake {
    //! A scripted stand-in process for unit tests: `/bin/sh` that replays fixed frames.
    //! Scripts keep the request pipe open with `exec 3<&0; cat <&3 >/dev/null &`: dash gives a
    //! background job /dev/null as stdin BEFORE applying its explicit redirections (so `<&0` would
    //! duplicate /dev/null), which closes the pipe before the client writes (EPIPE).
    use std::path::PathBuf;
    /// Returns `(/bin/sh, script)`: the frame client runs `EXECUTABLE SETTINGS stdio`, so the
    /// script travels as the "settings" path and nothing freshly written is ever executed
    /// (executing a just-written file races a sibling test's fork on Linux: ETXTBSY).
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

    #[test]
    fn framing_is_the_consent_protocol() {
        assert_eq!(pair(b"intent", b"plan").unwrap(), [6u32.to_le_bytes().as_slice(), b"intent", b"plan"].concat());
        assert_eq!(kind("plan", b"x").unwrap(), [4u16.to_le_bytes().as_slice(), b"plan", b"x"].concat());
        assert!(pair(&vec![0; CAP], b"").is_err());
    }

    #[test]
    fn a_refusal_frame_is_an_error_carrying_the_reason() {
        // 13-byte frame: op 255 + "changed-plan" — the client_consent.rs refusal test, as a process.
        let (exe, settings) = fake::script("refuse", "exec 3<&0; cat <&3 >/dev/null & printf '\\015\\000\\000\\000\\377changed-plan'");
        let mut p = Process::start(&exe, &settings).unwrap();
        let err = p.call(222, b"retained").unwrap_err();
        assert!(err.0.contains("changed-plan"), "{err}");
    }

    #[test]
    fn relative_paths_refuse() {
        assert!(Process::start(Path::new("consent"), Path::new("/x")).is_err());
    }
}
