//! `mini-shell-ssh MINI HOST CONFIG SOCKET WORKSPACE HOME`: the ssh forced command. One authorized
//! key is one participant session: the authorized_keys line that names this program binds the
//! connecting key to exactly one workspace and one session home, and the friend chooses neither.
//! `SSH_ORIGINAL_COMMAND`, when present, is handed to `mini shell` as one line in the shell's own
//! word syntax; it never reaches a system shell.
//!
//! ```text
//! ssh -t friend@host              interactive (prompt, Tab completion)
//! ssh friend@host 'read shared'   one verb; exit code is the verb's
//! ssh -T friend@host < script     script mode; stops at the first failure
//! ```
//!
//! The candidate builds this as `bin/mini-line`; the box installs a root-owned copy at
//! `/usr/local/lib/mini/mini-shell-ssh`, so the authorized_keys lines never change. Every path is
//! absolute (exit 64 otherwise) and MINI must be executable (66). The box's settings under
//! `/etc/mini` and the member's consent pins are read once each; a malformed one refuses with 78.
//!
//! A one-verb session holds the member's call slot here (an exclusive non-blocking flock on
//! HOME/.call-slots/1, then /2, close-on-exec, held for the call's life; a third call is refused by
//! name with 75) and hands the line, its standard input, output and error to the member's resident
//! shell for that slot (`mini line-resident`, `src/line_resident.rs`), starting it when none
//! listens, so no `mini` starts per verb. Each resident is keyed by everything that shapes its
//! commands: the `mini` file's identity, the arguments other than the line, the `MINI_*`
//! environment, `HOME`, `PATH` and the umask, so two sessions that would run differently never
//! share one. Anything that keeps a resident from being used execs `mini shell ... --call-slots
//! DIR --line LINE`, which takes the slot itself. An interactive login prints the motd and the
//! re-genesis notice beside this program, then execs `mini shell`.
// A closed standard error drops the message instead of panicking (`mini_streams`).
#[macro_use]
extern crate mini_streams;
use std::ffi::{OsStr, OsString};
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::fs::{FileTypeExt, MetadataExt, OpenOptionsExt};
use std::os::unix::net::UnixStream;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::time::{Duration, Instant};

const USAGE: &str = "usage: mini-shell-ssh ABS_MINI ABS_HOST ABS_CONFIG ABS_SOCKET ABS_WORKSPACE ABS_HOME";

fn exec(mini: &OsStr, args: &[OsString]) -> ExitCode {
    let error = Command::new(mini).args(args).exec();
    eprintln!("mini-shell-ssh: cannot run {}: {error}", Path::new(mini).display());
    ExitCode::from(70)
}

/// The first line of a file the box's operator wrote, without surrounding blanks; `None` when it
/// cannot be opened (absent or unreadable: the setting is not made). A file that opens but does
/// not read is an empty line, which every caller refuses.
fn first_line(path: &Path) -> Option<Vec<u8>> {
    let mut bytes = Vec::new();
    let _ = File::open(path).ok()?.take(4096).read_to_end(&mut bytes);
    let line = bytes.split(|b| *b == b'\n').next().unwrap_or_default();
    let blank = |b: &u8| *b == b' ' || *b == b'\t' || *b == b'\r';
    let start = line.iter().position(|b| !blank(b)).unwrap_or(line.len());
    let end = line.iter().rposition(|b| !blank(b)).map_or(start, |e| e + 1);
    Some(line[start..end].to_vec())
}

fn absolute(bytes: &[u8]) -> Option<OsString> {
    bytes.starts_with(b"/").then(|| OsString::from_vec(bytes.to_vec()))
}

fn is_digest(word: &[u8]) -> bool {
    word.len() == 64 && word.iter().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(b))
}

fn sha256_file(path: &Path) -> Result<String, String> {
    use sha2::Digest;
    let mut file = File::open(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut hasher = sha2::Sha256::new();
    std::io::copy(&mut file, &mut hasher).map_err(|e| format!("{}: {e}", path.display()))?;
    Ok(hasher.finalize().iter().map(|b| format!("{b:02x}")).collect())
}

/// The session's environment from the box's settings, each read once. `Err` is the refusal (78).
fn session_environment(mini: &Path, host: &OsStr, config: &OsStr, home: &Path) -> Result<(), String> {
    // The box's consent mode for hosted sessions: /etc/mini/session-consent (root 0644, one word).
    // `thin` is the client's thin consent path (no Store replay), used where the operator runs both
    // the Host and the hosted shell. Absent or `full`: full-peer consent. Remote and
    // bring-your-own clients never read this file.
    match first_line(Path::new("/etc/mini/session-consent")).as_deref() {
        Some(b"thin") => std::env::set_var("MINI_THIN_CONSENT", "1"),
        None | Some(b"" | b"full") => std::env::remove_var("MINI_THIN_CONSENT"),
        Some(_) => return Err("/etc/mini/session-consent must be thin or full".into()),
    }
    // Single tenancy (every hosted session runs as one account against the box's one pinned
    // config): /etc/mini/session-residents (root 0644, one absolute path to a directory that
    // account owns, 0700) gives every session the same resident directory, so the box runs ONE
    // consent provider and ONE codec Host for all of them (`mini_sdk::consent::serve_resident_kind`).
    // Absent: each session's residents live in its own home. Never set under split tenancy: there
    // each member is its own account and its residents are its own.
    if let Some(line) = first_line(Path::new("/etc/mini/session-residents")) {
        let dir = absolute(&line).ok_or("/etc/mini/session-residents must name an absolute directory")?;
        std::env::set_var("MINI_CONSENT_ANCHOR_DIR", dir);
    }
    // The client keeps consent anchors (and its residents) in MINI_CONSENT_ANCHOR_DIR, else
    // $HOME/.mini. sshd sets HOME to the account's passwd home, which on the box is root-owned
    // (/var/lib/mini: every write verb failed "Permission denied" there, explorer F1 2026-10-30),
    // and a root-side caller that starts this through `env -i` sets no HOME at all. Unless the
    // caller named a directory, the anchors live in the session home this program was given.
    if std::env::var_os("MINI_CONSENT_ANCHOR_DIR").is_none() {
        std::env::set_var("MINI_CONSENT_ANCHOR_DIR", home.join(".mini/consent-anchors"));
    }
    // Delegated full consent (split tenancy; mini-consent@NAME.socket, rendered per hosted
    // member): a member's client cannot read the operator's Store to replay it, so it asks the
    // operator's worker over HOME/consent/peer.sock. The client pins the listener (systemd's,
    // uid 0), the consent executable and the pinned config by sha256; the worker computes the same
    // pins from the same files. The ship renders both digests once into HOME/consent/peer.pins
    // (root 0644, one line: `CONSENT_SHA256 CONFIG_SHA256`, 64 lowercase hex each), so no command
    // hashes the 190 MB provider. A box without that file (shipped before it existed) hashes here.
    let peer = home.join("consent/peer.sock");
    if std::fs::metadata(&peer).is_ok_and(|m| m.file_type().is_socket()) {
        let consent_host = mini.parent().unwrap_or(Path::new("/")).join("minidregg-client-consent");
        let pins = home.join("consent/peer.pins");
        let (consent, settings) = match first_line(&pins) {
            Some(line) => {
                let mut words = line.split(|b| *b == b' ' || *b == b'\t').filter(|w| !w.is_empty());
                match (words.next(), words.next()) {
                    (Some(a), Some(b)) if is_digest(a) && is_digest(b) => {
                        (String::from_utf8_lossy(a).into_owned(), String::from_utf8_lossy(b).into_owned())
                    }
                    _ => return Err(format!("{} must hold two sha256 digests", pins.display())),
                }
            }
            None => (sha256_file(&consent_host)?, sha256_file(Path::new(config))?),
        };
        std::env::set_var("MINI_CONSENT_SOCKET", &peer);
        std::env::set_var("MINI_CONSENT_PEER_UID", "0");
        // The client takes a durable consent selection only with all three of these beside it.
        std::env::set_var("MINI_CONSENT_HOST", &consent_host);
        std::env::set_var("MINI_LOCAL_HOST", host);
        std::env::set_var("MINI_CONSENT_CONFIG", config);
        std::env::set_var("MINI_CONSENT_SHA256", consent);
        std::env::set_var("MINI_CONSENT_CONFIG_SHA256", settings);
    }
    // The box's shared codec Host (split tenancy): /etc/mini/session-codec (root 0644, one
    // absolute socket path, `mini serve-codec`'s systemd listener in a directory of the sessions'
    // group). Every member's codec frames go there; the client refuses unless it greets with this
    // session's own Host image and settings digests.
    if let Some(line) = first_line(Path::new("/etc/mini/session-codec")) {
        let socket = absolute(&line).ok_or("/etc/mini/session-codec must name an absolute socket")?;
        std::env::set_var("MINI_CODEC_SOCKET", socket);
        std::env::set_var("MINI_CODEC_PEER_UID", "0");
    }
    Ok(())
}

fn slot(dir: &Path) -> Option<Option<(u8, File)>> {
    match std::fs::create_dir(dir) {
        Ok(()) => {
            let _ = std::fs::set_permissions(dir, std::os::unix::fs::PermissionsExt::from_mode(0o700));
        }
        Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
        Err(_) => return None,
    }
    for n in [1u8, 2] {
        let file = OpenOptions::new().append(true).create(true).mode(0o600).open(dir.join(n.to_string())).ok()?;
        if unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } == 0 {
            return Some(Some((n, file)));
        }
    }
    Some(None)
}

/// FNV-1a over the key's parts, twice with different bases: a name, not a secret.
fn key(parts: &[&[u8]]) -> String {
    let mut out = String::new();
    for basis in [0xcbf2_9ce4_8422_2325u64, 0x8422_2325_cbf2_9ce4] {
        let mut hash = basis;
        for part in parts {
            for byte in (part.len() as u64).to_le_bytes().iter().chain(part.iter()) {
                hash ^= u64::from(*byte);
                hash = hash.wrapping_mul(0x0100_0000_01b3);
            }
        }
        out.push_str(&format!("{hash:016x}"));
    }
    out
}

fn send(stream: &UnixStream, body: &[u8]) -> std::io::Result<()> {
    let fds = [0i32, 1, 2];
    let space = unsafe { libc::CMSG_SPACE(12) } as usize;
    let mut control = vec![0u8; space];
    let mut iov = libc::iovec { iov_base: body.as_ptr() as *mut _, iov_len: body.len() };
    let mut message: libc::msghdr = unsafe { std::mem::zeroed() };
    message.msg_iov = &mut iov;
    message.msg_iovlen = 1;
    message.msg_control = control.as_mut_ptr().cast();
    message.msg_controllen = space as _;
    let sent = unsafe {
        let header = libc::CMSG_FIRSTHDR(&message);
        (*header).cmsg_level = libc::SOL_SOCKET;
        (*header).cmsg_type = libc::SCM_RIGHTS;
        (*header).cmsg_len = libc::CMSG_LEN(12) as _;
        std::ptr::copy_nonoverlapping(fds.as_ptr(), libc::CMSG_DATA(header) as *mut i32, 3);
        libc::sendmsg(stream.as_raw_fd(), &message, 0)
    };
    if sent < 0 {
        return Err(std::io::Error::last_os_error());
    }
    let mut rest = &body[sent as usize..];
    let mut stream = stream;
    while !rest.is_empty() {
        let n = stream.write(rest)?;
        rest = &rest[n..];
    }
    Ok(())
}

/// One line through the resident for the call slot this process takes. `shell` is the `mini`
/// argument vector without the slot and the line; `fallback` is the whole vector a fresh `mini`
/// runs when no resident can be used.
fn line(mini: &OsStr, shell: &[OsString], slots: &Path, text: &OsStr, fallback: &[OsString]) -> ExitCode {
    let (n, held) = match slot(slots) {
        None => return exec(mini, fallback),
        Some(None) => {
            eprintln!("mini-shell-ssh: two calls already running for this member; wait for one to finish");
            return ExitCode::from(75);
        }
        Some(Some(taken)) => taken,
    };
    let Ok(meta) = std::fs::metadata(mini) else { return exec(mini, fallback) };
    let identity = format!("{} {} {} {} {} {}", meta.dev(), meta.ino(), meta.size(), meta.mtime(), meta.mtime_nsec(), meta.ctime());
    let umask = unsafe { let m = libc::umask(0o077); libc::umask(m); m };
    let mut env: Vec<(OsString, OsString)> = std::env::vars_os()
        .filter(|(k, _)| k.as_bytes().starts_with(b"MINI_") || k == "HOME" || k == "PATH").collect();
    env.sort();
    let mut parts: Vec<Vec<u8>> = vec![identity.into_bytes(), umask.to_string().into_bytes()];
    parts.extend(shell.iter().map(|a| a.as_bytes().to_vec()));
    parts.push(b"--line".to_vec());
    for (k, v) in &env {
        parts.push([k.as_bytes(), b"=", v.as_bytes()].concat());
    }
    let refs: Vec<&[u8]> = parts.iter().map(Vec::as_slice).collect();
    let socket = slots.join(format!("r{n}-{}.sock", key(&refs)));
    if socket.as_os_str().len() > 100 {
        drop(held);
        return exec(mini, fallback);
    }
    let config = shell.iter().position(|a| a == "--config").and_then(|i| shell.get(i + 1)).cloned().unwrap_or_default();
    let stream = match UnixStream::connect(&socket) {
        Ok(stream) => Some(stream),
        Err(_) => {
            let started = Command::new(mini).arg("line-resident").arg(&socket).arg(&config)
                .stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::null())
                .process_group(0).status();
            let deadline = Instant::now() + Duration::from_secs(5);
            let mut connected = None;
            while started.as_ref().is_ok_and(|s| s.success()) && Instant::now() < deadline {
                if let Ok(stream) = UnixStream::connect(&socket) {
                    connected = Some(stream);
                    break;
                }
                std::thread::sleep(Duration::from_millis(1));
            }
            connected
        }
    };
    let Some(mut stream) = stream else {
        drop(held);
        return exec(mini, fallback);
    };
    let words: Vec<&OsStr> = shell.iter().map(OsString::as_os_str).chain([OsStr::new("--line"), text]).collect();
    let mut body = (words.len() as u32).to_be_bytes().to_vec();
    for a in &words {
        body.extend((a.len() as u32).to_be_bytes());
        body.extend(a.as_bytes());
    }
    if send(&stream, &body).is_err() {
        drop(held);
        return exec(mini, fallback);
    }
    let mut code = [0u8; 1];
    match stream.read(&mut code) {
        Ok(1) => {
            drop(held);
            ExitCode::from(code[0])
        }
        _ => {
            eprintln!("mini-shell-ssh: the member's resident shell ended during this line; whether it took effect is unknown (`history` shows what was kept)");
            ExitCode::from(70)
        }
    }
}

fn main() -> ExitCode {
    let mut argv = std::env::args_os();
    let program = argv.next().unwrap_or_default();
    let paths: Vec<OsString> = argv.collect();
    let Ok([mini, host, config, socket, workspace, home]) = <[OsString; 6]>::try_from(paths.clone()) else {
        eprintln!("{USAGE}");
        return ExitCode::from(64);
    };
    if !paths.iter().all(|p| p.as_bytes().starts_with(b"/")) {
        eprintln!("mini-shell-ssh paths must be absolute");
        return ExitCode::from(64);
    }
    let executable = std::ffi::CString::new(mini.as_bytes()).is_ok_and(|c| unsafe { libc::access(c.as_ptr(), libc::X_OK) } == 0);
    if !executable {
        eprintln!("mini client is not executable");
        return ExitCode::from(66);
    }
    unsafe { libc::umask(0o077) };
    let home = PathBuf::from(home);
    if let Err(refusal) = session_environment(Path::new(&mini), &host, &config, &home) {
        eprintln!("mini-shell-ssh: {refusal}");
        return ExitCode::from(78);
    }
    let shell: Vec<OsString> = [
        "shell".into(), "--socket".into(), socket, "--host".into(), host, "--config".into(), config,
        "--workspace".into(), workspace, "--home".into(), home.clone().into_os_string(),
    ].to_vec();
    let slots = home.join(".call-slots");
    let mut full = shell.clone();
    full.extend(["--call-slots".into(), slots.clone().into_os_string()]);
    match std::env::var_os("SSH_ORIGINAL_COMMAND").filter(|c| !c.is_empty()) {
        Some(text) => {
            let mut fallback = full;
            fallback.extend(["--line".into(), text.clone()]);
            line(&mini, &shell, &slots, &text, &fallback)
        }
        None => {
            // Interactive login only: the motd, then the re-genesis notice ship.sh --regenesis
            // writes (and ember deletes when it is old news), to stderr before the prompt. Both
            // live beside this program (/usr/local/lib/mini on the box).
            if program.as_bytes().contains(&b'/') {
                let lib = Path::new(&program).parent().unwrap_or(Path::new("/"));
                let mut stderr = std::io::stderr().lock();
                for note in ["motd.txt", "notice.txt"] {
                    if let Ok(mut text) = std::fs::read(lib.join(note)) {
                        while text.last() == Some(&b'\n') {
                            text.pop();
                        }
                        text.push(b'\n');
                        let _ = stderr.write_all(&text);
                    }
                }
            }
            exec(&mini, &full)
        }
    }
}
