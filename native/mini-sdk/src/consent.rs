//! The member's local consent provider (`minidregg-client-consent`, `Host/ClientConsentCore`),
//! started as `CONSENT SETTINGS stdio` by local custody only. The plan check is Lean
//! (`NativeClientConsent`, `NativeSpecializedConsent`, `NativeThinConsent`); this module frames
//! requests to it and keeps its admitted frontier, so there is exactly one check.
//!
//! Frames (READ `Host/ClientConsentCore.lean`): 220 intent, 221 observation, 222 plan, 224
//! operator (specialized) plan, 226 possession, 227 Objective, 228 offer a retained anchor, 229
//! the anchor of what was admitted, 230–232 thin consent and 234–235 thin birth consent (no Store read), 233 the Store re-check
//! against the held admission: answered at once and owed, the provider makes it on the next
//! frame's own Store read before answering that frame, so a 233 reply alone proves nothing about
//! the Store; only the frame after it does (`ClientConsentCore.serve`).
//!
//! **Retained anchors.** The provider admits the Store's history before its first consent frame.
//! The provider starts from the Store's MAC-verified checkpoint (CONSENT-STORE, the storage device
//! is trusted) and natively admits every record after it. What it admitted is kept as a retained
//! anchor (`Kernel.ConsentAnchor`) in a private file under the anchor directory, named by and bound
//! to the settings without their executable paths ([`crate::local::anchor_binding`]): a ship that
//! moves only binaries keeps it. The next provider is offered it (228) before admission: it starts
//! there when the anchor is above the Store's checkpoint, and refuses a Store that rolled back or
//! rewrote the anchored prefix. A provider of another consent epoch sets the anchor aside
//! (`ConsentAnchor.decode`) and starts from the checkpoint; changed settings never see it.
//!
//! **The resident provider.** A process that starts its own provider pays a Store admission
//! from the retained anchor before its first frame and drops the warm frontier on exit. The
//! resident provider ([`serve_resident`]) is that same provider, kept: ONE provider child per
//! binding, started as [`start`] starts one, relaying each client connection's frames to it one at
//! a time. Each connection's first frame is preceded by 233 (`ConsentAnchor.checkHeld`, made on that
//! frame's own read), so a rolled-back Store refuses the next command as a new provider would. A refusal there, or a dead
//! provider, ends the resident; the next command starts a new one from the retained anchor. Its
//! socket lives in the owner-private anchor directory (Linux uses a directory descriptor
//! when that address is too long), and both ends check the peer is this user.
//!
//! **The resident codec Host** ([`ResidentKind::Codec`]) is the same machinery holding the
//! member's storeless codec image (`HOST SETTINGS codec`, [`crate::local`]) instead of a consent
//! provider: ONE child per binding for every process of this user, where each process used to
//! start its own 159 MB Lean image. The codec is pure (`Host.Main.pureCodec` holds no state
//! between frames), so the reply bytes are the same function of the frame whichever process's
//! connection carries it; there is no Store to re-check and no anchor to retain. The image it
//! holds is the client's own selected semantic Host (`MINI_LOCAL_HOST`), never the serving
//! Store's: the operator selects that one.
use std::fs::{self, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Mutex;

use serde_json::{json, Value};

use crate::host_operations::CONSENT_PLANS;

/// The consent provider's own refusal byte: `Host/ClientConsentCore.lean` answers `255 ‖ reason`
/// for every frame it refuses. This is the local consent protocol's framing, not a reply marker
/// of the Host request registry (whose 255 is the undecided outcome envelope).
pub const CONSENT_REFUSAL: u8 = 255;
use crate::local::{anchor_binding, binding, pair, settings_bytes, Session, CAP};
use crate::{Error, Result};

/// Custody framing of a retained anchor: this tag, the 32-byte binding, then the provider's bytes.
const ANCHOR_TAG: &[u8] = b"MINI-CONSENT-ANCHOR-CUSTODY/v1\n";
const ANCHOR_CAP: u64 = 4096;

/// `Kernel.NativeClientConsent.staleObservationTag`: the provider's refusal of an observation
/// challenge that answers this exact retained intent and signature at another source height than
/// the one it admitted (the source moved between the Host's challenge and the local check).
pub const STALE_OBSERVATION_TAG: &str = "stale observation:";

pub(crate) struct AnchorCustody {
    path: PathBuf,
    binding: [u8; 32],
    retained: Option<Vec<u8>>,
}

/// How a consent frame failed.
#[derive(Debug, Clone, PartialEq)]
pub enum ConsentError {
    /// The provider answered `answer` (not the request's own byte) with this detail: it refused
    /// before anything was signed.
    Refused { operation: u8, answer: u8, detail: Vec<u8> },
    /// No answer: the provider could not be reached, died, or framed its reply wrongly.
    Failed(Error),
}

impl ConsentError {
    /// The provider's refusal of an observation (221) as stale: the source moved between the
    /// Host's challenge and the local check. Every other refusal stays terminal.
    pub fn is_stale_observation(&self) -> bool {
        matches!(self, ConsentError::Refused { operation: crate::host_operations::CONSENT_OBSERVATION, answer: CONSENT_REFUSAL, detail }
            if detail.starts_with(STALE_OBSERVATION_TAG.as_bytes()))
    }
}

impl std::fmt::Display for ConsentError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConsentError::Refused { detail, .. } => {
                write!(f, "local consent refused before signing: {}", String::from_utf8_lossy(detail))
            }
            ConsentError::Failed(e) => f.write_str(&e.0),
        }
    }
}

impl From<Error> for ConsentError {
    fn from(e: Error) -> Self {
        ConsentError::Failed(e)
    }
}
impl From<&str> for ConsentError {
    fn from(e: &str) -> Self {
        ConsentError::Failed(e.into())
    }
}
impl From<ConsentError> for Error {
    fn from(e: ConsentError) -> Self {
        Error(e.to_string())
    }
}
impl From<ConsentError> for String {
    fn from(e: ConsentError) -> Self {
        e.to_string()
    }
}

/// One frame to the provider, judged: the body when it answered the request's own byte.
pub fn round_trip(session: &mut Session, operation: u8, payload: &[u8]) -> std::result::Result<Vec<u8>, ConsentError> {
    let (answer, body) = session.exchange(operation, payload)?;
    if answer != operation {
        return Err(ConsentError::Refused { operation, answer, detail: body });
    }
    Ok(body)
}

/// The anchor directory: `$MINI_CONSENT_ANCHOR_DIR`, else `$HOME/.mini/consent-anchors`.
pub fn anchor_dir() -> Result<PathBuf> {
    if let Some(dir) = std::env::var_os("MINI_CONSENT_ANCHOR_DIR") {
        let dir = PathBuf::from(dir);
        if !dir.is_absolute() {
            return Err("MINI_CONSENT_ANCHOR_DIR must be absolute".into());
        }
        return Ok(dir);
    }
    Ok(PathBuf::from(std::env::var_os("HOME").ok_or("retained consent anchors need $HOME or MINI_CONSENT_ANCHOR_DIR")?)
        .join(".mini/consent-anchors"))
}

/// The anchor directory, created owner-private, refused when it is not.
pub fn private_anchor_dir() -> Result<PathBuf> {
    use std::os::unix::fs::{DirBuilderExt, MetadataExt};
    let dir = anchor_dir()?;
    fs::DirBuilder::new().recursive(true).mode(0o700).create(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let meta = fs::symlink_metadata(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    if !meta.is_dir() || meta.uid() != unsafe { libc::geteuid() } || meta.mode() & 0o077 != 0 {
        return Err(format!("consent anchor directory {} must be an owner-private directory", dir.display()).into());
    }
    Ok(dir)
}

/// One file per binding: a provider admits only under its own.
fn anchor_path(anchors: &Path, binding: &[u8; 32]) -> PathBuf {
    anchors.join(format!("{}.anchor", crate::hex::encode(binding)))
}

/// The retained anchor bytes for this binding: `None` when there is no file or it was written
/// under another binding. A file that is not owner-private and regular, or not this custody
/// format, refuses.
fn read_anchor(path: &Path, binding: &[u8; 32]) -> Result<Option<Vec<u8>>> {
    use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
    let file = match OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW).open(path) {
        Ok(file) => file,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(format!("retained consent anchor {}: {e}", path.display()).into()),
    };
    let meta = file.metadata().map_err(|e| e.to_string())?;
    if !meta.is_file() || meta.uid() != unsafe { libc::geteuid() } || meta.mode() & 0o077 != 0 {
        return Err(format!("retained consent anchor {} must be an owner-private regular file", path.display()).into());
    }
    let mut bytes = Vec::new();
    file.take(ANCHOR_CAP + 1).read_to_end(&mut bytes).map_err(|e| e.to_string())?;
    if bytes.len() as u64 > ANCHOR_CAP {
        return Err(format!("retained consent anchor {} exceeds its bound", path.display()).into());
    }
    let Some(rest) = bytes.strip_prefix(ANCHOR_TAG) else {
        return Err(format!("retained consent anchor {} is not MINI-CONSENT-ANCHOR-CUSTODY/v1", path.display()).into());
    };
    if rest.len() <= 32 {
        return Err(format!("retained consent anchor {} is truncated", path.display()).into());
    }
    if rest[..32] != binding[..] {
        return Ok(None);
    }
    Ok(Some(rest[32..].to_vec()))
}

fn anchor_file(binding: &[u8; 32], anchor: &[u8]) -> Vec<u8> {
    [ANCHOR_TAG, binding.as_slice(), anchor].concat()
}

/// Ask the provider for the anchor of what it admitted and retain it when it moved. Complete or
/// absent ([`crate::durable::replace`]): a crash leaves the previous anchor, from which the next
/// provider admits a longer suffix. A failure here costs only that; it is reported, not fatal.
pub fn retain_anchor(session: &mut Session) {
    retain_anchor_with(session, &mut |_| Ok(()))
}

fn retain_anchor_with(session: &mut Session, observe: &mut dyn FnMut(crate::durable::Stage) -> io::Result<()>) {
    if session.anchor.is_none() {
        return;
    }
    let anchor = match round_trip(session, crate::host_operations::CONSENT_ANCHOR_ADMITTED, &[]) {
        Ok(anchor) => anchor,
        Err(_) => return, // nothing admitted yet (a refused first admission ends the provider)
    };
    let custody = session.anchor.as_mut().expect("anchor custody");
    if custody.retained.as_deref() == Some(anchor.as_slice()) {
        return;
    }
    if let Some(parent) = custody.path.parent() {
        use std::os::unix::fs::DirBuilderExt;
        if let Err(e) = fs::DirBuilder::new().recursive(true).mode(0o700).create(parent) {
            eprintln!("mini: warning: cannot create {}: {e}", parent.display());
            return;
        }
    }
    match crate::durable::replace_with(&custody.path, &anchor_file(&custody.binding, &anchor), crate::durable::Perm::Private, observe) {
        Ok(()) => custody.retained = Some(anchor),
        Err(e) => eprintln!("mini: warning: cannot retain the consent anchor {}: {e}", custody.path.display()),
    }
}

/// Start a provider in this process and offer it this binding's retained anchor before any
/// admission. A refusal of the offer (another epoch, noncanonical bytes) is reported, never
/// silently replaced by a genesis admission.
pub fn start(anchors: &Path, executable: PathBuf, settings: &Path, settings_bytes: Vec<u8>) -> Result<Session> {
    let binding = anchor_binding(&settings_bytes)?;
    let path = anchor_path(anchors, &binding);
    let retained = read_anchor(&path, &binding)?;
    let what = format!("local consent provider {}", executable.display());
    let mut session = Session::spawn(executable, settings, settings_bytes, "stdio", &what)?;
    session.anchor = Some(AnchorCustody { path: path.clone(), binding, retained: retained.clone() });
    if let Some(anchor) = retained {
        round_trip(&mut session, crate::host_operations::CONSENT_ANCHOR_OFFER, &anchor).map_err(|e| format!("retained consent anchor {}: {e}", path.display()))?;
    }
    Ok(session)
}

/// Which resident a binding's socket serves: the consent provider (`r-`, `CONSENT SETTINGS
/// stdio`) or the storeless codec Host (`c-`, `HOST SETTINGS codec`, frames 7–11). Both live in
/// the owner-private anchor directory, both are keyed by [`binding`] (executable identity and
/// settings bytes), both hold one child under a flock with a PID file, check the peer's uid and
/// end when idle; only the consent one re-checks the Store per connection and retains an anchor.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ResidentKind {
    Consent,
    Codec,
}

impl ResidentKind {
    fn prefix(self) -> &'static str {
        match self {
            Self::Consent => "r",
            Self::Codec => "c",
        }
    }
    /// The resident's name in errors and logs.
    pub fn name(self) -> &'static str {
        match self {
            Self::Consent => "resident consent provider",
            Self::Codec => "resident codec Host",
        }
    }
    /// The one child a resident of this kind holds.
    fn start(self, anchors: &Path, executable: PathBuf, settings: &Path, settings_bytes: Vec<u8>) -> Result<Session> {
        match self {
            Self::Consent => start(anchors, executable, settings, settings_bytes),
            Self::Codec => Session::spawn(executable, settings, settings_bytes, "codec", "local native codec"),
        }
    }
}

/// `<r|c>-<first 16 bytes of the binding>.<suffix>`: a Unix socket path must fit `sun_path`.
fn resident_file(kind: ResidentKind, dir: &Path, binding: &[u8; 32], suffix: &str) -> PathBuf {
    dir.join(format!("{}-{}.{suffix}", kind.prefix(), crate::hex::encode(&binding[..16])))
}

/// Long Linux addresses traverse an open anchor directory through procfs. The
/// socket node stays beside the anchors, so PrivateTmp cannot split discovery.
/// Keep the descriptor alive while binding, connecting and cleaning the socket.
fn resident_socket(kind: ResidentKind, anchors: &Path, binding: &[u8; 32]) -> Result<(PathBuf, Option<fs::File>)> {
    use std::os::unix::ffi::OsStrExt;
    let ordinary = resident_file(kind, anchors, binding, "sock");
    if ordinary.as_os_str().as_bytes().len() < 100 { return Ok((ordinary, None)); }
    if !crate::private::dir_ok(&fs::symlink_metadata(anchors).map_err(|e| e.to_string())?) {
        return Err("resident anchor directory must be owner-private, not a symlink".into());
    }
    #[cfg(target_os = "linux")]
    {
        use std::os::fd::AsRawFd;
        use std::os::unix::fs::OpenOptionsExt;
        let directory = OpenOptions::new().read(true)
            .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(anchors).map_err(|e| format!("resident anchor directory: {e}"))?;
        if !crate::private::dir_ok(&directory.metadata().map_err(|e| e.to_string())?) {
            return Err("resident anchor directory must be owner-private".into());
        }
        let alias = PathBuf::from(format!("/proc/self/fd/{}", directory.as_raw_fd()));
        return Ok((resident_file(kind, &alias, binding, "sock"), Some(directory)));
    }
    #[cfg(not(target_os = "linux"))]
    {
        use sha2::Digest;
        use std::os::unix::fs::{DirBuilderExt, MetadataExt};
    let root = PathBuf::from(format!("/tmp/mipc-{}", unsafe { libc::geteuid() }));
    let private_dir = |path: &Path| -> Result<()> {
        match fs::DirBuilder::new().mode(0o700).create(path) {
            Ok(()) => (),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => (),
            Err(error) => return Err(format!("resident IPC directory {}: {error}", path.display()).into()),
        }
        let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
        if !crate::private::dir_ok(&meta) {
            return Err(format!("resident IPC directory {} must be an owner-private directory, not a symlink", path.display()).into());
        }
        Ok(())
    };
    private_dir(&root)?;
    let canonical = fs::canonicalize(anchors).map_err(|e| e.to_string())?;
    let meta = fs::metadata(&canonical).map_err(|e| e.to_string())?;
    let mut hash = sha2::Sha256::new();
    hash.update(b"MINI-RESIDENT-IPC-DIRECTORY/v1\0");
    hash.update(canonical.as_os_str().as_bytes());
    hash.update(meta.dev().to_le_bytes());
    hash.update(meta.ino().to_le_bytes());
    let digest = hash.finalize();
    let directory = root.join(crate::hex::encode(&digest[..16]));
    private_dir(&directory)?;
    Ok((resident_file(kind, &directory, binding, "sock"), None))
    }
}

/// A connection to a listening resident provider of this user, or an error.
fn resident_stream(socket: &Path) -> Result<std::os::unix::net::UnixStream> {
    use std::os::unix::fs::FileTypeExt;
    let meta = fs::symlink_metadata(socket).map_err(|e| e.to_string())?;
    if !meta.file_type().is_socket() || !crate::private::owned(&meta) {
        return Err(format!("{} is not this user's socket", socket.display()).into());
    }
    let stream = std::os::unix::net::UnixStream::connect(socket).map_err(|e| e.to_string())?;
    if crate::private::peer_uid(&stream)? != unsafe { libc::geteuid() } {
        return Err("the resident process runs as another user".into());
    }
    Ok(stream)
}

/// Connect to this binding's resident provider, starting it when none listens. `launch` is the
/// command that serves [`serve_resident`] for this executable and settings (the client binary's
/// own `consent-resident` verb); it is started in its own session, so it outlives this process
/// and never takes its terminal's signals, with its stderr in the binding's log.
pub fn connect_resident(executable: &Path, settings_bytes: Vec<u8>, launch: Command) -> Result<Session> {
    connect_resident_kind(ResidentKind::Consent, executable, settings_bytes, launch)
}

/// [`connect_resident`], with a second handle on the connection for the caller to watch between
/// frames: a resident that ended (killed, or its provider failed) closes it, and a caller that
/// holds its session for hours (a web body) must notice before it sends, then connect again (the
/// next resident starts from the binding's retained anchor).
pub fn connect_resident_watched(executable: &Path, settings_bytes: Vec<u8>, launch: Command) -> Result<(Session, std::os::unix::net::UnixStream)> {
    let stream = resident_connection(ResidentKind::Consent, executable, &settings_bytes, launch)?;
    let watch = stream.try_clone().map_err(|e| e.to_string())?;
    let input = stream.try_clone().map_err(|e| e.to_string())?;
    Ok((Session::over(Box::new(input), Box::new(stream), executable.to_path_buf(), settings_bytes), watch))
}

/// Make `command` a daemon of its own session that inherits nothing from its caller but stdio: every
/// fd above 2 is marked close-on-exec, so a lock or socket the caller holds (a `flock` wrapper's
/// fd, a journey's pipe) is never kept alive by a resident that outlives it. Marking, rather than
/// closing, leaves the standard library's exec-error pipe intact.
fn detach(command: &mut Command) {
    use std::os::unix::process::CommandExt;
    unsafe {
        command.pre_exec(|| {
            if libc::setsid() < 0 {
                return Err(io::Error::last_os_error());
            }
            #[cfg(target_os = "linux")]
            if libc::syscall(libc::SYS_close_range, 3u32, u32::MAX, 4u32 /* CLOSE_RANGE_CLOEXEC */) == 0 {
                return Ok(());
            }
            for fd in 3..4096 {
                let flags = libc::fcntl(fd, libc::F_GETFD);
                if flags >= 0 {
                    libc::fcntl(fd, libc::F_SETFD, flags | libc::FD_CLOEXEC);
                }
            }
            Ok(())
        });
    }
}

/// Connect to this binding's resident of `kind`, starting it when none listens. `launch` is the
/// command that serves [`serve_resident_kind`] of this kind for this executable and settings (the
/// client binary's own `consent-resident` or `codec-resident` verb).
pub fn connect_resident_kind(kind: ResidentKind, executable: &Path, settings_bytes: Vec<u8>, launch: Command) -> Result<Session> {
    let stream = resident_connection(kind, executable, &settings_bytes, launch)?;
    let input = stream.try_clone().map_err(|e| e.to_string())?;
    Ok(Session::over(Box::new(input), Box::new(stream), executable.to_path_buf(), settings_bytes))
}

/// A connection to this binding's resident of `kind`, starting it when none listens.
fn resident_connection(kind: ResidentKind, executable: &Path, settings_bytes: &[u8], launch: Command) -> Result<std::os::unix::net::UnixStream> {
    resident_connection_in(&private_anchor_dir()?, kind, executable, settings_bytes, launch)
}

/// [`connect_resident_kind`] in the resident directory `dir` (owner-private) rather than this
/// process's own: split tenancy's delegated consent workers all reach the operator's ONE shared
/// consent resident there. `launch` must serve that same directory (MINI_CONSENT_ANCHOR_DIR=`dir`).
pub fn connect_resident_in(dir: &Path, kind: ResidentKind, executable: &Path, settings_bytes: Vec<u8>, launch: Command) -> Result<Session> {
    if !crate::private::dir_ok(&fs::symlink_metadata(dir).map_err(|e| format!("{}: {e}", dir.display()))?) {
        return Err(format!("resident directory {} must be an owner-private directory", dir.display()).into());
    }
    let stream = resident_connection_in(dir, kind, executable, &settings_bytes, launch)?;
    let input = stream.try_clone().map_err(|e| e.to_string())?;
    Ok(Session::over(Box::new(input), Box::new(stream), executable.to_path_buf(), settings_bytes))
}

fn resident_connection_in(dir: &Path, kind: ResidentKind, executable: &Path, settings_bytes: &[u8], launch: Command) -> Result<std::os::unix::net::UnixStream> {
    use std::os::unix::fs::OpenOptionsExt;
    use std::os::unix::process::CommandExt;
    let dir = dir.to_path_buf();
    let binding = binding(executable, settings_bytes)?;
    let (socket, _socket_directory) = resident_socket(kind, &dir, &binding)?;
    let stream = match resident_stream(&socket) {
        Ok(stream) => stream,
        Err(_) => {
            let log = resident_file(kind, &dir, &binding, "log");
            let errors = OpenOptions::new().create(true).append(true).mode(0o600).custom_flags(libc::O_NOFOLLOW)
                .open(&log).map_err(|e| format!("{}: {e}", log.display()))?;
            let mut command = launch;
            command.stdin(Stdio::null()).stdout(Stdio::null()).stderr(errors);
            detach(&mut command);
            let mut daemon = command.spawn().map_err(|e| format!("cannot start the {}: {e}", kind.name()))?;
            let began = std::time::Instant::now();
            loop {
                if let Ok(stream) = resident_stream(&socket) {
                    break stream;
                }
                if let Some(status) = daemon.try_wait().map_err(|e| e.to_string())? {
                    // Exit 0 without a socket: another start holds the binding's lock and is
                    // still starting; keep waiting for its socket.
                    if !status.success() {
                        return Err(format!("{} failed to start ({status}); see {}", kind.name(), log.display()).into());
                    }
                }
                if began.elapsed() > std::time::Duration::from_secs(300) {
                    return Err(format!("{} did not listen within 300 s; see {}", kind.name(), log.display()).into());
                }
                std::thread::sleep(std::time::Duration::from_millis(5));
            }
        }
    };
    Ok(stream)
}

/// Removes the resident provider's socket and PID file when it ends, if they are still its own.
struct ResidentFiles {
    socket: PathBuf,
    pid: PathBuf,
    identity: (u64, u64),
}
impl Drop for ResidentFiles {
    fn drop(&mut self) {
        use std::os::unix::fs::MetadataExt;
        if fs::symlink_metadata(&self.socket).is_ok_and(|m| (m.dev(), m.ino()) == self.identity) {
            let _ = fs::remove_file(&self.socket);
        }
        let _ = fs::remove_file(&self.pid);
    }
}
struct Resident {
    session: Session,
    ended: bool,
}

/// Make this single-threaded process its starter's grandchild before it serves: the starter
/// (`resident_connection`) reaps the exit 0 and waits for the socket, so a resident is never a
/// long-lived client's child (a zombie at its idle exit, the wrong parent for the controller's
/// codec proof). True in the process that goes on to serve.
pub fn daemonize() -> Result<bool> {
    match unsafe { libc::fork() } {
        -1 => Err(format!("resident fork: {}", io::Error::last_os_error()).into()),
        0 => Ok(true),
        _ => Ok(false),
    }
}

/// Hold one provider for this binding and serve its frames on the binding's socket in `dir`
/// until the provider ends, the binding is superseded, or (`Some(idle)` only) no frame arrives
/// for `idle`. Exits at once (Ok) when another resident provider holds the binding.
pub fn serve_resident(dir: &Path, executable: PathBuf, settings: PathBuf, idle: Option<std::time::Duration>) -> Result<()> {
    serve_resident_kind(ResidentKind::Consent, dir, executable, settings, idle)
}

/// Hold one child of `kind` for this binding (a consent provider, or the storeless codec Host)
/// and serve its frames on the binding's socket in `dir`, one frame at a time across every
/// connection. Exits at once (Ok) when another resident of this kind holds the binding.
///
/// A resident keeps its warm state: with `idle` None (every member's resident) it never idles
/// out, so a member who comes back after an hour pays no provider start and no Store admission
/// from the retained anchor. It ends when its child ends, when its world is torn down (the Store
/// directory its settings name, `storageRoot`, removed), when its socket is unlinked or replaced,
/// or when its binding is superseded: another file at its
/// executable path (a `candidate/current` repointed by a ship) or other bytes at its settings path,
/// so no client can select this binding again. `Some(idle)` adds the idle exit.
///
/// Every client whose executable and settings bytes agree computes the same binding, so a box that
/// gives its hosted members one resident directory (`MINI_CONSENT_ANCHOR_DIR`; they run as one
/// account and their settings are the box's pinned config) runs ONE consent provider and ONE codec
/// Host for all of them.
pub fn serve_resident_kind(kind: ResidentKind, dir: &Path, executable: PathBuf, settings: PathBuf, idle: Option<std::time::Duration>) -> Result<()> {
    use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
    use std::os::unix::io::AsRawFd;
    use std::sync::{atomic::{AtomicBool, AtomicUsize, Ordering}, Arc};
    if !executable.is_absolute() || !settings.is_absolute() {
        return Err(format!("{}: executable and settings must be absolute", kind.name()).into());
    }
    let settings_bytes = settings_bytes(&settings)?;
    let binding = binding(&executable, &settings_bytes)?;
    let lock_path = resident_file(kind, dir, &binding, "lock");
    let lock = OpenOptions::new().create(true).read(true).write(true).mode(0o600).custom_flags(libc::O_NOFOLLOW)
        .open(&lock_path).map_err(|e| format!("{}: {e}", lock_path.display()))?;
    if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        return Ok(()); // another resident of this kind holds this binding
    }
    let (socket, _socket_directory) = resident_socket(kind, dir, &binding)?;
    crate::private::clear_stale_socket(&socket)?;
    let executable_path = executable.clone();
    // The Store the settings name (`storageRoot`): when it is gone the world is gone, whatever
    // else of it (the resident directory, the executables, the settings copy) lives elsewhere.
    let store_root = serde_json::from_slice::<serde_json::Value>(&settings_bytes).ok()
        .and_then(|v| v.get("storageRoot").and_then(|r| r.as_str()).map(PathBuf::from))
        .filter(|root| root.is_absolute() && fs::symlink_metadata(root).is_ok());
    let executable_started = fs::metadata(&executable_path).map_err(|e| format!("{}: {e}", executable_path.display()))?;
    let session = kind.start(dir, executable, &settings, settings_bytes)?;
    let listener = std::os::unix::net::UnixListener::bind(&socket)
        .map_err(|e| format!("{} socket {}: {e}", kind.name(), socket.display()))?;
    fs::set_permissions(&socket, fs::Permissions::from_mode(0o600)).map_err(|e| e.to_string())?;
    let meta = fs::symlink_metadata(&socket).map_err(|e| e.to_string())?;
    let pid = resident_file(kind, dir, &binding, "pid");
    let _files = ResidentFiles { socket: socket.clone(), pid: pid.clone(), identity: (meta.dev(), meta.ino()) };
    crate::durable::replace(&pid, format!("{}\n", std::process::id()).as_bytes(), crate::durable::Perm::Private)
        .map_err(|e| format!("{}: {e}", pid.display()))?;
    listener.set_nonblocking(true).map_err(|e| e.to_string())?;
    let shared = Arc::new(Mutex::new(Resident { session, ended: false }));
    let last = Arc::new(Mutex::new(std::time::Instant::now()));
    let active = Arc::new(AtomicUsize::new(0));
    let ended = Arc::new(AtomicBool::new(false));
    let mut looked = std::time::Instant::now();
    loop {
        if ended.load(Ordering::Acquire) {
            return Ok(());
        }
        match listener.accept() {
            Ok((stream, _)) => {
                active.fetch_add(1, Ordering::AcqRel);
                let (shared, last, active, ended) = (shared.clone(), last.clone(), active.clone(), ended.clone());
                std::thread::spawn(move || {
                    serve_connection(kind, stream, &shared, &last, &ended);
                    active.fetch_sub(1, Ordering::AcqRel);
                });
            }
            Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                let quiet = last.lock().map(|t| t.elapsed()).unwrap_or_default();
                if active.load(Ordering::Acquire) == 0 && idle.is_some_and(|idle| quiet > idle) {
                    return Ok(());
                }
                // Its world torn down (the Store its settings name removed, or its directory and socket), its
                // socket unlinked or replaced, or
                // its binding superseded (another executable at its path, other bytes at its settings path):
                // no client can bind it or reach it again, so it ends now.
                if looked.elapsed() >= std::time::Duration::from_secs(1) {
                    looked = std::time::Instant::now();
                    if !socket_is(&socket, _files.identity)
                        || store_root.as_ref().is_some_and(|root| fs::symlink_metadata(root).is_err())
                        || active.load(Ordering::Acquire) == 0 && superseded(&executable_path, &executable_started, &settings, &binding)
                    {
                        return Ok(());
                    }
                }
                // Wait on the listener itself: a connection is accepted the moment it arrives,
                // and an idle resident wakes once a second for the checks above.
                let mut ready = libc::pollfd { fd: listener.as_raw_fd(), events: libc::POLLIN, revents: 0 };
                unsafe { libc::poll(&mut ready, 1, 1000) };
            }
            Err(e) => return Err(format!("{} accept: {e}", kind.name()).into()),
        }
    }
}

/// The binding a client would compute now differs from the one this resident serves: another
/// file at its executable path (a ship repointing `candidate/current`, or the file removed), or
/// other bytes at the settings path it was started with. A settings path that no longer exists
/// supersedes nothing: residents shared by a box's members are often started from an attempt's
/// copy of the settings, and retiring that attempt leaves every client's binding as it was.
fn superseded(executable: &Path, started: &std::fs::Metadata, settings: &Path, serving: &[u8; 32]) -> bool {
    use std::os::unix::fs::MetadataExt;
    let identity = |m: &std::fs::Metadata| (m.dev(), m.ino(), m.size(), m.mtime(), m.mtime_nsec(), m.ctime(), m.ctime_nsec());
    match fs::metadata(executable) {
        Ok(now) if identity(&now) == identity(started) => {}
        _ => return true,
    }
    match fs::symlink_metadata(settings) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => false,
        _ => settings_bytes(settings).and_then(|bytes| binding(executable, &bytes)).map_or(true, |now| &now != serving),
    }
}

/// The socket at `path` is still the one this resident bound (device and inode).
fn socket_is(path: &Path, identity: (u64, u64)) -> bool {
    use std::os::unix::fs::MetadataExt;
    fs::symlink_metadata(path).is_ok_and(|m| (m.dev(), m.ino()) == identity)
}

/// One client connection: frames in, the child's answers out, one frame at a time across all
/// connections. For the consent provider, the connection's first frame is preceded by the Store
/// re-check (233), and 228, 229 and 233 are the resident's own. For the codec Host every frame
/// is relayed as it is (nothing to re-check, nothing to retain), and a connection whose child
/// failed is closed without a reply: a 255 frame would read as the Host's own undecided outcome,
/// which it is not; the client's frame fails as it would with its own dead child, and its next
/// frame starts a new resident.
fn serve_connection(kind: ResidentKind, stream: std::os::unix::net::UnixStream, shared: &Mutex<Resident>,
    last: &Mutex<std::time::Instant>, ended: &std::sync::atomic::AtomicBool) {
    serve_connection_from(kind, stream, shared, last, ended, false)
}

/// [`serve_connection`]; `any_peer` (the box's codec service only) accepts a peer of any uid:
/// who may connect is the listener's own file permissions.
fn serve_connection_from(kind: ResidentKind, stream: std::os::unix::net::UnixStream, shared: &Mutex<Resident>,
    last: &Mutex<std::time::Instant>, ended: &std::sync::atomic::AtomicBool, any_peer: bool) {
    if stream.set_nonblocking(false).is_err() {
        return;
    }
    if !any_peer && crate::private::peer_uid(&stream).ok() != Some(unsafe { libc::geteuid() }) {
        return;
    }
    let (mut input, mut output) = match stream.try_clone() {
        Ok(reader) => (reader, stream),
        Err(_) => return,
    };
    let mut rechecked = false;
    loop {
        let mut width = [0u8; 4];
        if input.read_exact(&mut width).is_err() {
            return;
        }
        let size = u32::from_le_bytes(width) as usize;
        if size == 0 || size > CAP {
            return;
        }
        let mut frame = vec![0; size];
        if input.read_exact(&mut frame).is_err() {
            return;
        }
        if let Ok(mut t) = last.lock() {
            *t = std::time::Instant::now();
        }
        let operation = frame[0];
        let codec = kind == ResidentKind::Codec;
        let (answer, body) = match shared.lock() {
            Err(_) if codec => return,
            Err(_) => (CONSENT_REFUSAL, b"resident consent provider lock poisoned".to_vec()),
            Ok(mut resident) => {
                if resident.ended {
                    if codec {
                        return;
                    }
                    (CONSENT_REFUSAL, b"the resident consent provider ended; the next command starts a new one".to_vec())
                } else if !codec && matches!(operation, crate::host_operations::CONSENT_ANCHOR_OFFER | crate::host_operations::CONSENT_ANCHOR_ADMITTED | crate::host_operations::CONSENT_STORE_RECHECK) {
                    (CONSENT_REFUSAL, format!("frame {operation} is reserved to the resident consent provider").into_bytes())
                } else {
                    // The codec Host holds no Store: nothing to re-check, no anchor to retain.
                    let checked = if rechecked || codec {
                        Ok(())
                    } else {
                        match resident.session.exchange(crate::host_operations::CONSENT_STORE_RECHECK, &[]) {
                            Ok((crate::host_operations::CONSENT_STORE_RECHECK, _)) => Ok(()),
                            Ok((_, detail)) => Err(String::from_utf8_lossy(&detail).into_owned()),
                            Err(e) => Err(e.0),
                        }
                    };
                    rechecked = true;
                    match checked.and_then(|_| resident.session.exchange(operation, &frame[1..]).map_err(|e| e.0)) {
                        Ok(reply) => {
                            if !codec {
                                retain_anchor(&mut resident.session);
                            }
                            reply
                        }
                        Err(e) => {
                            resident.ended = true;
                            ended.store(true, std::sync::atomic::Ordering::Release);
                            if codec {
                                return;
                            }
                            (CONSENT_REFUSAL, e.into_bytes())
                        }
                    }
                }
            }
        };
        let reply = [(body.len() as u32 + 1).to_le_bytes().as_slice(), &[answer], &body].concat();
        if output.write_all(&reply).and_then(|_| output.flush()).is_err() {
            return;
        }
    }
}

/// A thin plan frame's reply: `{display, headers}` with the headers as hex.
fn thin_reply(reply: &[u8]) -> ConsentResult<(Value, Vec<Vec<u8>>)> {
    let value: Value = serde_json::from_slice(reply).map_err(|e| Error(format!("thin consent reply: {e}")))?;
    let display = value.get("display").cloned().ok_or("thin consent reply lacks display")?;
    let rows = value.get("headers").and_then(Value::as_array).ok_or("thin consent reply lacks headers")?;
    let headers = rows.iter()
        .map(|row| crate::hex::decode_any_case(row.as_str().ok_or("thin consent header is not hex")?))
        .collect::<Result<Vec<_>>>()?;
    Ok((display, headers))
}

fn headers(bytes: &[u8]) -> Result<Vec<Vec<u8>>> {
    let value: Value = serde_json::from_slice(bytes).map_err(|e| format!("local consent headers: {e}"))?;
    let rows = value.as_array().ok_or("local consent headers are not a list")?;
    rows.iter().map(|row| crate::hex::decode_any_case(row.as_str().ok_or("local consent header is not hex")?)).collect()
}

/// `StreamCodec.nat`: base-255 little-endian digits, then the terminator 255.
fn stream_nat(mut value: usize) -> Vec<u8> {
    let mut out = Vec::new();
    while value > 0 {
        out.push((value % 255) as u8);
        value /= 255;
    }
    out.push(255);
    out
}
/// `StreamCodec.list bytesStream`.
fn stream_byte_list(items: &[Vec<u8>]) -> Vec<u8> {
    let mut out = stream_nat(items.len());
    for item in items {
        out.extend(stream_nat(item.len()));
        out.extend_from_slice(item);
    }
    out
}

type ConsentResult<T> = std::result::Result<T, ConsentError>;

/// A session with a consent provider (in this process, or a resident one), and the typed frames.
/// Every frame is followed by retaining the anchor of what the provider admitted.
pub struct Consent(pub Session);

impl Consent {
    /// One frame, judged; then the anchor is retained.
    pub fn call(&mut self, operation: u8, payload: &[u8]) -> ConsentResult<Vec<u8>> {
        let answer = round_trip(&mut self.0, operation, payload);
        retain_anchor(&mut self.0);
        answer
    }

    /// Complete independent full-history verification in this same retained session.
    /// An anchor alone is insufficient. Only an exact empty response is readiness.
    pub fn full_ready(&mut self) -> ConsentResult<()> {
        let answer = self.call(crate::host_operations::CONSENT_FULL_READY, &[])?;
        if !answer.is_empty() { return Err("full consent readiness returned payload".into()); }
        Ok(())
    }

    /// Op 220 (thin: 230): key is current at the verified frontier.
    /// The provider must return the retained intent unchanged.
    pub fn intent(&mut self, intent_bin: &[u8], key: &[u8], thin: bool) -> ConsentResult<()> {
        let checked = self.call(if thin { crate::host_operations::CONSENT_THIN_INTENT } else { crate::host_operations::CONSENT_INTENT }, &pair(intent_bin, &pair(key, &[])?)?)?;
        if checked != intent_bin {
            return Err("local consent returned a different retained intent".into());
        }
        Ok(())
    }

    /// Op 221 (thin: 231): the headers of the operator's challenge this intent permits `key` to sign.
    pub fn observation(&mut self, intent_bin: &[u8], key: &[u8], intent_signature: &[u8], challenge: &[u8], thin: bool)
        -> ConsentResult<Vec<Vec<u8>>> {
        let payload = pair(intent_bin, &pair(key, &pair(intent_signature, challenge)?)?)?;
        Ok(headers(&self.call(if thin { crate::host_operations::CONSENT_THIN_OBSERVATION } else { crate::host_operations::CONSENT_OBSERVATION }, &payload)?)?)
    }

    /// Op 222: the headers of the operator's plan this intent permits `key` to sign.
    pub fn plan(&mut self, intent_bin: &[u8], key: &[u8], plan: &[u8]) -> ConsentResult<Vec<Vec<u8>>> {
        Ok(headers(&self.call(crate::host_operations::CONSENT_PLAN, &pair(intent_bin, &pair(key, plan)?)?)?)?)
    }

    /// Op 232, thin consent: checked against the provider's own command and the target `views`
    /// the Host served under the member's observe grants (`Kernel.NativeThinConsent`), reading no
    /// Store. Returns what the provider displays and the headers. A turn it cannot display is
    /// refused with the unsigned input named.
    pub fn thin_plan(&mut self, intent_bin: &[u8], key: &[u8], plan: &[u8], views: &[Vec<u8>]) -> ConsentResult<(Value, Vec<Vec<u8>>)> {
        let payload = pair(intent_bin, &pair(key, &pair(plan, &stream_byte_list(views))?)?)?;
        thin_reply(&self.call(crate::host_operations::CONSENT_THIN_PLAN, &payload)?)
    }

    /// Op 234, thin birth intent consent: the retained birth intent must be the deployed authoring
    /// of the member's own `source` (its retained `source.json` bytes) at the coordinates the
    /// draft carries (`Kernel.NativeThinBirth.checkBirthIntentThin`). The provider returns the
    /// retained intent unchanged.
    pub fn thin_birth_intent(&mut self, intent_bin: &[u8], key: &[u8], source: &[u8]) -> ConsentResult<()> {
        let checked = self.call(crate::host_operations::CONSENT_THIN_BIRTH_INTENT, &pair(intent_bin, &pair(key, source)?)?)?;
        if checked != intent_bin {
            return Err("local consent returned a different retained intent".into());
        }
        Ok(())
    }

    /// Op 235, thin birth plan consent (`Kernel.NativeThinBirth.checkBirthThin`): the authoring
    /// check again, the plan's finalized descriptor against the authored draft, and every header
    /// against the member's derivation of its branch. Returns the display and the headers.
    pub fn thin_birth_plan(&mut self, intent_bin: &[u8], key: &[u8], plan: &[u8], source: &[u8]) -> ConsentResult<(Value, Vec<Vec<u8>>)> {
        let payload = pair(intent_bin, &pair(key, &pair(plan, source)?)?)?;
        thin_reply(&self.call(crate::host_operations::CONSENT_THIN_BIRTH_PLAN, &payload)?)
    }

    /// Op 224: the operator's reply to a specialized plan request (one of the registry's
    /// `consent_plans`) equals the plan the Lean planner reconstructs. A refusal never falls back
    /// to the offered plan.
    pub fn operator_plan(&mut self, operation: u8, request: &[u8], candidate: &[u8]) -> ConsentResult<()> {
        if !CONSENT_PLANS.contains(&operation) {
            return Err(ConsentError::Failed(Error(format!("operation {operation} is not a checked operator plan"))));
        }
        let retained = [vec![operation], request.to_vec()].concat();
        let expected = self.call(crate::host_operations::CONSENT_OPERATOR_PLAN, &pair(&retained, candidate)?)?;
        if expected != candidate {
            return Err("local native specialized consent returned a different plan".into());
        }
        Ok(())
    }

    /// Op 226: enrollment possession, a source-independent domain frame over the complete retained
    /// command with the selected new custody key and subject.
    pub fn possession(&mut self, command: &[u8], subject: &str, public_key: &[u8], candidate: &[u8]) -> ConsentResult<Vec<u8>> {
        if !crate::decimal::is_canonical(subject) {
            return Err("possession subject must be canonical decimal".into());
        }
        let selected = serde_json::to_vec(&json!({"subject": subject, "publicKey": crate::hex::encode(public_key)}))
            .map_err(|e| Error(e.to_string()))?;
        let checked = self.call(crate::host_operations::CONSENT_POSSESSION, &pair(command, &pair(&selected, candidate)?)?)?;
        if checked != candidate {
            return Err("native possession frame changed".into());
        }
        Ok(checked)
    }

    /// Op 227, Objective: the provider reconstructs the complete expected typed plan from the
    /// independently retained intent and verified source, binds the selected key to `role`, and
    /// returns its own ordered headers after whole-plan equality. An older provider refuses; a
    /// caller never falls back to the offered plan's inspected headers.
    pub fn objective(&mut self, intent_bin: &[u8], public_key: &[u8], role: &str, plan: &[u8]) -> ConsentResult<Vec<Vec<u8>>> {
        if public_key.len() != 32 || role.is_empty() || role.len() > 128 {
            return Err("invalid local Objective custody selection".into());
        }
        let selection = serde_json::to_vec(&json!({"publicKey": crate::hex::encode(public_key), "role": role}))
            .map_err(|e| Error(e.to_string()))?;
        Ok(headers(&self.call(crate::host_operations::CONSENT_OBJECTIVE, &pair(intent_bin, &pair(&selection, plan)?)?)?)?)
    }
}

/// The box's shared codec Host's greeting: this tag, the SHA-256 of the Host image it runs, and
/// the SHA-256 of the settings bytes it runs under. A client compares it with its own pins before
/// it sends a frame ([`connect_codec_service`]).
pub const CODEC_SERVICE_TAG: &[u8] = b"MINI-CODEC-SERVICE/v1\0";

/// The greeting of a codec service running `image_sha256` under `settings_bytes`.
pub fn codec_service_hello(image_sha256: &[u8; 32], settings_bytes: &[u8]) -> Vec<u8> {
    use sha2::Digest;
    [CODEC_SERVICE_TAG, image_sha256.as_slice(), sha2::Sha256::digest(settings_bytes).as_slice()].concat()
}

/// **The box's shared codec Host** (split tenancy: every member is its own account, so a member's
/// resident codec Host was one ~85 MB Lean image per member). ONE storeless `HOST SETTINGS codec`
/// child serves every connection on `listener`, one frame at a time, exactly as a member's resident
/// codec does (the codec is a pure function of the frame and holds no state, so sharing it changes
/// no reply; `Host.Main.pureCodec`). Each connection first receives [`codec_service_hello`] for the
/// image and settings, so a client that pinned another image or other settings refuses before it
/// sends a frame. Any peer uid is served: the listener's own permissions (its directory's group) say
/// who may connect. Runs until the child ends.
pub fn serve_codec_service(listener: std::os::unix::net::UnixListener, executable: PathBuf, settings: PathBuf,
    image_sha256: [u8; 32]) -> Result<()> {
    use std::sync::{atomic::AtomicBool, Arc};
    let settings_bytes = settings_bytes(&settings)?;
    let hello = codec_service_hello(&image_sha256, &settings_bytes);
    let session = Session::spawn(executable, &settings, settings_bytes, "codec", "shared codec Host")?;
    let shared = Arc::new(Mutex::new(Resident { session, ended: false }));
    let last = Arc::new(Mutex::new(std::time::Instant::now()));
    let ended = Arc::new(AtomicBool::new(false));
    listener.set_nonblocking(false).map_err(|e| e.to_string())?;
    for stream in listener.incoming() {
        if ended.load(std::sync::atomic::Ordering::Acquire) {
            return Err("the shared codec Host ended".into());
        }
        let Ok(mut stream) = stream else { continue };
        let (shared, last, ended, hello) = (shared.clone(), last.clone(), ended.clone(), hello.clone());
        std::thread::spawn(move || {
            if stream.write_all(&hello).is_ok() {
                serve_connection_from(ResidentKind::Codec, stream, &shared, &last, &ended, true);
            }
        });
    }
    Ok(())
}

/// A session with the box's shared codec Host at `socket`: the listener must be `peer_uid`'s (the
/// operator's, or 0 for a systemd-activated one) and must greet with exactly `expected`
/// ([`codec_service_hello`] of this client's own pins), or nothing is sent.
pub fn connect_codec_service(socket: &Path, peer_uid: u32, expected: &[u8], executable: PathBuf,
    settings_bytes: Vec<u8>) -> Result<Session> {
    let mut stream = std::os::unix::net::UnixStream::connect(socket)
        .map_err(|e| format!("shared codec Host {}: {e}", socket.display()))?;
    if crate::private::peer_uid(&stream).map_err(|e| e.to_string())? != peer_uid {
        return Err("shared codec Host listener is not the selected peer".into());
    }
    stream.set_read_timeout(Some(std::time::Duration::from_secs(30))).map_err(|e| e.to_string())?;
    let mut greeting = vec![0u8; expected.len()];
    stream.read_exact(&mut greeting).map_err(|e| format!("shared codec Host greeting: {e}"))?;
    if greeting != expected {
        return Err("shared codec Host runs another image or other settings than this client pinned".into());
    }
    stream.set_read_timeout(None).map_err(|e| e.to_string())?;
    let input = stream.try_clone().map_err(|e| e.to_string())?;
    Ok(Session::over(Box::new(input), Box::new(stream), executable, settings_bytes))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    /// A resident started while its caller holds an fd (a `flock` wrapper's lock, a journey's pipe)
    /// must not inherit it, or the resident keeps the caller's lock for as long as it lives.
    #[cfg(target_os = "linux")]
    #[test]
    fn a_detached_resident_inherits_no_fd_from_its_caller() {
        use std::os::unix::io::AsRawFd;
        let dir = stub_dir("detach");
        let held = fs::File::create(dir.join("held.lock")).unwrap();
        let fd = held.as_raw_fd();
        // an fd inherited across exec, as a `flock` wrapper's is
        unsafe { libc::fcntl(fd, libc::F_SETFD, 0) };
        assert_eq!(unsafe { libc::flock(fd, libc::LOCK_EX | libc::LOCK_NB) }, 0);
        let listing = dir.join("fds");
        let mut command = Command::new("/bin/sh");
        command.arg("-c").arg(format!("ls -1 /proc/$$/fd > {}", listing.display()));
        detach(&mut command);
        assert!(command.status().unwrap().success());
        let seen = fs::read_to_string(&listing).unwrap();
        let open: Vec<&str> = seen.lines().collect();
        // (the shell keeps a private fd of its own, 10; the caller's must be absent)
        assert!(!open.contains(&fd.to_string().as_str()), "the resident inherited the caller's fd: {open:?} (caller held {fd})");
    }

    fn stub_dir(label: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("mini-sdk-consent-{label}-{}-{}", std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir(&dir).unwrap();
        dir
    }

    fn framed(body: &[u8]) -> Vec<u8> {
        [(body.len() as u32).to_le_bytes().as_slice(), body].concat()
    }

    #[test]
    fn full_readiness_requires_its_exact_empty_acknowledgement() {
        for (reply, ready) in [(vec![236], true), (vec![236, 1], false),
            (vec![255], false), (vec![233], false)] {
            let session = Session::over(Box::new(Vec::<u8>::new()),
                Box::new(std::io::Cursor::new(framed(&reply))), "/stub".into(), vec![]);
            assert_eq!(Consent(session).full_ready().is_ok(), ready);
        }
    }

    /// A provider stub answering one frame with `answer` and `detail`, after reading 13 bytes.
    fn answering(answer: u8, detail: &str) -> Session {
        let mut body = vec![answer];
        body.extend_from_slice(detail.as_bytes());
        let mut frame = (body.len() as u32).to_le_bytes().to_vec();
        frame.extend_from_slice(&body);
        let script = format!("dd bs=1 count=13 >/dev/null 2>&1; printf '{}'", frame.iter().map(|b| format!("\\{b:03o}")).collect::<String>());
        let mut child = Command::new("/bin/sh").args(["-c", &script]).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
        let input = child.stdin.take().unwrap();
        let output = child.stdout.take().unwrap();
        let mut s = Session::over(Box::new(input), Box::new(output), "/bin/sh".into(), vec![]);
        s.child = Some(child);
        s
    }

    /// A provider stub that logs each request's opcode and answers it with that opcode and an
    /// empty body, or with the anchor bytes for frame 229.
    fn opcode_stub(dir: &Path, anchor: &[u8]) -> PathBuf {
        fs::write(dir.join("anchor-body"), anchor).unwrap();
        let path = dir.join("provider");
        fs::write(&path, format!(concat!(
            "#!/bin/sh\n",
            "while :; do\n",
            "  n=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 | tr -d ' \\n')\n",
            "  [ -n \"$n\" ] || exit 0\n",
            "  dd bs=1 count=\"$n\" of='{frame}' 2>/dev/null\n",
            "  op=$(od -An -tu1 -N1 '{frame}' | tr -d ' \\n')\n",
            "  echo \"$op\" >> '{log}'\n",
            "  if [ \"$op\" = 229 ]; then\n",
            "    m=$(( $(wc -c < '{body}') + 1 ))\n",
            "    printf \"$(printf '\\\\%03o\\\\000\\\\000\\\\000\\\\%03o' \"$m\" 229)\"; cat '{body}'\n",
            "  else\n",
            "    printf \"$(printf '\\\\001\\\\000\\\\000\\\\000\\\\%03o' \"$op\")\"\n",
            "  fi\n",
            "done\n"), log = dir.join("opcodes").display(), body = dir.join("anchor-body").display(),
            frame = dir.join("frame").display())).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        path
    }
    fn opcodes(dir: &Path) -> Vec<u8> {
        fs::read_to_string(dir.join("opcodes")).unwrap_or_default().lines().map(|line| line.trim().parse().unwrap()).collect()
    }

    #[test]
    fn thin_view_list_is_the_lean_byte_list_codec() {
        assert_eq!(stream_nat(0), vec![255]);
        assert_eq!(stream_nat(254), vec![254, 255]);
        assert_eq!(stream_nat(255), vec![0, 1, 255]);
        assert_eq!(stream_byte_list(&[]), vec![255]);
        assert_eq!(stream_byte_list(&[vec![7, 8], vec![]]), vec![2, 255, 2, 255, 7, 8, 255]);
    }

    #[test]
    fn consent_headers_preserve_duplicates_order_and_reject_unframed_values() {
        assert_eq!(headers(br#"["aabb","ff","aabb"]"#).unwrap(), vec![vec![170, 187], vec![255], vec![170, 187]]);
        for bad in [br#"{"headers":["aabb"]}"#.as_slice(), br#"[true]"#, br#"["zz"]"#] {
            assert!(headers(bad).is_err());
        }
    }

    #[test]
    fn a_refusal_never_returns_header_bytes_and_only_a_stale_observation_is_stale() {
        let error = round_trip(&mut answering(255, "changed-plan"), crate::host_operations::CONSENT_PLAN, b"retained").unwrap_err();
        assert_eq!(error.to_string(), "local consent refused before signing: changed-plan");
        assert!(!error.is_stale_observation());
        let stale = "stale observation: the remote challenge answers this intent at source height 36";
        assert!(round_trip(&mut answering(255, stale), crate::host_operations::CONSENT_OBSERVATION, b"retained").unwrap_err().is_stale_observation());
        // The tag counts only on an observation frame, and only as a refusal.
        assert!(!round_trip(&mut answering(255, stale), crate::host_operations::CONSENT_PLAN, b"retained").unwrap_err().is_stale_observation());
        assert!(!round_trip(&mut answering(254, stale), crate::host_operations::CONSENT_OBSERVATION, b"retained").unwrap_err().is_stale_observation());
    }

    #[test]
    fn a_consent_that_echoes_other_intent_bytes_refuses() {
        // Answers op 220 with the 3 bytes "abd" whatever was asked (4 + 1 + 4 + 3 + 4 + 32 bytes).
        let mut body = vec![220u8];
        body.extend_from_slice(b"abd");
        let frame = [(body.len() as u32).to_le_bytes().as_slice(), &body].concat();
        let script = format!("dd bs=1 count=48 >/dev/null 2>&1; printf '{}'", frame.iter().map(|b| format!("\\{b:03o}")).collect::<String>());
        let mut child = Command::new("/bin/sh").args(["-c", &script]).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
        let (input, output) = (child.stdin.take().unwrap(), child.stdout.take().unwrap());
        let mut session = Session::over(Box::new(input), Box::new(output), "/bin/sh".into(), vec![]);
        session.child = Some(child);
        let error = Consent(session).intent(b"abc", &[1u8; 32], false).unwrap_err();
        assert!(error.to_string().contains("different retained intent"), "{error}");
    }

    #[test]
    fn unchecked_operator_opcodes_refuse_before_any_frame() {
        let mut consent = Consent(answering(224, ""));
        assert!(consent.operator_plan(crate::host_operations::AUTHORIZED_PREPARE, b"", b"").is_err());
        // The list is generated from protocol/host-operations.json; pin membership, not a count.
        assert!(CONSENT_PLANS.contains(&210) && CONSENT_PLANS.contains(&215));
        assert!(CONSENT_PLANS.contains(&187) && CONSENT_PLANS.contains(&194));
    }

    #[test]
    fn retained_anchor_survives_a_ship_but_not_a_settings_change() {
        let dir = stub_dir("anchor-offer");
        let provider = opcode_stub(&dir, b"ANCHOR-AFTER");
        let settings = dir.join("consent.json");
        fs::write(&settings, b"{}").unwrap();
        // No retained anchor: admission from genesis (no 228), then the anchor is retained.
        let mut session = start(&dir.join("anchors"), provider.clone(), &settings, b"{}".to_vec()).unwrap();
        round_trip(&mut session, crate::host_operations::CONSENT_INTENT, b"intent").unwrap();
        retain_anchor(&mut session);
        drop(session);
        assert_eq!(opcodes(&dir), vec![220, 229]);
        let binding = anchor_binding(b"{}").unwrap();
        assert_eq!(read_anchor(&anchor_path(&dir.join("anchors"), &binding), &binding).unwrap().as_deref(), Some(&b"ANCHOR-AFTER"[..]));
        // The next provider is offered it first.
        fs::remove_file(dir.join("opcodes")).unwrap();
        let mut session = start(&dir.join("anchors"), provider.clone(), &settings, b"{}".to_vec()).unwrap();
        round_trip(&mut session, crate::host_operations::CONSENT_INTENT, b"intent").unwrap();
        drop(session);
        assert_eq!(opcodes(&dir), vec![228, 220]);
        // A replaced provider file (a ship) and moved executable settings keep the binding: offered.
        let resident = crate::local::binding(&provider, b"{}").unwrap();
        let copy = dir.join("provider-copy");
        fs::copy(&provider, &copy).unwrap();
        fs::rename(&copy, &provider).unwrap();
        assert_ne!(crate::local::binding(&provider, b"{}").unwrap(), resident, "a resident is not reused across a ship");
        assert_eq!(anchor_binding(br#"{"storageBinary":"/c1/store","domain":1}"#).unwrap(),
            anchor_binding(br#"{ "domain" : 1, "storageBinary" : "/c2/store" }"#).unwrap());
        fs::remove_file(dir.join("opcodes")).unwrap();
        let mut session = start(&dir.join("anchors"), provider.clone(), &settings, b"{ }".to_vec()).unwrap();
        round_trip(&mut session, crate::host_operations::CONSENT_INTENT, b"intent").unwrap();
        drop(session);
        assert_eq!(opcodes(&dir), vec![228, 220]);
        // Changed settings: another binding, so no offer.
        fs::remove_file(dir.join("opcodes")).unwrap();
        let mut session = start(&dir.join("anchors"), provider.clone(), &settings, br#"{"domain":2}"#.to_vec()).unwrap();
        round_trip(&mut session, crate::host_operations::CONSENT_INTENT, b"intent").unwrap();
        drop(session);
        assert_eq!(opcodes(&dir), vec![220]);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn a_resident_whose_socket_is_unlinked_sees_it_is_unreachable() {
        use std::os::unix::fs::MetadataExt;
        // A short directory: the macOS temp dir is longer than a socket address allows.
        let dir = PathBuf::from(format!("/tmp/mcs-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir(&dir).unwrap();
        let path = dir.join("r.sock");
        let listener = std::os::unix::net::UnixListener::bind(&path).unwrap();
        let meta = fs::symlink_metadata(&path).unwrap();
        let identity = (meta.dev(), meta.ino());
        assert!(socket_is(&path, identity));
        fs::remove_file(&path).unwrap();
        assert!(!socket_is(&path, identity), "unlinked (its world torn down)");
        drop(listener);
        let again = std::os::unix::net::UnixListener::bind(&path).unwrap();
        assert!(!socket_is(&path, identity), "another node at the same path is not this resident's");
        drop(again);
        let _ = fs::remove_dir_all(&dir);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn resident_socket_namespaces_are_short_private_and_anchor_specific() {
        use std::os::unix::fs::symlink;
        let dir = stub_dir("long-ipc");
        let first = dir.join("a".repeat(180));
        let second = dir.join("b".repeat(180));
        for path in [&first, &second] {
            fs::create_dir(path).unwrap();
            fs::set_permissions(path, fs::Permissions::from_mode(0o700)).unwrap();
        }
        let binding = [7u8; 32];
        let (socket, _held) = resident_socket(ResidentKind::Codec, &first, &binding).unwrap();
        let (other, _other_held) = resident_socket(ResidentKind::Codec, &second, &binding).unwrap();
        assert!(socket.as_os_str().len() < 100);
        let listener = std::os::unix::net::UnixListener::bind(&socket).unwrap();
        assert!(resident_file(ResidentKind::Codec, &first, &binding, "sock").exists());
        assert!(!resident_file(ResidentKind::Codec, &second, &binding, "sock").exists());
        assert_ne!(socket, other);
        drop(listener); fs::remove_file(&socket).unwrap();
        fs::set_permissions(&first, fs::Permissions::from_mode(0o755)).unwrap();
        assert!(resident_socket(ResidentKind::Codec, &first, &binding).is_err());
        fs::remove_dir(&first).unwrap();
        symlink(&second, &first).unwrap();
        assert!(resident_socket(ResidentKind::Codec, &first, &binding).is_err());
        fs::remove_file(&first).unwrap();
        let _ = fs::remove_dir_all(&dir);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn resident_socket_cross_private_tmp_reaches_the_same_anchor_node() {
        if let Some(anchors) = std::env::var_os("MINI_IPC_PRIVATE_TMP_TEST") {
            let (socket, _held) = resident_socket(ResidentKind::Codec, Path::new(&anchors), &[9; 32]).unwrap();
            let mut stream = resident_stream(&socket).unwrap();
            stream.write_all(b"same-anchor").unwrap();
            return;
        }
        let available = Command::new("unshare").args(["-Ur", "-m", "true"]).status();
        if !available.is_ok_and(|status| status.success()) {
            eprintln!("cross-PrivateTmp control unavailable: user mount namespaces refused");
            return;
        }
        // Outside /tmp: the child deliberately replaces its entire /tmp mount.
        let dir = std::env::current_dir().unwrap().join(format!(".ipc-private-tmp-{}", std::process::id()));
        fs::create_dir(&dir).unwrap();
        let anchors = dir.join("anchors-".to_owned() + &"long".repeat(40));
        fs::create_dir(&anchors).unwrap();
        fs::set_permissions(&anchors, fs::Permissions::from_mode(0o700)).unwrap();
        let (socket, _held) = resident_socket(ResidentKind::Codec, &anchors, &[9; 32]).unwrap();
        let listener = std::os::unix::net::UnixListener::bind(&socket).unwrap();
        let output = Command::new("unshare").args(["-Ur", "-m", "sh", "-c",
            "mount --make-rprivate / && mount -t tmpfs tmpfs /tmp && exec \"$@\"", "ipc-control"])
            .arg(std::env::current_exe().unwrap())
            .args(["--exact", "consent::tests::resident_socket_cross_private_tmp_reaches_the_same_anchor_node", "--nocapture"])
            .env("MINI_IPC_PRIVATE_TMP_TEST", &anchors).output().unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        let (mut stream, _) = listener.accept().unwrap();
        let mut bytes = [0; 11]; stream.read_exact(&mut bytes).unwrap();
        assert_eq!(&bytes, b"same-anchor");
        drop(listener); fs::remove_file(&socket).unwrap();
        fs::remove_dir_all(&dir).unwrap();
    }

    /// One provider for every connection of its binding; each connection's first frame is
    /// preceded by the Store re-check (233); the anchor is retained (229) after every frame;
    /// 228/229/233 from a client never reach the provider; an idle provider ends and removes its
    /// socket and PID file.
    #[test]
    fn resident_provider_rechecks_each_connection_and_serves_all_of_them() {
        // The persistent anchor path deliberately exceeds Unix socket address limits.
        let dir = PathBuf::from(format!("/tmp/msr-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir(&dir).unwrap();
        let provider = opcode_stub(&dir, b"ANCHOR-R");
        let settings = dir.join("consent.json");
        fs::write(&settings, b"{}").unwrap();
        let anchors = dir.join("anchors-".to_owned() + &"long".repeat(40));
        fs::create_dir(&anchors).unwrap();
        fs::set_permissions(&anchors, fs::Permissions::from_mode(0o700)).unwrap();
        let binding = binding(&provider, b"{}").unwrap();
        let (socket, _socket_directory) = resident_socket(ResidentKind::Consent, &anchors, &binding).unwrap();
        assert!(socket.as_os_str().len() < 100);
        let (a, p, s) = (anchors.clone(), provider.clone(), settings.clone());
        let daemon = std::thread::spawn(move || serve_resident(&a, p, s, Some(std::time::Duration::from_millis(400))));
        let connect = || {
            for _ in 0..2000 {
                if let Ok(stream) = resident_stream(&socket) {
                    let input = stream.try_clone().unwrap();
                    return Session::over(Box::new(input), Box::new(stream), provider.clone(), b"{}".to_vec());
                }
                std::thread::sleep(std::time::Duration::from_millis(5));
            }
            panic!("resident provider never listened");
        };
        let mut first = connect();
        assert_eq!(round_trip(&mut first, crate::host_operations::CONSENT_INTENT, b"intent").unwrap(), Vec::<u8>::new());
        assert_eq!(round_trip(&mut first, crate::host_operations::CONSENT_OBSERVATION, b"observe").unwrap(), Vec::<u8>::new());
        let mut second = connect();
        assert_eq!(round_trip(&mut second, crate::host_operations::CONSENT_PLAN, b"plan").unwrap(), Vec::<u8>::new());
        for reserved in [228u8, 229, 233] {
            let error = round_trip(&mut second, reserved, b"x").unwrap_err().to_string();
            assert!(error.contains("reserved to the resident consent provider"), "{error}");
        }
        assert_eq!(opcodes(&dir), vec![233, 220, 229, 221, 229, 233, 222, 229]);
        let anchored = anchor_binding(b"{}").unwrap();
        assert_eq!(read_anchor(&anchor_path(&anchors, &anchored), &anchored).unwrap().as_deref(), Some(&b"ANCHOR-R"[..]));
        assert!(resident_file(ResidentKind::Consent, &anchors, &binding, "pid").exists());
        drop(first);
        drop(second);
        daemon.join().unwrap().unwrap();
        assert!(!socket.exists() && !resident_file(ResidentKind::Consent, &anchors, &binding, "pid").exists());
        let _ = fs::remove_dir_all(&dir);
    }

    /// One resident codec Host serves every connection (every `mini` process) of its binding with
    /// ONE child, re-checks nothing, retains nothing, answers each frame with the child's own reply,
    /// and ends when idle, taking its socket and PID file with it.
    #[test]
    fn resident_codec_host_serves_every_connection_with_one_child() {
        // The persistent anchor path deliberately exceeds Unix socket address limits.
        let dir = PathBuf::from(format!("/tmp/mcc-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir(&dir).unwrap();
        let host = crate::local::fake::codec_stub(&dir);
        // The stub answers frame i from reply-i: each reply echoes the operation it answers.
        fs::write(dir.join("reply-1"), framed(b"\x07ok")).unwrap();
        fs::write(dir.join("reply-2"), framed(b"\x08ok")).unwrap();
        fs::write(dir.join("reply-3"), framed(b"\x0bok")).unwrap();
        fs::write(dir.join("reply"), framed(b"\xff unexpected fourth frame")).unwrap();
        let settings = dir.join("settings.json");
        fs::write(&settings, b"{}").unwrap();
        let anchors = dir.join("anchors-".to_owned() + &"long".repeat(40));
        fs::create_dir(&anchors).unwrap();
        fs::set_permissions(&anchors, fs::Permissions::from_mode(0o700)).unwrap();
        let binding = binding(&host, b"{}").unwrap();
        let (socket, _socket_directory) = resident_socket(ResidentKind::Codec, &anchors, &binding).unwrap();
        assert!(socket.as_os_str().len() < 100);
        assert_ne!(socket, resident_file(ResidentKind::Consent, &anchors, &binding, "sock"), "the codec socket is not the consent socket");
        let (a, h, s) = (anchors.clone(), host.clone(), settings.clone());
        let daemon = std::thread::spawn(move || serve_resident_kind(ResidentKind::Codec, &a, h, s, Some(std::time::Duration::from_millis(400))));
        let connect = || {
            for _ in 0..2000 {
                if let Ok(stream) = resident_stream(&socket) {
                    let input = stream.try_clone().unwrap();
                    return Session::over(Box::new(input), Box::new(stream), host.clone(), b"{}".to_vec());
                }
                std::thread::sleep(std::time::Duration::from_millis(5));
            }
            panic!("resident codec Host never listened");
        };
        let mut first = connect();
        assert_eq!(round_trip(&mut first, crate::host_operations::AUTHOR, b"intent").unwrap(), b"ok");
        let mut second = connect();
        assert_eq!(round_trip(&mut second, crate::host_operations::INSPECT, b"outcome").unwrap(), b"ok");
        assert_eq!(round_trip(&mut first, crate::host_operations::CALL_ASSEMBLE, b"assemble").unwrap(), b"ok");
        assert_eq!(fs::read_to_string(dir.join("starts")).unwrap().lines().count(), 1, "one child for all connections");
        let anchored = anchor_binding(b"{}").unwrap();
        assert!(read_anchor(&anchor_path(&anchors, &anchored), &anchored).unwrap().is_none(), "the codec Host retains no anchor");
        assert!(resident_file(ResidentKind::Codec, &anchors, &binding, "pid").exists());
        drop(first);
        drop(second);
        daemon.join().unwrap().unwrap();
        assert!(!socket.exists() && !resident_file(ResidentKind::Codec, &anchors, &binding, "pid").exists());
        let _ = fs::remove_dir_all(&dir);
    }

    /// A resident without an idle exit keeps serving while its binding is current and ends once
    /// its settings bytes change (a ship or a re-pinned config supersedes the binding).
    #[test]
    fn a_resident_without_idle_exit_ends_when_its_binding_is_superseded() {
        let dir = PathBuf::from(format!("/tmp/mcu-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir(&dir).unwrap();
        let host = crate::local::fake::codec_stub(&dir);
        fs::write(dir.join("reply-1"), framed(b"\x07ok")).unwrap();
        fs::write(dir.join("reply"), framed(b"\xff unexpected frame")).unwrap();
        let settings = dir.join("settings.json");
        fs::write(&settings, b"{}").unwrap();
        let anchors = dir.join("anchors");
        fs::create_dir(&anchors).unwrap();
        fs::set_permissions(&anchors, fs::Permissions::from_mode(0o700)).unwrap();
        let binding = binding(&host, b"{}").unwrap();
        let (socket, _socket_directory) = resident_socket(ResidentKind::Codec, &anchors, &binding).unwrap();
        let (a, h, s) = (anchors.clone(), host.clone(), settings.clone());
        let daemon = std::thread::spawn(move || serve_resident_kind(ResidentKind::Codec, &a, h, s, None));
        let mut session = (|| {
            for _ in 0..2000 {
                if let Ok(stream) = resident_stream(&socket) {
                    let input = stream.try_clone().unwrap();
                    return Session::over(Box::new(input), Box::new(stream), host.clone(), b"{}".to_vec());
                }
                std::thread::sleep(std::time::Duration::from_millis(5));
            }
            panic!("resident never listened");
        })();
        assert_eq!(round_trip(&mut session, crate::host_operations::AUTHOR, b"intent").unwrap(), b"ok");
        drop(session);
        std::thread::sleep(std::time::Duration::from_millis(1500));
        assert!(!daemon.is_finished(), "a current binding with no idle exit stays resident");
        fs::write(&settings, b"{\"moved\":1}").unwrap();
        for _ in 0..60 {
            if daemon.is_finished() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(100));
        }
        assert!(daemon.is_finished(), "a superseded binding ends its resident");
        daemon.join().unwrap().unwrap();
        assert!(!socket.exists());
        let _ = fs::remove_dir_all(&dir);
    }

    /// The box's shared codec Host serves any connection that accepts its greeting, with one child,
    /// and a client whose pins differ from the greeting refuses before it sends a frame.
    #[test]
    fn shared_codec_service_greets_with_its_pins_and_serves_every_connection() {
        let dir = PathBuf::from(format!("/tmp/mcx-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir(&dir).unwrap();
        let host = crate::local::fake::codec_stub(&dir);
        fs::write(dir.join("reply"), framed(b"\x07ok")).unwrap();
        let settings = dir.join("settings.json");
        fs::write(&settings, b"{}").unwrap();
        let socket = dir.join("codec.sock");
        let listener = std::os::unix::net::UnixListener::bind(&socket).unwrap();
        let image = [7u8; 32];
        let (h, s) = (host.clone(), settings.clone());
        std::thread::spawn(move || serve_codec_service(listener, h, s, image));
        let me = unsafe { libc::geteuid() };
        let expected = codec_service_hello(&image, b"{}");
        for _ in 0..2 {
            let mut session = connect_codec_service(&socket, me, &expected, host.clone(), b"{}".to_vec()).unwrap();
            assert_eq!(round_trip(&mut session, crate::host_operations::AUTHOR, b"intent").unwrap(), b"ok");
        }
        assert_eq!(fs::read_to_string(dir.join("starts")).unwrap().lines().count(), 1, "one child for every connection");
        let other = codec_service_hello(&[8u8; 32], b"{}");
        assert!(connect_codec_service(&socket, me, &other, host.clone(), b"{}".to_vec()).is_err(), "another image refuses");
        let settings_other = codec_service_hello(&image, b"{\"x\":1}");
        assert!(connect_codec_service(&socket, me, &settings_other, host.clone(), b"{}".to_vec()).is_err(), "other settings refuse");
        assert!(connect_codec_service(&socket, me + 1, &expected, host.clone(), b"{}".to_vec()).is_err(), "another listener owner refuses");
        let _ = fs::remove_dir_all(&dir);
    }

    /// A resident whose world is torn down ends, even when its directory, its executable and its
    /// settings file live outside that world: the Store its settings name is gone.
    #[test]
    fn a_resident_ends_when_the_store_its_settings_name_is_removed() {
        let dir = PathBuf::from(format!("/tmp/mcw-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir(&dir).unwrap();
        let host = crate::local::fake::codec_stub(&dir);
        fs::write(dir.join("reply"), framed(b"\xff unexpected frame")).unwrap();
        let world = dir.join("world");
        fs::create_dir_all(world.join("store")).unwrap();
        let settings_bytes = format!("{{\"storageRoot\":\"{}\"}}", world.join("store").display()).into_bytes();
        let settings = dir.join("settings.json");
        fs::write(&settings, &settings_bytes).unwrap();
        let anchors = dir.join("anchors");
        fs::create_dir(&anchors).unwrap();
        fs::set_permissions(&anchors, fs::Permissions::from_mode(0o700)).unwrap();
        let binding = binding(&host, &settings_bytes).unwrap();
        let (socket, _socket_directory) = resident_socket(ResidentKind::Codec, &anchors, &binding).unwrap();
        let (a, h, s) = (anchors.clone(), host.clone(), settings.clone());
        let daemon = std::thread::spawn(move || serve_resident_kind(ResidentKind::Codec, &a, h, s, None));
        for _ in 0..2000 {
            if socket.exists() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        std::thread::sleep(std::time::Duration::from_millis(1500));
        assert!(!daemon.is_finished(), "a resident of a live world stays");
        fs::remove_dir_all(&world).unwrap();
        for _ in 0..60 {
            if daemon.is_finished() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(100));
        }
        assert!(daemon.is_finished(), "a torn-down world ends its resident");
        daemon.join().unwrap().unwrap();
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn retained_anchor_file_refuses_foreign_or_exposed_bytes() {
        let dir = stub_dir("anchor-file");
        let path = dir.join("consent.json.consent-anchor");
        let binding = [7u8; 32];
        crate::durable::replace(&path, &anchor_file(&binding, b"A"), crate::durable::Perm::Private).unwrap();
        assert_eq!(read_anchor(&path, &binding).unwrap().as_deref(), Some(&b"A"[..]));
        assert_eq!(read_anchor(&path, &[8u8; 32]).unwrap(), None);
        fs::set_permissions(&path, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(read_anchor(&path, &binding).is_err());
        crate::durable::replace(&path, b"MINI-CONSENT-ANCHOR-CUSTODY/v0\nxxxx", crate::durable::Perm::Private).unwrap();
        assert!(read_anchor(&path, &binding).is_err());
        crate::durable::replace(&path, &anchor_file(&binding, b""), crate::durable::Perm::Private).unwrap();
        assert!(read_anchor(&path, &binding).is_err());
        let _ = fs::remove_dir_all(&dir);
    }

    /// A kill at every stage of retaining a new anchor leaves either the previous anchor
    /// or the new one, whole, under the same binding. Both are admissible offers.
    #[test]
    fn retained_anchor_survives_a_crash_at_every_stage() {
        use crate::durable::Stage;
        for stage in [Stage::MidWrite, Stage::BeforeCommit, Stage::AfterCommit] {
            let dir = stub_dir("anchor-crash");
            let provider = opcode_stub(&dir, b"NEW-ANCHOR");
            let settings = dir.join("consent.json");
            fs::write(&settings, b"{}").unwrap();
            let binding = anchor_binding(b"{}").unwrap();
            let path = anchor_path(&dir.join("anchors"), &binding);
            fs::create_dir(dir.join("anchors")).unwrap();
            crate::durable::replace(&path, &anchor_file(&binding, b"OLD-ANCHOR"), crate::durable::Perm::Private).unwrap();
            let mut session = start(&dir.join("anchors"), provider.clone(), &settings, b"{}".to_vec()).unwrap();
            round_trip(&mut session, crate::host_operations::CONSENT_INTENT, b"intent").unwrap();
            retain_anchor_with(&mut session, &mut |at| if at == stage { Err(io::Error::other("crash")) } else { Ok(()) });
            drop(session);
            let survived = read_anchor(&path, &binding).unwrap().unwrap();
            if matches!(stage, Stage::MidWrite | Stage::BeforeCommit) {
                assert_eq!(survived, b"OLD-ANCHOR", "{stage:?}");
            } else {
                assert_eq!(survived, b"NEW-ANCHOR", "{stage:?}");
            }
            let _ = fs::remove_dir_all(&dir);
        }
    }
}
