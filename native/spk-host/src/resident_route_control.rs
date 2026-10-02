//! Owner-private, generation-bound registration of immutable participant routes.
//! Transport authenticates the operator; only the fresh native admission passed
//! by the resident may add a listener. A retry acknowledges the original add and
//! cannot revive its sessions or replace an existing route's credentials.
use crate::dispatch_author::FixedAuthoring;
use crate::dispatch_native::{connect_deadline, private_dir, write_new};
use crate::http_entrance::{CustodianPolicy, EntranceKind};
use crate::stream_continuity::ContinuityBinding;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{FileTypeExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

pub(crate) const MAX_ROUTES: usize = 64;
const MAX_COMMAND: usize = 16 * 1024;
const PROTOCOL: &str = "mini-spk-route-register-v1";
pub const SOCKET_NAME: &str = "route-control.sock";

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}
fn decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}
fn digest(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RouteRegistration {
    pub protocol: String,
    pub registration_nonce_hex: String,
    pub expected_app: String,
    pub expected_app_generation: String,
    pub expected_session_generation: String,
    pub directory: PathBuf,
    pub dispatch_custody: PathBuf,
    pub dispatch_custody_sha256: String,
    pub custodian_sha256: String,
    pub display_name: String,
    pub preferred_handle: String,
}
impl RouteRegistration {
    fn validate(&self) -> io::Result<()> {
        if self.protocol != PROTOCOL
            || ![
                &self.registration_nonce_hex,
                &self.dispatch_custody_sha256,
                &self.custodian_sha256,
            ]
            .into_iter()
            .all(|s| digest(s))
            || ![
                &self.expected_app,
                &self.expected_app_generation,
                &self.expected_session_generation,
            ]
            .into_iter()
            .all(|s| decimal(s))
            || !clean_absolute(&self.directory)
            || !clean_absolute(&self.dispatch_custody)
            || self.display_name.is_empty()
            || self.display_name.len() > 256
            || self.preferred_handle.is_empty()
            || self.preferred_handle.len() > 256
            || self.display_name.chars().any(char::is_control)
            || self.preferred_handle.chars().any(char::is_control)
        {
            return Err(invalid("resident route registration shape refused"));
        }
        Ok(())
    }
}
fn clean_absolute(path: &Path) -> bool {
    path.is_absolute()
        && !path.components().any(|c| {
            matches!(
                c,
                std::path::Component::ParentDir | std::path::Component::CurDir
            )
        })
}

/// Captured from the exact files and presentation used by this resident, not
/// reconstructed from a later registration command or reopened mutable path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RouteIdentity {
    directory: PathBuf,
    dispatch_custody: PathBuf,
    dispatch_custody_sha256: String,
    custodian_sha256: String,
    display_name: String,
    preferred_handle: String,
}
impl RouteIdentity {
    pub(crate) fn capture(
        directory: &Path,
        dispatch_custody: &Path,
        display_name: &str,
        preferred_handle: &str,
        custody_bytes: &[u8],
        policy_bytes: &[u8],
    ) -> Self {
        Self {
            directory: directory.into(),
            dispatch_custody: dispatch_custody.into(),
            dispatch_custody_sha256: format!("{:x}", Sha256::digest(custody_bytes)),
            custodian_sha256: format!("{:x}", Sha256::digest(policy_bytes)),
            display_name: display_name.into(),
            preferred_handle: preferred_handle.into(),
        }
    }
    pub(crate) fn from_request(request: &RouteRegistration) -> Self {
        Self {
            directory: request.directory.clone(),
            dispatch_custody: request.dispatch_custody.clone(),
            dispatch_custody_sha256: request.dispatch_custody_sha256.clone(),
            custodian_sha256: request.custodian_sha256.clone(),
            display_name: request.display_name.clone(),
            preferred_handle: request.preferred_handle.clone(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RegistrationAction {
    Append(usize),
    Seal(usize),
}
impl RegistrationAction {
    pub(crate) fn index(self) -> usize {
        match self {
            Self::Append(index) | Self::Seal(index) => index,
        }
    }
}

/// Pure plan before source admission. Sealing does not consume another route
/// slot and cannot replace a loaded identity or an already fixed restriction.
pub(crate) fn registration_action(
    request: &RouteRegistration,
    identities: &[RouteIdentity],
    bindings: &[Option<ContinuityBinding>],
) -> io::Result<RegistrationAction> {
    request.validate()?;
    if identities.len() != bindings.len() {
        return Err(invalid("resident route registry length drift"));
    }
    if let Some(index) = identities
        .iter()
        .position(|identity| identity.directory == request.directory)
    {
        if bindings[index].is_some() {
            return Err(invalid("resident route already sealed"));
        }
        if identities[index] != RouteIdentity::from_request(request) {
            return Err(invalid(
                "existing route differs from retained immutable identity",
            ));
        }
        return Ok(RegistrationAction::Seal(index));
    }
    if identities.len() >= MAX_ROUTES {
        return Err(invalid("resident route limit reached"));
    }
    Ok(RegistrationAction::Append(identities.len()))
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct RouteRegistrationReply {
    pub protocol: String,
    pub registration_nonce_hex: String,
    pub route_index: usize,
    pub app: String,
    pub app_generation: String,
    pub session: String,
    pub session_generation: String,
    pub subject: String,
    pub ticket_resource: String,
    pub session_fingerprint_hex: String,
    pub admitted_height: String,
    pub admitted_world_root: String,
}

pub(crate) fn private_bytes(path: &Path) -> io::Result<Vec<u8>> {
    if !clean_absolute(path) {
        return Err(invalid("private route path refused"));
    }
    private_dir(
        path.parent()
            .ok_or_else(|| invalid("private route parent absent"))?,
    )?;
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file()
        || meta.nlink() != 1
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.permissions().mode() & 0o777 != 0o600
        || meta.len() == 0
        || meta.len() > MAX_COMMAND as u64
    {
        return Err(invalid("private route file identity refused"));
    }
    let mut bytes = Vec::new();
    file.take(MAX_COMMAND as u64 + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 != meta.len() {
        return Err(invalid("private route file size drift"));
    }
    Ok(bytes)
}

/// Read once and retain both identities. No later path read may replace either.
pub(crate) fn prepare(
    request: &RouteRegistration,
    app: &str,
    generation: &str,
) -> io::Result<(FixedAuthoring, CustodianPolicy)> {
    request.validate()?;
    if request.expected_app != app || request.expected_app_generation != generation {
        return Err(invalid("route targets another resident generation"));
    }
    private_dir(&request.directory)?;
    let custody_bytes = private_bytes(&request.dispatch_custody)?;
    let policy_bytes = private_bytes(&request.directory.join("custodian.json"))?;
    if format!("{:x}", Sha256::digest(&custody_bytes)) != request.dispatch_custody_sha256
        || format!("{:x}", Sha256::digest(&policy_bytes)) != request.custodian_sha256
    {
        return Err(invalid("immutable route file hash differs"));
    }
    let custody: FixedAuthoring = serde_json::from_slice(&custody_bytes)?;
    custody.validate()?;
    let policy = CustodianPolicy::from_bytes(&policy_bytes)?;
    policy.verify_tokens(&request.directory)?;
    if custody.app != app
        || custody.app != policy.fixed_app
        || custody.session != policy.fixed_session
        || custody.subject != policy.fixed_subject
        || custody.ticket_resource != policy.fixed_ticket
        || !matches!(
            (custody.session_kind.as_str(), policy.fixed_session_kind),
            ("web", EntranceKind::Browser) | ("api", EntranceKind::Api)
        )
    {
        return Err(invalid("route transport and fixed web custody differ"));
    }
    Ok((custody, policy))
}

fn peer_uid(stream: &UnixStream) -> io::Result<u32> {
    let mut credential = unsafe { std::mem::zeroed::<libc::ucred>() };
    let mut length = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
    if unsafe {
        libc::getsockopt(
            stream.as_raw_fd(),
            libc::SOL_SOCKET,
            libc::SO_PEERCRED,
            (&mut credential as *mut libc::ucred).cast(),
            &mut length,
        )
    } != 0
        || length as usize != std::mem::size_of::<libc::ucred>()
    {
        return Err(invalid("route control peer credentials absent"));
    }
    Ok(credential.uid)
}
fn read_until(stream: &mut UnixStream, mut bytes: &mut [u8], deadline: Instant) -> io::Result<()> {
    while !bytes.is_empty() {
        let remaining = deadline
            .checked_duration_since(Instant::now())
            .ok_or_else(|| {
                io::Error::new(io::ErrorKind::TimedOut, "route control read deadline")
            })?;
        stream.set_read_timeout(Some(remaining))?;
        match stream.read(bytes) {
            Ok(0) => {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "route control frame ended",
                ))
            }
            Ok(count) => bytes = &mut bytes[count..],
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }
    Ok(())
}
fn read_frame(stream: &mut UnixStream, deadline: Instant) -> io::Result<Vec<u8>> {
    let mut length = [0u8; 4];
    read_until(stream, &mut length, deadline)?;
    let length = u32::from_le_bytes(length) as usize;
    if length == 0 || length > MAX_COMMAND {
        return Err(invalid("route command frame bound refused"));
    }
    let mut bytes = vec![0; length];
    read_until(stream, &mut bytes, deadline)?;
    Ok(bytes)
}
fn write_frame(stream: &mut UnixStream, bytes: &[u8]) -> io::Result<()> {
    if bytes.is_empty() || bytes.len() > MAX_COMMAND {
        return Err(invalid("route reply frame bound refused"));
    }
    stream.write_all(&(bytes.len() as u32).to_le_bytes())?;
    stream.write_all(bytes)
}

#[derive(Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Envelope {
    result: Option<RouteRegistrationReply>,
    error: Option<String>,
}

const SEALS_DIRECTORY: &str = "route-seals";

/// A generation cannot silently lose a published or interrupted restriction.
/// Lifecycle STOP/new-generation recovery is required, never resealing as None.
pub(crate) fn refuse_retained_registrations(journal: &Path) -> io::Result<()> {
    let directory = journal.join(SEALS_DIRECTORY);
    match fs::symlink_metadata(&directory) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error),
        Ok(_) => {}
    }
    private_dir(&directory)?;
    if fs::read_dir(directory)?.next().transpose()?.is_some() {
        return Err(invalid(
            "retained route seal requires lifecycle STOP and a new generation",
        ));
    }
    Ok(())
}

pub(crate) struct RegistrationPublisher<'a> {
    directory: &'a Path,
    request: &'a RouteRegistration,
    started: bool,
    published: Option<RouteRegistrationReply>,
}
impl RegistrationPublisher<'_> {
    /// Call after all fallible preparation, before publishing any in-memory
    /// binding/listener. A publication failure is fatal to this resident.
    pub(crate) fn publish(
        &mut self,
        reply: &RouteRegistrationReply,
        binding: &ContinuityBinding,
        session_kind: &str,
    ) -> io::Result<()> {
        if self.started {
            return Err(invalid("route registration published twice"));
        }
        self.started = true;
        binding.validate()?;
        let fingerprint: String = binding
            .session_fingerprint
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        if reply.protocol != PROTOCOL
            || reply.registration_nonce_hex != self.request.registration_nonce_hex
            || reply.route_index >= MAX_ROUTES
            || binding.app != reply.app
            || binding.app_generation != reply.app_generation
            || binding.session != reply.session
            || binding.session_generation != reply.session_generation
            || binding.subject != reply.subject
            || binding.ticket_resource != reply.ticket_resource
            || fingerprint != reply.session_fingerprint_hex
            || self.request.expected_app != reply.app
            || self.request.expected_app_generation != reply.app_generation
            || self.request.expected_session_generation != reply.session_generation
            || !matches!(session_kind, "web" | "api")
        {
            return Err(invalid("route seal evidence differs from admitted binding"));
        }
        let bytes = serde_json::to_vec(&serde_json::json!({
            "protocol":"mini-spk-resident-route-seal-v1", "request":self.request, "reply":reply,
            "binding":{"domain":binding.domain,"semantics":binding.semantics,"app":binding.app,
                "appGeneration":binding.app_generation,"session":binding.session,
                "sessionGeneration":binding.session_generation,"subject":binding.subject,
                "ticketResource":binding.ticket_resource,"sessionFingerprintHex":fingerprint,"sessionKind":session_kind}
        }))?;
        if bytes.len() > MAX_COMMAND * 3 {
            return Err(invalid("route seal record too large"));
        }
        let pending_name = format!(".pending-{}.json", self.request.registration_nonce_hex);
        let pending = write_new(self.directory, &pending_name, &bytes)?;
        // A hard link publishes without replacing an earlier seal. During the
        // brief two-link interval, either filename makes reopen fail closed.
        let final_path = self
            .directory
            .join(format!("{}.json", self.request.registration_nonce_hex));
        fs::hard_link(&pending, &final_path)?;
        File::open(self.directory)?.sync_all()?;
        fs::remove_file(&pending)?;
        File::open(self.directory)?.sync_all()?;
        self.published = Some(reply.clone());
        Ok(())
    }
}

pub(crate) struct RouteControl {
    listener: UnixListener,
    socket: PathBuf,
    identity: (u64, u64),
    _lock: File,
    accepted: Vec<(RouteRegistration, RouteRegistrationReply)>,
    seals_directory: PathBuf,
    poisoned: bool,
}
impl RouteControl {
    pub(crate) fn bind(directory: &Path) -> io::Result<Self> {
        private_dir(directory)?;
        refuse_retained_registrations(directory)?;
        let seals_directory = directory.join(SEALS_DIRECTORY);
        if !seals_directory.exists() {
            use std::os::unix::fs::DirBuilderExt;
            fs::DirBuilder::new().mode(0o700).create(&seals_directory)?;
            File::open(directory)?.sync_all()?;
        }
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(directory.join(".resident-route-control.lock"))?;
        let meta = lock.metadata()?;
        if !meta.is_file()
            || meta.nlink() != 1
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.permissions().mode() & 0o777 != 0o600
        {
            return Err(invalid("route control lock identity refused"));
        }
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "route control active",
            ));
        }
        let socket = directory.join(SOCKET_NAME);
        match fs::symlink_metadata(&socket) {
            Err(e) if e.kind() == io::ErrorKind::NotFound => {}
            Err(e) => return Err(e),
            Ok(old) => {
                check_socket(&old)?;
                match connect_deadline(&socket, Instant::now() + Duration::from_millis(100)) {
                    Err(e) if e.kind() == io::ErrorKind::ConnectionRefused => {
                        let now = fs::symlink_metadata(&socket)?;
                        if (now.dev(), now.ino()) != (old.dev(), old.ino()) {
                            return Err(invalid("route stale socket changed"));
                        }
                        fs::remove_file(&socket)?;
                    }
                    _ => {
                        return Err(io::Error::new(
                            io::ErrorKind::AlreadyExists,
                            "route control socket active",
                        ))
                    }
                }
            }
        }
        let listener = UnixListener::bind(&socket)?;
        fs::set_permissions(&socket, fs::Permissions::from_mode(0o600))?;
        let meta = fs::symlink_metadata(&socket)?;
        check_socket(&meta)?;
        Ok(Self {
            listener,
            socket,
            identity: (meta.dev(), meta.ino()),
            _lock: lock,
            accepted: Vec::new(),
            seals_directory,
            poisoned: false,
        })
    }
    pub(crate) fn as_raw_fd(&self) -> libc::c_int {
        self.listener.as_raw_fd()
    }

    fn apply(
        &mut self,
        request: &RouteRegistration,
        mut admit: impl FnMut(
            &RouteRegistration,
            &mut RegistrationPublisher<'_>,
        ) -> io::Result<RouteRegistrationReply>,
    ) -> io::Result<RouteRegistrationReply> {
        if self.poisoned {
            return Err(invalid("resident route control publication is uncertain"));
        }
        request.validate()?;
        if let Some((prior, reply)) = self
            .accepted
            .iter()
            .find(|(prior, _)| prior.registration_nonce_hex == request.registration_nonce_hex)
        {
            return if prior == request {
                Ok(reply.clone())
            } else {
                Err(invalid(
                    "route registration nonce reused for different request",
                ))
            };
        }
        if self.accepted.len() >= MAX_ROUTES {
            return Err(invalid("route control registration limit reached"));
        }
        let mut publisher = RegistrationPublisher {
            directory: &self.seals_directory,
            request,
            started: false,
            published: None,
        };
        let result = admit(request, &mut publisher);
        match result {
            Ok(reply) if publisher.published.as_ref() == Some(&reply) => {
                self.accepted.push((request.clone(), reply.clone()));
                Ok(reply)
            }
            Ok(_) => {
                self.poisoned = true;
                Err(invalid(
                    "route admission returned without durable matching publication",
                ))
            }
            Err(error) => {
                self.poisoned |= publisher.started;
                Err(error)
            }
        }
    }
    /// Admission refusals affect only their connection. Interrupted publication
    /// is fatal: the resident must end instead of serving an unbound route.
    pub(crate) fn poll_once(
        &mut self,
        admit: impl FnMut(
            &RouteRegistration,
            &mut RegistrationPublisher<'_>,
        ) -> io::Result<RouteRegistrationReply>,
    ) -> io::Result<()> {
        let (mut stream, _) = self.listener.accept()?;
        if peer_uid(&stream).ok() != Some(unsafe { libc::geteuid() }) {
            return Ok(());
        }
        stream.set_read_timeout(Some(Duration::from_secs(2)))?;
        stream.set_write_timeout(Some(Duration::from_secs(1)))?;
        let result =
            read_frame(&mut stream, Instant::now() + Duration::from_secs(2)).and_then(|bytes| {
                let request: RouteRegistration = serde_json::from_slice(&bytes)?;
                self.apply(&request, admit)
            });
        if self.poisoned {
            return Err(invalid(
                "route seal publication interrupted; resident must end",
            ));
        }
        let envelope = match result {
            Ok(reply) => Envelope {
                result: Some(reply),
                error: None,
            },
            Err(error) => Envelope {
                result: None,
                error: Some(error.to_string().chars().take(512).collect()),
            },
        };
        let _ = write_frame(&mut stream, &serde_json::to_vec(&envelope)?);
        Ok(())
    }
}
fn check_socket(meta: &fs::Metadata) -> io::Result<()> {
    if !meta.file_type().is_socket()
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.permissions().mode() & 0o777 != 0o600
        || meta.nlink() != 1
    {
        return Err(invalid("route control socket identity refused"));
    }
    Ok(())
}
impl Drop for RouteControl {
    fn drop(&mut self) {
        if let Ok(meta) = fs::symlink_metadata(&self.socket) {
            if (meta.dev(), meta.ino()) == self.identity {
                let _ = fs::remove_file(&self.socket);
            }
        }
    }
}

/// Bounded client used by both first enrollment and regrant orchestration.
pub fn register(socket: &Path, request: &RouteRegistration) -> io::Result<RouteRegistrationReply> {
    request.validate()?;
    private_dir(
        socket
            .parent()
            .ok_or_else(|| invalid("route socket parent absent"))?,
    )?;
    check_socket(&fs::symlink_metadata(socket)?)?;
    let deadline = Instant::now() + Duration::from_secs(65);
    let mut stream = connect_deadline(socket, deadline)?;
    if peer_uid(&stream)? != unsafe { libc::geteuid() } {
        return Err(invalid("route control server uid differs"));
    }
    stream.set_read_timeout(Some(deadline.saturating_duration_since(Instant::now())))?;
    stream.set_write_timeout(Some(Duration::from_secs(2)))?;
    write_frame(&mut stream, &serde_json::to_vec(request)?)?;
    let envelope: Envelope = serde_json::from_slice(&read_frame(&mut stream, deadline)?)?;
    match (envelope.result, envelope.error) {
        (Some(reply), None)
            if reply.protocol == PROTOCOL
                && reply.registration_nonce_hex == request.registration_nonce_hex
                && reply.app == request.expected_app
                && reply.app_generation == request.expected_app_generation
                && reply.session_generation == request.expected_session_generation =>
        {
            Ok(reply)
        }
        (None, Some(error)) => Err(io::Error::other(error)),
        _ => Err(invalid("route control response mismatch")),
    }
}
pub fn register_file(socket: &Path, request: &Path) -> io::Result<RouteRegistrationReply> {
    register(socket, &serde_json::from_slice(&private_bytes(request)?)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::DirBuilderExt;
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    struct Fixture(PathBuf);
    impl Fixture {
        fn new() -> Self {
            let path =
                PathBuf::from(std::env::var_os("XDG_RUNTIME_DIR").expect("private test runtime"))
                    .join(format!(
                        "rctl-{}-{}",
                        std::process::id(),
                        NEXT.fetch_add(1, Ordering::Relaxed)
                    ));
            fs::DirBuilder::new().mode(0o700).create(&path).unwrap();
            Self(path)
        }
        fn request(&self) -> RouteRegistration {
            RouteRegistration {
                protocol: PROTOCOL.into(),
                registration_nonce_hex: "11".repeat(32),
                expected_app: "17".into(),
                expected_app_generation: "4".into(),
                expected_session_generation: "2".into(),
                directory: self.0.join("route"),
                dispatch_custody: self.0.join("custody.json"),
                dispatch_custody_sha256: "22".repeat(32),
                custodian_sha256: "33".repeat(32),
                display_name: "Member".into(),
                preferred_handle: "member".into(),
            }
        }
        fn materialize(&self) -> RouteRegistration {
            let mut request = self.request();
            crate::http_entrance::initialize_custodian(
                &request.directory,
                "app.example.test",
                "17",
                "8",
                "27",
                "37",
                "web",
            )
            .unwrap();
            let custody = serde_json::to_vec(&serde_json::json!({
                "protocol":"mini-spk-human-dispatch-custody-v1","app":"17","subject":"8","session":"27","sessionKind":"web",
                "issueIndex":"1","ticketResource":"37","packageManifest":"40","snapshotManifest":"41","sessionObserveCapability":"42",
                "manifestObserveCapability":"43","enrollmentObserveCapability":"44","signers":[{"role":"0","index":"0","keyId":"9","keyEpoch":"0","publicKeyHex":"00".repeat(32),"seedPath":self.0.join("seed")}]
            })).unwrap();
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(&request.dispatch_custody)
                .unwrap();
            file.write_all(&custody).unwrap();
            request.dispatch_custody_sha256 = format!("{:x}", Sha256::digest(&custody));
            request.custodian_sha256 = format!(
                "{:x}",
                Sha256::digest(fs::read(request.directory.join("custodian.json")).unwrap())
            );
            request
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
    fn reply(request: &RouteRegistration) -> RouteRegistrationReply {
        RouteRegistrationReply {
            protocol: PROTOCOL.into(),
            registration_nonce_hex: request.registration_nonce_hex.clone(),
            route_index: 1,
            app: request.expected_app.clone(),
            app_generation: request.expected_app_generation.clone(),
            session: "27".into(),
            session_generation: request.expected_session_generation.clone(),
            subject: "8".into(),
            ticket_resource: "37".into(),
            session_fingerprint_hex: "44".repeat(32),
            admitted_height: "123".into(),
            admitted_world_root: "456".into(),
        }
    }
    fn fixture_binding(request: &RouteRegistration) -> ContinuityBinding {
        let r = reply(request);
        ContinuityBinding {
            domain: "1".into(),
            semantics: "2".into(),
            app: r.app,
            app_generation: r.app_generation,
            session: r.session,
            session_generation: r.session_generation,
            subject: r.subject,
            ticket_resource: r.ticket_resource,
            session_fingerprint: [0x44; 32],
        }
    }
    fn publish_fixture(
        request: &RouteRegistration,
        publisher: &mut RegistrationPublisher<'_>,
    ) -> io::Result<RouteRegistrationReply> {
        let reply = reply(request);
        publisher.publish(&reply, &fixture_binding(request), "web")?;
        Ok(reply)
    }

    #[test]
    fn seal_existing_initial_route_preserves_b_and_retry_cannot_revive_lease() {
        let fixture = Fixture::new();
        let request = fixture.materialize();
        let (_, policy) = prepare(&request, "17", "4").unwrap();
        let listener =
            crate::http_entrance::PrivateHttpEntrance::bind_fixed(&request.directory, policy)
                .unwrap();
        let socket_before = fs::symlink_metadata(request.directory.join("http.sock")).unwrap();
        let identities = vec![
            RouteIdentity::from_request(&request),
            RouteIdentity {
                directory: fixture.0.join("b"),
                ..RouteIdentity::from_request(&request)
            },
        ];
        let b_binding = ContinuityBinding {
            subject: "9".into(),
            session: "28".into(),
            ..fixture_binding(&request)
        };
        let mut bindings = vec![None, Some(b_binding.clone())];
        let ended_a = crate::web_socket::StreamLease::begin(Duration::from_secs(60)).unwrap();
        ended_a.revoke();
        let live_b = crate::web_socket::StreamLease::begin(Duration::from_secs(60)).unwrap();
        let mut control = RouteControl::bind(&fixture.0).unwrap();
        assert_eq!(
            crate::dispatch_native::dispatch_opcode(bindings[0].as_ref()),
            34
        );
        let mut calls = 0;
        let sealed = control
            .apply(&request, |request, publisher| {
                let action = registration_action(request, &identities, &bindings)?;
                assert_eq!(action, RegistrationAction::Seal(0));
                calls += 1; // the production source154 admission happens here
                let binding = fixture_binding(request);
                let mut reply = reply(request);
                reply.route_index = action.index();
                publisher.publish(&reply, &binding, "web")?;
                bindings[action.index()] = Some(binding);
                Ok(reply)
            })
            .unwrap();
        assert_eq!(sealed.route_index, 0);
        assert_eq!(
            crate::dispatch_native::dispatch_opcode(bindings[0].as_ref()),
            164
        );
        assert_eq!(bindings[1], Some(b_binding));
        let again = control
            .apply(&request, |_, _| panic!("cached retry must not reseal"))
            .unwrap();
        assert_eq!(again, sealed);
        assert_eq!(calls, 1);
        assert!(ended_a.check().is_err());
        assert!(live_b.check().is_ok());
        let mut second = request.clone();
        second.registration_nonce_hex = "55".repeat(32);
        assert!(control
            .apply(&second, |request, _| {
                registration_action(request, &identities, &bindings)?;
                panic!("already pinned route must refuse before source admission")
            })
            .is_err());
        let socket_after = fs::symlink_metadata(request.directory.join("http.sock")).unwrap();
        assert_eq!(
            (socket_before.dev(), socket_before.ino()),
            (socket_after.dev(), socket_after.ino())
        );
        drop(listener);
    }

    #[test]
    fn seal_plan_checks_retained_identity_before_admission_and_works_at_capacity() {
        let fixture = Fixture::new();
        let request = fixture.materialize();
        let custody_bytes = fs::read(&request.dispatch_custody).unwrap();
        let policy_bytes = fs::read(request.directory.join("custodian.json")).unwrap();
        let captured = RouteIdentity::capture(
            &request.directory,
            &request.dispatch_custody,
            &request.display_name,
            &request.preferred_handle,
            &custody_bytes,
            &policy_bytes,
        );
        let mut identities = vec![captured];
        for index in 1..MAX_ROUTES {
            identities.push(RouteIdentity {
                directory: fixture.0.join(format!("route-{index}")),
                ..RouteIdentity::from_request(&request)
            });
        }
        let bindings = vec![None; MAX_ROUTES];
        assert_eq!(
            registration_action(&request, &identities, &bindings).unwrap(),
            RegistrationAction::Seal(0)
        );
        for field in ["custody", "policy", "path", "display", "handle"] {
            let mut changed = request.clone();
            match field {
                "custody" => changed.dispatch_custody_sha256 = "99".repeat(32),
                "policy" => changed.custodian_sha256 = "99".repeat(32),
                "path" => changed.dispatch_custody = fixture.0.join("other-custody.json"),
                "display" => changed.display_name = "Changed".into(),
                _ => changed.preferred_handle = "changed".into(),
            }
            assert!(registration_action(&changed, &identities, &bindings).is_err());
        }
        let mut append = request.clone();
        append.directory = fixture.0.join("another");
        assert!(registration_action(&append, &identities, &bindings).is_err());
        // Current-file drift with the original retained hash also fails before source.
        fs::write(request.directory.join("custodian.json"), b"changed").unwrap();
        assert!(prepare(&request, "17", "4").is_err());
    }

    #[test]
    fn interrupted_seal_publication_cannot_reopen_as_unbound_or_readmit() {
        let fixture = Fixture::new();
        let request = fixture.request();
        let mut control = RouteControl::bind(&fixture.0).unwrap();
        let mut bindings: Vec<Option<ContinuityBinding>> = vec![None];
        let mut calls = 0;
        let result = control.apply(&request, |request, publisher| {
            calls += 1;
            let mut reply = reply(request);
            reply.route_index = 0;
            publisher.publish(&reply, &fixture_binding(request), "web")?;
            // Model death after fsynced publication and before the memory update.
            Err(invalid("simulated interruption before memory publication"))
        });
        assert!(result.is_err());
        assert!(control.poisoned);
        assert!(bindings[0].is_none());
        let mut different = request.clone();
        different.registration_nonce_hex = "66".repeat(32);
        different.expected_session_generation = "3".into();
        assert!(control
            .apply(&different, |_, _| panic!("uncertain seal must not readmit"))
            .is_err());
        assert_eq!(calls, 1);
        let seal = control
            .seals_directory
            .join(format!("{}.json", request.registration_nonce_hex));
        let saved: serde_json::Value = serde_json::from_slice(&fs::read(seal).unwrap()).unwrap();
        assert_eq!(saved["request"], serde_json::to_value(&request).unwrap());
        assert_eq!(saved["binding"]["domain"], "1");
        drop(control);
        assert!(refuse_retained_registrations(&fixture.0).is_err());
        assert!(RouteControl::bind(&fixture.0).is_err());
        bindings.clear();
    }

    #[test]
    fn partial_pending_seal_and_publish_collision_fail_closed() {
        let fixture = Fixture::new();
        let mut control = RouteControl::bind(&fixture.0).unwrap();
        let request = fixture.request();
        let final_path = control
            .seals_directory
            .join(format!("{}.json", request.registration_nonce_hex));
        write_new(
            &control.seals_directory,
            final_path.file_name().unwrap().to_str().unwrap(),
            b"earlier seal",
        )
        .unwrap();
        assert!(control.apply(&request, publish_fixture).is_err());
        assert!(control.poisoned);
        assert_eq!(fs::read(&final_path).unwrap(), b"earlier seal");
        drop(control);
        assert!(RouteControl::bind(&fixture.0).is_err());
        let pending_fixture = Fixture::new();
        let control = RouteControl::bind(&pending_fixture.0).unwrap();
        write_new(
            &control.seals_directory,
            ".pending-interrupted.json",
            b"partial",
        )
        .unwrap();
        drop(control);
        assert!(refuse_retained_registrations(&pending_fixture.0).is_err());
        assert!(RouteControl::bind(&pending_fixture.0).is_err());
    }

    #[test]
    fn registration_is_idempotent_but_cannot_replace_or_reanimate_a_route() {
        let fixture = Fixture::new();
        let mut control = RouteControl::bind(&fixture.0).unwrap();
        let request = fixture.request();
        let mut calls = 0;
        let first = control
            .apply(&request, |request, publisher| {
                calls += 1;
                publish_fixture(request, publisher)
            })
            .unwrap();
        let again = control
            .apply(&request, |_, _| {
                panic!("retry must not readmit or mutate the prior lease")
            })
            .unwrap();
        assert_eq!(first, again);
        assert_eq!(calls, 1);
        let mut changed = request.clone();
        changed.expected_session_generation = "3".into();
        assert!(control
            .apply(&changed, |_, _| panic!(
                "changed nonce must not reach admission"
            ))
            .is_err());
        let mut fresh = changed;
        fresh.registration_nonce_hex = "55".repeat(32);
        assert!(control
            .apply(&fresh, |_, _| Err(invalid(
                "native current admission stale or revoked"
            )))
            .is_err());
        assert_eq!(control.accepted.len(), 1);
        assert_eq!(control.accepted[0].1.session_generation, "2");
    }
    #[test]
    fn route_files_require_exact_private_identity_hash_and_resident_generation() {
        let fixture = Fixture::new();
        let request = fixture.materialize();
        let (custody, policy) = prepare(&request, "17", "4").unwrap();
        assert_eq!(custody.session, policy.fixed_session);
        assert!(prepare(&request, "17", "5").is_err());
        let mut wrong = request.clone();
        wrong.dispatch_custody_sha256 = "99".repeat(32);
        assert!(prepare(&wrong, "17", "4").is_err());
        fs::set_permissions(&request.dispatch_custody, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(prepare(&request, "17", "4").is_err());
        fs::set_permissions(&request.dispatch_custody, fs::Permissions::from_mode(0o600)).unwrap();
        let link = fixture.0.join("link");
        std::os::unix::fs::symlink(&request.dispatch_custody, &link).unwrap();
        wrong = request.clone();
        wrong.dispatch_custody = link;
        assert!(prepare(&wrong, "17", "4").is_err());
        let mut value: serde_json::Value =
            serde_json::from_slice(&fs::read(&request.dispatch_custody).unwrap()).unwrap();
        value["session"] = "28".into();
        let bytes = serde_json::to_vec(&value).unwrap();
        fs::write(&request.dispatch_custody, &bytes).unwrap();
        wrong = request;
        wrong.dispatch_custody_sha256 = format!("{:x}", Sha256::digest(bytes));
        assert!(prepare(&wrong, "17", "4").is_err());
    }
    #[test]
    fn actual_private_control_roundtrip_retries_once_and_refuses_changed_nonce() {
        let fixture = Fixture::new();
        let mut control = RouteControl::bind(&fixture.0).unwrap();
        let socket = fixture.0.join(SOCKET_NAME);
        let request = fixture.request();
        let worker = std::thread::spawn(move || {
            let mut admissions = 0;
            for _ in 0..3 {
                control
                    .poll_once(|request, publisher| {
                        admissions += 1;
                        publish_fixture(request, publisher)
                    })
                    .unwrap();
            }
            assert_eq!(admissions, 1);
        });
        let first = register(&socket, &request).unwrap();
        assert_eq!(register(&socket, &request).unwrap(), first);
        let mut changed = request;
        changed.preferred_handle = "other".into();
        assert!(register(&socket, &changed).is_err());
        worker.join().unwrap();
        assert!(!socket.exists());
    }
    #[test]
    fn control_frame_has_an_absolute_deadline_and_a_size_bound() {
        let (mut server, mut client) = UnixStream::pair().unwrap();
        client
            .write_all(&((MAX_COMMAND + 1) as u32).to_le_bytes())
            .unwrap();
        assert!(read_frame(&mut server, Instant::now() + Duration::from_secs(1)).is_err());
        let (mut server, mut client) = UnixStream::pair().unwrap();
        let start = Instant::now();
        let worker = std::thread::spawn(move || {
            for byte in [4, 0, 0, 0, 1, 2, 3, 4] {
                if client.write_all(&[byte]).is_err() {
                    break;
                }
                std::thread::sleep(Duration::from_millis(20));
            }
        });
        assert!(read_frame(&mut server, start + Duration::from_millis(60)).is_err());
        assert!(start.elapsed() < Duration::from_millis(150));
        drop(server);
        worker.join().unwrap();
    }
}
