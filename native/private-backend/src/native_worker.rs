//! Closed recipient-local Protocol5 worker. Operator configuration pins native
//! source verifier image/argv and protected key/original-output/WAL paths.
//! It never accepts a network verifier, path, roster or authority callback.
//! Current output release remains a separate source obligation: this worker
//! receives protocol messages; it does not initiate request_delivery or export
//! plaintext result/outbox. Pending egress stays in the private recursive WAL.
use crate::{
    authenticated_ingress::{CommitteeParty, Envelope, Protocol, Receiver, SourcePartyAuthority},
    codec::{bad, bytes, Nat, Reader, MAX},
    private_initial::Initial,
    private_output_store::OutputMachine,
    recipient_seal::{RecipientKeyCustody, SealedIngress},
    source_endpoint::{InnerCredentialOutcome, InnerCredentialRequest, RequestClaim},
};
use sha2::{Digest, Sha256, Sha512};
use std::{
    fs::File,
    io::{Read, Result, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
};
const DISPATCH: &[u8] = b"DREGG.PRIVATE.WORKER.DISPATCH\x01";
const CONFIG: &[u8] = b"DREGG.PRIVATE.WORKER.CONFIG\x01";
#[derive(Clone)]
pub struct DispatchClaim {
    pub request_bytes: Vec<u8>,
    pub source_index: Nat,
    pub enrollment_bytes: Vec<u8>,
    pub source_record_bytes: Vec<u8>,
    pub source_receipt_bytes: Vec<u8>,
    pub certificate_bytes: Vec<u8>,
    pub worker_profile: Vec<u8>,
}
impl DispatchClaim {
    pub fn decode(b: &[u8]) -> Result<Self> {
        if b.len() > MAX || !b.starts_with(DISPATCH) {
            return Err(bad("worker dispatch frame/bound"));
        }
        let mut r = Reader::new(&b[DISPATCH.len()..])?;
        let v = Self {
            request_bytes: r.bytes()?,
            source_index: r.nat()?,
            enrollment_bytes: r.bytes()?,
            source_record_bytes: r.bytes()?,
            source_receipt_bytes: r.bytes()?,
            certificate_bytes: r.bytes()?,
            worker_profile: r.bytes()?,
        };
        r.finish()?;
        if v.encode() != b {
            return Err(bad("worker dispatch canonical"));
        }
        Ok(v)
    }
    pub fn encode(&self) -> Vec<u8> {
        let mut b = DISPATCH.to_vec();
        bytes(&self.request_bytes, &mut b);
        self.source_index.put(&mut b);
        for x in [
            &self.enrollment_bytes,
            &self.source_record_bytes,
            &self.source_receipt_bytes,
            &self.certificate_bytes,
            &self.worker_profile,
        ] {
            bytes(x, &mut b);
        }
        b
    }
}
/// Selected from protected operator custody; never decoded from DispatchClaim.
pub struct Config {
    pub local_party: CommitteeParty,
    pub n: usize,
    pub capacity_per_party: usize,
    pub key_identity: Vec<u8>,
    pub key_capacity: usize,
    pub key_wal: PathBuf,
    pub output_initial_base: PathBuf,
    pub output_context: [u8; 32],
    pub output_recipient: u16,
    pub output_bootstrap_sha256: [u8; 32],
    pub receiver_wal: PathBuf,
    pub anchor: PathBuf,
    pub native_program: PathBuf,
    pub native_image_sha256: [u8; 32],
    pub native_argv: Vec<String>,
    pub worker_profile: Vec<u8>,
}
fn path(r: &mut Reader<'_>) -> Result<PathBuf> {
    let s = String::from_utf8(r.bytes()?).map_err(|_| bad("operator path encoding"))?;
    let p = PathBuf::from(s);
    if !p.is_absolute() {
        return Err(bad("operator path must be absolute"));
    }
    Ok(p)
}
impl Config {
    /// Canonical protected local operator configuration. No secret key bytes
    /// enter this frame; it is never part of the public source packet.
    pub fn encode(&self) -> Result<Vec<u8>> {
        let mut b = CONFIG.to_vec();
        bytes(&self.local_party.encode(), &mut b);
        Nat::new(self.n as u64).put(&mut b);
        Nat::new(self.capacity_per_party as u64).put(&mut b);
        bytes(&self.key_identity, &mut b);
        Nat::new(self.key_capacity as u64).put(&mut b);
        for path in [&self.key_wal, &self.output_initial_base] {
            bytes(
                path.to_str()
                    .ok_or_else(|| bad("operator path encoding"))?
                    .as_bytes(),
                &mut b,
            );
        }
        bytes(&self.output_context, &mut b);
        Nat::new(self.output_recipient as u64).put(&mut b);
        bytes(&self.output_bootstrap_sha256, &mut b);
        for path in [&self.receiver_wal, &self.anchor, &self.native_program] {
            bytes(
                path.to_str()
                    .ok_or_else(|| bad("operator path encoding"))?
                    .as_bytes(),
                &mut b,
            );
        }
        bytes(&self.native_image_sha256, &mut b);
        Nat::new(self.native_argv.len() as u64).put(&mut b);
        for arg in &self.native_argv {
            bytes(arg.as_bytes(), &mut b);
        }
        bytes(&self.worker_profile, &mut b);
        if b.len() > MAX {
            return Err(bad("worker config capacity"));
        }
        Ok(b)
    }
    /// Check the actual files used by each custody role, including extension-
    /// derived original/lock/pending paths. Resolve parents before comparison;
    /// existing hard-link aliases and symlinks also refuse before secret work.
    pub fn validate_paths(&self) -> Result<()> {
        use std::os::unix::fs::MetadataExt;
        let roles = vec![
            self.key_wal.clone(),
            self.key_wal.with_extension("lock"),
            self.output_initial_base.clone(),
            self.output_initial_base.with_extension("lock"),
            self.output_initial_base.with_extension("initial"),
            self.output_initial_base.with_extension("initial.lock"),
            self.receiver_wal.clone(),
            self.receiver_wal.with_extension("lock"),
            self.receiver_wal.with_extension("initial"),
            self.receiver_wal.with_extension("initial.lock"),
            self.anchor.clone(),
            self.native_program.clone(),
        ];
        let mut names = std::collections::BTreeSet::new();
        let mut inodes = std::collections::BTreeSet::new();
        for role in roles {
            if !role.is_absolute() {
                return Err(bad("worker custody path must be absolute"));
            }
            let parent = role.parent().ok_or_else(|| bad("worker custody parent"))?;
            let name = role
                .file_name()
                .ok_or_else(|| bad("worker custody filename"))?;
            let resolved = std::fs::canonicalize(parent)?.join(name);
            if !names.insert(resolved) {
                return Err(bad("worker custody role path collision"));
            }
            match std::fs::symlink_metadata(&role) {
                Ok(m) => {
                    if m.file_type().is_symlink() || !inodes.insert((m.dev(), m.ino())) {
                        return Err(bad("worker custody role inode alias"));
                    }
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }
    pub fn load(file: &Path) -> Result<Self> {
        let meta = std::fs::symlink_metadata(file)?;
        use std::os::unix::fs::PermissionsExt;
        if !meta.is_file() || meta.permissions().mode() & 0o077 != 0 || meta.len() > MAX as u64 {
            return Err(bad("protected operator config custody"));
        }
        let b = std::fs::read(file)?;
        if !b.starts_with(CONFIG) {
            return Err(bad("worker config domain"));
        }
        let mut r = Reader::new(&b[CONFIG.len()..])?;
        let local_party = CommitteeParty::decode(&r.bytes()?)?;
        let n = r.count()?;
        let capacity_per_party = r.count()?;
        let key_identity = r.bytes()?;
        let key_capacity = r.count()?;
        let key_wal = path(&mut r)?;
        let output_initial_base = path(&mut r)?;
        let output_context = r
            .bytes()?
            .try_into()
            .map_err(|_| bad("output context bound"))?;
        let output_recipient =
            u16::try_from(r.count()?).map_err(|_| bad("output recipient bound"))?;
        let output_bootstrap_sha256 = r
            .bytes()?
            .try_into()
            .map_err(|_| bad("bootstrap digest bound"))?;
        let receiver_wal = path(&mut r)?;
        let anchor = path(&mut r)?;
        let native_program = path(&mut r)?;
        let digest = r.bytes()?;
        let native_image_sha256 = digest
            .try_into()
            .map_err(|_| bad("native image digest bound"))?;
        let count = r.count()?;
        if count > 32 {
            return Err(bad("native fixed argv bound"));
        }
        let mut native_argv = vec![];
        for _ in 0..count {
            native_argv
                .push(String::from_utf8(r.bytes()?).map_err(|_| bad("native argv encoding"))?);
        }
        let worker_profile = r.bytes()?;
        r.finish()?;
        if local_party.context.protocol != Protocol::PrivateOutput
            || local_party.party != local_party.context.recipient
            || n == 0
            || n > 16
            || local_party.party as usize >= n
            || capacity_per_party == 0
            || capacity_per_party > 65536
            || output_recipient as usize >= n
            || key_capacity == 0
            || key_capacity > 65536
            || worker_profile.is_empty()
            || key_identity.is_empty()
        {
            return Err(bad("worker fixed receiving profile"));
        }
        let config = Self {
            local_party,
            n,
            capacity_per_party,
            key_identity,
            key_capacity,
            key_wal,
            output_initial_base,
            output_context,
            output_recipient,
            output_bootstrap_sha256,
            receiver_wal,
            anchor,
            native_program,
            native_image_sha256,
            native_argv,
            worker_profile,
        };
        config.validate_paths()?;
        Ok(config)
    }
}
// Constructed only by the fixed image invocation in this module. Caller claims
// cannot create it; clear SIGN is compared endpoint-locally, never sent to host.
struct NativeAuthority {
    envelope: Envelope,
}
impl SourcePartyAuthority for NativeAuthority {
    fn verify_enrolled_packet(&self, p: &CommitteeParty, s: &[u8], c: &[u8]) -> Result<()> {
        if *p != self.envelope.party
            || s != self.envelope.signing_bytes()
            || c != self.envelope.credential
        {
            return Err(bad("native checked envelope scope"));
        }
        Ok(())
    }
}
fn invoke_native(
    config: &Config,
    request: &InnerCredentialRequest,
) -> Result<InnerCredentialOutcome> {
    // Keep the hashed image open and execute that descriptor on Linux. This
    // avoids replacing the path between digest verification and exec. The
    // deployment must pin the actual source-compiled image/config, not a test
    // executable emitting successful bytes.
    #[cfg(not(target_os = "linux"))]
    {
        let _ = (config, request);
        return Err(bad(
            "closed native worker requires Linux descriptor execution",
        ));
    }
    #[cfg(target_os = "linux")]
    {
        use std::os::fd::AsRawFd;
        let mut image = File::open(&config.native_program)?;
        let mut hash = Sha256::new();
        let mut buffer = [0u8; 65536];
        loop {
            let count = image.read(&mut buffer)?;
            if count == 0 {
                break;
            }
            hash.update(&buffer[..count]);
        }
        if hash.finalize().as_slice() != config.native_image_sha256 {
            return Err(bad("native verifier image pin refused"));
        }
        let fd = image.as_raw_fd();
        let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
        if flags < 0 || unsafe { libc::fcntl(fd, libc::F_SETFD, flags & !libc::FD_CLOEXEC) } < 0 {
            return Err(std::io::Error::last_os_error());
        }
        let mut child = Command::new("/usr/bin/timeout")
            .arg("45s")
            .arg(format!("/proc/self/fd/{fd}"))
            .args(&config.native_argv)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()?;
        let raw = request.encode()?;
        child
            .stdin
            .take()
            .ok_or_else(|| bad("native stdin absent"))?
            .write_all(&raw)?;
        let mut reply = vec![];
        child
            .stdout
            .take()
            .ok_or_else(|| bad("native stdout absent"))?
            .take(crate::source_endpoint::MAX_LOCAL_INNER as u64 + 1)
            .read_to_end(&mut reply)?;
        if !child.wait()?.success() {
            return Err(bad("actual native original-prefix verifier refused"));
        }
        drop(image);
        InnerCredentialOutcome::decode(&reply)
    }
}
/// Explicit successor worker profile. This holds the actual sealed verifier and
/// original settings for the whole synchronous invocation. Construction is only
/// from protected operator Config and original protected settings bytes; source
/// enrollment/worker image activation is a separate required deployment step.
/// The legacy worker CLI and its frozen source image remain unchanged.
pub struct SealedNative {
    invocation: crate::pinned_execution::SealedInvocation,
    config_bytes: Vec<u8>,
    arguments: Vec<String>,
}
impl SealedNative {
    pub fn new(config: &Config, original_native_settings: &[u8]) -> Result<Self> {
        // Config v1 argv begins with the original native settings path. The
        // sealed helper replaces ONLY that argument by the held settings FD.
        let first = config.native_argv.first().ok_or_else(|| bad("sealed native settings argument absent"))?;
        if !Path::new(first).is_absolute() {
            return Err(bad("sealed native original settings path"));
        }
        config.validate_paths()?;
        let invocation = crate::pinned_execution::SealedInvocation::new(
            &config.native_program, &config.native_image_sha256,
            original_native_settings,
        )?;
        Ok(Self { invocation, config_bytes: config.encode()?,
            arguments: config.native_argv[1..].to_vec() })
    }
    fn invoke(&self, config: &Config, request: &InnerCredentialRequest) -> Result<InnerCredentialOutcome> {
        if self.config_bytes != config.encode()? {
            return Err(bad("sealed native protected profile changed"));
        }
        let raw = request.encode()?;
        let reply = self.invocation.output_with_input(
            &self.arguments, &raw, 45,
            crate::source_endpoint::MAX_LOCAL_INNER,
            crate::source_endpoint::MAX_LOCAL_INNER,
        )?;
        InnerCredentialOutcome::decode(&reply)
    }
}
// Closed local selector; no requester callback or successful-byte oracle.
enum NativeInvocation<'a> { Legacy, Sealed(&'a SealedNative) }
impl NativeInvocation<'_> {
    fn invoke(&self, config: &Config, request: &InnerCredentialRequest) -> Result<InnerCredentialOutcome> {
        match self {
            Self::Legacy => invoke_native(config, request),
            Self::Sealed(held) => held.invoke(config, request),
        }
    }
}
/// Explicit sealed successor consumer. It shares the exact original-prefix
/// authority comparison and durable receiver with the legacy path. A new source
/// worker image/profile must activate this path; the existing CLI uses Legacy.
pub fn receive_sealed(config: &Config, dispatch: &DispatchClaim, held: &SealedNative) -> Result<Vec<u8>> {
    receive_with_invocation(config, dispatch, NativeInvocation::Sealed(held))
}
/// Actual native-image verification followed by actual private receiver WAL.
/// Response is pending local egress, not source Qualified/terminal YES or an
/// encrypted audience release. All recursive plaintext stays in private WAL.
pub fn receive(config: &Config, dispatch: &DispatchClaim) -> Result<Vec<u8>> {
    receive_with_invocation(config, dispatch, NativeInvocation::Legacy)
}
fn receive_with_invocation(config: &Config, dispatch: &DispatchClaim, invocation: NativeInvocation<'_>) -> Result<Vec<u8>> {
    if dispatch.worker_profile != config.worker_profile
        || dispatch.enrollment_bytes.is_empty()
        || dispatch.source_record_bytes.is_empty()
        || dispatch.source_receipt_bytes.is_empty()
    {
        return Err(bad("worker original source bindings absent"));
    }
    config.validate_paths()?;
    let request = RequestClaim::decode(&dispatch.request_bytes)?;
    let capsule = SealedIngress::decode(&request.raw_carrier)?;
    if capsule.party.context != config.local_party.context
        || capsule.party.party as usize >= config.n
    {
        return Err(bad("worker fixed source context"));
    }
    let keys =
        RecipientKeyCustody::open(&config.key_wal, &config.key_identity, config.key_capacity)?;
    let opened = keys.open_capsule(
        &capsule,
        &capsule.party,
        capsule.sequence,
        &capsule.recipient,
    )?;
    let native_request = InnerCredentialRequest::from_opened(
        &request,
        &opened,
        dispatch.source_index.clone(),
        dispatch.certificate_bytes.clone(),
    )?;
    let native = invocation.invoke(config, &native_request)?;
    if !native.matches_opened(&native_request, &opened)? {
        return Err(bad("native original credential refused"));
    }
    match &native {
        InnerCredentialOutcome::CredentialCheckedClaim {
            enrollment_bytes,
            source_receipt_bytes,
            ..
        } if *enrollment_bytes == dispatch.enrollment_bytes
            && *source_receipt_bytes == dispatch.source_receipt_bytes => {}
        _ => {
            return Err(bad(
                "native recovered enrollment/receipt differs from dispatch",
            ))
        }
    }
    let authority = NativeAuthority {
        envelope: opened.inner().clone(),
    };
    // FIRST persistent-output share getter is after native original-prefix
    // authorization. Original protected creation and rollback anchor are still
    // custody premises, not an arbitrary snapshot certification.
    // Actual original private output creation/key/outbox replay, held locked.
    // The operator profile pins this immutable bootstrap WAL prefix; further
    // packets append only the separately bound authenticated receiver WAL.
    let bootstrap = crate::private_output_store::Store::reopen(
        &config.output_initial_base,
        &config.local_party.context.generation,
        config.output_context,
        config.local_party.party,
        config.output_recipient,
        &config.anchor,
    )?;
    let bootstrap_file = File::open(&config.output_initial_base)?;
    if bootstrap_file.metadata()?.len() > MAX as u64 {
        return Err(bad("frozen bootstrap local capacity"));
    }
    let mut bootstrap_bytes = vec![];
    bootstrap_file
        .take(MAX as u64 + 1)
        .read_to_end(&mut bootstrap_bytes)?;
    if Sha256::digest(&bootstrap_bytes).as_slice() != config.output_bootstrap_sha256 {
        return Err(bad("frozen private bootstrap prefix changed"));
    }
    let state = bootstrap.state().clone();
    let mut original_binding = b"DREGG.PRIVATE.WORKER.ORIGINAL.BINDING\x01".to_vec();
    original_binding.extend(config.output_bootstrap_sha256);
    original_binding.extend(config.output_context);
    bytes(&config.worker_profile, &mut original_binding);
    let mut receiver = Receiver::open_bound(
        &config.receiver_wal,
        config.local_party.context.clone(),
        config.n,
        config.capacity_per_party,
        OutputMachine { state },
        &original_binding,
    )?;
    let outcome = receiver.receive(&authority, &opened.inner().encode()?)?;
    // Hiding endpoint receipt for retained pending egress. Do not publish an
    // unkeyed hash of a low-entropy private outbox or any clear result.
    let mut hidden = b"DREGG.PRIVATE.WORKER.PENDING.OUTBOX\x01".to_vec();
    // This key is endpoint-owned, not the sender-selected hiding nonce. A
    // corrupt sender knowing its nonce must not dictionary-test private egress.
    let pending_base = config.receiver_wal.with_extension("pending-key");
    let key = if pending_base.with_extension("initial").exists() {
        Initial::load(&pending_base, b"DREGG.PRIVATE.WORKER.PENDING.KEY\x01")?
    } else {
        let mut random = [0u8; 32];
        File::open("/dev/urandom")?.read_exact(&mut random)?;
        Initial::create(
            &pending_base,
            b"DREGG.PRIVATE.WORKER.PENDING.KEY\x01",
            &random,
        )?
    };
    if key.bytes.len() != 32 {
        return Err(bad("private pending receipt key bound"));
    }
    hidden.extend(&key.bytes);
    bytes(outcome.outbox(), &mut hidden);
    let mut response = b"DREGG.PRIVATE.WORKER.PENDING\x01".to_vec();
    response.extend(opened.semantic_commitment());
    response.extend(Sha512::digest(&request.raw_carrier));
    response.extend(Sha512::digest(&hidden));
    // Source endpoint must retain UNKNOWN/pending until actual recipient-sealed
    // egress is signed/admitted. This response cannot be old PROGRESSv1/v2.
    Ok(response)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{authenticated_ingress::Context, codec::Generation};
    fn config(program: &str, digest: [u8; 32]) -> Config {
        Config {
            local_party: CommitteeParty {
                context: Context {
                    protocol: Protocol::PrivateOutput,
                    generation: Generation {
                        invocation: Nat::new(1),
                        command: vec![3],
                        attempt: Nat::new(0),
                        generation: Nat::new(1),
                        configuration: Nat::new(2),
                    },
                    authority_epoch: Nat::new(1),
                    session: vec![4],
                    recipient: 1,
                    recipient_role: b"backend-party".to_vec(),
                },
                party: 1,
                subject: b"party1".to_vec(),
                key_epoch: Nat::new(1),
                key_binding: vec![5],
                credential_purpose: b"opaque".to_vec(),
            },
            n: 4,
            capacity_per_party: 4,
            key_identity: vec![7],
            key_capacity: 2,
            key_wal: "/never-selected-key-path".into(),
            output_initial_base: "/never-selected-output-path".into(),
            output_context: [1; 32],
            output_recipient: 1,
            output_bootstrap_sha256: [2; 32],
            receiver_wal: "/never-selected-receiver-path".into(),
            anchor: "/never-selected-anchor-path".into(),
            native_program: std::fs::canonicalize(program).unwrap_or_else(|_| program.into()),
            native_image_sha256: digest,
            native_argv: vec![],
            worker_profile: vec![9],
        }
    }
    #[test]
    fn derived_worker_custody_roles_and_hardlinks_refuse_before_secret_work() {
        let root = std::env::temp_dir().join(format!(
            "worker-role-poles-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&root).unwrap();
        let mut cfg = config("/usr/bin/false", [0; 32]);
        cfg.key_wal = root.join("key.wal");
        cfg.output_initial_base = root.join("state.output");
        cfg.receiver_wal = root.join("state.receiver");
        cfg.anchor = root.join("anchor.socket");
        assert!(
            cfg.validate_paths().is_err(),
            "same stem original/lock collision"
        );
        cfg.output_initial_base = root.join("output.wal");
        cfg.receiver_wal = root.join("receiver.wal");
        cfg.validate_paths().unwrap();
        std::fs::write(&cfg.key_wal, b"retained").unwrap();
        std::fs::hard_link(&cfg.key_wal, &cfg.receiver_wal).unwrap();
        assert!(
            cfg.validate_paths().is_err(),
            "different names cannot alias the same inode"
        );
        assert!(!cfg.output_initial_base.with_extension("initial").exists());
        assert!(!cfg.receiver_wal.with_extension("initial").exists());
    }
    #[test]
    fn protected_operator_config_roundtrip_refuses_public_file_and_trailing_bytes() {
        use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
        let path = std::env::temp_dir().join(format!(
            "mini-worker-config-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let cfg = config("/usr/bin/false", [0; 32]);
        let bytes = cfg.encode().unwrap();
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&path)
            .unwrap();
        file.write_all(&bytes).unwrap();
        file.sync_all().unwrap();
        assert_eq!(Config::load(&path).unwrap().encode().unwrap(), bytes);
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o644)).unwrap();
        assert!(Config::load(&path).is_err());
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600)).unwrap();
        file.write_all(&[0]).unwrap();
        file.sync_all().unwrap();
        assert!(Config::load(&path).is_err());
    }
    #[test]
    fn actual_fixed_native_program_wrong_image_and_process_refusal_cannot_authenticate() {
        let request = InnerCredentialRequest {
            original_request_bytes: vec![1],
            source_index: Nat::new(0),
            certificate_bytes: vec![2],
            credential: vec![3],
        };
        let mut cfg = config("/usr/bin/false", [0; 32]);
        assert!(invoke_native(&cfg, &request).is_err());
        cfg.native_image_sha256 = Sha256::digest(std::fs::read("/usr/bin/false").unwrap()).into();
        assert!(
            invoke_native(&cfg, &request).is_err(),
            "actual pinned child refusal never yields NativeAuthority"
        );
    }
    #[test]
    fn local_worker_source_bindings_and_large_inner_history_remain_distinct_from_mix_bounds() {
        let request = InnerCredentialRequest {
            original_request_bytes: vec![1],
            source_index: Nat::from_be(&[255; 32]),
            certificate_bytes: vec![2; 300000],
            credential: vec![3],
        };
        let bytes = request.encode().unwrap();
        assert!(bytes.len() > crate::source_endpoint::MAX_COMPLETE_NATIVE_REQUEST);
        assert_eq!(InnerCredentialRequest::decode(&bytes).unwrap(), request);
        assert!(crate::source_endpoint::admit_complete_transport_frame(&bytes, &[]).is_err());
        let claim = DispatchClaim {
            request_bytes: vec![1],
            source_index: request.source_index,
            enrollment_bytes: vec![],
            source_record_bytes: vec![2],
            source_receipt_bytes: vec![3],
            certificate_bytes: vec![4],
            worker_profile: vec![9],
        };
        assert_eq!(
            DispatchClaim::decode(&claim.encode()).unwrap().encode(),
            claim.encode()
        );
        assert!(
            receive(&config("/usr/bin/false", [0; 32]), &claim).is_err(),
            "no key/output path read before missing source binding refusal"
        );
        let mut trailing = claim.encode();
        trailing.push(0);
        assert!(DispatchClaim::decode(&trailing).is_err());
    }
}
