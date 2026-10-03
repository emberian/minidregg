//! Durable physical request custody. These states are never Mini admission
//! verdicts. Only the original native exchange can supply a native reply.
use super::{
    directory, outcome, persist, read_private, Admission, Journal, MAX_ENVELOPE, UNCERTAIN,
};
use crate::{transport, Result};
use sha2::{Digest, Sha256};
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{mpsc, Arc, Mutex};

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum DispatchState {
    Ready(Vec<u8>),
    Accepted,
    Uncertain,
}
impl DispatchState {
    pub(crate) fn transport_reply(self) -> Vec<u8> {
        match self {
            Self::Ready(v) => v,
            // A physical continuation is explicitly outside the native frame.
            Self::Accepted => outcome(3, b"durable transport custody; fetch exact result later"),
            Self::Uncertain => outcome(1, UNCERTAIN),
        }
    }
}
struct State {
    journal: Journal,
    active: HashSet<[u8; 16]>,
    reserved: [usize; 3],
}

/// A resident gateway owns accepted exact envelopes. Three bounded workers keep
/// application work from consuming the reserved control/recovery worker slots.
/// Restart resumes only requests without a dispatch marker; an unknown effect
/// is fenced forever until a source-authorized native recovery request resolves it.
pub(crate) struct AsyncDispatch {
    state: Arc<Mutex<State>>,
    wake: [mpsc::SyncSender<()>; 3],
    config: Vec<u8>,
}
impl AsyncDispatch {
    pub(crate) fn open(
        root: &Path,
        target: &Path,
        config: &[u8],
        pending: usize,
        retained: usize,
        max_reply: usize,
    ) -> Result<Self> {
        if pending < 3
            || pending > 256
            || retained < pending * 4
            || retained > 1_000_000
            || max_reply == 0
            || max_reply > MAX_ENVELOPE
            || config.len() > transport::MAX_CONFIG
            || std::os::unix::ffi::OsStrExt::as_bytes(target.as_os_str()).len() > 4096
        {
            return Err("invalid public asynchronous custody capacity".into());
        }
        directory(root)?;
        let lease = Arc::new(transport::service_lock(&root.join("async-service.lock"))?);
        // A restart cannot silently redirect an existing obligation to a different
        // native service, deployment config, or reply capacity.
        let mut pin = b"Mini/native-async-custody/v1".to_vec();
        pin.extend_from_slice(&(max_reply as u64).to_le_bytes());
        pin.extend_from_slice(&(pending as u64).to_le_bytes());
        pin.extend_from_slice(&(retained as u64).to_le_bytes());
        let target_bytes = std::os::unix::ffi::OsStrExt::as_bytes(target.as_os_str());
        pin.extend_from_slice(&(target_bytes.len() as u64).to_le_bytes());
        pin.extend_from_slice(target_bytes);
        pin.extend_from_slice(config);
        let profile = root.join("async-profile");
        if profile.exists() {
            if read_private(&profile, transport::MAX_CONFIG + 8192)? != pin {
                return Err("changed native gateway pin; preserve accepted obligations".into());
            }
        } else {
            persist(&profile, &pin)?;
        }
        let journal = Journal::open(root, retained)?;
        // Class reservations also count crash-left records before access/request
        // publication. They are never silently reclaimed or ignored on restart.
        let mut reserved = [0; 3];
        for entry in fs::read_dir(root).map_err(|e| e.to_string())? {
            let path = entry.map_err(|e| e.to_string())?.path();
            if let Some(stem) = path
                .file_name()
                .and_then(|v| v.to_str())
                .and_then(|v| v.strip_suffix(".class"))
            {
                if crate::decode_hex(stem)?.len() != 16 {
                    return Err("invalid custody reservation ID".into());
                }
                let class = read_private(&path, 1)?;
                if class.len() != 1 || class[0] >= 3 {
                    return Err("invalid custody reservation class".into());
                }
                reserved[class[0] as usize] += 1;
            }
        }
        if (0..3).any(|c| reserved[c] > journal.max[c]) {
            return Err("custody reservations exceed retained class capacity".into());
        }
        let state = Arc::new(Mutex::new(State {
            journal,
            active: HashSet::new(),
            reserved,
        }));
        let wake = std::array::from_fn(|class| {
            // Notifications coalesce. Durable request records, rather than an
            // in-memory queue, hold all accepted work and survive a lost caller.
            let (tx, rx) = mpsc::sync_channel(1);
            let state = state.clone();
            let target = target.to_path_buf();
            let config = config.to_vec();
            let lease = lease.clone();
            std::thread::spawn(move || {
                let _lease = lease;
                loop {
                    match run_next(&state, class, &target, &config, max_reply) {
                        Ok(true) => continue,
                        Ok(false) => {
                            if rx.recv().is_err() {
                                break;
                            }
                        }
                        // Preserve the immutable claim/request on an I/O fault.
                        // No alternate dispatch or invented native reply follows.
                        Err(_) => break,
                    }
                }
            });
            tx
        });
        Ok(Self {
            state,
            wake,
            config: config.to_vec(),
        })
    }

    pub(crate) fn offer(
        &self,
        class: usize,
        id: [u8; 16],
        body: &[u8],
        recovery: &[u8; 32],
    ) -> Result<DispatchState> {
        if class >= 3 || body.is_empty() || body.len() > MAX_ENVELOPE {
            return Err("native envelope exceeds asynchronous custody bound".into());
        }
        // A transport credential grants no Mini authority. The same public
        // envelope gate runs before custody; the native source admits all semantics.
        transport::catalog_enabled(&self.config).and_then(|c| {
            transport::public_envelope(body, &self.config, c).map_err(str::to_owned)
        })?;
        let mut s = self
            .state
            .lock()
            .map_err(|_| "native custody state poisoned")?;
        let access = s.journal.path(&id, "recovery");
        let class_path = s.journal.path(&id, "class");
        if class_path.exists() {
            if read_private(&class_path, 1)? != [class as u8] {
                return Err("custody reservation class conflict".into());
            }
        } else {
            if s.reserved[class] >= s.journal.max[class] {
                return Err("native custody class capacity exhausted before reservation".into());
            }
            // Reserve before publishing anything else. On an I/O error we keep
            // the in-memory reservation conservatively; restart counts whichever
            // immutable class records actually reached disk.
            s.reserved[class] += 1;
            persist(&class_path, &[class as u8])?;
        }
        if access.exists() {
            check_access(&access, recovery)?;
        } else {
            if s.journal.path(&id, "request").exists() {
                return Err(
                    "existing request lacks original recovery access; preserve custody".into(),
                );
            }
            persist(&access, recovery)?;
        }
        let admission = s.journal.admit(class, &id, body)?;
        let result = status(&s, &id, admission);
        // Wake after the exact immutable record has been durably accepted. A full
        // notification slot already promises a scan of the durable obligations.
        if result == DispatchState::Accepted {
            match self.wake[class].try_send(()) {
                Ok(()) | Err(mpsc::TrySendError::Full(())) => (),
                Err(mpsc::TrySendError::Disconnected(())) => {
                    return Err(
                        "native custody worker stopped; restart preserves obligations".into(),
                    )
                }
            }
        }
        Ok(result)
    }

    /// Fetch never admits or dispatches a request. The immutable original access
    /// capability, body digest and semantic class are independent of a new outer
    /// reply key or a reserved transport recovery epoch.
    pub(crate) fn fetch(
        &self,
        class: usize,
        id: [u8; 16],
        digest: &[u8; 32],
        recovery: &[u8; 32],
    ) -> Result<DispatchState> {
        let mut s = self
            .state
            .lock()
            .map_err(|_| "native custody state poisoned")?;
        check_access(&s.journal.path(&id, "recovery"), recovery)?;
        let body = read_private(&s.journal.path(&id, "request"), MAX_ENVELOPE)?;
        if class >= 3
            || Sha256::digest(&body).as_slice() != digest
            || read_private(&s.journal.path(&id, "class"), 1)? != [class as u8]
        {
            return Err("recovery capability does not name exact original request/class".into());
        }
        let admission = s.journal.admit(class, &id, &body)?;
        Ok(status(&s, &id, admission))
    }
}
fn check_access(path: &Path, expected: &[u8; 32]) -> Result<()> {
    let actual = read_private(path, 32)?;
    // Constant-time capability comparison, using the existing HMAC primitive.
    let key = ring::hmac::Key::new(ring::hmac::HMAC_SHA256, expected);
    let proof = ring::hmac::sign(&key, b"Mini/native-custody-access/v1");
    ring::hmac::verify(
        &ring::hmac::Key::new(ring::hmac::HMAC_SHA256, &actual),
        b"Mini/native-custody-access/v1",
        proof.as_ref(),
    )
    .map_err(|_| "native custody recovery capability refused".into())
}
fn status(s: &State, id: &[u8; 16], admission: Admission) -> DispatchState {
    match admission {
        Admission::Cached(v) => DispatchState::Ready(v),
        Admission::Uncertain if !s.active.contains(id) => DispatchState::Uncertain,
        Admission::Uncertain | Admission::Fresh => DispatchState::Accepted,
    }
}
fn run_next(
    state: &Arc<Mutex<State>>,
    class: usize,
    target: &Path,
    config: &[u8],
    max_reply: usize,
) -> Result<bool> {
    let job = {
        let mut s = state.lock().map_err(|_| "native custody state poisoned")?;
        let mut records: Vec<PathBuf> = fs::read_dir(&s.journal.root)
            .map_err(|e| e.to_string())?
            .map(|e| e.map(|e| e.path()).map_err(|e| e.to_string()))
            .collect::<Result<_>>()?;
        records.sort();
        let mut job = None;
        for path in records {
            let Some(stem) = path
                .file_name()
                .and_then(|n| n.to_str())
                .and_then(|n| n.strip_suffix(".request"))
            else {
                continue;
            };
            let id: [u8; 16] = crate::decode_hex(stem)?
                .try_into()
                .map_err(|_| "invalid custody request ID")?;
            if read_private(&s.journal.path(&id, "class"), 1)? != [class as u8]
                || s.journal.path(&id, "dispatch").exists()
            {
                continue;
            }
            // Recovery access must have been committed before request custody.
            read_private(&s.journal.path(&id, "recovery"), 32)?;
            let body = read_private(&path, MAX_ENVELOPE)?;
            s.journal.claim(&id, &body)?;
            s.active.insert(id);
            job = Some((id, body));
            break;
        }
        job
    };
    let Some((id, body)) = job else {
        return Ok(false);
    };
    let result = match transport::catalog_enabled(config)
        .and_then(|c| transport::public_envelope(&body, config, c).map_err(str::to_owned))
    {
        Err(e) => outcome(2, e.as_bytes()),
        Ok(()) => match transport::exchange_unix(target, &body) {
            Ok(v) if v.len() <= max_reply => outcome(0, &v),
            _ => outcome(1, UNCERTAIN),
        },
    };
    let mut s = state.lock().map_err(|_| "native custody state poisoned")?;
    let saved = s.journal.finish(&id, &result);
    s.active.remove(&id);
    saved?;
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::net::UnixListener;
    use std::time::{Duration, Instant};
    fn scratch() -> PathBuf {
        let p = std::env::temp_dir().join(format!(
            "mini-async-{}",
            crate::hex(&super::super::random::<16>().unwrap())
        ));
        directory(&p).unwrap();
        p
    }
    fn body() -> Vec<u8> {
        [vec![1, 2, 0, 0, 0], b"{}".to_vec(), vec![12]].concat()
    }
    fn ready(g: &AsyncDispatch, class: usize, id: [u8; 16], access: &[u8; 32]) -> Vec<u8> {
        let until = Instant::now() + Duration::from_secs(3);
        loop {
            if let DispatchState::Ready(v) = g
                .fetch(class, id, &Sha256::digest(body()).into(), access)
                .unwrap()
            {
                return v;
            }
            assert!(
                Instant::now() < until,
                "bounded native receiving did not complete"
            );
            std::thread::yield_now();
        }
    }
    #[test]
    fn async_custody_does_not_wait_for_native_work_and_reserves_repair_worker() {
        let root = scratch();
        let target = root.join("backend.sock");
        let listener = UnixListener::bind(&target).unwrap();
        let (started, observed) = mpsc::channel();
        let (release, held) = mpsc::channel();
        let fake = std::thread::spawn(move || {
            let (mut application, _) = listener.accept().unwrap();
            assert_eq!(
                transport::read_frame(&mut application).unwrap().unwrap(),
                body()
            );
            started.send(()).unwrap();
            let (mut repair, _) = listener.accept().unwrap();
            assert_eq!(transport::read_frame(&mut repair).unwrap().unwrap(), body());
            transport::write_frame(&mut repair, b"\x0cnative-repair-reply").unwrap();
            held.recv().unwrap();
            transport::write_frame(&mut application, b"\x0cnative-application-reply").unwrap();
        });
        let gateway = AsyncDispatch::open(&root, &target, b"{}", 4, 32, 1024).unwrap();
        let id = [1; 16];
        let access = [7; 32];
        let digest = Sha256::digest(body()).into();
        assert_eq!(
            gateway.offer(0, id, &body(), &access).unwrap(),
            DispatchState::Accepted
        );
        observed.recv_timeout(Duration::from_secs(3)).unwrap();
        // The native request is held at a barrier. Offer/fetch still return now.
        assert_eq!(
            gateway.offer(0, id, &body(), &access).unwrap(),
            DispatchState::Accepted
        );
        assert_eq!(
            gateway.fetch(0, id, &digest, &access).unwrap(),
            DispatchState::Accepted
        );
        assert!(gateway.fetch(0, id, &digest, &[8; 32]).is_err());
        assert!(gateway.fetch(1, id, &digest, &access).is_err());
        assert!(gateway.fetch(0, id, &[0; 32], &access).is_err());
        assert_eq!(
            gateway.offer(2, [2; 16], &body(), &[9; 32]).unwrap(),
            DispatchState::Accepted
        );
        assert_eq!(
            ready(&gateway, 2, [2; 16], &[9; 32]),
            outcome(0, b"\x0cnative-repair-reply")
        );
        release.send(()).unwrap();
        fake.join().unwrap();
        let exact = ready(&gateway, 0, id, &access);
        assert_eq!(exact, outcome(0, b"\x0cnative-application-reply"));
        assert_eq!(
            gateway.offer(0, id, &body(), &access).unwrap(),
            DispatchState::Ready(exact)
        );
    }
    #[test]
    fn async_custody_capacity_counts_crash_reservations_before_access_publication() {
        let root = scratch();
        // Simulate three crashes after bounded class reservation but before
        // access/request publication. A restart must still account for them.
        for n in 1..=3 {
            persist(&root.join(format!("{}.class", crate::hex(&[n; 16]))), &[1]).unwrap();
        }
        let gateway =
            AsyncDispatch::open(&root, &root.join("absent.sock"), b"{}", 3, 12, 1024).unwrap();
        for n in 4..=12 {
            assert!(gateway.offer(1, [n; 16], &body(), &[9; 32]).is_err());
            assert!(!root
                .join(format!("{}.recovery", crate::hex(&[n; 16])))
                .exists());
            assert!(!root
                .join(format!("{}.class", crate::hex(&[n; 16])))
                .exists());
        }
        // An existing reservation can finish publication within its slot.
        assert_eq!(
            gateway.offer(1, [1; 16], &body(), &[9; 32]).unwrap(),
            DispatchState::Accepted
        );
        assert_eq!(
            fs::read_dir(&root)
                .unwrap()
                .filter_map(|e| e.ok())
                .filter(|e| e.file_name().to_string_lossy().ends_with(".class"))
                .count(),
            3
        );
        assert!(gateway.offer(2, [1; 16], &body(), &[9; 32]).is_err());
    }
    #[test]
    fn async_custody_restart_fences_claim_and_recovers_unclaimed_exact_work() {
        let root = scratch();
        let target = root.join("backend.sock");
        let listener = UnixListener::bind(&target).unwrap();
        let id = [4; 16];
        let fresh = [5; 16];
        let access = [6; 32];
        let mut journal = Journal::open(&root, 32).unwrap();
        for ticket in [id, fresh] {
            persist(&journal.path(&ticket, "recovery"), &access).unwrap();
            journal.admit(0, &ticket, &body()).unwrap();
        }
        journal.claim(&id, &body()).unwrap();
        drop(journal);
        let fake = std::thread::spawn(move || {
            let (mut s, _) = listener.accept().unwrap();
            assert_eq!(transport::read_frame(&mut s).unwrap().unwrap(), body());
            transport::write_frame(&mut s, b"\x0cexact-restored-reply").unwrap();
        });
        let gateway = AsyncDispatch::open(&root, &target, b"{}", 4, 32, 1024).unwrap();
        assert_eq!(
            gateway
                .fetch(0, id, &Sha256::digest(body()).into(), &access)
                .unwrap(),
            DispatchState::Uncertain
        );
        assert_eq!(
            gateway.offer(0, id, &body(), &access).unwrap(),
            DispatchState::Uncertain
        );
        assert_eq!(
            ready(&gateway, 0, fresh, &access),
            outcome(0, b"\x0cexact-restored-reply")
        );
        fake.join().unwrap();
        assert!(AsyncDispatch::open(&root, &target, b"{}", 4, 32, 1024).is_err());
        // A changed envelope or recovery capability cannot replace custody.
        let mut changed = body();
        changed.push(0);
        assert!(gateway.offer(0, id, &changed, &access).is_err());
        assert!(gateway.offer(0, id, &body(), &[9; 32]).is_err());
    }
}
