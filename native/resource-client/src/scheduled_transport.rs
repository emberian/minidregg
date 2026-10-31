//! The native dispatch journal of the traffic-privacy research line (traffic stack 2:
//! `pq_mailbox.rs`, `cohort_tcp.rs`). One retained exact request per ticket, class quotas, and a
//! durable dispatch marker written BEFORE the native exchange, so an unknown outcome stays
//! `Uncertain` and is never dispatched twice; transport never invents a verdict. `dispatch_once`
//! sends one ticket through the same public envelope gate as the native byte proxy.
//!
//! Traffic stack 3 (`mini traffic`: the fixed-shape client/server facade over this journal, with
//! its local queue that re-dispatched a persisted request after a restart beside the caller's
//! fresh call, review §5.1 row 17) was deleted on 2026-10-26 (RUST-TRIAGE row 7).
use crate::transport;
use crate::Result;
use sha2::{Digest, Sha256};
use std::fs;
use std::path::{Path, PathBuf};

#[path = "async_dispatch.rs"]
mod async_dispatch;
pub(crate) use async_dispatch::{AsyncDispatch, DispatchState};

const MAX_ENVELOPE: usize = transport::CARRIED_LOOKUP_MAX_FRAME + transport::MAX_CONFIG + 38;
const UNCERTAIN: &[u8] = b"transport dispatch outcome uncertain; recover using native exact lookup";

fn retained_quotas(total: usize) -> [usize; 3] {
    [total / 2, total / 4, total - total / 2 - total / 4]
}
fn id_text(id: &[u8; 16]) -> String {
    crate::hex(id)
}
pub(crate) use crate::fsio::read_private;
pub(crate) fn persist(path: &Path, bytes: &[u8]) -> Result<()> {
    // Published only complete, never replacing a prior immutable
    // ticket/claim/reply. Crash-left staging files are never receipts.
    crate::create_private(path, bytes)
}
pub(crate) struct Journal {
    root: PathBuf,
    max: [usize; 3],
    count: [usize; 3],
}
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Admission {
    Fresh,
    Cached(Vec<u8>),
    Uncertain,
}
impl Journal {
    pub(crate) fn open(root: &Path, total: usize) -> Result<Self> {
        crate::fsio::ensure_private_dir_all(root)?;
        let max = retained_quotas(total);
        let mut count = [0; 3];
        for e in fs::read_dir(root).map_err(|e| e.to_string())? {
            let e = e.map_err(|e| e.to_string())?;
            let name = e.file_name().to_string_lossy().into_owned();
            if let Some(stem) = name.strip_suffix(".request") {
                let class = read_private(&root.join(format!("{stem}.class")), 1)?;
                if class.len() != 1 || class[0] >= 3 {
                    return Err("retained request missing immutable class; preserve old obligations before migration".into());
                }
                count[class[0] as usize] += 1;
            }
        }
        if (0..3).any(|i| count[i] > max[i]) {
            return Err("retained traffic obligations exceed class reservation".into());
        }
        Ok(Self {
            root: root.into(),
            max,
            count,
        })
    }
    fn path(&self, id: &[u8; 16], suffix: &str) -> PathBuf {
        self.root.join(format!("{}.{}", id_text(id), suffix))
    }
    pub(crate) fn admit(&mut self, class: usize, id: &[u8; 16], bytes: &[u8]) -> Result<Admission> {
        if class >= 3 || bytes.is_empty() || bytes.len() > MAX_ENVELOPE {
            return Err("native envelope exceeds traffic admission bound".into());
        }
        let request = self.path(id, "request");
        let class_path = self.path(id, "class");
        if request.exists() {
            if read_private(&request, MAX_ENVELOPE)? != bytes
                || read_private(&class_path, 1)? != [class as u8]
            {
                return Err("traffic ticket conflicts with retained exact envelope/class".into());
            }
        } else {
            if self.count[class] >= self.max[class] {
                return Err("traffic retained class capacity exhausted before dispatch".into());
            }
            if class_path.exists() {
                if read_private(&class_path, 1)? != [class as u8] {
                    return Err("traffic retained class conflict".into());
                }
            } else {
                persist(&class_path, &[class as u8])?;
            }
            persist(&request, bytes)?;
            self.count[class] += 1;
        }
        let reply = self.path(id, "reply");
        if reply.exists() {
            return Ok(Admission::Cached(read_private(&reply, MAX_ENVELOPE + 1)?));
        }
        if self.path(id, "dispatch").exists() {
            return Ok(Admission::Uncertain);
        }
        Ok(Admission::Fresh)
    }
    pub(crate) fn claim(&self, id: &[u8; 16], bytes: &[u8]) -> Result<()> {
        persist(&self.path(id, "dispatch"), &Sha256::digest(bytes))
    }
    pub(crate) fn finish(&self, id: &[u8; 16], bytes: &[u8]) -> Result<()> {
        persist(&self.path(id, "reply"), bytes)
    }
}

// A transport outcome is separate from the original Host frame. Code 0 is exact
// Host bytes, 1 is uncertain, 2 is pre-dispatch refusal. No proxy Pending verdict.
fn outcome(kind: u8, bytes: &[u8]) -> Vec<u8> {
    let mut out = vec![kind];
    out.extend_from_slice(bytes);
    out
}
/// Called under the mailbox's private service lock. Shares the original native
/// admission gate and dispatch journal, not an alternate authority surface.
pub(crate) fn dispatch_once(
    root: &Path,
    target: &Path,
    config: &[u8],
    class: usize,
    id: [u8; 16],
    body: &[u8],
    max_reply: usize,
) -> Result<Vec<u8>> {
    let mut j = Journal::open(root, 4096)?;
    match j.admit(class, &id, body)? {
        Admission::Cached(v) => return Ok(v),
        Admission::Uncertain => return Ok(outcome(1, UNCERTAIN)),
        Admission::Fresh => (),
    }
    j.claim(&id, body)?;
    let v = match transport::catalog_enabled(config)
        .and_then(|c| transport::public_envelope(body, config, c).map_err(str::to_owned))
    {
        Err(e) => outcome(2, e.as_bytes()),
        Ok(()) => match transport::exchange_unix(target, body) {
            Ok(v) if v.len() <= max_reply => outcome(0, &v),
            _ => outcome(1, UNCERTAIN),
        },
    };
    j.finish(&id, &v)?;
    Ok(v)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn scratch() -> PathBuf {
        let p = std::env::temp_dir().join(format!(
            "mini-traffic-{}-{}",
            std::process::id(),
            id_text(&crate::fsio::random().unwrap())
        ));
        crate::fsio::ensure_private_dir_all(&p).unwrap();
        p
    }
    #[test]
    fn application_retention_cannot_consume_control_or_recovery() {
        let root = scratch();
        let mut j = Journal::open(&root, 8).unwrap();
        for i in 0..4 {
            j.admit(0, &[i; 16], b"body").unwrap();
        }
        assert!(j.admit(0, &[9; 16], b"new").is_err());
        assert_eq!(j.admit(1, &[10; 16], b"control").unwrap(), Admission::Fresh);
        assert_eq!(
            j.admit(2, &[11; 16], b"recovery").unwrap(),
            Admission::Fresh
        );
        drop(j);
        Journal::open(&root, 8).unwrap();
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn durable_dispatch_marker_never_authorizes_second_effect() {
        let root = scratch();
        let id = [4; 16];
        let body = b"exact native signed ingress";
        let mut j = Journal::open(&root, 8).unwrap();
        assert_eq!(j.admit(0, &id, body).unwrap(), Admission::Fresh);
        j.claim(&id, body).unwrap();
        drop(j);
        let mut restored = Journal::open(&root, 8).unwrap();
        assert_eq!(restored.admit(0, &id, body).unwrap(), Admission::Uncertain);
        assert!(restored.admit(0, &id, b"changed body").is_err());
        let exact = outcome(0, b"exact native receipt");
        restored.finish(&id, &exact).unwrap();
        drop(restored);
        assert_eq!(
            Journal::open(&root, 8)
                .unwrap()
                .admit(0, &id, body)
                .unwrap(),
            Admission::Cached(exact)
        );
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn retention_pressure_never_erases_accepted_dispatch() {
        let root = scratch();
        let mut j = Journal::open(&root, 2).unwrap();
        let id = [1; 16];
        j.admit(0, &id, b"accepted").unwrap();
        j.claim(&id, b"accepted").unwrap();
        assert!(j.admit(0, &[2; 16], b"new").is_err());
        assert_eq!(j.admit(0, &id, b"accepted").unwrap(), Admission::Uncertain);
        fs::remove_dir_all(root).unwrap();
    }
}
