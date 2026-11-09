//! What wakes the publication hand-off (`Helper::collect`): a member's `workspace/proposals/` gaining
//! a proposal, or a proposal gaining its `recipient-reference.json` (`publish ID` writes it). On
//! Linux the helper holds one inotify descriptor over every member's `proposals/` directory and
//! each proposal directory in it, so a publication reaches the public reader the moment its
//! reference lands instead of at the next minute's sweep (demo-dry 2026-11-09: `/doc/welcome`
//! answered 404 for 40 s after the seed published it). The minute's sweep still runs: it adds
//! watches for members and proposals that appeared since, and it is the hand-off where inotify is
//! unavailable (macOS, the dev journey).

use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// A member's `workspace/` (until its `proposals/` exists), its `proposals/`, or one proposal.
#[derive(Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
enum Dir {
    Workspace,
    Proposals,
    Proposal,
}

#[cfg_attr(not(target_os = "linux"), allow(dead_code))]
pub struct Watch {
    #[cfg(target_os = "linux")]
    fd: Option<std::os::fd::OwnedFd>,
    /// Every watched directory, by watch descriptor, and what it is.
    watched: HashMap<i32, (PathBuf, Dir)>,
    paths: HashMap<PathBuf, i32>,
}

impl Watch {
    pub fn new() -> Self {
        #[cfg(target_os = "linux")]
        {
            use std::os::fd::FromRawFd;
            let raw = unsafe { libc::inotify_init1(libc::IN_NONBLOCK | libc::IN_CLOEXEC) };
            let fd = (raw >= 0).then(|| unsafe { std::os::fd::OwnedFd::from_raw_fd(raw) });
            Watch { fd, watched: HashMap::new(), paths: HashMap::new() }
        }
        #[cfg(not(target_os = "linux"))]
        Watch { watched: HashMap::new(), paths: HashMap::new() }
    }

    /// The descriptor to poll beside the listener, when there is one.
    pub fn raw_fd(&self) -> Option<i32> {
        #[cfg(target_os = "linux")]
        {
            use std::os::fd::AsRawFd;
            self.fd.as_ref().map(|fd| fd.as_raw_fd())
        }
        #[cfg(not(target_os = "linux"))]
        None
    }

    /// Watch each home's `workspace/proposals/` and every proposal directory in it (idempotent).
    pub fn cover(&mut self, homes: &[(String, PathBuf)]) {
        for (_, home) in homes {
            let proposals = home.join("workspace/proposals");
            if !proposals.is_dir() {
                self.add(&home.join("workspace"), Dir::Workspace);
                continue;
            }
            self.add(&proposals, Dir::Proposals);
            if let Ok(entries) = std::fs::read_dir(&proposals) {
                for e in entries.flatten() {
                    if e.file_type().is_ok_and(|t| t.is_dir()) {
                        self.add(&e.path(), Dir::Proposal);
                    }
                }
            }
        }
    }

    #[allow(unused_variables)]
    fn add(&mut self, dir: &Path, kind: Dir) {
        #[cfg(target_os = "linux")]
        {
            use std::os::fd::AsRawFd;
            use std::os::unix::ffi::OsStrExt;
            let Some(fd) = self.fd.as_ref() else { return };
            if self.paths.contains_key(dir) {
                return;
            }
            let Ok(c) = std::ffi::CString::new(dir.as_os_str().as_bytes()) else { return };
            let mask = libc::IN_ONLYDIR | libc::IN_CREATE | libc::IN_MOVED_TO | libc::IN_CLOSE_WRITE | libc::IN_DELETE_SELF;
            let wd = unsafe { libc::inotify_add_watch(fd.as_raw_fd(), c.as_ptr(), mask) };
            if wd >= 0 {
                self.watched.insert(wd, (dir.to_path_buf(), kind));
                self.paths.insert(dir.to_path_buf(), wd);
            }
        }
    }

    /// Drain pending events: true when any of them may be a publication (a new proposal is watched
    /// at once, so a reference written into it right after is seen too).
    pub fn changed(&mut self) -> bool {
        #[cfg(target_os = "linux")]
        {
            use std::os::fd::AsRawFd;
            let Some(raw) = self.fd.as_ref().map(|fd| fd.as_raw_fd()) else { return false };
            let mut any = false;
            let mut buf = [0u8; 8192];
            loop {
                let n = unsafe { libc::read(raw, buf.as_mut_ptr().cast(), buf.len()) };
                if n <= 0 {
                    break;
                }
                let mut at = 0usize;
                let head = std::mem::size_of::<libc::inotify_event>();
                while at + head <= n as usize {
                    let event: libc::inotify_event = unsafe { std::ptr::read_unaligned(buf.as_ptr().add(at).cast()) };
                    let name = &buf[at + head..at + head + event.len as usize];
                    let name = &name[..name.iter().position(|b| *b == 0).unwrap_or(name.len())];
                    at += head + event.len as usize;
                    any = true;
                    if event.mask & (libc::IN_DELETE_SELF | libc::IN_IGNORED) != 0 {
                        if let Some((dir, _)) = self.watched.remove(&event.wd) {
                            self.paths.remove(&dir);
                        }
                        continue;
                    }
                    let Some((dir, kind)) = self.watched.get(&event.wd).cloned() else { continue };
                    if event.mask & libc::IN_ISDIR != 0 && !name.is_empty() {
                        use std::os::unix::ffi::OsStrExt;
                        let child = dir.join(std::ffi::OsStr::from_bytes(name));
                        match kind {
                            Dir::Workspace if name == b"proposals" => self.add(&child, Dir::Proposals),
                            Dir::Proposals => self.add(&child, Dir::Proposal),
                            _ => {}
                        }
                    }
                }
            }
            any
        }
        #[cfg(not(target_os = "linux"))]
        false
    }
}

impl Default for Watch {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use super::*;

    #[test]
    fn a_reference_landing_in_a_proposal_made_after_the_cover_wakes_the_hand_off() {
        let home = std::env::temp_dir().join(format!("spawn-watch-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&home);
        std::fs::create_dir_all(home.join("workspace")).unwrap();
        let mut w = Watch::new();
        w.cover(&[("alice".into(), home.clone())]);
        assert!(!w.changed(), "nothing yet");
        // The first `delegate` makes proposals/ and the proposal; `publish` then writes the reference.
        std::fs::create_dir_all(home.join("workspace/proposals")).unwrap();
        assert!(w.changed());
        std::fs::create_dir(home.join("workspace/proposals/hp-1")).unwrap();
        assert!(w.changed());
        let tmp = home.join("workspace/proposals/hp-1/recipient-reference.json.tmp");
        std::fs::write(&tmp, b"{}").unwrap();
        std::fs::rename(&tmp, home.join("workspace/proposals/hp-1/recipient-reference.json")).unwrap();
        assert!(w.changed(), "the reference itself wakes it");
        assert!(!w.changed(), "drained");
        std::fs::remove_dir_all(&home).unwrap();
    }
}
