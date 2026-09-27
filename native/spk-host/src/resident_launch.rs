//! One resident operator supervisor starts the app child and retains fd3.
//! The source-owned lifecycle-v2 claim/descriptor adapter must construct the
//! exact `VerifiedBegin` and package command before calling this module.
#![allow(dead_code)] // Native lifecycle-v2 Host route is not linked yet.

use crate::hostd::{Journal, VerifiedBegin};
use crate::rpc_adapter::RpcDriver;
use crate::sandbox::{
    bwrap_args, directory_entry, inherited_fd, open_protected_directory, verify_executable,
    verify_var_volume, SandboxSpec,
};
use crate::spawn_gate::{AppFds, BoundedChild, SpawnSpec};
use crate::volume_custody::VolumeWitness;
use std::io;
use std::os::fd::{AsRawFd, OwnedFd};
use std::os::unix::net::UnixStream;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, reason)
}

/// Preopened file descriptors never appear in HTTP or Mini JSON. The app end
/// is duplicated to fd3 only inside the bounded, privilege-dropping gate.
pub(crate) struct PreparedResident {
    host_rpc: UnixStream,
    _child_rpc: OwnedFd,
    _image: OwnedFd,
    _persistent_var: OwnedFd,
    launch: SpawnSpec,
}

pub(crate) struct ResidentProcess {
    pub rpc: RpcDriver,
    child: BoundedChild,
}

impl ResidentProcess {
    pub(crate) fn child_pid(&self) -> u32 {
        self.child.pid()
    }

    /// A normal service shutdown drops the gate child, while systemd's exact
    /// unit cgroup closes any descendants. No HTTP request owns this process.
    pub(crate) fn wait(mut self) -> io::Result<i32> {
        self.child.wait()
    }
}

impl PreparedResident {
    pub(crate) fn prepare(
        spec: &SandboxSpec,
        app_uid: u32,
        app_gid: u32,
        bwrap_sha256: &str,
    ) -> io::Result<Self> {
        if app_uid == 0 || app_gid == 0 || unsafe { libc::geteuid() } == app_uid {
            return Err(invalid("resident supervisor must be separate from app UID"));
        }
        let args = bwrap_args(spec)?;
        let image = open_protected_directory(&spec.image_root, app_uid, false)?;
        let persistent_var = open_protected_directory(&spec.persistent_var, app_uid, true)?;
        if spec.persistent_var.starts_with(&spec.image_root)
            || spec.image_root.starts_with(&spec.persistent_var)
        {
            return Err(invalid("image and persistent /var overlap"));
        }
        for mountpoint in ["var", "tmp", "proc", "dev"] {
            directory_entry(image.as_raw_fd(), mountpoint)?;
        }
        verify_var_volume(
            &spec.persistent_var,
            persistent_var.as_raw_fd(),
            spec.persistent_var_max_bytes,
            app_uid,
        )?;
        verify_executable(&spec.bwrap, app_uid)?;

        let (host_rpc, child_rpc) = UnixStream::pair()?;
        let child_rpc = inherited_fd(child_rpc.as_raw_fd())?;
        let image = inherited_fd(image.as_raw_fd())?;
        let persistent_var = inherited_fd(persistent_var.as_raw_fd())?;
        let launch = SpawnSpec {
            program: spec.bwrap.clone(),
            sha256: bwrap_sha256.to_owned(),
            args,
            env: Vec::new(),
            app_uid,
            app_gid,
            fds: Some(AppFds {
                rpc: child_rpc.as_raw_fd(),
                image: image.as_raw_fd(),
                persistent_var: persistent_var.as_raw_fd(),
            }),
        };
        Ok(Self {
            host_rpc,
            _child_rpc: child_rpc,
            _image: image,
            _persistent_var: persistent_var,
            launch,
        })
    }

    /// Compare the root-owned custody handoff with the exact directory held
    /// open for fd5. This is a physical observation; the caller must also
    /// compare the witness bytes and volume ID to the source-owned v3 claim.
    pub(crate) fn compare_attested_volume(&self, witness: &VolumeWitness) -> io::Result<()> {
        witness.compare_open_mount(self._persistent_var.as_raw_fd())?;
        witness.recheck_handoff()
    }

    /// Repeat the fixed handoff/FD5 check at the last physical boundary before
    /// consuming the journal's one-shot spawn. This does not mint Mini launch
    /// authority or promise cancellation of a later operator mount change.
    pub(crate) fn start_attested(
        self,
        journal: &Journal,
        begin: &VerifiedBegin,
        witness: &VolumeWitness,
    ) -> io::Result<ResidentProcess> {
        self.compare_attested_volume(witness)?;
        self.start(journal, begin)
    }

    /// Must execute as the exact unit MainPID after native COMMITTED/v2 claim
    /// and signed package identity were independently matched. A source
    /// refusal or RPC setup failure never starts a second app generation.
    pub(crate) fn start(
        self,
        journal: &Journal,
        begin: &VerifiedBegin,
    ) -> io::Result<ResidentProcess> {
        let child = journal.enter_and_spawn(begin, &self.launch)?;
        let rpc = RpcDriver::from_connected_stream(begin.app, begin.generation, self.host_rpc)?;
        Ok(ResidentProcess { rpc, child })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resident_refuses_app_uid_equal_to_operator_before_opening_paths() {
        let spec = SandboxSpec {
            bwrap: "/missing/bwrap".into(),
            image_root: "/missing/image".into(),
            persistent_var: "/missing/var".into(),
            persistent_var_max_bytes: 1024,
            argv: vec!["/bin/true".into()],
            environ: vec![],
        };
        assert!(PreparedResident::prepare(
            &spec,
            unsafe { libc::geteuid() },
            unsafe { libc::getegid() },
            &"0".repeat(64),
        )
        .is_err());
    }
}
