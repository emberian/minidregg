//! Physical capacity, never Mini authorization or a second payment ledger.
pub mod core;
pub mod service;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::io::{Read, Write};
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::time::Duration;

pub const MAX_FRAME: usize = 65_536;
pub type Result<T> = std::result::Result<T, String>;

pub fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "command", rename_all = "kebab-case", deny_unknown_fields)]
pub enum Command {
    Status {
        after: Option<String>,
        limit: u16,
    },
    StatusGroups {
        after: Option<String>,
    },
    Drain {
        enabled: bool,
    },
    Enqueue {
        controller: String,
        job: core::Request,
    },
    Inspect {
        controller: String,
        id: String,
    },
    Dispatch {
        controller: String,
        id: String,
        lease: u64,
        attempt: String,
    },
    Finish {
        controller: String,
        id: String,
        lease: u64,
        outcome: core::Outcome,
    },
    Cancel {
        controller: String,
        id: String,
    },
}

impl Command {
    pub fn controller(&self) -> Option<&str> {
        match self {
            Self::Enqueue { controller, .. }
            | Self::Inspect { controller, .. }
            | Self::Dispatch { controller, .. }
            | Self::Finish { controller, .. }
            | Self::Cancel { controller, .. } => Some(controller),
            Self::Status { .. } | Self::StatusGroups { .. } | Self::Drain { .. } => None,
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "kebab-case", deny_unknown_fields)]
pub enum Reply {
    Status { status: Box<service::Status> },
    Job { job: Box<core::Job> },
    Refused { reason: String },
}

pub fn request(path: &Path, command: &Command) -> Result<core::Job> {
    let mut socket = UnixStream::connect(path).map_err(|e| format!("scheduler connect: {e}"))?;
    socket
        .set_read_timeout(Some(Duration::from_secs(5)))
        .map_err(|e| e.to_string())?;
    socket
        .set_write_timeout(Some(Duration::from_secs(5)))
        .map_err(|e| e.to_string())?;
    write_frame(&mut socket, command)?;
    match read_frame(&mut socket)? {
        Reply::Job { job } => Ok(*job),
        Reply::Refused { reason } => Err(format!("scheduler refused: {reason}")),
        Reply::Status { .. } => Err("scheduler returned status for a job request".into()),
    }
}

pub fn write_frame<T: Serialize>(socket: &mut (impl Write + ?Sized), value: &T) -> Result<()> {
    let bytes = serde_json::to_vec(value).map_err(|e| e.to_string())?;
    if bytes.len() > MAX_FRAME {
        return Err("scheduler frame exceeds bound".into());
    }
    socket
        .write_all(&(bytes.len() as u32).to_be_bytes())
        .map_err(|e| e.to_string())?;
    socket.write_all(&bytes).map_err(|e| e.to_string())
}

pub fn read_frame<T: for<'de> Deserialize<'de>>(socket: &mut (impl Read + ?Sized)) -> Result<T> {
    let mut length = [0u8; 4];
    socket.read_exact(&mut length).map_err(|e| e.to_string())?;
    let length = u32::from_be_bytes(length) as usize;
    if length > MAX_FRAME {
        return Err("scheduler frame exceeds bound".into());
    }
    let mut bytes = vec![0; length];
    socket.read_exact(&mut bytes).map_err(|e| e.to_string())?;
    serde_json::from_slice(&bytes).map_err(|e| format!("scheduler frame: {e}"))
}

/// Private operator control. It uses the same broker; there is no second manager.
pub fn operate(path: &Path, command: &Command) -> Result<service::Status> {
    let mut socket = UnixStream::connect(path).map_err(|e| format!("scheduler connect: {e}"))?;
    socket
        .set_read_timeout(Some(Duration::from_secs(5)))
        .map_err(|e| e.to_string())?;
    socket
        .set_write_timeout(Some(Duration::from_secs(5)))
        .map_err(|e| e.to_string())?;
    write_frame(&mut socket, command)?;
    match read_frame(&mut socket)? {
        Reply::Status { status } => Ok(*status),
        Reply::Refused { reason } => Err(format!("scheduler refused: {reason}")),
        Reply::Job { .. } => Err("scheduler returned job for an operator request".into()),
    }
}
