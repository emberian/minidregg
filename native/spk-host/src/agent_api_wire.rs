//! Fixed-controller transport for a future paid agent API dispatch.
//!
//! This is a byte/identity contract, not Mini admission. The server remains
//! disabled until event21's distinct source-owned reserve, permit, and fd3
//! fence are available. Human event11 frames can never satisfy this route.
#![allow(dead_code)]

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::io::{self, Read, Write};
use std::os::unix::net::UnixStream;
use std::time::{Duration, Instant};

pub(crate) const MAX_FRAME: usize = 262_144;
pub(crate) const MAX_REPLY_FRAME: usize = 1_048_576;
pub(crate) const MAX_BODY: usize = 65_536;
const TRANSFER_DEADLINE: Duration = Duration::from_secs(30);

fn refuse(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn canonical_decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn canonical_hex(value: &str) -> bool {
    value.len().is_multiple_of(2)
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn control_free(value: &str) -> bool {
    !value.bytes().any(|byte| {
        byte == 0
            || byte == b'\r'
            || byte == b'\n'
            || (byte < 0x20 && byte != b'\t')
            || byte == 0x7f
    })
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(crate) struct OrdinaryHeader {
    pub name: String,
    pub value: String,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(tag = "type", rename_all = "kebab-case", deny_unknown_fields)]
pub(crate) enum Request {
    Hello {
        protocol: String,
    },
    Dispatch {
        protocol: String,
        operation_id: String,
        method: String,
        path: String,
        query: String,
        headers: Vec<OrdinaryHeader>,
        body_hex: String,
    },
    Inspect {
        protocol: String,
        operation_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        binding_sha256: Option<String>,
    },
}

fn allowed_header(name: &str) -> bool {
    matches!(
        name,
        "cookie"
            | "accept"
            | "accept-encoding"
            | "content-type"
            | "user-agent"
            | "if-match"
            | "if-none-match"
            | "x-requested-with"
            | "x-csrftoken"
            | "x-csrf-token"
            | "oc-total-length"
            | "oc-chunk-size"
            | "x-oc-mtime"
            | "oc-fileid"
            | "oc-chunked"
            | "oc-checksum"
            | "oc-chunk-offset"
            | "oc-lazyops"
    )
}

impl Request {
    pub(crate) fn parse(bytes: &[u8]) -> io::Result<Self> {
        if bytes.is_empty() || bytes.len() > MAX_FRAME {
            return Err(refuse("agent API frame bound refused"));
        }
        let request: Self = serde_json::from_slice(bytes)?;
        let protocol = match &request {
            Self::Hello { protocol }
            | Self::Dispatch { protocol, .. }
            | Self::Inspect { protocol, .. } => protocol,
        };
        if protocol != "mini-spk-agent-api-v1" {
            return Err(refuse("agent API protocol refused"));
        }
        match &request {
            Self::Hello { .. } => {}
            Self::Inspect {
                operation_id,
                binding_sha256,
                ..
            } => {
                if !canonical_decimal(operation_id)
                    || binding_sha256.as_ref().is_some_and(|sha| {
                        sha.len() != 64
                            || !sha
                                .bytes()
                                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
                    })
                {
                    return Err(refuse("agent API inspection operation ID refused"));
                }
            }
            Self::Dispatch {
                operation_id,
                method,
                path,
                query,
                headers,
                body_hex,
                ..
            } => {
                if !canonical_decimal(operation_id)
                    || !matches!(
                        method.as_str(),
                        "GET" | "HEAD" | "POST" | "PUT" | "PATCH" | "DELETE"
                    )
                    || minidregg_signed_api_path::route("/", path).is_err()
                    || query.len() > 8192
                    || query.contains('#')
                    || !control_free(query)
                    || headers.len() > 128
                    || !canonical_hex(body_hex)
                    || body_hex.len() / 2 > MAX_BODY
                    || (matches!(method.as_str(), "GET" | "HEAD" | "DELETE")
                        && !body_hex.is_empty())
                {
                    return Err(refuse("agent API request bounds or syntax refused"));
                }
                for header in headers {
                    if !allowed_header(&header.name)
                        || header.name.len() > 128
                        || header.value.len() > 8192
                        || !control_free(&header.value)
                    {
                        return Err(refuse("agent API ordinary header refused"));
                    }
                }
            }
        }
        Ok(request)
    }
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct FixedBinding {
    pub protocol: String,
    pub app: String,
    pub app_generation: String,
    pub session: String,
    pub session_generation: String,
    pub subject: String,
    pub ticket: String,
    pub parent_task: String,
    pub parent_generation: String,
    pub purse_task: String,
    pub purse_generation: String,
    pub signed_api_path: String,
    pub host_unit: String,
    pub host_invocation: String,
}

impl FixedBinding {
    pub(crate) fn validate(&self) -> io::Result<()> {
        if self.protocol != "mini-spk-agent-binding-v1"
            || ![
                &self.app,
                &self.app_generation,
                &self.session,
                &self.session_generation,
                &self.subject,
                &self.ticket,
                &self.parent_task,
                &self.parent_generation,
                &self.purse_task,
                &self.purse_generation,
            ]
            .iter()
            .all(|value| canonical_decimal(value))
            || self.parent_task == self.purse_task
            || minidregg_signed_api_path::checked_prefix(&self.signed_api_path).is_err()
            || self.host_unit.is_empty()
            || self.host_unit.len() > 256
            || !control_free(&self.host_unit)
            || self.host_invocation.len() != 32
            || !canonical_hex(&self.host_invocation)
        {
            return Err(refuse("agent API fixed binding refused"));
        }
        Ok(())
    }

    /// A transport comparison key, not a Mini authority or a server signature.
    pub(crate) fn fingerprint(&self) -> io::Result<String> {
        self.validate()?;
        let mut digest = Sha256::new();
        digest.update(b"DREGG/SPK-AGENT-API-BINDING/v1\0");
        digest.update(serde_json::to_vec(self)?);
        Ok(digest
            .finalize()
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect())
    }
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(tag = "type", rename_all = "kebab-case", deny_unknown_fields)]
pub(crate) enum Reply {
    Binding {
        protocol: String,
        binding: Box<FixedBinding>,
        binding_sha256: String,
    },
    Http {
        protocol: String,
        operation_id: String,
        binding_sha256: String,
        status: u16,
        headers: Vec<OrdinaryHeader>,
        body_hex: String,
    },
    Refused {
        protocol: String,
        operation_id: String,
        binding_sha256: String,
        code: String,
    },
    Uncertain {
        protocol: String,
        operation_id: String,
        binding_sha256: String,
        phase: String,
    },
    Inspection {
        protocol: String,
        operation_id: String,
        binding_sha256: String,
        state: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        definite_reply_sha256: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        definite_reply_json_hex: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        retention_error: Option<String>,
    },
}

/// The caller owns SO_PEERCRED, socket inode/ACL, fixed binding comparison and
/// one-send journal. The wire reader has one absolute frame deadline; neither
/// a read timeout nor a disconnect is a native cancellation barrier.
pub(crate) fn read_frame(stream: &mut UnixStream) -> io::Result<Vec<u8>> {
    let deadline = Instant::now() + TRANSFER_DEADLINE;
    let mut length = [0u8; 4];
    read_exact_deadline(stream, &mut length, deadline)?;
    let size = u32::from_be_bytes(length) as usize;
    if size == 0 || size > MAX_FRAME {
        return Err(refuse("agent API frame length refused"));
    }
    let mut frame = vec![0u8; size];
    read_exact_deadline(stream, &mut frame, deadline)?;
    Ok(frame)
}

fn read_exact_deadline(
    stream: &mut UnixStream,
    bytes: &mut [u8],
    deadline: Instant,
) -> io::Result<()> {
    let mut position = 0;
    while position < bytes.len() {
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "agent API frame deadline",
            ));
        }
        stream.set_read_timeout(Some(remaining))?;
        let count = stream.read(&mut bytes[position..])?;
        if count == 0 {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "agent API frame EOF",
            ));
        }
        position += count;
    }
    Ok(())
}

pub(crate) fn write_frame(stream: &mut UnixStream, bytes: &[u8]) -> io::Result<()> {
    if bytes.is_empty() || bytes.len() > MAX_REPLY_FRAME {
        return Err(refuse("agent API response bound refused"));
    }
    let deadline = Instant::now() + TRANSFER_DEADLINE;
    for chunk in [((bytes.len() as u32).to_be_bytes()).as_slice(), bytes] {
        let mut position = 0;
        while position < chunk.len() {
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "agent API send deadline",
                ));
            }
            stream.set_write_timeout(Some(remaining))?;
            let count = stream.write(&chunk[position..])?;
            if count == 0 {
                return Err(io::Error::new(
                    io::ErrorKind::WriteZero,
                    "agent API write zero",
                ));
            }
            position += count;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn historical_inspect_requires_exact_lowercase_binding_pin() {
        let valid = format!(
            "{{\"type\":\"inspect\",\"protocol\":\"mini-spk-agent-api-v1\",\
             \"operation_id\":\"17\",\"binding_sha256\":\"{}\"}}",
            "a".repeat(64)
        );
        assert!(matches!(
            Request::parse(valid.as_bytes()),
            Ok(Request::Inspect { binding_sha256: Some(pin), .. }) if pin == "a".repeat(64)
        ));
        for bad in ["A".repeat(64), "a".repeat(63), "g".repeat(64)] {
            let changed = valid.replace(&"a".repeat(64), &bad);
            assert!(Request::parse(changed.as_bytes()).is_err());
        }
    }

    #[test]
    fn fixed_agent_wire_refuses_caller_subject_headers_and_alias_ids() {
        let valid = br#"{"type":"dispatch","protocol":"mini-spk-agent-api-v1","operation_id":"7","method":"POST","path":"info/refs","query":"service=git-receive-pack","headers":[{"name":"content-type","value":"application/x-git-receive-pack-request"}],"body_hex":"00"}"#;
        assert!(matches!(
            Request::parse(valid),
            Ok(Request::Dispatch { .. })
        ));
        let bad = [
            String::from_utf8(valid.to_vec())
                .unwrap()
                .replace("\"7\"", "\"07\""),
            String::from_utf8(valid.to_vec())
                .unwrap()
                .replace("content-type", "x-sandstorm-permissions"),
            String::from_utf8(valid.to_vec())
                .unwrap()
                .replace("info/refs", "/info/refs"),
            String::from_utf8(valid.to_vec())
                .unwrap()
                .replace("\"00\"", "\"GG\""),
        ];
        for request in bad {
            assert!(Request::parse(request.as_bytes()).is_err());
        }
        let root = String::from_utf8(valid.to_vec())
            .unwrap()
            .replace("\"info/refs\"", "\"\"");
        assert!(matches!(
            Request::parse(root.as_bytes()),
            Ok(Request::Dispatch { path, .. }) if path.is_empty()
        ));
    }

    #[test]
    fn binding_fingerprint_changes_with_session_and_invocation() {
        let binding = FixedBinding {
            protocol: "mini-spk-agent-binding-v1".into(),
            app: "8401".into(),
            app_generation: "2".into(),
            session: "8406".into(),
            session_generation: "1".into(),
            subject: "9".into(),
            ticket: "8501".into(),
            parent_task: "8601".into(),
            parent_generation: "3".into(),
            purse_task: "8701".into(),
            purse_generation: "4".into(),
            signed_api_path: "/repo.git/".into(),
            host_unit: "mini-spk-s0123456789abcdef-a8401-g2.service".into(),
            host_invocation: "a".repeat(32),
        };
        let first = binding.fingerprint().unwrap();
        let mut changed = binding.clone();
        changed.session = "8404".into();
        assert_ne!(first, changed.fingerprint().unwrap());
        changed = binding.clone();
        changed.host_invocation = "b".repeat(32);
        assert_ne!(first, changed.fingerprint().unwrap());
        changed = binding.clone();
        changed.parent_task = "8602".into();
        assert_ne!(first, changed.fingerprint().unwrap());
        changed = binding.clone();
        changed.purse_task = "8702".into();
        assert_ne!(first, changed.fingerprint().unwrap());
        changed = binding.clone();
        changed.signed_api_path = "/other.git/".into();
        assert_ne!(first, changed.fingerprint().unwrap());
        changed = binding.clone();
        changed.purse_task = changed.parent_task.clone();
        assert!(changed.validate().is_err());
    }
}
