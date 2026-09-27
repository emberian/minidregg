//! Versioned controller transport for lifetime agent dispatch. These bytes are
//! not a Mini permit; only a fresh installed op76 callback can open fd3.
#![allow(dead_code)] // Shared resident v3 listener is wired in a later source cut.

use crate::agent_api_lifetime_v3::LifetimeBinding;
use serde::{Deserialize, Serialize};
use std::io;

pub(crate) const PROTOCOL: &str = "mini-spk-agent-api-v3";
pub(crate) const MAX_FRAME: usize = 262_144;
pub(crate) const MAX_REPLY_FRAME: usize = 1_048_576;
const MAX_BODY: usize = 65_536;

fn refused(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn hex(value: &str) -> bool {
    value.len().is_multiple_of(2)
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn sha256(value: &str) -> bool {
    value.len() == 64 && hex(value)
}

fn control_free(value: &str) -> bool {
    !value
        .bytes()
        .any(|byte| byte == 0 || byte == b'\r' || byte == b'\n' || byte < 0x20 || byte == 0x7f)
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

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(crate) struct OrdinaryHeader {
    pub name: String,
    pub value: String,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(tag = "type", rename_all = "kebab-case", deny_unknown_fields)]
pub(crate) enum Request {
    HelloV3 {
        protocol: String,
    },
    DispatchV3 {
        protocol: String,
        #[serde(rename = "operationId")]
        operation_id: String,
        #[serde(rename = "bindingSha256")]
        binding_sha256: String,
        method: String,
        path: String,
        query: String,
        headers: Vec<OrdinaryHeader>,
        #[serde(rename = "bodyHex")]
        body_hex: String,
    },
    InspectV3 {
        protocol: String,
        #[serde(rename = "operationId")]
        operation_id: String,
        #[serde(rename = "bindingSha256")]
        binding_sha256: String,
        #[serde(rename = "operationFingerprint", default)]
        operation_fingerprint: Option<String>,
    },
}

impl Request {
    pub(crate) fn parse(bytes: &[u8]) -> io::Result<Self> {
        if bytes.is_empty() || bytes.len() > MAX_FRAME {
            return Err(refused("lifetime agent frame bound refused"));
        }
        let request: Self = serde_json::from_slice(bytes)?;
        let protocol = match &request {
            Self::HelloV3 { protocol }
            | Self::DispatchV3 { protocol, .. }
            | Self::InspectV3 { protocol, .. } => protocol,
        };
        if protocol != PROTOCOL {
            return Err(refused("lifetime agent protocol refused"));
        }
        match &request {
            Self::HelloV3 { .. } => {}
            Self::InspectV3 {
                operation_id,
                binding_sha256,
                operation_fingerprint,
                ..
            } => {
                if !decimal(operation_id)
                    || !sha256(binding_sha256)
                    || operation_fingerprint
                        .as_ref()
                        .is_some_and(|value| !sha256(value))
                {
                    return Err(refused("lifetime inspection coordinate refused"));
                }
            }
            Self::DispatchV3 {
                operation_id,
                binding_sha256,
                method,
                path,
                query,
                headers,
                body_hex,
                ..
            } => {
                if !decimal(operation_id)
                    || !sha256(binding_sha256)
                    || !matches!(
                        method.as_str(),
                        "GET" | "HEAD" | "POST" | "PUT" | "PATCH" | "DELETE"
                    )
                    || path.len() > 8192
                    || path.starts_with('/')
                    || path.contains(['?', '#'])
                    || !control_free(path)
                    || query.len() > 8192
                    || !control_free(query)
                    || headers.len() > 128
                    || !hex(body_hex)
                    || body_hex.len() / 2 > MAX_BODY
                    || (matches!(method.as_str(), "GET" | "HEAD" | "DELETE")
                        && !body_hex.is_empty())
                {
                    return Err(refused("lifetime HTTP request refused"));
                }
                for header in headers {
                    if !allowed_header(&header.name)
                        || header.name.len() > 128
                        || header.value.len() > 8192
                        || !control_free(&header.value)
                    {
                        return Err(refused("lifetime ordinary header refused"));
                    }
                }
            }
        }
        Ok(request)
    }
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(tag = "type", rename_all = "kebab-case", deny_unknown_fields)]
pub(crate) enum Reply {
    BindingV3 {
        protocol: String,
        binding: Box<LifetimeBinding>,
        #[serde(rename = "bindingSha256")]
        binding_sha256: String,
    },
    HttpV3 {
        protocol: String,
        #[serde(rename = "operationId")]
        operation_id: String,
        #[serde(rename = "bindingSha256")]
        binding_sha256: String,
        #[serde(rename = "operationFingerprint")]
        operation_fingerprint: String,
        status: u16,
        headers: Vec<OrdinaryHeader>,
        #[serde(rename = "bodyHex")]
        body_hex: String,
    },
    RefusedV3 {
        protocol: String,
        #[serde(rename = "operationId")]
        operation_id: String,
        #[serde(rename = "bindingSha256")]
        binding_sha256: String,
        #[serde(
            rename = "operationFingerprint",
            skip_serializing_if = "Option::is_none"
        )]
        operation_fingerprint: Option<String>,
        code: String,
    },
    UncertainV3 {
        protocol: String,
        #[serde(rename = "operationId")]
        operation_id: String,
        #[serde(rename = "bindingSha256")]
        binding_sha256: String,
        #[serde(rename = "operationFingerprint")]
        operation_fingerprint: String,
        phase: String,
    },
    InspectionV3 {
        protocol: String,
        #[serde(rename = "operationId")]
        operation_id: String,
        #[serde(rename = "bindingSha256")]
        binding_sha256: String,
        #[serde(
            rename = "operationFingerprint",
            skip_serializing_if = "Option::is_none"
        )]
        operation_fingerprint: Option<String>,
        state: String,
        #[serde(
            rename = "definiteReplySha256",
            skip_serializing_if = "Option::is_none"
        )]
        definite_reply_sha256: Option<String>,
        #[serde(
            rename = "definiteReplyJsonHex",
            skip_serializing_if = "Option::is_none"
        )]
        definite_reply_json_hex: Option<String>,
        #[serde(rename = "retentionError", skip_serializing_if = "Option::is_none")]
        retention_error: Option<String>,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn v3_forward_is_finite_and_does_not_accept_current_transport_claims() {
        let dispatch = json!({
            "type":"dispatch-v3", "protocol":PROTOCOL,
            "operationId":"9", "bindingSha256":"a".repeat(64),
            "method":"POST", "path":"git-receive-pack", "query":"",
            "headers":[], "bodyHex":"abcd",
        });
        assert!(Request::parse(&serde_json::to_vec(&dispatch).unwrap()).is_ok());
        let mut extra = dispatch.clone();
        extra["currentClaims"] = json!({});
        assert!(Request::parse(&serde_json::to_vec(&extra).unwrap()).is_err());
        let mut old = dispatch.clone();
        old["protocol"] = json!("mini-spk-agent-api-v1");
        assert!(Request::parse(&serde_json::to_vec(&old).unwrap()).is_err());
        let mut wrong = dispatch.clone();
        wrong["bindingSha256"] = json!("A".repeat(64));
        assert!(Request::parse(&serde_json::to_vec(&wrong).unwrap()).is_err());
    }

    #[test]
    fn pre_reserve_refusal_and_post_reserve_uncertainty_have_distinct_fingerprints() {
        let refusal = Reply::RefusedV3 {
            protocol: PROTOCOL.into(),
            operation_id: "9".into(),
            binding_sha256: "a".repeat(64),
            operation_fingerprint: None,
            code: "no-dispatch".into(),
        };
        let encoded = serde_json::to_value(&refusal).unwrap();
        assert!(encoded.get("operationFingerprint").is_none());
        let uncertain = Reply::UncertainV3 {
            protocol: PROTOCOL.into(),
            operation_id: "9".into(),
            binding_sha256: "a".repeat(64),
            operation_fingerprint: "b".repeat(64),
            phase: "reserved".into(),
        };
        let encoded = serde_json::to_value(&uncertain).unwrap();
        assert_eq!(encoded["operationFingerprint"], "b".repeat(64));
    }
}
