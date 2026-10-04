//! Bounded framing shared by the local socket and the Lean host's stdio service.
use sha2::{Digest, Sha256};
use std::fs;
use std::fs::OpenOptions;
use std::io::{self, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{FileTypeExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::mpsc;
use std::time::{Duration, Instant};

use crate::serve_queue::{self, fair_queue, TrySendError};

// Mirrors FnEvidenceCodec.maxHostFrameBytes; the host's length includes op byte.
pub(crate) const HOST_MAX_FRAME: usize = 12_102_760;
pub(crate) const MAX_CONFIG: usize = 65_536;
// Op153 wraps every formerly valid raw call without reducing its capacity.
pub(crate) const MAX_CARRIED_CALL: usize = HOST_MAX_FRAME - 1;
pub(crate) const CARRIED_LOOKUP_MAX_FRAME: usize = HOST_MAX_FRAME + 4 + 1024;
const MAX_FRAME: usize = CARRIED_LOOKUP_MAX_FRAME + 5 + MAX_CONFIG + 32;

fn request_within_bound(request: &[u8]) -> bool {
    match request {
        [153, payload @ ..] => carried_lookup_request(payload),
        _ => request.len() <= HOST_MAX_FRAME,
    }
}

/// The largest JSON source an author request (op 7) may carry. Measured
/// against the clients: the biggest legitimate sources are 4 MiB
/// (`current_birth::MAX_SOURCE` and `MAX_INTENT`, `workspace::studio::MAX_SOURCE`,
/// `hermes_handoff::LIMIT`); a 12 MB array of 5M elements cost the Host ~11 s and
/// 775 MB, so the 12 MB frame bound was the wrong bound for this operation.
pub(crate) const AUTHOR_JSON_MAX: usize = 4 * 1024 * 1024;
/// An author request is `u16 kind length ++ kind ++ JSON`; kinds are registry
/// names (the longest is under 64 bytes), so 256 bytes of kind is generous.
pub(crate) const AUTHOR_KIND_FRAME_MAX: usize = 2 + 256;
/// The whole op 7 body.
pub(crate) const AUTHOR_BODY_MAX: usize = AUTHOR_KIND_FRAME_MAX + AUTHOR_JSON_MAX;
/// An op 9 body is a JSON list of one to four Ed25519 signatures
/// (`Host.Json.signatures` refuses any other length): well under 1 KiB.
pub(crate) const SIGNATURES_BODY_MAX: usize = 16 * 1024;
/// Ops 0 (describe) and 6 (profile) take no payload; the Host refuses one.
pub(crate) const NO_BODY_OPS: [u8; 2] = [0, 6];

/// How long the Host may take to answer a state-touching request before the
/// service gives up on it, kills the Host and reports the status uncertain.
pub(crate) const HOST_STATE_OP_BUDGET: Duration = Duration::from_secs(600);
/// The pure, source-owned operations (describe, profile, author, inspect,
/// signatures, observe-assemble, assemble) read no Store and commit nothing.
/// The slowest measured, a 12 MB op 7 array, took ~11 s; with op 7 now bounded
/// at 4 MiB this is more than ten times the worst case. A pure request that
/// outlives it costs the service one Host restart and the caller an uncertain
/// status about a request that could not have changed anything.
pub(crate) const HOST_PURE_OP_BUDGET: Duration = Duration::from_secs(120);

/// The Host-time budget for one request, by its operation byte.
pub(crate) fn host_budget(request: &[u8]) -> Duration {
    match request.first() {
        Some(0 | 6..=11) => HOST_PURE_OP_BUDGET,
        _ => HOST_STATE_OP_BUDGET,
    }
}

/// The named refusal for a request whose body exceeds its own operation's
/// bound, judged before the Host sees a byte of it. `None` is not an
/// approval: `request_within_bound` and `allowed_operation` still judge it.
pub(crate) fn operation_body_refusal(request: &[u8]) -> Option<&'static str> {
    match request {
        [operation, _, ..] if NO_BODY_OPS.contains(operation) => {
            Some("operation takes no request body")
        }
        [7, body @ ..] if body.len() > AUTHOR_BODY_MAX => {
            Some("author request body exceeds its bound")
        }
        [9, body @ ..] if body.len() > SIGNATURES_BODY_MAX => {
            Some("signatures request body exceeds its bound")
        }
        _ => None,
    }
}

pub(crate) fn host_image_sha256(path: &Path) -> Result<[u8; 32], String> {
    let mut file = fs::File::open(path)
        .map_err(|e| format!("cannot open host image {}: {e}", path.display()))?;
    let mut hash = Sha256::new();
    let mut chunk = [0u8; 64 * 1024];
    loop {
        let count = file
            .read(&mut chunk)
            .map_err(|e| format!("cannot hash host image {}: {e}", path.display()))?;
        if count == 0 {
            return Ok(hash.finalize().into());
        }
        hash.update(&chunk[..count]);
    }
}

fn parse_host_sha256(value: &str) -> Result<[u8; 32], String> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err("expected host SHA-256 must be 64 lowercase hex digits".to_owned());
    }
    let mut bytes = [0u8; 32];
    for (index, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[2 * index..2 * index + 2], 16)
            .map_err(|_| "invalid expected host SHA-256")?;
    }
    Ok(bytes)
}

/// Where a client's Host requests go. Every socket argument, workspace pin and
/// attempt manifest carries one address: an absolute path names the
/// deployment's unix socket; `ssh:DEST` names the byte proxy reached by
/// `ssh -T DEST` (`mini socket-proxy` on the far side), whose stdio carries
/// exactly the frames the unix socket would, one reply per request.
pub(crate) enum Endpoint<'a> {
    Unix(&'a Path),
    Remote(&'a str),
}

pub(crate) const REMOTE_PREFIX: &str = "ssh:";

/// An ssh destination as `ssh` itself takes it (`user@host`, or a Host alias
/// from the caller's ssh config). It is passed after `--`, so it can never be
/// read as an ssh option; ports and identities belong in the ssh config.
pub(crate) fn remote_destination(destination: &str) -> Result<(), String> {
    if destination.is_empty()
        || destination.len() > 255
        || destination.starts_with('-')
        || !destination
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b'-' | b'@' | b'%' | b'+'))
    {
        return Err("--remote takes one ssh destination: user@host or an ssh config Host alias".into());
    }
    Ok(())
}

pub(crate) fn remote_address(destination: &str) -> Result<std::path::PathBuf, String> {
    remote_destination(destination)?;
    Ok(format!("{REMOTE_PREFIX}{destination}").into())
}

pub(crate) fn endpoint(address: &Path) -> Result<Endpoint<'_>, String> {
    match address.to_str().and_then(|text| text.strip_prefix(REMOTE_PREFIX)) {
        Some(destination) => {
            remote_destination(destination)?;
            Ok(Endpoint::Remote(destination))
        }
        None => Ok(Endpoint::Unix(address)),
    }
}

pub(crate) fn is_remote(address: &Path) -> bool {
    matches!(endpoint(address), Ok(Endpoint::Remote(_)))
}

/// The form a workspace or attempt manifest pins: a remote address verbatim,
/// a unix socket as an absolute path.
pub(crate) fn pinned_address(address: &Path) -> Result<String, String> {
    match endpoint(address)? {
        Endpoint::Remote(destination) => Ok(format!("{REMOTE_PREFIX}{destination}")),
        Endpoint::Unix(path) => {
            let path = if path.is_absolute() {
                path.to_path_buf()
            } else {
                std::env::current_dir()
                    .map_err(|error| format!("cannot resolve {}: {error}", path.display()))?
                    .join(path)
            };
            path.to_str()
                .map(str::to_owned)
                .ok_or_else(|| format!("socket path is not valid UTF-8: {}", path.display()))
        }
    }
}

/// Splits a socket envelope after its config pin: the Host-image pin a
/// version-2 envelope carries, and the request that follows.
fn split_envelope<'a>(
    envelope: &'a [u8],
    config: &[u8],
) -> Result<(Option<&'a [u8]>, &'a [u8]), &'static str> {
    if envelope.len() < 5 || !matches!(envelope[0], 1 | 2) {
        return Err("invalid socket envelope");
    }
    let config_length = u32::from_le_bytes(envelope[1..5].try_into().unwrap()) as usize;
    let config_end = config_length
        .checked_add(5)
        .ok_or("invalid socket envelope")?;
    if config_length != config.len() || envelope.get(5..config_end) != Some(config) {
        return Err("config pin mismatch");
    }
    let (pin, request_start) = if envelope[0] == 2 {
        let sha_end = config_end
            .checked_add(32)
            .ok_or("invalid socket envelope")?;
        (
            Some(envelope.get(config_end..sha_end).ok_or("invalid socket envelope")?),
            sha_end,
        )
    } else {
        (None, config_end)
    };
    let request = envelope
        .get(request_start..)
        .ok_or("invalid socket envelope")?;
    if request.is_empty() {
        return Err("invalid socket envelope");
    }
    Ok((pin, request))
}

fn request_from_envelope<'a>(
    envelope: &'a [u8],
    config: &[u8],
    host_sha256: &[u8; 32],
) -> Result<&'a [u8], &'static str> {
    let (pin, request) = split_envelope(envelope, config)?;
    if pin.is_some_and(|pin| pin != host_sha256.as_slice()) {
        return Err("host image pin mismatch");
    }
    Ok(request)
}

/// What the byte proxy checks before a frame may reach the public socket: the
/// envelope names the deployment's pinned config, and its request is an
/// operation the public socket serves. The Host image pin and everything
/// inside the request are the socket's and the Host's to judge.
pub(crate) fn public_envelope(
    envelope: &[u8],
    config: &[u8],
    catalog_enabled: bool,
) -> Result<(), &'static str> {
    let (_, request) = split_envelope(envelope, config)?;
    if !request_within_bound(request) {
        return Err("host frame exceeds bound");
    }
    if let Some(reason) = operation_body_refusal(request) {
        return Err(reason);
    }
    if !allowed_operation(request, catalog_enabled) {
        return Err("operation unavailable on selected socket");
    }
    Ok(())
}

pub(crate) fn catalog_enabled(config: &[u8]) -> Result<bool, String> {
    Ok(serde_json::from_slice::<serde_json::Value>(config)
        .map_err(|e| format!("invalid operator config JSON: {e}"))?
        .get("fnReplyCatalog")
        .is_some_and(serde_json::Value::is_object))
}

// Continuity carries points and optional authenticated Merkle siblings, never local paths.
// Lean owns the shape and proof semantics; the socket bounds JSON before dispatch.
fn continuity_request(payload: &[u8]) -> bool {
    !payload.is_empty() && payload.len() <= 64 * 1024
        && serde_json::from_slice::<serde_json::Value>(payload).is_ok_and(|value| value.is_object())
}

// API17's source producer carries a legacy reserve pair or a v2 reserve pair
// plus an optional exact fence pair. Only framing is judged here; the native
// Host still authenticates both receipts and their history.
fn provider_continuity_request(payload: &[u8]) -> bool {
    if payload.is_empty() || payload.len() >= HOST_MAX_FRAME {
        return false;
    }
    let receipt_pair = |bytes: &[u8]| exact_pair(bytes).is_some_and(|(call, outcome)| {
        !call.is_empty() && call.len() < HOST_MAX_FRAME && !outcome.is_empty() && outcome.len() <= 1024
    });
    let v2_body = |body: &[u8]| {
        let Some(prefix) = body.get(..4) else { return false; };
        let length = u32::from_le_bytes(prefix.try_into().expect("four-byte prefix")) as usize;
        let Some(end) = length.checked_add(4).filter(|end| *end <= body.len()) else { return false; };
        let reserve = &body[4..end];
        let fence = &body[end..];
        receipt_pair(reserve) && (fence.is_empty() || receipt_pair(fence))
    };
    if let Some(body) = payload.strip_prefix(crate::provider_continuity::V2) {
        v2_body(body)
    } else if let Some(body) = payload.strip_prefix(crate::provider_continuity::V3) {
        exact_pair(body).is_some_and(|(receipts, point)| {
            v2_body(receipts) && exact_pair(point).is_some_and(|(count, root)| {
                let natural = |digits: &[u8]| !digits.is_empty() && digits.len() <= 80
                    && digits.iter().all(u8::is_ascii_digit)
                    && (digits.len() == 1 || digits[0] != b'0');
                natural(count) && count != b"0" && natural(root)
            })
        })
    } else {
        receipt_pair(payload)
    }
}

// Public, read-only carried SignedCall lookup: bounded JSON header and raw call.
fn carried_lookup_request(payload: &[u8]) -> bool {
    if payload.len() < 6 || payload.len() >= CARRIED_LOOKUP_MAX_FRAME {
        return false;
    }
    let length = u32::from_le_bytes(payload[..4].try_into().unwrap()) as usize;
    if length == 0
        || length > 1024
        || length >= payload.len() - 4
        || payload.len() - 4 - length > MAX_CARRIED_CALL
    {
        return false;
    }
    serde_json::from_slice::<serde_json::Value>(&payload[4..4 + length]).is_ok_and(|value| {
        value["algorithm"] == "minidregg-carried-call-lookup-v1"
            && value["originIdentity"].is_object()
    })
}

pub(crate) fn allowed_operation(request: &[u8], catalog_enabled: bool) -> bool {
    match request {
        // Explicit reserve birth methods carry canonical signed source/owner requests.
        // Host verifies the exact descriptor and current authority independently.
        [201 | 202, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        // Source-owned enrollment quote and exact paid claim status/quote. Host validates fields;
        // ingress only bounds the JSON object before any backend exchange.
        [121 | 181 | 182, payload @ ..] => !payload.is_empty() && payload.len() <= 4096
            && serde_json::from_slice::<serde_json::Value>(payload).is_ok_and(|value| value.is_object()),
        // Closed public claim prepare, detached assembly, submit and exact
        // lookup. Canonical command/ingress admission remains source-owned.
        [183, command @ ..] => !command.is_empty() && command.len() <= 2048,
        [184, pair @ ..] if pair.len() <= 4096 => exact_pair(pair).is_some_and(
            |(plan, signature)| !plan.is_empty() && plan.len() <= 3072 && signature.len() == 64,
        ),
        [185 | 186, ingress @ ..] => !ingress.is_empty() && ingress.len() <= 4096,
        [151, payload @ ..] => continuity_request(payload),
        [153, payload @ ..] => carried_lookup_request(payload),
        [0..=11, ..] => true,
        // Realm wells (K-WELL): plan, detached assembly, submit.
        [123..=125, _, ..] => true,
        // NOCK K-NOCK-CELL / K-RAN: read-only program check / show / sample /
        // run dry run (134 reads no target cell: values are the caller's);
        // N11: NockApp door poke dry run / peek / state (135-137, same rule).
        // Renumbered from 117-123 at the final merge (pay holds 117-120).
        [131..=137, ..] => true,
        [12 | 14] => true,
        [13 | 15, digits @ ..] => {
            !digits.is_empty()
                && digits.len() <= 80
                && digits.iter().all(u8::is_ascii_digit)
                && (digits.len() == 1 || digits[0] != b'0')
        }
        [16, carrier @ ..] => catalog_enabled && !carrier.is_empty() && carrier.len() <= 1_516_384,
        [17, payload @ ..] => provider_continuity_request(payload),
        [18, digits @ ..] => {
            catalog_enabled
                && !digits.is_empty()
                && digits.len() <= 80
                && digits.iter().all(u8::is_ascii_digit)
                && (digits.len() == 1 || digits[0] != b'0')
        }
        [19, payload @ ..] if payload.len() >= 10 => {
            let metadata_length = u32::from_le_bytes(payload[..4].try_into().unwrap()) as usize;
            if metadata_length == 0 || metadata_length > 4096 || payload.len() < metadata_length + 9
            {
                return false;
            }
            let request_prefix = metadata_length + 4;
            let request_length = u32::from_le_bytes(
                payload[request_prefix..request_prefix + 4]
                    .try_into()
                    .unwrap(),
            ) as usize;
            if request_length == 0 || request_length > 1_048_576 {
                return false;
            }
            let response_prefix = request_prefix + 4 + request_length;
            response_prefix < payload.len() && payload.len() - response_prefix <= 8_388_608
        }
        [20 | 21, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [28 | 29, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [30 | 31, payload @ ..] => {
            !payload.is_empty()
                && payload.len() <= 256 * 1024
                && serde_json::from_slice::<serde_json::Value>(payload)
                    .is_ok_and(|value| value.is_object())
        }
        // The source bound is 4 MiB, the client's current-birth source bound: a
        // Nock program birth (NOCK K-NOCK-CELL) carries its jam as hex.
        [91, pair @ ..] if pair.len() < HOST_MAX_FRAME => {
            exact_pair(pair).is_some_and(|(observation, source)| {
                !observation.is_empty()
                    && !source.is_empty()
                    && source.len() <= 4 * 1024 * 1024
                    && serde_json::from_slice::<serde_json::Value>(source)
                        .is_ok_and(|value| value.is_object())
            })
        }
        [86, pair @ ..] => pair.len() < HOST_MAX_FRAME && exact_pair(pair).is_some(),
        [87, pair @ ..] if pair.len() < HOST_MAX_FRAME => exact_pair(pair)
            .and_then(|(plan, signatures)| {
                exact_pair(signatures).map(|(sponsor, rest)| (plan, sponsor, rest))
            })
            .is_some_and(|(plan, sponsor, rest)| {
                !plan.is_empty() && sponsor.len() == 64 && matches!(rest.len(), 64 | 160)
            }),
        [88 | 89, ingress @ ..] => !ingress.is_empty() && ingress.len() < HOST_MAX_FRAME,
        // Factory-observation provisioning: sponsor-observed plan, one detached
        // sponsor signature, and exact submit/lookup. The Host rechecks all.
        [92, pair @ ..] => pair.len() < HOST_MAX_FRAME && exact_pair(pair).is_some(),
        [93, pair @ ..] if pair.len() < HOST_MAX_FRAME => exact_pair(pair)
            .is_some_and(|(plan, signature)| !plan.is_empty() && signature.len() == 64),
        [94 | 95, ingress @ ..] => !ingress.is_empty() && ingress.len() < HOST_MAX_FRAME,
        // Fleet turns: plan and topic poll carry one signed account observation
        // and one canonical body; assembly carries one plan and one raw
        // signature; submit/lookup carry one signed ingress; head carries one
        // signed observation; receipt carries one canonical decimal id.
        [96 | 100 | 180, pair @ ..] => pair.len() < HOST_MAX_FRAME && exact_pair(pair).is_some(),
        [97, pair @ ..] if pair.len() < HOST_MAX_FRAME => {
            exact_pair(pair).is_some_and(|(plan, signature)| !plan.is_empty() && signature.len() == 64)
        }
        [98 | 99 | 101, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        // P-AFFORDANCES dry run: one signed observation (as op 1) and one
        // signature list. The Host re-plans, assembles and commits nothing.
        [130, pair @ ..] => pair.len() < HOST_MAX_FRAME && exact_pair(pair).is_some(),
        // Member app readiness is exact plan + detached signatures; native
        // assembly and current specialized admission have no physical effect.
        [193, pair @ ..] => pair.len() < HOST_MAX_FRAME && exact_pair(pair)
            .is_some_and(|(plan, signatures)| !plan.is_empty() && !signatures.is_empty()),
        // Exact request, one current-key signature, and five full current
        // resource observations. Old operator preparation36 stays private.
        [194, pair @ ..] if pair.len() < HOST_MAX_FRAME => exact_pair(pair)
            .and_then(|(request, rest)| exact_pair(rest).map(|(signature, reads)| (request, signature, reads)))
            .is_some_and(|(request, signature, mut reads)| {
                if request.is_empty() || signature.len() != 64 { return false; }
                for _ in 0..4 {
                    let Some((read, rest)) = exact_pair(reads) else { return false; };
                    if read.is_empty() { return false; }
                    reads = rest;
                }
                !reads.is_empty()
            }),
        // C-SAT-2 law-sat: one law-sat request (JSON); the Host reads no Store.
        [150, request @ ..] => !request.is_empty() && request.len() < HOST_MAX_FRAME,
        // Key pre-rotation: plan (one command), assembly (one plan and one raw
        // signature by the NEW key), submit/lookup (one ingress), status (one
        // JSON query). No current-key or sponsor signature participates.
        [140 | 142 | 143, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [141, pair @ ..] if pair.len() < HOST_MAX_FRAME => {
            exact_pair(pair).is_some_and(|(plan, signature)| !plan.is_empty() && signature.len() == 64)
        }
        // Explicit next commitment adoption: source plan, distinct current/next
        // signatures, and exact ingress submit/lookup. Semantic checks are native.
        [187, payload @ ..] => !payload.is_empty() && payload.len() <= 4096
            && serde_json::from_slice::<serde_json::Value>(payload).is_ok_and(|v| v.is_object()),
        [188, payload @ ..] if payload.len() < HOST_MAX_FRAME => exact_pair(payload)
            .and_then(|(plan, signatures)| exact_pair(signatures).map(|(current, next)| (plan, current, next)))
            .is_some_and(|(plan, current, next)| !plan.is_empty() && current.len() == 64 && next.len() == 64),
        [189 | 190, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [144, payload @ ..] => {
            !payload.is_empty()
                && payload.len() <= 1024
                && serde_json::from_slice::<serde_json::Value>(payload)
                    .is_ok_and(|value| value.is_object())
        }
        [102, digits @ ..] => {
            !digits.is_empty()
                && digits.len() <= 80
                && digits.iter().all(u8::is_ascii_digit)
                && (digits.len() == 1 || digits[0] != b'0')
        }
        // K-CLOCK: tick plan, detached assembly (plan + one signature), submit, view.
        [126 | 128, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [127, pair @ ..] if pair.len() < HOST_MAX_FRAME => exact_pair(pair)
            .is_some_and(|(plan, signature)| !plan.is_empty() && signature.len() == 64),
        [129] => true,
        // PAY: the pay cell's signed commands (103 plan, 104 assembly, 105 submit, 106
        // receipt-only lookup), its public view (107), and the observer's reports (108-111,
        // the same four shapes). Each command is authorized by its own signature and
        // capability inside the Host; the socket only bounds the frame. 112 is the public
        // enrollment view (P3b-1), empty payload like 107.
        [103 | 108, command @ ..] => !command.is_empty() && command.len() < HOST_MAX_FRAME,
        [104 | 109, pair @ ..] if pair.len() < HOST_MAX_FRAME => {
            exact_pair(pair).is_some_and(|(plan, signature)| signature.len() == 64 && !plan.is_empty())
        }
        [105 | 106 | 110 | 111, ingress @ ..] => {
            !ingress.is_empty() && ingress.len() < HOST_MAX_FRAME
        }
        [107 | 112] => true,
        // PAY P6: the purse refill quartet. The Host decodes each component canonically.
        [113 | 115 | 116, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [114, pair @ ..] if pair.len() < HOST_MAX_FRAME => {
            exact_pair(pair).is_some_and(|(plan, signature)| !plan.is_empty() && signature.len() == 64)
        }
        // C3 K-JOB-MONEY: the job-money quartet (fund, claim, settle). Same shape as P6's.
        // 160-163 (C3 shipped them at 131-134, which the Nock block holds).
        [160 | 162 | 163, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [161, pair @ ..] if pair.len() < HOST_MAX_FRAME => {
            exact_pair(pair).is_some_and(|(plan, signature)| !plan.is_empty() && signature.len() == 64)
        }
        // C14 TAIL-BOUND: certify plan, detached assembly (ops 170-173; the lane shipped 130-133, which the dry run and the Nock block hold) (plan + one signature), submit, view.
        [170 | 172, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [171, pair @ ..] if pair.len() < HOST_MAX_FRAME => exact_pair(pair)
            .is_some_and(|(plan, signature)| !plan.is_empty() && signature.len() == 64),
        [173] => true,
        _ => false,
    }
}

// These lifecycle, dispatch, share-issue, and fn namespace routes carry operator custody
// selectors or may commit writes. They are available only on the separately
// started owner-private operator socket, never on the public service socket.
fn exact_pair(payload: &[u8]) -> Option<(&[u8], &[u8])> {
    let prefix: [u8; 4] = payload.get(..4)?.try_into().ok()?;
    let first_len = u32::from_le_bytes(prefix) as usize;
    if first_len == 0 || first_len >= payload.len().checked_sub(4)? {
        return None;
    }
    Some((&payload[4..4 + first_len], &payload[4 + first_len..]))
}

fn allowed_operator_operation(request: &[u8]) -> bool {
    match request {
        // Failed START recovery stays on the owner-private socket. This checks
        // framing only; Lean authenticates the original claim, custodian report
        // and current signed management law before any durable reconciliation.
        [206 | 207, pair @ ..] => pair.len() < HOST_MAX_FRAME && exact_pair(pair).is_some(),
        [208 | 209, ingress @ ..] => !ingress.is_empty() && ingress.len() < HOST_MAX_FRAME,
        [151, payload @ ..] => continuity_request(payload),
        [153, payload @ ..] => carried_lookup_request(payload),
        // Read-only signed stream authority checks remain operator-private.
        [152 | 154, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        // Route-bound164 uses the same mutating dispatch receiver with an extra immutable restriction.
        [22 | 23 | 26 | 27 | 34 | 35 | 38 | 39 | 44 | 46 | 47 | 48 | 50 | 52 | 54 | 55 | 56 | 58
        | 66 | 68 | 70 | 72 | 73 | 74 | 76 | 77 | 78 | 80 | 82 | 84 | 85 | 164, payload @ ..] => {
            !payload.is_empty() && payload.len() < HOST_MAX_FRAME
        }
        [40 | 41, payload @ ..] => !payload.is_empty() && payload.len() <= 8192,
        // Event17/19 testimony and receipt-only lookups remain on the owner
        // operator socket. The public listener cannot advance a fn frontier.
        [60..=63, payload @ ..] => !payload.is_empty() && payload.len() <= 16_384,
        // Strict Option Digest plan request; Host derives all other fields
        // from its pinned local fn service and verified Mini history.
        [64, payload @ ..] => !payload.is_empty() && payload.len() <= 128,
        // One retained poll plan and one detached raw Ed25519 signature.
        [65, pair @ ..] if pair.len() >= 4 + 1 + 64 && pair.len() < HOST_MAX_FRAME => {
            let plan_length = u32::from_le_bytes(pair[..4].try_into().unwrap()) as usize;
            plan_length > 0 && plan_length < pair.len() - 4 && pair.len() - 4 - plan_length == 64
        }
        // Op42 obtains all selectors from pinned operator settings and a live
        // local fn status/position call. No caller field enters its plan.
        [42] => true,
        // Custody signs the source header and returns exactly one raw Ed25519
        // signature. Lean constructs the canonical credential envelope.
        [43, pair @ ..] if pair.len() >= 4 + 1 + 64 && pair.len() <= 4 + 8192 + 64 => {
            let plan_length = u32::from_le_bytes(pair[..4].try_into().unwrap()) as usize;
            plan_length > 0
                && plan_length <= 8192
                && plan_length < pair.len() - 4
                && pair.len() - 4 - plan_length == 64
        }
        [28 | 29, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        // Source-owned enrollment authoring and exact lookup. The host still
        // canonical-decodes each component and checks current authority.
        [86, pair @ ..] => pair.len() < HOST_MAX_FRAME && exact_pair(pair).is_some(),
        [87, pair @ ..] if pair.len() < HOST_MAX_FRAME => exact_pair(pair)
            .and_then(|(plan, signatures)| {
                // possession (64), then for a pre-rotated record the next key
                // (32) and its co-signature (64).
                let (sponsor, rest) = exact_pair(signatures)?;
                Some(!plan.is_empty() && sponsor.len() == 64 && matches!(rest.len(), 64 | 160))
            })
            .unwrap_or(false),
        [88 | 89, ingress @ ..] => !ingress.is_empty() && ingress.len() < HOST_MAX_FRAME,
        [92, pair @ ..] => pair.len() < HOST_MAX_FRAME && exact_pair(pair).is_some(),
        [93, pair @ ..] if pair.len() < HOST_MAX_FRAME => exact_pair(pair)
            .is_some_and(|(plan, signature)| !plan.is_empty() && signature.len() == 64),
        [94 | 95, ingress @ ..] => !ingress.is_empty() && ingress.len() < HOST_MAX_FRAME,
        // Sponsor-custodied self-enrollment: plan, detached signature,
        // submit and exact lookup. Public callers cannot enter these routes.
        [117 | 119 | 120, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [118, pair @ ..] if pair.len() < HOST_MAX_FRAME => exact_pair(pair)
            .is_some_and(|(plan, signature)| !plan.is_empty() && signature.len() == 64),
        // K-CLOCK: tick plan, detached assembly (plan + one signature), submit, view.
        [126 | 128, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [127, pair @ ..] if pair.len() < HOST_MAX_FRAME => exact_pair(pair)
            .is_some_and(|(plan, signature)| !plan.is_empty() && signature.len() == 64),
        [129] => true,
        // C14 TAIL-BOUND: certify plan, detached assembly (plan + one signature), submit, view.
        [130 | 132, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [131, pair @ ..] if pair.len() < HOST_MAX_FRAME => exact_pair(pair)
            .is_some_and(|(plan, signature)| !plan.is_empty() && signature.len() == 64),
        [133] => true,
        [32, payload @ ..] => !payload.is_empty() && payload.len() <= 256 * 1024,
        [33, pair @ ..] if pair.len() >= 6 && pair.len() < HOST_MAX_FRAME => {
            let plan_length = u32::from_le_bytes(pair[..4].try_into().unwrap()) as usize;
            plan_length > 0 && plan_length < pair.len() - 4
        }
        // The source request codec can carry an admitted 8 MiB HTTP body.
        // Only the complete native Host frame limits this private author route.
        [36, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [37, pair @ ..] if pair.len() >= 6 && pair.len() < HOST_MAX_FRAME => {
            let plan_length = u32::from_le_bytes(pair[..4].try_into().unwrap()) as usize;
            plan_length > 0 && plan_length < pair.len() - 4
        }
        [45 | 49 | 51 | 53 | 57 | 59 | 67 | 69 | 71 | 75 | 79 | 81 | 83, pair @ ..]
            if pair.len() >= 6 && pair.len() < HOST_MAX_FRAME =>
        {
            let plan_length = u32::from_le_bytes(pair[..4].try_into().unwrap()) as usize;
            plan_length > 0 && plan_length < pair.len() - 4
        }
        _ => false,
    }
}

pub(crate) fn read_config(path: &Path) -> Result<Vec<u8>, String> {
    let file = fs::File::open(path)
        .map_err(|e| format!("cannot read host config {}: {e}", path.display()))?;
    let mut bytes = Vec::new();
    file.take((MAX_CONFIG + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("cannot read host config {}: {e}", path.display()))?;
    if bytes.len() > MAX_CONFIG {
        return Err("host config exceeds socket pin bound".to_owned());
    }
    Ok(bytes)
}

pub(crate) fn read_frame<R: Read>(reader: &mut R) -> io::Result<Option<Vec<u8>>> {
    read_frame_bounded(reader, MAX_FRAME)
}

pub(crate) fn read_frame_bounded<R: Read>(reader: &mut R, bound: usize) -> io::Result<Option<Vec<u8>>> {
    let mut prefix = [0u8; 4];
    let mut read = 0;
    while read < prefix.len() {
        match reader.read(&mut prefix[read..])? {
            0 if read == 0 => return Ok(None),
            0 => {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "truncated frame length",
                ))
            }
            n => read += n,
        }
    }
    let size = u32::from_le_bytes(prefix) as usize;
    if !(1..=MAX_FRAME.min(bound)).contains(&size) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "invalid frame length",
        ));
    }
    // Grown as bytes arrive: a length prefix alone reserves nothing, so a
    // client that names a large frame and trickles holds only what it sent.
    let mut frame = Vec::new();
    reader.take(size as u64).read_to_end(&mut frame)?;
    if frame.len() != size {
        return Err(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "truncated frame",
        ));
    }
    Ok(Some(frame))
}

pub(crate) fn write_frame<W: Write>(writer: &mut W, frame: &[u8]) -> io::Result<()> {
    if !(1..=MAX_FRAME).contains(&frame.len()) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "invalid frame length",
        ));
    }
    writer.write_all(&(frame.len() as u32).to_le_bytes())?;
    writer.write_all(frame)?;
    writer.flush()
}

#[repr(C)]
struct PollFd {
    fd: i32,
    events: i16,
    revents: i16,
}

#[cfg(target_os = "macos")]
unsafe extern "C" {
    fn poll(fds: *mut PollFd, count: u32, timeout: i32) -> i32;
}
#[cfg(not(target_os = "macos"))]
unsafe extern "C" {
    fn poll(fds: *mut PollFd, count: usize, timeout: i32) -> i32;
}
unsafe extern "C" {
    fn fcntl(fd: i32, command: i32, ...) -> i32;
    fn flock(fd: i32, operation: i32) -> i32;
}

/// Logical process ownership, independent of descriptor aliases inherited
/// transiently by a concurrent child between fork and exec.
#[derive(Debug)]
pub(crate) struct ServiceLock {
    file: fs::File,
    owner_pid: libc::pid_t,
}
impl ServiceLock {
    pub(crate) fn release(&self) {
        // A child dropping inherited scope must not unlock the parent.
        if unsafe { libc::getpid() } == self.owner_pid {
            unsafe { libc::flock(self.file.as_raw_fd(), libc::LOCK_UN); }
        }
    }
}
impl Drop for ServiceLock {
    fn drop(&mut self) { self.release(); }
}
pub(crate) fn service_lock(path: &Path) -> Result<ServiceLock, String> {
    let file = match OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
    {
        Ok(file) => file,
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => OpenOptions::new()
            .write(true)
            .open(path)
            .map_err(|error| format!("cannot open service lock {}: {error}", path.display()))?,
        Err(error) => {
            return Err(format!(
                "cannot create service lock {}: {error}",
                path.display()
            ))
        }
    };
    let named = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect service lock {}: {error}", path.display()))?;
    let opened = file
        .metadata()
        .map_err(|error| format!("cannot inspect opened service lock: {error}"))?;
    if !named.file_type().is_file()
        || named.uid() != effective_uid()
        || named.mode() & 0o077 != 0
        || (named.dev(), named.ino()) != (opened.dev(), opened.ino())
    {
        return Err("service lock is not an owner-private regular file".to_owned());
    }
    const LOCK_EX: i32 = 2;
    const LOCK_NB: i32 = 4;
    if unsafe { flock(file.as_raw_fd(), LOCK_EX | LOCK_NB) } < 0 {
        return Err(format!(
            "another service owns {}: {}",
            path.display(),
            io::Error::last_os_error()
        ));
    }
    Ok(ServiceLock { file, owner_pid: unsafe { libc::getpid() } })
}

pub(crate) fn pin_config(path: &Path, bytes: &[u8]) -> Result<(), String> {
    match fs::symlink_metadata(path) {
        Ok(metadata) => {
            if !metadata.file_type().is_file()
                || metadata.uid() != effective_uid()
                || metadata.mode() & 0o077 != 0
            {
                return Err("retained host config is not an owner-private regular file".to_owned());
            }
            if read_config(path)? != bytes {
                return Err("retained host config differs from requested service config".to_owned());
            }
        }
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            crate::create_private(path, bytes)
                .map_err(|error| format!("cannot pin config: {error}"))?;
        }
        Err(error) => {
            return Err(format!(
                "cannot inspect pinned config {}: {error}",
                path.display()
            ))
        }
    }
    Ok(())
}

pub(crate) fn pin_service_mode(path: &Path, operator: bool, legacy_config_exists: bool) -> Result<(), String> {
    if operator && !path.exists() && legacy_config_exists {
        return Err("existing public service pin cannot be upgraded to operator mode".into());
    }
    pin_config(
        path,
        if operator {
            b"operator-v1"
        } else {
            b"public-v1"
        },
    )
}

pub(crate) fn clear_stale_socket(path: &Path) -> Result<(), String> {
    let metadata = match fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(format!("cannot inspect socket {}: {error}", path.display())),
    };
    if !metadata.file_type().is_socket() || metadata.uid() != effective_uid() {
        return Err("socket path is not an owned Unix socket".to_owned());
    }
    match UnixStream::connect(path) {
        Ok(_) => Err("another service still listens on socket".to_owned()),
        Err(error) if error.kind() == io::ErrorKind::ConnectionRefused => {
            let current = fs::symlink_metadata(path)
                .map_err(|error| format!("cannot recheck stale socket: {error}"))?;
            if !current.file_type().is_socket()
                || (current.dev(), current.ino()) != (metadata.dev(), metadata.ino())
            {
                return Err("socket path changed during stale recovery".to_owned());
            }
            fs::remove_file(path).map_err(|error| format!("cannot remove stale socket: {error}"))
        }
        Err(error) => Err(format!("cannot prove socket stale: {error}")),
    }
}

pub(crate) fn set_nonblocking<F: AsRawFd>(file: &F) -> io::Result<()> {
    const F_GETFL: i32 = 3;
    const F_SETFL: i32 = 4;
    #[cfg(target_os = "macos")]
    const O_NONBLOCK: i32 = 0x0004;
    #[cfg(not(target_os = "macos"))]
    const O_NONBLOCK: i32 = 0x0800;
    let flags = unsafe { fcntl(file.as_raw_fd(), F_GETFL) };
    if flags < 0 {
        return Err(io::Error::last_os_error());
    }
    if unsafe { fcntl(file.as_raw_fd(), F_SETFL, flags | O_NONBLOCK) } < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

pub(crate) struct DeadlinePipe<'a, R: Read + AsRawFd> {
    pub(crate) reader: &'a mut R,
    pub(crate) deadline: Instant,
}

impl<R: Read + AsRawFd> Read for DeadlinePipe<'_, R> {
    fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
        loop {
            let remaining = self.deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "frame read deadline",
                ));
            }
            let mut fd = PollFd {
                fd: self.reader.as_raw_fd(),
                events: 1,
                revents: 0,
            };
            let milliseconds = remaining.as_millis().min(i32::MAX as u128) as i32;
            let result = unsafe { poll(&mut fd, 1, milliseconds.max(1)) };
            if result > 0 {
                return self.reader.read(bytes);
            }
            if result < 0 {
                let error = io::Error::last_os_error();
                if error.kind() != io::ErrorKind::Interrupted {
                    return Err(error);
                }
            }
        }
    }
}

pub(crate) struct DeadlinePipeWrite<'a, W: Write + AsRawFd> {
    pub(crate) writer: &'a mut W,
    pub(crate) deadline: Instant,
}

impl<W: Write + AsRawFd> Write for DeadlinePipeWrite<'_, W> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        loop {
            let remaining = self.deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "host request write deadline",
                ));
            }
            let mut fd = PollFd {
                fd: self.writer.as_raw_fd(),
                events: 4,
                revents: 0,
            };
            let milliseconds = remaining.as_millis().min(i32::MAX as u128) as i32;
            let result = unsafe { poll(&mut fd, 1, milliseconds.max(1)) };
            if result > 0 {
                match self.writer.write(bytes) {
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => continue,
                    other => return other,
                }
            }
            if result < 0 {
                let error = io::Error::last_os_error();
                if error.kind() != io::ErrorKind::Interrupted {
                    return Err(error);
                }
            }
        }
    }
    fn flush(&mut self) -> io::Result<()> {
        self.writer.flush()
    }
}

/// A failed write or read leaves the request's execution status unknown. Callers
/// retain the original signed call and use historical lookup before resubmission.
pub fn invoke(
    socket: &Path,
    config: &Path,
    operation: u8,
    payload: &[u8],
) -> Result<Vec<u8>, String> {
    invoke_inner(Path::new(""), socket, config, None, operation, payload)
}

/// An upgraded worker requires the executable image actually serving the
/// socket to match its durable host pin. Version 2 is mandatory on this path:
/// an older service rejects the envelope before it can forward the request.
pub fn invoke_pinned(
    socket: &Path,
    config: &Path,
    expected_host_sha256: &str,
    operation: u8,
    payload: &[u8],
) -> Result<Vec<u8>, String> {
    let expected = parse_host_sha256(expected_host_sha256)?;
    invoke_inner(Path::new(""), socket, config, Some(&expected), operation, payload)
}

/// The main caller has an independently selected local Host; direct remote
/// callers must instead select their local consent pins explicitly.
pub(crate) fn invoke_pinned_with_local(
    local_host: &Path, socket: &Path, config: &Path, expected_host_sha256: &str,
    operation: u8, payload: &[u8],
) -> Result<Vec<u8>, String> {
    let expected = parse_host_sha256(expected_host_sha256)?;
    invoke_inner(local_host, socket, config, Some(&expected), operation, payload)
}

fn check_signing_plan_reply(local_host: &Path, config: &Path, operation: u8,
    payload: &[u8], reply: &[u8]) -> Result<(), String> {
    if crate::client_consent::plan_operation(operation) && reply.first() == Some(&operation) {
        crate::client_consent::operator_plan(local_host, config, operation, payload, &reply[1..])?;
    }
    Ok(())
}

/// Public read workflows use one absolute deadline across connect, write and read.
/// Unlike ordinary invocation, this deliberately supports only a local Unix socket.
pub(crate) fn invoke_pinned_deadline(
    socket: &Path,
    config: &Path,
    expected_host_sha256: &str,
    operation: u8,
    payload: &[u8],
    deadline: Instant,
) -> Result<Vec<u8>, String> {
    let expected = parse_host_sha256(expected_host_sha256)?;
    let Endpoint::Unix(socket) = endpoint(socket)? else {
        return Err("deadline invocation requires a local Unix socket".to_owned());
    };
    let config_path = config;
    let config = read_config(config)?;
    let oversized = if operation == 153 {
        !carried_lookup_request(payload)
    } else {
        payload.len() >= HOST_MAX_FRAME
    };
    if oversized {
        return Err("host request exceeds frame bound or has malformed carried lookup before transmission".to_owned());
    }
    let mut frame = Vec::with_capacity(config.len() + payload.len() + 38);
    frame.push(2);
    frame.extend_from_slice(&(config.len() as u32).to_le_bytes());
    frame.extend_from_slice(&config);
    frame.extend_from_slice(&expected);
    frame.push(operation);
    frame.extend_from_slice(payload);
    let started = Instant::now();
    let mut stream = connect_unix_deadline(socket, deadline)
        .map_err(|e| format!("cannot connect within deadline: {e}"))?;
    write_frame(
        &mut DeadlinePipeWrite {
            writer: &mut stream,
            deadline,
        },
        &frame,
    )
    .map_err(|e| format!("uncertain host request write: {e}"))?;
    let reply = read_frame(&mut DeadlinePipe {
        reader: &mut stream,
        deadline,
    })
    .map_err(|e| format!("uncertain host response read: {e}"))?
    .ok_or_else(|| "uncertain host response: connection closed".to_owned())?;
    crate::trace::record("host", &format!("op{operation}"), frame.len(), reply.len(), started);
    if reply.len() > HOST_MAX_FRAME || reply.is_empty() {
        return Err("uncertain host response exceeds host frame bound".to_owned());
    }
    if reply[0] == 254 {
        return Err(format!(
            "socket rejected request: {}",
            String::from_utf8_lossy(&reply[1..])
        ));
    }
    if !response_operation_matches(operation, &reply) {
        return Err(format!(
            "uncertain host response: unexpected operation {}",
            reply[0]
        ));
    }
    check_signing_plan_reply(Path::new(""), config_path, operation, payload, &reply)?;
    Ok(reply)
}

fn connect_unix_deadline(path: &Path, deadline: Instant) -> io::Result<UnixStream> {
    use std::os::fd::FromRawFd;
    use std::os::unix::ffi::OsStrExt;
    let name = path.as_os_str().as_bytes();
    let mut address: libc::sockaddr_un = unsafe { std::mem::zeroed() };
    if name.is_empty() || name.contains(&0) || name.len() >= address.sun_path.len() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "invalid Unix socket path",
        ));
    }
    address.sun_family = libc::AF_UNIX as _;
    for (to, from) in address.sun_path.iter_mut().zip(name) {
        *to = *from as _;
    }
    let length =
        (std::mem::offset_of!(libc::sockaddr_un, sun_path) + name.len() + 1) as libc::socklen_t;
    #[cfg(target_os = "macos")]
    {
        address.sun_len = length as u8;
    }
    let fd = unsafe { libc::socket(libc::AF_UNIX, libc::SOCK_STREAM, 0) };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    let stream = unsafe { UnixStream::from_raw_fd(fd) };
    if unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) } < 0 {
        return Err(io::Error::last_os_error());
    }
    stream.set_nonblocking(true)?;
    loop {
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "Unix connect deadline",
            ));
        }
        if unsafe { libc::connect(fd, &address as *const _ as *const libc::sockaddr, length) } == 0
        {
            return Ok(stream);
        }
        let error = io::Error::last_os_error();
        match error.raw_os_error() {
            Some(libc::EINTR) => continue,
            // AF_UNIX queue saturation does not establish a pending connection.
            // POLLOUT on that socket can spin, so retry with a bounded short pause.
            Some(code) if code == libc::EAGAIN || code == libc::EWOULDBLOCK => {
                std::thread::sleep(remaining.min(Duration::from_millis(2)));
                continue;
            }
            Some(libc::EINPROGRESS) | Some(libc::EALREADY) => {}
            _ => return Err(error),
        }
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "Unix connect deadline",
                ));
            }
            let mut pollfd = libc::pollfd {
                fd,
                events: libc::POLLOUT,
                revents: 0,
            };
            let result = unsafe {
                libc::poll(
                    &mut pollfd,
                    1,
                    remaining.as_millis().min(i32::MAX as u128).max(1) as i32,
                )
            };
            if result == 0 {
                continue;
            }
            if result < 0 {
                let error = io::Error::last_os_error();
                if error.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(error);
            }
            let mut status: libc::c_int = 0;
            let mut size = std::mem::size_of_val(&status) as libc::socklen_t;
            if unsafe {
                libc::getsockopt(
                    fd,
                    libc::SOL_SOCKET,
                    libc::SO_ERROR,
                    &mut status as *mut _ as *mut libc::c_void,
                    &mut size,
                )
            } < 0
            {
                return Err(io::Error::last_os_error());
            }
            if status != 0 {
                return Err(io::Error::from_raw_os_error(status));
            }
            return Ok(stream);
        }
    }
}

// The same source dispatch receiver returns tag34 permits/outcomes for a
// route-bound164 request. Its dedicated no-record verdict may answer either
// request; only exact bytes distinguish it from an uncertain outcome.
fn response_operation_matches(operation: u8, reply: &[u8]) -> bool {
    match reply.split_first() {
        Some((&tag, _)) if tag == operation || tag == 255 => true,
        Some((&34, _)) if operation == 164 => true,
        Some((&164, payload)) if operation == 34 => {
            payload == b"DREGG/APPLICATION/DISPATCH-NO-RECORD-REFUSAL/v1"
        }
        _ => false,
    }
}

fn invoke_inner(
    local_host: &Path,
    socket: &Path,
    config: &Path,
    expected_host_sha256: Option<&[u8; 32]>,
    operation: u8,
    payload: &[u8],
) -> Result<Vec<u8>, String> {
    let config_path = config;
    let config = read_config(config)?;
    let oversized = if operation == 153 {
        !carried_lookup_request(payload)
    } else {
        payload.len() >= HOST_MAX_FRAME
    };
    if oversized {
        return Err("host request exceeds frame bound or has malformed carried lookup before transmission".to_owned());
    }
    let mut frame = Vec::with_capacity(payload.len() + config.len() + 38);
    frame.push(if expected_host_sha256.is_some() { 2 } else { 1 });
    frame.extend_from_slice(&(config.len() as u32).to_le_bytes());
    frame.extend_from_slice(&config);
    if let Some(expected) = expected_host_sha256 {
        frame.extend_from_slice(expected);
    }
    frame.push(operation);
    frame.extend_from_slice(payload);
    let started = std::time::Instant::now();
    let reply = match endpoint(socket)? {
        Endpoint::Unix(path) => exchange_unix(path, &frame)?,
        Endpoint::Remote(destination) => crate::proxy::exchange(destination, &frame)?,
    };
    crate::trace::record("host", &format!("op{operation}"), frame.len(), reply.len(), started);
    if reply.len() > HOST_MAX_FRAME {
        return Err("uncertain host response exceeds host frame bound".to_owned());
    }
    if reply[0] == 254 {
        return Err(format!(
            "socket rejected request: {}",
            String::from_utf8_lossy(&reply[1..])
        ));
    }
    if !response_operation_matches(operation, &reply) {
        return Err(format!(
            "uncertain host response: unexpected operation {}",
            reply[0]
        ));
    }
    check_signing_plan_reply(local_host, config_path, operation, payload, &reply)?;
    Ok(reply)
}

/// One framed request on a fresh unix-socket connection and its framed reply.
/// A failure after the write leaves the request's status uncertain.
pub(crate) fn exchange_unix(socket: &Path, frame: &[u8]) -> Result<Vec<u8>, String> {
    let mut stream = UnixStream::connect(socket)
        .map_err(|e| format!("cannot connect to {}: {e}", socket.display()))?;
    stream
        .set_write_timeout(Some(Duration::from_secs(10)))
        .map_err(|e| format!("cannot set socket write deadline: {e}"))?;
    if let Err(error) = write_frame(&mut stream, frame) {
        // The service may have refused this connection before reading it
        // (`busy`) and closed it; its refusal is then already waiting here.
        // Only a 254 counts: the socket answers 254 solely for requests it
        // never forwarded, so the status is certain. Anything else stays
        // uncertain.
        if let Ok(Some(refusal)) = read_frame(&mut DeadlinePipe {
            reader: &mut stream,
            deadline: Instant::now() + Duration::from_secs(1),
        }) {
            if refusal.first() == Some(&254) {
                return Ok(refusal);
            }
        }
        return Err(format!("uncertain host request write: {error}"));
    }
    read_frame(&mut DeadlinePipe {
        reader: &mut stream,
        deadline: Instant::now() + Duration::from_secs(600),
    })
    .map_err(|e| format!("uncertain host response read: {e}"))?
    .ok_or_else(|| "uncertain host response: connection closed".to_owned())
}

/// The stdio transport: one framed request written to a byte pipe that ends at
/// the proxy, and its framed reply read back. The first exchange on a new ssh
/// session also waits out the ssh handshake, hence the longer write deadline.
/// `writer` must be non-blocking.
pub(crate) fn exchange_stdio<W: Write + AsRawFd, R: Read + AsRawFd>(
    writer: &mut W,
    reader: &mut R,
    frame: &[u8],
) -> Result<Vec<u8>, String> {
    write_frame(
        &mut DeadlinePipeWrite {
            writer,
            deadline: Instant::now() + Duration::from_secs(60),
        },
        frame,
    )
    .map_err(|e| format!("uncertain host request write: {e}"))?;
    read_frame(&mut DeadlinePipe {
        reader,
        deadline: Instant::now() + Duration::from_secs(600),
    })
    .map_err(|e| format!("uncertain host response read: {e}"))?
    .ok_or_else(|| "uncertain host response: proxy closed".to_owned())
}

/// The socket directory must be owned by this account and inaccessible to
/// others. This closes the interval between bind and chmod on the socket.
pub fn serve(socket: &Path, host: &Path, config: &Path) -> Result<(), String> {
    serve_with_mode(socket, host, config, None)
}

/// `extra_peers` are the uids admitted to the operator socket besides this
/// service's own (`--peer-uid`). Empty is the owner-only rule.
pub fn serve_operator(socket: &Path, host: &Path, config: &Path, extra_peers: &[u32]) -> Result<(), String> {
    let peers = OperatorPeers::with(extra_peers);
    serve_with_mode(socket, host, config, Some(&peers))
}

/// The peers an operator socket admits: this service's effective uid, always,
/// plus an explicit configured set. A session (tenant) uid is never configured;
/// sessions reach the Host through the public relay, whose opcode filter is the
/// public surface. Absence of a peer credential refuses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperatorPeers(Vec<u32>);

impl OperatorPeers {
    pub fn with(extra: &[u32]) -> Self {
        Self::for_owner(effective_uid(), extra)
    }

    fn for_owner(owner: u32, extra: &[u32]) -> Self {
        let mut uids = vec![owner];
        for uid in extra {
            if !uids.contains(uid) {
                uids.push(*uid);
            }
        }
        Self(uids)
    }

    pub fn admits(&self, uid: u32) -> bool {
        self.0.contains(&uid)
    }
}

fn serve_with_mode(
    socket: &Path,
    host: &Path,
    config: &Path,
    operator_peers: Option<&OperatorPeers>,
) -> Result<(), String> {
    let operator = operator_peers.is_some();
    if is_remote(socket) {
        return Err("serve binds a unix socket; an ssh: address names a remote proxy".into());
    }
    let host_sha256 = host_image_sha256(host)?;
    let config_bytes = read_config(config)?;
    let catalog_enabled = catalog_enabled(&config_bytes)?;
    let parent = socket
        .parent()
        .ok_or("socket requires a parent directory")?;
    let metadata = fs::metadata(parent)
        .map_err(|e| format!("cannot inspect socket directory {}: {e}", parent.display()))?;
    if !metadata.is_dir() || metadata.uid() != effective_uid() || metadata.mode() & 0o077 != 0 {
        return Err(format!(
            "socket directory {} must be owned by this user with mode 0700",
            parent.display()
        ));
    }
    let _service_lock = service_lock(&socket.with_extension("lock"))?;
    let pinned_config = socket.with_extension("config");
    pin_service_mode(
        &socket.with_extension("mode"),
        operator,
        pinned_config.exists(),
    )?;
    clear_stale_socket(socket)?;
    pin_config(&pinned_config, &config_bytes)?;
    let listener =
        UnixListener::bind(socket).map_err(|e| format!("cannot bind {}: {e}", socket.display()))?;
    let socket_metadata = fs::symlink_metadata(socket)
        .map_err(|e| format!("cannot inspect new socket {}: {e}", socket.display()))?;
    struct SocketGuard<'a>(&'a Path, u64, u64);
    impl Drop for SocketGuard<'_> {
        fn drop(&mut self) {
            if let Ok(metadata) = fs::symlink_metadata(self.0) {
                if metadata.file_type().is_socket()
                    && (metadata.dev(), metadata.ino()) == (self.1, self.2)
                {
                    let _ = fs::remove_file(self.0);
                }
            }
        }
    }
    let _guard = SocketGuard(socket, socket_metadata.dev(), socket_metadata.ino());
    fs::set_permissions(socket, fs::Permissions::from_mode(0o600))
        .map_err(|e| format!("cannot protect socket {}: {e}", socket.display()))?;
    let mut start = || HostProcess::start_pinned(host, &pinned_config, &host_sha256, &config_bytes);
    eprintln!("mini: serving {}", socket.display());
    if let Some(peers) = operator_peers {
        return supervise_operator(listener, socket, &config_bytes, &host_sha256, catalog_enabled, peers, &mut start);
    }
    supervise(
        &listener,
        None,
        &config_bytes,
        &host_sha256,
        catalog_enabled,
        &mut start,
    )
}

/// A local child invocation with privately held execution/settings custody.
/// Synchronous status/output are the only execution APIs: no Command or child can escape
/// and outlive these images. Linux executes sealed bytes; other platforms only
/// recheck pathnames and retain their documented check/use race boundary.
pub(crate) struct PinnedLocalInvocation {
    host: std::path::PathBuf,
    config: std::path::PathBuf,
    image: fs::File,
    config_image: Option<fs::File>,
    #[cfg(not(target_os = "linux"))]
    expected_image: [u8; 32],
    #[cfg(not(target_os = "linux"))]
    expected_config: Vec<u8>,
}
impl PinnedLocalInvocation {
    pub(crate) fn new(host: &Path, config: &Path, expected_image: &[u8; 32], expected_config: &[u8]) -> Result<Self, String> {
        let config_image = HostProcess::checked_config(config, expected_config)?;
        let image = HostProcess::checked_image(host, expected_image)?;
        Ok(Self {
            host: host.to_path_buf(), config: config.to_path_buf(), image, config_image,
            #[cfg(not(target_os = "linux"))]
            expected_image: *expected_image,
            #[cfg(not(target_os = "linux"))]
            expected_config: expected_config.to_vec(),
        })
    }

    fn command(&self) -> Result<Command, String> {
        #[cfg(not(target_os = "linux"))]
        {
            // Keep per-invocation refusal fences, without claiming the pathname
            // becomes immutable between this check and the actual child exec.
            let _ = HostProcess::checked_config(&self.config, &self.expected_config)?;
            let _ = HostProcess::checked_image(&self.host, &self.expected_image)?;
        }
        HostProcess::pinned_command(&self.host, &self.config, &self.image, self.config_image.as_ref())
    }

    pub(crate) fn status(&self, arguments: &[&std::ffi::OsStr]) -> Result<std::process::ExitStatus, String> {
        self.command()?.args(arguments).stdout(Stdio::null()).stderr(Stdio::null())
            .status().map_err(|e| format!("cannot invoke pinned local source {}: {e}", self.host.display()))
    }

    /// Captured output has std::process::Command::output semantics. Consumers
    /// enforce their source-specific output contract before using these bytes.
    pub(crate) fn output(&self, arguments: &[&std::ffi::OsStr]) -> Result<std::process::Output, String> {
        self.command()?.args(arguments).output()
            .map_err(|e| format!("cannot capture pinned local source {}: {e}", self.host.display()))
    }
}

/// One running Host and its two pipes. Dropping it kills and reaps the process.
struct HostProcess {
    child: std::process::Child,
    input: std::process::ChildStdin,
    output: std::process::ChildStdout,
    // Linux executes a sealed snapshot rather than reopening mutable bytes.
    // Retain it through the child's lifetime, including script interpreter startup.
    _image: Option<fs::File>,
    _config_image: Option<fs::File>,
}

impl HostProcess {
    /// Each restart must execute the advertised image and exact original settings.
    fn start_pinned(host: &Path, config: &Path, expected: &[u8; 32], expected_config: &[u8]) -> Result<Self, String> {
        let config_image = Self::checked_config(config, expected_config)?;
        let image = Self::checked_image(host, expected)?;
        Self::start_checked_images(host, config, image, config_image)
    }

    fn checked_config(config: &Path, expected: &[u8]) -> Result<Option<fs::File>, String> {
        if read_config(config)? != expected {
            return Err("host config changed; refusing launch under the socket's original settings".into());
        }
        #[cfg(target_os = "linux")]
        {
            // Copy the original advertised bytes, rather than reopen the checked
            // pathname. Later pathname changes cannot alter the child's settings.
            return Self::sealed_snapshot(io::Cursor::new(expected), false).map(Some);
        }
        #[cfg(not(target_os = "linux"))]
        Ok(None)
    }

    #[cfg(target_os = "linux")]
    fn sealed_snapshot<R: Read>(mut source: R, executable: bool) -> Result<fs::File, String> {
        use std::os::fd::FromRawFd;
        use std::io::{Seek, SeekFrom};
        let base = libc::MFD_CLOEXEC | libc::MFD_ALLOW_SEALING;
        let name = if executable { c"mini-host" } else { c"mini-host-config" };
        // Explicit execute/no-execute intent on new kernels; older kernels
        // reject these flags with EINVAL and support the original memfd API.
        let intent = if executable { 0x10 } else { 0x08 };
        let mut fd = unsafe { libc::memfd_create(name.as_ptr(), base | intent) };
        if fd < 0 && io::Error::last_os_error().raw_os_error() == Some(libc::EINVAL) {
            fd = unsafe { libc::memfd_create(name.as_ptr(), base) };
        }
        if fd < 0 { return Err(format!("cannot create immutable host snapshot: {}", io::Error::last_os_error())); }
        let mut snapshot = unsafe { fs::File::from_raw_fd(fd) };
        if unsafe { libc::fchmod(fd, if executable { 0o700 } else { 0o400 }) } != 0 {
            return Err(format!("cannot protect host snapshot: {}", io::Error::last_os_error()));
        }
        io::copy(&mut source, &mut snapshot).map_err(|e| format!("cannot copy host snapshot: {e}"))?;
        let seals = libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL;
        if unsafe { libc::fcntl(fd, libc::F_ADD_SEALS, seals) } != 0 {
            return Err(format!("cannot seal host snapshot: {}", io::Error::last_os_error()));
        }
        snapshot.seek(SeekFrom::Start(0)).map_err(|e| format!("cannot read sealed host snapshot: {e}"))?;
        Ok(snapshot)
    }

    fn checked_image(host: &Path, expected: &[u8; 32]) -> Result<fs::File, String> {
        let source = fs::File::open(host)
            .map_err(|e| format!("cannot open pinned host {}: {e}", host.display()))?;
        let before = source.metadata().map_err(|e| format!("cannot inspect pinned host: {e}"))?;
        if !before.is_file() {
            return Err("pinned host image must be a regular file".into());
        }
        // Hash AFTER sealing, so an in-place writer racing the copy cannot
        // change bytes between their verification and execution.
        #[cfg(target_os = "linux")]
        let mut image = Self::sealed_snapshot(source, true)?;
        #[cfg(not(target_os = "linux"))]
        let mut image = source;
        let mut hash = Sha256::new();
        let mut chunk = [0u8; 64 * 1024];
        loop {
            let count = image.read(&mut chunk)
                .map_err(|e| format!("cannot hash pinned host: {e}"))?;
            if count == 0 { break; }
            hash.update(&chunk[..count]);
        }
        #[cfg(not(target_os = "linux"))]
        {
            let after = image.metadata().map_err(|e| format!("cannot reinspect pinned host: {e}"))?;
            let identity = |m: &fs::Metadata| (m.dev(), m.ino(), m.len(), m.mtime(),
                m.mtime_nsec(), m.ctime(), m.ctime_nsec());
            if identity(&before) != identity(&after) {
                return Err("host image changed while checking its pin".into());
            }
        }
        let actual: [u8; 32] = hash.finalize().into();
        if &actual != expected {
            return Err("host image changed; refusing launch under the socket's original pin".into());
        }
        Ok(image)
    }

    fn pinned_command(host: &Path, config: &Path, image: &fs::File, config_image: Option<&fs::File>) -> Result<Command, String> {
        #[cfg(target_os = "linux")]
        let executable = std::path::PathBuf::from(format!(
            "/proc/{}/fd/{}", std::process::id(), image.as_raw_fd()));
        // Platforms without Linux seals retain a checked pathname boundary.
        #[cfg(not(target_os = "linux"))]
        let executable = host.to_path_buf();
        #[cfg(target_os = "linux")]
        let config_argument = std::path::PathBuf::from(format!("/proc/{}/fd/{}",
            std::process::id(), config_image.ok_or("missing immutable host config")?.as_raw_fd()));
        #[cfg(not(target_os = "linux"))]
        let config_argument = config.to_path_buf();
        let mut command = Command::new(executable);
        command.arg(config_argument);
        Ok(command)
    }

    fn start_checked_images(host: &Path, config: &Path, image: fs::File, config_image: Option<fs::File>) -> Result<Self, String> {
        let mut command = Self::pinned_command(host, config, &image, config_image.as_ref())?;
        command.arg("stdio");
        let mut process = Self::start(&mut command, &host.display().to_string())?;
        process._image = Some(image);
        process._config_image = config_image;
        Ok(process)
    }

    fn start(command: &mut Command, name: &str) -> Result<Self, String> {
        let mut child = command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .map_err(|e| format!("cannot start host {name}: {e}"))?;
        let input = child.stdin.take().ok_or("host stdin unavailable")?;
        let output = child.stdout.take().ok_or("host stdout unavailable")?;
        let process = HostProcess {
            child,
            input,
            output,
            _image: None,
            _config_image: None,
        };
        set_nonblocking(&process.input).map_err(|e| format!("cannot bound host input pipe: {e}"))?;
        eprintln!("mini: host process {}", process.child.id());
        Ok(process)
    }

    /// Kill and reap, so no two Hosts ever hold the Store at once.
    fn stop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }

    fn exited(&mut self) -> bool {
        !matches!(self.child.try_wait(), Ok(None))
    }

    /// One request and its reply. Any error leaves the request's status
    /// uncertain: it may have been admitted before the Host stopped answering.
    fn exchange(&mut self, request: &[u8]) -> Result<Vec<u8>, String> {
        self.exchange_within(request, host_budget(request))
    }

    /// `exchange` with the Host-time budget named by the caller.
    fn exchange_within(&mut self, request: &[u8], budget: Duration) -> Result<Vec<u8>, String> {
        write_frame(
            &mut DeadlinePipeWrite {
                writer: &mut self.input,
                deadline: Instant::now() + Duration::from_secs(30),
            },
            request,
        )
        .map_err(|e| format!("host request write: {e}"))?;
        let reply = read_frame(&mut DeadlinePipe {
            reader: &mut self.output,
            deadline: Instant::now() + budget,
        })
        .map_err(|e| format!("host response read: {e}"))?
        .ok_or("host closed during request")?;
        if reply.len() > HOST_MAX_FRAME {
            return Err("host response exceeds bounded native frame".to_owned());
        }
        Ok(reply)
    }
}

impl Drop for HostProcess {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// The bounds of a served socket. Every connection is read on its own thread
/// under its own deadline; only the Host exchange is serialised.
#[derive(Clone, Copy)]
struct ServeBounds {
    /// A client has this long, from accept, to deliver one complete envelope.
    read_deadline: Duration,
    /// Connections alive at once (being read, queued for the Host, or awaiting
    /// its reply). The next one is refused `busy: connection limit`. Each holds
    /// at most one envelope (`MAX_FRAME`), so this also bounds buffered bytes.
    max_connections: usize,
    /// Envelopes read and waiting for the Host. The next one is refused
    /// `busy: host queue full` before it reaches the Host.
    host_queue: usize,
    /// Longest an envelope may wait in the Host queue. When the Host thread
    /// takes a job that waited longer, or whose caller has already closed its
    /// connection, the job is answered 254 and never written to the Host.
    /// It is well inside the client's 600 s reply window, so a live caller
    /// receives the certain refusal instead of timing out as "uncertain"
    /// while its request still waits to execute.
    queue_residence: Duration,
}

const SERVE_BOUNDS: ServeBounds = ServeBounds {
    read_deadline: Duration::from_secs(10),
    max_connections: 64,
    host_queue: 32,
    queue_residence: Duration::from_secs(60),
};

/// One envelope's request, read and checked, handed to the Host thread. The
/// reply channel has room for the one reply, so the Host thread never waits
/// on a client.
struct HostJob {
    request: Vec<u8>,
    reply: mpsc::SyncSender<Vec<u8>>,
    /// When the connection thread queued it (residence is measured from here).
    queued: Instant,
    /// A duplicate of the caller's connection, used only to observe whether
    /// the caller hung up while the job waited. Never read or written.
    caller: Option<UnixStream>,
}

/// Why a queued job is answered without reaching the Host, if it is.
/// Judged by the Host thread immediately before the one place a request is
/// written to the Host (`dispatch_job`), so a 254 can only ever describe a
/// request that was never forwarded.
fn unforwardable(job: &HostJob, now: Instant, residence: Duration) -> Option<&'static str> {
    if job.caller.as_ref().is_some_and(caller_hung_up) {
        Some("caller abandoned queued request")
    } else if now.saturating_duration_since(job.queued) > residence {
        Some("busy: queue residence deadline")
    } else {
        None
    }
}

/// The caller closed its end. Honest clients never half-close after sending
/// their envelope, so end-of-stream as well as a hangup means nobody will
/// read the reply. An unreadable poll is not evidence of abandonment.
fn caller_hung_up(stream: &UnixStream) -> bool {
    let mut descriptor = libc::pollfd {
        fd: stream.as_raw_fd(),
        events: libc::POLLIN,
        revents: 0,
    };
    if unsafe { libc::poll(&mut descriptor, 1, 0) } <= 0 {
        return false;
    }
    if descriptor.revents & (libc::POLLHUP | libc::POLLERR | libc::POLLNVAL) != 0 {
        return true;
    }
    if descriptor.revents & libc::POLLIN == 0 {
        return false;
    }
    let mut byte = 0u8;
    let peeked = unsafe {
        libc::recv(
            descriptor.fd,
            &mut byte as *mut u8 as *mut libc::c_void,
            1,
            libc::MSG_PEEK | libc::MSG_DONTWAIT,
        )
    };
    peeked == 0
}

/// Why a queued job was answered without reaching the Host because the queue
/// was full and its peer held more than its share (`serve_queue`).
const DISPLACED_REFUSAL: &str = "busy: host queue share displaced";

/// Queue `job` for the Host thread under `peer`'s share. When the queue is full
/// and a fuller peer holds a slot, that peer's newest job is dropped from the
/// queue and answered here with the certain refusal: it was never written to
/// the Host, so the 254 describes a request that never ran.
fn queue_job(
    jobs: &serve_queue::Sender<HostJob>,
    peer: u32,
    job: HostJob,
) -> Result<(), TrySendError<HostJob>> {
    if let Some(displaced) = jobs.try_send(peer, job)? {
        let _ = displaced.reply.send(refusal_frame(DISPLACED_REFUSAL));
    }
    Ok(())
}

/// The refusal frame a connection thread writes for an unforwarded job.
fn refusal_frame(reason: &str) -> Vec<u8> {
    let mut refusal = vec![254];
    refusal.extend_from_slice(reason.as_bytes());
    refusal
}

/// What a connection thread needs to judge an envelope before the Host sees it.
struct EnvelopeRules<'a> {
    /// `Some` on the owner-private operator socket: the admitted peer uids.
    operator: Option<&'a OperatorPeers>,
    config_bytes: &'a [u8],
    host_sha256: &'a [u8; 32],
    catalog_enabled: bool,
    read_deadline: Duration,
}

fn refuse(stream: &mut UnixStream, reason: &str) {
    let _ = write_frame(stream, &refusal_frame(reason));
}

/// The accept loop. Nothing a client sends ends it: a bad envelope is refused
/// (254) or dropped, and a Host that stops answering is replaced. A request in
/// flight when its Host stopped gets no reply, which the client reports as an
/// uncertain status (`invoke`). Only a Host that cannot be started at all ends
/// the service.
fn supervise(
    listener: &UnixListener,
    operator: Option<&OperatorPeers>,
    config_bytes: &[u8],
    host_sha256: &[u8; 32],
    catalog_enabled: bool,
    start: &mut dyn FnMut() -> Result<HostProcess, String>,
) -> Result<(), String> {
    supervise_bounded(
        listener,
        &EnvelopeRules {
            operator,
            config_bytes,
            host_sha256,
            catalog_enabled,
            read_deadline: SERVE_BOUNDS.read_deadline,
        },
        SERVE_BOUNDS,
        start,
    )
}

/// Three kinds of thread. This one owns the Host and runs one request at a
/// time, in arrival order. One accept thread admits connections up to
/// `max_connections`. Each connection thread reads its envelope under its
/// own deadline, judges it, queues it for the Host (or is refused `busy`),
/// and writes the reply. A client that trickles bytes, sends nothing, or
/// never reads its reply holds its own thread and nothing else.
fn supervise_bounded(
    listener: &UnixListener,
    rules: &EnvelopeRules<'_>,
    bounds: ServeBounds,
    start: &mut dyn FnMut() -> Result<HostProcess, String>,
) -> Result<(), String> {
    let mut process = start()?;
    let (jobs, queue) = fair_queue::<HostJob>(bounds.host_queue);
    let stopping = AtomicBool::new(false);
    let live = AtomicUsize::new(0);
    std::thread::scope(|scope| {
        let (stopping, live) = (&stopping, &live);
        scope.spawn(move || {
            accept_connections(scope, listener, rules, bounds, jobs, stopping, live)
        });
        let ended = serve_host(&mut process, queue, start, bounds.queue_residence);
        stopping.store(true, Ordering::SeqCst);
        ended
    })
}

/// Close private admission, drain every accepted connection and queued Host
/// exchange, then retain this exact process/Host instance for explicit unit
/// stop. A signed read cannot substitute for this channel-disconnection proof.
fn supervise_operator(
    listener: UnixListener,
    socket: &Path,
    config: &[u8],
    host_sha256: &[u8; 32],
    catalog: bool,
    peers: &OperatorPeers,
    start: &mut dyn FnMut() -> Result<HostProcess, String>,
) -> Result<(), String> {
    let mut process = start()?;
    let mut control = crate::operator_drain::Control::start(socket, config, host_sha256, process.child.id())?;
    let state = control.state.clone();
    let (jobs, queue) = fair_queue::<HostJob>(SERVE_BOUNDS.host_queue);
    let rules = EnvelopeRules { operator: Some(peers), config_bytes: config, host_sha256, catalog_enabled: catalog, read_deadline: SERVE_BOUNDS.read_deadline };
    std::thread::scope(|scope| {
        let (state, rules) = (&state, &rules);
        let accept = scope.spawn(move || {
            accept_connections(scope, &listener, rules, SERVE_BOUNDS, jobs, &state.close, &state.live);
            // Closing the actual listener precedes the admissionClosed bit.
            // Existing readers remain counted and may finish their one turn.
            drop(listener);
            state.admission_closed.store(true, Ordering::Release);
        });
        let ended = serve_host_observed(
            &mut process,
            queue,
            start,
            SERVE_BOUNDS.queue_residence,
            Some(state),
        );
        state.close.store(true, Ordering::Release);
        let accepted = accept.join().map_err(|_| "operator accept thread panicked");
        ended?;
        accepted?;
        // Every sender lives in the accept loop or an accepted worker. The
        // receiver ends only after all workers finish response delivery and
        // drop their sender. Thus no queued or active Host request remains.
        if !state.admission_closed.load(Ordering::Acquire) || state.live.load(Ordering::Acquire) != 0 {
            return Err("operator drain ended before admission/worker closure".into());
        }
        state.drained.store(true, Ordering::Release);
        control.hold_closed()
    })
}

/// The Host thread: one request at a time, a Host that stops is replaced.
/// Returns only when a Host cannot be started (or every sender is gone).
fn serve_host(
    process: &mut HostProcess,
    queue: serve_queue::Receiver<HostJob>,
    start: &mut dyn FnMut() -> Result<HostProcess, String>,
    residence: Duration,
) -> Result<(), String> {
    serve_host_observed(process, queue, start, residence, None)
}

fn serve_host_observed(
    process: &mut HostProcess,
    queue: serve_queue::Receiver<HostJob>,
    start: &mut dyn FnMut() -> Result<HostProcess, String>,
    residence: Duration,
    state: Option<&crate::operator_drain::State>,
) -> Result<(), String> {
    for job in queue {
        // Pre-transmission only: once `exchange` below has begun, the job is
        // never answered 254 (`serve_refuses_254_only_before_forward`).
        if let Some(reason) = unforwardable(&job, Instant::now(), residence) {
            let _ = job.reply.send(refusal_frame(reason));
            continue;
        }
        if process.exited() {
            eprintln!("mini: host process {} exited between requests; restarting", process.child.id());
            process.stop();
            *process = start()?;
            if let Some(state) = state { state.host_pid.store(process.child.id(), Ordering::Release); }
        }
        match process.exchange(&job.request) {
            Ok(reply) => {
                let _ = job.reply.send(reply);
            }
            Err(error) => {
                eprintln!(
                    "mini: host process {}: {error}; status uncertain; restarting",
                    process.child.id()
                );
                drop(job);
                process.stop();
                *process = start()?;
                if let Some(state) = state { state.host_pid.store(process.child.id(), Ordering::Release); }
            }
        }
    }
    Ok(())
}

fn accept_connections<'scope, 'env>(
    scope: &'scope std::thread::Scope<'scope, 'env>,
    listener: &UnixListener,
    rules: &'env EnvelopeRules<'env>,
    bounds: ServeBounds,
    jobs: serve_queue::Sender<HostJob>,
    stopping: &'scope AtomicBool,
    live: &'scope AtomicUsize,
) {
    while !stopping.load(Ordering::SeqCst) {
        // Wait for a connection in short slices so a stopping service is seen.
        let mut fd = PollFd {
            fd: listener.as_raw_fd(),
            events: 1,
            revents: 0,
        };
        let ready = unsafe { poll(&mut fd, 1, 100) };
        if ready < 0 {
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::Interrupted {
                eprintln!("mini: socket poll failed: {error}");
                std::thread::sleep(Duration::from_millis(100));
            }
            continue;
        }
        if ready == 0 {
            continue;
        }
        let mut stream = match listener.accept() {
            Ok((stream, _)) => stream,
            Err(e) => {
                eprintln!("mini: socket accept failed: {e}");
                std::thread::sleep(Duration::from_millis(100));
                continue;
            }
        };
        if live.fetch_add(1, Ordering::SeqCst) >= bounds.max_connections {
            live.fetch_sub(1, Ordering::SeqCst);
            // A fresh socket's send buffer takes this frame without waiting.
            let _ = stream.set_write_timeout(Some(Duration::from_secs(1)));
            refuse(&mut stream, "busy: connection limit");
            continue;
        }
        let jobs = jobs.clone();
        let spawned = std::thread::Builder::new()
            .name("mini-serve-client".into())
            .stack_size(256 * 1024)
            .spawn_scoped(scope, move || {
                serve_connection(stream, rules, &jobs);
                live.fetch_sub(1, Ordering::SeqCst);
            });
        if let Err(error) = spawned {
            // The closure (and its stream) is dropped unrun; release its slot.
            live.fetch_sub(1, Ordering::SeqCst);
            eprintln!("mini: cannot start a client reader: {error}");
        }
    }
}

/// One connection: read the envelope by its deadline, judge it, queue it for
/// the Host, and write the reply.
fn serve_connection(
    mut stream: UnixStream,
    rules: &EnvelopeRules<'_>,
    jobs: &serve_queue::Sender<HostJob>,
) {
    if let Err(e) = stream.set_write_timeout(Some(Duration::from_secs(10))) {
        eprintln!("mini: cannot set client write deadline: {e}");
        return;
    }
    if let Some(peers) = rules.operator {
        match peer_uid(&stream) {
            Ok(uid) if peers.admits(uid) => {}
            Ok(_) => return refuse(&mut stream, "operator peer UID mismatch"),
            Err(e) => {
                eprintln!("mini: {e}");
                return refuse(&mut stream, "operator peer credential unavailable");
            }
        }
    }
    let mut envelope = match read_frame(&mut DeadlinePipe {
        reader: &mut stream,
        deadline: Instant::now() + rules.read_deadline,
    }) {
        Ok(Some(frame)) => frame,
        Ok(None) => return,
        Err(e) => {
            eprintln!("mini: refused invalid socket frame: {e}");
            return refuse(&mut stream, &format!("invalid socket frame: {e}"));
        }
    };
    let request_start = match request_from_envelope(&envelope, rules.config_bytes, rules.host_sha256) {
        Ok(request) => envelope.len() - request.len(),
        Err(reason) => return refuse(&mut stream, reason),
    };
    envelope.drain(..request_start);
    let request = envelope;
    if !request_within_bound(&request) {
        return refuse(&mut stream, "host frame exceeds bound");
    }
    if let Some(reason) = operation_body_refusal(&request) {
        return refuse(&mut stream, reason);
    }
    if !(if rules.operator.is_some() {
        // The owner-private listener is the single Host endpoint for both
        // lifecycle clients and the separately filtered public ingress relay.
        allowed_operator_operation(&request) || allowed_operation(&request, rules.catalog_enabled)
    } else {
        allowed_operation(&request, rules.catalog_enabled)
    }) {
        return refuse(&mut stream, "operation unavailable on selected socket");
    }
    let (reply, answer) = mpsc::sync_channel(1);
    // Without a duplicate the job cannot be observed for hangup; it is still
    // bounded by the residence deadline.
    let caller = stream.try_clone().ok();
    let peer = peer_uid(&stream).unwrap_or(serve_queue::UNKNOWN_PEER);
    match queue_job(jobs, peer, HostJob {
        request,
        reply,
        queued: Instant::now(),
        caller,
    }) {
        Ok(()) => {}
        Err(TrySendError::Full(_)) => return refuse(&mut stream, "busy: host queue full"),
        Err(TrySendError::Disconnected(_)) => return,
    }
    // No reply means the Host stopped during this request (or the service is
    // ending): closing without a frame is what `invoke` reports as uncertain.
    if let Ok(reply) = answer.recv() {
        if let Err(error) = write_frame(&mut stream, &reply) {
            eprintln!("mini: client lost host reply; status uncertain: {error}");
        }
    }
}

#[cfg(any(
    target_os = "macos",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd"
))]
pub(crate) fn peer_uid(stream: &UnixStream) -> Result<u32, String> {
    unsafe extern "C" {
        fn getpeereid(socket: i32, uid: *mut u32, gid: *mut u32) -> i32;
    }
    let mut uid = 0;
    let mut gid = 0;
    if unsafe { getpeereid(stream.as_raw_fd(), &mut uid, &mut gid) } != 0 {
        return Err(format!(
            "operator peer credential: {}",
            io::Error::last_os_error()
        ));
    }
    Ok(uid)
}

#[cfg(target_os = "linux")]
pub(crate) fn peer_uid(stream: &UnixStream) -> Result<u32, String> {
    #[repr(C)]
    struct Ucred {
        pid: i32,
        uid: u32,
        gid: u32,
    }
    unsafe extern "C" {
        fn getsockopt(fd: i32, level: i32, name: i32, value: *mut Ucred, length: *mut u32) -> i32;
    }
    let mut credential = Ucred {
        pid: 0,
        uid: 0,
        gid: 0,
    };
    let mut length = std::mem::size_of::<Ucred>() as u32;
    if unsafe { getsockopt(stream.as_raw_fd(), 1, 17, &mut credential, &mut length) } != 0
        || length as usize != std::mem::size_of::<Ucred>()
    {
        return Err(format!(
            "operator peer credential: {}",
            io::Error::last_os_error()
        ));
    }
    Ok(credential.uid)
}

#[cfg(not(any(
    target_os = "linux",
    target_os = "macos",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd"
)))]
pub(crate) fn peer_uid(_stream: &UnixStream) -> Result<u32, String> {
    Err("operator peer credentials are unavailable on this platform".into())
}

pub(crate) fn effective_uid() -> u32 {
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    unsafe { geteuid() }
}

#[cfg(test)]
mod tests {
    #[test]
    fn failed_start_recovery_is_private_and_requires_complete_frames() {
        for operation in [206u8, 207] {
            let valid = [operation, 1, 0, 0, 0, b'P', b'S'];
            assert!(super::allowed_operator_operation(&valid));
            assert!(!super::allowed_operation(&valid, false));
            assert!(!super::allowed_operator_operation(&[operation]));
            assert!(!super::allowed_operator_operation(&[operation, 1, 0, 0, 0, b'P']));
        }
        for operation in [208u8, 209] {
            let valid = [operation, b'I'];
            assert!(super::allowed_operator_operation(&valid));
            assert!(!super::allowed_operation(&valid, false));
            assert!(!super::allowed_operator_operation(&[operation]));
            let mut oversized = vec![0; super::HOST_MAX_FRAME + 1];
            oversized[0] = operation;
            assert!(!super::allowed_operator_operation(&oversized));
        }
    }

    use super::*;
    use std::thread;

    fn refusal_for_peer(peers: &OperatorPeers) -> Vec<u8> {
        let (mut client, server) = UnixStream::pair().unwrap();
        let (jobs, _queue) = fair_queue::<HostJob>(1);
        let worker = thread::spawn({
            let peers = peers.clone();
            move || {
                let rules = EnvelopeRules {
                    operator: Some(&peers),
                    config_bytes: b"config",
                    host_sha256: &[0; 32],
                    catalog_enabled: false,
                    read_deadline: Duration::from_millis(200),
                };
                serve_connection(server, &rules, &jobs);
            }
        });
        // One frame that no envelope rule accepts: an admitted peer is refused
        // for the frame, a foreign peer before any byte is read.
        write_frame(&mut client, b"x").unwrap();
        let reply = read_frame(&mut client).unwrap().unwrap();
        worker.join().unwrap();
        reply
    }

    #[test]
    fn transport_operator_peers_default_to_owner_and_add_only_configured_uids() {
        let owner = OperatorPeers::for_owner(1000, &[]);
        assert!(owner.admits(1000));
        assert!(!owner.admits(1001) && !owner.admits(0));
        let relay = OperatorPeers::for_owner(1000, &[1002, 1000, 1002]);
        assert_eq!(relay, OperatorPeers(vec![1000, 1002]));
        assert!(relay.admits(1002) && !relay.admits(1001));
        assert!(OperatorPeers::with(&[]).admits(effective_uid()));
    }

    #[test]
    fn transport_operator_socket_refuses_a_peer_outside_the_allowlist() {
        let me = effective_uid();
        let foreign = OperatorPeers(vec![me.wrapping_add(1)]);
        let reply = refusal_for_peer(&foreign);
        assert_eq!(reply, [&[254u8][..], b"operator peer UID mismatch"].concat());
        let admitted = refusal_for_peer(&OperatorPeers::with(&[]));
        assert_eq!(admitted[0], 254);
        assert_ne!(&admitted[1..], b"operator peer UID mismatch");
    }

    /// Two real uids. Run on a Linux box where `sudo -n setpriv` works:
    /// MINI_TEST_FOREIGN_UID=65534 cargo nextest run --run-ignored all -E 'test(transport_operator_socket_two_uid)'
    /// A foreign process is refused by the filesystem on the owner-private
    /// layout (EACCES), and by the peer allowlist when the layout is opened.
    #[test]
    #[ignore]
    fn transport_operator_socket_two_uid_foreign_process_is_refused() {
        use std::os::unix::fs::PermissionsExt;
        let foreign: u32 = std::env::var("MINI_TEST_FOREIGN_UID").expect("MINI_TEST_FOREIGN_UID").parse().unwrap();
        assert_ne!(foreign, effective_uid());
        let directory = std::env::temp_dir().join(format!("mini-two-uid-{}", std::process::id()));
        fs::create_dir(&directory).unwrap();
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
        let socket = directory.join("operator.sock");
        let key = directory.join("credentials.key");
        fs::write(&key, [7u8; 32]).unwrap();
        fs::set_permissions(&key, fs::Permissions::from_mode(0o600)).unwrap();
        let listener = UnixListener::bind(&socket).unwrap();
        fs::set_permissions(&socket, fs::Permissions::from_mode(0o600)).unwrap();
        let probe = |path: &Path, verb: &str| -> String {
            let script = format!(
                "import socket,sys\ntry:\n  {verb}\nexcept PermissionError:\n  print('EACCES'); sys.exit(0)\nprint('OPENED')",
            );
            let output = Command::new("sudo")
                .args(["-n", "setpriv", &format!("--reuid={foreign}"), &format!("--regid={foreign}"), "--clear-groups", "--", "python3", "-c", &script, path.to_str().unwrap()])
                .output()
                .unwrap();
            assert!(output.status.success(), "probe failed: {}", String::from_utf8_lossy(&output.stderr));
            String::from_utf8(output.stdout).unwrap().trim().to_owned()
        };
        let connect = "s=socket.socket(socket.AF_UNIX); s.connect(sys.argv[1])";
        let open = "open(sys.argv[1],'rb').read()";
        assert_eq!(probe(&socket, connect), "EACCES");
        assert_eq!(probe(&key, open), "EACCES");
        // Open the layout (as a misdeployment would): the peer check still refuses.
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o711)).unwrap();
        fs::set_permissions(&socket, fs::Permissions::from_mode(0o666)).unwrap();
        let server = thread::spawn(move || {
            let (stream, _) = listener.accept().unwrap();
            let peers = OperatorPeers::with(&[]);
            let (jobs, _queue) = fair_queue::<HostJob>(1);
            let rules = EnvelopeRules {
                operator: Some(&peers),
                config_bytes: b"config",
                host_sha256: &[0; 32],
                catalog_enabled: false,
                read_deadline: Duration::from_millis(500),
            };
            serve_connection(stream, &rules, &jobs);
        });
        let refused = "s=socket.socket(socket.AF_UNIX); s.connect(sys.argv[1]); h=s.recv(4); n=int.from_bytes(h,'little'); b=s.recv(n); print(b[1:].decode()); sys.exit(0)";
        assert_eq!(probe(&socket, refused), "operator peer UID mismatch");
        server.join().unwrap();
        fs::remove_dir_all(&directory).unwrap();
    }

    #[test]
    fn socket_restart_refuses_replaced_host_under_original_pin() {
        let directory = std::env::temp_dir().join(format!(
            "mini-host-pin-{}-{}", std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir(&directory).unwrap();
        let host = directory.join("host");
        let config = directory.join("config");
        fs::write(&config, b"{}").unwrap();
        // The script interpreter reopens the descriptor path after exec. The
        // retained image must survive that startup and the child's full life.
        fs::write(&host, b"#!/bin/sh\nprintf original\n").unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        let expected = host_image_sha256(&host).unwrap();
        let mut first = HostProcess::start_pinned(&host, &config, &expected, b"{}").unwrap();
        let mut reply = String::new();
        first.output.read_to_string(&mut reply).unwrap();
        assert!(first.child.wait().unwrap().success());
        assert_eq!(reply, "original");
        drop(first);
        let staged = directory.join("changed");
        fs::write(&staged, b"#!/bin/sh\nprintf replacement\n").unwrap();
        fs::set_permissions(&staged, fs::Permissions::from_mode(0o700)).unwrap();
        fs::rename(&staged, &host).unwrap();
        let refused = HostProcess::start_pinned(&host, &config, &expected, b"{}");
        assert!(matches!(refused, Err(ref error) if error.contains("original pin")));
        let upgraded = host_image_sha256(&host).unwrap();
        let mut second = HostProcess::start_pinned(&host, &config, &upgraded, b"{}").unwrap();
        let mut reply = String::new();
        second.output.read_to_string(&mut reply).unwrap();
        assert!(second.child.wait().unwrap().success());
        assert_eq!(reply, "replacement");
        drop(second);
        fs::remove_dir_all(directory).unwrap();
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn pinned_local_invocation_uses_exact_images_across_multiple_commands() {
        use std::ffi::OsStr;
        let directory = std::env::temp_dir().join(format!("mini-local-seal-{}-{}",
            std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir(&directory).unwrap();
        let host = directory.join("host");
        let config = directory.join("config");
        let output = directory.join("output");
        let original = b"#!/bin/sh\n[ \"$(cat \"$1\")\" = original ] || exit 9\nprintf '%s' \"$2\" >> \"$3\"\nprintf '%s' \"$2\"\nprintf original >&2\n";
        fs::write(&host, original).unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        fs::write(&config, b"original").unwrap();
        let expected = host_image_sha256(&host).unwrap();
        let invocation = PinnedLocalInvocation::new(&host, &config, &expected, b"original").unwrap();
        let changed = b"#!/bin/sh\nexit 33\n";
        fs::write(&host, changed).unwrap();
        fs::write(&config, b"changed").unwrap();
        let replacement = directory.join("replacement");
        fs::write(&replacement, changed).unwrap();
        fs::rename(&replacement, &host).unwrap();
        fs::write(&replacement, b"replacement").unwrap();
        fs::rename(&replacement, &config).unwrap();
        for verb in ["author", "inspect", "inspect-readback"] {
            assert!(invocation.status(&[OsStr::new(verb), output.as_os_str()]).unwrap().success());
        }
        let captured = invocation.output(&[OsStr::new("capture"), output.as_os_str()]).unwrap();
        assert!(captured.status.success());
        assert_eq!(captured.stdout, b"capture");
        assert_eq!(captured.stderr, b"original");
        assert_eq!(fs::read(&output).unwrap(), b"authorinspectinspect-readbackcapture");
        // A replace/restore attack can satisfy caller pathname fences. It still
        // cannot change the code/settings that any of the three children used.
        fs::write(&host, original).unwrap();
        fs::write(&config, b"original").unwrap();
        assert_eq!(host_image_sha256(&host).unwrap(), expected);
        assert_eq!(read_config(&config).unwrap(), b"original");
        drop(invocation);
        fs::remove_dir_all(directory).unwrap();
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn sealed_config_survives_mutation_and_restart_refuses_changed_settings() {
        use std::os::unix::fs::FileExt;
        let directory = std::env::temp_dir().join(format!("mini-config-seal-{}-{}",
            std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir(&directory).unwrap();
        let host = directory.join("host");
        let config = directory.join("config");
        fs::write(&host, b"#!/bin/sh\ncat \"$1\"\n").unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        fs::write(&config, b"original settings").unwrap();
        let expected = host_image_sha256(&host).unwrap();
        let image = HostProcess::checked_image(&host, &expected).unwrap();
        let config_image = HostProcess::checked_config(&config, b"original settings").unwrap();
        let sealed = config_image.as_ref().unwrap();
        assert_eq!(sealed.write_at(b"X", 0).unwrap_err().raw_os_error(), Some(libc::EPERM));
        assert_eq!(sealed.set_len(1).unwrap_err().raw_os_error(), Some(libc::EPERM));
        fs::write(&config, b"mutated settings").unwrap();
        let replacement = directory.join("replacement");
        fs::write(&replacement, b"replaced settings").unwrap();
        fs::rename(&replacement, &config).unwrap();
        let mut process = HostProcess::start_checked_images(&host, &config, image, config_image).unwrap();
        let mut reply = String::new();
        process.output.read_to_string(&mut reply).unwrap();
        assert!(process.child.wait().unwrap().success());
        assert_eq!(reply, "original settings");
        drop(process);
        assert!(matches!(HostProcess::start_pinned(&host, &config, &expected, b"original settings"),
            Err(ref error) if error.contains("original settings")));
        fs::remove_dir_all(directory).unwrap();
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn sealed_host_snapshot_survives_in_place_and_pathname_replacement() {
        use std::os::unix::fs::FileExt;
        let directory = std::env::temp_dir().join(format!(
            "mini-host-seal-{}-{}", std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir(&directory).unwrap();
        let host = directory.join("host");
        let config = directory.join("config");
        fs::write(&config, b"{}").unwrap();
        let original = b"#!/bin/sh\nprintf original\n";
        fs::write(&host, original).unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        let expected = host_image_sha256(&host).unwrap();
        let image = HostProcess::checked_image(&host, &expected).unwrap();
        let seals = unsafe { libc::fcntl(image.as_raw_fd(), libc::F_GET_SEALS) };
        assert_eq!(seals & (libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL),
            libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL);
        assert_eq!(image.write_at(b"X", 0).unwrap_err().raw_os_error(), Some(libc::EPERM));
        assert_eq!(image.set_len(1).unwrap_err().raw_os_error(), Some(libc::EPERM));
        // Both changes happen in the old hash/exec race window. Neither may
        // alter the executable handed to this child or its script interpreter.
        fs::write(&host, b"#!/bin/sh\nprintf mutated\n").unwrap();
        let replacement = directory.join("replacement");
        fs::write(&replacement, b"#!/bin/sh\nprintf replaced\n").unwrap();
        fs::rename(&replacement, &host).unwrap();
        let mut process = HostProcess::start_checked_images(&host, &config, image, HostProcess::checked_config(&config, b"{}").unwrap()).unwrap();
        let mut reply = String::new();
        process.output.read_to_string(&mut reply).unwrap();
        assert!(process.child.wait().unwrap().success());
        assert_eq!(reply, "original");
        drop(process);
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn adoption_routes_bound_plan_and_two_role_signatures() {
        let mut request = vec![187];
        request.extend_from_slice(b"{}");
        request.resize(4097, b' ');
        assert!(allowed_operation(&request, false));
        request.push(b' ');
        assert!(!allowed_operation(&request, false));
        assert!(!allowed_operation(&[187, b'[', b']'], false));
        let signatures = crate::participant_enrollment::pair(&[1;64], &[2;64]).unwrap();
        let payload = crate::participant_enrollment::pair(b"plan", &signatures).unwrap();
        let assembly = [vec![188],payload].concat();
        assert!(allowed_operation(&assembly, false));
        assert!(!allowed_operation(&assembly[..assembly.len()-1], false));
        let malformed = [vec![188],crate::participant_enrollment::pair(b"plan", &[1;128]).unwrap()].concat();
        assert!(!allowed_operation(&malformed, false));
        for opcode in [189,190] {
            assert!(allowed_operation(&[opcode,1], false));
            assert!(!allowed_operation(&[opcode], false));
            let mut oversized = vec![opcode]; oversized.resize(HOST_MAX_FRAME+1,1);
            assert!(!allowed_operation(&oversized, false));
        }
    }

    #[test]
    fn enrollment_quote_is_public_only_with_bounded_json_object() {
        let mut max = b"{}".to_vec();
        max.resize(4096, b' ');
        for payload in [b"{}".as_slice(), max.as_slice()] {
            let mut request = vec![121];
            request.extend_from_slice(payload);
            assert!(allowed_operation(&request, false));
        }
        let mut too_large = max;
        too_large.push(b' ');
        for payload in [b"".as_slice(), b"[]", b"null", b"x", &[255], too_large.as_slice()] {
            let mut request = vec![121];
            request.extend_from_slice(payload);
            assert!(!allowed_operation(&request, false));
        }
        assert!(!allowed_operation(&[152, 1], false), "private renew remains private");
    }

    #[test]
    fn pinned_envelope_checks_config_and_host_before_exposing_request() {
        let host = [7u8; 32];
        let other_host = [8u8; 32];
        let request = [13, b'4'];
        let v2 = [
            vec![2, 6, 0, 0, 0],
            b"config".to_vec(),
            host.to_vec(),
            request.to_vec(),
        ]
        .concat();
        assert_eq!(
            request_from_envelope(&v2, b"config", &host),
            Ok(request.as_slice())
        );
        assert_eq!(
            request_from_envelope(&v2, b"changed", &host),
            Err("config pin mismatch")
        );
        assert_eq!(
            request_from_envelope(&v2, b"config", &other_host),
            Err("host image pin mismatch")
        );
        assert_eq!(
            request_from_envelope(&v2[..v2.len() - 2], b"config", &host),
            Err("invalid socket envelope")
        );
        let v1 = [vec![1, 6, 0, 0, 0], b"config".to_vec(), request.to_vec()].concat();
        assert_eq!(
            request_from_envelope(&v1, b"config", &host),
            Ok(request.as_slice())
        );
        assert_ne!(v2[0], 1); // A prior v1-only service refuses rather than forwarding v2.
    }

    #[test]
    fn pinned_invocation_sends_v2_without_fallback() {
        let directory = Path::new("/tmp").join(format!(
            "mip-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        let socket = directory.join("test.sock");
        let config = directory.join("config.json");
        fs::write(&config, b"config").unwrap();
        let listener = UnixListener::bind(&socket).unwrap();
        let host = [7u8; 32];
        let host_hex = "07".repeat(32);
        let thread = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let envelope = read_frame(&mut stream).unwrap().unwrap();
            assert_eq!(envelope[0], 2);
            assert_eq!(
                request_from_envelope(&envelope, b"config", &host),
                Ok(&[13, b'4'][..])
            );
            write_frame(&mut stream, &[13, 1]).unwrap();
        });
        assert_eq!(
            invoke_pinned(&socket, &config, &host_hex, 13, b"4").unwrap(),
            vec![13, 1]
        );
        thread.join().unwrap();
        assert!(invoke_pinned(&socket, &config, &"AB".repeat(32), 13, b"4").is_err());
        fs::remove_file(socket).unwrap();
        fs::remove_file(config).unwrap();
        fs::remove_dir(directory).unwrap();
    }

    struct SmallReader<'a> {
        bytes: &'a [u8],
    }
    impl Read for SmallReader<'_> {
        fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
            let count = out.len().min(1).min(self.bytes.len());
            out[..count].copy_from_slice(&self.bytes[..count]);
            self.bytes = &self.bytes[count..];
            Ok(count)
        }
    }

    #[test]
    fn fragmented_frames_are_reassembled_and_truncation_is_uncertain() {
        let mut wire = Vec::new();
        write_frame(&mut wire, &[2, 0, 255, 7]).unwrap();
        assert_eq!(
            read_frame(&mut SmallReader { bytes: &wire }).unwrap(),
            Some(vec![2, 0, 255, 7])
        );
        assert_eq!(
            read_frame(&mut SmallReader { bytes: &wire[..6] })
                .unwrap_err()
                .kind(),
            io::ErrorKind::UnexpectedEof
        );
        assert!(read_frame(&mut SmallReader {
            bytes: &[0, 0, 0, 0]
        })
        .is_err());
    }

    #[test]
    fn socket_invocation_handles_fragmented_reply_and_marks_lost_reply_uncertain() {
        let directory = std::env::temp_dir().join(format!(
            "mini-transport-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        let socket = directory.join("test.sock");
        let config = directory.join("config.json");
        fs::write(&config, b"config").unwrap();
        let listener = UnixListener::bind(&socket).unwrap();
        let thread = thread::spawn(move || {
            let (mut first, _) = listener.accept().unwrap();
            assert_eq!(
                read_frame(&mut first).unwrap(),
                Some([vec![1, 6, 0, 0, 0], b"config".to_vec(), vec![2, 42]].concat())
            );
            let mut reply = Vec::new();
            write_frame(&mut reply, &[2, 7, 8]).unwrap();
            for byte in reply {
                first.write_all(&[byte]).unwrap();
            }
            let (mut second, _) = listener.accept().unwrap();
            assert_eq!(
                read_frame(&mut second).unwrap(),
                Some([vec![1, 6, 0, 0, 0], b"config".to_vec(), vec![2, 42]].concat())
            );
        });
        assert_eq!(invoke(&socket, &config, 2, &[42]).unwrap(), vec![2, 7, 8]);
        assert!(invoke(&socket, &config, 2, &[42])
            .unwrap_err()
            .contains("uncertain"));
        thread.join().unwrap();
        fs::remove_file(socket).unwrap();
        fs::remove_file(config).unwrap();
        fs::remove_dir(directory).unwrap();
    }

    /// A Host that stops mid-request costs that request a certain answer and
    /// nothing else: the socket stays, and the next request reaches a fresh Host.
    #[test]
    fn supervisor_outlives_a_host_that_exits_mid_request() {
        let directory = std::env::temp_dir().join(format!(
            "mini-supervise-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        let socket = directory.join("test.sock");
        let config = directory.join("config.json");
        fs::write(&config, b"config").unwrap();
        let listener = UnixListener::bind(&socket).unwrap();
        // Answers each frame with its own operation byte; op 9 exits instead.
        let script = r#"while n=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 | tr -d ' \n'); [ -n "$n" ]; do
  op=$(dd bs=1 count=1 2>/dev/null | od -An -tu1 | tr -d ' \n')
  [ "$n" -gt 1 ] && dd bs=1 count=$((n - 1)) of=/dev/null 2>/dev/null
  [ "$op" = 9 ] && exit 3
  printf '\001\000\000\000'; printf "\\$(printf %03o "$op")"
done"#;
        let starts = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let counted = starts.clone();
        thread::spawn(move || {
            let mut start = || {
                counted.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                HostProcess::start(Command::new("/bin/sh").arg("-c").arg(script), "fake")
            };
            let _ = supervise(&listener, None, b"config", &[0; 32], false, &mut start);
        });
        assert_eq!(invoke(&socket, &config, 3, &[1, 2]).unwrap(), vec![3]);
        assert!(invoke(&socket, &config, 9, &[])
            .unwrap_err()
            .contains("uncertain"));
        assert_eq!(invoke(&socket, &config, 3, &[]).unwrap(), vec![3]);
        assert_eq!(invoke(&socket, &config, 5, &[7]).unwrap(), vec![5]);
        assert_eq!(starts.load(std::sync::atomic::Ordering::SeqCst), 2);
        let _ = fs::remove_dir_all(directory);
    }

    /// A fake Host: answers each frame with its own operation byte; op 8
    /// sleeps one second first (a slow request); op 9 exits instead. Every
    /// operation that reaches it is appended to `$MINI_FAKE_HOST_LOG`.
    const FAKE_HOST: &str = r#"while n=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 | tr -d ' \n'); [ -n "$n" ]; do
  op=$(dd bs=1 count=1 2>/dev/null | od -An -tu1 | tr -d ' \n')
  [ "$n" -gt 1 ] && dd bs=1 count=$((n - 1)) of=/dev/null 2>/dev/null
  echo "$op" >> "$MINI_FAKE_HOST_LOG"
  [ "$op" = 9 ] && exit 3
  [ "$op" = 8 ] && sleep 1
  printf '\001\000\000\000'; printf "\\$(printf %03o "$op")"
done"#;

    struct FakeService {
        directory: std::path::PathBuf,
        socket: std::path::PathBuf,
        config: std::path::PathBuf,
    }

    impl Drop for FakeService {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.directory);
        }
    }

    fn fake_service(name: &str, bounds: ServeBounds) -> FakeService {
        let directory = std::env::temp_dir().join(format!(
            "mini-{name}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        let socket = directory.join("test.sock");
        let config = directory.join("config.json");
        fs::write(&config, b"config").unwrap();
        let log = directory.join("host.log");
        fs::write(&log, b"").unwrap();
        let listener = UnixListener::bind(&socket).unwrap();
        thread::spawn(move || {
            let mut start = || {
                HostProcess::start(
                    Command::new("/bin/sh")
                        .arg("-c")
                        .arg(FAKE_HOST)
                        .env("MINI_FAKE_HOST_LOG", &log),
                    "fake",
                )
            };
            let rules = EnvelopeRules {
                operator: None,
                config_bytes: b"config",
                host_sha256: &[0; 32],
                catalog_enabled: false,
                read_deadline: bounds.read_deadline,
            };
            let _ = supervise_bounded(&listener, &rules, bounds, &mut start);
        });
        FakeService {
            directory,
            socket,
            config,
        }
    }

    impl FakeService {
        /// Every operation the fake Host actually received, in order.
        fn forwarded(&self) -> Vec<u8> {
            fs::read_to_string(self.directory.join("host.log"))
                .unwrap()
                .lines()
                .map(|line| line.parse().unwrap())
                .collect()
        }

        fn invoke_later(&self, operation: u8) -> thread::JoinHandle<Result<Vec<u8>, String>> {
            let socket = self.socket.clone();
            let config = self.config.clone();
            thread::spawn(move || invoke(&socket, &config, operation, &[]))
        }
    }

    fn timed_invoke(service: &FakeService, operation: u8) -> (Result<Vec<u8>, String>, Duration) {
        let started = Instant::now();
        let result = invoke(&service.socket, &service.config, operation, &[]);
        (result, started.elapsed())
    }

    /// A client that sends three bytes of a frame and stalls holds its own
    /// connection only: another client is answered at once, and the staller
    /// is refused by name at its deadline.
    #[test]
    fn serve_a_trickling_client_holds_no_one_else() {
        let service = fake_service(
            "trickle",
            ServeBounds {
                read_deadline: Duration::from_secs(3),
                max_connections: 8,
                host_queue: 4,
                queue_residence: Duration::from_secs(60),
            },
        );
        let mut staller = UnixStream::connect(&service.socket).unwrap();
        staller.write_all(&[9, 0, 0]).unwrap();
        let (answer, waited) = timed_invoke(&service, 3);
        assert_eq!(answer.unwrap(), vec![3]);
        assert!(waited < Duration::from_secs(1), "honest client waited {waited:?}");
        let refusal = read_frame(&mut DeadlinePipe {
            reader: &mut staller,
            deadline: Instant::now() + Duration::from_secs(5),
        })
        .unwrap()
        .unwrap();
        assert_eq!(refusal, b"\xfeinvalid socket frame: frame read deadline");
    }

    /// A slow Host request does not stop another client being read: it is
    /// queued and answered right after; beyond the queue bound a client is
    /// refused `busy` without waiting.
    #[test]
    fn serve_a_slow_request_queues_the_next_and_a_full_queue_is_busy() {
        let service = fake_service(
            "queue",
            ServeBounds {
                read_deadline: Duration::from_secs(2),
                max_connections: 8,
                host_queue: 1,
                queue_residence: Duration::from_secs(60),
            },
        );
        let slow = {
            let socket = service.socket.clone();
            let config = service.config.clone();
            thread::spawn(move || invoke(&socket, &config, 8, &[]))
        };
        thread::sleep(Duration::from_millis(200));
        let queued = {
            let socket = service.socket.clone();
            let config = service.config.clone();
            thread::spawn(move || {
                let started = Instant::now();
                (invoke(&socket, &config, 3, &[]), started.elapsed())
            })
        };
        thread::sleep(Duration::from_millis(200));
        let (busy, waited) = timed_invoke(&service, 5);
        assert_eq!(busy.unwrap_err(), "socket rejected request: busy: host queue full");
        assert!(waited < Duration::from_secs(1), "busy refusal waited {waited:?}");
        assert_eq!(slow.join().unwrap().unwrap(), vec![8]);
        let (answer, waited) = queued.join().unwrap();
        assert_eq!(answer.unwrap(), vec![3]);
        assert!(waited < Duration::from_secs(3), "queued client waited {waited:?}");
        assert_eq!(timed_invoke(&service, 5).0.unwrap(), vec![5]);
    }

    /// Idle connections up to the bound cost the others nothing; one beyond
    /// it is refused `busy: connection limit`, and each idle one is refused
    /// by name at its deadline, freeing its slot.
    #[test]
    fn serve_idle_connections_are_bounded_and_named() {
        let service = fake_service(
            "idle",
            ServeBounds {
                read_deadline: Duration::from_secs(3),
                max_connections: 6,
                host_queue: 4,
                queue_residence: Duration::from_secs(60),
            },
        );
        let idle: Vec<UnixStream> = (0..5)
            .map(|_| UnixStream::connect(&service.socket).unwrap())
            .collect();
        thread::sleep(Duration::from_millis(100));
        let (answer, waited) = timed_invoke(&service, 3);
        assert_eq!(answer.unwrap(), vec![3]);
        assert!(waited < Duration::from_secs(1), "honest client waited {waited:?}");
        // The honest connection's slot is released just after its reply is
        // written; let that happen before filling the last slot.
        thread::sleep(Duration::from_millis(300));
        let extra: Vec<UnixStream> = (0..1)
            .map(|_| UnixStream::connect(&service.socket).unwrap())
            .collect();
        thread::sleep(Duration::from_millis(100));
        assert_eq!(
            timed_invoke(&service, 3).0.unwrap_err(),
            "socket rejected request: busy: connection limit"
        );
        for mut stream in idle.into_iter().chain(extra) {
            let refusal = read_frame(&mut DeadlinePipe {
                reader: &mut stream,
                deadline: Instant::now() + Duration::from_secs(5),
            })
            .unwrap()
            .unwrap();
            assert_eq!(refusal, b"\xfeinvalid socket frame: frame read deadline");
        }
        thread::sleep(Duration::from_millis(100));
        assert_eq!(timed_invoke(&service, 3).0.unwrap(), vec![3]);
    }

    /// A client that sends a whole request and never reads the reply does not
    /// hold the Host: the next request is answered.
    #[test]
    fn serve_a_client_that_never_reads_holds_no_one_else() {
        let service = fake_service("noread", SERVE_BOUNDS);
        let mut silent = UnixStream::connect(&service.socket).unwrap();
        write_frame(&mut silent, &[[1, 6, 0, 0, 0].as_slice(), b"config", &[3]].concat()).unwrap();
        let (answer, waited) = timed_invoke(&service, 5);
        assert_eq!(answer.unwrap(), vec![5]);
        assert!(waited < Duration::from_secs(1), "honest client waited {waited:?}");
        drop(silent);
    }

    /// A caller that queues a request behind a slow one and then hangs up is
    /// never forwarded: the Host sees the slow request and the next live one,
    /// and nothing in between.
    #[test]
    fn serve_a_queued_abandoned_request_never_reaches_the_host() {
        let service = fake_service(
            "abandon",
            ServeBounds {
                read_deadline: Duration::from_secs(2),
                max_connections: 8,
                host_queue: 4,
                queue_residence: Duration::from_secs(60),
            },
        );
        let slow = service.invoke_later(8);
        thread::sleep(Duration::from_millis(200));
        let mut abandoned = UnixStream::connect(&service.socket).unwrap();
        write_frame(&mut abandoned, &[[1, 6, 0, 0, 0].as_slice(), b"config", &[7]].concat()).unwrap();
        thread::sleep(Duration::from_millis(200));
        drop(abandoned);
        assert_eq!(slow.join().unwrap().unwrap(), vec![8]);
        assert_eq!(timed_invoke(&service, 5).0.unwrap(), vec![5]);
        assert_eq!(service.forwarded(), vec![8, 5]);
    }

    /// A live caller whose request outwaits the residence deadline gets the
    /// certain 254 refusal, and the request is not forwarded afterwards.
    #[test]
    fn serve_a_request_past_queue_residence_is_refused_254_unforwarded() {
        let service = fake_service(
            "residence",
            ServeBounds {
                read_deadline: Duration::from_secs(2),
                max_connections: 8,
                host_queue: 4,
                queue_residence: Duration::from_millis(300),
            },
        );
        let slow = service.invoke_later(8);
        thread::sleep(Duration::from_millis(200));
        let (late, waited) = timed_invoke(&service, 7);
        assert_eq!(late.unwrap_err(), "socket rejected request: busy: queue residence deadline");
        assert!(waited < Duration::from_secs(2), "refusal waited {waited:?}");
        assert_eq!(slow.join().unwrap().unwrap(), vec![8]);
        assert_eq!(timed_invoke(&service, 5).0.unwrap(), vec![5]);
        assert_eq!(service.forwarded(), vec![8, 5]);
    }

    /// 254 is answered only for requests never written to the Host: a request
    /// whose Host exchange outlasts the residence deadline still gets its
    /// reply, every 254 corresponds to an operation absent from the Host's
    /// log, and every reply to one present in it.
    #[test]
    fn serve_refuses_254_only_before_forward() {
        let service = fake_service(
            "before-forward",
            ServeBounds {
                read_deadline: Duration::from_secs(2),
                max_connections: 16,
                host_queue: 8,
                queue_residence: Duration::from_millis(500),
            },
        );
        let slow = service.invoke_later(8);
        thread::sleep(Duration::from_millis(100));
        let queued: Vec<_> = [1u8, 2, 3, 4]
            .into_iter()
            .map(|operation| (operation, service.invoke_later(operation)))
            .collect();
        let mut abandoned = UnixStream::connect(&service.socket).unwrap();
        write_frame(&mut abandoned, &[[1, 6, 0, 0, 0].as_slice(), b"config", &[6]].concat()).unwrap();
        thread::sleep(Duration::from_millis(100));
        drop(abandoned);
        // The slow exchange itself lasts twice the residence deadline.
        assert_eq!(slow.join().unwrap().unwrap(), vec![8]);
        let mut outcomes = vec![(8u8, true)];
        for (operation, handle) in queued {
            match handle.join().unwrap() {
                Ok(reply) => {
                    assert_eq!(reply, vec![operation]);
                    outcomes.push((operation, true));
                }
                Err(error) => {
                    assert!(error.starts_with("socket rejected request: "), "{error}");
                    outcomes.push((operation, false));
                }
            }
        }
        assert_eq!(timed_invoke(&service, 10).0.unwrap(), vec![10]);
        outcomes.push((10, true));
        let forwarded = service.forwarded();
        assert!(!forwarded.contains(&6), "abandoned request reached the Host");
        for (operation, answered) in outcomes {
            assert_eq!(forwarded.contains(&operation), answered, "operation {operation}");
        }
        // These four waited behind a one-second exchange with a 500 ms bound.
        assert_eq!(forwarded, vec![8, 10]);
    }

    fn envelope_for(request: &[u8]) -> Vec<u8> {
        let mut envelope = vec![1];
        envelope.extend_from_slice(&6u32.to_le_bytes());
        envelope.extend_from_slice(b"config");
        envelope.extend_from_slice(request);
        envelope
    }

    fn author_request(body_length: usize) -> Vec<u8> {
        let mut request = vec![7];
        request.resize(1 + body_length, b' ');
        request
    }

    /// Every operation's body has its own bound, named, and judged before the
    /// Host sees a byte: the byte proxy and the serving socket share it.
    #[test]
    fn operation_bodies_have_named_bounds_on_the_public_envelope() {
        let judge = |request: &[u8]| public_envelope(&envelope_for(request), b"config", false);
        // Op 7: the bound is the largest legitimate source plus its kind frame.
        assert_eq!(judge(&author_request(AUTHOR_BODY_MAX)), Ok(()));
        assert_eq!(
            judge(&author_request(AUTHOR_BODY_MAX + 1)),
            Err("author request body exceeds its bound")
        );
        // The measured worst case: a 12 MB op 7 body.
        assert_eq!(
            judge(&author_request(HOST_MAX_FRAME - 1)),
            Err("author request body exceeds its bound")
        );
        // Op 9: a list of at most four signatures.
        let mut signatures = vec![9];
        signatures.resize(1 + SIGNATURES_BODY_MAX, b' ');
        assert_eq!(judge(&signatures), Ok(()));
        signatures.push(b' ');
        assert_eq!(judge(&signatures), Err("signatures request body exceeds its bound"));
        // Ops 0 and 6 take no payload.
        assert_eq!(judge(&[0]), Ok(()));
        assert_eq!(judge(&[6]), Ok(()));
        assert_eq!(judge(&[0, 1]), Err("operation takes no request body"));
        assert_eq!(judge(&[6, 0]), Err("operation takes no request body"));
        // Op 8 (inspect) and the state-touching operations keep the frame bound.
        assert_eq!(judge(&[8, 1, 2, 3]), Ok(()));
    }

    /// An oversized author body is refused by name at the serving socket, never
    /// reaches the Host, and the service answers the next request.
    #[test]
    fn serve_refuses_an_oversized_author_body_by_name_and_serves_on() {
        let service = fake_service(
            "author-bound",
            ServeBounds {
                read_deadline: Duration::from_secs(10),
                max_connections: 8,
                host_queue: 4,
                queue_residence: Duration::from_secs(60),
            },
        );
        let oversized = vec![b' '; AUTHOR_BODY_MAX + 1];
        let refused = invoke(&service.socket, &service.config, 7, &oversized).unwrap_err();
        assert_eq!(
            refused,
            "socket rejected request: author request body exceeds its bound"
        );
        assert_eq!(timed_invoke(&service, 5).0.unwrap(), vec![5]);
        assert_eq!(
            invoke(&service.socket, &service.config, 7, &vec![b' '; 1024]).unwrap(),
            vec![7]
        );
        assert_eq!(service.forwarded(), vec![5, 7]);
    }

    /// The Host-time budget is by operation: the pure source-owned operations
    /// get far less than a state-touching one, and a request that outlives its
    /// budget is cut off with the Host's reply deadline, not left for 600 s.
    #[test]
    fn host_time_budget_is_per_operation_and_cuts_off_a_slow_host() {
        for pure in [0u8, 6, 7, 8, 9, 10, 11] {
            assert_eq!(host_budget(&[pure]), HOST_PURE_OP_BUDGET, "op {pure}");
        }
        for state in [1u8, 2, 3, 4, 5, 20, 130, 153] {
            assert_eq!(host_budget(&[state]), HOST_STATE_OP_BUDGET, "op {state}");
        }
        assert!(HOST_PURE_OP_BUDGET < HOST_STATE_OP_BUDGET);
        let mut host = HostProcess::start(
            Command::new("/bin/sh")
                .arg("-c")
                .arg("dd bs=1 count=5 of=/dev/null 2>/dev/null; sleep 10"),
            "fake",
        )
        .unwrap();
        let started = Instant::now();
        let error = host
            .exchange_within(&[7], Duration::from_millis(400))
            .unwrap_err();
        assert!(error.contains("deadline"), "{error}");
        assert!(started.elapsed() < Duration::from_secs(5), "waited {:?}", started.elapsed());
    }

    fn queued_job(marker: u8) -> (HostJob, mpsc::Receiver<Vec<u8>>) {
        let (reply, answer) = mpsc::sync_channel(1);
        let job = HostJob {
            request: vec![marker],
            reply,
            queued: Instant::now(),
            caller: None,
        };
        (job, answer)
    }

    /// With the queue full of one peer's jobs, another peer is not refused
    /// `busy: host queue full`: it takes a slot, and the fuller peer's newest
    /// job is answered with the certain 254 refusal, unforwarded.
    #[test]
    fn a_full_queue_displaces_the_fullest_peer_with_a_certain_refusal() {
        let (jobs, mut queue) = fair_queue::<HostJob>(3);
        let mut answers = Vec::new();
        for marker in [1u8, 2, 3] {
            let (job, answer) = queued_job(marker);
            assert!(queue_job(&jobs, 1000, job).is_ok());
            answers.push(answer);
        }
        // The same peer cannot grow past the bound.
        let (job, _) = queued_job(9);
        assert!(matches!(queue_job(&jobs, 1000, job), Err(TrySendError::Full(_))));
        // Another peer is admitted; peer 1000's newest job (3) is refused.
        let (job, _answer) = queued_job(4);
        assert!(queue_job(&jobs, 2000, job).is_ok());
        assert_eq!(
            answers[2].try_recv().unwrap(),
            refusal_frame("busy: host queue share displaced")
        );
        assert!(answers[0].try_recv().is_err() && answers[1].try_recv().is_err());
        // The Host thread serves the two peers in turn; 3 never reaches it.
        drop(jobs);
        let order: Vec<u8> = queue.by_ref().map(|job| job.request[0]).collect();
        assert_eq!(order, vec![1, 4, 2]);
    }

    #[test]
    fn host_pipe_deadline_bounds_missing_reply() {
        let (mut receiver, _writer) = UnixStream::pair().unwrap();
        let error = read_frame(&mut DeadlinePipe {
            reader: &mut receiver,
            deadline: Instant::now() + Duration::from_millis(20),
        })
        .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::TimedOut);
    }

    #[test]
    fn host_pipe_deadline_bounds_stalled_request_write() {
        let (mut writer, _reader) = UnixStream::pair().unwrap();
        set_nonblocking(&writer).unwrap();
        let error = write_frame(
            &mut DeadlinePipeWrite {
                writer: &mut writer,
                deadline: Instant::now() + Duration::from_millis(20),
            },
            &vec![7; MAX_FRAME],
        )
        .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::TimedOut);
    }

    #[test]
    fn member_app_frames_are_bounded_and_private_preparation_stays_private() {
        fn pair(a:&[u8],b:&[u8])->Vec<u8> {
            let mut p=(a.len() as u32).to_le_bytes().to_vec();p.extend(a);p.extend(b);p
        }
        let mut reads=vec![5];
        for read in [4,3,2,1] {reads=pair(&[read],&reads);}
        let plan=pair(&[1],&pair(&[7;64],&reads));
        let mut frame=vec![194];frame.extend(plan.clone());
        assert!(allowed_operation(&frame,false));
        let mut short=vec![194];short.extend(pair(&[1],&pair(&[7;63],&reads)));
        assert!(!allowed_operation(&short,false));
        let mut missing=vec![194];missing.extend(pair(&[1],&pair(&[7;64],&[5])));
        assert!(!allowed_operation(&missing,false));
        let mut empty=vec![194];empty.extend(pair(&[],&pair(&[7;64],&reads)));
        assert!(!allowed_operation(&empty,false));
        let mut ready=vec![193];ready.extend(pair(&[1],&[2]));
        assert!(allowed_operation(&ready,false));
        assert!(!allowed_operation(&[193,1],false));
        assert!(!allowed_operation(&[36,1],false));
        assert!(!allowed_operation(&[37,1],false));
    }
    #[test]
    fn public_fn_operations_have_no_path_payload() {
        assert!(allowed_operation(&[12], false));
        assert!(!allowed_operation(&[12, b'/'], false));
        assert!(allowed_operation(&[13, b'0'], false));
        assert!(allowed_operation(&[13, b'1', b'2', b'3'], false));
        assert!(!allowed_operation(&[13], false));
        assert!(!allowed_operation(&[13, b'0', b'1'], false));
        assert!(!allowed_operation(&[13, b'1', b'/'], false));
        assert!(allowed_operation(&[14], false));
        assert!(!allowed_operation(&[14, b'/'], false));
        assert!(allowed_operation(&[15, b'2'], false));
        assert!(!allowed_operation(&[15, b'0', b'2'], false));
        assert!(!allowed_operation(&[16, b'R'], false));
        assert!(!allowed_operation(&[16], true));
        assert!(allowed_operation(&[16, b'R'], true));
        assert!(allowed_operation(&[18, b'1'], true));
        assert!(!allowed_operation(&[18, b'1'], false));
        assert!(!allowed_operation(&[18, b'/'], true));
        assert!(allowed_operation(&[17, 1, 0, 0, 0, b'C', b'O'], false));
        assert!(!allowed_operation(&[17, 0, 0, 0, 0, b'O'], false));
        assert!(!allowed_operation(&[17, 1, 0, 0, 0, b'C'], false));
        let mut oversized = vec![b'R'; 1_516_386];
        oversized[0] = 16;
        assert!(!allowed_operation(&oversized, true));
    }

    #[test]
    fn metering_requires_complete_bounded_byte_triple() {
        let mut frame = vec![19];
        frame.extend(2u32.to_le_bytes());
        frame.extend(b"{}");
        frame.extend(3u32.to_le_bytes());
        frame.extend(b"req");
        frame.extend(b"response");
        assert!(allowed_operation(&frame, false));
        assert!(!allowed_operation(&frame[..frame.len() - 8], false));
        let mut oversized = frame.clone();
        oversized[1..5].copy_from_slice(&4097u32.to_le_bytes());
        assert!(!allowed_operation(&oversized, false));
        let mut missing_request = frame;
        missing_request[7..11].copy_from_slice(&0u32.to_le_bytes());
        assert!(!allowed_operation(&missing_request, false));
        assert!(allowed_operation(&[20, 1], false));
        assert!(allowed_operation(&[21, 1], false));
        assert!(!allowed_operation(&[20], false));
        assert!(!allowed_operation(&[21], false));
    }

    #[test]
    fn carried_lookup_keeps_full_old_call_capacity_with_narrow_frame_exception() {
        let mut header =
            br#"{"algorithm":"minidregg-carried-call-lookup-v1","originIdentity":{}}"#.to_vec();
        header.resize(1024, b' ');
        let mut request = vec![153];
        request.extend_from_slice(&(header.len() as u32).to_le_bytes());
        request.extend(&header);
        request.resize(CARRIED_LOOKUP_MAX_FRAME, 7);
        assert_eq!(request.len() - 1 - 4 - header.len(), MAX_CARRIED_CALL);
        assert!(request_within_bound(&request));
        assert!(allowed_operation(&request, false));
        assert!(allowed_operator_operation(&request));
        let config = vec![b'x'; MAX_CONFIG];
        let mut envelope = vec![2];
        envelope.extend_from_slice(&(config.len() as u32).to_le_bytes());
        envelope.extend(&config);
        envelope.extend_from_slice(&[0; 32]);
        envelope.extend(&request);
        assert_eq!(envelope.len(), MAX_FRAME);
        assert!(public_envelope(&envelope, &config, false).is_ok());
        let mut framed = Vec::new();
        write_frame(&mut framed, &envelope).unwrap();
        assert_eq!(
            read_frame(&mut std::io::Cursor::new(&framed))
                .unwrap()
                .unwrap(),
            envelope
        );
        request.push(7);
        assert!(!request_within_bound(&request));
        assert!(!allowed_operation(&request, false));
        assert!(!allowed_operator_operation(&request));
        let oversized = ((MAX_FRAME + 1) as u32).to_le_bytes();
        assert!(read_frame(&mut oversized.as_slice()).is_err());
        // The ordinary call opcode retains exactly its old body limit.
        let mut ordinary = vec![3; HOST_MAX_FRAME];
        assert!(request_within_bound(&ordinary));
        ordinary.push(1);
        assert!(!request_within_bound(&ordinary));
        for header in [
            br#"[]"#.as_slice(),
            br#"{"algorithm":"wrong","originIdentity":{}}"#,
            br#"{"algorithm":"minidregg-carried-call-lookup-v1"}"#,
        ] {
            let mut bad = vec![153];
            bad.extend_from_slice(&(header.len() as u32).to_le_bytes());
            bad.extend(header);
            bad.push(1);
            assert!(!allowed_operation(&bad, false));
            assert!(!allowed_operator_operation(&bad));
        }
    }

    #[test]
    fn provider_continuity_source_frames_reach_native_api17() {
        for (fence, v2) in [(None, false), (None, true), (Some((&b"fence-call"[..], &b"fence-outcome"[..])), true)] {
            let payload = crate::provider_continuity::request_payload(b"reserve-call", b"reserve-outcome", fence, v2).unwrap();
            let frame = [vec![17], payload.clone()].concat();
            assert!(allowed_operation(&frame, false));
            if v2 {
                let previous = serde_json::json!({"checkedAcceptedCount":"7","checkedWorldRoot":"42"});
                let resolved = crate::provider_continuity::resolution_payload(&payload, &previous).unwrap();
                assert!(allowed_operation(&[vec![17], resolved.clone()].concat(), false));
                // The final root is the second word of an exact pair, without
                // its own length prefix. Dropping only '2' from '42' produces
                // the well-framed root '4'; the Host must reject its history,
                // not the ingress. Truncating the entire root is malformed.
                assert!(!allowed_operation(&[vec![17], resolved[..resolved.len()-2].to_vec()].concat(), false));
                let mut noncanonical = resolved.clone();
                let end = noncanonical.len();
                noncanonical[end-2..].copy_from_slice(b"04");
                assert!(!allowed_operation(&[vec![17], noncanonical].concat(), false));
                let mut trailing = resolved;
                trailing.push(0);
                assert!(!allowed_operation(&[vec![17], trailing].concat(), false));
            }
            // Removing the final fence/outcome or truncating the v2 envelope
            // cannot become a generic allowed operation.
            assert!(!allowed_operation(&frame[..5], false));
        }
        let oversized = crate::provider_continuity::request_payload(b"call", &vec![0; 1025], None, true).unwrap();
        assert!(!allowed_operation(&[vec![17], oversized].concat(), false));
        let empty = crate::provider_continuity::request_payload(b"", b"outcome", None, true).unwrap();
        assert!(!allowed_operation(&[vec![17], empty].concat(), false));
        let mut malformed = crate::provider_continuity::request_payload(b"call", b"outcome", None, true).unwrap();
        malformed.extend_from_slice(&[1, 0, 0, 0, 1]);
        assert!(!allowed_operation(&[vec![17], malformed].concat(), false));
    }

    #[test]
    fn receipt_continuity_accepts_only_bounded_json_objects_on_both_sockets() {
        let mut valid = vec![151];
        valid.extend_from_slice(br#"{"identity":{},"from":null,"target":{"height":"1","worldRoot":"2"}}"#);
        assert!(allowed_operation(&valid, false));
        assert!(allowed_operator_operation(&valid));
        for payload in [b"".as_slice(), b"[]", b"{", b"/tmp/request.json"] {
            let frame = [vec![151], payload.to_vec()].concat();
            assert!(!allowed_operation(&frame, false));
            assert!(!allowed_operator_operation(&frame));
        }
        let oversized = [vec![151, b'{'], vec![b' '; 64 * 1024], vec![b'}']].concat();
        assert!(!allowed_operation(&oversized, false));
        assert!(!allowed_operator_operation(&oversized));
    }

    #[test]
    fn current_birth_authoring_accepts_only_bounded_json_objects() {
        assert!(allowed_operation(&[30, b'{', b'}'], false));
        assert!(allowed_operation(&[31, b'{', b'}'], false));
        let mut observed_resource = vec![91];
        observed_resource.extend_from_slice(&1u32.to_le_bytes());
        observed_resource.push(b'O');
        observed_resource.extend_from_slice(b"{}");
        assert!(allowed_operation(&observed_resource, false));
        assert!(!allowed_operation(&[30, b'[', b']'], false));
        assert!(!allowed_operation(&[31, b'{'], false));
        assert!(!allowed_operation(&[91, b'{', b'}'], false));
        let mut oversized = vec![b' '; 256 * 1024 + 2];
        oversized[0] = 30;
        oversized[1] = b'{';
        *oversized.last_mut().unwrap() = b'}';
        assert!(!allowed_operation(&oversized, false));
        let mut oversized_birth = vec![91];
        oversized_birth.extend_from_slice(&1u32.to_le_bytes());
        oversized_birth.push(b'O');
        let mut source = vec![b' '; 4 * 1024 * 1024 + 1];
        source[0] = b'{';
        *source.last_mut().unwrap() = b'}';
        oversized_birth.extend_from_slice(&source);
        assert!(!allowed_operation(&oversized_birth, false));
    }

    #[test]
    fn nock_program_reads_are_public() {
        // Renumbered at the final merge: 117-123 -> 131-137.
        assert!(allowed_operation(&[131, 0, 0, 0, 0], false));
        assert!(allowed_operation(&[132, b'7'], false));
        assert!(allowed_operation(&[133, b'{', b'}'], false));
        assert!(allowed_operation(&[134, b'{', b'}'], false));
        assert!(allowed_operation(&[135, b'{', b'}'], false));
        assert!(allowed_operation(&[136, b'{', b'}'], false));
        assert!(allowed_operation(&[137, b'{', b'}'], false));
        assert!(!allowed_operation(&[138, b'{', b'}'], false));
    }

    #[test]
    fn participant_enrollment_uses_strict_pairs_on_public_and_operator_sockets() {
        let mut plan = vec![86];
        plan.extend_from_slice(&1u32.to_le_bytes());
        plan.extend_from_slice(b"SC");
        assert!(allowed_operator_operation(&plan));
        assert!(allowed_operation(&plan, false));
        assert!(!allowed_operator_operation(&[86, 1, 0, 0, 0, b'S']));
        assert!(!allowed_operation(&[86, 1, 0, 0, 0, b'S'], false));

        let mut signatures = Vec::new();
        signatures.extend_from_slice(&64u32.to_le_bytes());
        signatures.extend_from_slice(&[1u8; 64]);
        signatures.extend_from_slice(&[2u8; 64]);
        let mut seal = vec![87];
        seal.extend_from_slice(&1u32.to_le_bytes());
        seal.push(b'P');
        seal.extend_from_slice(&signatures);
        assert!(allowed_operator_operation(&seal));
        assert!(allowed_operation(&seal, false));
        seal.pop();
        assert!(!allowed_operator_operation(&seal));
        assert!(!allowed_operation(&seal, false));
        // A pre-rotated record: possession, then the next key and its co-signature.
        let mut signatures = Vec::new();
        signatures.extend_from_slice(&64u32.to_le_bytes());
        signatures.extend_from_slice(&[1u8; 64]);
        signatures.extend_from_slice(&[2u8; 160]);
        let mut seal = vec![87];
        seal.extend_from_slice(&1u32.to_le_bytes());
        seal.push(b'P');
        seal.extend_from_slice(&signatures);
        assert!(allowed_operator_operation(&seal));
        assert!(allowed_operation(&seal, false));
        for operation in [88, 89] {
            assert!(allowed_operator_operation(&[operation, b'I']));
            assert!(!allowed_operator_operation(&[operation]));
            assert!(allowed_operation(&[operation, b'I'], false));
        }
    }

    #[test]
    fn factory_observation_provisioning_uses_strict_pairs_and_one_signature() {
        let mut plan = vec![92];
        plan.extend_from_slice(&1u32.to_le_bytes());
        plan.extend_from_slice(b"SC");
        assert!(allowed_operator_operation(&plan));
        assert!(allowed_operation(&plan, false));
        assert!(!allowed_operation(&[92, 1, 0, 0, 0, b'S'], false));

        let mut seal = vec![93];
        seal.extend_from_slice(&1u32.to_le_bytes());
        seal.push(b'P');
        seal.extend_from_slice(&[1u8; 64]);
        assert!(allowed_operator_operation(&seal));
        assert!(allowed_operation(&seal, false));
        seal.pop();
        assert!(!allowed_operator_operation(&seal));
        assert!(!allowed_operation(&seal, false));
        seal.extend_from_slice(&[1u8; 2]);
        assert!(!allowed_operation(&seal, false));
        for operation in [94, 95] {
            assert!(allowed_operator_operation(&[operation, b'I']));
            assert!(!allowed_operator_operation(&[operation]));
            assert!(allowed_operation(&[operation, b'I'], false));
            assert!(!allowed_operation(&[operation], false));
        }
    }

    #[test]
    fn unsigned_share_issue_plan_stays_off_public_socket() {
        let mut assembly = vec![33];
        assembly.extend(1u32.to_le_bytes());
        assembly.extend(*b"PS");
        for request in [&[32, 1][..], assembly.as_slice()] {
            assert!(!allowed_operation(request, false));
            assert!(allowed_operator_operation(request));
        }
        assert!(!allowed_operator_operation(&[32]));
        assert!(!allowed_operator_operation(&[33, 1, 0, 0, 0, b'P']));
        assert!(!allowed_operator_operation(&[30, b'{', b'}']));
    }

    #[test]
    fn session_enrollment_is_private_and_pair_framed() {
        for operation in [82, 84, 85] {
            assert!(allowed_operator_operation(&[operation, 1]));
            assert!(!allowed_operator_operation(&[operation]));
            assert!(!allowed_operation(&[operation, 1], true));
        }
        let mut pair = vec![83];
        pair.extend_from_slice(&1u32.to_le_bytes());
        pair.extend_from_slice(b"PS");
        assert!(allowed_operator_operation(&pair));
        assert!(!allowed_operation(&pair, true));
        let mut empty_plan = pair.clone();
        empty_plan[1..5].copy_from_slice(&0u32.to_le_bytes());
        assert!(!allowed_operator_operation(&empty_plan));
        let mut missing_signatures = pair.clone();
        missing_signatures[1..5].copy_from_slice(&2u32.to_le_bytes());
        assert!(!allowed_operator_operation(&missing_signatures));
        let mut oversized = vec![83];
        oversized.extend_from_slice(&1u32.to_le_bytes());
        oversized.resize(HOST_MAX_FRAME + 1, 1);
        assert!(!allowed_operator_operation(&oversized));
    }

    #[test]
    fn dispatch_response_tags_require_exact_no_record_verdict() {
        let mut refused = vec![164];
        refused.extend_from_slice(b"DREGG/APPLICATION/DISPATCH-NO-RECORD-REFUSAL/v1");
        assert!(response_operation_matches(34, &refused));
        assert!(response_operation_matches(164, &[34, 1]));
        assert!(response_operation_matches(34, &[34, 1]));
        assert!(!response_operation_matches(152, &refused));
        refused.push(0);
        assert!(!response_operation_matches(34, &refused));
        assert!(!response_operation_matches(34, &[164]));
        assert!(!response_operation_matches(154, &[34, 1]));
        assert!(!response_operation_matches(34, &[]));
    }

    #[test]
    fn lifecycle_and_dispatch_routes_are_bounded_and_operator_only() {
        for operation in [22, 23, 26, 27, 34, 35, 38, 39, 152, 154, 164] {
            assert!(allowed_operator_operation(&[operation, 1]));
            assert!(!allowed_operation(&[operation, 1], true));
            assert!(!allowed_operator_operation(&[operation]));
        }
        let oversized = vec![1; HOST_MAX_FRAME];
        for operation in [22, 23, 26, 27, 34, 35, 38, 39, 152, 154, 164] {
            let mut request = vec![operation];
            request.extend_from_slice(&oversized);
            assert!(!allowed_operator_operation(&request));
        }

        let author = [36, 1];
        assert!(allowed_operator_operation(&author));
        assert!(!allowed_operation(&author, true));
        assert!(!allowed_operator_operation(&[36]));
        // ApplicationDispatchAdmission admits an 8 MiB HTTP body. Its
        // source-owned request envelope must fit above that body size.
        let mut large_author = vec![36];
        large_author.extend(vec![1; 8 * 1024 * 1024 + 4096]);
        assert!(allowed_operator_operation(&large_author));
        assert!(!allowed_operation(&large_author, true));
        large_author.resize(HOST_MAX_FRAME, 1);
        assert!(allowed_operator_operation(&large_author));
        large_author.push(1);
        assert!(!allowed_operator_operation(&large_author));

        let mut assembly = vec![37];
        assembly.extend(1u32.to_le_bytes());
        assembly.extend(*b"PS");
        assert!(allowed_operator_operation(&assembly));
        assert!(!allowed_operation(&assembly, true));
        assert!(!allowed_operator_operation(&[37, 1, 0, 0, 0, b'P']));
        let mut empty_plan = assembly.clone();
        empty_plan[1..5].copy_from_slice(&0u32.to_le_bytes());
        assert!(!allowed_operator_operation(&empty_plan));
        let mut missing_signatures = assembly;
        missing_signatures[1..5].copy_from_slice(&2u32.to_le_bytes());
        assert!(!allowed_operator_operation(&missing_signatures));

        // A private operator service is not a generic tunnel into the public
        // authoring, observation, or selected-release receiver operations.
        for operation in [0, 1, 7, 8, 20, 21, 24, 25, 30, 31] {
            assert!(!allowed_operator_operation(&[operation, 1]));
        }
    }

    #[test]
    fn namespace_and_lifecycle_authoring_routes_stay_private_and_bounded() {
        for operation in [40, 41] {
            assert!(allowed_operator_operation(&[operation, 1]));
            assert!(!allowed_operation(&[operation, 1], true));
            assert!(!allowed_operator_operation(&[operation]));
            let mut too_large = vec![operation];
            too_large.extend(vec![1; 8193]);
            assert!(!allowed_operator_operation(&too_large));
        }

        assert!(allowed_operator_operation(&[42]));
        assert!(!allowed_operator_operation(&[42, 1]));
        assert!(!allowed_operation(&[42], true));

        let mut namespace_assembly = vec![43];
        namespace_assembly.extend(1u32.to_le_bytes());
        namespace_assembly.extend(b"P");
        namespace_assembly.extend([0x5a; 64]);
        assert!(allowed_operator_operation(&namespace_assembly));
        assert!(!allowed_operation(&namespace_assembly, true));
        assert!(!allowed_operator_operation(&[43, 1, 0, 0, 0, b'P', 0x5a]));
        let mut empty_plan = namespace_assembly.clone();
        empty_plan[1..5].copy_from_slice(&0u32.to_le_bytes());
        assert!(!allowed_operator_operation(&empty_plan));
        let mut wrong_signature_length = namespace_assembly;
        wrong_signature_length[1..5].copy_from_slice(&2u32.to_le_bytes());
        assert!(!allowed_operator_operation(&wrong_signature_length));
        let mut oversized_plan_length = wrong_signature_length;
        oversized_plan_length[1..5].copy_from_slice(&8192u32.to_le_bytes());
        assert!(!allowed_operator_operation(&oversized_plan_length));

        assert!(allowed_operator_operation(&[44, 1]));
        assert!(!allowed_operator_operation(&[44]));
        assert!(!allowed_operation(&[44, 1], true));
        let mut completion_assembly = vec![45];
        completion_assembly.extend(1u32.to_le_bytes());
        completion_assembly.extend(*b"PS");
        assert!(allowed_operator_operation(&completion_assembly));
        assert!(!allowed_operation(&completion_assembly, true));
        assert!(!allowed_operator_operation(&[45, 1, 0, 0, 0, b'P']));

        assert!(allowed_operator_operation(&[50, 1]));
        assert!(!allowed_operator_operation(&[50]));
        assert!(!allowed_operation(&[50, 1], true));
        let mut begin_assembly = vec![51];
        begin_assembly.extend(1u32.to_le_bytes());
        begin_assembly.extend(*b"PS");
        assert!(allowed_operator_operation(&begin_assembly));
        assert!(!allowed_operation(&begin_assembly, true));
        assert!(!allowed_operator_operation(&[51, 1, 0, 0, 0, b'P']));

        assert!(allowed_operator_operation(&[52, 1]));
        assert!(!allowed_operator_operation(&[52]));
        assert!(!allowed_operation(&[52, 1], true));
        let mut claim_assembly = vec![53];
        claim_assembly.extend(1u32.to_le_bytes());
        claim_assembly.extend(*b"PS");
        assert!(allowed_operator_operation(&claim_assembly));
        assert!(!allowed_operation(&claim_assembly, true));
        assert!(!allowed_operator_operation(&[53, 1, 0, 0, 0, b'P']));

        for operation in [46, 47] {
            assert!(allowed_operator_operation(&[operation, 1]));
            assert!(!allowed_operator_operation(&[operation]));
            assert!(!allowed_operation(&[operation, 1], true));
        }

        for operation in [48, 58] {
            assert!(allowed_operator_operation(&[operation, 1]));
            assert!(!allowed_operator_operation(&[operation]));
            assert!(!allowed_operation(&[operation, 1], true));
        }
        for operation in [49, 59] {
            let mut assembly = vec![operation];
            assembly.extend(1u32.to_le_bytes());
            assembly.extend(*b"PS");
            assert!(allowed_operator_operation(&assembly));
            assert!(!allowed_operation(&assembly, true));
            assert!(!allowed_operator_operation(&[operation, 1, 0, 0, 0, b'P']));
        }

        for operation in [54, 55, 56] {
            assert!(allowed_operator_operation(&[operation, 1]));
            assert!(!allowed_operator_operation(&[operation]));
            assert!(!allowed_operation(&[operation, 1], true));
        }
        let mut grain_share_assembly = vec![57];
        grain_share_assembly.extend(1u32.to_le_bytes());
        grain_share_assembly.extend(*b"PS");
        assert!(allowed_operator_operation(&grain_share_assembly));
        assert!(!allowed_operation(&grain_share_assembly, true));
        assert!(!allowed_operator_operation(&[57, 1, 0, 0, 0, b'P']));

        for operation in [60, 61, 62, 63, 64, 66, 68, 70, 72, 73, 74, 76, 77, 78, 80] {
            assert!(allowed_operator_operation(&[operation, 1]));
            assert!(!allowed_operator_operation(&[operation]));
            assert!(!allowed_operation(&[operation, 1], true));
        }
        let mut fn_frontier_assembly = vec![65];
        fn_frontier_assembly.extend(1u32.to_le_bytes());
        fn_frontier_assembly.push(b'P');
        fn_frontier_assembly.extend([7u8; 64]);
        assert!(allowed_operator_operation(&fn_frontier_assembly));
        assert!(!allowed_operation(&fn_frontier_assembly, true));
        assert!(!allowed_operator_operation(&[65, 1, 0, 0, 0, b'P']));
        let mut launch_begin_assembly = vec![67];
        launch_begin_assembly.extend(1u32.to_le_bytes());
        launch_begin_assembly.extend(*b"PS");
        assert!(allowed_operator_operation(&launch_begin_assembly));
        assert!(!allowed_operation(&launch_begin_assembly, true));
        assert!(!allowed_operator_operation(&[67, 1, 0, 0, 0, b'P']));
        let mut launch_claim_assembly = vec![69];
        launch_claim_assembly.extend(1u32.to_le_bytes());
        launch_claim_assembly.extend(*b"PS");
        assert!(allowed_operator_operation(&launch_claim_assembly));
        assert!(!allowed_operation(&launch_claim_assembly, true));
        assert!(!allowed_operator_operation(&[69, 1, 0, 0, 0, b'P']));
        let mut launch_completion_assembly = vec![71];
        launch_completion_assembly.extend(1u32.to_le_bytes());
        launch_completion_assembly.extend(*b"PS");
        assert!(allowed_operator_operation(&launch_completion_assembly));
        assert!(!allowed_operation(&launch_completion_assembly, true));
        assert!(!allowed_operator_operation(&[71, 1, 0, 0, 0, b'P']));
        let mut grant_assembly = vec![75];
        grant_assembly.extend(1u32.to_le_bytes());
        grant_assembly.extend(*b"PS");
        assert!(allowed_operator_operation(&grant_assembly));
        assert!(!allowed_operation(&grant_assembly, true));
        assert!(!allowed_operator_operation(&[75, 1, 0, 0, 0, b'P']));
        for operation in [79, 81] {
            let mut assembly = vec![operation];
            assembly.extend(1u32.to_le_bytes());
            assembly.extend(*b"PS");
            assert!(allowed_operator_operation(&assembly));
            assert!(!allowed_operation(&assembly, true));
            assert!(!allowed_operator_operation(&[operation, 1, 0, 0, 0, b'P']));
            let mut oversized = vec![operation];
            oversized.resize(HOST_MAX_FRAME + 1, 0);
            assert!(!allowed_operator_operation(&oversized));
        }
    }

    #[test]
    fn service_mode_pin_refuses_public_to_operator_restart() {
        let directory = std::env::temp_dir().join(format!(
            "mini-service-mode-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
        let mode = directory.join("socket.mode");
        pin_service_mode(&mode, false, false).unwrap();
        pin_service_mode(&mode, false, true).unwrap();
        assert!(pin_service_mode(&mode, true, true).is_err());
        fs::remove_file(&mode).unwrap();
        assert!(pin_service_mode(&mode, true, true).is_err());
        pin_service_mode(&mode, true, false).unwrap();
        assert!(pin_service_mode(&mode, false, true).is_err());
        fs::remove_file(mode).unwrap();
        fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn service_restart_reuses_exact_pin_and_only_recovers_a_stale_socket() {
        let directory = std::env::temp_dir().join(format!(
            "mini-restart-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
        let lock_path = directory.join("host.lock");
        let first_lock = service_lock(&lock_path).unwrap();
        assert!(service_lock(&lock_path).is_err());
        drop(first_lock);
        let second_lock = service_lock(&lock_path).unwrap();
        let config = directory.join("host.config");
        pin_config(&config, b"fixed\n").unwrap();
        pin_config(&config, b"fixed\n").unwrap();
        assert!(pin_config(&config, b"drift\n").is_err());
        assert_eq!(fs::read(&config).unwrap(), b"fixed\n");

        let socket = directory.join("host.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        assert!(clear_stale_socket(&socket).is_err());
        drop(listener);
        clear_stale_socket(&socket).unwrap();
        assert!(!socket.exists());
        drop(second_lock);
        fs::remove_file(config).unwrap();
        fs::remove_file(lock_path).unwrap();
        fs::remove_dir(directory).unwrap();
    }
    #[test]
    fn pay_operations_are_public_and_shape_bounded() {
        for operation in [103u8, 105, 106, 108, 110, 111] {
            assert!(allowed_operation(&[operation, 1], false));
            assert!(!allowed_operation(&[operation], false));
        }
        assert!(allowed_operation(&[107], false));
        assert!(!allowed_operation(&[107, 0], false));
        for operation in [104u8, 109] {
            let mut pair = vec![operation, 1, 0, 0, 0, b'P'];
            pair.extend([7u8; 64]);
            assert!(allowed_operation(&pair, false));
            pair.pop();
            assert!(!allowed_operation(&pair, false));
            assert!(!allowed_operation(&[operation, 0, 0, 0, 0], false));
        }
        assert!(allowed_operation(&[112], false));
        assert!(!allowed_operation(&[112, 0], false));
        let oversized = [vec![108u8], vec![1; HOST_MAX_FRAME]].concat();
        assert!(!allowed_operation(&oversized, false));
        // The operator socket admits none of them: the pay rail is signed, not custodial.
        for operation in 103u8..=112 {
            assert!(!allowed_operator_operation(&[operation, 1]));
        }
    }
    #[test]
    fn paid_claim_public_routes_enforce_payload_boundaries() {
        for operation in [181u8, 182] {
            for enabled in [false, true] {
                for payload in [b"{}".as_slice(), b" { \"owner\": \"01\" } "] {
                    assert!(allowed_operation(&[&[operation], payload].concat(), enabled));
                }
                for payload in [
                    b"".as_slice(), b" ", b"{", b"[]", b"null", b"1", b"\"x\"",
                    b"{}{}", b"{} trailing", &[0xff],
                ] {
                    assert!(!allowed_operation(&[&[operation], payload].concat(), enabled));
                }
                let mut largest = vec![b' '; 4094];
                largest.extend_from_slice(b"{}");
                assert!(allowed_operation(&[&[operation], largest.as_slice()].concat(), enabled));
                largest.push(b' ');
                assert!(!allowed_operation(&[&[operation], largest.as_slice()].concat(), enabled));
            }
        }
        for (operation, limit) in [(183u8, 2048), (185, 4096), (186, 4096)] {
            assert!(!allowed_operation(&[operation], false));
            for length in [1, limit] {
                let request = [&[operation], vec![7; length].as_slice()].concat();
                assert!(allowed_operation(&request, false));
            }
            assert!(!allowed_operation(
                &[&[operation], vec![7; limit + 1].as_slice()].concat(), false,
            ));
        }
        // Neighboring unreserved numbers are not introduced as aliases.
        // 187 now belongs to key adoption; 191 remains reserved without a receiver.
        assert!(!allowed_operation(&[191, b'{', b'}'], false));
        assert!(!allowed_operation(&[188, 1], false));
    }

    fn claim_assembly(plan_length: usize, signature_length: usize) -> Vec<u8> {
        let mut request = vec![184];
        request.extend_from_slice(&(plan_length as u32).to_le_bytes());
        request.extend(vec![b'P'; plan_length]);
        request.extend(vec![7; signature_length]);
        request
    }

    #[test]
    fn paid_claim_assembly_requires_exact_bounded_pair() {
        for plan_length in [1, 3072] {
            let request = claim_assembly(plan_length, 64);
            assert!(allowed_operation(&request, false));
            for signature_length in [0, 1, 63, 65, 128] {
                assert!(!allowed_operation(
                    &claim_assembly(plan_length, signature_length), false,
                ));
            }
        }
        for plan_length in [0, 3073, 4096] {
            assert!(!allowed_operation(&claim_assembly(plan_length, 64), false));
        }
        for request in [
            vec![184], vec![184, 1], vec![184, 1, 0, 0],
            vec![184, 255, 255, 255, 255, 1],
            vec![184, 1, 0, 0, 0],
        ] {
            assert!(!allowed_operation(&request, false));
        }
        let mut truncated = claim_assembly(1, 64);
        truncated[1..5].copy_from_slice(&2u32.to_le_bytes());
        assert!(!allowed_operation(&truncated, false));
        let mut trailing = claim_assembly(1, 64);
        trailing.push(0);
        assert!(!allowed_operation(&trailing, false));
    }

    #[test]
    fn paid_claim_public_envelope_keeps_config_and_catalog_gates() {
        let config = b"public-config";
        for request in [
            vec![181, b'{', b'}'], vec![182, b'{', b'}'], vec![183, 1],
            claim_assembly(1, 64), vec![185, 1], vec![186, 1],
        ] {
            let mut envelope = vec![1];
            envelope.extend_from_slice(&(config.len() as u32).to_le_bytes());
            envelope.extend_from_slice(config);
            envelope.extend_from_slice(&request);
            assert!(public_envelope(&envelope, config, false).is_ok());
            assert!(public_envelope(&envelope, b"other-config", false).is_err());
        }
    }

    #[test]
    fn self_enrollment_quartet_is_operator_only_and_shape_bounded() {
        for operation in [117u8, 119, 120] {
            assert!(!allowed_operation(&[operation, 1], false));
            assert!(allowed_operator_operation(&[operation, 1]));
            assert!(!allowed_operator_operation(&[operation]));
        }
        let mut pair = vec![118u8, 1, 0, 0, 0, b'P'];
        pair.extend([7u8; 64]);
        assert!(!allowed_operation(&pair, false));
        assert!(allowed_operator_operation(&pair));
        pair.pop();
        assert!(!allowed_operator_operation(&pair));
        assert!(!allowed_operator_operation(&[118, 0, 0, 0, 0]));
        let oversized = [vec![119u8], vec![1; HOST_MAX_FRAME]].concat();
        assert!(!allowed_operator_operation(&oversized));
    }


    /// Common topology: a filtered public relay and private custodians converge
    /// on one private Host endpoint. Public routes must therefore be admitted by
    /// the private listener's union gate, while the relay still refuses 117-120.
    #[test]
    fn paid_public_relay_and_observer_share_current_private_host_gate() {
        let directory = std::env::temp_dir().join(format!(
            "mini-paid-private-{}-{}", std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)
                .unwrap().as_nanos()));
        fs::create_dir(&directory).unwrap();
        let socket = directory.join("private.sock");
        let config = directory.join("config.json");
        fs::write(&config, b"config").unwrap();
        let listener = UnixListener::bind(&socket).unwrap();
        let script = r#"count=0
while n=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 | tr -d ' \n'); [ -n "$n" ]; do
  op=$(dd bs=1 count=1 2>/dev/null | od -An -tu1 | tr -d ' \n')
  [ "$n" -gt 1 ] && dd bs=1 count=$((n - 1)) of=/dev/null 2>/dev/null
  [ "$op" = 9 ] && exit 3
  count=$((count + 1))
  printf '\002\000\000\000'
  printf "\\$(printf %03o "$op")\\$(printf %03o "$count")"
done"#;
        let service = thread::spawn(move || {
            let mut starts = 0;
            let mut start = || {
                starts += 1;
                if starts > 1 { return Err("fixture completed".to_owned()); }
                HostProcess::start(Command::new("/bin/sh").arg("-c").arg(script), "fake")
            };
            // This is the current connection/queue gate used by
            // supervise_operator, without starting a real drain/admin service.
            supervise(&listener, Some(&OperatorPeers::with(&[])), b"config", &[0;32], false, &mut start)
        });
        let envelope = |request: &[u8]| {
            let mut bytes = vec![1,6,0,0,0];
            bytes.extend_from_slice(b"config");
            bytes.extend_from_slice(request);
            bytes
        };
        let mut count = 0u8;
        for request in [
            vec![121,b'{',b'}'],vec![181,b'{',b'}'],vec![182,b'{',b'}'],
            vec![183,1],claim_assembly(1,64),vec![185,1],vec![186,1],
        ] {
            public_envelope(&envelope(&request), b"config", false).unwrap();
            assert!(invoke(&socket,&config,request[0],&[]).unwrap_err()
                .contains("operation unavailable"));
            count += 1;
            let reply = invoke(&socket,&config,request[0],&request[1..]);
            if crate::client_consent::plan_operation(request[0]) {
                // Transport admission is not permission to sign the fake
                // operator's one-byte plan: direct callers must check consent.
                assert!(reply.is_err(), "direct plan caller bypassed local consent");
            } else {
                assert_eq!(reply.unwrap(), vec![request[0],count]);
            }
        }
        let mut seal = claim_assembly(1,64);
        seal[0] = 118;
        for request in [vec![117,1],seal,vec![119,1],vec![120,1]] {
            assert!(public_envelope(&envelope(&request),b"config",false).is_err());
            count += 1;
            let reply = invoke(&socket,&config,request[0],&request[1..]);
            if crate::client_consent::plan_operation(request[0]) {
                // Transport admission is not permission to sign the fake
                // operator's one-byte plan: direct callers must check consent.
                assert!(reply.is_err(), "direct plan caller bypassed local consent");
            } else {
                assert_eq!(reply.unwrap(), vec![request[0],count]);
            }
        }
        // A catalog route must not acquire permission merely by reaching the
        // union gate of the private Host.
        assert!(invoke(&socket,&config,16,b"catalog").unwrap_err()
            .contains("operation unavailable"));
        assert!(invoke(&socket,&config,187,b"unknown").unwrap_err()
            .contains("operation unavailable"));
        count += 1;
        assert_eq!(invoke(&socket,&config,185,b"ingress").unwrap(),vec![185,count]);
        assert!(invoke(&socket,&config,9,&[]).unwrap_err().contains("uncertain"));
        assert_eq!(service.join().unwrap().unwrap_err(),"fixture completed");
        fs::remove_dir_all(directory).unwrap();
    }

}

#[cfg(test)]
mod bootstrap_deadline_tests {
    use super::*;
    struct Scratch(std::path::PathBuf);
    impl Scratch {
        fn new() -> Self {
            let path = std::path::PathBuf::from(format!(
                "/tmp/mdld-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            fs::create_dir(&path).unwrap();
            fs::write(path.join("config"), b"public-config").unwrap();
            Self(path)
        }
    }
    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    #[test]
    fn quote_gate_only_accepts_bounded_json_objects() {
        assert!(allowed_operation(
            &[vec![121], b"{}".to_vec()].concat(),
            false
        ));
        for bytes in [b"".as_slice(), b"{", b"[]", b"null"] {
            assert!(!allowed_operation(
                &[vec![121], bytes.to_vec()].concat(),
                false
            ));
        }
        let mut largest = vec![121, b'{', b'"', b'x', b'"', b':', b'"'];
        largest.extend(vec![b'a'; 4088]);
        largest.extend_from_slice(b"\"}");
        assert_eq!(largest.len(), 4097);
        assert!(allowed_operation(&largest, false));
        largest.insert(8, b'a');
        assert!(!allowed_operation(&largest, false));
        for op in 117..=120 {
            assert!(!allowed_operation(&[op, b'{', b'}'], false));
        }
    }
    #[test]
    fn deadline_exchange_keeps_v2_identity_and_operation_pin() {
        let scratch = Scratch::new();
        let socket = scratch.0.join("socket");
        let listener = UnixListener::bind(&socket).unwrap();
        let server = std::thread::spawn(move || {
            for reply_op in [121, 112] {
                let (mut stream, _) = listener.accept().unwrap();
                let frame = read_frame(&mut stream).unwrap().unwrap();
                assert_eq!(
                    request_from_envelope(&frame, b"public-config", &[0x11; 32]).unwrap(),
                    b"y{}"
                );
                write_frame(&mut stream, &[reply_op, b'{', b'}']).unwrap();
            }
        });
        assert_eq!(
            invoke_pinned_deadline(
                &socket,
                &scratch.0.join("config"),
                &"11".repeat(32),
                121,
                b"{}",
                Instant::now() + Duration::from_secs(2)
            )
            .unwrap(),
            b"y{}"
        );
        assert!(invoke_pinned_deadline(
            &socket,
            &scratch.0.join("config"),
            &"11".repeat(32),
            121,
            b"{}",
            Instant::now() + Duration::from_secs(2)
        )
        .unwrap_err()
        .contains("unexpected operation"));
        server.join().unwrap();
    }
    #[test]
    fn stalled_response_obeys_absolute_deadline() {
        let scratch = Scratch::new();
        let socket = scratch.0.join("socket");
        let listener = UnixListener::bind(&socket).unwrap();
        let server = std::thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            read_frame(&mut stream).unwrap().unwrap();
            std::thread::sleep(Duration::from_millis(350));
        });
        let start = Instant::now();
        assert!(invoke_pinned_deadline(
            &socket,
            &scratch.0.join("config"),
            &"11".repeat(32),
            121,
            b"{}",
            start + Duration::from_millis(60)
        )
        .unwrap_err()
        .contains("deadline"));
        assert!(start.elapsed() < Duration::from_millis(250));
        server.join().unwrap();
    }
    #[cfg(target_os = "linux")]
    #[test]
    fn saturated_unix_accept_backlog_cannot_escape_connect_deadline() {
        let scratch = Scratch::new();
        let socket = scratch.0.join("socket");
        let listener = UnixListener::bind(&socket).unwrap();
        assert_eq!(unsafe { libc::listen(listener.as_raw_fd(), 0) }, 0);
        let _queued = UnixStream::connect(&socket).unwrap();
        let start = Instant::now();
        let error = invoke_pinned_deadline(
            &socket,
            &scratch.0.join("config"),
            &"11".repeat(32),
            121,
            b"{}",
            start + Duration::from_millis(60),
        )
        .unwrap_err();
        assert!(
            error.contains("connect") && error.contains("deadline"),
            "{error}"
        );
        assert!(start.elapsed() < Duration::from_millis(250));
    }
    #[test]
    fn stalled_request_write_obeys_absolute_deadline() {
        let scratch = Scratch::new();
        let socket = scratch.0.join("socket");
        let listener = UnixListener::bind(&socket).unwrap();
        let server = std::thread::spawn(move || {
            let (_stream, _) = listener.accept().unwrap();
            std::thread::sleep(Duration::from_millis(350));
        });
        let start = Instant::now();
        let error = invoke_pinned_deadline(
            &socket,
            &scratch.0.join("config"),
            &"11".repeat(32),
            121,
            &vec![b'x'; HOST_MAX_FRAME - 1],
            start + Duration::from_millis(60),
        )
        .unwrap_err();
        assert!(
            error.contains("write") && error.contains("deadline"),
            "{error}"
        );
        assert!(start.elapsed() < Duration::from_millis(250));
        server.join().unwrap();
    }
}
