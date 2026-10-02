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

// Mirrors FnEvidenceCodec.maxHostFrameBytes; the host's length includes op byte.
pub(crate) const HOST_MAX_FRAME: usize = 12_102_760;
const MAX_CONFIG: usize = 65_536;
const MAX_FRAME: usize = HOST_MAX_FRAME + 5 + MAX_CONFIG + 32;

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
    if request.len() > HOST_MAX_FRAME {
        return Err("host frame exceeds bound");
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

fn allowed_operation(request: &[u8], catalog_enabled: bool) -> bool {
    match request {
        // Source-owned enrollment/renewal quote. Host/Json validates the fields;
        // ingress only bounds the JSON object before any backend exchange.
        [121, payload @ ..] => !payload.is_empty() && payload.len() <= 4096
            && serde_json::from_slice::<serde_json::Value>(payload).is_ok_and(|value| value.is_object()),
        [151, payload @ ..] => continuity_request(payload),
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
        [17, pair @ ..] if pair.len() >= 6 => {
            let call_length = u32::from_le_bytes(pair[..4].try_into().unwrap()) as usize;
            call_length > 0 && call_length < pair.len() - 4 && pair.len() - 4 - call_length <= 1024
        }
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
        // C-SAT-2 law-sat: one law-sat request (JSON); the Host reads no Store.
        [150, request @ ..] => !request.is_empty() && request.len() < HOST_MAX_FRAME,
        // Key pre-rotation: plan (one command), assembly (one plan and one raw
        // signature by the NEW key), submit/lookup (one ingress), status (one
        // JSON query). No current-key or sponsor signature participates.
        [140 | 142 | 143, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [141, pair @ ..] if pair.len() < HOST_MAX_FRAME => {
            exact_pair(pair).is_some_and(|(plan, signature)| !plan.is_empty() && signature.len() == 64)
        }
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
        [151, payload @ ..] => continuity_request(payload),
        [22 | 23 | 26 | 27 | 34 | 35 | 38 | 39 | 44 | 46 | 47 | 48 | 50 | 52 | 54 | 55 | 56 | 58
        | 66 | 68 | 70 | 72 | 73 | 74 | 76 | 77 | 78 | 80 | 82 | 84 | 85, payload @ ..] => {
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

pub(crate) fn service_lock(path: &Path) -> Result<fs::File, String> {
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
    Ok(file)
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
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(path)
                .map_err(|error| {
                    format!("cannot create pinned config {}: {error}", path.display())
                })?;
            file.write_all(bytes)
                .and_then(|()| file.sync_all())
                .map_err(|error| {
                    format!("cannot write pinned config {}: {error}", path.display())
                })?;
            fs::File::open(path.parent().ok_or("pinned config has no parent")?)
                .and_then(|directory| directory.sync_all())
                .map_err(|error| format!("cannot sync pinned config directory: {error}"))?;
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
    invoke_inner(socket, config, None, operation, payload)
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
    invoke_inner(socket, config, Some(&expected), operation, payload)
}

fn invoke_inner(
    socket: &Path,
    config: &Path,
    expected_host_sha256: Option<&[u8; 32]>,
    operation: u8,
    payload: &[u8],
) -> Result<Vec<u8>, String> {
    let config = read_config(config)?;
    if payload.len() >= HOST_MAX_FRAME {
        return Err("host request exceeds frame bound before transmission".to_owned());
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
    let reply = match endpoint(socket)? {
        Endpoint::Unix(path) => exchange_unix(path, &frame)?,
        Endpoint::Remote(destination) => crate::proxy::exchange(destination, &frame)?,
    };
    if reply.len() > HOST_MAX_FRAME {
        return Err("uncertain host response exceeds host frame bound".to_owned());
    }
    if reply[0] == 254 {
        return Err(format!(
            "socket rejected request: {}",
            String::from_utf8_lossy(&reply[1..])
        ));
    }
    if reply[0] != operation && reply[0] != 255 {
        return Err(format!(
            "uncertain host response: unexpected operation {}",
            reply[0]
        ));
    }
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
    serve_with_mode(socket, host, config, false)
}

pub fn serve_operator(socket: &Path, host: &Path, config: &Path) -> Result<(), String> {
    serve_with_mode(socket, host, config, true)
}

fn serve_with_mode(
    socket: &Path,
    host: &Path,
    config: &Path,
    operator: bool,
) -> Result<(), String> {
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
    let mut start = || {
        let mut command = Command::new(host);
        command.arg(&pinned_config).arg("stdio");
        HostProcess::start(&mut command, &host.display().to_string())
    };
    eprintln!("mini: serving {}", socket.display());
    if operator {
        return supervise_operator(listener, socket, &config_bytes, &host_sha256, catalog_enabled, &mut start);
    }
    supervise(
        &listener,
        operator,
        &config_bytes,
        &host_sha256,
        catalog_enabled,
        &mut start,
    )
}

/// One running Host and its two pipes. Dropping it kills and reaps the process.
struct HostProcess {
    child: std::process::Child,
    input: std::process::ChildStdin,
    output: std::process::ChildStdout,
}

impl HostProcess {
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
            deadline: Instant::now() + Duration::from_secs(600),
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
}

const SERVE_BOUNDS: ServeBounds = ServeBounds {
    read_deadline: Duration::from_secs(10),
    max_connections: 64,
    host_queue: 32,
};

/// One envelope's request, read and checked, handed to the Host thread. The
/// reply channel has room for the one reply, so the Host thread never waits
/// on a client.
struct HostJob {
    request: Vec<u8>,
    reply: mpsc::SyncSender<Vec<u8>>,
}

/// What a connection thread needs to judge an envelope before the Host sees it.
struct EnvelopeRules<'a> {
    operator: bool,
    config_bytes: &'a [u8],
    host_sha256: &'a [u8; 32],
    catalog_enabled: bool,
    read_deadline: Duration,
}

fn refuse(stream: &mut UnixStream, reason: &str) {
    let mut refusal = vec![254];
    refusal.extend_from_slice(reason.as_bytes());
    let _ = write_frame(stream, &refusal);
}

/// The accept loop. Nothing a client sends ends it: a bad envelope is refused
/// (254) or dropped, and a Host that stops answering is replaced. A request in
/// flight when its Host stopped gets no reply, which the client reports as an
/// uncertain status (`invoke`). Only a Host that cannot be started at all ends
/// the service.
fn supervise(
    listener: &UnixListener,
    operator: bool,
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
    let (jobs, queue) = mpsc::sync_channel::<HostJob>(bounds.host_queue);
    let stopping = AtomicBool::new(false);
    let live = AtomicUsize::new(0);
    std::thread::scope(|scope| {
        let (stopping, live) = (&stopping, &live);
        scope.spawn(move || {
            accept_connections(scope, listener, rules, bounds, jobs, stopping, live)
        });
        let ended = serve_host(&mut process, queue, start);
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
    start: &mut dyn FnMut() -> Result<HostProcess, String>,
) -> Result<(), String> {
    let mut process = start()?;
    let mut control = crate::operator_drain::Control::start(socket, config, host_sha256, process.child.id())?;
    let state = control.state.clone();
    let (jobs, queue) = mpsc::sync_channel::<HostJob>(SERVE_BOUNDS.host_queue);
    let rules = EnvelopeRules { operator: true, config_bytes: config, host_sha256, catalog_enabled: catalog, read_deadline: SERVE_BOUNDS.read_deadline };
    std::thread::scope(|scope| {
        let (state, rules) = (&state, &rules);
        let accept = scope.spawn(move || {
            accept_connections(scope, &listener, rules, SERVE_BOUNDS, jobs, &state.close, &state.live);
            // Closing the actual listener precedes the admissionClosed bit.
            // Existing readers remain counted and may finish their one turn.
            drop(listener);
            state.admission_closed.store(true, Ordering::Release);
        });
        let ended = serve_host_observed(&mut process, queue, start, Some(state));
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
    queue: mpsc::Receiver<HostJob>,
    start: &mut dyn FnMut() -> Result<HostProcess, String>,
) -> Result<(), String> {
    serve_host_observed(process, queue, start, None)
}

fn serve_host_observed(
    process: &mut HostProcess,
    queue: mpsc::Receiver<HostJob>,
    start: &mut dyn FnMut() -> Result<HostProcess, String>,
    state: Option<&crate::operator_drain::State>,
) -> Result<(), String> {
    for job in queue {
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
    jobs: mpsc::SyncSender<HostJob>,
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
    jobs: &mpsc::SyncSender<HostJob>,
) {
    if let Err(e) = stream.set_write_timeout(Some(Duration::from_secs(10))) {
        eprintln!("mini: cannot set client write deadline: {e}");
        return;
    }
    if rules.operator {
        match peer_uid(&stream) {
            Ok(uid) if uid == effective_uid() => {}
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
    if request.len() > HOST_MAX_FRAME {
        return refuse(&mut stream, "host frame exceeds bound");
    }
    if !(if rules.operator {
        // The owner-private listener is the single Host endpoint for both
        // lifecycle clients and the separately filtered public ingress relay.
        allowed_operator_operation(&request) || allowed_operation(&request, rules.catalog_enabled)
    } else {
        allowed_operation(&request, rules.catalog_enabled)
    }) {
        return refuse(&mut stream, "operation unavailable on selected socket");
    }
    let (reply, answer) = mpsc::sync_channel(1);
    match jobs.try_send(HostJob { request, reply }) {
        Ok(()) => {}
        Err(mpsc::TrySendError::Full(_)) => return refuse(&mut stream, "busy: host queue full"),
        Err(mpsc::TrySendError::Disconnected(_)) => return,
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
    use super::*;
    use std::thread;

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
            let _ = supervise(&listener, false, b"config", &[0; 32], false, &mut start);
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
    /// sleeps one second first (a slow request); op 9 exits instead.
    const FAKE_HOST: &str = r#"while n=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 | tr -d ' \n'); [ -n "$n" ]; do
  op=$(dd bs=1 count=1 2>/dev/null | od -An -tu1 | tr -d ' \n')
  [ "$n" -gt 1 ] && dd bs=1 count=$((n - 1)) of=/dev/null 2>/dev/null
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
        let listener = UnixListener::bind(&socket).unwrap();
        thread::spawn(move || {
            let mut start =
                || HostProcess::start(Command::new("/bin/sh").arg("-c").arg(FAKE_HOST), "fake");
            let rules = EnvelopeRules {
                operator: false,
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
    fn lifecycle_and_dispatch_routes_are_bounded_and_operator_only() {
        for operation in [22, 23, 26, 27, 34, 35, 38, 39] {
            assert!(allowed_operator_operation(&[operation, 1]));
            assert!(!allowed_operation(&[operation, 1], true));
            assert!(!allowed_operator_operation(&[operation]));
        }
        let oversized = vec![1; HOST_MAX_FRAME];
        for operation in [22, 23, 26, 27, 34, 35, 38, 39] {
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

}
