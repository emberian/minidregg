//! `PrivateEnvelope/v2`: a value the operator stores and cannot read.
//!
//! The kernel sees an atom `inlineObject(PRIVATE schema)` whose payload is the
//! envelope bytes, or a stream entry whose payload is the envelope bytes; content
//! laws are computed from counts and byte sizes only (`Kernel/ContentResource.lean`,
//! `project`), so nothing here is checked by the host. Members hold the room key;
//! the operator holds ciphertext, the epoch, the commitment and a size class: every
//! envelope is a whole number of 64-byte blocks (`envelope_len`). Design:
//! PRIVACY.md §3.1, §3.6; operator view and key-loss policy: `docs/PRIVATE-CELL.md`.
//!
//! v1 -> v2 (lane PRIVATE-ROOMS): v1 padded the value to 64 bytes inside a 133-byte
//! overhead, so envelopes were 133 + 64k bytes. v2 pads so the WHOLE envelope is a
//! multiple of 64 (what the operator measures on the wire); a v1 frame refuses.
//!
//! Every derivation is cSHAKE256 with its own customization string, every input
//! length-prefixed. One secret per friend: the 32-byte seed `keygen` writes signs
//! (Ed25519, as before) and, through `derive_enc_key`, decrypts (hybrid:
//! X25519 + ML-KEM-768, v3 -- a v1 X25519-only wrap or keyring refuses).
//!
//! The room-key protocol that hands these keys out (wraps in the room's `keys`
//! cell, rotation on a kick, the cache sync) is `roomkey.rs`.

use crate::hybrid_kem::{self, cshake, cshake_xof, random, CIPHERTEXT_LEN};
use crate::{hex, Result};
use argon2::{Algorithm, Argon2, Params, Version};
use chacha20poly1305::aead::{Aead, KeyInit, Payload};
use chacha20poly1305::{XChaCha20Poly1305, XNonce};
use serde_json::{json, Map, Value};
use std::collections::BTreeMap;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::path::Path;
use zeroize::{Zeroize, Zeroizing};

pub(crate) const ENVELOPE_FRAME: &[u8] = b"DREGG/PRIVATE-CELL/v2";
pub(crate) const WRAP_FRAME: &[u8] = b"DREGG/PRIVATE-WRAP/v3";
const ESCROW_FRAME: &[u8] = b"DREGG/SEED-ESCROW/v2";
const CACHE_FRAME: &[u8] = b"DREGG/PRIVATE-KEYCACHE/v2";
const COMMIT_LABEL: &[u8] = b"DREGG.PRIVATE-CELL.COMMIT/v1";
const SCHEMA_LABEL: &[u8] = b"DREGG.PRIVATE-CELL.SCHEMA/v1";
const ENC_LABEL: &[u8] = b"DREGG.CLIENT.ENC/v1";
/// The combiner's customization string: it names the suite, so a KEK derived for
/// X25519 + ML-KEM-768 is never confusable with any other derivation.
const KEK_LABEL: &[u8] = b"DREGG.PRIVATE-WRAP.KEK/x25519+ml-kem-768/v3";
const KEM_SEED_LABEL: &[u8] = b"DREGG.CLIENT.KEM-SEED/v1";
const KEY_ID_LABEL: &[u8] = b"DREGG.CLIENT.ENC-KEY-ID/v1";

const BUCKET: usize = 64;
const BLINDER: usize = 32;
const LENGTH: usize = 4;
const NONCE: usize = 24;
const TAG: usize = 16;
const KEY: usize = 32;
const MAX_PLAINTEXT: usize = 1 << 20;
const HEADER: usize = ENVELOPE_FRAME.len() + 4 + 32 + NONCE;
/// Everything in an envelope but the padded value: header, blinder, length, tag.
const OVERHEAD: usize = HEADER + BLINDER + LENGTH + TAG;
pub(crate) const WRAPPED_LEN: usize = CIPHERTEXT_LEN + NONCE + KEY + TAG;
const SALT: usize = 16;
/// Argon2id, RFC 9106 §4 second recommendation minus lanes: 64 MiB, 3 passes, 1 lane.
const ARGON_MEMORY_KIB: u32 = 64 * 1024;
const ARGON_PASSES: u32 = 3;
const ARGON_LANES: u32 = 1;
const MAX_CACHE: u64 = 4 * 1024 * 1024;

/// The sentence every user-facing entry point for private rooms carries. A private room's
/// protocol (hybrid wraps, founder-pinned lineage, two-phase release) is implemented and
/// tested; it has not been audited, and the devnet is one validator that is also the
/// operator. Say so wherever a friend meets the feature.
pub(crate) const PRIVACY_DISCLAIMER: &str = "devnet quality; privacy not audited";

pub(crate) const KEYCACHE_PASSPHRASE_ENV: &str = "MINI_KEYCACHE_PASSPHRASE";

/// The key-cache passphrase, held by this process and never by its children.
/// `adopt_keycache_passphrase` (first thing in `main`, before any thread or
/// child exists) moves it out of the environment; nothing this process spawns
/// (the Host, consent executables, `sh`, `stty`, ...) inherits it. The one
/// child that needs it, the shell's own `mini` subprocess, is handed it
/// explicitly (`chat::client`).
static KEYCACHE_PASSPHRASE: std::sync::OnceLock<Option<zeroize::Zeroizing<Vec<u8>>>> =
    std::sync::OnceLock::new();

pub(crate) fn adopt_keycache_passphrase() {
    let value = std::env::var_os(KEYCACHE_PASSPHRASE_ENV)
        .map(|value| zeroize::Zeroizing::new(value.into_encoded_bytes()));
    std::env::remove_var(KEYCACHE_PASSPHRASE_ENV);
    let _ = KEYCACHE_PASSPHRASE.set(value);
}

/// The passphrase, if one was given. Without `adopt` (unit tests), read once
/// from the environment.
pub(crate) fn keycache_passphrase() -> Option<zeroize::Zeroizing<Vec<u8>>> {
    KEYCACHE_PASSPHRASE
        .get_or_init(|| {
            std::env::var_os(KEYCACHE_PASSPHRASE_ENV)
                .map(|value| zeroize::Zeroizing::new(value.into_encoded_bytes()))
        })
        .clone()
}

/// D3: printed by `keygen`. Escrow is opt-in; the default is no recovery.
pub(crate) const KEYGEN_NOTICE: &str = "\
This key is the only copy. It signs as you and opens your private rooms.
If you lose it and have no next key there is no recovery: you enroll a new subject and are re-invited.
Room content comes back by re-wrap at the current epoch; older epochs come back
only from a member who kept them. Your old posts stay under the old subject.
Escrow is off. `--escrow-to-sponsor @SPONSOR-ENC-PUB --escrow-subject SUBJECT` writes your seed encrypted
to your sponsor, which lets your sponsor sign as you.";

fn aead(key: &[u8; KEY]) -> XChaCha20Poly1305 {
    XChaCha20Poly1305::new(key.into())
}

pub(crate) fn decode_hex(value: &str) -> Result<Vec<u8>> { crate::decode_hex(value) }

fn fixed<const N: usize>(bytes: &[u8], label: &str) -> Result<[u8; N]> {
    bytes
        .try_into()
        .map_err(|_| format!("{label} must be {N} bytes"))
}

/// Where a value sits: the room whose key seals it, the cell, and the address in
/// the cell. All three are bound into the commitment and the AEAD data, so the
/// operator cannot move an envelope to another cell, address or room unnoticed.
#[derive(Clone, Copy)]
pub(crate) struct Place<'a> {
    pub(crate) room: &'a str,
    pub(crate) cell: &'a str,
    pub(crate) address: &'a str,
}

/// The kernel schema digest of a private atom: cSHAKE256 of the frame, as the
/// unsigned big-endian integer the host's decimal `Digest` carries.
pub(crate) fn schema_decimal() -> String {
    schema_decimal_of(ENVELOPE_FRAME)
}

/// The schema digest of an atom whose payload is framed by `frame`.
pub(crate) fn schema_decimal_of(frame: &[u8]) -> String {
    let mut digits = Vec::new();
    let mut value = cshake(SCHEMA_LABEL, &[frame]).to_vec();
    while value.iter().any(|byte| *byte != 0) {
        let mut remainder = 0u32;
        for byte in value.iter_mut() {
            let current = (remainder << 8) | u32::from(*byte);
            *byte = (current / 10) as u8;
            remainder = current % 10;
        }
        digits.push(b'0' + remainder as u8);
    }
    if digits.is_empty() {
        digits.push(b'0');
    }
    digits.reverse();
    String::from_utf8(digits).expect("decimal digits")
}

// ---------------------------------------------------------------- room keys

/// `k_R^e`. Rotation draws a fresh key; it is not derived from the old one, so a
/// member removed at `e` learns nothing about `e + 1`.
pub(crate) struct RoomKey {
    epoch: u32,
    key: Zeroizing<[u8; KEY]>,
}

impl RoomKey {
    pub(crate) fn generate(epoch: u32) -> Result<Self> {
        Ok(Self {
            epoch,
            key: Zeroizing::new(random::<KEY>()?),
        })
    }

    pub(crate) fn epoch(&self) -> u32 {
        self.epoch
    }

    /// Borrow secret material for internal commitments and exact retry checks.
    /// The owning key remains in its Zeroizing allocation; this returns no copy.
    pub(crate) fn secret_bytes(&self) -> &[u8; KEY] {
        &self.key
    }

    #[cfg(test)]
    pub(crate) fn bytes(&self) -> [u8; KEY] {
        *self.key
    }

    fn from_parts(epoch: u32, key: [u8; KEY]) -> Self {
        Self {
            epoch,
            key: Zeroizing::new(key),
        }
    }
}

/// Every room key this client holds, by room id and epoch. Old epochs are kept:
/// a member who is later removed still opens what was sealed while it belonged.
/// `forgotten` records epochs this client deleted on purpose, so a sync of the
/// room's keys cell does not unwrap them again.
#[derive(Default)]
pub(crate) struct Keyring {
    rooms: BTreeMap<String, BTreeMap<u32, Zeroizing<[u8; KEY]>>>,
    forgotten: BTreeMap<String, std::collections::BTreeSet<u32>>,
}

impl Keyring {
    pub(crate) fn insert(&mut self, room: &str, key: &RoomKey) {
        self.rooms
            .entry(room.to_owned())
            .or_default()
            .insert(key.epoch, Zeroizing::new(*key.key));
    }

    pub(crate) fn get(&self, room: &str, epoch: u32) -> Option<RoomKey> {
        let key = self.rooms.get(room)?.get(&epoch)?;
        Some(RoomKey::from_parts(epoch, **key))
    }

    pub(crate) fn latest(&self, room: &str) -> Option<RoomKey> {
        let (epoch, key) = self.rooms.get(room)?.iter().next_back()?;
        Some(RoomKey::from_parts(*epoch, **key))
    }

    /// The epochs held for `room`, ascending.
    pub(crate) fn epochs(&self, room: &str) -> Vec<u32> {
        self.rooms.get(room).map(|e| e.keys().copied().collect()).unwrap_or_default()
    }

    /// Delete one epoch locally and remember it as forgotten (PRIVACY §3.6 `forget`).
    pub(crate) fn forget(&mut self, room: &str, epoch: u32) -> bool {
        let held = self
            .rooms
            .get_mut(room)
            .is_some_and(|epochs| epochs.remove(&epoch).is_some());
        if held {
            self.forgotten.entry(room.to_owned()).or_default().insert(epoch);
        }
        held
    }

    pub(crate) fn is_forgotten(&self, room: &str, epoch: u32) -> bool {
        self.forgotten.get(room).is_some_and(|e| e.contains(&epoch))
    }

    pub(crate) fn forgotten(&self, room: &str) -> Vec<u32> {
        self.forgotten.get(room).map(|e| e.iter().copied().collect()).unwrap_or_default()
    }
}

// ---------------------------------------------------------------- envelope

/// The length of the envelope that carries a `len`-byte value: the smallest
/// multiple of 64 that holds the value and the 133-byte overhead. Values of
/// 0..=59 bytes are one class (192), 60..=123 the next (256), and so on.
pub(crate) fn envelope_len(len: usize) -> usize {
    (OVERHEAD + len).div_ceil(BUCKET) * BUCKET
}

/// The zero-padded value region inside the ciphertext for a `len`-byte value.
pub(crate) fn padded_len(len: usize) -> usize {
    envelope_len(len) - OVERHEAD
}

/// The largest value an envelope of at most `limit` bytes can carry.
pub(crate) fn max_value_within(limit: usize) -> usize {
    (limit / BUCKET * BUCKET).saturating_sub(OVERHEAD)
}

fn pad(value: &[u8]) -> Vec<u8> {
    let mut padded = value.to_vec();
    padded.resize(padded_len(value.len()), 0);
    padded
}

/// What a reader without the epoch's key is shown: never a guess.
pub(crate) fn sealed_marker(epoch: u32) -> String {
    format!("[sealed under epoch {epoch} — you do not hold that key]")
}

fn place_parts<'a>(place: &Place<'a>) -> [&'a [u8]; 3] {
    [
        place.room.as_bytes(),
        place.cell.as_bytes(),
        place.address.as_bytes(),
    ]
}

/// `commit = cSHAKE256_{COMMIT}(room, cell, address, epoch, r, v)`. The blinder `r`
/// travels inside the ciphertext: a member can re-derive `commit`, the operator
/// cannot test guesses of a low-entropy `v` against it.
pub(crate) fn commitment(
    place: &Place<'_>,
    epoch: u32,
    blinder: &[u8; BLINDER],
    value: &[u8],
) -> [u8; 32] {
    let [room, cell, address] = place_parts(place);
    cshake(
        COMMIT_LABEL,
        &[room, cell, address, &epoch.to_be_bytes(), blinder, value],
    )
}

fn envelope_aad(place: &Place<'_>, epoch: u32, commit: &[u8; 32]) -> Vec<u8> {
    let mut aad = Vec::new();
    for part in [ENVELOPE_FRAME]
        .into_iter()
        .chain(place_parts(place))
        .chain([&epoch.to_be_bytes()[..], &commit[..]])
    {
        aad.extend_from_slice(&(part.len() as u64).to_be_bytes());
        aad.extend_from_slice(part);
    }
    aad
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PrivateEnvelope {
    pub(crate) epoch: u32,
    pub(crate) commit: [u8; 32],
    nonce: [u8; NONCE],
    ct: Vec<u8>,
}

/// What a member recovers: the value and the blinder that opens `commit`.
pub(crate) struct Opened {
    pub(crate) value: Vec<u8>,
    pub(crate) blinder: [u8; BLINDER],
}

fn seal_committed(
    key: &RoomKey,
    place: &Place<'_>,
    value: &[u8],
    blinder: [u8; BLINDER],
    commit: [u8; 32],
) -> Result<PrivateEnvelope> {
    if value.len() > MAX_PLAINTEXT {
        return Err(format!("private value exceeds {MAX_PLAINTEXT} bytes"));
    }
    let mut inner = Zeroizing::new(Vec::with_capacity(
        BLINDER + LENGTH + padded_len(value.len()),
    ));
    inner.extend_from_slice(&blinder);
    inner.extend_from_slice(&(value.len() as u32).to_be_bytes());
    inner.extend_from_slice(&pad(value));
    let nonce = random::<NONCE>()?;
    let ct = aead(&key.key)
        .encrypt(
            XNonce::from_slice(&nonce),
            Payload {
                msg: &inner,
                aad: &envelope_aad(place, key.epoch, &commit),
            },
        )
        .map_err(|_| "private envelope encryption failed")?;
    Ok(PrivateEnvelope {
        epoch: key.epoch,
        commit,
        nonce,
        ct,
    })
}

pub(crate) fn seal(key: &RoomKey, place: &Place<'_>, value: &[u8]) -> Result<PrivateEnvelope> {
    let blinder = random::<BLINDER>()?;
    let commit = commitment(place, key.epoch, &blinder, value);
    seal_committed(key, place, value, blinder, commit)
}

pub(crate) fn open(
    keys: &Keyring,
    place: &Place<'_>,
    envelope: &PrivateEnvelope,
) -> Result<Opened> {
    let key = keys
        .get(place.room, envelope.epoch)
        .ok_or_else(|| format!("no key for epoch {}", envelope.epoch))?;
    let inner = Zeroizing::new(
        aead(&key.key)
            .decrypt(
                XNonce::from_slice(&envelope.nonce),
                Payload {
                    msg: &envelope.ct,
                    aad: &envelope_aad(place, envelope.epoch, &envelope.commit),
                },
            )
            .map_err(|_| "private envelope failed its integrity check")?,
    );
    let blinder: [u8; BLINDER] = fixed(&inner[..BLINDER], "blinder")?;
    let len = u32::from_be_bytes(fixed(&inner[BLINDER..BLINDER + LENGTH], "length")?) as usize;
    let padded = &inner[BLINDER + LENGTH..];
    if len > MAX_PLAINTEXT
        || padded.len() != padded_len(len)
        || padded[len..].iter().any(|b| *b != 0)
    {
        return Err("private envelope has non-canonical padding".into());
    }
    let opened = Opened {
        value: padded[..len].to_vec(),
        blinder,
    };
    if !verify_commit(place, envelope.epoch, &opened, &envelope.commit) {
        return Err("private envelope commitment does not match its plaintext".into());
    }
    Ok(opened)
}

/// A law or referee holding an opening checks it with this (K-PRED-HASHEQ later).
pub(crate) fn verify_commit(
    place: &Place<'_>,
    epoch: u32,
    opened: &Opened,
    commit: &[u8; 32],
) -> bool {
    commitment(place, epoch, &opened.blinder, &opened.value) == *commit
}

impl PrivateEnvelope {
    pub(crate) fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(HEADER + self.ct.len());
        bytes.extend_from_slice(ENVELOPE_FRAME);
        bytes.extend_from_slice(&self.epoch.to_be_bytes());
        bytes.extend_from_slice(&self.commit);
        bytes.extend_from_slice(&self.nonce);
        bytes.extend_from_slice(&self.ct);
        bytes
    }

    pub(crate) fn from_bytes(bytes: &[u8]) -> Result<Self> {
        let body = bytes
            .strip_prefix(ENVELOPE_FRAME)
            .ok_or("not a DREGG/PRIVATE-CELL/v1 envelope")?;
        if bytes.len() < envelope_len(0) || bytes.len() % BUCKET != 0 {
            return Err("private envelope has an invalid length".into());
        }
        Ok(Self {
            epoch: u32::from_be_bytes(fixed(&body[..4], "epoch")?),
            commit: fixed(&body[4..36], "commit")?,
            nonce: fixed(&body[36..36 + NONCE], "nonce")?,
            ct: body[36 + NONCE..].to_vec(),
        })
    }
}

// ---------------------------------------------------------------- member keys

/// A member's hybrid key pair is the shared `hybrid_kem` type: one implementation
/// of the X25519 + ML-KEM-768 combiner serves rooms, the traffic mix and every
/// other key exchange.
pub(crate) use crate::hybrid_kem::{
    HybridPublic as MemberPublic, HybridSecret as MemberSecret,
    KEM_SEED_LEN, PUBLIC_LEN as MEMBER_PUBLIC_LEN,
};

/// The marker `keygen --hosted` leaves beside a signing key that lives on a
/// shared box: an empty file `KEY.hosted`. The key's owner reads it when it
/// SIGNS its encryption-key record (`hosted` byte), so an inviter learns the
/// custody from the invitee itself instead of depending on an operator list.
pub(crate) fn hosted_marker_path(key: &Path) -> std::path::PathBuf {
    let mut name = key.as_os_str().to_owned();
    name.push(".hosted");
    std::path::PathBuf::from(name)
}

pub(crate) fn key_is_hosted(key: &Path) -> bool {
    hosted_marker_path(key).exists()
}

/// The friend's secret encryption keys for the seed its signing key file holds.
/// Both halves come from the one 32-byte seed that signs: X25519 as
/// `cSHAKE256(ENC_LABEL, seed)`, and the ML-KEM-768 key from the FIPS 203 seed
/// `cSHAKE256-XOF(KEM_SEED_LABEL, seed)` (64 bytes `d || z`) -- so a seed alone
/// still recovers every key.
pub(crate) fn derive_enc_key(seed: &[u8; 32]) -> Result<MemberSecret> {
    let mut x25519 = cshake(ENC_LABEL, &[seed]);
    let kem_seed = Zeroizing::new(cshake_xof::<KEM_SEED_LEN>(KEM_SEED_LABEL, &[seed]));
    let secret = MemberSecret::from_parts(x25519, *kem_seed);
    x25519.zeroize();
    secret
}

pub(crate) fn enc_public(seed: &[u8; 32]) -> Result<MemberPublic> {
    Ok(derive_enc_key(seed)?.public().clone())
}

// ---------------------------------------------------------------- the encryption keyring

/// FIX-IDENTITY B. Every encryption secret is derived from the signing seed, so
/// a signing-key rotation (which overwrites the seed) changes it. Before the seed
/// is overwritten, `rotate-key` keeps the OLD encryption secrets here, beside the
/// key, so every room epoch wrapped to them stays openable: `KEY.enc-ring`, mode
/// 0600 -- exactly the protection the seed itself has (the seed is a raw 0600
/// file). Each entry holds the X25519 secret and the 64-byte ML-KEM-768 seed,
/// never a signing seed: a past signing key is revoked at the Host and nothing
/// here could sign.
///
/// v2 (hybrid): v1 held X25519 secrets only. A v1 ring REFUSES to load: it
/// cannot open a v3 wrap, and silently treating it as empty would hide that.
const ENC_RING_TYPE: &str = "minidregg-encryption-keyring-v2";
const ENC_RING_TYPE_V1: &str = "minidregg-encryption-keyring-v1";

pub(crate) fn enc_ring_path(key: &Path) -> std::path::PathBuf {
    let mut name = key.as_os_str().to_owned();
    name.push(".enc-ring");
    std::path::PathBuf::from(name)
}

fn read_seed(key: &Path) -> Result<Zeroizing<[u8; 32]>> {
    let bytes = Zeroizing::new(
        fs::read(key).map_err(|error| format!("cannot read signing key {}: {error}", key.display()))?,
    );
    let seed: [u8; 32] = bytes
        .as_slice()
        .try_into()
        .map_err(|_| format!("signing key {} must contain exactly 32 raw bytes", key.display()))?;
    Ok(Zeroizing::new(seed))
}

type RingEntry = (String, Zeroizing<[u8; 32]>, Zeroizing<[u8; KEM_SEED_LEN]>);

fn load_enc_ring(key: &Path) -> Result<Vec<RingEntry>> {
    let path = enc_ring_path(key);
    let bytes = match fs::read(&path) {
        Ok(bytes) => Zeroizing::new(bytes),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(error) => return Err(format!("cannot read {}: {error}", path.display())),
    };
    let value: Value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("{} is not an encryption keyring: {error}", path.display()))?;
    match value.get("type").and_then(Value::as_str) {
        Some(ENC_RING_TYPE) => {}
        Some(ENC_RING_TYPE_V1) => {
            return Err(format!(
                "{} is a {ENC_RING_TYPE_V1} (X25519 only, written before hybrid ML-KEM-768 wraps): it cannot open a v3 wrap and is refused, not read as empty; move it aside once its rooms are re-founded",
                path.display()
            ))
        }
        _ => return Err(format!("{} is not a {ENC_RING_TYPE}", path.display())),
    }
    let mut out = Vec::new();
    for entry in value.get("keys").and_then(Value::as_array).ok_or("keyring lacks keys")? {
        let epoch = entry.get("keyEpoch").and_then(Value::as_str).ok_or("keyring entry lacks keyEpoch")?;
        let x25519: [u8; 32] = decode_hex(entry.get("x25519").and_then(Value::as_str).ok_or("keyring entry lacks x25519")?)?
            .try_into()
            .map_err(|_| "a keyring X25519 secret is 32 bytes")?;
        let kem: [u8; KEM_SEED_LEN] = decode_hex(entry.get("kemSeed").and_then(Value::as_str).ok_or("keyring entry lacks kemSeed")?)?
            .try_into()
            .map_err(|_| "a keyring ML-KEM seed is 64 bytes")?;
        out.push((epoch.to_owned(), Zeroizing::new(x25519), Zeroizing::new(kem)));
    }
    Ok(out)
}

/// Keep the encryption secrets of the seed now at `key`, labelled with the key
/// epoch they belonged to. Idempotent: a pair already kept is not added again.
pub(crate) fn keyring_remember(key: &Path, key_epoch: &str) -> Result<()> {
    let seed = read_seed(key)?;
    let current = derive_enc_key(&seed)?;
    let (x25519, kem) = current.parts();
    let mut ring = load_enc_ring(key)?;
    if ring.iter().any(|(_, kept_x, kept_k)| **kept_x == *x25519 && **kept_k == *kem) {
        return Ok(());
    }
    ring.push((key_epoch.to_owned(), x25519, kem));
    let mut keys = Vec::new();
    for (epoch, x25519, kem) in &ring {
        let public = MemberSecret::from_parts(**x25519, **kem)?.public().id();
        keys.push(json!({"keyEpoch":epoch,"keyId":hex(&public),
            "x25519":hex(&x25519[..]),"kemSeed":hex(&kem[..])}));
    }
    let bytes = Zeroizing::new(
        serde_json::to_vec_pretty(&json!({"type":ENC_RING_TYPE,"keys":keys})).map_err(|e| e.to_string())?,
    );
    let path = enc_ring_path(key);
    let mut staged = path.as_os_str().to_owned();
    staged.push(".staged");
    let staged = std::path::PathBuf::from(staged);
    let _ = fs::remove_file(&staged);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&staged)
        .map_err(|error| format!("cannot create {}: {error}", staged.display()))?;
    file.write_all(&bytes)
        .and_then(|()| file.sync_all())
        .map_err(|error| format!("cannot write {}: {error}", staged.display()))?;
    fs::rename(&staged, &path).map_err(|error| format!("cannot install {}: {error}", path.display()))
}

/// Every encryption identity this key file can open with: the current seed's
/// first, then every kept past one, newest last.
pub(crate) fn enc_secrets(key: &Path) -> Result<Vec<MemberSecret>> {
    let seed = read_seed(key)?;
    let mut out = vec![derive_enc_key(&seed)?];
    for (_, x25519, kem) in load_enc_ring(key)? {
        out.push(MemberSecret::from_parts(*x25519, *kem)?);
    }
    Ok(out)
}

// ---------------------------------------------------------------- hybrid wraps

/// A hybrid wrap (frame v3): the hybrid ciphertext (one ephemeral X25519 key and
/// one ML-KEM-768 ciphertext, `hybrid_kem::encapsulate`) and a
/// XChaCha20-Poly1305 box of a 32-byte secret under the KEK that combiner
/// derives from BOTH shared secrets.
///
/// `ephemeral (32) || ML-KEM-768 ciphertext (1088) || nonce (24) || box (48)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Wrapped {
    hybrid: [u8; CIPHERTEXT_LEN],
    nonce: [u8; NONCE],
    ct: Vec<u8>,
}

impl Wrapped {
    pub(crate) fn to_bytes(&self) -> Vec<u8> {
        [&self.hybrid[..], &self.nonce, &self.ct].concat()
    }

    pub(crate) fn from_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != WRAPPED_LEN {
            return Err(format!("a v3 hybrid wrap is exactly {WRAPPED_LEN} bytes, not {}", bytes.len()));
        }
        Ok(Self {
            hybrid: fixed(&bytes[..CIPHERTEXT_LEN], "hybrid ciphertext")?,
            nonce: fixed(&bytes[CIPHERTEXT_LEN..CIPHERTEXT_LEN + NONCE], "nonce")?,
            ct: bytes[CIPHERTEXT_LEN + NONCE..].to_vec(),
        })
    }
}

fn seal_to(
    frame: &[u8],
    context: &[&[u8]],
    recipient: &MemberPublic,
    secret: &[u8; KEY],
) -> Result<Wrapped> {
    let encapsulated = hybrid_kem::encapsulate(KEK_LABEL, frame, context, recipient)?;
    let nonce = random::<NONCE>()?;
    let ct = aead(&encapsulated.kek)
        .encrypt(XNonce::from_slice(&nonce), Payload { msg: secret, aad: &encapsulated.transcript })
        .map_err(|_| "wrap encryption failed")?;
    Ok(Wrapped { hybrid: encapsulated.ciphertext, nonce, ct })
}

fn open_from(
    frame: &[u8],
    context: &[&[u8]],
    secret: &MemberSecret,
    wrapped: &Wrapped,
) -> Result<Zeroizing<[u8; KEY]>> {
    let (kek, transcript) = hybrid_kem::decapsulate(KEK_LABEL, frame, context, secret, &wrapped.hybrid)?;
    let plain = Zeroizing::new(
        aead(&kek)
            .decrypt(
                XNonce::from_slice(&wrapped.nonce),
                Payload { msg: &wrapped.ct, aad: &transcript },
            )
            .map_err(|_| "wrap does not open under this member key")?,
    );
    Ok(Zeroizing::new(fixed(&plain, "wrapped key")?))
}

pub(crate) fn wrap_room_key(
    room: &str,
    member: &str,
    member_pub: &MemberPublic,
    key: &RoomKey,
) -> Result<Wrapped> {
    seal_to(
        WRAP_FRAME,
        &[room.as_bytes(), &key.epoch.to_be_bytes(), member.as_bytes()],
        member_pub,
        &key.key,
    )
}

pub(crate) fn unwrap_room_key(
    room: &str,
    epoch: u32,
    member: &str,
    member_secret: &MemberSecret,
    wrapped: &Wrapped,
) -> Result<RoomKey> {
    let key = open_from(
        WRAP_FRAME,
        &[room.as_bytes(), &epoch.to_be_bytes(), member.as_bytes()],
        member_secret,
        wrapped,
    )?;
    Ok(RoomKey::from_parts(epoch, *key))
}

/// D3 (b), opt-in only: the seed encrypted to the sponsor's hybrid key.
pub(crate) fn escrow_seed(subject: &str, seed: &[u8; 32], sponsor: &MemberPublic) -> Result<Wrapped> {
    seal_to(ESCROW_FRAME, &[subject.as_bytes()], sponsor, seed)
}

pub(crate) fn recover_escrowed_seed(
    subject: &str,
    sponsor: &MemberSecret,
    wrapped: &Wrapped,
) -> Result<Zeroizing<[u8; 32]>> {
    open_from(ESCROW_FRAME, &[subject.as_bytes()], sponsor, wrapped)
}

// ---------------------------------------------------------------- key cache

fn passphrase_key(passphrase: &[u8], salt: &[u8; SALT]) -> Result<Zeroizing<[u8; KEY]>> {
    if passphrase.is_empty() {
        return Err("key cache passphrase must not be empty".into());
    }
    let params = Params::new(ARGON_MEMORY_KIB, ARGON_PASSES, ARGON_LANES, Some(KEY))
        .map_err(|error| format!("argon2 parameters: {error}"))?;
    let mut key = Zeroizing::new([0u8; KEY]);
    Argon2::new(Algorithm::Argon2id, Version::V0x13, params)
        .hash_password_into(passphrase, salt, key.as_mut())
        .map_err(|error| format!("argon2: {error}"))?;
    Ok(key)
}

/// `frame ‖ salt ‖ nonce ‖ XChaCha20-Poly1305_{Argon2id(passphrase, salt)}(json)`,
/// written 0600 through a temporary file and a rename.
pub(crate) fn save_cache(path: &Path, passphrase: &[u8], keys: &Keyring) -> Result<()> {
    let mut rooms = Map::new();
    for (room, epochs) in &keys.rooms {
        let epochs: Map<String, Value> = epochs
            .iter()
            .map(|(epoch, key)| (epoch.to_string(), Value::String(hex(&key[..]))))
            .collect();
        rooms.insert(room.clone(), Value::Object(epochs));
    }
    let forgotten: Map<String, Value> = keys
        .forgotten
        .iter()
        .map(|(room, epochs)| (room.clone(), json!(epochs.iter().map(u32::to_string).collect::<Vec<_>>())))
        .collect();
    let plain = Zeroizing::new(
        serde_json::to_vec(&json!({"rooms": rooms, "forgotten": forgotten})).map_err(|e| e.to_string())?,
    );
    let salt = random::<SALT>()?;
    let nonce = random::<NONCE>()?;
    let header = [CACHE_FRAME, &salt, &nonce].concat();
    let ct = aead(&*passphrase_key(passphrase, &salt)?)
        .encrypt(
            XNonce::from_slice(&nonce),
            Payload {
                msg: &plain,
                aad: &header,
            },
        )
        .map_err(|_| "key cache encryption failed")?;
    let temporary = path.with_extension("cache.tmp");
    let _ = fs::remove_file(&temporary);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&temporary)
        .map_err(|error| format!("cannot create {}: {error}", temporary.display()))?;
    file.write_all(&[header, ct].concat())
        .and_then(|()| file.sync_all())
        .map_err(|error| format!("cannot write {}: {error}", temporary.display()))?;
    fs::rename(&temporary, path)
        .map_err(|error| format!("cannot replace {}: {error}", path.display()))
}

pub(crate) fn load_cache(path: &Path, passphrase: &[u8]) -> Result<Keyring> {
    let mut bytes = Vec::new();
    File::open(path)
        .and_then(|file| file.take(MAX_CACHE + 1).read_to_end(&mut bytes))
        .map_err(|error| format!("cannot read key cache {}: {error}", path.display()))?;
    let header_len = CACHE_FRAME.len() + SALT + NONCE;
    if bytes.len() > MAX_CACHE as usize
        || bytes.len() < header_len + TAG
        || !bytes.starts_with(CACHE_FRAME)
    {
        return Err("not a DREGG/PRIVATE-KEYCACHE/v2 file".into());
    }
    let salt: [u8; SALT] = fixed(&bytes[CACHE_FRAME.len()..CACHE_FRAME.len() + SALT], "salt")?;
    let nonce = &bytes[CACHE_FRAME.len() + SALT..header_len];
    let plain = Zeroizing::new(
        aead(&*passphrase_key(passphrase, &salt)?)
            .decrypt(
                XNonce::from_slice(nonce),
                Payload {
                    msg: &bytes[header_len..],
                    aad: &bytes[..header_len],
                },
            )
            .map_err(|_| "key cache does not open: wrong passphrase or altered file")?,
    );
    let value: Value = serde_json::from_slice(&plain).map_err(|e| format!("key cache: {e}"))?;
    let mut keys = Keyring::default();
    for (room, epochs) in value
        .get("rooms")
        .and_then(Value::as_object)
        .ok_or("key cache lacks rooms")?
    {
        for (epoch, key) in epochs
            .as_object()
            .ok_or("key cache room must be an object")?
        {
            let epoch: u32 = epoch.parse().map_err(|_| "key cache epoch")?;
            let mut raw = decode_hex(key.as_str().ok_or("key cache key must be hex")?)?;
            let key = fixed::<KEY>(&raw, "room key")?;
            raw.zeroize();
            keys.insert(room, &RoomKey::from_parts(epoch, key));
        }
    }
    for (room, epochs) in value
        .get("forgotten")
        .and_then(Value::as_object)
        .ok_or("key cache lacks forgotten")?
    {
        for epoch in epochs.as_array().ok_or("key cache forgotten epochs must be a list")? {
            let epoch: u32 = epoch
                .as_str()
                .and_then(|e| e.parse().ok())
                .ok_or("key cache forgotten epoch")?;
            keys.forgotten.entry(room.clone()).or_default().insert(epoch);
        }
    }
    Ok(keys)
}

// ---------------------------------------------------------------- workspace hook

/// Legacy room-key document atoms are read-only. Fresh private document text
/// goes through protected-document audiences, and a room-key envelope is
/// sealed only at a stream position (`roomkey::seal_for_room`), which is
/// written once -- so no room-key envelope is ever re-sealed at an existing
/// address and none can be rolled back to an earlier ciphertext there. What
/// remains: structural actions, and striking a legacy private line while
/// retaining its exact ciphertext.
pub(crate) fn legacy_content(lowered: Value) -> Result<Value> {
    use crate::workspace::content_privacy::{actions as validate, classify, Exposure};
    let mut lowered = validate(&lowered["actions"], true)?;
    let private_kind = json!({"type":"inlineObject","schema":schema_decimal()});
    for action in lowered["actions"].as_array_mut().expect("validated actions") {
        match classify(action)? {
            Exposure::Structure => {}
            Exposure::EditText if action["tombstone"] == json!(true) => {
                let before = &action["before"];
                let fields = ["document", "kind", "payload", "createdBy", "createdAt", "revision", "tombstonedAt"];
                let record = before.as_object().ok_or("private edit lacks exact before record")?;
                if record.len() != fields.len() || fields.iter().any(|f| !record.contains_key(*f)) {
                    return Err("private edit before has unexpected fields".into());
                }
                if before["kind"] != private_kind {
                    return Err("private strike requires a ciphertext before record".into());
                }
                PrivateEnvelope::from_bytes(&decode_hex(before["payload"].as_str()
                    .ok_or("private edit before lacks payload")?)?)?;
                // Striking a line retains its existing encrypted body: it neither
                // publishes a supplied plaintext nor re-seals the old envelope.
                if action["payload"] != before["payload"] {
                    return Err("private tombstone must retain its ciphertext payload".into());
                }
                action["kind"] = private_kind.clone();
            }
            Exposure::CreateText | Exposure::EditText => return Err(
                "fresh private text requires protected-document audience enrollment; a room-key envelope is never re-sealed at an existing address".into()),
            Exposure::Unsupported | Exposure::Annotation | Exposure::RewrapAnnotation | Exposure::RewrapAtom => return Err("private content action requires protected-document audience enrollment".into()),
        }
    }
    Ok(lowered)
}

/// The opened text is presentation only. Callers retain the original atom for
/// stale guards; they never replace its kind/payload with this returned value.
/// A sealed line without an authenticated opening cannot enter an editable file.
pub(crate) fn is_private_kind(kind: &Value) -> bool {
    kind == &json!({"type":"inlineObject","schema":schema_decimal()}) || super::protected_document::is_kind(kind)
}

pub(crate) fn opened_text(atom: &Value) -> Result<Option<Vec<u8>>> {
    if !is_private_kind(&atom["kind"]) {
        return Ok(None);
    }
    if let Some(text) = atom["private"]["text"].as_str() {
        return Ok(Some(text.as_bytes().to_vec()));
    }
    if let Some(bytes) = atom["private"]["hex"].as_str() {
        return Ok(Some(decode_hex(bytes)?));
    }
    Err("private line has no authenticated opening; unlock its room key before editing".into())
}

/// `workspace read --private ROOM`: annotate every private atom in a signed view.
/// With the epoch key: `private: {epoch, commit, text|hex}`. Without it:
/// `private: "[sealed under epoch N — you do not hold that key]"`. A failed open
/// is annotated, not hidden.
pub(crate) fn open_view(view: &mut Value, room: &str, cell: &str, keys: Option<&Keyring>) -> usize {
    let schema = schema_decimal();
    let mut count = 0;
    annotate(view, room, cell, keys, &schema, &mut count);
    count
}

fn annotate(
    value: &mut Value,
    room: &str,
    cell: &str,
    keys: Option<&Keyring>,
    schema: &str,
    count: &mut usize,
) {
    match value {
        Value::Array(items) => items
            .iter_mut()
            .for_each(|item| annotate(item, room, cell, keys, schema, count)),
        Value::Object(object) => {
            let private = object.get("type").and_then(Value::as_str) == Some("atom")
                && object
                    .get("kind")
                    .and_then(|k| k.get("schema"))
                    .and_then(Value::as_str)
                    == Some(schema);
            if private {
                *count += 1;
                let note = private_note(object, room, cell, keys);
                object.insert("private".into(), note);
            } else {
                object
                    .values_mut()
                    .for_each(|item| annotate(item, room, cell, keys, schema, count));
            }
        }
        _ => {}
    }
}

fn private_note(
    atom: &Map<String, Value>,
    room: &str,
    cell: &str,
    keys: Option<&Keyring>,
) -> Value {
    let envelope = match atom
        .get("payload")
        .and_then(Value::as_str)
        .ok_or_else(|| "private atom lacks payload".to_string())
        .and_then(decode_hex)
        .and_then(|bytes| PrivateEnvelope::from_bytes(&bytes))
    {
        Ok(envelope) => envelope,
        Err(error) => return json!({"refused": error}),
    };
    let label = sealed_marker(envelope.epoch);
    let Some(keys) = keys else {
        return Value::String(label);
    };
    let Some(address) = atom.get("id").and_then(Value::as_str) else {
        return json!({"refused": "private atom lacks id", "label": label});
    };
    match open(
        keys,
        &Place {
            room,
            cell,
            address,
        },
        &envelope,
    ) {
        Ok(opened) => {
            let body = match String::from_utf8(opened.value.clone()) {
                Ok(text) => ("text", Value::String(text)),
                Err(_) => ("hex", Value::String(hex(&opened.value))),
            };
            json!({"epoch": envelope.epoch, "commit": hex(&envelope.commit), body.0: body.1})
        }
        Err(error) if error.starts_with("no key for epoch") => Value::String(label),
        Err(error) => json!({"refused": error, "label": label}),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hybrid_kem::KEM_CT_LEN;
    use ed25519_dalek::SigningKey;

    /// nextest runs each test in its own process, so this owns the OnceLock.
    #[test]
    fn keycache_passphrase_leaves_the_environment_before_any_child() {
        std::env::set_var(KEYCACHE_PASSPHRASE_ENV, "correct horse");
        adopt_keycache_passphrase();
        assert!(std::env::var_os(KEYCACHE_PASSPHRASE_ENV).is_none());
        assert_eq!(keycache_passphrase().as_deref().map(Vec::as_slice), Some(&b"correct horse"[..]));
        let child = std::process::Command::new("/usr/bin/env").output().unwrap();
        assert!(child.status.success());
        assert!(!String::from_utf8_lossy(&child.stdout).contains(KEYCACHE_PASSPHRASE_ENV));
    }

    const PLACE: Place<'static> = Place {
        room: "71",
        cell: "72",
        address: "9",
    };

    fn ring(key: &RoomKey) -> Keyring {
        let mut keys = Keyring::default();
        keys.insert(PLACE.room, key);
        keys
    }

    fn scratch(label: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!("mini-private-{label}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn round_trip_opens_and_commit_rederives() {
        let key = RoomKey::generate(0).unwrap();
        let envelope = seal(&key, &PLACE, b"the lab is at seven").unwrap();
        let parsed = PrivateEnvelope::from_bytes(&envelope.to_bytes()).unwrap();
        assert_eq!(parsed, envelope);
        let opened = open(&ring(&key), &PLACE, &parsed).unwrap();
        assert_eq!(opened.value, b"the lab is at seven");
        assert!(verify_commit(&PLACE, 0, &opened, &parsed.commit));
        assert!(!verify_commit(&PLACE, 1, &opened, &parsed.commit));
    }

    #[test]
    fn same_value_twice_gives_unlinkable_commits() {
        let key = RoomKey::generate(0).unwrap();
        let first = seal(&key, &PLACE, b"yes").unwrap();
        let second = seal(&key, &PLACE, b"yes").unwrap();
        assert_ne!(first.commit, second.commit);
        assert_ne!(first.ct, second.ct);
    }

    #[test]
    fn tampered_ciphertext_refused() {
        let key = RoomKey::generate(0).unwrap();
        let mut envelope = seal(&key, &PLACE, b"hello").unwrap();
        envelope.ct[40] ^= 1;
        let error = open(&ring(&key), &PLACE, &envelope).err().unwrap();
        assert!(error.contains("integrity"), "{error}");
    }

    #[test]
    fn tampered_commit_or_place_refused() {
        let key = RoomKey::generate(0).unwrap();
        let keys = ring(&key);
        let envelope = seal(&key, &PLACE, b"hello").unwrap();
        let mut commit = envelope.clone();
        commit.commit[0] ^= 1;
        assert!(open(&keys, &PLACE, &commit)
            .err()
            .unwrap()
            .contains("integrity"));
        let moved = Place {
            address: "10",
            ..PLACE
        };
        assert!(open(&keys, &moved, &envelope)
            .err()
            .unwrap()
            .contains("integrity"));
        let other_cell = Place {
            cell: "73",
            ..PLACE
        };
        assert!(open(&keys, &other_cell, &envelope)
            .err()
            .unwrap()
            .contains("integrity"));
    }

    #[test]
    fn member_authored_commit_that_misstates_the_plaintext_refused() {
        let key = RoomKey::generate(0).unwrap();
        let blinder = [7u8; BLINDER];
        let lie = commitment(&PLACE, 0, &blinder, b"bid 10");
        let envelope = seal_committed(&key, &PLACE, b"bid 99", blinder, lie).unwrap();
        let error = open(&ring(&key), &PLACE, &envelope).err().unwrap();
        assert!(error.contains("commitment does not match"), "{error}");
    }

    #[test]
    fn wrong_room_key_refused() {
        let key = RoomKey::generate(0).unwrap();
        let envelope = seal(&key, &PLACE, b"hello").unwrap();
        let other = RoomKey::generate(0).unwrap();
        assert!(open(&ring(&other), &PLACE, &envelope)
            .err()
            .unwrap()
            .contains("integrity"));
    }

    #[test]
    fn every_envelope_is_whole_64_byte_blocks_and_hides_length_within_a_class() {
        let key = RoomKey::generate(0).unwrap();
        let size = |n: usize| seal(&key, &PLACE, &vec![b'a'; n]).unwrap().to_bytes().len();
        for n in 0..=600 {
            assert_eq!(size(n) % 64, 0, "length {n}");
            assert_eq!(size(n), envelope_len(n), "length {n}");
        }
        for n in 0..=59 {
            assert_eq!(size(n), 192, "length {n}");
        }
        assert_eq!(size(60), 256);
        assert_eq!(size(123), 256);
        assert_eq!(size(124), 320);
        assert_eq!(max_value_within(4096), 3963);
        assert_eq!(envelope_len(3963), 4096);
        assert_eq!(envelope_len(3964), 4160);
    }

    #[test]
    fn non_canonical_envelope_lengths_refused() {
        let key = RoomKey::generate(0).unwrap();
        let bytes = seal(&key, &PLACE, b"x").unwrap().to_bytes();
        assert!(PrivateEnvelope::from_bytes(&bytes[..bytes.len() - 1]).is_err());
        assert!(PrivateEnvelope::from_bytes(&[bytes.clone(), vec![0]].concat()).is_err());
        let mut frame = bytes;
        frame[20] = b'1';
        assert!(PrivateEnvelope::from_bytes(&frame)
            .err()
            .unwrap()
            .contains("not a DREGG"));
    }

    use sha2::{Digest, Sha256};

    const KAT_TRANSCRIPT_SHA256: &str = "68d2bb8e36b6216b877efa867cd838371cba31a476a80035a4b7f75235d9312c";
    const KAT_KEK: &str = "64f554872ea555dc44317554720ab62466775814286345e527619ed52c44e708";

    fn dk(n: u8) -> MemberSecret {
        derive_enc_key(&[n; 32]).unwrap()
    }

    fn ep(n: u8) -> MemberPublic {
        enc_public(&[n; 32]).unwrap()
    }

    #[test]
    fn wrap_opens_for_its_member_and_not_another() {
        let s = ep(1);
        let key = RoomKey::generate(3).unwrap();
        let wrap = Wrapped::from_bytes(&wrap_room_key("71", "11", &s, &key).unwrap().to_bytes())
            .unwrap();
        let opened = unwrap_room_key("71", 3, "11", &dk(1), &wrap).unwrap();
        assert_eq!((opened.epoch, *opened.key), (3, *key.key));
        let wrong = unwrap_room_key("71", 3, "11", &dk(2), &wrap);
        assert!(wrong.err().unwrap().contains("does not open"));
        let relabelled = unwrap_room_key("71", 3, "12", &dk(1), &wrap);
        assert!(relabelled.is_err(), "a wrap is bound to its member id");
        let other_epoch = unwrap_room_key("71", 4, "11", &dk(1), &wrap);
        assert!(other_epoch.is_err(), "a wrap is bound to its epoch");
        let other_room = unwrap_room_key("70", 3, "11", &dk(1), &wrap);
        assert!(other_room.is_err(), "a wrap is bound to its room");
    }

    #[test]
    fn a_hybrid_wrap_has_the_v3_shape_and_a_fresh_ciphertext_every_time() {
        let key = RoomKey::generate(0).unwrap();
        let a = wrap_room_key("71", "11", &ep(1), &key).unwrap().to_bytes();
        let b = wrap_room_key("71", "11", &ep(1), &key).unwrap().to_bytes();
        assert_eq!(a.len(), WRAPPED_LEN);
        assert_eq!(WRAPPED_LEN, 32 + 1088 + 24 + 48, "ephemeral || ML-KEM-768 ciphertext || nonce || box");
        assert_ne!(a, b, "ephemeral key, KEM encapsulation and nonce are all fresh");
        assert_ne!(a[..32], b[..32]);
        assert_ne!(a[32..32 + KEM_CT_LEN], b[32..32 + KEM_CT_LEN]);
        let public = ep(1).to_bytes();
        assert_eq!(public.len(), MEMBER_PUBLIC_LEN);
        assert_eq!(MEMBER_PUBLIC_LEN, 32 + 1184);
        assert_eq!(MemberPublic::from_bytes(&public).unwrap(), ep(1));
        assert!(MemberPublic::from_bytes(&public[..32]).unwrap_err().contains("hybrid encryption key"),
            "an X25519-only key is not an encryption key any more");
    }

    #[test]
    fn tampering_either_ciphertext_component_refuses_the_wrap() {
        let key = RoomKey::generate(3).unwrap();
        let bytes = wrap_room_key("71", "11", &ep(1), &key).unwrap().to_bytes();
        let opens = |bytes: &[u8]| {
            unwrap_room_key("71", 3, "11", &dk(1), &Wrapped::from_bytes(bytes).unwrap())
        };
        assert!(opens(&bytes).is_ok());
        // X25519 half: the ephemeral public key.
        let mut ephemeral = bytes.clone();
        ephemeral[0] ^= 1;
        assert!(opens(&ephemeral).err().unwrap().contains("does not open"));
        // ML-KEM half: the encapsulation ciphertext (first, middle and last byte).
        for at in [32, 32 + KEM_CT_LEN / 2, 32 + KEM_CT_LEN - 1] {
            let mut kem = bytes.clone();
            kem[at] ^= 1;
            assert!(opens(&kem).err().unwrap().contains("does not open"), "KEM ciphertext byte {at}");
        }
        // The box, its nonce and its tag.
        for at in [32 + KEM_CT_LEN, 32 + KEM_CT_LEN + NONCE, WRAPPED_LEN - 1] {
            let mut boxed = bytes.clone();
            boxed[at] ^= 1;
            assert!(opens(&boxed).is_err(), "box byte {at}");
        }
        assert!(Wrapped::from_bytes(&bytes[..WRAPPED_LEN - 1]).is_err());
        let mut long = bytes.clone();
        long.push(0);
        assert!(Wrapped::from_bytes(&long).is_err());
    }

    #[test]
    fn a_wrap_needs_both_halves_of_the_recipient_identity() {
        // The hybrid is only as good as the requirement that BOTH secrets are
        // used: an identity with the right X25519 half and another's ML-KEM half
        // (or the reverse) cannot open the wrap.
        let key = RoomKey::generate(0).unwrap();
        let wrap = wrap_room_key("71", "11", &ep(1), &key).unwrap();
        assert!(unwrap_room_key("71", 0, "11", &dk(1), &wrap).is_ok());
        let right_x_wrong_kem = dk(1).with_kem_of(&dk(2)).unwrap();
        let wrong_x_right_kem = dk(1).with_x25519_of(&dk(2)).unwrap();
        assert!(unwrap_room_key("71", 0, "11", &right_x_wrong_kem, &wrap).is_err());
        assert!(unwrap_room_key("71", 0, "11", &wrong_x_right_kem, &wrap).is_err());
    }

    #[test]
    fn a_recipient_with_another_kem_key_is_not_the_recipient() {
        // A public key whose X25519 half is member 1's and whose ML-KEM half is
        // member 2's names a third identity: member 1 cannot open a wrap to it
        // (the transcript binds both public keys), and its id differs from both.
        let spliced = MemberPublic::from_bytes(&[&ep(1).to_bytes()[..32], &ep(2).to_bytes()[32..]].concat()).unwrap();
        assert_ne!(spliced.id(), ep(1).id());
        assert_ne!(spliced.id(), ep(2).id());
        let key = RoomKey::generate(0).unwrap();
        let wrap = wrap_room_key("71", "11", &spliced, &key).unwrap();
        assert!(unwrap_room_key("71", 0, "11", &dk(1), &wrap).is_err());
        assert!(unwrap_room_key("71", 0, "11", &dk(2), &wrap).is_err());
        assert!(unwrap_room_key("71", 0, "11", &dk(1).with_kem_of(&dk(2)).unwrap(), &wrap).is_ok());
    }

    /// Known-answer vector for the combiner. The expected KEK was computed by an
    /// independent implementation (Python, pycryptodome `cSHAKE256`, not the
    /// `sha3` crate this code runs on) from the same inputs:
    ///   KEK = cSHAKE256(S = KEK_LABEL, X = for each of [ss_x25519, ss_mlkem, transcript]:
    ///                                       u64be(len) || bytes, L = 256 bits)
    /// with ss_x25519 = 32 x 0x11, ss_mlkem = 32 x 0x22 and the transcript below
    /// (frame, room "71", epoch 3, member "11", ephemeral 32 x 0x33, KEM
    /// ciphertext 1088 x 0x44, X25519 key 32 x 0x55, ML-KEM key 1184 x 0x66,
    /// each u64be-length-prefixed).
    #[test]
    fn the_combiner_matches_an_independent_known_answer() {
        let recipient = MemberPublic::from_raw_unchecked([0x55; 32], [0x66; hybrid_kem::KEM_EK_LEN]);
        let transcript = hybrid_kem::transcript(
            WRAP_FRAME,
            &[b"71", &3u32.to_be_bytes(), b"11"],
            &[0x33; 32],
            &[0x44; KEM_CT_LEN],
            &recipient,
        );
        assert_eq!(hex(&Sha256::digest(&transcript)), KAT_TRANSCRIPT_SHA256);
        let kek = hybrid_kem::combine(KEK_LABEL, &[0x11; 32], &[0x22; 32], &transcript);
        assert_eq!(hex(&kek[..]), KAT_KEK);
        // Each input is load-bearing: flipping either shared secret or any
        // transcript byte gives a different key.
        assert_ne!(hybrid_kem::combine(KEK_LABEL, &[0x12; 32], &[0x22; 32], &transcript)[..], kek[..]);
        assert_ne!(hybrid_kem::combine(KEK_LABEL, &[0x11; 32], &[0x23; 32], &transcript)[..], kek[..]);
        let mut other = transcript.clone();
        *other.last_mut().unwrap() ^= 1;
        assert_ne!(hybrid_kem::combine(KEK_LABEL, &[0x11; 32], &[0x22; 32], &other)[..], kek[..]);
        // Swapping the two shared secrets is not the same key (they are not interchangeable).
        assert_ne!(hybrid_kem::combine(KEK_LABEL, &[0x22; 32], &[0x11; 32], &transcript)[..], kek[..]);
    }

    /// Independent known answers (pure-Python FIPS 203 `kyber-py` `_keygen_internal(d, z)`
    /// and pycryptodome `cSHAKE256`, neither of which is the code under test): the
    /// seeded ML-KEM-768 key AWS-LC derives from a FIPS 203 seed, and the whole chain
    /// member seed -> cSHAKE256 -> (X25519 secret, ML-KEM seed) -> encapsulation key.
    #[test]
    fn the_seeded_ml_kem_key_matches_an_independent_fips_203_implementation() {
        let seed: [u8; KEM_SEED_LEN] = std::array::from_fn(|i| i as u8);
        let (_, ek) = hybrid_kem::ml_kem_768_from_seed(&seed).unwrap();
        assert_eq!(hex(&Sha256::digest(ek)), "0b7934c83125c788995e2ba6bd761e33046b3e40571be53e023309a29f398cc9");
        let member = [7u8; 32];
        assert_eq!(hex(&cshake_xof::<KEM_SEED_LEN>(KEM_SEED_LABEL, &[&member])),
            "6dced71e0350ea6f8bc7260011db1c96f00818159ffdde14bef9829680fd16156c7d305aad5baa12d55253580e0c96d153650bd0ce23e0a8067a7699d7e3bc07");
        assert_eq!(hex(&cshake(ENC_LABEL, &[&member])),
            "d136b4e4fe6c9422db54a421e27dc43565fc353d91f5eeed00d11c7b1be78386");
        assert_eq!(hex(&Sha256::digest(&dk(7).public().to_bytes()[32..])),
            "f25326bac91dc9d641e27ade7dbc1a9a856a353e302fa600a2b9bda21abe77f4");
    }

    #[test]
    fn ml_kem_keys_come_from_the_seed_and_round_trip_across_a_reload() {
        let a = dk(7);
        let b = dk(7);
        assert_eq!(a.public(), b.public(), "same seed, same hybrid public key");
        assert_ne!(dk(7).public(), dk(8).public());
        assert_ne!(dk(7).public().kem()[..], dk(8).public().kem()[..]);
        // The ML-KEM half is not the X25519 half under another name, and not the
        // signing key's: independent derivations of one seed.
        assert_ne!(dk(7).public().x25519()[..], dk(7).public().kem()[..32]);
        // A key rebuilt from its keyring parts is the same identity.
        let (x25519, kem) = a.parts();
        let reloaded = MemberSecret::from_parts(*x25519, *kem).unwrap();
        assert_eq!(reloaded.public(), a.public());
        // Encapsulation to the seeded key decapsulates (checked through a wrap).
        let key = RoomKey::generate(0).unwrap();
        let wrap = wrap_room_key("71", "11", a.public(), &key).unwrap();
        assert!(unwrap_room_key("71", 0, "11", &reloaded, &wrap).is_ok());
    }

    #[test]
    fn low_order_member_key_refused() {
        let key = RoomKey::generate(0).unwrap();
        let zero = MemberPublic::from_bytes(&[&[0u8; 32][..], &ep(1).to_bytes()[32..]].concat()).unwrap();
        assert!(wrap_room_key("71", "11", &zero, &key)
            .err()
            .unwrap()
            .contains("low-order"));
    }

    #[test]
    fn the_encryption_keyring_keeps_every_past_secret_across_seed_rotations() {
        let dir = scratch("enc-ring");
        let key = dir.join("mini.key");
        fs::write(&key, [1u8; 32]).unwrap();
        assert_eq!(enc_secrets(&key).unwrap().len(), 1, "no ring: the current secret only");
        keyring_remember(&key, "1").unwrap();
        keyring_remember(&key, "1").unwrap();
        // rotate-key overwrites the seed; the old secret stays openable.
        fs::write(&key, [2u8; 32]).unwrap();
        let secrets: Vec<MemberPublic> = enc_secrets(&key).unwrap().iter()
            .map(|s| s.public().clone()).collect();
        assert_eq!(secrets, vec![ep(2), ep(1)]);
        // The kept pair opens a wrap addressed to the OLD hybrid key.
        let room_key = RoomKey::generate(0).unwrap();
        let wrap = wrap_room_key("71", "11", &ep(1), &room_key).unwrap();
        let kept = enc_secrets(&key).unwrap();
        assert!(unwrap_room_key("71", 0, "11", &kept[0], &wrap).is_err());
        assert!(unwrap_room_key("71", 0, "11", &kept[1], &wrap).is_ok());
        use std::os::unix::fs::MetadataExt;
        assert_eq!(fs::metadata(enc_ring_path(&key)).unwrap().mode() & 0o777, 0o600);
        let text = fs::read_to_string(enc_ring_path(&key)).unwrap();
        assert!(!text.contains(&hex(&[1u8; 32])), "the ring holds no signing seed");
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn keygen_hosted_leaves_a_marker_the_record_signer_reads() {
        let dir = scratch("hosted-marker");
        let key = dir.join("mini.key");
        fs::write(&key, [1u8; 32]).unwrap();
        assert!(!key_is_hosted(&key));
        fs::write(hosted_marker_path(&key), b"").unwrap();
        assert!(key_is_hosted(&key));
        assert_eq!(hosted_marker_path(&key), dir.join("mini.key.hosted"));
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_v1_encryption_keyring_refuses_by_name_and_is_not_read_as_empty() {
        let dir = scratch("enc-ring-v1");
        let key = dir.join("mini.key");
        fs::write(&key, [1u8; 32]).unwrap();
        fs::write(enc_ring_path(&key), br#"{"type":"minidregg-encryption-keyring-v1","keys":[]}"#).unwrap();
        let error = enc_secrets(&key).err().unwrap();
        assert!(error.contains("minidregg-encryption-keyring-v1") && error.contains("refused"), "{error}");
        assert!(keyring_remember(&key, "1").is_err(), "remembering must not overwrite a ring it cannot read");
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn enc_key_is_deterministic_from_the_seed_and_not_the_signing_key() {
        let seed = [9u8; 32];
        assert_eq!(enc_public(&seed).unwrap(), enc_public(&seed).unwrap());
        assert_eq!(
            *derive_enc_key(&seed).unwrap().parts().0,
            *derive_enc_key(&seed).unwrap().parts().0
        );
        assert_ne!(enc_public(&seed).unwrap(), ep(8));
        let signing = SigningKey::from_bytes(&seed);
        let enc = *derive_enc_key(&seed).unwrap().parts().0;
        assert_ne!(enc, seed);
        assert_ne!(enc, signing.to_scalar_bytes());
        assert_ne!(
            *enc_public(&seed).unwrap().x25519(),
            signing.verifying_key().to_bytes()
        );
        assert_ne!(
            *enc_public(&seed).unwrap().x25519(),
            signing.verifying_key().to_montgomery().to_bytes()
        );
    }

    #[test]
    fn key_cache_round_trips_and_refuses_the_wrong_passphrase() {
        let dir = scratch("cache");
        let path = dir.join("keys.cache");
        let e0 = RoomKey::generate(0).unwrap();
        let e1 = RoomKey::generate(1).unwrap();
        let mut keys = ring(&e0);
        keys.insert(PLACE.room, &e1);
        save_cache(&path, b"correct horse", &keys).unwrap();
        let bytes = fs::read(&path).unwrap();
        assert!(!bytes
            .windows(KEY)
            .any(|w| w == &e0.key[..] || w == &e1.key[..]));
        let loaded = load_cache(&path, b"correct horse").unwrap();
        assert_eq!(*loaded.get("71", 0).unwrap().key, *e0.key);
        assert_eq!(*loaded.latest("71").unwrap().key, *e1.key);
        assert!(load_cache(&path, b"correct horsf")
            .err()
            .unwrap()
            .contains("wrong passphrase"));
        assert!(save_cache(&path, b"", &keys).is_err());
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn escrow_is_off_by_default_and_opens_only_for_the_sponsor() {
        assert!(KEYGEN_NOTICE.contains("no recovery"));
        assert!(KEYGEN_NOTICE.contains("Escrow is off"));
        let seed = [5u8; 32];
        let wrapped = escrow_seed("11", &seed, &ep(6)).unwrap();
        assert_eq!(*recover_escrowed_seed("11", &dk(6), &wrapped).unwrap(), seed);
        assert!(recover_escrowed_seed("11", &dk(7), &wrapped).is_err());
        assert!(recover_escrowed_seed("12", &dk(6), &wrapped).is_err());
    }

    #[test]
    fn a_sealed_atom_reads_back_only_at_its_address() {
        let key = RoomKey::generate(2).unwrap();
        let envelope = seal(&key, &Place { room: "71", cell: "72", address: "9" }, b"meet at noon").unwrap();
        let kind = json!({"type":"inlineObject","schema":schema_decimal()});
        let payload = hex(&envelope.to_bytes());
        assert!(!payload.contains(&hex(b"meet at noon")));
        let view = json!({"cell":{"entries":[{"type":"atom","id":"9","document":"1",
            "kind":kind,"payload":payload}]}});
        let mut without = view.clone();
        assert_eq!(open_view(&mut without, "71", "72", None), 1);
        let label = without["cell"]["entries"][0]["private"].as_str().unwrap();
        assert_eq!(label, "[sealed under epoch 2 — you do not hold that key]");
        let mut with = view.clone();
        open_view(&mut with, "71", "72", Some(&ring(&key)));
        assert_eq!(with["cell"]["entries"][0]["private"]["text"], "meet at noon");
        let mut moved = view;
        moved["cell"]["entries"][0]["id"] = json!("10");
        open_view(&mut moved, "71", "72", Some(&ring(&key)));
        assert!(moved["cell"]["entries"][0]["private"]["refused"].as_str().unwrap().contains("integrity"));
    }

    #[test]
    fn legacy_private_content_never_seals_and_only_strikes_retaining_ciphertext() {
        let old_key = RoomKey::generate(0).unwrap();
        let old = seal(&old_key, &PLACE, b"before secret").unwrap();
        let kind = json!({"type":"inlineObject","schema":schema_decimal()});
        let before = json!({"document":"72","kind":kind,"payload":hex(&old.to_bytes()),
            "createdBy":{"subject":"1","capabilityKind":"object","capability":"2"},
            "createdAt":"3","revision":"4","tombstonedAt":null});
        let edit = json!({"type":"content","actions":[{"type":"editAtom","atom":"9",
            "before":before,"kind":kind,"payload":hex(b"after secret"),"tombstone":false},
            {"type":"editElement","element":"1","revision":"4",
                "op":{"type":"move","child":"9","index":"0"}}]});
        assert!(legacy_content(edit.clone()).unwrap_err().contains("never re-sealed"),
            "re-sealing at an existing address is the rollback surface; it is gone");
        let create = json!({"type":"content","actions":[
            {"type":"createAtom","atom":"9","kind":{"type":"text"},"payload":hex(b"meet at noon")}]});
        assert!(legacy_content(create).is_err());
        let mut strike = edit.clone();
        strike["actions"][0]["tombstone"] = json!(true);
        assert!(legacy_content(strike.clone()).is_err(), "a strike may not carry new bytes");
        strike["actions"][0]["payload"] = before["payload"].clone();
        let struck = legacy_content(strike).unwrap();
        assert_eq!(struck["actions"][0]["payload"], before["payload"]);
        assert_eq!(struck["actions"][0]["before"], before);
        let mut plaintext_guard = edit;
        plaintext_guard["actions"][0]["tombstone"] = json!(true);
        plaintext_guard["actions"][0]["before"]["kind"] = json!({"type":"text"});
        plaintext_guard["actions"][0]["before"]["payload"] = json!(hex(b"before secret"));
        plaintext_guard["actions"][0]["payload"] = json!(hex(b"before secret"));
        assert!(legacy_content(plaintext_guard).is_err());
        let opaque = json!({"type":"content","actions":[{"type":"createDocument","rootElement":"1",
            "schema":"1","body":{"type":"opaque","schema":"1","payload":"00"}}]});
        assert!(legacy_content(opaque).is_err());
    }

    #[test]
    fn schema_digest_is_a_canonical_decimal() {
        let schema = schema_decimal();
        assert!(schema.len() > 70 && !schema.starts_with('0'));
        assert!(schema.bytes().all(|b| b.is_ascii_digit()));
    }
}
