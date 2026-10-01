//! `PrivateEnvelope/v1`: a content-cell value the operator stores and cannot read.
//!
//! The kernel sees an atom `inlineObject(PRIVATE schema)` whose payload is the
//! envelope bytes; content laws are computed from counts and byte sizes only
//! (`Kernel/ContentResource.lean`, `project`), so nothing here is checked by the
//! host. Members hold the room key; the operator holds ciphertext, the epoch, the
//! commitment and a 64-byte size class. Design: PRIVACY.md §3.1; operator view and
//! key-loss policy: `docs/PRIVATE-CELL.md`.
//!
//! Every derivation is cSHAKE256 with its own customization string, every input
//! length-prefixed. One secret per friend: the 32-byte seed `keygen` writes signs
//! (Ed25519, as before) and, through `derive_enc_key`, decrypts (X25519).
//!
//! Only `seal_content`/`open_view` and the cache loader are reachable from the
//! binary today (the `--private ROOM` hook in `workspace`). Wrap, rekey, cache
//! save, enc-key derivation and escrow are exercised by the tests and consumed by
//! row 7 (the room-key verbs); that lane deletes the allowance below.
#![cfg_attr(not(test), allow(dead_code))]

use crate::{hex, Result};
use argon2::{Algorithm, Argon2, Params, Version};
use chacha20poly1305::aead::{Aead, KeyInit, Payload};
use chacha20poly1305::{XChaCha20Poly1305, XNonce};
use serde_json::{json, Map, Value};
use sha3::digest::{core_api::CoreWrapper, ExtendableOutput, Update, XofReader};
use sha3::CShake256Core;
use std::collections::BTreeMap;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::path::Path;
use x25519_dalek::{PublicKey, StaticSecret};
use zeroize::{Zeroize, Zeroizing};

pub(crate) const ENVELOPE_FRAME: &[u8] = b"DREGG/PRIVATE-CELL/v1";
const WRAP_FRAME: &[u8] = b"DREGG/PRIVATE-WRAP/v1";
const ESCROW_FRAME: &[u8] = b"DREGG/SEED-ESCROW/v1";
const CACHE_FRAME: &[u8] = b"DREGG/PRIVATE-KEYCACHE/v1";
const KEYS_RECORD: &str = "DREGG/PRIVATE-KEYS/v1";
const COMMIT_LABEL: &[u8] = b"DREGG.PRIVATE-CELL.COMMIT/v1";
const SCHEMA_LABEL: &[u8] = b"DREGG.PRIVATE-CELL.SCHEMA/v1";
const ENC_LABEL: &[u8] = b"DREGG.CLIENT.ENC/v1";
const KEK_LABEL: &[u8] = b"DREGG.PRIVATE-WRAP.KEK/v1";

const BUCKET: usize = 64;
const BLINDER: usize = 32;
const LENGTH: usize = 4;
const NONCE: usize = 24;
const TAG: usize = 16;
const KEY: usize = 32;
const MAX_PLAINTEXT: usize = 1 << 20;
const HEADER: usize = ENVELOPE_FRAME.len() + 4 + 32 + NONCE;
const WRAPPED_LEN: usize = 32 + NONCE + KEY + TAG;
const SALT: usize = 16;
/// Argon2id, RFC 9106 §4 second recommendation minus lanes: 64 MiB, 3 passes, 1 lane.
const ARGON_MEMORY_KIB: u32 = 64 * 1024;
const ARGON_PASSES: u32 = 3;
const ARGON_LANES: u32 = 1;
const MAX_CACHE: u64 = 4 * 1024 * 1024;

pub(crate) const KEYCACHE_PASSPHRASE_ENV: &str = "MINI_KEYCACHE_PASSPHRASE";

/// D3: printed by `keygen`. Escrow is opt-in; the default is no recovery.
pub(crate) const KEYGEN_NOTICE: &str = "\
This key is the only copy. It signs as you and opens your private rooms.
If you lose it and have no next key there is no recovery: you enroll a new subject and are re-invited.
Room content comes back by re-wrap at the current epoch; older epochs come back
only from a member who kept them. Your old posts stay under the old subject.
Escrow is off. `--escrow-to-sponsor @SPONSOR-ENC-PUB --escrow-subject SUBJECT` writes your seed encrypted
to your sponsor, which lets your sponsor sign as you.";

fn cshake(label: &[u8], parts: &[&[u8]]) -> [u8; 32] {
    let mut hasher = CoreWrapper::from_core(CShake256Core::new(label));
    for part in parts {
        hasher.update(&(part.len() as u64).to_be_bytes());
        hasher.update(part);
    }
    let mut output = [0u8; 32];
    XofReader::read(&mut hasher.finalize_xof(), &mut output);
    output
}

fn random<const N: usize>() -> Result<[u8; N]> {
    let mut bytes = [0u8; N];
    File::open("/dev/urandom")
        .and_then(|mut source| source.read_exact(&mut bytes))
        .map_err(|error| format!("cannot obtain operating-system randomness: {error}"))?;
    Ok(bytes)
}

fn aead(key: &[u8; KEY]) -> XChaCha20Poly1305 {
    XChaCha20Poly1305::new(key.into())
}

pub(crate) fn decode_hex(value: &str) -> Result<Vec<u8>> {
    if value.len() % 2 != 0 {
        return Err("hex must have an even length".into());
    }
    (0..value.len())
        .step_by(2)
        .map(|index| {
            u8::from_str_radix(&value[index..index + 2], 16).map_err(|_| "invalid hex".to_string())
        })
        .collect()
}

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
    let mut digits = Vec::new();
    let mut value = cshake(SCHEMA_LABEL, &[ENVELOPE_FRAME]).to_vec();
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

    /// Kick = revoke (kernel) + `rotate` + `KeysRecord::for_members` of the rest.
    pub(crate) fn rotate(&self) -> Result<Self> {
        Self::generate(
            self.epoch
                .checked_add(1)
                .ok_or("room-key epoch exhausted")?,
        )
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
#[derive(Default)]
pub(crate) struct Keyring {
    rooms: BTreeMap<String, BTreeMap<u32, Zeroizing<[u8; KEY]>>>,
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

    /// Crypto-shred one epoch locally (PRIVACY §3.6 `forget`).
    pub(crate) fn forget(&mut self, room: &str, epoch: u32) -> bool {
        self.rooms
            .get_mut(room)
            .is_some_and(|epochs| epochs.remove(&epoch).is_some())
    }
}

// ---------------------------------------------------------------- envelope

/// The padded length of a value: the smallest positive multiple of 64 that holds
/// it. Values of 0..=64 bytes are one class, 65..=128 the next.
pub(crate) fn padded_len(len: usize) -> usize {
    len.max(1).div_ceil(BUCKET) * BUCKET
}

pub(crate) fn pad64(value: &[u8]) -> Vec<u8> {
    let mut padded = value.to_vec();
    padded.resize(padded_len(value.len()), 0);
    padded
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
    inner.extend_from_slice(&pad64(value));
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
    let value = padded[..len].to_vec();
    if commitment(place, envelope.epoch, &blinder, &value) != envelope.commit {
        return Err("private envelope commitment does not match its plaintext".into());
    }
    Ok(Opened { value, blinder })
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
        let ct_len = bytes.len().saturating_sub(HEADER);
        let min_ct = BLINDER + LENGTH + BUCKET + TAG;
        if bytes.len() < HEADER + min_ct || (ct_len - min_ct) % BUCKET != 0 {
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

/// The friend's X25519 secret: `cSHAKE256("DREGG.CLIENT.ENC/v1", seed)`, the same
/// 32-byte seed whose Ed25519 key signs. Clamping happens inside X25519.
pub(crate) fn derive_enc_key(seed: &[u8; 32]) -> StaticSecret {
    let mut bytes = cshake(ENC_LABEL, &[seed]);
    let secret = StaticSecret::from(bytes);
    bytes.zeroize();
    secret
}

pub(crate) fn enc_public(seed: &[u8; 32]) -> PublicKey {
    PublicKey::from(&derive_enc_key(seed))
}

/// ECIES: ephemeral X25519 → cSHAKE KEK → XChaCha20-Poly1305 of a 32-byte secret.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Wrapped {
    ephemeral: [u8; 32],
    nonce: [u8; NONCE],
    ct: Vec<u8>,
}

impl Wrapped {
    pub(crate) fn to_bytes(&self) -> Vec<u8> {
        [&self.ephemeral[..], &self.nonce, &self.ct].concat()
    }

    pub(crate) fn from_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != WRAPPED_LEN {
            return Err(format!("a wrap is exactly {WRAPPED_LEN} bytes"));
        }
        Ok(Self {
            ephemeral: fixed(&bytes[..32], "ephemeral key")?,
            nonce: fixed(&bytes[32..32 + NONCE], "nonce")?,
            ct: bytes[32 + NONCE..].to_vec(),
        })
    }
}

fn kek_and_aad(
    frame: &[u8],
    context: &[&[u8]],
    shared: &[u8; 32],
    ephemeral: &PublicKey,
    recipient: &PublicKey,
) -> (Zeroizing<[u8; KEY]>, Vec<u8>) {
    let mut aad = Vec::new();
    for part in [frame]
        .into_iter()
        .chain(context.iter().copied())
        .chain([&ephemeral.as_bytes()[..], &recipient.as_bytes()[..]])
    {
        aad.extend_from_slice(&(part.len() as u64).to_be_bytes());
        aad.extend_from_slice(part);
    }
    (Zeroizing::new(cshake(KEK_LABEL, &[shared, &aad])), aad)
}

fn seal_to(
    frame: &[u8],
    context: &[&[u8]],
    recipient: &PublicKey,
    secret: &[u8; KEY],
) -> Result<Wrapped> {
    let ephemeral_secret = StaticSecret::from(random::<32>()?);
    let ephemeral = PublicKey::from(&ephemeral_secret);
    let shared = ephemeral_secret.diffie_hellman(recipient);
    if !shared.was_contributory() {
        return Err("recipient X25519 key is a low-order point".into());
    }
    let (kek, aad) = kek_and_aad(frame, context, shared.as_bytes(), &ephemeral, recipient);
    let nonce = random::<NONCE>()?;
    let ct = aead(&kek)
        .encrypt(
            XNonce::from_slice(&nonce),
            Payload {
                msg: secret,
                aad: &aad,
            },
        )
        .map_err(|_| "wrap encryption failed")?;
    Ok(Wrapped {
        ephemeral: *ephemeral.as_bytes(),
        nonce,
        ct,
    })
}

fn open_from(
    frame: &[u8],
    context: &[&[u8]],
    secret: &StaticSecret,
    wrapped: &Wrapped,
) -> Result<Zeroizing<[u8; KEY]>> {
    let ephemeral = PublicKey::from(wrapped.ephemeral);
    let recipient = PublicKey::from(secret);
    let shared = secret.diffie_hellman(&ephemeral);
    if !shared.was_contributory() {
        return Err("wrap ephemeral key is a low-order point".into());
    }
    let (kek, aad) = kek_and_aad(frame, context, shared.as_bytes(), &ephemeral, &recipient);
    let plain = Zeroizing::new(
        aead(&kek)
            .decrypt(
                XNonce::from_slice(&wrapped.nonce),
                Payload {
                    msg: &wrapped.ct,
                    aad: &aad,
                },
            )
            .map_err(|_| "wrap does not open under this member key")?,
    );
    Ok(Zeroizing::new(fixed(&plain, "wrapped key")?))
}

pub(crate) fn wrap_room_key(
    room: &str,
    member: &str,
    member_pub: &PublicKey,
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
    member_secret: &StaticSecret,
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

/// D3 (b), opt-in only: the seed encrypted to the sponsor's X25519 key.
pub(crate) fn escrow_seed(subject: &str, seed: &[u8; 32], sponsor: &PublicKey) -> Result<Wrapped> {
    seal_to(ESCROW_FRAME, &[subject.as_bytes()], sponsor, seed)
}

pub(crate) fn recover_escrowed_seed(
    subject: &str,
    sponsor: &StaticSecret,
    wrapped: &Wrapped,
) -> Result<Zeroizing<[u8; 32]>> {
    open_from(ESCROW_FRAME, &[subject.as_bytes()], sponsor, wrapped)
}

// ---------------------------------------------------------------- R/keys

/// The `R/keys` record for one epoch: one wrap per current member, as JSON bytes
/// for a content atom under R. A member missing from the list has no key for it.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct KeysRecord {
    pub(crate) room: String,
    pub(crate) epoch: u32,
    pub(crate) wrapped: Vec<(String, Wrapped)>,
}

impl KeysRecord {
    pub(crate) fn for_members(
        room: &str,
        key: &RoomKey,
        members: &[(&str, PublicKey)],
    ) -> Result<Self> {
        let mut wrapped = Vec::with_capacity(members.len());
        for (member, public) in members {
            wrapped.push((
                member.to_string(),
                wrap_room_key(room, member, public, key)?,
            ));
        }
        wrapped.sort_by(|left, right| left.0.cmp(&right.0));
        if wrapped.windows(2).any(|pair| pair[0].0 == pair[1].0) {
            return Err("duplicate member in room-key record".into());
        }
        Ok(Self {
            room: room.to_owned(),
            epoch: key.epoch,
            wrapped,
        })
    }

    pub(crate) fn open_for(&self, member: &str, secret: &StaticSecret) -> Result<RoomKey> {
        let (_, wrap) = self
            .wrapped
            .iter()
            .find(|(id, _)| id == member)
            .ok_or_else(|| format!("no key for epoch {}: {member} has no wrap", self.epoch))?;
        unwrap_room_key(&self.room, self.epoch, member, secret, wrap)
    }

    pub(crate) fn to_bytes(&self) -> Vec<u8> {
        let wrapped: Vec<Value> = self
            .wrapped
            .iter()
            .map(|(member, wrap)| json!({"member": member, "wrap": hex(&wrap.to_bytes())}))
            .collect();
        serde_json::to_vec(&json!({"type": KEYS_RECORD, "room": self.room,
            "epoch": self.epoch.to_string(), "wrapped": wrapped}))
        .expect("keys record serializes")
    }

    pub(crate) fn from_bytes(bytes: &[u8]) -> Result<Self> {
        let value: Value =
            serde_json::from_slice(bytes).map_err(|e| format!("keys record: {e}"))?;
        let object = value.as_object().ok_or("keys record must be an object")?;
        if object.len() != 4 || object.get("type").and_then(Value::as_str) != Some(KEYS_RECORD) {
            return Err("not a DREGG/PRIVATE-KEYS/v1 record".into());
        }
        let text = |key: &str| {
            object
                .get(key)
                .and_then(Value::as_str)
                .ok_or(format!("keys record lacks {key}"))
        };
        let epoch_text = text("epoch")?;
        let epoch: u32 = epoch_text.parse().map_err(|_| "keys record epoch")?;
        if epoch.to_string() != epoch_text {
            return Err("keys record epoch must be canonical decimal".into());
        }
        let mut wrapped = Vec::new();
        for entry in object
            .get("wrapped")
            .and_then(Value::as_array)
            .ok_or("keys record lacks wrapped")?
        {
            let entry = entry
                .as_object()
                .filter(|e| e.len() == 2)
                .ok_or("wrap entry has unexpected fields")?;
            let member = entry
                .get("member")
                .and_then(Value::as_str)
                .ok_or("wrap entry lacks member")?;
            let wrap = entry
                .get("wrap")
                .and_then(Value::as_str)
                .ok_or("wrap entry lacks wrap")?;
            wrapped.push((member.to_owned(), Wrapped::from_bytes(&decode_hex(wrap)?)?));
        }
        if wrapped.windows(2).any(|pair| pair[0].0 >= pair[1].0) {
            return Err("keys record members must be strictly sorted".into());
        }
        Ok(Self {
            room: text("room")?.to_owned(),
            epoch,
            wrapped,
        })
    }
}

/// Kick: a fresh key at `epoch + 1` wrapped for `remaining` only. The kernel half
/// (revoke the capability, bump `epoch` under R's law) is not this module's.
pub(crate) fn rekey(
    room: &str,
    current: &RoomKey,
    remaining: &[(&str, PublicKey)],
) -> Result<(RoomKey, KeysRecord)> {
    let next = current.rotate()?;
    let record = KeysRecord::for_members(room, &next, remaining)?;
    Ok((next, record))
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
    let plain =
        Zeroizing::new(serde_json::to_vec(&json!({"rooms": rooms})).map_err(|e| e.to_string())?);
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
        return Err("not a DREGG/PRIVATE-KEYCACHE/v1 file".into());
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
    Ok(keys)
}

// ---------------------------------------------------------------- workspace hook

/// `workspace propose --private ROOM`: every `createAtom` in a lowered content
/// payload must be a `text` atom; its payload becomes an envelope under the room's
/// latest key, its kind the private schema. Element bodies carrying bytes refuse:
/// only atoms are sealed, and a plaintext beside a private room is a leak.
pub(crate) fn seal_content(lowered: Value, room: &str, cell: &str, key: &RoomKey) -> Result<Value> {
    let mut lowered = lowered;
    let actions = lowered
        .get_mut("actions")
        .and_then(Value::as_array_mut)
        .ok_or("content payload lacks actions")?;
    for action in actions.iter_mut() {
        match action.get("type").and_then(Value::as_str) {
            Some("createAtom") => {
                if action.get("kind") != Some(&json!({"type":"text"})) {
                    return Err("--private seals text atoms only".into());
                }
                let atom = action
                    .get("atom")
                    .and_then(Value::as_str)
                    .ok_or("createAtom lacks atom")?
                    .to_owned();
                let plain = Zeroizing::new(decode_hex(
                    action
                        .get("payload")
                        .and_then(Value::as_str)
                        .ok_or("createAtom lacks payload")?,
                )?);
                let envelope = seal(
                    key,
                    &Place {
                        room,
                        cell,
                        address: &atom,
                    },
                    &plain,
                )?;
                action["kind"] = json!({"type":"inlineObject","schema":schema_decimal()});
                action["payload"] = Value::String(hex(&envelope.to_bytes()));
            }
            Some("createDocument") => {
                if action
                    .get("body")
                    .and_then(|b| b.get("type"))
                    .and_then(Value::as_str)
                    == Some("opaque")
                {
                    return Err(
                        "--private refuses an opaque element body: seal the bytes as an atom"
                            .into(),
                    );
                }
            }
            _ => {}
        }
    }
    Ok(lowered)
}

/// `workspace read --private ROOM`: annotate every private atom in a signed view.
/// With the epoch key: `private: {epoch, commit, text|hex}`. Without it:
/// `private: "[private: epoch N, commit …]"`. A failed open is annotated, not hidden.
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
    let label = format!(
        "[private: epoch {}, commit {}]",
        envelope.epoch,
        hex(&envelope.commit)
    );
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

/// The key cache of a workspace, opened with `MINI_KEYCACHE_PASSPHRASE`. Absent
/// passphrase: `None` (reads print labels; writes refuse). Wrong passphrase: error.
pub(crate) fn workspace_keys(root: &Path) -> Result<Option<Keyring>> {
    let Some(passphrase) = std::env::var_os(KEYCACHE_PASSPHRASE_ENV) else {
        return Ok(None);
    };
    let passphrase = Zeroizing::new(passphrase.into_encoded_bytes());
    load_cache(&root.join("private").join("keys.cache"), &passphrase).map(Some)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::SigningKey;

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
    fn pad64_hides_length_within_64_byte_classes() {
        let key = RoomKey::generate(0).unwrap();
        let size = |n: usize| seal(&key, &PLACE, &vec![b'a'; n]).unwrap().to_bytes().len();
        let first = size(1);
        for n in 0..=64 {
            assert_eq!(size(n), first, "length {n}");
        }
        assert_eq!(size(65), first + 64);
        assert_eq!(size(128), first + 64);
        assert_eq!(size(129), first + 128);
        assert_eq!(pad64(b"abc").len(), 64);
        assert_eq!(pad64(&[1; 64]).len(), 64);
        assert_eq!(pad64(&[1; 65]).len(), 128);
    }

    #[test]
    fn non_canonical_envelope_lengths_refused() {
        let key = RoomKey::generate(0).unwrap();
        let bytes = seal(&key, &PLACE, b"x").unwrap().to_bytes();
        assert!(PrivateEnvelope::from_bytes(&bytes[..bytes.len() - 1]).is_err());
        assert!(PrivateEnvelope::from_bytes(&[bytes.clone(), vec![0]].concat()).is_err());
        let mut frame = bytes;
        frame[20] = b'2';
        assert!(PrivateEnvelope::from_bytes(&frame)
            .err()
            .unwrap()
            .contains("not a DREGG"));
    }

    #[test]
    fn wrap_opens_for_its_member_and_not_another() {
        let s = enc_public(&[1; 32]);
        let key = RoomKey::generate(3).unwrap();
        let record = KeysRecord::for_members("71", &key, &[("11", s)]).unwrap();
        let parsed = KeysRecord::from_bytes(&record.to_bytes()).unwrap();
        assert_eq!(parsed, record);
        let opened = parsed.open_for("11", &derive_enc_key(&[1; 32])).unwrap();
        assert_eq!((opened.epoch, *opened.key), (3, *key.key));
        let wrap = &parsed.wrapped[0].1;
        let wrong = unwrap_room_key("71", 3, "11", &derive_enc_key(&[2; 32]), wrap);
        assert!(wrong.err().unwrap().contains("does not open"));
        let relabelled = unwrap_room_key("71", 3, "12", &derive_enc_key(&[1; 32]), wrap);
        assert!(relabelled.is_err(), "a wrap is bound to its member id");
        let other_epoch = unwrap_room_key("71", 4, "11", &derive_enc_key(&[1; 32]), wrap);
        assert!(other_epoch.is_err(), "a wrap is bound to its epoch");
        assert!(parsed
            .open_for("12", &derive_enc_key(&[2; 32]))
            .err()
            .unwrap()
            .contains("no key for epoch 3"));
    }

    #[test]
    fn low_order_member_key_refused() {
        let key = RoomKey::generate(0).unwrap();
        let zero = PublicKey::from([0u8; 32]);
        assert!(wrap_room_key("71", "11", &zero, &key)
            .err()
            .unwrap()
            .contains("low-order"));
    }

    #[test]
    fn rotation_opens_new_epoch_not_old_and_kicked_keeps_the_past() {
        let (a_seed, b_seed) = ([1u8; 32], [2u8; 32]);
        let members = [("11", enc_public(&a_seed)), ("12", enc_public(&b_seed))];
        let e0 = RoomKey::generate(0).unwrap();
        let r0 = KeysRecord::for_members("71", &e0, &members).unwrap();
        let old = seal(&e0, &PLACE, b"before the kick").unwrap();
        let (e1, r1) = rekey("71", &e0, &members[..1]).unwrap();
        assert_eq!(e1.epoch, 1);
        let new = seal(&e1, &PLACE, b"after the kick").unwrap();

        let mut b = Keyring::default();
        b.insert("71", &r0.open_for("12", &derive_enc_key(&b_seed)).unwrap());
        assert!(r1
            .open_for("12", &derive_enc_key(&b_seed))
            .err()
            .unwrap()
            .contains("no key for epoch 1"));
        assert_eq!(open(&b, &PLACE, &old).unwrap().value, b"before the kick");
        assert_eq!(open(&b, &PLACE, &new).err().unwrap(), "no key for epoch 1");

        let mut a = Keyring::default();
        a.insert("71", &r1.open_for("11", &derive_enc_key(&a_seed)).unwrap());
        assert_eq!(open(&a, &PLACE, &old).err().unwrap(), "no key for epoch 0");
        a.insert("71", &r0.open_for("11", &derive_enc_key(&a_seed)).unwrap());
        assert_eq!(open(&a, &PLACE, &new).unwrap().value, b"after the kick");
        assert_eq!(open(&a, &PLACE, &old).unwrap().value, b"before the kick");
        assert_eq!(a.latest("71").unwrap().epoch, 1);
        assert!(a.forget("71", 0));
        assert_eq!(open(&a, &PLACE, &old).err().unwrap(), "no key for epoch 0");
    }

    #[test]
    fn enc_key_is_deterministic_from_the_seed_and_not_the_signing_key() {
        let seed = [9u8; 32];
        assert_eq!(enc_public(&seed), enc_public(&seed));
        assert_eq!(
            derive_enc_key(&seed).to_bytes(),
            derive_enc_key(&seed).to_bytes()
        );
        assert_ne!(enc_public(&seed), enc_public(&[8u8; 32]));
        let signing = SigningKey::from_bytes(&seed);
        let enc = derive_enc_key(&seed).to_bytes();
        assert_ne!(enc, seed);
        assert_ne!(enc, signing.to_scalar_bytes());
        assert_ne!(
            *enc_public(&seed).as_bytes(),
            signing.verifying_key().to_bytes()
        );
        assert_ne!(
            *enc_public(&seed).as_bytes(),
            signing.verifying_key().to_montgomery().to_bytes()
        );
    }

    #[test]
    fn key_cache_round_trips_and_refuses_the_wrong_passphrase() {
        let dir = scratch("cache");
        let path = dir.join("keys.cache");
        let e0 = RoomKey::generate(0).unwrap();
        let e1 = e0.rotate().unwrap();
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
        let wrapped = escrow_seed("11", &seed, &enc_public(&[6; 32])).unwrap();
        assert_eq!(
            *recover_escrowed_seed("11", &derive_enc_key(&[6; 32]), &wrapped).unwrap(),
            seed
        );
        assert!(recover_escrowed_seed("11", &derive_enc_key(&[7; 32]), &wrapped).is_err());
        assert!(recover_escrowed_seed("12", &derive_enc_key(&[6; 32]), &wrapped).is_err());
    }

    #[test]
    fn workspace_hook_seals_text_atoms_and_reads_back() {
        let key = RoomKey::generate(2).unwrap();
        let lowered = json!({"type":"content","actions":[
            {"type":"createAtom","atom":"9","kind":{"type":"text"},"payload":hex(b"meet at noon")}]});
        let sealed = seal_content(lowered, "71", "72", &key).unwrap();
        let action = &sealed["actions"][0];
        let payload = action["payload"].as_str().unwrap();
        assert!(!payload.contains(&hex(b"meet at noon")));
        assert_eq!(action["kind"]["schema"].as_str().unwrap(), schema_decimal());

        let view = json!({"cell":{"entries":[{"type":"atom","id":"9","document":"1",
            "kind":action["kind"].clone(),"payload":payload}]}});
        let mut without = view.clone();
        assert_eq!(open_view(&mut without, "71", "72", None), 1);
        let label = without["cell"]["entries"][0]["private"].as_str().unwrap();
        assert!(label.starts_with("[private: epoch 2, commit "), "{label}");
        let mut with = view.clone();
        open_view(&mut with, "71", "72", Some(&ring(&key)));
        assert_eq!(
            with["cell"]["entries"][0]["private"]["text"],
            "meet at noon"
        );
        let mut moved = view;
        moved["cell"]["entries"][0]["id"] = json!("10");
        open_view(&mut moved, "71", "72", Some(&ring(&key)));
        assert!(moved["cell"]["entries"][0]["private"]["refused"]
            .as_str()
            .unwrap()
            .contains("integrity"));

        let opaque = json!({"type":"content","actions":[{"type":"createDocument","rootElement":"1",
            "schema":"1","body":{"type":"opaque","schema":"1","payload":"00"}}]});
        assert!(seal_content(opaque, "71", "72", &key).is_err());
        let inline = json!({"type":"content","actions":[{"type":"createAtom","atom":"9",
            "kind":{"type":"inlineObject","schema":"1"},"payload":"00"}]});
        assert!(seal_content(inline, "71", "72", &key).is_err());
    }

    #[test]
    fn schema_digest_is_a_canonical_decimal() {
        let schema = schema_decimal();
        assert!(schema.len() > 70 && !schema.starts_with('0'));
        assert!(schema.bytes().all(|b| b.is_ascii_digit()));
    }
}
