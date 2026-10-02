//! The room-key protocol of a private room (PRIVACY §3.1, row 7 / B4).
//!
//! A private room `R` is a room (K-ROOM 3c) whose content the members' clients
//! seal under a ROOM KEY `k_R^e` before it reaches the socket. The founder's
//! client draws `k_R^0` at `room new NAME --private`; every later epoch `e + 1`
//! is drawn fresh at a kick (never derived from `e`). The node never holds a
//! room key. It holds WRAPS: `k_R^e` encrypted to one member's X25519 key
//! (`private::wrap_room_key`: ephemeral X25519, a cSHAKE256 key-encryption key
//! bound to room, epoch, member and both public keys, XChaCha20-Poly1305).
//!
//! THE `keys` CELL. The wraps live in one content cell born `--in R` by the
//! founder (reference `NAME-keys`), one atom per `(epoch, member)`:
//!   atom id   = epoch * 2^64 + member        (one id per pair: a second wrap
//!                                             for the same pair is refused by
//!                                             the content controller)
//!   kind      = inlineObject(schema of "DREGG/PRIVATE-WRAP/v1")
//!   payload   = member's X25519 public key (32) ‖ wrap (104)
//! Its law (`deploy/shell/templates/room/private/law.keys.json`,
//! `Kernel/PrivateRoomKeys.lean`) lets only the founder write, and only by
//! creating atoms: no edit, no tombstone. So the room's EPOCH -- the largest
//! epoch with a wrap -- never goes backwards, and a member cannot hand anyone a
//! key. Every member may read every wrap (the cheaper choice: per-address
//! observation is not on this tree, and a wrap opens for one X25519 secret
//! only). The member's public key rides beside its wrap so that whoever rotates
//! can rewrap to every remaining member without a roster of its own.
//!
//! THE CLIENT'S CACHE. Each workspace keeps the epochs it holds in
//! `ROOT/private/keys.cache` (Argon2id + XChaCha20-Poly1305 under
//! `MINI_KEYCACHE_PASSPHRASE`). `sync` reads the keys cell with the reader's own
//! room grant, unwraps every wrap addressed to this subject that the cache does
//! not hold, and stores it -- an invitee's first read is its first sync.
//!
//! SEALING. `seal_for_room` seals under the room's CURRENT epoch only: a client
//! that does not hold it (a kicked member, a member never wrapped) refuses to
//! seal. The epoch is in the clear in every envelope so a reader picks its key;
//! a reader without that epoch's key is shown `private::sealed_marker` and never
//! a guess. A stream entry is bound to (room, stream cell, sequence) -- the
//! position the plan read -- so an envelope cannot be moved to another stream
//! or position unnoticed.
//!
//! WHAT THE OPERATOR SEES: cell ids, which subject wrote which wrap and entry at
//! which height, the epochs, the members' public encryption keys, commitments,
//! and every envelope's size as a whole number of 64-byte blocks. Not a key,
//! not a plaintext.
//!
//! KICK = the K-ROOM revoke + ROTATE: a fresh `k_R^{e+1}` wrapped for every
//! member that held a wrap at `e`, still holds a grant covering R (the Host's
//! `who` view), and is not the one kicked. The kicked member keeps the past --
//! every epoch it already held, and whatever it already read -- and gets
//! nothing new.
//!
//! FORGET: `forget NAME [EPOCH]` deletes this client's copies and records them
//! as forgotten so `sync` does not unwrap them again. The wrap stays in the
//! append-only keys cell and this subject's X25519 secret still opens it:
//! forgetting is a promise this client keeps, not a cryptographic erasure, until
//! the subject's key itself is rotated (PRIVACY row 13).

use super::private::{
    self, derive_enc_key, enc_public, open, seal, unwrap_room_key, wrap_room_key, Keyring, Place,
    PrivateEnvelope, RoomKey, Wrapped, KEYCACHE_PASSPHRASE_ENV, WRAPPED_LEN, WRAP_FRAME,
};
use super::{
    bounded_json, make_private_dir, member, member_path, propose, reference, signed_view,
    submit_intent, validate_name,
};
use crate::{hex, query_retained, Result};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use x25519_dalek::{PublicKey, StaticSecret};
use zeroize::Zeroizing;

/// The keys cell's law, as the template ships it; `@FOUNDER` is the founder.
const KEYS_LAW: &str = include_str!("../../../deploy/shell/templates/room/private/law.keys.json");
/// The room cell's own law for the private template.
const ROOM_LAW: &str = include_str!("../../../deploy/shell/templates/room/private/law.room.json");
/// The kernel's stream payload limit (`StreamCell.maxPayloadBytes`).
const MAX_STREAM_PAYLOAD: usize = 4096;
/// Where the operator lists the subjects whose signing key is a file on the box.
const HOSTED_SUBJECTS_DEFAULT: &str = "/etc/mini/hosted-subjects";
pub(crate) const HOSTED_SUBJECTS_ENV: &str = "MINI_HOSTED_SUBJECTS";

pub(crate) fn keys_law(founder: &str) -> Value {
    serde_json::from_str(&KEYS_LAW.replace("@FOUNDER", founder)).expect("the template law is JSON")
}

pub(crate) fn room_law() -> Value {
    serde_json::from_str(ROOM_LAW).expect("the template law is JSON")
}

/// The reference name of a room's keys cell in the founder's workspace.
pub(crate) fn keys_name(room: &str) -> Result<String> {
    let name = format!("{room}-keys");
    validate_name(&name).map_err(|_| format!("a private room's name is at most 59 characters ({room})"))?;
    Ok(name)
}

pub(crate) fn wrap_schema() -> String {
    private::schema_decimal_of(WRAP_FRAME)
}

// ---------------------------------------------------------------- wrap atoms

/// One wrap in the keys cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct WrapAtom {
    pub(crate) epoch: u32,
    pub(crate) member: u64,
    pub(crate) enc_pub: [u8; 32],
    pub(crate) wrapped: Wrapped,
}

pub(crate) fn wrap_atom_id(epoch: u32, member: u64) -> String {
    ((u128::from(epoch) << 64) | u128::from(member)).to_string()
}

pub(crate) fn parse_wrap_atom_id(id: &str) -> Result<(u32, u64)> {
    let value: u128 = id.parse().map_err(|_| format!("wrap atom id {id} is not a decimal below 2^96"))?;
    if value.to_string() != id {
        return Err(format!("wrap atom id {id} is not canonical"));
    }
    let epoch = u32::try_from(value >> 64).map_err(|_| format!("wrap atom id {id} exceeds epoch range"))?;
    Ok((epoch, value as u64))
}

fn subject_number(subject: &str) -> Result<u64> {
    let value: u64 = subject.parse().map_err(|_| format!("subject {subject} is not a 64-bit decimal"))?;
    if value.to_string() != subject {
        return Err(format!("subject {subject} is not canonical"));
    }
    Ok(value)
}

impl WrapAtom {
    pub(crate) fn new(room: &str, member: &str, enc_pub: &PublicKey, key: &RoomKey) -> Result<Self> {
        Ok(Self {
            epoch: key.epoch(),
            member: subject_number(member)?,
            enc_pub: *enc_pub.as_bytes(),
            wrapped: wrap_room_key(room, member, enc_pub, key)?,
        })
    }

    pub(crate) fn payload(&self) -> Vec<u8> {
        [&self.enc_pub[..], &self.wrapped.to_bytes()].concat()
    }

    pub(crate) fn from_atom(id: &str, payload: &[u8]) -> Result<Self> {
        let (epoch, member) = parse_wrap_atom_id(id)?;
        if payload.len() != 32 + WRAPPED_LEN {
            return Err(format!("wrap atom {id} is {} bytes, not {}", payload.len(), 32 + WRAPPED_LEN));
        }
        Ok(Self {
            epoch,
            member,
            enc_pub: payload[..32].try_into().expect("32 bytes"),
            wrapped: Wrapped::from_bytes(&payload[32..])?,
        })
    }

    /// The content action that writes this wrap.
    pub(crate) fn action(&self) -> Value {
        json!({"type":"createAtom","atom":wrap_atom_id(self.epoch, self.member),
            "kind":{"type":"inlineObject","schema":wrap_schema()},"payload":hex(&self.payload())})
    }

    pub(crate) fn open(&self, room: &str, secret: &StaticSecret) -> Result<RoomKey> {
        unwrap_room_key(room, self.epoch, &self.member.to_string(), secret, &self.wrapped)
    }
}

/// Every wrap atom in a signed view of a keys cell. An atom of the wrap schema
/// that does not parse is an error: only the founder writes this cell.
pub(crate) fn wraps_in_view(view: &Value) -> Result<Vec<WrapAtom>> {
    fn walk(value: &Value, schema: &str, out: &mut Vec<Result<WrapAtom>>) {
        match value {
            Value::Array(items) => items.iter().for_each(|item| walk(item, schema, out)),
            Value::Object(object) => {
                let wrap = object.get("type").and_then(Value::as_str) == Some("atom")
                    && object.get("kind").and_then(|k| k.get("schema")).and_then(Value::as_str)
                        == Some(schema);
                if wrap {
                    out.push((|| {
                        let id = object.get("id").and_then(Value::as_str).ok_or("wrap atom lacks id")?;
                        let payload = object
                            .get("payload")
                            .and_then(Value::as_str)
                            .ok_or("wrap atom lacks payload")?;
                        WrapAtom::from_atom(id, &private::decode_hex(payload)?)
                    })());
                } else {
                    object.values().for_each(|item| walk(item, schema, out));
                }
            }
            _ => {}
        }
    }
    let mut found = Vec::new();
    walk(view, &wrap_schema(), &mut found);
    let mut wraps = found.into_iter().collect::<Result<Vec<_>>>()?;
    wraps.sort_by_key(|w| (w.epoch, w.member));
    wraps.dedup();
    Ok(wraps)
}

/// The room's epoch: the largest epoch any wrap names.
pub(crate) fn current_epoch(wraps: &[WrapAtom]) -> Option<u32> {
    wraps.iter().map(|w| w.epoch).max()
}

/// Members at `epoch` (with the public key each was wrapped to).
pub(crate) fn members_at(wraps: &[WrapAtom], epoch: u32) -> BTreeMap<u64, [u8; 32]> {
    wraps.iter().filter(|w| w.epoch == epoch).map(|w| (w.member, w.enc_pub)).collect()
}

/// The wraps a rotation writes: a fresh key at `epoch + 1` for every member at
/// `epoch` who is still `current` and is not `dropped`. Returns the new key, the
/// wraps, and the members left out.
pub(crate) fn rotation(
    room: &str,
    wraps: &[WrapAtom],
    current: &BTreeSet<u64>,
    dropped: Option<u64>,
) -> Result<(RoomKey, Vec<WrapAtom>, Vec<u64>)> {
    let epoch = current_epoch(wraps).ok_or("the room has no keys yet")?;
    let next = RoomKey::generate(epoch.checked_add(1).ok_or("room-key epoch exhausted")?)?;
    let mut out = Vec::new();
    let mut left = Vec::new();
    for (member, enc_pub) in members_at(wraps, epoch) {
        if Some(member) == dropped || !current.contains(&member) {
            left.push(member);
            continue;
        }
        out.push(WrapAtom::new(room, &member.to_string(), &PublicKey::from(enc_pub), &next)?);
    }
    Ok((next, out, left))
}

// ---------------------------------------------------------------- envelopes in streams

/// Seal one stream entry's plaintext for `room` under `key`, bound to the stream
/// cell and the sequence the entry will take. The result is the entry's payload.
pub(crate) fn seal_for_room(
    key: &RoomKey,
    room: &str,
    stream: &str,
    sequence: &str,
    plaintext: &[u8],
) -> Result<Vec<u8>> {
    let limit = private::max_value_within(MAX_STREAM_PAYLOAD);
    if plaintext.len() > limit {
        return Err(format!("a sealed entry carries at most {limit} bytes; this one is {}", plaintext.len()));
    }
    let place = Place { room, cell: stream, address: sequence };
    Ok(seal(key, &place, plaintext)?.to_bytes())
}

/// Open one stream entry's payload. With the epoch's key: `{epoch, commit,
/// text|hex}`. Without it: the sealed marker (a string). A payload that is not an
/// envelope: `{unsealed: text|hex}` (a member posted plaintext into a private
/// room). A failed open: `{refused, epoch}`.
pub(crate) fn open_in_room(
    keys: Option<&Keyring>,
    room: &str,
    stream: &str,
    sequence: &str,
    payload: &[u8],
) -> Value {
    if !payload.starts_with(private::ENVELOPE_FRAME) {
        return json!({"unsealed": text_or_hex(payload)});
    }
    let envelope = match PrivateEnvelope::from_bytes(payload) {
        Ok(envelope) => envelope,
        Err(error) => return json!({"refused": error}),
    };
    let marker = Value::String(private::sealed_marker(envelope.epoch));
    let Some(keys) = keys else { return marker };
    if keys.get(room, envelope.epoch).is_none() {
        return marker;
    }
    let place = Place { room, cell: stream, address: sequence };
    match open(keys, &place, &envelope) {
        Ok(opened) => {
            // The blinder is what opens the commitment: a member can show a
            // referee that this entry's `commit` holds this text.
            let mut value = json!({"epoch": envelope.epoch, "commit": hex(&envelope.commit),
                "blinder": hex(&opened.blinder)});
            match String::from_utf8(opened.value.clone()) {
                Ok(text) => value["text"] = json!(text),
                Err(_) => value["hex"] = json!(hex(&opened.value)),
            }
            value
        }
        Err(error) => json!({"refused": error, "epoch": envelope.epoch}),
    }
}

fn text_or_hex(bytes: &[u8]) -> Value {
    match std::str::from_utf8(bytes) {
        Ok(text) => json!(text),
        Err(_) => json!(hex(bytes)),
    }
}

// ---------------------------------------------------------------- hosted subjects (B6)

/// PRIVACY B6. A subject whose signing key is a file on this box (a hosted
/// friend, hosted Hermes, a bot) invited into a private room puts the room key
/// where root can read it. Refused unless the inviter said `--i-know`.
pub(crate) fn hosted_private_invite(
    room_private: bool,
    invitee_hosted: bool,
    i_know: bool,
) -> std::result::Result<(), String> {
    if room_private && invitee_hosted && !i_know {
        return Err(HOSTED_REFUSAL.into());
    }
    Ok(())
}

pub(crate) const HOSTED_REFUSAL: &str = "the invitee is a hosted subject (its signing key, and so the X25519 key a wrap opens with, is a file on this box) and this room is --private: wrapping the room key to it puts the room key where root can read it, and a hosted Hermes sends what it reads to its model provider; the room is then readable on the box. Repeat with --i-know to invite anyway";

/// The operator's list of hosted subjects: one decimal per line, `#` comments.
/// An absent file lists nobody (a friend's own machine has none).
pub(crate) fn hosted_subjects() -> Result<(PathBuf, BTreeSet<String>)> {
    let path = std::env::var_os(HOSTED_SUBJECTS_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(HOSTED_SUBJECTS_DEFAULT));
    let text = match fs::read_to_string(&path) {
        Ok(text) => text,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok((path, BTreeSet::new())),
        Err(error) => return Err(format!("cannot read the hosted-subject list {}: {error}", path.display())),
    };
    let mut out = BTreeSet::new();
    for line in text.lines() {
        let line = line.split('#').next().unwrap_or("").trim();
        if !line.is_empty() {
            subject_number(line)?;
            out.insert(line.to_owned());
        }
    }
    Ok((path, out))
}

// ---------------------------------------------------------------- the cache

fn passphrase() -> Result<Zeroizing<Vec<u8>>> {
    std::env::var_os(KEYCACHE_PASSPHRASE_ENV)
        .map(|value| Zeroizing::new(value.into_encoded_bytes()))
        .ok_or_else(|| {
            format!("a private room's keys live in this workspace's encrypted key cache: set {KEYCACHE_PASSPHRASE_ENV}")
        })
}

fn cache_path(root: &Path) -> PathBuf {
    root.join("private").join("keys.cache")
}

fn load_ring(root: &Path, passphrase: &[u8]) -> Result<Keyring> {
    let path = cache_path(root);
    if !path.exists() {
        return Ok(Keyring::default());
    }
    private::load_cache(&path, passphrase)
}

fn save_ring(root: &Path, passphrase: &[u8], ring: &Keyring) -> Result<()> {
    let dir = root.join("private");
    if !dir.exists() {
        make_private_dir(&dir)?;
    }
    private::save_cache(&cache_path(root), passphrase, ring)
}

/// This workspace's X25519 secret, derived from the seed its signing key file holds.
fn own_secret(workspace: &Value) -> Result<StaticSecret> {
    let path = member_path(workspace, "key")?;
    Ok(derive_enc_key(&*seed_of(&path)?))
}

pub(crate) fn seed_of(path: &Path) -> Result<Zeroizing<[u8; 32]>> {
    let bytes = Zeroizing::new(
        fs::read(path).map_err(|error| format!("cannot read signing key {}: {error}", path.display()))?,
    );
    let seed: [u8; 32] = bytes
        .as_slice()
        .try_into()
        .map_err(|_| format!("signing key {} must contain exactly 32 raw bytes", path.display()))?;
    Ok(Zeroizing::new(seed))
}

/// `mini enc-public --secret KEY`: the X25519 public key an inviter wraps to.
pub(crate) fn enc_public_hex(secret: &Path) -> Result<String> {
    Ok(hex(enc_public(&*seed_of(secret)?).as_bytes()))
}

// ---------------------------------------------------------------- references

/// A room reference that is private: `(room id, keys cell id)`.
pub(crate) fn private_room(root: &Path, room: &str) -> Result<(Value, String, String)> {
    let room_ref = reference(root, room)?;
    let keys = room_ref
        .get("private")
        .and_then(|p| p.get("keys"))
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{room} is not a private room (its reference names no keys cell)"))?
        .to_owned();
    let id = member(&room_ref, "target")?.to_owned();
    Ok((room_ref, id, keys))
}

/// A reference value for reading the keys cell with the room grant.
fn keys_view_ref(room_ref: &Value, keys: &str) -> Result<Value> {
    Ok(json!({"kind":"object","target":keys,
        "observeCapability":member(room_ref,"observeCapability")?}))
}

/// Replace a reference file in place (temporary file + rename, 0600).
pub(crate) fn rewrite_reference(root: &Path, name: &str, value: &Value) -> Result<()> {
    let path = root.join("refs").join(format!("{name}.json"));
    let temporary = root.join("refs").join(format!(".{name}.json.tmp"));
    let _ = fs::remove_file(&temporary);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&temporary)
        .map_err(|error| format!("cannot create {}: {error}", temporary.display()))?;
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    file.write_all(&bytes)
        .and_then(|()| file.sync_all())
        .map_err(|error| format!("cannot write {}: {error}", temporary.display()))?;
    fs::rename(&temporary, &path).map_err(|error| format!("cannot replace {}: {error}", path.display()))
}

// ---------------------------------------------------------------- reading the room

pub(crate) struct Synced {
    pub(crate) room: String,
    pub(crate) wraps: Vec<WrapAtom>,
    pub(crate) ring: Keyring,
    pub(crate) learned: Vec<u32>,
}

impl Synced {
    pub(crate) fn epoch(&self) -> Option<u32> {
        current_epoch(&self.wraps)
    }
}

/// Read the keys cell with this workspace's room grant and store every epoch
/// wrapped for this subject that the cache does not hold (and has not forgotten).
pub(crate) fn sync(root: &Path, workspace: &Value, room_name: &str) -> Result<Synced> {
    let passphrase = passphrase()?;
    let (room_ref, room, keys) = private_room(root, room_name)?;
    let (view, _, _) = signed_view(root, workspace, &keys_view_ref(&room_ref, &keys)?, "resource")?;
    let wraps = wraps_in_view(&view)?;
    let mut ring = load_ring(root, &passphrase)?;
    let me = subject_number(member(workspace, "subject")?)?;
    let secret = own_secret(workspace)?;
    let mut learned = Vec::new();
    for wrap in wraps.iter().filter(|w| w.member == me) {
        if ring.get(&room, wrap.epoch).is_some() || ring.is_forgotten(&room, wrap.epoch) {
            continue;
        }
        match wrap.open(&room, &secret) {
            Ok(key) => {
                ring.insert(&room, &key);
                learned.push(wrap.epoch);
            }
            Err(error) => eprintln!(
                "room {room_name}: the wrap for you at epoch {} does not open under your key ({error}); the inviter used another encryption key",
                wrap.epoch
            ),
        }
    }
    if !learned.is_empty() {
        save_ring(root, &passphrase, &ring)?;
        eprintln!("room {room_name}: learned epoch(s) {learned:?} from the keys cell");
    }
    Ok(Synced { room, wraps, ring, learned })
}

/// The key a writer seals under: the room's current epoch, which this client
/// must hold. A member who was never wrapped at it, or was kicked, refuses here.
pub(crate) fn current_key(root: &Path, workspace: &Value, room_name: &str) -> Result<(String, RoomKey)> {
    let synced = sync(root, workspace, room_name)?;
    let epoch = synced.epoch().ok_or_else(|| format!("{room_name} has no keys yet"))?;
    let key = synced.ring.get(&synced.room, epoch).ok_or_else(|| {
        format!("{room_name} is at epoch {epoch} and this client holds no key for it: nothing is sealed (were you removed, or never given a wrap?)")
    })?;
    Ok((synced.room, key))
}

/// The keys this reader may open with: synced when a passphrase is set, none otherwise.
pub(crate) fn reader_keys(root: &Path, workspace: &Value, room_name: &str) -> Result<(String, Option<Keyring>)> {
    if std::env::var_os(KEYCACHE_PASSPHRASE_ENV).is_none() {
        let (_, room, _) = private_room(root, room_name)?;
        return Ok((room, None));
    }
    let synced = sync(root, workspace, room_name)?;
    Ok((synced.room, Some(synced.ring)))
}

// ---------------------------------------------------------------- writing (one turn each)

/// Propose and submit one request under `proposal_id`.
fn turn(root: &Path, workspace: &Value, proposal_id: &str, request: &Value) -> Result<()> {
    validate_name(proposal_id)?;
    let source = root.join("sources").join(format!("roomkey-{proposal_id}.json"));
    let mut bytes = serde_json::to_vec_pretty(request).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    super::private_file(&source, &bytes)?;
    propose(root, workspace, &source, proposal_id, None)?;
    submit_intent(
        root,
        workspace,
        &root.join("proposals").join(proposal_id).join("intent.json"),
        "intent",
        false,
        Some(&root.join("attempts").join(proposal_id)),
    )
}

fn write_wraps(root: &Path, workspace: &Value, keys_ref: &str, proposal_id: &str, wraps: &[WrapAtom]) -> Result<()> {
    if wraps.is_empty() || wraps.len() > 64 {
        return Err(format!("one keys write carries 1..64 wraps, not {}", wraps.len()));
    }
    let actions: Vec<Value> = wraps.iter().map(WrapAtom::action).collect();
    turn(root, workspace, proposal_id, &json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":[{"name":keys_ref,"payload":{"type":"content","actions":actions}}]}))
}

/// The keys cell reference this workspace writes through: the founder's own
/// (born with the room), or, for anyone else, one made from its room grant --
/// which the keys cell's law refuses for every write (`keysLaw_refuses_nonfounder_write`).
fn writable_keys_ref(root: &Path, room_name: &str, room_ref: &Value, keys: &str) -> Result<String> {
    let name = keys_name(room_name)?;
    if !root.join("refs").join(format!("{name}.json")).exists() {
        let capability = member(room_ref, "operationCapability")?;
        rewrite_reference(root, &name, &json!({"type":"minidregg-participant-reference-v1","name":name,
            "kind":"object","target":keys,"observeCapability":member(room_ref,"observeCapability")?,
            "operationCapability":capability,"controlCapability":null,"provenance":null,
            "authority":"hint-only"}))?;
    }
    Ok(name)
}

/// `room new NAME --private`, after the room cell is born: draw `k_R^0`, birth
/// the keys cell in the room under the keys law, mark the room reference private,
/// and wrap every epoch this founder holds to itself. Each step is skipped when
/// already done, so a failure part-way is finished by running it again.
pub(crate) fn found(root: &Path, workspace: &Value, room_name: &str) -> Result<()> {
    let passphrase = passphrase()?;
    let mut room_ref = reference(root, room_name)?;
    let room = member(&room_ref, "target")?.to_owned();
    let founder = member(workspace, "subject")?.to_owned();
    let mut ring = load_ring(root, &passphrase)?;
    if ring.latest(&room).is_none() {
        ring.insert(&room, &RoomKey::generate(0)?);
        save_ring(root, &passphrase, &ring)?;
        eprintln!("room {room_name}: drew the epoch-0 room key (kept in {})", cache_path(root).display());
    }
    let keys_ref = keys_name(room_name)?;
    if !root.join("refs").join(format!("{keys_ref}.json")).exists() {
        let law = root.join("sources").join(format!("roomkey-law-{keys_ref}.json"));
        if !law.exists() {
            super::private_file(&law, &serde_json::to_vec(&keys_law(&founder)).map_err(|e| e.to_string())?)?;
        }
        super::create(root, workspace, &keys_ref, "content", &law, Some(room_name), "object", None, None, None)?;
    }
    let keys = member(&reference(root, &keys_ref)?, "target")?.to_owned();
    if room_ref.get("private").and_then(|p| p.get("keys")).and_then(Value::as_str) != Some(keys.as_str()) {
        room_ref["private"] = json!({"keys": keys});
        rewrite_reference(root, room_name, &room_ref)?;
    }
    let synced = sync(root, workspace, room_name)?;
    let me = subject_number(&founder)?;
    let mine: BTreeSet<u32> = synced.wraps.iter().filter(|w| w.member == me).map(|w| w.epoch).collect();
    let public = PublicKey::from(&own_secret(workspace)?);
    let mut wraps = Vec::new();
    for epoch in synced.ring.epochs(&room) {
        if !mine.contains(&epoch) {
            let key = synced.ring.get(&room, epoch).expect("listed epoch");
            wraps.push(WrapAtom::new(&room, &founder, &public, &key)?);
        }
    }
    if !wraps.is_empty() {
        let nonce = super::random_nonce()?;
        write_wraps(root, workspace, &keys_ref, &format!("rk-self-{}", &nonce[nonce.len().saturating_sub(16)..]), &wraps)?;
    }
    println!("{}", serde_json::to_string_pretty(&json!({"type":"minidregg-private-room-v1",
        "room":room_name,"target":room,"keys":keys,"epochs":synced.ring.epochs(&room)}))
        .map_err(|e| e.to_string())?);
    Ok(())
}

/// B6, before anything is proposed: a hosted invitee needs `--i-know`.
pub(crate) fn check_invitee(invitee: &str, i_know: bool) -> Result<()> {
    subject_number(invitee)?;
    let (list, hosted) = hosted_subjects()?;
    hosted_private_invite(true, hosted.contains(invitee), i_know)
        .map_err(|why| format!("{why} ({invitee} is listed in {})", list.display()))
}

/// The invitee half of `room invite` for a private room: wrap the current epoch
/// (and, with `past`, every earlier epoch this inviter holds) to the invitee's
/// X25519 key, in one write of the keys cell. The grant is K-ROOM's delegation.
pub(crate) fn invite(
    root: &Path,
    workspace: &Value,
    room_name: &str,
    invitee: &str,
    enc_pub_hex: &str,
    past: bool,
    i_know: bool,
    proposal_id: &str,
) -> Result<()> {
    check_invitee(invitee, i_know)?;
    let enc: [u8; 32] = private::decode_hex(enc_pub_hex.trim())?
        .try_into()
        .map_err(|_| "an encryption public key is 32 bytes (64 hex digits): `mini enc-public`, or `whoami` in the shell".to_owned())?;
    let enc = PublicKey::from(enc);
    let (room_ref, room, keys) = private_room(root, room_name)?;
    let synced = sync(root, workspace, room_name)?;
    let epoch = synced.epoch().ok_or_else(|| format!("{room_name} has no keys yet"))?;
    if synced.ring.get(&room, epoch).is_none() {
        return Err(format!("{room_name} is at epoch {epoch} and this client holds no key for it"));
    }
    let wrapped: BTreeSet<u32> = synced
        .wraps
        .iter()
        .filter(|w| w.member.to_string() == invitee)
        .map(|w| w.epoch)
        .collect();
    let epochs: Vec<u32> = if past {
        synced.ring.epochs(&room).into_iter().filter(|e| *e <= epoch).collect()
    } else {
        vec![epoch]
    };
    let mut wraps = Vec::new();
    for e in epochs {
        if wrapped.contains(&e) {
            eprintln!("room {room_name}: {invitee} already holds a wrap at epoch {e}");
            continue;
        }
        let key = synced.ring.get(&room, e).expect("listed epoch");
        wraps.push(WrapAtom::new(&room, invitee, &enc, &key)?);
    }
    if wraps.is_empty() {
        return Err(format!("{invitee} already holds a wrap at every epoch asked for"));
    }
    let keys_ref = writable_keys_ref(root, room_name, &room_ref, &keys)?;
    let epochs: Vec<u32> = wraps.iter().map(|w| w.epoch).collect();
    write_wraps(root, workspace, &keys_ref, proposal_id, &wraps)?;
    eprintln!("room {room_name}: wrapped epoch(s) {epochs:?} for {invitee}");
    Ok(())
}

/// Rotate: a fresh key at the next epoch, wrapped for every member at the
/// current epoch who still holds a grant covering the room (the Host's `who`)
/// and is not `dropped`.
pub(crate) fn rotate(
    root: &Path,
    workspace: &Value,
    room_name: &str,
    dropped: Option<&str>,
    proposal_id: &str,
) -> Result<()> {
    let passphrase = passphrase()?;
    let (room_ref, room, keys) = private_room(root, room_name)?;
    let synced = sync(root, workspace, room_name)?;
    let (who, _, _) = signed_view(root, workspace, &room_ref, "who")?;
    let current: BTreeSet<u64> = who
        .get("members")
        .and_then(Value::as_array)
        .ok_or("the Host's who view lists no members")?
        .iter()
        .filter_map(|m| m.get("subject").and_then(Value::as_str))
        .filter_map(|s| s.parse().ok())
        .collect();
    let dropped = dropped.map(subject_number).transpose()?;
    let (next, wraps, left) = rotation(&room, &synced.wraps, &current, dropped)?;
    let me = subject_number(member(workspace, "subject")?)?;
    if !wraps.iter().any(|w| w.member == me) {
        return Err("this rotation would not wrap the new key to its writer: only a current member rotates".into());
    }
    let keys_ref = writable_keys_ref(root, room_name, &room_ref, &keys)?;
    write_wraps(root, workspace, &keys_ref, proposal_id, &wraps)?;
    let mut ring = load_ring(root, &passphrase)?;
    ring.insert(&room, &next);
    save_ring(root, &passphrase, &ring)?;
    let members: Vec<String> = wraps.iter().map(|w| w.member.to_string()).collect();
    let left: Vec<String> = left.iter().map(u64::to_string).collect();
    println!("{}", serde_json::to_string_pretty(&json!({"type":"minidregg-room-rotation-v1",
        "room":room_name,"epoch":next.epoch(),"wrappedFor":members,"leftOut":left,
        "note":"those left out keep the past; they get nothing new"})).map_err(|e| e.to_string())?);
    Ok(())
}

/// `room kick` in a private room: the K-ROOM revoke, then the rotation.
pub(crate) fn kick(root: &Path, workspace: &Value, room_name: &str, subject: &str, proposal_id: &str) -> Result<()> {
    private_room(root, room_name)?;
    turn(root, workspace, proposal_id, &json!({"type":"minidregg-workspace-proposal-v1",
        "action":"revoke","name":room_name,"recipient":subject}))?;
    rotate(root, workspace, room_name, Some(subject), &format!("{proposal_id}-rotate"))
}

/// `room keys NAME`: the epochs this client holds (local; no Host call).
pub(crate) fn list(root: &Path, room_name: &str) -> Result<()> {
    let passphrase = passphrase()?;
    let (_, room, keys) = private_room(root, room_name)?;
    let ring = load_ring(root, &passphrase)?;
    println!("{}", serde_json::to_string_pretty(&json!({"type":"minidregg-room-keys-v1",
        "room":room_name,"target":room,"keys":keys,"held":ring.epochs(&room),
        "forgotten":ring.forgotten(&room),"authority":"local"})).map_err(|e| e.to_string())?);
    Ok(())
}

/// `forget NAME [EPOCH]`: delete this client's copies (all epochs, or one).
pub(crate) fn forget(root: &Path, room_name: &str, epoch: Option<u32>) -> Result<()> {
    let passphrase = passphrase()?;
    let (_, room, _) = private_room(root, room_name)?;
    let mut ring = load_ring(root, &passphrase)?;
    let epochs = match epoch {
        Some(epoch) => vec![epoch],
        None => ring.epochs(&room),
    };
    let mut gone = Vec::new();
    for epoch in epochs {
        if ring.forget(&room, epoch) {
            gone.push(epoch);
        }
    }
    save_ring(root, &passphrase, &ring)?;
    println!("{}", serde_json::to_string_pretty(&json!({"type":"minidregg-room-forget-v1",
        "room":room_name,"forgotten":gone,"held":ring.epochs(&room),
        "note":"this client deleted these keys and will not unwrap them again; the wraps stay in the room's keys cell, so your encryption key could still open them until it is rotated"}))
        .map_err(|e| e.to_string())?);
    Ok(())
}

/// Open one sealed payload with this client's cache alone (no Host call): what a
/// member who was removed can still read of what it already fetched, and what a
/// reader re-renders from a retained view.
pub(crate) fn open_local(root: &Path, room_name: &str, stream: &str, sequence: &str, payload_hex: &str) -> Result<()> {
    let passphrase = passphrase()?;
    let (_, room, _) = private_room(root, room_name)?;
    let ring = load_ring(root, &passphrase)?;
    let note = open_in_room(Some(&ring), &room, stream, sequence, &private::decode_hex(payload_hex.trim())?);
    println!("{}", serde_json::to_string_pretty(&json!({"type":"minidregg-room-open-v1",
        "room":room_name,"stream":stream,"sequence":sequence,"private":note,"authority":"local"}))
        .map_err(|e| e.to_string())?);
    Ok(())
}

// ---------------------------------------------------------------- the tail

/// A signed window of a stream (`QueryView.tail`), retained like `signed_view`.
fn signed_window(root: &Path, workspace: &Value, reference: &Value, start: &str, count: &str) -> Result<Value> {
    let (attempt, nonce) = super::new_attempt(root)?;
    let intent = json!({"subject":member(workspace,"subject")?,"nonce":nonce,
        "purpose":{"type":"query","kind":member(reference,"kind")?,
            "target":member(reference,"target")?,"view":"tail","start":start,"count":count},
        "grants":[{"kind":member(reference,"kind")?,"target":member(reference,"target")?,
            "capability":member(reference,"observeCapability")?}]});
    let source = root.join("sources").join(format!("q-{nonce}.json"));
    super::private_file(&source, &serde_json::to_vec(&intent).map_err(|e| e.to_string())?)?;
    query_retained(
        &member_path(workspace, "host")?,
        &member_path(workspace, "config")?,
        &source,
        OsStr::new("intent"),
        &member_path(workspace, "key")?,
        "view-tail",
        &attempt,
    )
}

/// `workspace tail --private ROOM`: the signed window, every entry annotated
/// with `private` (its opening, the sealed marker, or why it refused).
pub(crate) fn tail(root: &Path, workspace: &Value, name: &str, start: &str, count: &str, room_name: &str) -> Result<()> {
    let (room, keys) = reader_keys(root, workspace, room_name)?;
    let stream_ref = reference(root, name)?;
    let stream = member(&stream_ref, "target")?.to_owned();
    let mut view = signed_window(root, workspace, &stream_ref, start, count)?;
    let (mut opened, mut sealed) = (0usize, 0usize);
    if let Some(entries) = view.get_mut("entries").and_then(Value::as_array_mut) {
        for entry in entries {
            let sequence = entry.get("sequence").and_then(Value::as_str).unwrap_or("").to_owned();
            let note = match entry.get("payload").and_then(Value::as_str).map(private::decode_hex) {
                Some(Ok(bytes)) => open_in_room(keys.as_ref(), &room, &stream, &sequence, &bytes),
                Some(Err(error)) => json!({"refused": error}),
                None => json!({"refused": "the view carried no payload for this entry"}),
            };
            if note.get("text").is_some() || note.get("hex").is_some() {
                opened += 1;
            } else if note.is_string() {
                sealed += 1;
            }
            entry["private"] = note;
        }
    }
    eprintln!("workspace tail: {opened} opened, {sealed} sealed without a key, under room {room_name}");
    println!("{}", serde_json::to_string_pretty(&view).map_err(|e| e.to_string())?);
    Ok(())
}

/// Read a JSON request file (the shell's spelling) for `room-key --op invite`.
pub(crate) fn request(path: &Path) -> Result<Value> {
    bounded_json(path)
}

#[cfg(test)]
mod tests {
    use super::*;

    const ROOM: &str = "71";

    fn wrap_for(seed: u8, member: &str, key: &RoomKey) -> WrapAtom {
        WrapAtom::new(ROOM, member, &enc_public(&[seed; 32]), key).unwrap()
    }

    fn atom_view(wraps: &[WrapAtom]) -> Value {
        let entries: Vec<Value> = wraps
            .iter()
            .map(|w| {
                let a = w.action();
                json!({"type":"atom","id":a["atom"],"kind":a["kind"],"payload":a["payload"]})
            })
            .collect();
        json!({"cell":{"entries":entries}})
    }

    #[test]
    fn wrap_atoms_round_trip_through_a_view_and_open_only_for_their_member() {
        let e0 = RoomKey::generate(0).unwrap();
        let wraps = vec![wrap_for(1, "11", &e0), wrap_for(2, "12", &e0)];
        let parsed = wraps_in_view(&atom_view(&wraps)).unwrap();
        assert_eq!(parsed, wraps);
        assert_eq!(parsed[0].action()["atom"], "11");
        let key = parsed[1].open(ROOM, &derive_enc_key(&[2; 32])).unwrap();
        assert_eq!((key.epoch(), key.bytes()), (0, e0.bytes()));
        assert!(parsed[1].open(ROOM, &derive_enc_key(&[1; 32])).is_err(), "a member cannot open another's wrap");
        assert!(parsed[1].open("70", &derive_enc_key(&[2; 32])).is_err(), "a wrap is bound to its room");
    }

    #[test]
    fn wrap_atom_ids_name_one_epoch_and_member_and_refuse_noncanonical_forms() {
        assert_eq!(wrap_atom_id(0, 12), "12");
        assert_eq!(wrap_atom_id(1, 12), (18446744073709551616u128 + 12).to_string());
        assert_eq!(parse_wrap_atom_id(&wrap_atom_id(7, u64::MAX)).unwrap(), (7, u64::MAX));
        assert!(parse_wrap_atom_id("012").is_err());
        assert!(parse_wrap_atom_id(&(1u128 << 96).to_string()).is_err());
        let e3 = RoomKey::generate(3).unwrap();
        let mut payload = wrap_for(1, "11", &e3).payload();
        assert!(WrapAtom::from_atom("11", &payload[..payload.len() - 1]).is_err());
        payload.push(0);
        assert!(WrapAtom::from_atom("11", &payload).is_err());
    }

    #[test]
    fn a_malformed_wrap_atom_in_the_keys_cell_is_an_error_not_skipped() {
        let view = json!({"cell":{"entries":[{"type":"atom","id":"11",
            "kind":{"type":"inlineObject","schema":wrap_schema()},"payload":"00"}]}});
        assert!(wraps_in_view(&view).is_err());
        let other = json!({"cell":{"entries":[{"type":"atom","id":"11",
            "kind":{"type":"text"},"payload":"00"}]}});
        assert!(wraps_in_view(&other).unwrap().is_empty());
    }

    #[test]
    fn non_member_cannot_open_a_sealed_entry() {
        let e0 = RoomKey::generate(0).unwrap();
        let payload = seal_for_room(&e0, ROOM, "80", "1", b"meet at the lab").unwrap();
        let mut a = Keyring::default();
        a.insert(ROOM, &e0);
        assert_eq!(open_in_room(Some(&a), ROOM, "80", "1", &payload)["text"], "meet at the lab");
        let outsider = Keyring::default();
        assert_eq!(
            open_in_room(Some(&outsider), ROOM, "80", "1", &payload),
            json!("[sealed under epoch 0 — you do not hold that key]")
        );
        assert_eq!(
            open_in_room(None, ROOM, "80", "1", &payload),
            json!("[sealed under epoch 0 — you do not hold that key]")
        );
        let mut wrong = Keyring::default();
        wrong.insert(ROOM, &RoomKey::generate(0).unwrap());
        assert!(open_in_room(Some(&wrong), ROOM, "80", "1", &payload)["refused"]
            .as_str()
            .unwrap()
            .contains("integrity"));
        assert!(!payload.windows(15).any(|w| w == b"meet at the lab"));
    }

    #[test]
    fn a_sealed_entry_is_bound_to_its_stream_and_position() {
        let e0 = RoomKey::generate(0).unwrap();
        let mut a = Keyring::default();
        a.insert(ROOM, &e0);
        let payload = seal_for_room(&e0, ROOM, "80", "4", b"hi").unwrap();
        assert!(open_in_room(Some(&a), ROOM, "80", "5", &payload).get("refused").is_some());
        assert!(open_in_room(Some(&a), ROOM, "81", "4", &payload).get("refused").is_some());
        assert!(open_in_room(Some(&a), "70", "80", "4", &payload).get("refused").is_none(),
            "another room's ring has no key for it: shown sealed");
    }

    #[test]
    fn kicked_member_cannot_open_post_rotation_content_and_keeps_the_past() {
        let (a, b, c) = ("11", "12", "13");
        let e0 = RoomKey::generate(0).unwrap();
        let wraps0 = vec![wrap_for(1, a, &e0), wrap_for(2, b, &e0), wrap_for(3, c, &e0)];
        let before = seal_for_room(&e0, ROOM, "80", "1", b"before the kick").unwrap();

        let current: BTreeSet<u64> = [11, 13].into_iter().collect();
        let (e1, wraps1, left) = rotation(ROOM, &wraps0, &current, Some(12)).unwrap();
        assert_eq!(e1.epoch(), 1);
        assert_eq!(left, vec![12]);
        assert_eq!(wraps1.iter().map(|w| w.member).collect::<Vec<_>>(), vec![11, 13]);
        assert_ne!(e1.bytes(), e0.bytes(), "the next epoch is drawn, not derived");
        let after = seal_for_room(&e1, ROOM, "81", "1", b"after the kick").unwrap();
        let all: Vec<WrapAtom> = wraps0.iter().chain(&wraps1).cloned().collect();
        assert_eq!(current_epoch(&all), Some(1));

        // B synced epoch 0 before the kick and has no wrap at epoch 1.
        let mut b_ring = Keyring::default();
        b_ring.insert(ROOM, &wraps0[1].open(ROOM, &derive_enc_key(&[2; 32])).unwrap());
        assert!(all.iter().all(|w| !(w.epoch == 1 && w.member == 12)));
        assert_eq!(open_in_room(Some(&b_ring), ROOM, "80", "1", &before)["text"], "before the kick");
        assert_eq!(
            open_in_room(Some(&b_ring), ROOM, "81", "1", &after),
            json!("[sealed under epoch 1 — you do not hold that key]")
        );
        // Even B's X25519 secret opens none of the epoch-1 wraps.
        for wrap in &wraps1 {
            assert!(wrap.open(ROOM, &derive_enc_key(&[2; 32])).is_err());
        }
        // C opens both.
        let mut c_ring = Keyring::default();
        for wrap in all.iter().filter(|w| w.member == 13) {
            c_ring.insert(ROOM, &wrap.open(ROOM, &derive_enc_key(&[3; 32])).unwrap());
        }
        assert_eq!(open_in_room(Some(&c_ring), ROOM, "81", "1", &after)["text"], "after the kick");
        assert_eq!(open_in_room(Some(&c_ring), ROOM, "80", "1", &before)["text"], "before the kick");
    }

    #[test]
    fn rotation_leaves_out_members_without_a_grant_and_needs_a_keyed_room() {
        let e0 = RoomKey::generate(0).unwrap();
        let wraps0 = vec![wrap_for(1, "11", &e0), wrap_for(2, "12", &e0)];
        let only_a: BTreeSet<u64> = [11].into_iter().collect();
        let (_, wraps1, left) = rotation(ROOM, &wraps0, &only_a, None).unwrap();
        assert_eq!(wraps1.len(), 1);
        assert_eq!(left, vec![12]);
        assert!(rotation(ROOM, &[], &only_a, None).is_err());
    }

    #[test]
    fn a_wrong_epoch_is_refused_by_name() {
        let e0 = RoomKey::generate(0).unwrap();
        let e1 = RoomKey::generate(1).unwrap();
        let mut ring = Keyring::default();
        ring.insert(ROOM, &e0);
        let sealed = PrivateEnvelope::from_bytes(&seal_for_room(&e1, ROOM, "80", "1", b"x").unwrap()).unwrap();
        let place = Place { room: ROOM, cell: "80", address: "1" };
        assert_eq!(open(&ring, &place, &sealed).err().unwrap(), "no key for epoch 1");
        // A wrap for epoch 0 relabelled as epoch 1 (its atom id) does not open.
        let w = wrap_for(1, "11", &e0);
        let relabelled = WrapAtom::from_atom(&wrap_atom_id(1, 11), &w.payload()).unwrap();
        assert!(relabelled.open(ROOM, &derive_enc_key(&[1; 32])).is_err());
    }

    #[test]
    fn every_sealed_payload_is_a_multiple_of_64_bytes_and_fits_a_stream_entry() {
        let e0 = RoomKey::generate(0).unwrap();
        let limit = private::max_value_within(MAX_STREAM_PAYLOAD);
        for n in (0..=limit).step_by(7).chain([limit]) {
            let payload = seal_for_room(&e0, ROOM, "80", "1", &vec![b'x'; n]).unwrap();
            assert_eq!(payload.len() % 64, 0, "length {n}");
            assert!(payload.len() <= MAX_STREAM_PAYLOAD, "length {n}");
        }
        assert!(seal_for_room(&e0, ROOM, "80", "1", &vec![b'x'; limit + 1]).is_err());
    }

    #[test]
    fn a_hosted_invitee_into_a_private_room_needs_i_know() {
        assert!(hosted_private_invite(true, true, false).unwrap_err().contains("--i-know"));
        assert!(hosted_private_invite(true, true, true).is_ok());
        assert!(hosted_private_invite(true, false, false).is_ok());
        assert!(hosted_private_invite(false, true, false).is_ok());
    }

    #[test]
    fn the_template_laws_are_the_ones_the_lean_theorems_name() {
        let law = keys_law("7");
        assert_eq!(law, json!({"type":"any","predicates":[
            {"type":"memberOf","slot":"request/verb","values":["1","3","4","5"]},
            {"type":"all","predicates":[
                {"type":"eq","slot":"request/subject","value":"7"},
                {"type":"eq","slot":"content/atom-edits","value":"0"},
                {"type":"eq","slot":"content/tombstones","value":"0"},
                {"type":"eqSlots","left":"content/operations","right":"content/atom-creates"}]}]}));
        assert!(room_law().is_object());
    }

    #[test]
    fn forgotten_epochs_are_not_relearned_and_the_cache_keeps_them_forgotten() {
        let dir = std::env::temp_dir().join(format!("mini-roomkey-forget-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        let e0 = RoomKey::generate(0).unwrap();
        let mut ring = Keyring::default();
        ring.insert(ROOM, &e0);
        assert!(ring.forget(ROOM, 0));
        assert!(ring.is_forgotten(ROOM, 0));
        let path = dir.join("keys.cache");
        private::save_cache(&path, b"pass", &ring).unwrap();
        let loaded = private::load_cache(&path, b"pass").unwrap();
        assert!(loaded.get(ROOM, 0).is_none());
        assert!(loaded.is_forgotten(ROOM, 0));
        assert_eq!(loaded.forgotten(ROOM), vec![0]);
        fs::remove_dir_all(dir).unwrap();
    }
}
