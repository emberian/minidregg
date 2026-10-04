//! The room-key protocol of a private room (PRIVACY §3.1, row 7 / B4).
//!
//! A private room `R` is a room (K-ROOM 3c) whose content the members' clients
//! seal under a ROOM KEY `k_R^e` before it reaches the socket. The founder's
//! client draws `k_R^0` at `room new NAME --private`; every later epoch `e + 1`
//! is drawn fresh at a kick (never derived from `e`). The node never holds a
//! room key. It holds WRAPS: `k_R^e` encrypted to one member's HYBRID key
//! (`private::wrap_room_key`, wrap v3: an ephemeral X25519 exchange AND an
//! ML-KEM-768 encapsulation, both shared secrets and the full transcript (both
//! ciphertexts, both public keys, room, epoch, member) into one cSHAKE256
//! key-encryption key, then XChaCha20-Poly1305) -- secure if EITHER primitive
//! survives, so a recorded wrap is not harvest-now-decrypt-later exposed to a
//! quantum adversary. DEVNET QUALITY; PRIVACY NOT AUDITED.
//!
//! THE `keys` CELL. The wraps live in one content cell born `--in R` by the
//! founder (reference `NAME-keys`), partitioned by atom id
//! (`Kernel/PrivateRoomKeys.lean`):
//!   WRAP of epoch e for member m, addressed to m's key of generation g:
//!     atom id   = (e + 1) * 2^96 + g * 2^64 + m
//!     kind      = inlineObject(schema of "DREGG/PRIVATE-AUTH-WRAP/v3")
//!     payload   = key id (32) ‖ wrap (1192) ‖ keys grant (8)
//!                 ‖ founder-signed epoch certificate (192) ‖ founder-signed delivery (108).
//!     (the key id names the recipient's hybrid key; the wrap is
//!      ephemeral X25519 (32) ‖ ML-KEM-768 ciphertext (1088) ‖ nonce (24) ‖ box (48).)
//!   RELEASE of that wrap, written in an EARLIER turn (`ReleaseStatement`):
//!     atom id   = ((2^30 + 1 + e) << 96) | g << 64 | m
//!     kind      = inlineObject(schema of "DREGG/PRIVATE-ROOM-RELEASE/v1")
//!     payload   = founder-signed commitment to the wrap's exact bytes, its
//!                 certificate, its recipient's record digest and its grant (232).
//!   m's ENCRYPTION-KEY RECORD (FIX-IDENTITY):
//!     atom id   = m
//!     kind      = inlineObject(schema of "DREGG/PRIVATE-ENC-KEY/v3")
//!     payload   = epoch (4) ‖ X25519 key (32) ‖ ML-KEM-768 encapsulation key (1184)
//!                 ‖ room (8) ‖ keys cell (8) ‖ custody (1) ‖ member signing key (32) ‖ member signature (64).
//! The signature binds the suite, room, keys cell, member, epoch, BOTH encryption keys and
//! the member's own declaration of custody (hosted on a shared box, or its own machine).
//! Pre-hybrid records (v1, v2) and wraps (v2) REFUSE by name; nothing reads them as a key.
//! Recipient selection additionally requires the record to verify under the
//! founder's PIN for that member; the record's own public key is never an anchor.
//! The generation g is the key epoch of the record a wrap was addressed to (0:
//! a key given at invite time, before any record). A second wrap to the SAME key
//! is the same id, refused by the content controller; a RE-WRAP to a member's
//! newer key is a new id. Its law (`law.keys.json`) lets only the founder write
//! wraps and releases, only by creating atoms (no edit, no tombstone); the
//! client's retained head never goes backwards; it lets each subject
//! write only its own record (one create or edit at its own number). Every
//! member may read every wrap and record (per-address observation is not on
//! this tree, and a wrap opens for one X25519 secret only). Whoever rotates
//! wraps each kept member only to its authenticated current signed RECORD.
//! An unpinned or differently-signed record refuses disclosure; an old wrap is no fallback.
//!
//! THE KEYS GRANT. A member's room grant carries no `mutate`, so at invite the
//! founder also delegates `observe, mutate` on the keys cell alone to the
//! invitee; the keys law confines that grant to the member's own record. Its
//! capability id rides in every wrap for the member (big-endian, 0 = none: the
//! founder's own), so the member learns it at its first sync and needs no
//! reference file for it.
//!
//! A MEMBER'S SIGNING-KEY ROTATION changes its X25519 key (both come from the
//! seed). `mini rotate-key` keeps the old secret in the encryption keyring
//! (`private::keyring_remember`, KEY.enc-ring) and publishes the new public key
//! as the member's record in every private room it is in (`publish_rotation`);
//! `sync` opens a wrap with whichever keyring secret it is addressed to.
//!
//! THE CLIENT'S CACHE. Each workspace keeps the epochs it holds in
//! `ROOT/private/keys.cache` (Argon2id + XChaCha20-Poly1305 under
//! `MINI_KEYCACHE_PASSPHRASE`). `sync` reads the keys cell with the reader's own
//! room grant, unwraps every wrap addressed to this subject that the cache does
//! not hold, and stores it -- an invitee's first read is its first sync.
//!
//! SEALING. `seal_for_room` seals under the room's authenticated head epoch only: a client
//! that does not hold it (a kicked member, a member never wrapped) refuses to
//! seal. The epoch is in the clear in every envelope so a reader picks its key;
//! a reader without that epoch's key is shown `private::sealed_marker` and never
//! a guess. A stream entry is bound to (room, stream cell, sequence) -- the
//! position the plan read -- so an envelope cannot be moved to another stream
//! or position unnoticed.
//!
//! FOUNDER-KEY TRANSITION. The founder's signing key can move (`rotate-key`) without a
//! re-pin by any member: `room-key --op transition` writes a record signed by the OLD
//! and the NEW key into the keys cell BEFORE the Host rotation, `rotate-key` refuses a
//! founder until it has, and every client verifies the chain from its pin
//! (`FounderChain`). See docs/PRIVATE-ROOMS-DESIGN.txt section 7.
//!
//! AUTHORITY: out-of-band PINS (`pin_founder`, `pin_member`). On a one-validator
//! devnet every served fact is the operator's word, so every epoch certificate,
//! wrap and release must verify under the PINNED founder key, and every
//! recipient record under the founder's pin for that member. The member's
//! founder pin is trust on first use through whatever channel carried it --
//! the operator, unless the member compares the printed fingerprint with the
//! founder directly. ORDERING: a wrap of an already-used key is a disclosure,
//! so it is written only after its founder-signed release record was confirmed
//! and read back unchanged (the release state machine below); a release that
//! fails readback is dead forever. Design: docs/PRIVATE-ROOMS-DESIGN.txt.
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
    self, derive_enc_key, enc_public, open, seal, unwrap_room_key, wrap_room_key, Keyring,
    MemberPublic, MemberSecret, Place, PrivateEnvelope, RoomKey, Wrapped, KEYCACHE_PASSPHRASE_ENV,
    MEMBER_PUBLIC_LEN, WRAPPED_LEN,
};
use super::{
    bounded_json, make_private_dir, member, member_path, propose, reference, signed_view,
    submit_intent, validate_name,
};
use crate::{hex, query_retained, Result};
use serde_json::{json, Value};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use sha3::{digest::{core_api::CoreWrapper, ExtendableOutput, Update, XofReader}, CShake256Core};
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
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
    private::schema_decimal_of(AUTH_WRAP_FRAME)
}

const EPOCH_FRAME: &[u8] = b"DREGG/PRIVATE-ROOM-EPOCH/v1";
const AUTH_WRAP_FRAME: &[u8] = b"DREGG/PRIVATE-AUTH-WRAP/v3";
/// The pre-hybrid wrap frame. Nothing writes it; a keys cell that holds one refuses to load.
const AUTH_WRAP_FRAME_V2: &[u8] = b"DREGG/PRIVATE-AUTH-WRAP/v2";

fn lineage_digest(parts: &[&[u8]]) -> [u8; 32] {
    let mut hash = CoreWrapper::from_core(CShake256Core::new(b"DREGG.PRIVATE-ROOM.LINEAGE/v1"));
    for part in parts {
        hash.update(&(part.len() as u64).to_be_bytes());
        hash.update(part);
    }
    let mut digest = [0; 32];
    XofReader::read(&mut hash.finalize_xof(), &mut digest);
    digest
}

/// An epoch has one key commitment and one predecessor, regardless of how many
/// members later receive a wrap. Its signer must be the room's PINNED founder
/// key (`founder_pin`); the key a certificate carries is never its own anchor.
#[derive(Clone, Debug, PartialEq, Eq)]
struct EpochCertificate {
    room: u64,
    keys: u64,
    epoch: u32,
    parent: [u8; 32],
    key_commitment: [u8; 32],
    signer: u64,
    signer_epoch: u32,
    signer_public: [u8; 32],
    signature: [u8; 64],
}

impl EpochCertificate {
    fn body(&self) -> Vec<u8> {
        [&self.room.to_be_bytes()[..], &self.keys.to_be_bytes(), &self.epoch.to_be_bytes(),
            &self.parent, &self.key_commitment, &self.signer.to_be_bytes(),
            &self.signer_epoch.to_be_bytes(), &self.signer_public].concat()
    }
    fn statement(&self) -> Vec<u8> { [EPOCH_FRAME, &[1], &self.body()].concat() }
    fn identity(&self) -> [u8; 32] { lineage_digest(&[&self.statement()]) }
    fn bytes(&self) -> Vec<u8> { [&self.body()[..], &self.signature].concat() }
    fn from_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != 192 { return Err("epoch certificate must have 192 bytes".into()); }
        Ok(Self {
            room: u64::from_be_bytes(bytes[0..8].try_into().expect("8 bytes")),
            keys: u64::from_be_bytes(bytes[8..16].try_into().expect("8 bytes")),
            epoch: u32::from_be_bytes(bytes[16..20].try_into().expect("4 bytes")),
            parent: bytes[20..52].try_into().expect("32 bytes"),
            key_commitment: bytes[52..84].try_into().expect("32 bytes"),
            signer: u64::from_be_bytes(bytes[84..92].try_into().expect("8 bytes")),
            signer_epoch: u32::from_be_bytes(bytes[92..96].try_into().expect("4 bytes")),
            signer_public: bytes[96..128].try_into().expect("32 bytes"),
            signature: bytes[128..192].try_into().expect("64 bytes"),
        })
    }
    fn sign(room: &str, keys: &str, key: &RoomKey, parent: [u8; 32],
        subject: u64, signer_epoch: u32, signer: &SigningKey) -> Result<Self> {
        let room = subject_number(room)?;
        let keys = subject_number(keys)?;
        if key.epoch() > MAX_EPOCH {
            return Err("room-key epoch exhausted".into());
        }
        let mut certificate = Self { room, keys, epoch: key.epoch(), parent,
            key_commitment: Self::commitment(room, keys, key), signer: subject,
            signer_epoch, signer_public: signer.verifying_key().to_bytes(), signature: [0; 64] };
        certificate.signature = signer.sign(&certificate.statement()).to_bytes();
        Ok(certificate)
    }
    fn commitment(room: u64, keys: u64, key: &RoomKey) -> [u8; 32] {
        lineage_digest(&[b"DREGG/PRIVATE-ROOM-KEY/v1", &room.to_be_bytes(),
            &keys.to_be_bytes(), &key.epoch().to_be_bytes(), key.secret_bytes()])
    }
    fn check_signature(&self, actual_public: &[u8; 32]) -> Result<()> {
        if self.signer_public != *actual_public { return Err("epoch signer differs from the pinned founder key".into()); }
        VerifyingKey::from_bytes(actual_public).map_err(|_| "invalid epoch signing key")?
            .verify_strict(&self.statement(), &Signature::from_bytes(&self.signature))
            .map_err(|_| "epoch certificate signature is invalid".into())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct WrapAttestation {
    certificate: EpochCertificate,
    signer: u64,
    signer_epoch: u32,
    signer_public: [u8; 32],
    signature: [u8; 64],
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct EpochHead { epoch: u32, identity: [u8; 32] }

fn advance_head(retained: Option<&EpochHead>, candidate: &EpochHead) -> Result<()> {
    if let Some(retained) = retained {
        if candidate.epoch < retained.epoch || (candidate.epoch == retained.epoch
            && candidate.identity != retained.identity) {
            return Err("room epoch rollback or equivocation against retained authenticated lineage".into());
        }
    }
    Ok(())
}

/// The certificates the founder-signed wraps carry form ONE chain: a genesis
/// certificate (zero parent) and then certificates whose epoch is strictly
/// greater than their parent's and whose parent is its identity. An epoch may be
/// skipped -- the epoch of a dead release draft is burned, never reused -- but
/// never forked. The keys cell is append-only and served whole, so the chain is
/// checked from genesis every time; a retained head must lie on it and may not
/// be passed by a lower or different head. No wraps: no head (an empty cell),
/// which a client that retains a head refuses.
fn check_epoch_chain(wraps: &[WrapAtom], retained: Option<&EpochHead>) -> Result<Option<EpochHead>> {
    let mut certificates = BTreeMap::<u32, &EpochCertificate>::new();
    let mut context = None;
    for wrap in wraps {
        let certificate = &wrap.attestation.as_ref()
            .ok_or("unsigned wraps cannot select a room epoch")?.certificate;
        if wrap.epoch != certificate.epoch { return Err("wrap epoch differs from certificate".into()); }
        let actual_context = (certificate.room, certificate.keys);
        if context.is_some_and(|expected| expected != actual_context) {
            return Err("room epoch chain crosses room or keys-cell contexts".into());
        }
        context = Some(actual_context);
        if let Some(other) = certificates.insert(certificate.epoch, certificate) {
            if other != certificate { return Err("conflicting certificates for one room epoch".into()); }
        }
    }
    let mut head: Option<EpochHead> = None;
    let mut includes_retained = retained.is_none();
    for certificate in certificates.values() {
        match &head {
            None if certificate.parent == [0; 32] => {}
            None => return Err("room epoch chain does not start at a genesis certificate".into()),
            Some(previous) if certificate.epoch > previous.epoch
                && certificate.parent == previous.identity => {}
            Some(_) => return Err("room epoch chain has a missing, forked or different predecessor".into()),
        }
        let next = EpochHead { epoch: certificate.epoch, identity: certificate.identity() };
        if retained == Some(&next) { includes_retained = true; }
        head = Some(next);
    }
    let Some(head) = head else {
        return match retained {
            None => Ok(None),
            Some(_) => Err("served keys cell has no epoch but this client retains an authenticated room epoch".into()),
        };
    };
    advance_head(retained, &head)?;
    if !includes_retained { return Err("served lineage omits or replaces the retained room epoch".into()); }
    Ok(Some(head))
}

fn epoch_head_path(root: &Path, room: &str) -> Result<PathBuf> {
    subject_number(room)?;
    Ok(root.join("private").join(format!("epoch-head-{room}.json")))
}

fn read_epoch_head(root: &Path, room: &str, keys: &str) -> Result<Option<(Value, EpochHead)>> {
    let path = epoch_head_path(root, room)?;
    if !path.exists() { return Ok(None); }
    let value = bounded_json(&path)?;
    if value["type"] != "minidregg-authenticated-room-head-v1" || value["room"] != room
        || value["keys"] != keys { return Err("retained room lineage belongs to another context".into()); }
    let epoch: u32 = member(&value, "epoch")?.parse().map_err(|_| "invalid retained epoch")?;
    let identity = crate::decode_hex(member(&value, "identity")?)?.try_into()
        .map_err(|_| "retained epoch identity must have 32 bytes")?;
    Ok(Some((value, EpochHead { epoch, identity })))
}

/// How many founder-key transitions this client has authenticated (0 for a head written
/// before any), and the founder key it saw in effect then.
fn retained_transitions(retained: Option<&Value>) -> usize {
    retained.and_then(|value| value["transitions"].as_u64()).unwrap_or(0) as usize
}

fn retained_founder_tip(retained: Option<&Value>) -> Option<[u8; 32]> {
    crate::decode_hex(retained?["founderTip"].as_str()?).ok()?.try_into().ok()
}

/// A served founder-key chain shorter than one this client already authenticated is a
/// rollback (the operator hiding the hand-over); the same length with another tip is a fork.
fn check_chain_not_rolled_back(retained: Option<&Value>, chain: &FounderChain) -> Result<()> {
    let seen = retained_transitions(retained);
    if chain.transitions() < seen {
        return Err(format!("served founder-key chain has {} transition(s) but this client already authenticated {seen}: the hand-over was hidden or rolled back", chain.transitions()));
    }
    if chain.transitions() == seen && seen > 0 && retained_founder_tip(retained).is_some_and(|tip| tip != *chain.tip()) {
        return Err("served founder-key chain forks from the one this client authenticated".into());
    }
    Ok(())
}

/// A local head preserves authority evidence across key-cache erasure. The
/// source-authenticated batch is required before this durable CAS is reached.
fn retain_epoch_head(root: &Path, room: &str, keys: &str, prior: Option<&Value>, head: &EpochHead,
    chain: &FounderChain, source_evidence: &Value) -> Result<()> {
    if prior.is_some_and(|value| value["epoch"] == head.epoch.to_string()
        && value["identity"] == hex(&head.identity)
        && retained_transitions(Some(value)) == chain.transitions()
        && retained_founder_tip(Some(value)) == Some(*chain.tip())) { return Ok(()); }
    if !root.join("private").exists() { make_private_dir(&root.join("private"))?; }
    super::publish_retained_json(&epoch_head_path(root, room)?,
        &json!({"type":"minidregg-authenticated-room-head-v1", "room":room,
            "keys":keys,"epoch":head.epoch.to_string(),"identity":hex(&head.identity),
            "transitions":chain.transitions(),"founderTip":hex(chain.tip()),
            "sourceEvidence":source_evidence}), prior)
}

// ---------------------------------------------------------------- pinned authority

/// Out-of-band pins are the authority of a private room. On a one-validator
/// devnet everything the node serves -- a subject's current key included -- is
/// the operator's word, so neither a served record's embedded key nor a served
/// certificate's signer is trusted. The FOUNDER pin is written by the founder at
/// `found` and by a member at `recipient-record --founder-key` (or
/// `pin-founder`). It is trust on first use through whatever channel carried the
/// key, which is the operator unless the member checks the printed fingerprint
/// against one the founder gave it directly. MEMBER pins are written by the
/// founder from each member's signed v3 declaration.
const FOUNDER_PIN_TYPE: &str = "minidregg-room-founder-pin-v1";
const MEMBER_PINS_TYPE: &str = "minidregg-room-member-pins-v1";

fn pin_path(root: &Path, kind: &str, room: &str) -> Result<PathBuf> {
    subject_number(room)?;
    Ok(root.join("private").join(format!("room-{kind}-{room}.json")))
}

fn verifying_key(bytes: &[u8; 32]) -> Result<VerifyingKey> {
    VerifyingKey::from_bytes(bytes).map_err(|_| "pinned key is not an Ed25519 public key".into())
}

/// A short human-comparable fingerprint of a founder key.
pub(crate) fn fingerprint(public: &[u8; 32]) -> String {
    let digest = lineage_digest(&[b"DREGG/PRIVATE-ROOM-FOUNDER-FINGERPRINT/v1", public]);
    digest[..10].chunks(2).map(hex).collect::<Vec<_>>().join("-")
}

fn ensure_private(root: &Path) -> Result<()> {
    if !root.join("private").exists() { make_private_dir(&root.join("private"))?; }
    Ok(())
}

/// Pin (or, with `replace`, re-pin) the founder key of room `room`/`keys`.
pub(crate) fn pin_founder(root: &Path, room: &str, keys: &str, public_hex: &str, replace: bool) -> Result<Value> {
    subject_number(keys)?;
    let public: [u8; 32] = crate::decode_hex(public_hex.trim())?.try_into()
        .map_err(|_| "a founder key is 32 bytes (64 hex digits)")?;
    verifying_key(&public)?;
    ensure_private(root)?;
    let path = pin_path(root, "founder", room)?;
    let value = json!({"type":FOUNDER_PIN_TYPE,"room":room,"keys":keys,"founderKeyHex":hex(&public),
        "fingerprint":fingerprint(&public)});
    let prior = if path.exists() { Some(bounded_json(&path)?) } else { None };
    match &prior {
        Some(prior) if *prior == value => return Ok(value),
        Some(_) if !replace => return Err(format!(
            "room {room} already pins a different founder key; re-pin only after checking the new fingerprint {} with the founder directly (--replace true)", fingerprint(&public))),
        _ => {}
    }
    super::publish_retained_json(&path, &value, prior.as_ref())?;
    eprintln!("room {room}: pinned founder key {} (fingerprint {}). This pin is trust on first use through the channel that carried it; compare the fingerprint with the founder directly.",
        hex(&public), fingerprint(&public));
    Ok(value)
}

fn founder_pin(root: &Path, room: &str, keys: &str) -> Result<[u8; 32]> {
    let path = pin_path(root, "founder", room)?;
    if !path.exists() {
        return Err(format!("room {room} has no pinned founder key: get it from the founder (`room-key --op pin-founder`, or `recipient-record --founder-key`); served wraps are not authority"));
    }
    let value = bounded_json(&path)?;
    if value["type"] != FOUNDER_PIN_TYPE || value["room"] != room || value["keys"] != keys {
        return Err("founder pin belongs to another room or keys cell".into());
    }
    let public: [u8; 32] = crate::decode_hex(member(&value, "founderKeyHex")?)?.try_into()
        .map_err(|_| "pinned founder key must be 32 bytes")?;
    verifying_key(&public)?;
    Ok(public)
}

fn member_pins(root: &Path, room: &str, keys: &str) -> Result<(Option<Value>, BTreeMap<u64, [u8; 32]>)> {
    let path = pin_path(root, "members", room)?;
    if !path.exists() { return Ok((None, BTreeMap::new())); }
    let value = bounded_json(&path)?;
    if value["type"] != MEMBER_PINS_TYPE || value["room"] != room || value["keys"] != keys {
        return Err("member pins belong to another room or keys cell".into());
    }
    let mut pins = BTreeMap::new();
    for (subject, key) in value["members"].as_object().ok_or("member pins lack members")? {
        let public: [u8; 32] = crate::decode_hex(key.as_str().ok_or("member pin must be hex")?)?
            .try_into().map_err(|_| "member pin must be 32 bytes")?;
        pins.insert(subject_number(subject)?, public);
    }
    Ok((Some(value), pins))
}

/// Pin a member's signing key. An existing different pin refuses unless `replace`.
fn pin_member(root: &Path, room: &str, keys: &str, subject: u64, public: &[u8; 32], replace: bool) -> Result<()> {
    verifying_key(public)?;
    let (prior, mut pins) = member_pins(root, room, keys)?;
    match pins.get(&subject) {
        Some(pinned) if pinned == public => return Ok(()),
        Some(_) if !replace => return Err(format!(
            "member {subject} declared a signing key different from the one pinned for room {room}: accept it only from the member directly (`room-key --op pin-member --replace true`)")),
        _ => {}
    }
    pins.insert(subject, *public);
    ensure_private(root)?;
    let members: serde_json::Map<String, Value> = pins.iter()
        .map(|(subject, key)| (subject.to_string(), json!(hex(key)))).collect();
    super::publish_retained_json(&pin_path(root, "members", room)?,
        &json!({"type":MEMBER_PINS_TYPE,"room":room,"keys":keys,"members":members}), prior.as_ref())
}

/// `room-key --op pin-member`: pin the signing key of a member's signed
/// v3 declaration (the founder, from the member, out of band).
pub(crate) fn pin_member_declaration(root: &Path, room_name: &str, subject: &str,
    declaration: &str, replace: bool) -> Result<Value> {
    let (_, room, keys) = private_room(root, room_name)?;
    let number = subject_number(subject)?;
    let bytes = crate::decode_hex(&recipient_argument(declaration)?)?;
    if bytes.len() != SIGNED_RECORD_LEN { return Err(format!("pin-member needs the member's signed v3 declaration ({SIGNED_RECORD_LEN} bytes)")); }
    let record = EncRecord::from_atom(subject, &bytes, &Value::Null)?;
    let signing = record.attestation.signing_public;
    record.authenticate(&room, &keys, &signing)?;
    pin_member(root, &room, &keys, number, &signing, replace)?;
    Ok(json!({"room":room_name,"member":subject,"signingKey":hex(&signing)}))
}

/// The authority of a recipient record: its signature verifies under the
/// founder's pin for that member. Nothing served constructs this.
fn authenticate_recipient(pins: &BTreeMap<u64, [u8; 32]>, room: &str, keys: &str,
    record: &EncRecord) -> Result<AuthenticatedRecord> {
    let pinned = pins.get(&record.member).ok_or_else(|| format!(
        "member {} has no pinned signing key: pin its signed declaration first", record.member))?;
    let checked = record.authenticate(room, keys, pinned)?;
    Ok(AuthenticatedRecord { record: checked.0 })
}

/// Digest of a recipient's complete signed record, as a release binds it.
fn record_digest(record: &EncRecord) -> Result<[u8; 32]> {
    Ok(lineage_digest(&[b"DREGG/PRIVATE-ENC-KEY-DIGEST/v1", &record.canonical_signed_payload()?]))
}

// ---------------------------------------------------------------- founder-key transition

/// A FOUNDER-KEY TRANSITION: the pinned founder key hands the room to its successor.
///   atom id = (2^31 + 1 + index) << 96
///   payload = room (8) ‖ keys (8) ‖ index (4) ‖ after epoch (4) ‖ after certificate
///             identity (32) ‖ old key (32) ‖ new key (32) ‖ old signature (64) ‖ new signature (64).
/// BOTH keys sign the same statement: the OLD key says "this key succeeds me, from the epoch
/// after `after epoch`", the NEW key says "I hold the secret and accept". A transition is
/// therefore unforgeable without the current founder secret (an operator, or a member, cannot
/// extend the chain) and cannot name a key nobody holds (a typo or a hostile key cannot lock
/// the room). Transitions form ONE chain: index 0, 1, 2 ... each old key is the previous new
/// key. A member's pin may be ANY key on the chain: a later key authenticates the whole chain
/// back to its first key (every link needs the later key's own signature), an earlier one
/// authenticates it forward. The epoch certificate of epoch e is signed by the key in effect
/// at e (the number of transitions with `after epoch < e` selects it); deliveries and releases
/// of epoch e by that key or any later one, because a founder may invite after rotating.
const TRANSITION_FRAME: &[u8] = b"DREGG/PRIVATE-ROOM-FOUNDER-TRANSITION/v1";
const TRANSITION_BODY_LEN: usize = 8 + 8 + 4 + 4 + 32 + 32 + 32;
const TRANSITION_HIGH_BASE: u128 = (1 << 31) + 1;
/// Transition indices fill the id region `2^31+1 ..= 2^31+2^20`, above every release.
pub(crate) const MAX_TRANSITIONS: u32 = 1 << 20;

pub(crate) fn transition_schema() -> String {
    private::schema_decimal_of(TRANSITION_FRAME)
}

pub(crate) fn transition_atom_id(index: u32) -> String {
    ((TRANSITION_HIGH_BASE + u128::from(index)) << 96).to_string()
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct FounderTransition {
    room: u64,
    keys: u64,
    index: u32,
    after_epoch: u32,
    after_certificate: [u8; 32],
    old_key: [u8; 32],
    new_key: [u8; 32],
    old_signature: [u8; 64],
    new_signature: [u8; 64],
}

impl FounderTransition {
    fn body(&self) -> Vec<u8> {
        [&self.room.to_be_bytes()[..], &self.keys.to_be_bytes(), &self.index.to_be_bytes(),
            &self.after_epoch.to_be_bytes(), &self.after_certificate, &self.old_key, &self.new_key].concat()
    }
    fn statement(&self) -> Vec<u8> { [TRANSITION_FRAME, &[1], &self.body()].concat() }
    fn payload(&self) -> Vec<u8> { [&self.body()[..], &self.old_signature, &self.new_signature].concat() }
    fn atom(&self) -> String { transition_atom_id(self.index) }

    /// Sign the hand-over from `old` to `new`, both secrets in hand, after the certificate `after`.
    fn sign(room: &str, keys: &str, index: u32, after: &EpochHead, old: &SigningKey, new: &SigningKey) -> Result<Self> {
        if index >= MAX_TRANSITIONS { return Err("founder-key transitions exhausted".into()); }
        let mut transition = Self { room: subject_number(room)?, keys: subject_number(keys)?, index,
            after_epoch: after.epoch, after_certificate: after.identity,
            old_key: old.verifying_key().to_bytes(), new_key: new.verifying_key().to_bytes(),
            old_signature: [0; 64], new_signature: [0; 64] };
        if transition.old_key == transition.new_key { return Err("a founder-key transition names a different key".into()); }
        let statement = transition.statement();
        transition.old_signature = old.sign(&statement).to_bytes();
        transition.new_signature = new.sign(&statement).to_bytes();
        Ok(transition)
    }

    fn from_atom(id: &str, payload: &[u8]) -> Result<Self> {
        if payload.len() != TRANSITION_BODY_LEN + 128 {
            return Err(format!("founder-key transition atom {id} has an invalid length"));
        }
        let u64_at = |at: usize| u64::from_be_bytes(payload[at..at + 8].try_into().expect("8 bytes"));
        let u32_at = |at: usize| u32::from_be_bytes(payload[at..at + 4].try_into().expect("4 bytes"));
        let b32 = |at: usize| -> [u8; 32] { payload[at..at + 32].try_into().expect("32 bytes") };
        let transition = Self { room: u64_at(0), keys: u64_at(8), index: u32_at(16), after_epoch: u32_at(20),
            after_certificate: b32(24), old_key: b32(56), new_key: b32(88),
            old_signature: payload[120..184].try_into().expect("64 bytes"),
            new_signature: payload[184..248].try_into().expect("64 bytes") };
        if transition.index >= MAX_TRANSITIONS || transition.atom() != id {
            return Err(format!("founder-key transition atom {id} is not at the address its statement names"));
        }
        Ok(transition)
    }

    fn action(&self) -> Value {
        json!({"type":"createAtom","atom":self.atom(),
            "kind":{"type":"inlineObject","schema":transition_schema()},"payload":hex(&self.payload())})
    }

    /// Both signatures verify over this exact statement, in this room and keys cell.
    fn check(&self, room: &str, keys: &str) -> Result<()> {
        if self.room != subject_number(room)? || self.keys != subject_number(keys)? {
            return Err("founder-key transition differs from its room or keys cell".into());
        }
        if self.old_key == self.new_key { return Err("a founder-key transition names a different key".into()); }
        let statement = self.statement();
        verifying_key(&self.old_key)?.verify_strict(&statement, &Signature::from_bytes(&self.old_signature))
            .map_err(|_| "founder-key transition: the old key's signature does not verify")?;
        verifying_key(&self.new_key)?.verify_strict(&statement, &Signature::from_bytes(&self.new_signature))
            .map_err(|_| "founder-key transition: the new key's possession signature does not verify")?;
        Ok(())
    }
}

/// Every transition in a signed view of a keys cell, by index (a malformed one is an error).
fn transitions_in_view(view: &Value) -> Result<Vec<FounderTransition>> {
    let mut atoms = Vec::new();
    collect_atoms(view, &transition_schema(), &mut atoms);
    let mut out = BTreeMap::new();
    for atom in atoms {
        let id = member(atom, "id")?;
        let transition = FounderTransition::from_atom(id, &crate::decode_hex(member(atom, "payload")?)?)?;
        if out.insert(transition.index, transition).is_some() { return Err("transition atom repeats an address".into()); }
    }
    Ok(out.into_values().collect())
}

fn collect_atoms<'a>(value: &'a Value, schema: &str, out: &mut Vec<&'a Value>) {
    match value {
        Value::Array(items) => items.iter().for_each(|item| collect_atoms(item, schema, out)),
        Value::Object(object) => {
            if object.get("type").and_then(Value::as_str) == Some("atom")
                && object.get("kind").and_then(|k| k.get("schema")).and_then(Value::as_str) == Some(schema) {
                out.push(value);
            } else {
                object.values().for_each(|item| collect_atoms(item, schema, out));
            }
        }
        _ => {}
    }
}

/// The founder keys of a room in order, and where each one's authority begins.
/// `keys[0]` is the first key on the chain; `after[i]` is the `after epoch` of the
/// transition to `keys[i + 1]`: that key is in effect for epochs strictly above it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FounderChain {
    keys: Vec<[u8; 32]>,
    after: Vec<u32>,
}

impl FounderChain {
    /// No transition: the pinned key alone.
    fn single(pin: [u8; 32]) -> Self { Self { keys: vec![pin], after: Vec::new() } }

    /// The key that signs new epochs, wraps and releases now.
    pub(crate) fn tip(&self) -> &[u8; 32] { self.keys.last().expect("a chain has a key") }

    pub(crate) fn transitions(&self) -> usize { self.after.len() }

    fn contains(&self, key: &[u8; 32]) -> bool { self.keys.contains(key) }

    fn index_for_epoch(&self, epoch: u32) -> usize { self.after.iter().filter(|after| **after < epoch).count() }

    /// The key that must have signed the certificate of `epoch`.
    fn epoch_key(&self, epoch: u32) -> &[u8; 32] { &self.keys[self.index_for_epoch(epoch)] }

    /// The keys that may sign a delivery or release of `epoch`: its own key and every later one.
    fn delivery_keys(&self, epoch: u32) -> &[[u8; 32]] { &self.keys[self.index_for_epoch(epoch)..] }

    /// Verify the served transitions against the pinned key and the served certificates.
    /// Every link: signed by both keys; the old key is the previous link's new key; its
    /// `after` names the certificate the keys cell shows at that epoch; `after epoch` never
    /// decreases. The pin must lie on the chain.
    fn verify(room: &str, keys: &str, pin: &[u8; 32], transitions: &[FounderTransition],
        certificates: &BTreeMap<u32, &EpochCertificate>) -> Result<Self> {
        let Some(first) = transitions.first() else { return Ok(Self::single(*pin)) };
        let mut chain = Self { keys: vec![first.old_key], after: Vec::new() };
        for (position, transition) in transitions.iter().enumerate() {
            if transition.index as usize != position {
                return Err("founder-key transitions are not contiguous from index 0 (a link is missing)".into());
            }
            transition.check(room, keys)?;
            if transition.old_key != *chain.tip() {
                return Err("founder-key transition does not start where the previous one ended (a fork)".into());
            }
            if chain.after.last().is_some_and(|previous| transition.after_epoch < *previous) {
                return Err("founder-key transitions go back in epochs".into());
            }
            let certificate = certificates.get(&transition.after_epoch).ok_or_else(|| format!(
                "founder-key transition {} names epoch {}, which the keys cell does not show", transition.index, transition.after_epoch))?;
            if certificate.identity() != transition.after_certificate {
                return Err(format!("founder-key transition {} names another certificate than the one at epoch {}",
                    transition.index, transition.after_epoch));
            }
            if chain.keys.contains(&transition.new_key) {
                return Err("founder-key transition returns to a key already retired".into());
            }
            chain.keys.push(transition.new_key);
            chain.after.push(transition.after_epoch);
        }
        if !chain.contains(pin) {
            return Err("the pinned founder key is not on the founder-key chain this keys cell serves".into());
        }
        Ok(chain)
    }
}

// ---------------------------------------------------------------- release records

/// The RELEASE record of one delivery, written (turn 1) before its ciphertext
/// (turn 2): founder-signed, carrying no ciphertext, only its commitment.
///   atom id = ((2^30 + 1 + epoch) << 96) | gen << 64 | member
///   payload = room (8) ‖ keys (8) ‖ epoch (4) ‖ certificate identity (32)
///             ‖ member (8) ‖ gen (4) ‖ recipient record digest (32) ‖ grant (8)
///             ‖ delivery commitment (32) ‖ signer key (32) ‖ signature (64).
/// A wrap is accepted only beside its release, and the release names its exact bytes.
const RELEASE_FRAME: &[u8] = b"DREGG/PRIVATE-ROOM-RELEASE/v1";
const RELEASE_BODY_LEN: usize = 8 + 8 + 4 + 32 + 8 + 4 + 32 + 8 + 32 + 32;
const RELEASE_HIGH_BASE: u128 = (1 << 30) + 1;

pub(crate) fn release_schema() -> String {
    private::schema_decimal_of(RELEASE_FRAME)
}

pub(crate) fn release_atom_id(epoch: u32, gen: u32, member: u64) -> String {
    (((RELEASE_HIGH_BASE + u128::from(epoch)) << 96) | (u128::from(gen) << 64) | u128::from(member)).to_string()
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReleaseStatement {
    room: u64,
    keys: u64,
    epoch: u32,
    certificate: [u8; 32],
    member: u64,
    gen: u32,
    record: [u8; 32],
    grant: u64,
    commitment: [u8; 32],
    signer_public: [u8; 32],
    signature: [u8; 64],
}

impl ReleaseStatement {
    fn body(&self) -> Vec<u8> {
        [&self.room.to_be_bytes()[..], &self.keys.to_be_bytes(), &self.epoch.to_be_bytes(),
            &self.certificate, &self.member.to_be_bytes(), &self.gen.to_be_bytes(), &self.record,
            &self.grant.to_be_bytes(), &self.commitment, &self.signer_public].concat()
    }
    fn statement(&self) -> Vec<u8> { [RELEASE_FRAME, &[1], &self.body()].concat() }
    fn payload(&self) -> Vec<u8> { [&self.body()[..], &self.signature].concat() }
    fn atom(&self) -> String { release_atom_id(self.epoch, self.gen, self.member) }

    /// Sign the release of one signed delivery.
    fn sign(wrap: &WrapAtom, record: [u8; 32], signer: &SigningKey) -> Result<Self> {
        let certificate = &wrap.attestation.as_ref().ok_or("a release names a signed delivery")?.certificate;
        let mut release = Self { room: certificate.room, keys: certificate.keys, epoch: wrap.epoch,
            certificate: certificate.identity(), member: wrap.member, gen: wrap.gen, record,
            grant: wrap.grant, commitment: wrap.payload_commitment()?,
            signer_public: signer.verifying_key().to_bytes(), signature: [0; 64] };
        release.signature = signer.sign(&release.statement()).to_bytes();
        Ok(release)
    }

    fn from_atom(id: &str, payload: &[u8]) -> Result<Self> {
        if payload.len() != RELEASE_BODY_LEN + 64 {
            return Err(format!("release atom {id} has an invalid length"));
        }
        let u64_at = |at: usize| u64::from_be_bytes(payload[at..at + 8].try_into().expect("8 bytes"));
        let u32_at = |at: usize| u32::from_be_bytes(payload[at..at + 4].try_into().expect("4 bytes"));
        let b32 = |at: usize| -> [u8; 32] { payload[at..at + 32].try_into().expect("32 bytes") };
        let release = Self { room: u64_at(0), keys: u64_at(8), epoch: u32_at(16), certificate: b32(20),
            member: u64_at(52), gen: u32_at(60), record: b32(64), grant: u64_at(96),
            commitment: b32(104), signer_public: b32(136),
            signature: payload[168..232].try_into().expect("64 bytes") };
        if release.epoch > MAX_EPOCH || release.atom() != id {
            return Err(format!("release atom {id} is not at the address its statement names"));
        }
        Ok(release)
    }

    fn action(&self) -> Value {
        json!({"type":"createAtom","atom":self.atom(),
            "kind":{"type":"inlineObject","schema":release_schema()},"payload":hex(&self.payload())})
    }

    /// The release is the room's: signed by a founder key allowed for its epoch (`chain`).
    fn check(&self, room: &str, keys: &str, chain: &FounderChain) -> Result<()> {
        if self.room != subject_number(room)? || self.keys != subject_number(keys)?
            || !chain.delivery_keys(self.epoch).contains(&self.signer_public) {
            return Err("release record differs from its room, keys cell or founder key chain".into());
        }
        verifying_key(&self.signer_public)?.verify_strict(&self.statement(), &Signature::from_bytes(&self.signature))
            .map_err(|_| "release record signature does not verify under the founder key it names".into())
    }

    /// Does this release name exactly this delivery?
    fn names(&self, wrap: &WrapAtom) -> Result<()> {
        let certificate = &wrap.attestation.as_ref().ok_or("unsigned delivery")?.certificate;
        if self.epoch != wrap.epoch || self.gen != wrap.gen || self.member != wrap.member
            || self.grant != wrap.grant || self.certificate != certificate.identity()
            || self.commitment != wrap.payload_commitment()? {
            return Err(format!("wrap at epoch {} for {} differs from the delivery its release committed to", wrap.epoch, wrap.member));
        }
        Ok(())
    }
}

/// Every release record in a signed view of a keys cell (a malformed one is an error).
fn releases_in_view(view: &Value) -> Result<BTreeMap<String, ReleaseStatement>> {
    fn walk<'a>(value: &'a Value, schema: &str, out: &mut Vec<&'a Value>) {
        match value {
            Value::Array(items) => items.iter().for_each(|item| walk(item, schema, out)),
            Value::Object(object) => {
                if object.get("type").and_then(Value::as_str) == Some("atom")
                    && object.get("kind").and_then(|k| k.get("schema")).and_then(Value::as_str) == Some(schema) {
                    out.push(value);
                } else {
                    object.values().for_each(|item| walk(item, schema, out));
                }
            }
            _ => {}
        }
    }
    let mut atoms = Vec::new();
    walk(view, &release_schema(), &mut atoms);
    let mut out = BTreeMap::new();
    for atom in atoms {
        let id = member(atom, "id")?;
        let release = ReleaseStatement::from_atom(id, &crate::decode_hex(member(atom, "payload")?)?)?;
        if out.insert(id.to_owned(), release).is_some() { return Err("release atom repeats an address".into()); }
    }
    Ok(out)
}

/// What a served keys cell proves under the pinned founder key: every release
/// and every wrap founder-signed, every wrap beside the release that committed
/// to its exact bytes, and one certificate chain consistent with the retained head.
#[derive(Debug)]
struct Lineage {
    wraps: Vec<WrapAtom>,
    releases: BTreeMap<String, ReleaseStatement>,
    certificates: BTreeMap<u32, EpochCertificate>,
    head: Option<EpochHead>,
    /// The founder keys the keys cell serves, verified against the pin.
    chain: FounderChain,
}

impl Lineage {
    /// The epoch a new release must take: above the head and above every epoch
    /// any release ever named (a dead draft's epoch is burned).
    fn next_epoch(&self) -> Result<u32> {
        let highest = self.head.as_ref().map(|head| head.epoch)
            .into_iter().chain(self.releases.values().map(|release| release.epoch)).max();
        let next = match highest { None => 0, Some(epoch) => epoch.checked_add(1).ok_or("room-key epoch exhausted")? };
        if next > MAX_EPOCH { return Err("room-key epoch exhausted".into()); }
        Ok(next)
    }
}

/// `pin` is the founder key this client pinned (out of band); it may be any key on the
/// served founder-key chain (`FounderChain::verify`).
fn verify_lineage(room: &str, keys: &str, pin: &[u8; 32], view: &Value,
    retained: Option<&EpochHead>) -> Result<Lineage> {
    let wraps = wraps_in_view(view)?;
    let releases = releases_in_view(view)?;
    let transitions = transitions_in_view(view)?;
    let mut served = BTreeMap::<u32, &EpochCertificate>::new();
    for wrap in &wraps {
        let certificate = &wrap.attestation.as_ref().ok_or("unsigned room wrap is not authenticated lineage")?.certificate;
        if let Some(other) = served.insert(certificate.epoch, certificate) {
            if other != certificate { return Err("conflicting certificates for one room epoch".into()); }
        }
    }
    let chain = FounderChain::verify(room, keys, pin, &transitions, &served)?;
    for release in releases.values() { release.check(room, keys, &chain)?; }
    let mut certificates = BTreeMap::new();
    for wrap in &wraps {
        let attestation = wrap.attestation.as_ref().expect("checked above");
        if !chain.delivery_keys(wrap.epoch).contains(&attestation.signer_public) {
            return Err("a wrap's delivery is signed by a key that is not a founder key for its epoch".into());
        }
        wrap.check_signatures(room, keys, chain.epoch_key(wrap.epoch), &attestation.signer_public)?;
        let release = releases.get(&release_atom_id(wrap.epoch, wrap.gen, wrap.member))
            .ok_or("a wrap was disclosed without a founder-signed release record")?;
        release.names(wrap)?;
        certificates.insert(attestation.certificate.epoch, attestation.certificate.clone());
    }
    let head = check_epoch_chain(&wraps, retained)?;
    Ok(Lineage { wraps, releases, certificates, head, chain })
}

/// A member's encryption-key record in the keys cell.
///
/// v3 (hybrid): `key epoch (4) || X25519 key (32) || ML-KEM-768 encapsulation key (1184)
/// || room (8) || keys cell (8) || custody (1) || member signing key (32) || member
/// signature (64)`, 1333 bytes, the signature over BOTH encryption keys and the custody
/// byte: 1 = the member declares its signing key is a file on a shared (hosted) box,
/// 0 = it declares the key stays on its own machine. v1 (unsigned, 36 bytes) and v2
/// (signed, X25519 only, 148 bytes) records refuse by name; nothing reads them as a key.
pub(crate) const RECORD_FRAME_V1: &[u8] = b"DREGG/PRIVATE-ENC-KEY/v1";
const RECORD_FRAME_V2: &[u8] = b"DREGG/PRIVATE-ENC-KEY/v2";
const SIGNED_RECORD_FRAME: &[u8] = b"DREGG/PRIVATE-ENC-KEY/v3";
const SIGNED_RECORD_LEN: usize = 4 + MEMBER_PUBLIC_LEN + 8 + 8 + 1 + 32 + 64;

pub(crate) fn record_schema() -> String {
    private::schema_decimal_of(SIGNED_RECORD_FRAME)
}

// ---------------------------------------------------------------- wrap atoms

/// One wrap in the keys cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct WrapAtom {
    pub(crate) epoch: u32,
    pub(crate) gen: u32,
    pub(crate) member: u64,
    /// The id (`MemberPublic::id`) of the hybrid key this wrap is addressed to.
    pub(crate) enc_id: [u8; 32],
    pub(crate) wrapped: Wrapped,
    /// The member's keys-cell grant (0: none).
    pub(crate) grant: u64,
    attestation: Option<WrapAttestation>,
}

const WRAP_PAYLOAD_LEN: usize = 32 + WRAPPED_LEN + 8;

/// The largest room-key epoch. Wraps take atom-id high halves 1..=2^30 and
/// release records 2^30+1..=2^31, so the two regions never meet.
pub(crate) const MAX_EPOCH: u32 = (1 << 30) - 1;

pub(crate) fn wrap_atom_id(epoch: u32, gen: u32, member: u64) -> String {
    (((u128::from(epoch) + 1) << 96) | (u128::from(gen) << 64) | u128::from(member)).to_string()
}

pub(crate) fn parse_wrap_atom_id(id: &str) -> Result<(u32, u32, u64)> {
    let value: u128 = id.parse().map_err(|_| format!("wrap atom id {id} is not a decimal below 2^128"))?;
    if value.to_string() != id {
        return Err(format!("wrap atom id {id} is not canonical"));
    }
    let high = value >> 96;
    if high == 0 {
        return Err(format!("atom id {id} is in the record region, not a wrap"));
    }
    let epoch = u32::try_from(high - 1)
        .ok()
        .filter(|epoch| *epoch <= MAX_EPOCH)
        .ok_or_else(|| format!("wrap atom id {id} exceeds the epoch range"))?;
    Ok((epoch, ((value >> 64) & 0xffff_ffff) as u32, value as u64))
}

/// One member's encryption-key record. `atom` is the record as the signed view
/// showed it: an edit names it exactly (`before`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EncRecord {
    pub(crate) member: u64,
    pub(crate) key_epoch: u32,
    pub(crate) enc: MemberPublic,
    pub(crate) atom: Value,
    attestation: KeyAttestation,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct KeyAttestation {
    room: u64,
    keys: u64,
    /// The member's own signed statement that its signing key is a file on a shared box.
    hosted: bool,
    signing_public: [u8; 32],
    signature: [u8; 64],
}

/// A record whose signature verified under a key the caller supplied.
struct SignatureCheckedRecord(EncRecord);

/// A record whose signature verified under the founder's PIN for its member
/// (`authenticate_recipient`). Its embedded signing key is never its own anchor.
#[derive(Debug)]
pub(crate) struct AuthenticatedRecord {
    record: EncRecord,
}

fn record_statement(room: u64, keys: u64, member: u64, epoch: u32, hosted: bool,
    signing_public: &[u8; 32], encryption_public: &MemberPublic) -> Vec<u8> {
    [SIGNED_RECORD_FRAME, &[1u8], &room.to_be_bytes(), &keys.to_be_bytes(),
        &member.to_be_bytes(), &epoch.to_be_bytes(), &[u8::from(hosted)], signing_public,
        &encryption_public.to_bytes()].concat()
}

impl EncRecord {
    fn signed_payload(room: &str, keys: &str, member: u64, key_epoch: u32, hosted: bool,
        enc: &MemberPublic, signer: &SigningKey) -> Result<Vec<u8>> {
        let room = subject_number(room)?;
        let keys = subject_number(keys)?;
        let public = signer.verifying_key().to_bytes();
        let signature = signer.sign(&record_statement(room, keys, member, key_epoch, hosted, &public, enc));
        Ok([&key_epoch.to_be_bytes()[..], &enc.to_bytes(), &room.to_be_bytes(),
            &keys.to_be_bytes(), &[u8::from(hosted)], &public, &signature.to_bytes()].concat())
    }

    fn canonical_signed_payload(&self) -> Result<Vec<u8>> {
        let attestation = &self.attestation;
        Ok([&self.key_epoch.to_be_bytes()[..], &self.enc.to_bytes(), &attestation.room.to_be_bytes(),
            &attestation.keys.to_be_bytes(), &[u8::from(attestation.hosted)],
            &attestation.signing_public, &attestation.signature].concat())
    }

    pub(crate) fn from_atom(id: &str, payload: &[u8], atom: &Value) -> Result<Self> {
        let member = subject_number(id).map_err(|_| format!("record atom id {id} is not a subject number"))?;
        if payload.len() == 36 || payload.len() == 148 {
            return Err(format!(
                "record {id} is a pre-hybrid {} record ({} bytes, X25519 only): it is refused, not read as a key; the member publishes a {} record ({SIGNED_RECORD_LEN} bytes)",
                if payload.len() == 36 { "DREGG/PRIVATE-ENC-KEY/v1" } else { "DREGG/PRIVATE-ENC-KEY/v2" },
                payload.len(), "DREGG/PRIVATE-ENC-KEY/v3"));
        }
        if payload.len() != SIGNED_RECORD_LEN {
            return Err(format!("record {id} has an invalid encryption-key record length ({} bytes; a v3 record is {SIGNED_RECORD_LEN})", payload.len()));
        }
        let at = 4 + MEMBER_PUBLIC_LEN;
        Ok(Self {
            member,
            key_epoch: u32::from_be_bytes(payload[..4].try_into().expect("4 bytes")),
            enc: MemberPublic::from_bytes(&payload[4..at])?,
            atom: atom.clone(),
            attestation: KeyAttestation {
                room: u64::from_be_bytes(payload[at..at + 8].try_into().expect("8 bytes")),
                keys: u64::from_be_bytes(payload[at + 8..at + 16].try_into().expect("8 bytes")),
                hosted: match payload[at + 16] {
                    0 => false,
                    1 => true,
                    other => return Err(format!("record {id} declares custody {other}; it is 0 (own machine) or 1 (hosted)")),
                },
                signing_public: payload[at + 17..at + 49].try_into().expect("32 bytes"),
                signature: payload[at + 49..at + 113].try_into().expect("64 bytes"),
            },
        })
    }

    fn authenticate(&self, room: &str, keys: &str, current_public: &[u8; 32]) -> Result<SignatureCheckedRecord> {
        let attestation = &self.attestation;
        if attestation.room != subject_number(room)? || attestation.keys != subject_number(keys)?
            || attestation.signing_public != *current_public {
            return Err("recipient record differs from its room, keys cell or pinned member signing key".into());
        }
        VerifyingKey::from_bytes(current_public).map_err(|_| "invalid authenticated signing key")?
            .verify_strict(&record_statement(attestation.room, attestation.keys, self.member,
                self.key_epoch, attestation.hosted, current_public, &self.enc), &Signature::from_bytes(&attestation.signature))
            .map_err(|_| "recipient encryption key signature does not verify under the pinned member key")?;
        Ok(SignatureCheckedRecord(self.clone()))
    }
}

fn subject_number(subject: &str) -> Result<u64> {
    let value: u64 = subject.parse().map_err(|_| format!("subject {subject} is not a 64-bit decimal"))?;
    if value.to_string() != subject {
        return Err(format!("subject {subject} is not canonical"));
    }
    Ok(value)
}

impl WrapAtom {
    pub(crate) fn new(room: &str, member: &str, enc: &MemberPublic, gen: u32, grant: u64, key: &RoomKey) -> Result<Self> {
        if key.epoch() > MAX_EPOCH {
            return Err("room-key epoch exhausted".into());
        }
        Ok(Self {
            epoch: key.epoch(),
            gen,
            member: subject_number(member)?,
            enc_id: enc.id(),
            wrapped: wrap_room_key(room, member, enc, key)?,
            grant,
            attestation: None,
        })
    }

    fn unsigned_payload(&self) -> Vec<u8> {
        [&self.enc_id[..], &self.wrapped.to_bytes(), &self.grant.to_be_bytes()].concat()
    }

    pub(crate) fn payload(&self) -> Vec<u8> {
        let mut payload = self.unsigned_payload();
        if let Some(attestation) = &self.attestation {
            payload.extend(attestation.certificate.bytes());
            payload.extend(attestation.signer.to_be_bytes());
            payload.extend(attestation.signer_epoch.to_be_bytes());
            payload.extend(attestation.signer_public);
            payload.extend(attestation.signature);
        }
        payload
    }

    /// Exact source delivery commitment: cSHAKE with the lineage domain over
    /// one length-prefixed complete signed payload. Neither the encrypted
    /// component alone nor the certificate identity substitutes for this.
    pub(crate) fn payload_commitment(&self) -> Result<[u8; 32]> {
        if self.attestation.is_none() {
            return Err("unsigned wrap has no authorized delivery commitment".into());
        }
        let payload = self.payload();
        if payload.len() != WRAP_PAYLOAD_LEN + 300 {
            return Err("delivery commitment requires the complete signed wrap".into());
        }
        Ok(lineage_digest(&[&payload]))
    }

    fn statement(&self, certificate: &EpochCertificate, signer: u64,
        signer_epoch: u32, signer_public: &[u8; 32]) -> Vec<u8> {
        [AUTH_WRAP_FRAME, &[1], &self.epoch.to_be_bytes(), &self.gen.to_be_bytes(),
            &self.member.to_be_bytes(), &self.unsigned_payload(), &certificate.identity(),
            &signer.to_be_bytes(), &signer_epoch.to_be_bytes(), signer_public].concat()
    }

    fn sign(mut self, certificate: &EpochCertificate, subject: u64,
        signer_epoch: u32, signer: &SigningKey) -> Result<Self> {
        if self.epoch != certificate.epoch { return Err("wrap and epoch certificate disagree".into()); }
        let public = signer.verifying_key().to_bytes();
        let signature = signer.sign(&self.statement(certificate, subject, signer_epoch, &public));
        self.attestation = Some(WrapAttestation { certificate: certificate.clone(),
            signer: subject, signer_epoch, signer_public: public, signature: signature.to_bytes() });
        Ok(self)
    }

    /// Both signatures must verify under the pinned founder key (callers pass it twice).
    fn check_signatures(&self, room: &str, keys: &str,
        epoch_public: &[u8; 32], delivery_public: &[u8; 32]) -> Result<()> {
        let attestation = self.attestation.as_ref().ok_or("unsigned room wrap is not authenticated lineage")?;
        let certificate = &attestation.certificate;
        if certificate.room != subject_number(room)? || certificate.keys != subject_number(keys)?
            || certificate.epoch != self.epoch || attestation.signer_public != *delivery_public {
            return Err("signed wrap differs from room, keys cell, epoch or authorized delivery signer".into());
        }
        certificate.check_signature(epoch_public)?;
        VerifyingKey::from_bytes(delivery_public).map_err(|_| "invalid delivery signing key")?
            .verify_strict(&self.statement(certificate, attestation.signer,
                attestation.signer_epoch, delivery_public), &Signature::from_bytes(&attestation.signature))
            .map_err(|_| "room wrap signature is invalid".into())
    }

    pub(crate) fn from_atom(id: &str, payload: &[u8]) -> Result<Self> {
        let (epoch, gen, member) = parse_wrap_atom_id(id)?;
        if payload.len() != WRAP_PAYLOAD_LEN && payload.len() != WRAP_PAYLOAD_LEN + 300 {
            return Err(format!("wrap atom {id} has an invalid signed-wrap length"));
        }
        Ok(Self {
            epoch,
            gen,
            member,
            enc_id: payload[..32].try_into().expect("32 bytes"),
            wrapped: Wrapped::from_bytes(&payload[32..32 + WRAPPED_LEN])?,
            grant: u64::from_be_bytes(payload[32 + WRAPPED_LEN..WRAP_PAYLOAD_LEN].try_into().expect("8 bytes")),
            attestation: if payload.len() == WRAP_PAYLOAD_LEN + 300 {
                let bytes = &payload[WRAP_PAYLOAD_LEN..];
                Some(WrapAttestation {
                    certificate: EpochCertificate::from_bytes(&bytes[..192])?,
                    signer: u64::from_be_bytes(bytes[192..200].try_into().expect("8 bytes")),
                    signer_epoch: u32::from_be_bytes(bytes[200..204].try_into().expect("4 bytes")),
                    signer_public: bytes[204..236].try_into().expect("32 bytes"),
                    signature: bytes[236..300].try_into().expect("64 bytes"),
                })
            } else { None },
        })
    }

    /// The content action that writes this wrap.
    pub(crate) fn action(&self) -> Value {
        json!({"type":"createAtom","atom":wrap_atom_id(self.epoch, self.gen, self.member),
            "kind":{"type":"inlineObject","schema":wrap_schema()},"payload":hex(&self.payload())})
    }

    pub(crate) fn open(&self, room: &str, secret: &MemberSecret) -> Result<RoomKey> {
        if secret.public().id() != self.enc_id {
            return Err("wrap is addressed to another encryption key".into());
        }
        let key = unwrap_room_key(room, self.epoch, &self.member.to_string(), secret, &self.wrapped)?;
        if let Some(attestation) = &self.attestation {
            let certificate = &attestation.certificate;
            if certificate.room != subject_number(room)? || certificate.epoch != key.epoch()
                || certificate.key_commitment != EpochCertificate::commitment(certificate.room, certificate.keys, &key) {
                return Err("opened key differs from its authenticated epoch commitment".into());
            }
        }
        Ok(key)
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
    let mut pre_hybrid = Vec::new();
    walk(view, &private::schema_decimal_of(AUTH_WRAP_FRAME_V2), &mut pre_hybrid);
    if !pre_hybrid.is_empty() {
        return Err("this keys cell holds a pre-hybrid DREGG/PRIVATE-AUTH-WRAP/v2 wrap (X25519 only): the room predates the v3 hybrid X25519 + ML-KEM-768 format and is refused, not read; found the room again".into());
    }
    walk(view, &wrap_schema(), &mut found);
    let mut wraps = found.into_iter().collect::<Result<Vec<_>>>()?;
    wraps.sort_by_key(|w| (w.epoch, w.member, w.gen));
    wraps.dedup();
    Ok(wraps)
}

/// Every member's encryption-key record in a signed view of a keys cell. The law
/// lets only the member write its own record, so a malformed one is that
/// member's: it is reported and skipped, never trusted.
pub(crate) fn records_in_view(view: &Value) -> BTreeMap<u64, EncRecord> {
    fn walk<'a>(value: &'a Value, schema: &str, out: &mut Vec<&'a Value>) {
        match value {
            Value::Array(items) => items.iter().for_each(|item| walk(item, schema, out)),
            Value::Object(object) => {
                let record = object.get("type").and_then(Value::as_str) == Some("atom")
                    && object.get("kind").and_then(|k| k.get("schema")).and_then(Value::as_str)
                        == Some(schema);
                if record {
                    out.push(value);
                } else {
                    object.values().for_each(|item| walk(item, schema, out));
                }
            }
            _ => {}
        }
    }
    let mut found = Vec::new();
    walk(view, &record_schema(), &mut found);
    // Pre-hybrid records are parsed only to be refused by name; they are never recipient authority.
    walk(view, &private::schema_decimal_of(RECORD_FRAME_V2), &mut found);
    walk(view, &private::schema_decimal_of(RECORD_FRAME_V1), &mut found);
    let mut out = BTreeMap::new();
    for atom in found {
        let parsed = (|| {
            let id = atom.get("id").and_then(Value::as_str).ok_or("record atom lacks id")?;
            let payload = atom.get("payload").and_then(Value::as_str).ok_or("record atom lacks payload")?;
            EncRecord::from_atom(id, &crate::decode_hex(payload)?, atom)
        })();
        match parsed {
            Ok(record) => {
                out.insert(record.member, record);
            }
            Err(error) => eprintln!("keys cell: an encryption-key record is malformed and ignored ({error})"),
        }
    }
    out
}

/// Members at `epoch`, each with its newest wrap there (highest generation).
pub(crate) fn members_at(wraps: &[WrapAtom], epoch: u32) -> BTreeMap<u64, WrapAtom> {
    let mut out: BTreeMap<u64, WrapAtom> = BTreeMap::new();
    for w in wraps.iter().filter(|w| w.epoch == epoch) {
        if out.get(&w.member).is_none_or(|known| w.gen > known.gen) {
            out.insert(w.member, w.clone());
        }
    }
    out
}

/// A member's keys grant: the one its newest wrap carries (0: none).
pub(crate) fn grant_of(wraps: &[WrapAtom], member: u64) -> u64 {
    wraps
        .iter()
        .filter(|w| w.member == member && w.grant != 0)
        .max_by_key(|w| (w.epoch, w.gen))
        .map_or(0, |w| w.grant)
}

/// A recipient a release wraps to: its address generation, its X25519 key and
/// the digest of the signed record that authorized it (zero: the founder's own key).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Recipient {
    gen: u32,
    enc: MemberPublic,
    record: [u8; 32],
}

impl Recipient {
    fn of(authenticated: &AuthenticatedRecord) -> Result<Self> {
        Ok(Self { gen: authenticated.record.key_epoch, enc: authenticated.record.enc.clone(),
            record: record_digest(&authenticated.record)? })
    }
}

/// The wraps a rotation writes: a fresh key at `next` for every member at the
/// head epoch who is still `current` and is not `dropped`, each to its
/// AUTHENTICATED recipient. Returns the new key, the (unsigned) wraps with their
/// recipient digests, and the members left out.
pub(crate) fn rotation(
    room: &str,
    wraps: &[WrapAtom],
    head: u32,
    next: u32,
    recipients: &BTreeMap<u64, Recipient>,
    current: &BTreeSet<u64>,
    dropped: Option<u64>,
) -> Result<(RoomKey, Vec<(WrapAtom, [u8; 32])>, Vec<u64>)> {
    if next <= head { return Err("a rotation's epoch must exceed the head".into()); }
    let key = RoomKey::generate(next)?;
    let mut out = Vec::new();
    let mut left = Vec::new();
    for member in members_at(wraps, head).into_keys() {
        if Some(member) == dropped || !current.contains(&member) {
            left.push(member);
            continue;
        }
        let recipient = recipients.get(&member)
            .ok_or_else(|| format!("member {member} lacks an authenticated recipient record"))?;
        let wrap = WrapAtom::new(room, &member.to_string(), &recipient.enc,
            recipient.gen, grant_of(wraps, member), &key)?;
        out.push((wrap, recipient.record));
    }
    Ok((key, out, left))
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
    crate::workspace::private::keycache_passphrase()
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

/// This workspace's hybrid (X25519 + ML-KEM-768) secret, derived from the seed
/// its signing key file holds.
fn own_secret(workspace: &Value) -> Result<MemberSecret> {
    let path = member_path(workspace, "key")?;
    derive_enc_key(&*seed_of(&path)?)
}

/// Every hybrid secret this workspace opens with: the current one, then every
/// past one its keyring kept across signing-key rotations.
fn own_secrets(workspace: &Value) -> Result<Vec<MemberSecret>> {
    private::enc_secrets(&member_path(workspace, "key")?)
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

/// `mini enc-public --secret KEY`: the full hybrid public key (X25519 ||
/// ML-KEM-768 encapsulation key, 1216 bytes) a sponsor's escrow is sealed to.
pub(crate) fn enc_public_hex(secret: &Path) -> Result<String> {
    Ok(hex(&enc_public(&*seed_of(secret)?)?.to_bytes()))
}

/// `mini enc-key-id --secret KEY`: the 32-byte id of that key, which a room's
/// inviter uses to SELECT an already-published, signed record of it and which a
/// registration or `whoami` shows. A key id authorizes nothing by itself: a
/// first invite needs the member's signed declaration.
pub(crate) fn enc_key_id_hex(secret: &Path) -> Result<String> {
    Ok(hex(&enc_public(&*seed_of(secret)?)?.id()))
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
    pub(crate) keys: String,
    pub(crate) wraps: Vec<WrapAtom>,
    pub(crate) records: BTreeMap<u64, EncRecord>,
    pub(crate) ring: Keyring,
    pub(crate) learned: Vec<u32>,
    lineage: Lineage,
}

impl Synced {
    pub(crate) fn epoch(&self) -> Option<u32> {
        self.lineage.head.as_ref().map(|head| head.epoch)
    }
}

/// The ring may hold no epoch above the authenticated head: such a key came from
/// a later epoch this client already authenticated, so the served view rolled back.
fn check_ring_below_head(ring: &Keyring, room: &str, head: Option<&EpochHead>) -> Result<()> {
    match (ring.latest(room), head) {
        (Some(key), Some(head)) if key.epoch() > head.epoch =>
            Err("served room lineage is older than this client's retained key epochs".into()),
        (Some(_), None) => Err("served keys cell has no epoch but this client holds room keys".into()),
        _ => Ok(()),
    }
}

/// Read the keys cell with this workspace's room grant, verify it under the
/// pinned founder key against the retained head, and store every epoch wrapped
/// for this subject that the cache does not hold (and has not forgotten).
pub(crate) fn sync(root: &Path, workspace: &Value, room_name: &str) -> Result<Synced> {
    let passphrase = passphrase()?;
    let (room_ref, room, keys) = private_room(root, room_name)?;
    let founder = founder_pin(root, &room, &keys)?;
    let (view, _, _) = signed_view(root, workspace, &keys_view_ref(&room_ref, &keys)?, "resource")?;
    let retained = read_epoch_head(root, &room, &keys)?;
    let lineage = verify_lineage(&room, &keys, &founder, &view, retained.as_ref().map(|(_, head)| head))?;
    check_chain_not_rolled_back(retained.as_ref().map(|(value, _)| value), &lineage.chain)?;
    let records = records_in_view(&view);
    let mut ring = load_ring(root, &passphrase)?;
    check_ring_below_head(&ring, &room, lineage.head.as_ref())?;
    // Preserve the authenticated epoch even if the latest wrap cannot open or
    // the client later forgets its decryption keys. Never fall back to an older
    // epoch on either condition.
    if let Some(head) = &lineage.head {
        retain_epoch_head(root, &room, &keys, retained.as_ref().map(|(value, _)| value), head, &lineage.chain,
            &json!({"authority":"founder-pin","founderKeyHex":hex(&founder),"founderTipHex":hex(lineage.chain.tip())}))?;
    }
    let me = subject_number(member(workspace, "subject")?)?;
    let secrets = own_secrets(workspace)?;
    let mut learned = Vec::new();
    let mut unopened = BTreeSet::new();
    // A member may hold several wraps at one epoch (re-wraps after it rotated):
    // the newest generation first, with whichever keyring secret it names.
    let mut mine: Vec<&WrapAtom> = lineage.wraps.iter().filter(|w| w.member == me).collect();
    mine.sort_by_key(|w| (w.epoch, std::cmp::Reverse(w.gen)));
    for wrap in mine {
        if let Some(key) = ring.get(&room, wrap.epoch) {
            let certificate = &wrap.attestation.as_ref().ok_or("cached epoch lacks authenticated certificate")?.certificate;
            if certificate.key_commitment != EpochCertificate::commitment(certificate.room, certificate.keys, &key) {
                return Err("cached room key differs from the authenticated epoch commitment; nothing is sealed".into());
            }
            continue;
        }
        if ring.is_forgotten(&room, wrap.epoch) {
            continue;
        }
        let Some(secret) = secrets.iter().find(|s| s.public().id() == wrap.enc_id) else {
            unopened.insert(wrap.epoch);
            continue;
        };
        match wrap.open(&room, secret) {
            Ok(key) => {
                ring.insert(&room, &key);
                learned.push(wrap.epoch);
                unopened.remove(&wrap.epoch);
            }
            Err(error) => {
                eprintln!("room {room_name}: the wrap for you at epoch {} does not open ({error})", wrap.epoch);
            }
        }
    }
    for epoch in unopened.iter().filter(|e| ring.get(&room, **e).is_none()) {
        eprintln!(
            "room {room_name}: the wrap for you at epoch {epoch} is addressed to an encryption key this client does not hold (not the current one, and not one KEY.enc-ring kept); ask the founder for `room rewrap ID {room_name} {me}` after `room register`"
        );
    }
    if !learned.is_empty() {
        save_ring(root, &passphrase, &ring)?;
        eprintln!("room {room_name}: learned epoch(s) {learned:?} from the keys cell");
    }
    Ok(Synced { room, keys, wraps: lineage.wraps.clone(), records, ring, learned, lineage })
}

/// The key a writer seals under: the room's authenticated head epoch, which this
/// client must hold. A member who was never wrapped at it, or was kicked, refuses here.
pub(crate) fn current_key(root: &Path, workspace: &Value, room_name: &str) -> Result<(String, RoomKey)> {
    let synced = sync(root, workspace, room_name)?;
    let head = synced.lineage.head.as_ref().ok_or("room has no authenticated epoch: nothing is sealed")?;
    let certificate = synced.lineage.certificates.get(&head.epoch)
        .ok_or("authenticated current epoch lacks its certificate")?;
    let key = select_current_key(&synced.ring, &synced.room, head, certificate)?;
    Ok((synced.room, key))
}

fn select_current_key(ring: &Keyring, room: &str, head: &EpochHead, certificate: &EpochCertificate) -> Result<RoomKey> {
    if ring.latest(room).is_some_and(|key| key.epoch() > head.epoch) {
        return Err("authenticated room view is below retained key epochs: nothing is sealed".into());
    }
    let key = ring.get(room, head.epoch).ok_or_else(||
        format!("room is at authenticated epoch {} and this client lacks its key: nothing is sealed", head.epoch))?;
    if certificate.room != subject_number(room)? || certificate.epoch != head.epoch
        || certificate.identity() != head.identity
        || certificate.key_commitment != EpochCertificate::commitment(certificate.room, certificate.keys, &key) {
        return Err("cached sealing key differs from authenticated current epoch: nothing is sealed".into());
    }
    Ok(key)
}


/// The keys this reader may open with: synced when a passphrase is set, none otherwise.
pub(crate) fn reader_keys(root: &Path, workspace: &Value, room_name: &str) -> Result<(String, Option<Keyring>)> {
    if crate::workspace::private::keycache_passphrase().is_none() {
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
    let directory = root.join("proposals").join(proposal_id);
    if !directory.exists() { make_private_dir(&directory)?; }
    let _lock = crate::transport::service_lock(&directory.join("roomkey-turn.lock"))?;
    let source = root.join("sources").join(format!("roomkey-{proposal_id}.json"));
    super::publish_retained_json(&source, request, None)?;
    let intent = directory.join("intent.json");
    let attempt = root.join("attempts").join(proposal_id);
    if directory.join("request.json").exists() {
        if bounded_json(&directory.join("request.json"))? != *request || !intent.exists() {
            return Err("room operation has a different or incomplete retained proposal; recover its original operation".into());
        }
    } else {
        if attempt.exists() || intent.exists() {
            return Err("room operation has incomplete original custody; do not reauthor it".into());
        }
        propose(root, workspace, &source, proposal_id, None)?;
    }
    if attempt.exists() {
        if fs::read(attempt.join("intent.json")).map_err(|error| error.to_string())?
            != fs::read(&intent).map_err(|error| error.to_string())? {
            return Err("room operation attempt differs from its retained original intent".into());
        }
        // Lookup the original call, including UNKNOWN; no fresh nonce/call is
        // substituted for this operation. Closed receipt continuity verifies
        // confirmation before the caller proceeds to the next phase.
        super::recover(root, &attempt)?;
    } else {
        submit_intent(root, workspace, &intent, "intent", false, Some(&attempt))?;
    }
    if super::accepted_outcome(&attempt)?.is_none() {
        return Err("room operation is not source-confirmed; recover its original attempt before proceeding".into());
    }
    Ok(())
}

/// Admit the caller's exact room delegation before key release. A prepared
/// proposal is not audience membership. The ordinary source grant is published
/// only after the protected original-call receipt confirms it.
pub(crate) fn admit_invitation_grant(root: &Path, workspace: &Value,
    proposal_id: &str, request: &Value) -> Result<()> {
    turn(root, workspace, proposal_id, request)?;
    super::publish_delegation(root, proposal_id, &root.join("attempts").join(proposal_id))
}

/// The `content` request that creates `actions` in the keys cell (1..=64).
fn content_request(keys_ref: &str, actions: Vec<Value>) -> Result<Value> {
    if actions.is_empty() || actions.len() > 64 {
        return Err(format!("one keys write carries 1..64 atoms, not {}", actions.len()));
    }
    Ok(json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":[{"name":keys_ref,"payload":{"type":"content","actions":actions}}]}))
}

// ---------------------------------------------------------------- the release state machine
//
// A wrap of an already-used key is a disclosure the moment it leaves this
// client: a refusal at the node does not unsend it. So every release runs
//   DRAFTED   the exact signed deliveries (and a new epoch's key, encrypted apart
//             from the sealing cache) are retained; nothing has left custody;
//   APPLIED   turn 1 created one founder-signed RELEASE record per delivery
//             (commitments only), the node confirmed it, and a fresh signed view
//             read back shows those records byte-exact, every recipient record
//             unchanged, the room's head unchanged and every recipient still a
//             member -- otherwise the release is DEAD;
//   DISCLOSED turn 2 created the wraps those records committed to.
// DEAD is terminal: a dead draft's ciphertexts are never sent and its key never
// enters the sealing cache. Starting a release kills every other undisclosed
// release of the room, and a new epoch is drawn above every epoch any release
// record ever named, so a dead epoch is burned for good.

/// One delivery: the founder-signed wrap and the release record naming it.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Delivery {
    wrap: WrapAtom,
    release: ReleaseStatement,
}

impl Delivery {
    fn new(wrap: WrapAtom, record: [u8; 32], founder: &Founder) -> Result<Self> {
        let release = ReleaseStatement::sign(&wrap, record, &founder.signer)?;
        Ok(Self { wrap, release })
    }
}

struct ReleaseSpec {
    room: String,
    keys: String,
    keys_ref: String,
    purpose: &'static str,
    head_before: Option<EpochHead>,
    /// The key of a NEW epoch (found, rotate); none when re-wrapping held epochs.
    key: Option<RoomKey>,
    deliveries: Vec<Delivery>,
}

#[derive(Debug, PartialEq, Eq)]
enum ReleaseState {
    Drafted,
    Applied,
    Disclosed,
    Dead(String),
}

/// What a release needs from the node; tests substitute a recording fake.
trait ReleaseHost {
    fn turn(&mut self, proposal_id: &str, request: &Value) -> Result<()>;
    fn keys_view(&mut self) -> Result<Value>;
    fn members(&mut self) -> Result<BTreeSet<u64>>;
}

struct LiveHost<'a> {
    root: &'a Path,
    workspace: &'a Value,
    room_ref: Value,
    keys: String,
}

impl ReleaseHost for LiveHost<'_> {
    fn turn(&mut self, proposal_id: &str, request: &Value) -> Result<()> {
        turn(self.root, self.workspace, proposal_id, request)
    }
    fn keys_view(&mut self) -> Result<Value> {
        Ok(signed_view(self.root, self.workspace, &keys_view_ref(&self.room_ref, &self.keys)?, "resource")?.0)
    }
    fn members(&mut self) -> Result<BTreeSet<u64>> {
        who_members(self.root, self.workspace, &self.room_ref)
    }
}

/// The subjects the Host's signed `who` view lists under the room.
fn who_members(root: &Path, workspace: &Value, room_ref: &Value) -> Result<BTreeSet<u64>> {
    let (who, _, _) = signed_view(root, workspace, room_ref, "who")?;
    Ok(who.get("members").and_then(Value::as_array).ok_or("the Host's who view lists no members")?
        .iter()
        .filter_map(|m| m.get("subject").and_then(Value::as_str))
        .filter_map(|s| s.parse().ok())
        .collect())
}

/// The founder's signing key, refused unless it is the room's pinned founder key.
struct Founder {
    signer: SigningKey,
    subject: u64,
    key_epoch: u32,
    /// The key this client pinned: what `verify_lineage` anchors to (not the signer once keys moved).
    pin: [u8; 32],
}

/// Only the tip of the founder-key chain signs: a retired key (rotated away, possibly leaked)
/// and a key not yet handed the room both refuse.
fn require_tip(signer: &[u8; 32], chain: &FounderChain) -> Result<()> {
    if signer != chain.tip() {
        return Err("only the room's current founder key signs epochs, wraps and releases; this workspace's signing key is not the tip of its founder-key chain (`room-key --op transition` hands the room to a new key)".into());
    }
    Ok(())
}

/// Does rotating from `mine` to `next` strand this founder? Only when `mine` is still the
/// tip and `next` is not yet on the chain.
fn rotation_strands(mine: &[u8; 32], next: &[u8; 32], chain: &FounderChain) -> bool {
    chain.tip() == mine && chain.tip() != next
}

/// The founder's signing key, refused unless it is the TIP of the room's founder-key chain.
fn founder_signer(root: &Path, workspace: &Value, room: &str, keys: &str, chain: &FounderChain) -> Result<Founder> {
    let pin = founder_pin(root, room, keys)?;
    let signer = crate::read_secret(&member_path(workspace, "key")?)?;
    require_tip(&signer.verifying_key().to_bytes(), chain)?;
    let key_epoch = crate::key_rotation::current_key_epoch(root)?;
    Ok(Founder { signer, subject: subject_number(member(workspace, "subject")?)?,
        key_epoch: key_epoch.parse().map_err(|_| "signing key epoch must fit 32 bits")?, pin })
}

struct RetainedReleaseDraft {
    directory: PathBuf,
    manifest: Value,
}

const RELEASE_DRAFT_TYPE: &str = "minidregg-retained-room-release-v2";

fn head_json(head: Option<&EpochHead>) -> Value {
    head.map_or(Value::Null, |head| json!({"epoch":head.epoch.to_string(),"identity":hex(&head.identity)}))
}

impl RetainedReleaseDraft {
    fn operation(room: &str, proposal_id: &str) -> [u8; 32] {
        lineage_digest(&[b"DREGG/PRIVATE-ROOM-RELEASE-OPERATION/v1", room.as_bytes(), proposal_id.as_bytes()])
    }

    fn parent(root: &Path) -> PathBuf {
        root.join("private").join("room-releases")
    }

    fn directory(root: &Path, operation: &[u8; 32]) -> PathBuf {
        Self::parent(root).join(hex(operation))
    }

    fn load(root: &Path, operation: &[u8; 32]) -> Result<Option<Self>> {
        let directory = Self::directory(root, operation);
        if !directory.exists() { return Ok(None); }
        super::private_dir(&directory)?;
        let manifest_path = directory.join("draft.json");
        if !manifest_path.exists() {
            return Err("room release draft is incomplete; it is never disclosed (start a new operation)".into());
        }
        let manifest = bounded_json(&manifest_path)?;
        if member(&manifest, "type")? != RELEASE_DRAFT_TYPE || member(&manifest, "operationHex")? != hex(operation) {
            return Err("retained room release operation differs".into());
        }
        if !manifest["keyEpoch"].is_null() {
            let encrypted = fs::read(directory.join("draft-key.cache")).map_err(|error| error.to_string())?;
            if hex(&lineage_digest(&[b"DREGG/PRIVATE-ROOM-DRAFT-CACHE/v1", &encrypted]))
                != member(&manifest, "encryptedKeyCommitmentHex")? {
                return Err("retained release encrypted key differs; nothing is disclosed".into());
            }
        }
        Ok(Some(Self { directory, manifest }))
    }

    fn stage(root: &Path, operation: &[u8; 32], proposal_id: &str, spec: &ReleaseSpec,
        passphrase: &[u8]) -> Result<Self> {
        if spec.deliveries.is_empty() || spec.deliveries.len() > 64 {
            return Err("a release carries 1..64 deliveries".into());
        }
        let mut addresses = BTreeSet::new();
        for delivery in &spec.deliveries {
            let wrap = &delivery.wrap;
            let certificate = &wrap.attestation.as_ref().ok_or("release draft requires signed deliveries")?.certificate;
            delivery.release.names(wrap)?;
            if certificate.room.to_string() != spec.room || certificate.keys.to_string() != spec.keys
                || !addresses.insert(wrap_atom_id(wrap.epoch, wrap.gen, wrap.member)) {
                return Err("retained deliveries differ from their room or repeat an address".into());
            }
            if let Some(key) = &spec.key {
                if wrap.epoch != key.epoch()
                    || certificate.key_commitment != EpochCertificate::commitment(certificate.room, certificate.keys, key) {
                    return Err("a new epoch's deliveries must all carry its key".into());
                }
            }
        }
        let private = root.join("private");
        if !private.exists() { make_private_dir(&private)?; }
        let parent = Self::parent(root);
        if !parent.exists() { make_private_dir(&parent)?; }
        let _lock = crate::transport::service_lock(&parent.join(format!("{}.lock", hex(operation))))?;
        if Self::load(root, operation)?.is_some() {
            return Err("room release operation already exists; it is resumed, never re-drafted".into());
        }
        let directory = Self::directory(root, operation);
        make_private_dir(&directory)?;
        let mut manifest = json!({"type":RELEASE_DRAFT_TYPE,"operationHex":hex(operation),
            "proposal":proposal_id,"room":spec.room,"keysCell":spec.keys,"keysRef":spec.keys_ref,
            "purpose":spec.purpose,"headBefore":head_json(spec.head_before.as_ref()),
            "keyEpoch":spec.key.as_ref().map(|key| key.epoch().to_string()),
            "deliveries":spec.deliveries.iter().map(|d| json!({
                "wrapAtom":wrap_atom_id(d.wrap.epoch, d.wrap.gen, d.wrap.member),
                "wrapPayloadHex":hex(&d.wrap.payload()),
                "releaseAtom":d.release.atom(),"releasePayloadHex":hex(&d.release.payload())})).collect::<Vec<_>>()});
        if let Some(key) = &spec.key {
            let mut draft_ring = Keyring::default();
            draft_ring.insert(&spec.room, key);
            private::save_cache(&directory.join("draft-key.cache"), passphrase, &draft_ring)?;
            fs::File::open(&directory).and_then(|file| file.sync_all()).map_err(|error| error.to_string())?;
            let encrypted = fs::read(directory.join("draft-key.cache")).map_err(|error| error.to_string())?;
            manifest["encryptedKeyCommitmentHex"] = json!(hex(&lineage_digest(&[b"DREGG/PRIVATE-ROOM-DRAFT-CACHE/v1", &encrypted])));
        }
        super::publish_retained_json(&directory.join("draft.json"), &manifest, None)?;
        Self::load(root, operation)?.ok_or_else(|| "retained room release draft disappeared".into())
    }

    fn room(&self) -> Result<&str> { member(&self.manifest, "room") }

    fn state(&self) -> Result<ReleaseState> {
        let dead = self.directory.join("dead.json");
        if dead.exists() {
            return Ok(ReleaseState::Dead(member(&bounded_json(&dead)?, "reason")?.to_owned()));
        }
        if self.directory.join("disclosed.json").exists() { return Ok(ReleaseState::Disclosed); }
        if self.directory.join("applied.json").exists() { return Ok(ReleaseState::Applied); }
        Ok(ReleaseState::Drafted)
    }

    fn mark(&self, name: &str, row: &Value) -> Result<()> {
        let mut row = row.clone();
        row["operationHex"] = self.manifest["operationHex"].clone();
        super::publish_retained_json(&self.directory.join(name), &row, None)
    }

    /// Terminal. A disclosed release cannot die; a dead one stays dead.
    fn kill(&self, reason: &str) -> Result<()> {
        match self.state()? {
            ReleaseState::Dead(_) => Ok(()),
            ReleaseState::Disclosed => Err("a disclosed release cannot be killed".into()),
            _ => self.mark("dead.json", &json!({"type":"minidregg-dead-room-release-v1","reason":reason})),
        }
    }

    fn key(&self, passphrase: &[u8]) -> Result<Option<RoomKey>> {
        if self.manifest["keyEpoch"].is_null() { return Ok(None); }
        let epoch: u32 = member(&self.manifest, "keyEpoch")?.parse().map_err(|_| "invalid draft key epoch")?;
        let room = self.room()?;
        let ring = private::load_cache(&self.directory.join("draft-key.cache"), passphrase)?;
        if ring.epochs(room) != vec![epoch] {
            return Err("retained release cache must contain exactly its committed epoch".into());
        }
        let key = ring.get(room, epoch).ok_or("retained release key absent")?;
        for delivery in self.deliveries()? {
            let certificate = &delivery.wrap.attestation.as_ref().ok_or("unsigned delivery")?.certificate;
            if certificate.key_commitment != EpochCertificate::commitment(certificate.room, certificate.keys, &key) {
                return Err("retained draft key differs from the signed epoch commitment".into());
            }
        }
        Ok(Some(key))
    }

    fn deliveries(&self) -> Result<Vec<Delivery>> {
        self.manifest["deliveries"].as_array().ok_or("release draft lacks deliveries")?.iter().map(|row| {
            let wrap = WrapAtom::from_atom(member(row, "wrapAtom")?, &crate::decode_hex(member(row, "wrapPayloadHex")?)?)?;
            let release = ReleaseStatement::from_atom(member(row, "releaseAtom")?,
                &crate::decode_hex(member(row, "releasePayloadHex")?)?)?;
            release.names(&wrap)?;
            Ok(Delivery { wrap, release })
        }).collect()
    }

    fn head_before(&self) -> Result<Option<EpochHead>> {
        let head = &self.manifest["headBefore"];
        if head.is_null() { return Ok(None); }
        Ok(Some(EpochHead { epoch: member(head, "epoch")?.parse().map_err(|_| "invalid draft head epoch")?,
            identity: crate::decode_hex(member(head, "identity")?)?.try_into()
                .map_err(|_| "draft head identity must be 32 bytes")? }))
    }
}

/// Every retained release of `room`.
fn drafts_of_room(root: &Path, room: &str) -> Result<Vec<RetainedReleaseDraft>> {
    let parent = RetainedReleaseDraft::parent(root);
    if !parent.exists() { return Ok(Vec::new()); }
    let mut out = Vec::new();
    for entry in fs::read_dir(&parent).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        if !entry.file_type().map_err(|error| error.to_string())?.is_dir() { continue; }
        let Ok(operation) = crate::decode_hex(&entry.file_name().to_string_lossy())
            .and_then(|bytes| <[u8; 32]>::try_from(bytes).map_err(|_| "not an operation".to_string())) else { continue };
        if let Some(draft) = RetainedReleaseDraft::load(root, &operation)? {
            if draft.room()? == room { out.push(draft); }
        }
    }
    Ok(out)
}

/// The proposal of this room's live (undisclosed, not dead) release of `purpose`.
fn live_release(root: &Path, room: &str, purpose: &str) -> Result<Option<String>> {
    for draft in drafts_of_room(root, room)? {
        if matches!(draft.state()?, ReleaseState::Drafted | ReleaseState::Applied)
            && draft.manifest["purpose"] == purpose {
            return Ok(Some(member(&draft.manifest, "proposal")?.to_owned()));
        }
    }
    Ok(None)
}

/// The APPLIED check: run on a fresh signed view after turn 1 was confirmed.
fn check_readback(draft: &RetainedReleaseDraft, deliveries: &[Delivery], founder: &[u8; 32],
    me: u64, view: &Value, members: &BTreeSet<u64>) -> Result<()> {
    let room = draft.room()?;
    let keys = member(&draft.manifest, "keysCell")?;
    let lineage = verify_lineage(room, keys, founder, view, None)?;
    if lineage.head != draft.head_before()? {
        return Err("the room's epoch moved after this release was drafted".into());
    }
    let records = records_in_view(view);
    for delivery in deliveries {
        let release = &delivery.release;
        if lineage.releases.get(&release.atom()) != Some(release) {
            return Err(format!("the readback lacks this release's exact record for member {}", release.member));
        }
        if lineage.wraps.iter().any(|w| (w.epoch, w.gen, w.member) == (release.epoch, release.gen, release.member)) {
            return Err("a wrap already exists at this delivery's address".into());
        }
        if release.member == me { continue; }
        if let Some(record) = records.get(&release.member) {
            if record_digest(record)? != release.record {
                return Err(format!("member {} published a different recipient record after this release was drafted: the bound key is stale", release.member));
            }
        }
        if !members.contains(&release.member) {
            return Err(format!("member {} no longer holds a grant under the room", release.member));
        }
    }
    Ok(())
}

struct Released {
    key: Option<RoomKey>,
    wraps: Vec<WrapAtom>,
}

/// Run (or resume) release `proposal_id` of `room` through the state machine.
/// `build` drafts it and is called only when no release of that id exists.
fn run_release(root: &Path, host: &mut dyn ReleaseHost, founder: &[u8; 32], me: u64,
    room: &str, proposal_id: &str, passphrase: &[u8],
    build: impl FnOnce() -> Result<ReleaseSpec>) -> Result<Released> {
    validate_name(proposal_id)?;
    let operation = RetainedReleaseDraft::operation(room, proposal_id);
    let draft = match RetainedReleaseDraft::load(root, &operation)? {
        Some(draft) => draft,
        None => {
            let spec = build()?;
            if spec.room != room { return Err("release spec names another room".into()); }
            // One live release per room: older undisclosed ones die BEFORE the
            // new one exists, so two releases can never both reach disclosure.
            for other in drafts_of_room(root, room)? {
                if matches!(other.state()?, ReleaseState::Drafted | ReleaseState::Applied) {
                    other.kill(&format!("superseded by release {proposal_id}"))?;
                }
            }
            RetainedReleaseDraft::stage(root, &operation, proposal_id, &spec, passphrase)?
        }
    };
    let deliveries = draft.deliveries()?;
    let keys_ref = member(&draft.manifest, "keysRef")?.to_owned();
    let released = |draft: &RetainedReleaseDraft| -> Result<Released> {
        Ok(Released { key: draft.key(passphrase)?, wraps: deliveries.iter().map(|d| d.wrap.clone()).collect() })
    };
    match draft.state()? {
        ReleaseState::Dead(why) => return Err(format!(
            "release {proposal_id} is dead and is never disclosed ({why}); start a new operation")),
        ReleaseState::Disclosed => return released(&draft),
        ReleaseState::Applied => {}
        ReleaseState::Drafted => {
            host.turn(&format!("{proposal_id}-bind"),
                &content_request(&keys_ref, deliveries.iter().map(|d| d.release.action()).collect())?)?;
            let view = host.keys_view()?;
            let members = host.members()?;
            if let Err(why) = check_readback(&draft, &deliveries, founder, me, &view, &members) {
                draft.kill(&why)?;
                return Err(format!("release {proposal_id}: its records were bound but the readback refused; nothing was disclosed and this release is dead forever: {why}"));
            }
            draft.mark("applied.json", &json!({"type":"minidregg-applied-room-release-v1",
                "releases":deliveries.iter().map(|d| d.release.atom()).collect::<Vec<_>>()}))?;
        }
    }
    // A concurrent release may have killed this one after its readback.
    if let ReleaseState::Dead(why) = draft.state()? {
        return Err(format!("release {proposal_id} died before disclosure ({why})"));
    }
    host.turn(&format!("{proposal_id}-wraps"),
        &content_request(&keys_ref, deliveries.iter().map(|d| d.wrap.action()).collect())?)?;
    draft.mark("disclosed.json", &json!({"type":"minidregg-disclosed-room-release-v1"}))?;
    released(&draft)
}

/// Install a disclosed release's new epoch key in the sealing cache.
fn install_released_key(root: &Path, passphrase: &[u8], room: &str, key: Option<&RoomKey>) -> Result<()> {
    let Some(key) = key else { return Ok(()) };
    let mut ring = load_ring(root, passphrase)?;
    if ring.get(room, key.epoch()).is_none() {
        ring.insert(room, key);
        save_ring(root, passphrase, &ring)?;
    }
    Ok(())
}

/// Resume an existing release of this id, if there is one.
fn resume_release(root: &Path, workspace: &Value, room_name: &str, proposal_id: &str,
    passphrase: &[u8]) -> Result<Option<Released>> {
    let (room_ref, room, keys) = private_room(root, room_name)?;
    validate_name(proposal_id)?;
    if RetainedReleaseDraft::load(root, &RetainedReleaseDraft::operation(&room, proposal_id))?.is_none() {
        return Ok(None);
    }
    let founder = founder_pin(root, &room, &keys)?;
    let me = subject_number(member(workspace, "subject")?)?;
    let mut host = LiveHost { root, workspace, room_ref, keys };
    let released = run_release(root, &mut host, &founder, me, &room, proposal_id, passphrase,
        || Err("unreachable: the release exists".into()))?;
    install_released_key(root, passphrase, &room, released.key.as_ref())?;
    Ok(Some(released))
}

/// The founder delegates `observe, mutate` on the keys cell alone to `invitee`
/// (submitted): the grant the keys law confines to the invitee's own record.
/// Returns its capability id.
fn keys_grant(root: &Path, workspace: &Value, keys_ref: &str, invitee: &str, proposal_id: &str) -> Result<u64> {
    turn(root, workspace, proposal_id, &json!({"type":"minidregg-workspace-proposal-v1","action":"delegate",
        "name":keys_ref,"recipient":invitee,"verbs":["observe","mutate"],"maxCost":"50000"}))?;
    let summary = bounded_json(&root.join("proposals").join(proposal_id).join("proposal.json"))?;
    let id = summary
        .get("delegation")
        .and_then(|d| d.get("childCapability"))
        .and_then(Value::as_str)
        .ok_or("the keys-grant delegation names no child capability")?;
    id.parse().map_err(|_| format!("keys grant {id} is not a 64-bit capability id"))
}

/// The keys cell reference this workspace writes through: the founder's own
/// (born with the room), or, for a member, one made from the keys grant its
/// wraps carry (`member_grant`), confined by the keys law to its own record.
fn writable_keys_ref(root: &Path, room_name: &str, room_ref: &Value, keys: &str) -> Result<String> {
    writable_keys_ref_with(root, room_name, room_ref, keys, None)
}

fn writable_keys_ref_with(
    root: &Path,
    room_name: &str,
    room_ref: &Value,
    keys: &str,
    member_grant: Option<u64>,
) -> Result<String> {
    let name = keys_name(room_name)?;
    if let Some(grant) = member_grant {
        let current = reference(root, &name).ok();
        let wanted = grant.to_string();
        if current.as_ref().and_then(|r| r.get("operationCapability")).and_then(Value::as_str)
            != Some(wanted.as_str())
            && current.as_ref().and_then(|r| r.get("controlCapability")).is_none_or(Value::is_null)
        {
            rewrite_reference(root, &name, &json!({"type":"minidregg-participant-reference-v1","name":name,
                "kind":"object","target":keys,"observeCapability":member(room_ref,"observeCapability")?,
                "operationCapability":wanted,"controlCapability":null,"provenance":null,
                "authority":"hint-only"}))?;
        }
        return Ok(name);
    }
    if !root.join("refs").join(format!("{name}.json")).exists() {
        let capability = member(room_ref, "operationCapability")?;
        rewrite_reference(root, &name, &json!({"type":"minidregg-participant-reference-v1","name":name,
            "kind":"object","target":keys,"observeCapability":member(room_ref,"observeCapability")?,
            "operationCapability":capability,"controlCapability":null,"provenance":null,
            "authority":"hint-only"}))?;
    }
    Ok(name)
}

/// `room new NAME --private`, after the room cell is born: birth the keys cell in
/// the room under the keys law, mark the room reference private, pin this
/// founder's own key, and release the genesis epoch to the founder itself
/// (records, then wrap). Re-running resumes the live genesis release.
pub(crate) fn found(root: &Path, workspace: &Value, room_name: &str) -> Result<()> {
    let passphrase = passphrase()?;
    let mut room_ref = reference(root, room_name)?;
    let room = member(&room_ref, "target")?.to_owned();
    let founder_subject = member(workspace, "subject")?.to_owned();
    let keys_ref = keys_name(room_name)?;
    if !root.join("refs").join(format!("{keys_ref}.json")).exists() {
        let law = root.join("sources").join(format!("roomkey-law-{keys_ref}.json"));
        if !law.exists() {
            super::private_file(&law, &serde_json::to_vec(&keys_law(&founder_subject)).map_err(|e| e.to_string())?)?;
        }
        super::create(root, workspace, &keys_ref, "content", &law, Some(room_name), "object", None, None, None)?;
    }
    let keys = member(&reference(root, &keys_ref)?, "target")?.to_owned();
    if room_ref.get("private").and_then(|p| p.get("keys")).and_then(Value::as_str) != Some(keys.as_str()) {
        room_ref["private"] = json!({"keys": keys});
        rewrite_reference(root, room_name, &room_ref)?;
    }
    let public = crate::read_secret(&member_path(workspace, "key")?)?.verifying_key().to_bytes();
    let me = subject_number(&founder_subject)?;
    pin_founder(root, &room, &keys, &hex(&public), false)?;
    pin_member(root, &room, &keys, me, &public, false)?;
    let synced = sync(root, workspace, room_name)?;
    if let Some(epoch) = synced.epoch() {
        if synced.ring.get(&room, epoch).is_none() {
            return Err(format!("{room_name} already has epoch {epoch} and this client does not hold it"));
        }
    } else {
        let founder = founder_signer(root, workspace, &room, &keys, &synced.lineage.chain)?;
        let enc = own_secret(workspace)?.public().clone();
        let proposal = match live_release(root, &room, "found")? {
            Some(proposal) => proposal,
            None => {
                let nonce = super::random_nonce()?;
                format!("rk-found-{}", &nonce[nonce.len().saturating_sub(16)..])
            }
        };
        let lineage = &synced.lineage;
        let mut host = LiveHost { root, workspace, room_ref: room_ref.clone(), keys: keys.clone() };
        let released = run_release(root, &mut host, &founder.pin, me, &room, &proposal, &passphrase, || {
            let key = RoomKey::generate(lineage.next_epoch()?)?;
            let certificate = EpochCertificate::sign(&room, &keys, &key, [0; 32], me, founder.key_epoch, &founder.signer)?;
            let wrap = WrapAtom::new(&room, &founder_subject, &enc, 0, 0, &key)?
                .sign(&certificate, me, founder.key_epoch, &founder.signer)?;
            Ok(ReleaseSpec { room: room.clone(), keys: keys.clone(), keys_ref: keys_ref.clone(),
                purpose: "found", head_before: None, key: Some(key),
                deliveries: vec![Delivery::new(wrap, [0; 32], &founder)?] })
        })?;
        install_released_key(root, &passphrase, &room, released.key.as_ref())?;
    }
    let ring = load_ring(root, &passphrase)?;
    println!("{}", serde_json::to_string_pretty(&json!({"type":"minidregg-private-room-v1",
        "room":room_name,"target":room,"keys":keys,"epochs":ring.epochs(&room),
        "founderKeyHex":hex(&public),"founderFingerprint":fingerprint(&public),
        "disclaimer":private::PRIVACY_DISCLAIMER,
        "note":"devnet quality; privacy not audited. Give each member the room id, keys cell and founder key DIRECTLY (not through this node) so they can pin it: room-key --op recipient-record --room-id ROOM --keys-cell KEYS --founder-key HEX"}))
        .map_err(|e| e.to_string())?);
    Ok(())
}

/// `room-key --op transition --next-key FILE`: hand the room to the founder's NEXT signing
/// key BEFORE `rotate-key` makes it the daily key. The old key still signs here (it is still
/// the Host-valid signer of this write); the next key signs too, proving it is held. Ordering
/// is the two-phase rule of releases: the record is BOUND to the keys cell and read back
/// verified first, and only then may the Host rotation happen (`founder_rotation_gate`
/// refuses `rotate-key` until it has). Nothing secret is disclosed by a transition, so there
/// is no draft/dead-draft machinery: the write is idempotent under its proposal id.
pub(crate) fn transition(root: &Path, workspace: &Value, room_name: &str, next_key: &Path,
    proposal_id: &str) -> Result<()> {
    let (room_ref, room, keys) = private_room(root, room_name)?;
    let synced = sync(root, workspace, room_name)?;
    let head = synced.lineage.head.clone().ok_or("room has no authenticated epoch yet: nothing to hand over")?;
    let chain = &synced.lineage.chain;
    let next = crate::read_secret(next_key)?;
    let next_public = next.verifying_key().to_bytes();
    if *chain.tip() == next_public {
        println!("{}", serde_json::to_string_pretty(&json!({"type":"minidregg-room-founder-transition-v1",
            "room":room_name,"transition":"already published","founderKeyHex":hex(&next_public),
            "fingerprint":fingerprint(&next_public)})).map_err(|e| e.to_string())?);
        return Ok(());
    }
    let founder = founder_signer(root, workspace, &room, &keys, chain)?;
    let index = u32::try_from(chain.transitions()).map_err(|_| "founder-key transitions exhausted")?;
    let record = FounderTransition::sign(&room, &keys, index, &head, &founder.signer, &next)?;
    let keys_ref = writable_keys_ref(root, room_name, &room_ref, &keys)?;
    turn(root, workspace, proposal_id, &content_request(&keys_ref, vec![record.action()])?)?;
    let (view, _, _) = signed_view(root, workspace, &keys_view_ref(&room_ref, &keys)?, "resource")?;
    let lineage = verify_lineage(&room, &keys, &founder.pin, &view, Some(&head))?;
    if *lineage.chain.tip() != next_public || lineage.chain.transitions() != chain.transitions() + 1 {
        return Err("the founder-key transition was submitted but the readback does not show it as the tip of the chain; do not rotate the key".into());
    }
    eprintln!("room {room_name}: founder key handed from {} to {} (fingerprint {}). Members' clients accept it by itself: both keys signed. Now run `rotate-key`; until then this key still signs.",
        fingerprint(&founder.signer.verifying_key().to_bytes()), hex(&next_public), fingerprint(&next_public));
    println!("{}", serde_json::to_string_pretty(&json!({"type":"minidregg-room-founder-transition-v1",
        "room":room_name,"transition":"published","index":index,"afterEpoch":head.epoch,
        "oldKeyHex":hex(&founder.signer.verifying_key().to_bytes()),"founderKeyHex":hex(&next_public),
        "fingerprint":fingerprint(&next_public)})).map_err(|e| e.to_string())?);
    Ok(())
}

/// The gate `rotate-key` runs BEFORE it advances the Host: for every private room whose
/// founder key this workspace holds now (the pin, or the tip it last authenticated), the
/// next key must already be the tip of the room's published founder-key chain. Without
/// this a founder that rotated would hold a signing key no member pins, and could neither
/// invite nor rotate nor kick in its own room. Fails closed: a room it cannot read refuses.
pub(crate) fn founder_rotation_gate(root: &Path, next_public: &[u8; 32]) -> Result<()> {
    let workspace = super::load(root)?;
    let mine = crate::read_secret(&member_path(&workspace, "key")?)?.verifying_key().to_bytes();
    let mut owed = Vec::new();
    for name in private_room_names(root) {
        let (room_ref, room, keys) = private_room(root, &name)?;
        let retained = read_epoch_head(root, &room, &keys)?;
        let pin = match founder_pin(root, &room, &keys) { Ok(pin) => pin, Err(_) => continue };
        let was_mine = pin == mine || retained_founder_tip(retained.as_ref().map(|(value, _)| value)) == Some(mine);
        if !was_mine { continue; }
        let (view, _, _) = signed_view(root, &workspace, &keys_view_ref(&room_ref, &keys)?, "resource")
            .map_err(|error| format!("room {name}: cannot read the keys cell to check the founder-key chain ({error}); rotate-key refuses rather than strand the room"))?;
        let lineage = verify_lineage(&room, &keys, &pin, &view, retained.as_ref().map(|(_, head)| head))?;
        if rotation_strands(&mine, next_public, &lineage.chain) {
            owed.push(name);
        }
    }
    if owed.is_empty() { return Ok(()); }
    Err(format!("this workspace is the founder of private room(s) {} and the key you are rotating to is not yet on their founder-key chain: run `room-key --op transition --name ROOM --next-key NEXT-KEY` for each first, or no member (and not you) could verify what the new key signs",
        owed.join(", ")))
}

/// The private rooms this workspace references (sorted).
fn private_room_names(root: &Path) -> Vec<String> {
    let mut rooms: Vec<String> = fs::read_dir(root.join("refs"))
        .map(|entries| entries.flatten()
            .filter_map(|entry| entry.file_name().into_string().ok())
            .filter_map(|name| name.strip_suffix(".json").map(str::to_owned))
            .filter(|name| !name.starts_with('.'))
            .filter(|name| reference(root, name).is_ok_and(|r| r.get("private").and_then(|p| p.get("keys")).is_some()))
            .collect())
        .unwrap_or_default();
    rooms.sort();
    rooms
}

/// B6, before anything is proposed: a hosted invitee needs `--i-know`. Two
/// independent signals say an invitee is hosted, and EITHER refuses: the
/// operator's list of hosted subjects, and (once its signed record is in hand,
/// `check_declared_custody`) the invitee's own signed declaration that its
/// signing key is a file on a shared box.
pub(crate) fn check_invitee(invitee: &str, i_know: bool) -> Result<()> {
    subject_number(invitee)?;
    let (list, hosted) = hosted_subjects()?;
    hosted_private_invite(true, hosted.contains(invitee), i_know)
        .map_err(|why| format!("{why} ({invitee} is listed in {})", list.display()))
}

/// THE one spelling of a private-room invite. The shell's `room invite` and
/// `chat invite` (and `summon`, which invites through chat) all run the
/// `room-key` operation with exactly these flags, so the hosted-subject rule
/// (`check_invitee`, `check_declared_custody`) and the release state machine
/// guard every path. `op` is `invite`, or `invite-check`: the same checks with
/// nothing written, which a caller that grants first runs BEFORE granting.
pub(crate) fn invite_flags(op: &str, dir: &Path, room: &str, member: &str, enc: &str,
    proposal_id: &str, request: Option<&Path>, past: bool, i_know: bool)
    -> Vec<(String, std::ffi::OsString)> {
    let mut flags: Vec<(String, std::ffi::OsString)> = vec![
        ("action".into(), "room-key".into()), ("op".into(), op.into()), ("dir".into(), dir.into()),
        ("name".into(), room.into()), ("member".into(), member.into()), ("enc-pub".into(), enc.into()),
        ("proposal-id".into(), proposal_id.into())];
    if let Some(request) = request { flags.push(("request".into(), request.into())); }
    if past { flags.push(("past".into(), "true".into())); }
    if i_know { flags.push(("i-know".into(), "true".into())); }
    flags
}

/// The same rule, from the invitee's own SIGNED custody declaration. A member
/// that lies about its custody lies in a record that carries its signature; one
/// that tells the truth cannot be wrapped for by accident.
fn check_declared_custody(record: &EncRecord, i_know: bool) -> Result<()> {
    hosted_private_invite(true, record.attestation.hosted, i_know).map_err(|why| format!(
        "{why} (member {} declared this itself: its signed key record says its signing key is a file on a shared box)", record.member))
}

/// A member may sign its first room encryption declaration before it has a
/// keys-cell grant or any wrap. This offline signature is a declaration only:
/// the inviter and the source release controller still authenticate its exact
/// identity/key epoch, current room entitlement and release permission.
pub(crate) fn signed_recipient_descriptor(workspace: &Value, room: &str, keys: &str,
    key_epoch: &str) -> Result<Value> {
    let epoch: u32 = key_epoch.parse().map_err(|_| "recipient key epoch must fit32bits")?;
    if epoch.to_string() != key_epoch { return Err("recipient key epoch must be canonical decimal".into()); }
    let subject = member(workspace, "subject")?;
    let signer = crate::read_secret(&member_path(workspace, "key")?)?;
    let encryption = enc_public(&*seed_of(&member_path(workspace, "key")?)?)?;
    let hosted = private::key_is_hosted(&member_path(workspace, "key")?);
    let payload = EncRecord::signed_payload(room, keys, subject_number(subject)?, epoch, hosted,
        &encryption, &signer)?;
    Ok(json!({"type":"minidregg-signed-room-recipient-v3","member":subject,
        "room":room,"keysCell":keys,"keyEpoch":key_epoch,"recordHex":hex(&payload),
        "authority":"the founder pins this signing key: hand it to the founder directly, not through the node"}))
}

/// Shared shell/chat transport parsing. This function never authenticates a
/// recipient: its callers authenticate the signed record it yields against the
/// room and the pinned signing key (`pin_member_declaration`, `invitation_record`).
pub(crate) fn recipient_argument(text: &str) -> Result<String> {
    let text = text.trim();
    if text.len() > 8192 { return Err("recipient declaration exceeds its transport bound".into()); }
    let declaration = if text.starts_with('{') {
        let value: Value = serde_json::from_str(text).map_err(|error| error.to_string())?;
        if member(&value, "type")? != "minidregg-signed-room-recipient-v3" {
            return Err("unknown signed room recipient declaration (only minidregg-signed-room-recipient-v3, the hybrid X25519 + ML-KEM-768 declaration, is read)".into());
        }
        let record_hex = member(&value, "recordHex")?;
        let bytes = crate::decode_hex(record_hex)?;
        let record = EncRecord::from_atom(member(&value, "member")?, &bytes, &Value::Null)?;
        let attestation = &record.attestation;
        if attestation.room.to_string() != member(&value, "room")?
            || attestation.keys.to_string() != member(&value, "keysCell")?
            || record.key_epoch.to_string() != member(&value, "keyEpoch")? {
            return Err("recipient declaration metadata differs from its signed record".into());
        }
        record_hex.to_owned()
    } else { text.to_owned() };
    let bytes = crate::decode_hex(&declaration)?;
    if bytes.len() != 32 && bytes.len() != SIGNED_RECORD_LEN {
        return Err(format!("a recipient declaration is a signed v3 record ({SIGNED_RECORD_LEN} bytes) or the 32-byte key id of an existing signed record, not {} bytes", bytes.len()));
    }
    Ok(hex(&bytes))
}

fn invitation_record(invitee: u64, declaration_hex: &str, stored: Option<&EncRecord>) -> Result<EncRecord> {
    let bytes = crate::decode_hex(&recipient_argument(declaration_hex)?)?;
    match bytes.len() {
        SIGNED_RECORD_LEN => {
            let record = EncRecord::from_atom(&invitee.to_string(), &bytes, &Value::Null)?;
            if let Some(stored) = stored {
                if stored.canonical_signed_payload()? != record.canonical_signed_payload()? {
                    return Err("supplied signed recipient declaration differs from the stored current record".into());
                }
            }
            Ok(record)
        }
        32 => {
            let stored = stored.ok_or_else(|| format!("first invite requires the member's full signed v3 recipient declaration ({SIGNED_RECORD_LEN} bytes); a bare key id cannot authorize disclosure"))?;
            if bytes != stored.enc.id() { return Err("named encryption key id differs from the recipient record".into()); }
            Ok(stored.clone())
        }
        _ => Err(format!("invite encryption declaration must be a signed v3 record ({SIGNED_RECORD_LEN} bytes), or the 32-byte key id of an existing signed record")),
    }
}

/// Check the signed declaration and the authenticated head before an
/// invitation creates a room grant. The invitee's signing key must be unpinned
/// or pinned to the same key; the release rechecks everything on readback.
pub(crate) fn invite_preflight(root: &Path, workspace: &Value, room_name: &str,
    invitee: &str, declaration_hex: &str, i_know: bool) -> Result<()> {
    check_invitee(invitee, i_know)?;
    let (_, room, keys) = private_room(root, room_name)?;
    let synced = sync(root, workspace, room_name)?;
    let epoch = synced.epoch().ok_or("private room has no authenticated epoch yet")?;
    if synced.ring.get(&room, epoch).is_none() {
        return Err("inviter does not hold the authenticated current room key".into());
    }
    founder_pin(root, &room, &keys)?;
    let number = subject_number(invitee)?;
    let record = invitation_record(number, declaration_hex, synced.records.get(&number))?;
    let signing = record.attestation.signing_public;
    record.authenticate(&room, &keys, &signing)?;
    check_declared_custody(&record, i_know)?;
    let (_, pins) = member_pins(root, &room, &keys)?;
    if pins.get(&number).is_some_and(|pinned| *pinned != signing) {
        return Err(format!("{invitee} declared a signing key different from its pin: accept it only from the member directly (room-key --op pin-member --replace true)"));
    }
    Ok(())
}

/// The invitee half of `room invite` for a private room: release the current
/// epoch (and, with `past`, every earlier epoch this inviter holds) to the
/// invitee's authenticated X25519 key. Its signed declaration pins its signing
/// key on first invite. The grant is K-ROOM's delegation.
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
    let passphrase = passphrase()?;
    if let Some(released) = resume_release(root, workspace, room_name, proposal_id, &passphrase)? {
        eprintln!("room {room_name}: release {proposal_id} disclosed epoch(s) {:?} for {invitee}",
            released.wraps.iter().map(|w| w.epoch).collect::<Vec<_>>());
        return Ok(());
    }
    let (room_ref, room, keys) = private_room(root, room_name)?;
    let synced = sync(root, workspace, room_name)?;
    let head = synced.lineage.head.clone().ok_or_else(|| format!("{room_name} has no keys yet"))?;
    if synced.ring.get(&room, head.epoch).is_none() {
        return Err(format!("{room_name} is at epoch {} and this client holds no key for it", head.epoch));
    }
    let invitee_number = subject_number(invitee)?;
    let record = invitation_record(invitee_number, enc_pub_hex, synced.records.get(&invitee_number))?;
    let signing = record.attestation.signing_public;
    record.authenticate(&room, &keys, &signing)?;
    check_declared_custody(&record, i_know)?;
    pin_member(root, &room, &keys, invitee_number, &signing, false)?;
    let (_, pins) = member_pins(root, &room, &keys)?;
    let recipient = Recipient::of(&authenticate_recipient(&pins, &room, &keys, &record)?)?;
    let founder = founder_signer(root, workspace, &room, &keys, &synced.lineage.chain)?;
    let epochs: Vec<u32> = if past {
        synced.ring.epochs(&room).into_iter().filter(|e| *e <= head.epoch).collect()
    } else {
        vec![head.epoch]
    };
    let keys_ref = writable_keys_ref(root, room_name, &room_ref, &keys)?;
    // Only the founder (whose keys reference carries the cell's control) can
    // delegate the keys grant.
    let control = reference(root, &keys_ref)?
        .get("controlCapability")
        .is_some_and(|control| !control.is_null());
    let grant = match grant_of(&synced.wraps, invitee_number) {
        0 if control => keys_grant(root, workspace, &keys_ref, invitee, &format!("{proposal_id}-grant"))?,
        known => known,
    };
    let mut deliveries = Vec::new();
    for e in epochs {
        let held: Vec<&WrapAtom> = synced.wraps.iter()
            .filter(|w| w.member == invitee_number && w.epoch == e).collect();
        if held.iter().any(|w| w.enc_id == recipient.enc.id()) {
            eprintln!("room {room_name}: {invitee} already holds a wrap at epoch {e} to this key");
            continue;
        }
        if held.iter().any(|w| w.gen == recipient.gen) {
            return Err(format!(
                "{invitee} holds a wrap at epoch {e} to another key at generation {}: only a key {invitee} publishes as its record (`room register`, or `rotate-key`) can be wrapped again", recipient.gen));
        }
        if synced.lineage.releases.contains_key(&release_atom_id(e, recipient.gen, invitee_number)) {
            return Err(format!("the release address of epoch {e} for {invitee} at generation {} is burned by a dead release: rotate the room (`room rotate`) and invite at the new epoch", recipient.gen));
        }
        let key = synced.ring.get(&room, e).expect("listed epoch");
        let certificate = synced.lineage.certificates.get(&e)
            .ok_or_else(|| format!("held epoch {e} is not on the authenticated chain; it is never released"))?;
        let wrap = WrapAtom::new(&room, invitee, &recipient.enc, recipient.gen, grant, &key)?
            .sign(certificate, founder.subject, founder.key_epoch, &founder.signer)?;
        deliveries.push(Delivery::new(wrap, recipient.record, &founder)?);
    }
    if deliveries.is_empty() {
        return Err(format!("{invitee} already holds a wrap to this key at every epoch asked for"));
    }
    let me = founder.subject;
    let mut host = LiveHost { root, workspace, room_ref, keys: keys.clone() };
    let released = run_release(root, &mut host, &founder.pin, me, &room, proposal_id, &passphrase, || {
        Ok(ReleaseSpec { room: room.clone(), keys: keys.clone(), keys_ref, purpose: "invite",
            head_before: Some(head), key: None, deliveries })
    })?;
    eprintln!("room {room_name}: released epoch(s) {:?} for {invitee}",
        released.wraps.iter().map(|w| w.epoch).collect::<Vec<_>>());
    Ok(())
}

/// The authenticated recipients of every kept member at the head: its pinned
/// record, or (the founder) its own current key.
fn kept_recipients(root: &Path, workspace: &Value, synced: &Synced, head: u32,
    current: &BTreeSet<u64>, dropped: Option<u64>) -> Result<BTreeMap<u64, Recipient>> {
    let me = subject_number(member(workspace, "subject")?)?;
    let (_, pins) = member_pins(root, &synced.room, &synced.keys)?;
    let own = own_secret(workspace)?.public().clone();
    members_at(&synced.wraps, head).into_keys()
        .filter(|member| Some(*member) != dropped && current.contains(member))
        .map(|member| {
            if member == me {
                let gen = synced.records.get(&me).filter(|r| r.enc == own).map_or(0, |r| r.key_epoch);
                return Ok((me, Recipient { gen, enc: own.clone(), record: [0; 32] }));
            }
            let record = synced.records.get(&member)
                .ok_or_else(|| format!("member {member} must publish a signed recipient-key record"))?;
            Ok((member, Recipient::of(&authenticate_recipient(&pins, &synced.room, &synced.keys, record)?)?))
        }).collect()
}

/// Rotate: a fresh key at the next unburned epoch, released to every member at
/// the head who still holds a grant covering the room (the Host's `who`) and is
/// not `dropped`.
pub(crate) fn rotate(
    root: &Path,
    workspace: &Value,
    room_name: &str,
    dropped: Option<&str>,
    proposal_id: &str,
) -> Result<()> {
    let passphrase = passphrase()?;
    let (room_ref, room, keys) = private_room(root, room_name)?;
    let released = match resume_release(root, workspace, room_name, proposal_id, &passphrase)? {
        Some(released) => released,
        None => {
            let synced = sync(root, workspace, room_name)?;
            let current = who_members(root, workspace, &room_ref)?;
            let dropped = dropped.map(subject_number).transpose()?;
            let head = synced.lineage.head.clone().ok_or("room has no keys")?;
            let recipients = kept_recipients(root, workspace, &synced, head.epoch, &current, dropped)?;
            let founder = founder_signer(root, workspace, &room, &keys, &synced.lineage.chain)?;
            let next = synced.lineage.next_epoch()?;
            let (key, wraps, left) = rotation(&room, &synced.wraps, head.epoch, next, &recipients, &current, dropped)?;
            if !wraps.iter().any(|(w, _)| w.member == founder.subject) {
                return Err("this rotation would not wrap the new key to its writer: only a current member rotates".into());
            }
            if !left.is_empty() {
                eprintln!("room {room_name}: left out of epoch {next}: {left:?} (they keep the past; they get nothing new)");
            }
            let certificate = EpochCertificate::sign(&room, &keys, &key, head.identity, founder.subject,
                founder.key_epoch, &founder.signer)?;
            let deliveries = wraps.into_iter().map(|(wrap, record)| {
                Delivery::new(wrap.sign(&certificate, founder.subject, founder.key_epoch, &founder.signer)?, record, &founder)
            }).collect::<Result<Vec<_>>>()?;
            let keys_ref = writable_keys_ref(root, room_name, &room_ref, &keys)?;
            let mut host = LiveHost { root, workspace, room_ref: room_ref.clone(), keys: keys.clone() };
            let released = run_release(root, &mut host, &founder.pin, founder.subject, &room, proposal_id, &passphrase, || {
                Ok(ReleaseSpec { room: room.clone(), keys: keys.clone(), keys_ref, purpose: "rotate",
                    head_before: Some(head), key: Some(key), deliveries })
            })?;
            install_released_key(root, &passphrase, &room, released.key.as_ref())?;
            released
        }
    };
    let epoch = released.key.as_ref().map(RoomKey::epoch);
    let members: Vec<String> = released.wraps.iter().map(|w| w.member.to_string()).collect();
    println!("{}", serde_json::to_string_pretty(&json!({"type":"minidregg-room-rotation-v1",
        "room":room_name,"epoch":epoch,"wrappedFor":members,
        "note":"members left out keep the past; they get nothing new"})).map_err(|e| e.to_string())?);
    Ok(())
}

/// Write (create, or edit to the current key) this subject's encryption-key
/// record in one private room's keys cell. One signed line: the law admits it
/// from this subject only, at its own number. Returns what it did.
pub(crate) fn register(root: &Path, workspace: &Value, room_name: &str, key_epoch: &str, proposal_id: &str) -> Result<Value> {
    let key_epoch: u32 = key_epoch.parse().map_err(|_| format!("key epoch {key_epoch} is not a 32-bit decimal"))?;
    let (room_ref, room, keys) = private_room(root, room_name)?;
    let (view, _, _) = signed_view(root, workspace, &keys_view_ref(&room_ref, &keys)?, "resource")?;
    let me = subject_number(member(workspace, "subject")?)?;
    let public = own_secret(workspace)?.public().clone();
    let wraps = wraps_in_view(&view)?;
    let signer = crate::read_secret(&member_path(workspace, "key")?)?;
    let hosted = private::key_is_hosted(&member_path(workspace, "key")?);
    let payload = EncRecord::signed_payload(&room, &keys, me, key_epoch, hosted, &public, &signer)?;
    let kind = json!({"type":"inlineObject","schema":record_schema()});
    let action = match records_in_view(&view).remove(&me) {
        Some(record) if record.enc == public && record.key_epoch == key_epoch
            && record.attestation.hosted == hosted
            && record.authenticate(&room, &keys, &signer.verifying_key().to_bytes()).is_ok() => {
            return Ok(json!({"room":room_name,"record":"already current","keyEpoch":key_epoch.to_string()}));
        }
        Some(record) => {
            let before = super::atom_record(&record.atom)?;
            json!({"type":"editAtom","atom":me.to_string(),"before":before,"kind":kind,
                "payload":hex(&payload),"tombstone":false})
        }
        None => json!({"type":"createAtom","atom":me.to_string(),"kind":kind,"payload":hex(&payload)}),
    };
    // The founder writes through its own keys reference; a member through the
    // keys grant its wraps carry.
    let keys_ref = match grant_of(&wraps, me) {
        0 => writable_keys_ref(root, room_name, &room_ref, &keys)?,
        grant => writable_keys_ref_with(root, room_name, &room_ref, &keys, Some(grant))?,
    };
    turn(root, workspace, proposal_id, &json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":[{"name":keys_ref,"payload":{"type":"content","actions":[action]}}]}))?;
    Ok(json!({"room":room_name,"record":"published","keyEpoch":key_epoch.to_string(),
        "encryptionKey":hex(&public.id())}))
}

/// After an admitted `rotate-key`: publish the new encryption key to every
/// private room this workspace references. Never fails the rotation (it is
/// already installed); each room's outcome is returned and printed, and a room
/// it could not reach is named with the one line that repairs it.
pub(crate) fn publish_rotation(root: &Path, key_epoch: &str) -> Value {
    let workspace = match super::load(root) {
        Ok(workspace) => workspace,
        Err(error) => return json!([{"error": format!("cannot load the workspace to publish: {error}")}]),
    };
    let rooms = private_room_names(root);
    let mut out = Vec::new();
    for name in rooms {
        let nonce = super::random_nonce().unwrap_or_default();
        let proposal = format!("rk-reg-{}", &nonce[nonce.len().saturating_sub(16)..]);
        match register(root, &workspace, &name, key_epoch, &proposal) {
            Ok(done) => {
                eprintln!("room {name}: your new encryption key is published (key epoch {key_epoch}); the founder's next rotation wraps to it");
                out.push(done);
            }
            Err(error) => {
                eprintln!("room {name}: could NOT publish your new encryption key ({error}); until you do, its next epochs are wrapped to your old key or not at all. Repair: `room register {name}`");
                out.push(json!({"room":name,"error":error}));
            }
        }
    }
    if out.is_empty() {
        eprintln!("no private room references in this workspace: no encryption key to publish");
    }
    Value::Array(out)
}

/// `room rewrap ID ROOM SUBJECT` (the founder): release every epoch this founder
/// holds again to SUBJECT's recorded key, where SUBJECT holds no wrap to it --
/// the repair for a member who published a new encryption key. The record must
/// verify under SUBJECT's pinned signing key (a member whose signing key changed
/// re-declares to the founder directly: `pin-member --replace true`).
pub(crate) fn rewrap(root: &Path, workspace: &Value, room_name: &str, subject: &str, proposal_id: &str) -> Result<()> {
    let passphrase = passphrase()?;
    if let Some(released) = resume_release(root, workspace, room_name, proposal_id, &passphrase)? {
        eprintln!("room {room_name}: release {proposal_id} disclosed epoch(s) {:?} for {subject}",
            released.wraps.iter().map(|w| w.epoch).collect::<Vec<_>>());
        return Ok(());
    }
    let number = subject_number(subject)?;
    let (room_ref, room, keys) = private_room(root, room_name)?;
    let synced = sync(root, workspace, room_name)?;
    let head = synced.lineage.head.clone().ok_or("room has no keys")?;
    let record = synced.records.get(&number).ok_or_else(|| {
        format!("{subject} has published no encryption-key record in {room_name}: it runs `room register {room_name}` first")
    })?;
    let (_, pins) = member_pins(root, &room, &keys)?;
    let recipient = Recipient::of(&authenticate_recipient(&pins, &room, &keys, record)?)?;
    let founder = founder_signer(root, workspace, &room, &keys, &synced.lineage.chain)?;
    let mut deliveries = Vec::new();
    for epoch in synced.ring.epochs(&room) {
        let held: Vec<&WrapAtom> = synced.wraps.iter().filter(|w| w.member == number && w.epoch == epoch).collect();
        if held.is_empty() || held.iter().any(|w| w.enc_id == recipient.enc.id() || w.gen == recipient.gen) {
            continue;
        }
        if synced.lineage.releases.contains_key(&release_atom_id(epoch, recipient.gen, number)) {
            return Err(format!("the release address of epoch {epoch} for {subject} is burned by a dead release: rotate the room instead"));
        }
        let key = synced.ring.get(&room, epoch).expect("listed epoch");
        let certificate = synced.lineage.certificates.get(&epoch)
            .ok_or_else(|| format!("held epoch {epoch} is not on the authenticated chain"))?;
        let wrap = WrapAtom::new(&room, subject, &recipient.enc, recipient.gen,
            grant_of(&synced.wraps, number), &key)?
            .sign(certificate, founder.subject, founder.key_epoch, &founder.signer)?;
        deliveries.push(Delivery::new(wrap, recipient.record, &founder)?);
    }
    if deliveries.is_empty() {
        return Err(format!("{subject} already holds a wrap to its recorded key at every epoch it was wrapped at"));
    }
    let keys_ref = writable_keys_ref(root, room_name, &room_ref, &keys)?;
    let mut host = LiveHost { root, workspace, room_ref, keys: keys.clone() };
    let released = run_release(root, &mut host, &founder.pin, founder.subject, &room, proposal_id, &passphrase, || {
        Ok(ReleaseSpec { room: room.clone(), keys: keys.clone(), keys_ref, purpose: "rewrap",
            head_before: Some(head), key: None, deliveries })
    })?;
    println!("{}", serde_json::to_string_pretty(&json!({"type":"minidregg-room-rewrap-v1",
        "room":room_name,"member":subject,"epochs":released.wraps.iter().map(|w| w.epoch).collect::<Vec<_>>(),
        "generation":recipient.gen,"encryptionKey":hex(&recipient.enc.id())})).map_err(|e| e.to_string())?);
    Ok(())
}

/// `room kick` in a private room: the K-ROOM revoke, then the rotation.
pub(crate) fn kick(root: &Path, workspace: &Value, room_name: &str, subject: &str, proposal_id: &str) -> Result<()> {
    // Do not revoke and then discover a kept member cannot be authenticated: a
    // partial kick would leave the former member holding the active epoch.
    // This is a preflight only; the rotation's readback checks again.
    let dropped = subject_number(subject)?;
    let synced = sync(root, workspace, room_name)?;
    let head = synced.epoch().ok_or("room has no keys")?;
    let everyone: BTreeSet<u64> = members_at(&synced.wraps, head).into_keys().collect();
    kept_recipients(root, workspace, &synced, head, &everyone, Some(dropped))?;
    // Every standing grant the member holds under the room, then the rotation.
    super::room_kick(root, workspace, room_name, subject, proposal_id, true)?;
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
    const KEYS: &str = "72";
    const FOUNDER: u64 = 11;

    fn founder_key() -> SigningKey { SigningKey::from_bytes(&[1; 32]) }

    fn founder() -> Founder { Founder { signer: founder_key(), subject: FOUNDER, key_epoch: 0, pin: pinned() } }

    fn pinned() -> [u8; 32] { founder_key().verifying_key().to_bytes() }

    fn dk(n: u8) -> MemberSecret { derive_enc_key(&[n; 32]).unwrap() }

    fn ep(n: u8) -> MemberPublic { enc_public(&[n; 32]).unwrap() }

    fn wrap_for(seed: u8, member: &str, key: &RoomKey) -> WrapAtom {
        WrapAtom::new(ROOM, member, &ep(seed), 0, 0, key).unwrap()
    }

    fn signed_record(seed: u8, member: u64, epoch: u32) -> EncRecord {
        let payload = EncRecord::signed_payload(ROOM, KEYS, member, epoch, false,
            &ep(seed), &SigningKey::from_bytes(&[seed; 32])).unwrap();
        EncRecord::from_atom(&member.to_string(), &payload, &json!({})).unwrap()
    }

    fn pins_for(entries: &[(u64, u8)]) -> BTreeMap<u64, [u8; 32]> {
        entries.iter().map(|(member, seed)|
            (*member, SigningKey::from_bytes(&[*seed; 32]).verifying_key().to_bytes())).collect()
    }

    fn recipient(seed: u8, member: u64, epoch: u32) -> Recipient {
        let record = signed_record(seed, member, epoch);
        Recipient::of(&authenticate_recipient(&pins_for(&[(member, seed)]), ROOM, KEYS, &record).unwrap()).unwrap()
    }

    fn recipients(entries: &[(u64, u8)]) -> BTreeMap<u64, Recipient> {
        entries.iter().map(|(member, seed)| (*member, recipient(*seed, *member, 0))).collect()
    }

    /// A founder-signed epoch: its certificate and one released delivery per (member, seed).
    fn epoch(key: &RoomKey, parent: [u8; 32], members: &[(u64, u8)], signer: &SigningKey)
        -> (EpochCertificate, Vec<Delivery>) {
        let certificate = EpochCertificate::sign(ROOM, KEYS, key, parent, FOUNDER, 0, signer).unwrap();
        let deliveries = members.iter().map(|(member, seed)| {
            let wrap = wrap_for(*seed, &member.to_string(), key).sign(&certificate, FOUNDER, 0, signer).unwrap();
            let release = ReleaseStatement::sign(&wrap, [0; 32], signer).unwrap();
            Delivery { wrap, release }
        }).collect();
        (certificate, deliveries)
    }

    fn atom(action: &Value) -> Value {
        json!({"type":"atom","id":action["atom"],"kind":action["kind"],"payload":action["payload"]})
    }

    fn cell(deliveries: &[&Delivery]) -> Value {
        let mut entries = Vec::new();
        for delivery in deliveries {
            entries.push(atom(&delivery.release.action()));
            entries.push(atom(&delivery.wrap.action()));
        }
        json!({"cell":{"entries":entries}})
    }

    fn record_atom(record: &EncRecord) -> Value {
        json!({"type":"atom","id":record.member.to_string(),
            "kind":{"type":"inlineObject","schema":record_schema()},
            "payload":hex(&record.canonical_signed_payload().unwrap())})
    }

    #[test]
    fn founder_unsigned_or_foreign_wrap_set_is_refused() {
        let e0 = RoomKey::generate(0).unwrap();
        let (c0, d0) = epoch(&e0, [0; 32], &[(13, 3)], &founder_key());
        let lineage = verify_lineage(ROOM, KEYS, &pinned(), &cell(&[&d0[0]]), None).unwrap();
        assert_eq!(lineage.head, Some(EpochHead { epoch: 0, identity: c0.identity() }));
        // The operator mints epoch 1 under its own key and serves it beside the
        // genuine genesis: refused, whole, never skipped.
        let operator = SigningKey::from_bytes(&[8; 32]);
        let minted = RoomKey::generate(1).unwrap();
        let (_, forged) = epoch(&minted, c0.identity(), &[(13, 3)], &operator);
        assert!(verify_lineage(ROOM, KEYS, &pinned(), &cell(&[&d0[0], &forged[0]]), None).is_err(),
            "an operator-signed epoch is not the pinned founder's");
        // A forged wrap carried beside a GENUINE release fails the commitment.
        let mut swapped = forged[0].clone();
        swapped.release = d0[0].release.clone();
        assert!(verify_lineage(ROOM, KEYS, &pinned(), &cell(&[&swapped]), None).is_err());
        // An unsigned wrap, or a genuine wrap without its release record, is refused.
        let unsigned = json!({"cell":{"entries":[atom(&d0[0].release.action()),
            atom(&wrap_for(3, "13", &e0).action())]}});
        assert!(verify_lineage(ROOM, KEYS, &pinned(), &unsigned, None).is_err());
        let bare = json!({"cell":{"entries":[atom(&d0[0].wrap.action())]}});
        assert!(verify_lineage(ROOM, KEYS, &pinned(), &bare, None).unwrap_err()
            .contains("without a founder-signed release"));
        // The same founder-signed set under another room's pin or context is refused.
        assert!(verify_lineage(ROOM, KEYS, &operator.verifying_key().to_bytes(), &cell(&[&d0[0]]), None).is_err());
        assert!(verify_lineage(ROOM, "73", &pinned(), &cell(&[&d0[0]]), None).is_err());
        // A changed wrap byte under the same release fails.
        let mut replaced = d0[0].clone();
        replaced.wrap.wrapped = wrap_for(3, "13", &minted).wrapped;
        assert!(verify_lineage(ROOM, KEYS, &pinned(), &cell(&[&replaced]), None).is_err());
    }

    #[test]
    fn older_or_equivocating_lineage_is_refused_and_never_selects_an_old_sealing_key() {
        let e0 = RoomKey::generate(0).unwrap();
        let (c0, d0) = epoch(&e0, [0; 32], &[(13, 3)], &founder_key());
        let e1 = RoomKey::generate(1).unwrap();
        let (c1, d1) = epoch(&e1, c0.identity(), &[(13, 3)], &founder_key());
        let head = verify_lineage(ROOM, KEYS, &pinned(), &cell(&[&d0[0], &d1[0]]), None).unwrap().head.unwrap();
        assert_eq!(head, EpochHead { epoch: 1, identity: c1.identity() });
        assert!(verify_lineage(ROOM, KEYS, &pinned(), &cell(&[&d0[0]]), Some(&head)).is_err(),
            "the operator cannot return the pre-kick prefix to a client that saw epoch 1");
        assert!(verify_lineage(ROOM, KEYS, &pinned(), &json!({"cell":{"entries":[]}}), Some(&head)).is_err(),
            "an empty cell cannot erase a retained head");
        // A second founder-signed epoch 1 (equivocation) is refused against the head.
        let other = RoomKey::generate(1).unwrap();
        let (_, fork) = epoch(&other, c0.identity(), &[(13, 3)], &founder_key());
        assert!(verify_lineage(ROOM, KEYS, &pinned(), &cell(&[&d0[0], &fork[0]]), Some(&head)).is_err());
        assert!(advance_head(Some(&head), &EpochHead { epoch: 1, identity: [8; 32] }).is_err());
        // Monotone sealing: a ring above the head, a forgotten head key, or a
        // cached key differing from the certificate never seals.
        let mut ring = Keyring::default();
        ring.insert(ROOM, &e0);
        ring.insert(ROOM, &e1);
        let key = select_current_key(&ring, ROOM, &head, &c1).unwrap();
        let payload = seal_for_room(&key, ROOM, "80", "1", b"after kick").unwrap();
        let mut kicked = Keyring::default();
        kicked.insert(ROOM, &e0);
        assert!(open_in_room(Some(&kicked), ROOM, "80", "1", &payload).is_string());
        let old_head = EpochHead { epoch: 0, identity: c0.identity() };
        assert!(select_current_key(&ring, ROOM, &old_head, &c0).is_err(), "ring above head refuses");
        assert!(check_ring_below_head(&ring, ROOM, Some(&old_head)).is_err());
        assert!(check_ring_below_head(&ring, ROOM, None).is_err());
        assert!(check_ring_below_head(&ring, ROOM, Some(&head)).is_ok());
        ring.forget(ROOM, 1);
        assert!(select_current_key(&ring, ROOM, &head, &c1).is_err(), "forgetting the head key never falls back to epoch 0");
        let mut poisoned = Keyring::default();
        poisoned.insert(ROOM, &RoomKey::generate(1).unwrap());
        assert!(select_current_key(&poisoned, ROOM, &head, &c1).is_err());
    }

    #[test]
    fn the_chain_starts_at_genesis_skips_burned_epochs_and_never_forks() {
        let e0 = RoomKey::generate(0).unwrap();
        let (c0, d0) = epoch(&e0, [0; 32], &[(13, 3)], &founder_key());
        let e2 = RoomKey::generate(2).unwrap();
        let (c2, d2) = epoch(&e2, c0.identity(), &[(13, 3)], &founder_key());
        let head = check_epoch_chain(&[d0[0].wrap.clone(), d2[0].wrap.clone()], None).unwrap().unwrap();
        assert_eq!(head, EpochHead { epoch: 2, identity: c2.identity() }, "a burned epoch 1 is skipped");
        assert!(check_epoch_chain(&[d2[0].wrap.clone()], None).is_err(), "no genesis");
        assert_eq!(check_epoch_chain(&[], None).unwrap(), None);
        // A wrap at the burned epoch 1 appearing later breaks the chain.
        let e1 = RoomKey::generate(1).unwrap();
        let (_, d1) = epoch(&e1, c0.identity(), &[(13, 3)], &founder_key());
        assert!(check_epoch_chain(&[d0[0].wrap.clone(), d1[0].wrap.clone(), d2[0].wrap.clone()], None).is_err());
    }

    #[test]
    fn recipient_signature_rejects_operator_substitution_and_unpinned_members() {
        let signer = SigningKey::from_bytes(&[9; 32]);
        let trusted_public = signer.verifying_key().to_bytes();
        let payload = EncRecord::signed_payload(ROOM, KEYS, 11, 2, false, &ep(9), &signer).unwrap();
        let parse = |bytes: &[u8]| EncRecord::from_atom("11", bytes, &json!({})).unwrap();
        let pins = pins_for(&[(11, 9)]);
        let legitimate = Recipient::of(&authenticate_recipient(&pins, ROOM, KEYS, &parse(&payload)).unwrap()).unwrap();
        assert_eq!((legitimate.gen, legitimate.enc.clone()), (2, ep(9)));
        let old_key = RoomKey::generate(0).unwrap();
        let wraps = [wrap_for(1, "11", &old_key)];
        let (new_key, released, _) = rotation(ROOM, &wraps, 0, 1, &[(11, legitimate)].into_iter().collect(),
            &[11].into_iter().collect(), None).unwrap();
        assert_eq!(released[0].0.open(ROOM, &dk(9)).unwrap().bytes(), new_key.bytes());
        assert!(released[0].0.open(ROOM, &dk(8)).is_err());
        let mut substituted = payload.clone();
        substituted[4..36].copy_from_slice(ep(8).x25519());
        assert!(parse(&substituted).authenticate(ROOM, KEYS, &trusted_public).is_err(),
            "the signature binds the X25519 half");
        // ... and the ML-KEM half: splicing in another member's encapsulation key
        // yields a well-formed key the signature does not cover.
        let mut spliced = payload.clone();
        spliced[36..4 + MEMBER_PUBLIC_LEN].copy_from_slice(&ep(8).to_bytes()[32..]);
        assert!(parse(&spliced).authenticate(ROOM, KEYS, &trusted_public).is_err(),
            "the signature binds the ML-KEM-768 half");
        let operator = SigningKey::from_bytes(&[8; 32]);
        let forged = EncRecord::signed_payload(ROOM, KEYS, 11, 2, false, &ep(8), &operator).unwrap();
        assert!(authenticate_recipient(&pins, ROOM, KEYS, &parse(&forged)).is_err(),
            "a record self-signed by an operator-chosen key is not the pinned member");
        assert!(parse(&payload).authenticate("70", KEYS, &trusted_public).is_err());
        assert!(parse(&payload).authenticate(ROOM, "73", &trusted_public).is_err());
        let relabelled = EncRecord::from_atom("12", &payload, &json!({})).unwrap();
        assert!(relabelled.authenticate(ROOM, KEYS, &trusted_public).is_err());
        // Pre-hybrid records refuse by name: v1 (unsigned, 36 bytes) and v2
        // (signed, X25519 only, 148 bytes) are never read as a key.
        let v1 = [&2u32.to_be_bytes()[..], ep(9).x25519()].concat();
        let error = EncRecord::from_atom("11", &v1, &json!({})).unwrap_err();
        assert!(error.contains("DREGG/PRIVATE-ENC-KEY/v1") && error.contains("refused"), "{error}");
        let mut v2 = v1.clone();
        v2.extend([0u8; 112]);
        assert_eq!(v2.len(), 148);
        let error = EncRecord::from_atom("11", &v2, &json!({})).unwrap_err();
        assert!(error.contains("DREGG/PRIVATE-ENC-KEY/v2") && error.contains("refused"), "{error}");
        assert!(EncRecord::from_atom("11", &payload[..payload.len() - 1], &json!({})).is_err());
        assert!(authenticate_recipient(&BTreeMap::new(), ROOM, KEYS, &parse(&payload)).unwrap_err()
            .contains("no pinned signing key"), "an unpinned member is never authenticated from what the node serves");
    }

    #[test]
    fn wrap_atoms_round_trip_through_a_view_and_open_only_for_their_member() {
        let e0 = RoomKey::generate(0).unwrap();
        let wraps = vec![wrap_for(1, "11", &e0), wrap_for(2, "12", &e0)];
        let view = json!({"cell":{"entries":wraps.iter().map(|w| atom(&w.action())).collect::<Vec<_>>()}});
        let parsed = wraps_in_view(&view).unwrap();
        assert_eq!(parsed, wraps);
        assert_eq!(parsed[0].action()["atom"], wrap_atom_id(0, 0, 11));
        let key = parsed[1].open(ROOM, &dk(2)).unwrap();
        assert_eq!((key.epoch(), key.bytes()), (0, e0.bytes()));
        assert!(parsed[1].open(ROOM, &dk(1)).is_err(), "a member cannot open another's wrap");
        assert!(parsed[1].open("70", &dk(2)).is_err(), "a wrap is bound to its room");
    }

    #[test]
    fn wrap_and_release_atom_ids_name_one_address_in_disjoint_regions() {
        // Kernel/PrivateRoomKeys.lean wrapAtomId: (epoch + 1) * 2^96 + gen * 2^64 + member.
        assert_eq!(wrap_atom_id(0, 0, 12), ((1u128 << 96) + 12).to_string());
        assert_eq!(wrap_atom_id(1, 2, 12), ((2u128 << 96) + (2u128 << 64) + 12).to_string());
        assert_eq!(parse_wrap_atom_id(&wrap_atom_id(7, 3, u64::MAX)).unwrap(), (7, 3, u64::MAX));
        assert_eq!(parse_wrap_atom_id(&wrap_atom_id(MAX_EPOCH, u32::MAX, 1)).unwrap(), (MAX_EPOCH, u32::MAX, 1));
        assert_ne!(wrap_atom_id(4, 1, 12), wrap_atom_id(4, 2, 12), "a re-wrap is a new atom");
        assert!(parse_wrap_atom_id("012").is_err());
        assert!(parse_wrap_atom_id("12").is_err(), "the record region is not a wrap");
        assert!(parse_wrap_atom_id(&release_atom_id(0, 0, 12)).is_err(), "the release region is not a wrap");
        let highest_wrap: u128 = wrap_atom_id(MAX_EPOCH, u32::MAX, u64::MAX).parse().unwrap();
        let lowest_release: u128 = release_atom_id(0, 0, 0).parse().unwrap();
        let highest_release: u128 = release_atom_id(MAX_EPOCH, u32::MAX, u64::MAX).parse().unwrap();
        assert!(highest_wrap < lowest_release && highest_release < u128::MAX);
        let e3 = RoomKey::generate(3).unwrap();
        let id = wrap_atom_id(3, 0, 11);
        let mut payload = wrap_for(1, "11", &e3).payload();
        assert!(WrapAtom::from_atom(&id, &payload[..payload.len() - 1]).is_err());
        payload.push(0);
        assert!(WrapAtom::from_atom(&id, &payload).is_err());
        let (_, d) = epoch(&e3, [0; 32], &[(1, 1)], &founder_key());
        let release = &d[0].release;
        assert_eq!(ReleaseStatement::from_atom(&release.atom(), &release.payload()).unwrap(), *release);
        assert!(ReleaseStatement::from_atom(&release_atom_id(4, 0, 1), &release.payload()).is_err(),
            "a release is only valid at the address its statement names");
    }

    #[test]
    fn a_member_who_rotated_is_rewrapped_to_its_record_and_opens_with_its_keyring() {
        let e0 = RoomKey::generate(0).unwrap();
        let mut old = wrap_for(1, "11", &e0);
        old.grant = 900;
        let wraps0 = vec![wrap_for(2, "12", &e0), old.clone()];
        // 11 rotated: its record names the key of seed 9 at key epoch 2.
        let records = [(11, recipient(9, 11, 2)), (12, recipient(2, 12, 0))].into_iter().collect();
        let current: BTreeSet<u64> = [11, 12].into_iter().collect();
        let (e1, wraps1, _) = rotation(ROOM, &wraps0, 0, 1, &records, &current, None).unwrap();
        let mine = &wraps1.iter().find(|(w, _)| w.member == 11).unwrap().0;
        assert_eq!((mine.gen, mine.grant), (2, 900), "to the record, carrying the keys grant");
        assert!(mine.open(ROOM, &dk(1)).is_err(), "the OLD secret cannot open the new epoch");
        assert_eq!(mine.open(ROOM, &dk(9)).unwrap().bytes(), e1.bytes());
        assert_eq!(old.open(ROOM, &dk(1)).unwrap().bytes(), e0.bytes());
        assert!(rotation(ROOM, &wraps0, 0, 1, &BTreeMap::new(), &current, None).is_err(),
            "an operator-served old wrap cannot substitute for an authenticated recipient");
        assert!(rotation(ROOM, &wraps0, 1, 1, &records, &current, None).is_err());
    }

    // ---- founder-key transition ----

    fn key_n(n: u8) -> SigningKey { SigningKey::from_bytes(&[n; 32]) }

    fn pub_of(key: &SigningKey) -> [u8; 32] { key.verifying_key().to_bytes() }

    fn head_of(certificate: &EpochCertificate) -> EpochHead {
        EpochHead { epoch: certificate.epoch, identity: certificate.identity() }
    }

    fn cell_with(extra: &[Value], deliveries: &[&Delivery]) -> Value {
        let mut entries = cell(deliveries)["cell"]["entries"].as_array().unwrap().clone();
        entries.extend(extra.iter().cloned());
        json!({"cell":{"entries":entries}})
    }

    fn handed(index: u32, after: &EpochCertificate, old: &SigningKey, new: &SigningKey) -> FounderTransition {
        FounderTransition::sign(ROOM, KEYS, index, &head_of(after), old, new).unwrap()
    }

    fn t_atom(t: &FounderTransition) -> Value { atom(&t.action()) }

    #[test]
    fn a_founder_key_transition_moves_the_room_to_the_next_key_without_a_re_pin() {
        let (k0, k1) = (founder_key(), key_n(21));
        let e0 = RoomKey::generate(0).unwrap();
        let (c0, d0) = epoch(&e0, [0; 32], &[(13, 3)], &k0);
        let t0 = handed(0, &c0, &k0, &k1);
        let e1 = RoomKey::generate(1).unwrap();
        let (c1, d1) = epoch(&e1, c0.identity(), &[(13, 3)], &k1);
        let view = cell_with(&[t_atom(&t0)], &[&d0[0], &d1[0]]);
        // The client pinned k0 and never re-pins: the chain carries it to k1.
        let lineage = verify_lineage(ROOM, KEYS, &pub_of(&k0), &view, None).unwrap();
        assert_eq!((lineage.chain.tip(), lineage.chain.transitions()), (&pub_of(&k1), 1));
        assert_eq!(lineage.head, Some(head_of(&c1)));
        // A late joiner that was handed the CURRENT key out of band verifies the same cell,
        // history included (every link needs the later key's own signature).
        assert_eq!(verify_lineage(ROOM, KEYS, &pub_of(&k1), &view, None).unwrap().chain, lineage.chain);
        // A pin that is on no link of the chain refuses.
        let stranger = verify_lineage(ROOM, KEYS, &pub_of(&key_n(99)), &view, None).unwrap_err();
        assert!(stranger.contains("not on the founder-key chain"), "{stranger}");
        // With no transition the chain is the pin, as before.
        let plain = verify_lineage(ROOM, KEYS, &pub_of(&k0), &cell(&[&d0[0]]), None).unwrap();
        assert_eq!((plain.chain.tip(), plain.chain.transitions()), (&pub_of(&k0), 0));
        assert!(verify_lineage(ROOM, KEYS, &pub_of(&k1), &cell(&[&d0[0]]), None).is_err(),
            "a pin the served cell never mentions authenticates nothing");
    }

    #[test]
    fn a_retired_key_signs_nothing_after_the_hand_over_and_the_new_key_may_still_invite_into_old_epochs() {
        let (k0, k1) = (founder_key(), key_n(21));
        let e0 = RoomKey::generate(0).unwrap();
        let (c0, d0) = epoch(&e0, [0; 32], &[(13, 3)], &k0);
        let t0 = handed(0, &c0, &k0, &k1);
        // The retired key mints epoch 1 after handing over: refused whole.
        let e1 = RoomKey::generate(1).unwrap();
        let (_, late_by_old) = epoch(&e1, c0.identity(), &[(13, 3)], &k0);
        let refused = verify_lineage(ROOM, KEYS, &pub_of(&k0), &cell_with(&[t_atom(&t0)], &[&d0[0], &late_by_old[0]]), None);
        assert!(refused.is_err(), "epoch 1 must be signed by the key in effect at epoch 1");
        // A delivery of epoch 1 by the retired key: its certificate may be right, the delivery is not.
        let (c1, by_new) = epoch(&e1, c0.identity(), &[(13, 3)], &k1);
        let stale_delivery = {
            let wrap = wrap_for(4, "14", &e1).sign(&c1, FOUNDER, 0, &k0).unwrap();
            let release = ReleaseStatement::sign(&wrap, [0; 32], &k0).unwrap();
            Delivery { wrap, release }
        };
        assert!(verify_lineage(ROOM, KEYS, &pub_of(&k0),
            &cell_with(&[t_atom(&t0)], &[&d0[0], &by_new[0], &stale_delivery]), None).is_err());
        // The new key invites into the OLD epoch 0 (its certificate stays k0's): allowed.
        let invite_old = {
            let wrap = wrap_for(4, "14", &e0).sign(&c0, FOUNDER, 0, &k1).unwrap();
            let release = ReleaseStatement::sign(&wrap, [0; 32], &k1).unwrap();
            Delivery { wrap, release }
        };
        let view = cell_with(&[t_atom(&t0)], &[&d0[0], &invite_old]);
        assert!(verify_lineage(ROOM, KEYS, &pub_of(&k0), &view, None).is_ok());
        // The limit, said plainly: the cell cannot say WHEN a delivery was signed, so a delivery
        // of an epoch the retired key owned still verifies under it. What stops a retired key
        // from signing is the Host (it revokes the old key at rotation) and the tip guard of
        // the founder's own client (`require_tip`), not this verification.
        let by_retired = {
            let wrap = wrap_for(4, "14", &e0).sign(&c0, FOUNDER, 0, &k0).unwrap();
            let release = ReleaseStatement::sign(&wrap, [0; 32], &k0).unwrap();
            Delivery { wrap, release }
        };
        assert!(verify_lineage(ROOM, KEYS, &pub_of(&k0), &cell_with(&[t_atom(&t0)], &[&d0[0], &by_retired]), None).is_ok());
        // ... but not before the hand-over exists: without t0, k1 is nobody.
        assert!(verify_lineage(ROOM, KEYS, &pub_of(&k0), &cell(&[&d0[0], &invite_old]), None).is_err());
        // The tip guard the founder's own client applies.
        let chain = verify_lineage(ROOM, KEYS, &pub_of(&k0), &view, None).unwrap().chain;
        assert!(require_tip(&pub_of(&k1), &chain).is_ok());
        assert!(require_tip(&pub_of(&k0), &chain).unwrap_err().contains("not the tip"));
    }

    #[test]
    fn a_forged_one_sided_or_misplaced_transition_is_refused() {
        let (k0, k1, k2) = (founder_key(), key_n(21), key_n(22));
        let operator = key_n(8);
        let e0 = RoomKey::generate(0).unwrap();
        let (c0, d0) = epoch(&e0, [0; 32], &[(13, 3)], &k0);
        let check = |t: &FounderTransition| verify_lineage(ROOM, KEYS, &pub_of(&k0), &cell_with(&[t_atom(t)], &[&d0[0]]), None);
        assert!(check(&handed(0, &c0, &k0, &k1)).is_ok());
        // Signed by the OPERATOR as the old key: the pin is on no link.
        assert!(check(&handed(0, &c0, &operator, &k1)).is_err());
        // The old key named, its signature forged by the operator.
        let mut forged_old = handed(0, &c0, &k0, &k1);
        forged_old.old_signature = operator.sign(&forged_old.statement()).to_bytes();
        assert!(check(&forged_old).unwrap_err().contains("old key's signature"));
        // Possession not proven: the new key never signed (a hostile or mistyped key cannot take the room).
        let mut unproven = handed(0, &c0, &k0, &k1);
        unproven.new_signature = k0.sign(&unproven.statement()).to_bytes();
        assert!(check(&unproven).unwrap_err().contains("possession"));
        // Another room's or keys cell's transition.
        let mut elsewhere = handed(0, &c0, &k0, &k1);
        elsewhere.room += 1;
        assert!(check(&elsewhere).is_err());
        // Names a certificate the cell does not show, or another one than it shows.
        let mut ghost = handed(0, &c0, &k0, &k1);
        ghost.after_epoch = 5;
        assert!(check(&ghost).is_err());
        let mut wrong_cert = handed(0, &c0, &k0, &k1);
        wrong_cert.after_certificate[0] ^= 1;
        let error = check(&wrong_cert).unwrap_err();
        assert!(error.contains("signature") || error.contains("another certificate"), "{error}");
        // A link without its predecessor, a repeated address, a fork, a return to a retired key.
        assert!(check(&handed(1, &c0, &k0, &k1)).unwrap_err().contains("contiguous"));
        let t0 = handed(0, &c0, &k0, &k1);
        let repeated = verify_lineage(ROOM, KEYS, &pub_of(&k0), &cell_with(&[t_atom(&t0), t_atom(&t0)], &[&d0[0]]), None);
        assert!(repeated.unwrap_err().contains("repeats an address"));
        let fork = handed(1, &c0, &k0, &k2);
        assert!(verify_lineage(ROOM, KEYS, &pub_of(&k0), &cell_with(&[t_atom(&t0), t_atom(&fork)], &[&d0[0]]), None)
            .unwrap_err().contains("fork"));
        let back = handed(1, &c0, &k1, &k0);
        assert!(verify_lineage(ROOM, KEYS, &pub_of(&k0), &cell_with(&[t_atom(&t0), t_atom(&back)], &[&d0[0]]), None)
            .unwrap_err().contains("retired"));
        // Two hand-overs in a row chain: k0 -> k1 -> k2, both after epoch 0.
        let t1 = handed(1, &c0, &k1, &k2);
        let two = verify_lineage(ROOM, KEYS, &pub_of(&k0), &cell_with(&[t_atom(&t0), t_atom(&t1)], &[&d0[0]]), None).unwrap();
        assert_eq!((two.chain.tip(), two.chain.transitions()), (&pub_of(&k2), 2));
        // Wire shape: exact length, an address that matches its statement.
        let payload = t0.payload();
        assert_eq!(payload.len(), TRANSITION_BODY_LEN + 128);
        assert_eq!(FounderTransition::from_atom(&t0.atom(), &payload).unwrap(), t0);
        assert!(FounderTransition::from_atom(&t0.atom(), &payload[..payload.len() - 1]).is_err());
        assert!(FounderTransition::from_atom(&transition_atom_id(1), &payload).is_err());
        assert!(parse_wrap_atom_id(&t0.atom()).is_err(), "the transition region is not a wrap");
        let highest_release: u128 = release_atom_id(MAX_EPOCH, u32::MAX, u64::MAX).parse().unwrap();
        assert!(transition_atom_id(0).parse::<u128>().unwrap() > highest_release);
        assert!(transition_atom_id(MAX_TRANSITIONS - 1).parse::<u128>().unwrap() < (1u128 << 127) + (1u128 << 126));
    }

    #[test]
    fn a_client_that_saw_the_hand_over_refuses_a_cell_that_hides_it() {
        let (k0, k1) = (founder_key(), key_n(21));
        let e0 = RoomKey::generate(0).unwrap();
        let (c0, d0) = epoch(&e0, [0; 32], &[(13, 3)], &k0);
        let with = verify_lineage(ROOM, KEYS, &pub_of(&k0), &cell_with(&[t_atom(&handed(0, &c0, &k0, &k1))], &[&d0[0]]), None).unwrap();
        let without = verify_lineage(ROOM, KEYS, &pub_of(&k0), &cell(&[&d0[0]]), None).unwrap();
        let root = scratch("chain-head");
        let head = with.head.clone().unwrap();
        retain_epoch_head(&root, ROOM, KEYS, None, &head, &with.chain, &json!({})).unwrap();
        let (retained, _) = read_epoch_head(&root, ROOM, KEYS).unwrap().unwrap();
        assert_eq!(retained_transitions(Some(&retained)), 1);
        assert_eq!(retained_founder_tip(Some(&retained)), Some(pub_of(&k1)));
        assert!(check_chain_not_rolled_back(Some(&retained), &with.chain).is_ok());
        let hidden = check_chain_not_rolled_back(Some(&retained), &without.chain).unwrap_err();
        assert!(hidden.contains("hidden or rolled back"), "{hidden}");
        // A same-length chain that ends at another key is a fork.
        let k2 = key_n(22);
        let forked = verify_lineage(ROOM, KEYS, &pub_of(&k0), &cell_with(&[t_atom(&handed(0, &c0, &k0, &k2))], &[&d0[0]]), None).unwrap();
        assert!(check_chain_not_rolled_back(Some(&retained), &forked.chain).unwrap_err().contains("forks"));
        // A client that never saw one accepts the first sight (no history: residual R2).
        assert!(check_chain_not_rolled_back(None, &with.chain).is_ok());
        // Re-retaining the same chain is a no-op; a client's own sync is the only writer.
        retain_epoch_head(&root, ROOM, KEYS, Some(&retained), &head, &with.chain, &json!({})).unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn rotating_to_a_key_the_room_does_not_know_strands_only_the_founder_who_has_not_handed_over() {
        let (k0, k1) = (founder_key(), key_n(21));
        let e0 = RoomKey::generate(0).unwrap();
        let (c0, d0) = epoch(&e0, [0; 32], &[(13, 3)], &k0);
        let before = verify_lineage(ROOM, KEYS, &pub_of(&k0), &cell(&[&d0[0]]), None).unwrap().chain;
        let after = verify_lineage(ROOM, KEYS, &pub_of(&k0), &cell_with(&[t_atom(&handed(0, &c0, &k0, &k1))], &[&d0[0]]), None).unwrap().chain;
        // The founder still at k0, about to rotate to k1: stranded until the hand-over is published.
        assert!(rotation_strands(&pub_of(&k0), &pub_of(&k1), &before));
        // After the hand-over the tip is the next key: the rotation is safe.
        assert!(!rotation_strands(&pub_of(&k0), &pub_of(&k1), &after));
        // A member (not the tip) is never gated, whatever it rotates to.
        assert!(!rotation_strands(&pub_of(&key_n(77)), &pub_of(&k1), &before));
    }

    #[test]
    fn the_release_machinery_runs_under_the_new_founder_key_after_a_hand_over() {
        let (k0, k1) = (founder_key(), key_n(21));
        let root = scratch("after-handover");
        let (mut host, e0, c0, records) = genesis_host(&[FOUNDER, 13]);
        let t0 = handed(0, &c0, &k0, &k1);
        host.entries.push(t_atom(&t0));
        // k1 invites member 13 into epoch 0: its delivery and release are k1's; the readback
        // (check_readback, anchored at the PINNED k0) verifies them through the chain.
        let spec = {
            let record = &records[&13];
            let wrap = WrapAtom::new(ROOM, "13", &record.enc, 0, 0, &e0).unwrap().sign(&c0, FOUNDER, 1, &k1).unwrap();
            let founder = Founder { signer: k1.clone(), subject: FOUNDER, key_epoch: 1, pin: pub_of(&k0) };
            ReleaseSpec { room: ROOM.into(), keys: KEYS.into(), keys_ref: "lab-keys".into(), purpose: "invite",
                head_before: Some(head_of(&c0)), key: None,
                deliveries: vec![Delivery::new(wrap, record_digest(record).unwrap(), &founder).unwrap()] }
        };
        let released = run_release(&root, &mut host, &pub_of(&k0), FOUNDER, ROOM, "inv-2", b"pass", || Ok(spec)).unwrap();
        assert_eq!(released.wraps[0].attestation.as_ref().unwrap().signer_public, pub_of(&k1));
        let lineage = verify_lineage(ROOM, KEYS, &pub_of(&k0), &host.keys_view().unwrap(), None).unwrap();
        assert!(lineage.wraps.iter().any(|w| w.member == 13) && lineage.chain.tip() == &pub_of(&k1));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn a_pre_hybrid_v2_wrap_in_a_keys_cell_refuses_the_whole_cell_by_name() {
        // A v2 (X25519-only) wrap atom: the room predates the hybrid format. It is
        // refused by name, not skipped, so a stale room cannot read as an empty one.
        let old_schema = private::schema_decimal_of(AUTH_WRAP_FRAME_V2);
        assert_ne!(old_schema, wrap_schema(), "v2 and v3 are different schemas");
        let view = json!({"cell":{"entries":[{"type":"atom","id":wrap_atom_id(0, 0, 11),
            "kind":{"type":"inlineObject","schema":old_schema},"payload":"00"}]}});
        let error = wraps_in_view(&view).unwrap_err();
        assert!(error.contains("DREGG/PRIVATE-AUTH-WRAP/v2") && error.contains("refused"), "{error}");
        assert!(verify_lineage(ROOM, KEYS, &pinned(), &view, None).is_err());
        // A v3 cell is not mistaken for it.
        let e0 = RoomKey::generate(0).unwrap();
        let (_, d) = epoch(&e0, [0; 32], &[(13, 3)], &founder_key());
        assert!(wraps_in_view(&cell(&[&d[0]])).is_ok());
    }

    #[test]
    fn a_member_that_declares_hosted_custody_is_refused_without_i_know_and_cannot_be_altered_into_own_machine() {
        let signer = SigningKey::from_bytes(&[9; 32]);
        let public = signer.verifying_key().to_bytes();
        let hosted = EncRecord::signed_payload(ROOM, KEYS, 9, 0, true, &ep(9), &signer).unwrap();
        let own = EncRecord::signed_payload(ROOM, KEYS, 9, 0, false, &ep(9), &signer).unwrap();
        assert_eq!((hosted.len(), own.len()), (SIGNED_RECORD_LEN, SIGNED_RECORD_LEN));
        assert_eq!(SIGNED_RECORD_LEN, 1333);
        let parse = |bytes: &[u8]| EncRecord::from_atom("9", bytes, &json!({})).unwrap();
        let hosted_record = parse(&hosted);
        assert!(hosted_record.attestation.hosted && !parse(&own).attestation.hosted);
        assert!(hosted_record.authenticate(ROOM, KEYS, &public).is_ok());
        let refusal = check_declared_custody(&hosted_record, false).unwrap_err();
        assert!(refusal.contains("--i-know") && refusal.contains("declared this itself"), "{refusal}");
        assert!(check_declared_custody(&hosted_record, true).is_ok());
        assert!(check_declared_custody(&parse(&own), false).is_ok());
        // The custody byte is under the member's signature: flipping it to look
        // like an own-machine member breaks the record (an operator cannot launder a hosted member).
        let at = 4 + MEMBER_PUBLIC_LEN + 16;
        assert_eq!(hosted[at], 1);
        let mut laundered = hosted.clone();
        laundered[at] = 0;
        assert!(parse(&laundered).authenticate(ROOM, KEYS, &public).is_err());
        assert_ne!(record_digest(&hosted_record).unwrap(), record_digest(&parse(&own)).unwrap());
        let mut odd = hosted.clone();
        odd[at] = 2;
        assert!(EncRecord::from_atom("9", &odd, &json!({})).unwrap_err().contains("custody 2"));
    }

    #[test]
    fn every_private_invite_path_spells_one_room_key_invocation() {
        let dir = Path::new("/w");
        let flags = |op: &str, request: Option<&Path>, past, i_know|
            invite_flags(op, dir, "lab", "12", "ab", "i1", request, past, i_know)
                .into_iter().map(|(k, v)| (k, v.into_string().unwrap())).collect::<Vec<_>>();
        let pairs = |rows: &[(&str, &str)]| rows.iter()
            .map(|(k, v)| ((*k).to_owned(), (*v).to_owned())).collect::<Vec<_>>();
        assert_eq!(flags("invite", None, false, false), pairs(&[("action", "room-key"), ("op", "invite"),
            ("dir", "/w"), ("name", "lab"), ("member", "12"), ("enc-pub", "ab"), ("proposal-id", "i1")]));
        assert_eq!(flags("invite", Some(Path::new("/h/r.json")), true, true), pairs(&[("action", "room-key"),
            ("op", "invite"), ("dir", "/w"), ("name", "lab"), ("member", "12"), ("enc-pub", "ab"),
            ("proposal-id", "i1"), ("request", "/h/r.json"), ("past", "true"), ("i-know", "true")]));
        assert_eq!(flags("invite-check", None, false, true)[1], ("op".to_owned(), "invite-check".to_owned()));
    }

    #[test]
    fn a_wrap_to_another_key_id_never_opens_even_for_the_right_room_and_member() {
        let e0 = RoomKey::generate(0).unwrap();
        let mut wrap = wrap_for(1, "11", &e0);
        assert!(wrap.open(ROOM, &dk(1)).is_ok());
        wrap.enc_id = ep(2).id();
        assert!(wrap.open(ROOM, &dk(1)).err().unwrap().contains("another encryption key"));
    }

    #[test]
    fn a_malformed_wrap_or_release_atom_in_the_keys_cell_is_an_error_not_skipped() {
        let view = json!({"cell":{"entries":[{"type":"atom","id":"11",
            "kind":{"type":"inlineObject","schema":wrap_schema()},"payload":"00"}]}});
        assert!(wraps_in_view(&view).is_err());
        let release = json!({"cell":{"entries":[{"type":"atom","id":release_atom_id(0, 0, 11),
            "kind":{"type":"inlineObject","schema":release_schema()},"payload":"00"}]}});
        assert!(releases_in_view(&release).is_err());
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
        assert_eq!(open_in_room(Some(&outsider), ROOM, "80", "1", &payload),
            json!("[sealed under epoch 0 — you do not hold that key]"));
        assert_eq!(open_in_room(None, ROOM, "80", "1", &payload),
            json!("[sealed under epoch 0 — you do not hold that key]"));
        let mut wrong = Keyring::default();
        wrong.insert(ROOM, &RoomKey::generate(0).unwrap());
        assert!(open_in_room(Some(&wrong), ROOM, "80", "1", &payload)["refused"].as_str().unwrap().contains("integrity"));
        assert!(!payload.windows(15).any(|w| w == b"meet at the lab"));
    }

    #[test]
    fn a_sealed_entry_is_bound_to_its_stream_and_position() {
        let e0 = RoomKey::generate(0).unwrap();
        let mut a = Keyring::default();
        a.insert(ROOM, &e0);
        let payload = seal_for_room(&e0, ROOM, "80", "4", b"hi").unwrap();
        let earlier = seal_for_room(&e0, ROOM, "80", "3", b"earlier").unwrap();
        assert!(open_in_room(Some(&a), ROOM, "80", "5", &payload).get("refused").is_some());
        assert!(open_in_room(Some(&a), ROOM, "81", "4", &payload).get("refused").is_some());
        assert!(open_in_room(Some(&a), ROOM, "80", "4", &earlier).get("refused").is_some(),
            "re-serving an earlier entry's ciphertext at this position does not open");
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
        let (e1, wraps1, left) = rotation(ROOM, &wraps0, 0, 1, &recipients(&[(11, 1), (13, 3)]), &current, Some(12)).unwrap();
        let wraps1: Vec<WrapAtom> = wraps1.into_iter().map(|(w, _)| w).collect();
        assert_eq!(e1.epoch(), 1);
        assert_eq!(left, vec![12]);
        assert_eq!(wraps1.iter().map(|w| w.member).collect::<Vec<_>>(), vec![11, 13]);
        assert_ne!(e1.bytes(), e0.bytes(), "the next epoch is drawn, not derived");
        let after = seal_for_room(&e1, ROOM, "81", "1", b"after the kick").unwrap();
        let all: Vec<WrapAtom> = wraps0.iter().chain(&wraps1).cloned().collect();
        let mut b_ring = Keyring::default();
        b_ring.insert(ROOM, &wraps0[1].open(ROOM, &dk(2)).unwrap());
        assert_eq!(open_in_room(Some(&b_ring), ROOM, "80", "1", &before)["text"], "before the kick");
        assert_eq!(open_in_room(Some(&b_ring), ROOM, "81", "1", &after),
            json!("[sealed under epoch 1 — you do not hold that key]"));
        for wrap in &wraps1 {
            assert!(wrap.open(ROOM, &dk(2)).is_err());
        }
        let mut c_ring = Keyring::default();
        for wrap in all.iter().filter(|w| w.member == 13) {
            c_ring.insert(ROOM, &wrap.open(ROOM, &dk(3)).unwrap());
        }
        assert_eq!(open_in_room(Some(&c_ring), ROOM, "81", "1", &after)["text"], "after the kick");
        assert_eq!(open_in_room(Some(&c_ring), ROOM, "80", "1", &before)["text"], "before the kick");
    }

    #[test]
    fn rotation_leaves_out_members_without_a_grant_and_needs_a_keyed_room() {
        let e0 = RoomKey::generate(0).unwrap();
        let wraps0 = vec![wrap_for(1, "11", &e0), wrap_for(2, "12", &e0)];
        let only_a: BTreeSet<u64> = [11].into_iter().collect();
        let (_, wraps1, left) = rotation(ROOM, &wraps0, 0, 1, &recipients(&[(11, 1)]), &only_a, None).unwrap();
        assert_eq!(wraps1.len(), 1);
        assert_eq!(left, vec![12]);
        assert!(rotation(ROOM, &[], 0, 1, &BTreeMap::new(), &only_a, None).unwrap().1.is_empty());
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
        let w = wrap_for(1, "11", &e0);
        let relabelled = WrapAtom::from_atom(&wrap_atom_id(1, 0, 11), &w.payload()).unwrap();
        assert!(relabelled.open(ROOM, &dk(1)).is_err());
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
                {"type":"eqSlots","left":"content/operations","right":"content/atom-creates"},
                {"type":"not","predicate":{"type":"eq","slot":"content/atoms/high-min","value":"0"}}]},
            {"type":"all","predicates":[
                {"type":"eq","slot":"content/operations","value":"1"},
                {"type":"eq","slot":"content/tombstones","value":"0"},
                {"type":"eq","slot":"content/atoms/high-max","value":"0"},
                {"type":"eqSlots","left":"content/atoms/low-min","right":"request/subject"},
                {"type":"eqSlots","left":"content/atoms/low-max","right":"request/subject"}]}]}));
        assert!(room_law().is_object());
    }

    #[test]
    fn first_invite_signed_descriptor_pins_its_key_but_needs_no_prior_wrap_or_record() {
        let signer = SigningKey::from_bytes(&[9; 32]);
        let encryption = ep(9);
        let payload = EncRecord::signed_payload(ROOM, KEYS, 9, 0, false, &encryption, &signer).unwrap();
        assert_eq!(payload.len(), SIGNED_RECORD_LEN);
        assert!(invitation_record(9, &hex(&encryption.id()), None).is_err());
        let declaration = json!({"type":"minidregg-signed-room-recipient-v3","member":"9",
            "room":ROOM,"keysCell":KEYS,"keyEpoch":"0","recordHex":hex(&payload)});
        assert_eq!(recipient_argument(&declaration.to_string()).unwrap(), hex(&payload));
        let mut wrong_metadata = declaration.clone(); wrong_metadata["room"] = json!("73");
        assert!(recipient_argument(&wrong_metadata.to_string()).is_err());
        let declared = invitation_record(9, &declaration.to_string(), None).unwrap();
        assert!(declared.authenticate(ROOM, KEYS, &signer.verifying_key().to_bytes()).is_ok());
        assert!(declared.authenticate(ROOM, KEYS, &SigningKey::from_bytes(&[8; 32]).verifying_key().to_bytes()).is_err());
        assert!(declared.authenticate(ROOM, "73", &signer.verifying_key().to_bytes()).is_err());
        assert!(invitation_record(9, &hex(&encryption.id()), Some(&declared)).is_ok(), "the selector is the 32-byte key id");
        assert!(invitation_record(9, &hex(&ep(8).id()), Some(&declared)).is_err(), "another key's id selects nothing");
        let mut substituted = payload.clone(); substituted[4] ^= 1;
        assert!(invitation_record(9, &hex(&substituted), Some(&declared)).is_err());
        // The pre-hybrid declaration type and an X25519-only key refuse by name.
        let old = json!({"type":"minidregg-signed-room-recipient-v2","member":"9",
            "room":ROOM,"keysCell":KEYS,"keyEpoch":"0","recordHex":hex(&payload)});
        assert!(recipient_argument(&old.to_string()).unwrap_err().contains("recipient-v3"));
        assert!(recipient_argument(&hex(encryption.x25519())).is_ok(), "32 bytes parse as a selector; it selects only an existing record");
    }

    #[test]
    fn release_commitment_binds_the_complete_wrap_and_its_exact_address() {
        let key = RoomKey::generate(1).unwrap();
        let (_, deliveries) = epoch(&key, [1; 32], &[(9, 9)], &founder_key());
        let signed = &deliveries[0].wrap;
        let release = &deliveries[0].release;
        let payload = signed.payload();
        assert_eq!(payload.len(), 32 + WRAPPED_LEN + 8 + 300);
        assert_eq!(payload.len(), 1532);
        assert_eq!(signed.payload_commitment().unwrap(), lineage_digest(&[&payload]));
        assert_eq!(release.commitment, signed.payload_commitment().unwrap());
        release.check(ROOM, KEYS, &FounderChain::single(pinned())).unwrap();
        release.names(signed).unwrap();
        assert!(wrap_for(9, "9", &key).payload_commitment().is_err(), "an unsigned wrap has no commitment");
        // The commitment covers the key id, BOTH ciphertext components, the box,
        // grant, certificate, signer and signature -- not merely the encrypted component.
        for offset in [0, 32, 32 + 32 + 500, 32 + WRAPPED_LEN - 1, 32 + WRAPPED_LEN, 1232, 1424, 1432, 1436, 1531] {
            let mut substituted = payload.clone(); substituted[offset] ^= 1;
            let altered = WrapAtom::from_atom(&wrap_atom_id(1, 0, 9), &substituted).unwrap();
            assert!(release.names(&altered).is_err(), "offset {offset}");
        }
        let mut wrong_address = signed.clone(); wrong_address.gen = 2;
        assert!(release.names(&wrong_address).is_err());
        let mut forged = release.clone(); forged.grant ^= 1;
        assert!(forged.check(ROOM, KEYS, &FounderChain::single(pinned())).is_err());
    }

    /// A node that applies content creates to one keys cell and records every request.
    struct FakeHost {
        entries: Vec<Value>,
        members: BTreeSet<u64>,
        submitted: Vec<(String, Value)>,
        after_bind: Option<Box<dyn FnMut(&mut Vec<Value>)>>,
    }

    impl ReleaseHost for FakeHost {
        fn turn(&mut self, proposal_id: &str, request: &Value) -> Result<()> {
            self.submitted.push((proposal_id.to_owned(), request.clone()));
            for action in request["targets"][0]["payload"]["actions"].as_array().unwrap() {
                if self.entries.iter().any(|entry| entry["id"] == action["atom"]) {
                    return Err("atom already exists".into());
                }
                self.entries.push(atom(action));
            }
            if proposal_id.ends_with("-bind") {
                if let Some(hook) = self.after_bind.as_mut() { hook(&mut self.entries); }
            }
            Ok(())
        }
        fn keys_view(&mut self) -> Result<Value> { Ok(json!({"cell":{"entries":self.entries.clone()}})) }
        fn members(&mut self) -> Result<BTreeSet<u64>> { Ok(self.members.clone()) }
    }

    fn scratch(label: &str) -> PathBuf {
        let root = std::env::temp_dir().join(format!("mini-private-room-{label}-{}-{}",
            std::process::id(), super::super::random_nonce().unwrap()));
        super::super::make_private_dir(&root).unwrap();
        root
    }

    fn wrapped_in(entries: &[Value]) -> Vec<WrapAtom> {
        wraps_in_view(&json!({"cell":{"entries":entries}})).unwrap()
    }

    /// Genesis released to the founder (13 is the second member).
    fn genesis_host(members: &[u64]) -> (FakeHost, RoomKey, EpochCertificate, BTreeMap<u64, EncRecord>) {
        let e0 = RoomKey::generate(0).unwrap();
        let (c0, d0) = epoch(&e0, [0; 32], &[(FOUNDER, 1)], &founder_key());
        let record = signed_record(3, 13, 0);
        let mut entries = vec![atom(&d0[0].release.action()), atom(&d0[0].wrap.action())];
        entries.push(record_atom(&record));
        let host = FakeHost { entries, members: members.iter().copied().collect(),
            submitted: Vec::new(), after_bind: None };
        (host, e0, c0, [(13, record)].into_iter().collect())
    }

    fn invite_spec(e0: &RoomKey, c0: &EpochCertificate, record: &EncRecord) -> ReleaseSpec {
        let wrap = WrapAtom::new(ROOM, "13", &record.enc, 0, 0, e0).unwrap()
            .sign(c0, FOUNDER, 0, &founder_key()).unwrap();
        ReleaseSpec { room: ROOM.into(), keys: KEYS.into(), keys_ref: "lab-keys".into(), purpose: "invite",
            head_before: Some(EpochHead { epoch: 0, identity: c0.identity() }), key: None,
            deliveries: vec![Delivery::new(wrap, record_digest(record).unwrap(), &founder()).unwrap()] }
    }

    #[test]
    fn release_binds_records_then_reads_back_then_discloses_the_wrap() {
        let root = scratch("release");
        let (mut host, e0, c0, records) = genesis_host(&[FOUNDER, 13]);
        let released = run_release(&root, &mut host, &pinned(), FOUNDER, ROOM, "inv-1", b"pass",
            || Ok(invite_spec(&e0, &c0, &records[&13]))).unwrap();
        assert_eq!(host.submitted.iter().map(|(id, _)| id.as_str()).collect::<Vec<_>>(), vec!["inv-1-bind", "inv-1-wraps"]);
        let bind = host.submitted[0].1.to_string();
        assert!(!bind.contains(&hex(&released.wraps[0].wrapped.to_bytes())), "turn 1 carries no ciphertext");
        let lineage = verify_lineage(ROOM, KEYS, &pinned(), &host.keys_view().unwrap(), None).unwrap();
        assert!(lineage.wraps.iter().any(|w| w.member == 13));
        assert_eq!(lineage.wraps.iter().find(|w| w.member == 13).unwrap()
            .open(ROOM, &dk(3)).unwrap().bytes(), e0.bytes());
        // Resuming a disclosed release re-sends nothing.
        run_release(&root, &mut host, &pinned(), FOUNDER, ROOM, "inv-1", b"pass", || unreachable!()).unwrap();
        assert_eq!(host.submitted.len(), 2);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn a_full_64_delivery_release_still_fits_the_retained_draft_bound() {
        // A hybrid delivery is ~3.7 KB of JSON (1532-byte wrap + 232-byte release, hex), so a
        // 64-delivery draft is ~240 KB: the retained manifest is read back through the
        // 256 KiB record bound. Stage the worst case and load it again.
        let root = scratch("full-release");
        let key = RoomKey::generate(1).unwrap();
        let members: Vec<(u64, u8)> = (0..64u64).map(|m| (100 + m, (100 + m) as u8)).collect();
        let (c1, deliveries) = epoch(&key, [1; 32], &members, &founder_key());
        let spec = ReleaseSpec { room: ROOM.into(), keys: KEYS.into(), keys_ref: "lab-keys".into(),
            purpose: "rotate", head_before: None, key: Some(key), deliveries };
        let operation = RetainedReleaseDraft::operation(ROOM, "full");
        RetainedReleaseDraft::stage(&root, &operation, "full", &spec, b"pass").unwrap();
        let draft = RetainedReleaseDraft::load(&root, &operation).unwrap().unwrap();
        assert_eq!(draft.deliveries().unwrap().len(), 64);
        let bytes = fs::metadata(draft.directory.join("draft.json")).unwrap().len();
        assert!(bytes < 256 * 1024, "the draft manifest is {bytes} bytes");
        assert_eq!(c1.epoch, 1);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn a_stale_recipient_never_receives_a_wrap_of_an_already_used_key() {
        let root = scratch("stale");
        let (mut host, e0, c0, records) = genesis_host(&[FOUNDER, 13]);
        // Between turn 1 and the readback, 13 publishes a new record (it rotated:
        // the bound key is stale -- an old device, a leaked secret).
        let rotated = signed_record(4, 13, 1);
        host.after_bind = Some(Box::new(move |entries: &mut Vec<Value>| {
            entries.retain(|entry| entry["id"] != "13");
            entries.push(record_atom(&rotated));
        }));
        let error = run_release(&root, &mut host, &pinned(), FOUNDER, ROOM, "inv-1", b"pass",
            || Ok(invite_spec(&e0, &c0, &records[&13]))).err().unwrap();
        assert!(error.contains("stale") && error.contains("dead"), "{error}");
        assert_eq!(host.submitted.len(), 1, "only the commitments left custody");
        assert!(wrapped_in(&host.entries).iter().all(|w| w.member != 13), "no wrap reached the stale key");
        // Dead forever: resuming the same release never discloses it.
        host.after_bind = None;
        let again = run_release(&root, &mut host, &pinned(), FOUNDER, ROOM, "inv-1", b"pass", || unreachable!());
        assert!(again.err().unwrap().contains("dead"));
        assert_eq!(host.submitted.len(), 1);
        // A member who lost its grant, or a moved head, also kills before disclosure.
        let (mut host, e0, c0, records) = genesis_host(&[FOUNDER]);
        assert!(run_release(&root, &mut host, &pinned(), FOUNDER, ROOM, "inv-2", b"pass",
            || Ok(invite_spec(&e0, &c0, &records[&13]))).err().unwrap().contains("no longer holds a grant"));
        assert!(wrapped_in(&host.entries).iter().all(|w| w.member != 13));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn a_refused_rotation_draft_is_dead_forever_and_its_epoch_is_never_selected() {
        let root = scratch("dead-draft");
        let (mut host, _, c0, records) = genesis_host(&[FOUNDER, 13]);
        let head0 = EpochHead { epoch: 0, identity: c0.identity() };
        let rotation_spec = |key: RoomKey, to: &[(u64, MemberPublic, [u8; 32])]| {
            let certificate = EpochCertificate::sign(ROOM, KEYS, &key, c0.identity(), FOUNDER, 0, &founder_key()).unwrap();
            let deliveries = to.iter().map(|(member, enc, record)| {
                let wrap = WrapAtom::new(ROOM, &member.to_string(), enc, 0, 0, &key).unwrap()
                    .sign(&certificate, FOUNDER, 0, &founder_key()).unwrap();
                Delivery::new(wrap, *record, &founder()).unwrap()
            }).collect();
            ReleaseSpec { room: ROOM.into(), keys: KEYS.into(), keys_ref: "lab-keys".into(), purpose: "rotate",
                head_before: Some(head0.clone()), key: Some(key), deliveries }
        };
        let me = (FOUNDER, ep(1), [0; 32]);
        let thirteen = (13, records[&13].enc.clone(), record_digest(&records[&13]).unwrap());
        // Draft Z: its first turn fails (UNKNOWN to the client). It stays a draft,
        // and its key never enters the sealing cache.
        struct Refusing;
        impl ReleaseHost for Refusing {
            fn turn(&mut self, _: &str, _: &Value) -> Result<()> { Err("node unreachable".into()) }
            fn keys_view(&mut self) -> Result<Value> { Err("unused".into()) }
            fn members(&mut self) -> Result<BTreeSet<u64>> { Err("unused".into()) }
        }
        let z_key = RoomKey::generate(1).unwrap();
        assert!(run_release(&root, &mut Refusing, &pinned(), FOUNDER, ROOM, "rot-z", b"pass",
            || Ok(rotation_spec(z_key, &[me.clone()]))).is_err());
        let z = RetainedReleaseDraft::load(&root, &RetainedReleaseDraft::operation(ROOM, "rot-z")).unwrap().unwrap();
        assert_eq!(z.state().unwrap(), ReleaseState::Drafted);
        assert!(load_ring(&root, b"pass").unwrap().get(ROOM, 1).is_none(), "a draft key never enters the sealing cache");
        // Draft A at epoch 1 kills Z before it exists; its records apply, then
        // 13 rotates before the readback: A is refused and dead, epoch 1 burned.
        let rotated = signed_record(4, 13, 1);
        host.after_bind = Some(Box::new(move |entries: &mut Vec<Value>| {
            entries.retain(|entry| entry["id"] != "13");
            entries.push(record_atom(&rotated));
        }));
        let a_key = RoomKey::generate(1).unwrap();
        assert!(run_release(&root, &mut host, &pinned(), FOUNDER, ROOM, "rot-a", b"pass",
            || Ok(rotation_spec(a_key, &[me.clone(), thirteen]))).err().unwrap().contains("dead"));
        assert!(matches!(z.state().unwrap(), ReleaseState::Dead(_)), "one live draft per room");
        assert!(run_release(&root, &mut host, &pinned(), FOUNDER, ROOM, "rot-z", b"pass", || unreachable!())
            .err().unwrap().contains("dead"), "a dead draft is never resumed");
        let a = RetainedReleaseDraft::load(&root, &RetainedReleaseDraft::operation(ROOM, "rot-a")).unwrap().unwrap();
        assert!(matches!(a.state().unwrap(), ReleaseState::Dead(_)));
        assert!(wrapped_in(&host.entries).iter().all(|w| w.epoch == 0), "nothing of A was disclosed");
        assert!(load_ring(&root, b"pass").unwrap().get(ROOM, 1).is_none());
        // The next rotation skips the burned epoch.
        host.after_bind = None;
        let lineage = verify_lineage(ROOM, KEYS, &pinned(), &host.keys_view().unwrap(), None).unwrap();
        assert_eq!(lineage.next_epoch().unwrap(), 2, "a burned epoch is never reused");
        let b_key = RoomKey::generate(2).unwrap();
        let b_bytes = b_key.bytes();
        let b = run_release(&root, &mut host, &pinned(), FOUNDER, ROOM, "rot-b", b"pass",
            || Ok(rotation_spec(b_key, &[me.clone()]))).unwrap();
        assert_eq!(b.key.unwrap().bytes(), b_bytes);
        let head = verify_lineage(ROOM, KEYS, &pinned(), &host.keys_view().unwrap(), None).unwrap().head.unwrap();
        assert_eq!(head.epoch, 2);
        // Even if A's founder-signed wraps surfaced later, they break the chain
        // for every reader: the dead epoch is never selectable.
        let mut with_a = host.entries.clone();
        for delivery in a.deliveries().unwrap() { with_a.push(atom(&delivery.wrap.action())); }
        assert!(verify_lineage(ROOM, KEYS, &pinned(), &json!({"cell":{"entries":with_a}}), None).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn founder_and_member_pins_refuse_silent_replacement() {
        let root = scratch("pins");
        let key = hex(&pinned());
        pin_founder(&root, ROOM, KEYS, &key, false).unwrap();
        pin_founder(&root, ROOM, KEYS, &key, false).unwrap();
        assert_eq!(founder_pin(&root, ROOM, KEYS).unwrap(), pinned());
        let other = hex(&SigningKey::from_bytes(&[8; 32]).verifying_key().to_bytes());
        assert!(pin_founder(&root, ROOM, KEYS, &other, false).unwrap_err().contains("--replace true"));
        assert!(founder_pin(&root, ROOM, "73").is_err(), "a pin names its keys cell");
        assert!(founder_pin(&root, "70", KEYS).unwrap_err().contains("no pinned founder key"));
        pin_founder(&root, ROOM, KEYS, &other, true).unwrap();
        assert_ne!(founder_pin(&root, ROOM, KEYS).unwrap(), pinned());
        let nine = SigningKey::from_bytes(&[9; 32]).verifying_key().to_bytes();
        pin_member(&root, ROOM, KEYS, 9, &nine, false).unwrap();
        assert!(pin_member(&root, ROOM, KEYS, 9, &pinned(), false).is_err());
        assert_eq!(member_pins(&root, ROOM, KEYS).unwrap().1[&9], nine);
        assert_eq!(fingerprint(&nine), fingerprint(&nine));
        assert_ne!(fingerprint(&nine), fingerprint(&pinned()));
        fs::remove_dir_all(root).unwrap();
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
