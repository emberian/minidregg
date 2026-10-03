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
//! founder (reference `NAME-keys`), partitioned by atom id
//! (`Kernel/PrivateRoomKeys.lean`):
//!   WRAP of epoch e for member m, addressed to m's key of generation g:
//!     atom id   = (e + 1) * 2^96 + g * 2^64 + m
//!     kind      = inlineObject(schema of "DREGG/PRIVATE-AUTH-WRAP/v2")
//!     payload   = X25519 public key (32) ‖ wrap (104) ‖ keys grant (8)
//!                 ‖ signed epoch certificate (192) ‖ signed delivery (108).
//!   m's ENCRYPTION-KEY RECORD (FIX-IDENTITY):
//!     atom id   = m
//!     kind      = inlineObject(schema of "DREGG/PRIVATE-ENC-KEY/v2")
//!     payload   = epoch (4) ‖ X25519 key (32) ‖ room (8) ‖ keys cell (8)
//!                 ‖ member signing key (32) ‖ member signature (64).
//! The signature binds the suite, room, keys cell, member, epoch and both keys.
//! Recipient selection additionally requires independently authenticated current
//! signing authority; the record's own public key is never a trust anchor.
//! Legacy unsigned v1 records can be edited but cannot authorize a new wrap.
//! The generation g is the key epoch of the record a wrap was addressed to (0:
//! a key given at invite time, before any record). A second wrap to the SAME key
//! is the same id, refused by the content controller; a RE-WRAP to a member's
//! newer key is a new id. Its law (`law.keys.json`) lets only the founder write
//! wraps, only by creating atoms (no edit, no tombstone), so the room's EPOCH --
//! source-authenticated latest epoch and retained client lineage never go
//! backwards; it lets each subject
//! write only its own record (one create or edit at its own number). Every
//! member may read every wrap and record (per-address observation is not on
//! this tree, and a wrap opens for one X25519 secret only). Whoever rotates
//! wraps each kept member only to its authenticated current signed RECORD.
//! An absent current-authority proof refuses disclosure; an old wrap is no fallback.
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
//! SEALING. `seal_for_room` seals under the room's CURRENT epoch only: a client
//! that does not hold it (a kicked member, a member never wrapped) refuses to
//! seal. The epoch is in the clear in every envelope so a reader picks its key;
//! a reader without that epoch's key is shown `private::sealed_marker` and never
//! a guess. A stream entry is bound to (room, stream cell, sequence) -- the
//! position the plan read -- so an envelope cannot be moved to another stream
//! or position unnoticed.
//!
//! AUTHORITY BOUNDARY: signed recipient/epoch/delivery checks alone do not
//! authorize room-key release. The registered current-source latest-head and
//! guarded release Applied producers are required; missing producers refuse.
//! A valid old genesis prefix is insufficient on first contact.
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
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use sha3::{digest::{core_api::CoreWrapper, ExtendableOutput, Update, XofReader}, CShake256Core};
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
    private::schema_decimal_of(b"DREGG/PRIVATE-AUTH-WRAP/v2")
}

const EPOCH_FRAME: &[u8] = b"DREGG/PRIVATE-ROOM-EPOCH/v1";
const AUTH_WRAP_FRAME: &[u8] = b"DREGG/PRIVATE-AUTH-WRAP/v2";

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
/// authorized members later receive a wrap. Rotation authority is checked by
/// the rooted source producer; a self-signed certificate is not authority.
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
        if key.epoch() > MAX_EPOCH || (key.epoch() == 0) != (parent == [0; 32]) {
            return Err("epoch genesis/predecessor shape is invalid".into());
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
        if self.signer_public != *actual_public { return Err("epoch signer differs from rooted authority".into()); }
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

/// Consistency of already source-authenticated certificates. This checks the
/// entire supplied prefix or an extension of a retained head; it is not the
/// first-contact authority proof.
fn check_epoch_chain(wraps: &[WrapAtom], retained: Option<&EpochHead>) -> Result<EpochHead> {
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
        let previous = head.as_ref().or(retained);
        match previous {
            None if certificate.epoch == 0 && certificate.parent == [0; 32] => {},
            Some(previous) if certificate.epoch == previous.epoch
                && certificate.identity() == previous.identity => {},
            Some(previous) if previous.epoch.checked_add(1) == Some(certificate.epoch)
                && certificate.parent == previous.identity => {},
            // A complete authenticated prefix can start from genesis even when
            // this client has already retained a later head.
            _ if head.is_none() && certificate.epoch == 0 && certificate.parent == [0; 32] => {},
            _ => return Err("room epoch chain has a missing or different predecessor".into()),
        }
        let next = EpochHead { epoch: certificate.epoch, identity: certificate.identity() };
        if retained == Some(&next) { includes_retained = true; }
        // An extension whose first parent is the retained head also anchors it.
        if head.is_none() && retained.is_some_and(|p| p.epoch.checked_add(1) == Some(next.epoch)
            && p.identity == certificate.parent) { includes_retained = true; }
        head = Some(next);
    }
    let head = head.ok_or("no authenticated room epoch certificate")?;
    advance_head(retained, &head)?;
    if !includes_retained { return Err("served lineage omits or replaces the retained room epoch".into()); }
    Ok(head)
}

/// First contact requires the latest head independently selected from the
/// authenticated source, even if the served certificates form a valid old
/// prefix. None is allowed only for an authenticated newly empty keys cell.
fn check_source_head(wraps: &[WrapAtom], retained: Option<&EpochHead>,
    latest: Option<&EpochHead>) -> Result<Option<EpochHead>> {
    match latest {
        None if wraps.is_empty() && retained.is_none() => Ok(None),
        None => Err("source has no epoch but served or retained lineage is nonempty".into()),
        Some(latest) => {
            let candidate = check_epoch_chain(wraps, retained)?;
            if &candidate != latest {
                return Err("served epoch prefix differs from the independently authenticated latest head".into());
            }
            Ok(Some(candidate))
        }
    }
}

/// The closed source query validates admitted historical issuance and exact
/// current observed wraps. Its latest certificate may already be Applied while
/// delivery is pending. Whole-source ancestry belongs to that private token;
/// the client need not retransmit an unbounded genesis chain on every sync.
fn check_source_latest(room: &str, keys: &str, wraps: &[WrapAtom],
    retained: Option<&EpochHead>, certificate: Option<&EpochCertificate>) -> Result<Option<EpochHead>> {
    let Some(certificate) = certificate else {
        return check_source_head(wraps, retained, None);
    };
    let room = subject_number(room)?;
    let keys = subject_number(keys)?;
    if certificate.room != room || certificate.keys != keys || certificate.epoch > MAX_EPOCH {
        return Err("source latest epoch certificate belongs to another room/keys context or exceeds suite bounds".into());
    }
    let head = EpochHead { epoch: certificate.epoch, identity: certificate.identity() };
    advance_head(retained, &head)?;
    for wrap in wraps {
        let supplied = &wrap.attestation.as_ref().ok_or("source served an unsigned epoch delivery")?.certificate;
        if supplied.room != room || supplied.keys != keys || wrap.epoch != supplied.epoch
            || supplied.epoch > head.epoch || (supplied.epoch == head.epoch && supplied != certificate) {
            return Err("served delivery differs from independently selected source lineage".into());
        }
    }
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

/// A local head preserves authority evidence across key-cache erasure. The
/// source-authenticated batch is required before this durable CAS is reached.
fn retain_epoch_head(root: &Path, room: &str, keys: &str, prior: Option<&Value>, head: &EpochHead,
    source_evidence: &Value) -> Result<()> {
    if prior.is_some_and(|value| value["epoch"] == head.epoch.to_string()
        && value["identity"] == hex(&head.identity)) { return Ok(()); }
    if !root.join("private").exists() { make_private_dir(&root.join("private"))?; }
    super::publish_retained_json(&epoch_head_path(root, room)?,
        &json!({"type":"minidregg-authenticated-room-head-v1", "room":room,
            "keys":keys,"epoch":head.epoch.to_string(),"identity":hex(&head.identity),
            "sourceEvidence":source_evidence}), prior)
}

/// Filled only by the pinned current-source verifier, which proves signer
/// standing, room/keys law, exact current observed wraps and admitted epoch
/// issuance/ancestry at the custody point. Parsed metadata cannot construct it.
/// Signature checking or a local high-water mark cannot construct this value.
struct AuthenticatedWraps {
    wraps: Vec<WrapAtom>,
    latest_certificate: Option<EpochCertificate>,
    source_evidence: Value,
}

fn authenticate_current_wraps(_root: &Path, _workspace: &Value, _room: &str,
    _keys: &str, _signed_observation: &Path, _wraps: Vec<WrapAtom>) -> Result<AuthenticatedWraps> {
    Err("authenticated room epoch/rotation lineage requires the rooted current-source verifier; operator-served wraps and self-signed founder keys are not authority".into())
}

/// A member's encryption-key record in the keys cell.
pub(crate) const RECORD_FRAME: &[u8] = b"DREGG/PRIVATE-ENC-KEY/v1";
const SIGNED_RECORD_FRAME: &[u8] = b"DREGG/PRIVATE-ENC-KEY/v2";
const SIGNED_RECORD_LEN: usize = 148;

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
    pub(crate) enc_pub: [u8; 32],
    pub(crate) wrapped: Wrapped,
    /// The member's keys-cell grant (0: none).
    pub(crate) grant: u64,
    attestation: Option<WrapAttestation>,
}

const WRAP_PAYLOAD_LEN: usize = 32 + WRAPPED_LEN + 8;

/// The largest room-key epoch: `(epoch + 1) * 2^96` stays below 2^127.
pub(crate) const MAX_EPOCH: u32 = (1 << 31) - 1;

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
    pub(crate) enc_pub: [u8; 32],
    pub(crate) atom: Value,
    attestation: Option<KeyAttestation>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct KeyAttestation {
    room: u64,
    keys: u64,
    signing_public: [u8; 32],
    signature: [u8; 64],
}

/// A direct cryptographic check is distinct from current source authority.
/// Its embedded signing key is never accepted as its own trust anchor.
struct SignatureCheckedRecord(EncRecord);

enum RecipientAuthority {
    Current(super::receipt_continuity::VerifiedCurrentRecipient),
    #[cfg(test)]
    TrustedFixture,
}

pub(crate) struct AuthenticatedRecord {
    record: EncRecord,
    authority: RecipientAuthority,
}

fn record_statement(room: u64, keys: u64, member: u64, epoch: u32,
    signing_public: &[u8; 32], encryption_public: &[u8; 32]) -> Vec<u8> {
    [SIGNED_RECORD_FRAME, &[1u8], &room.to_be_bytes(), &keys.to_be_bytes(),
        &member.to_be_bytes(), &epoch.to_be_bytes(), signing_public, encryption_public].concat()
}

impl EncRecord {
    fn signed_payload(room: &str, keys: &str, member: u64, key_epoch: u32,
        enc_pub: &[u8; 32], signer: &SigningKey) -> Result<Vec<u8>> {
        let room = subject_number(room)?;
        let keys = subject_number(keys)?;
        let public = signer.verifying_key().to_bytes();
        let signature = signer.sign(&record_statement(room, keys, member, key_epoch, &public, enc_pub));
        Ok([&key_epoch.to_be_bytes()[..], enc_pub, &room.to_be_bytes(),
            &keys.to_be_bytes(), &public, &signature.to_bytes()].concat())
    }

    fn canonical_signed_payload(&self) -> Result<Vec<u8>> {
        let attestation = self.attestation.as_ref().ok_or("unsigned recipient record has no signed payload")?;
        Ok([&self.key_epoch.to_be_bytes()[..], &self.enc_pub, &attestation.room.to_be_bytes(),
            &attestation.keys.to_be_bytes(), &attestation.signing_public, &attestation.signature].concat())
    }

    pub(crate) fn from_atom(id: &str, payload: &[u8], atom: &Value) -> Result<Self> {
        let member = subject_number(id).map_err(|_| format!("record atom id {id} is not a subject number"))?;
        if payload.len() != 36 && payload.len() != SIGNED_RECORD_LEN {
            return Err(format!("record {id} has an invalid encryption-key record length"));
        }
        Ok(Self {
            member,
            key_epoch: u32::from_be_bytes(payload[..4].try_into().expect("4 bytes")),
            enc_pub: payload[4..36].try_into().expect("32 bytes"),
            atom: atom.clone(),
            attestation: if payload.len() == SIGNED_RECORD_LEN {
                Some(KeyAttestation {
                    room: u64::from_be_bytes(payload[36..44].try_into().expect("8 bytes")),
                    keys: u64::from_be_bytes(payload[44..52].try_into().expect("8 bytes")),
                    signing_public: payload[52..84].try_into().expect("32 bytes"),
                    signature: payload[84..148].try_into().expect("64 bytes"),
                })
            } else { None },
        })
    }

    fn authenticate(&self, room: &str, keys: &str, current_public: &[u8; 32],
        current_epoch: u32) -> Result<SignatureCheckedRecord> {
        let attestation = self.attestation.as_ref()
            .ok_or("unsigned legacy recipient record: member must publish a signed room key record")?;
        if attestation.room != subject_number(room)? || attestation.keys != subject_number(keys)?
            || attestation.signing_public != *current_public || self.key_epoch != current_epoch {
            return Err("recipient record differs from its room, keys cell or authenticated current member authority".into());
        }
        VerifyingKey::from_bytes(current_public).map_err(|_| "invalid authenticated signing key")?
            .verify_strict(&record_statement(attestation.room, attestation.keys, self.member,
                self.key_epoch, current_public, &self.enc_pub), &Signature::from_bytes(&attestation.signature))
            .map_err(|_| "recipient encryption key signature does not verify under current member authority")?;
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
    pub(crate) fn new(room: &str, member: &str, enc_pub: &PublicKey, gen: u32, grant: u64, key: &RoomKey) -> Result<Self> {
        if key.epoch() > MAX_EPOCH {
            return Err("room-key epoch exhausted".into());
        }
        Ok(Self {
            epoch: key.epoch(),
            gen,
            member: subject_number(member)?,
            enc_pub: *enc_pub.as_bytes(),
            wrapped: wrap_room_key(room, member, enc_pub, key)?,
            grant,
            attestation: None,
        })
    }

    fn unsigned_payload(&self) -> Vec<u8> {
        [&self.enc_pub[..], &self.wrapped.to_bytes(), &self.grant.to_be_bytes()].concat()
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
            return Err("delivery commitment requires the complete signed wrap444".into());
        }
        Ok(lineage_digest(&[&payload]))
    }

    /// Draft input for the canonical source author. This does not establish
    /// audience entitlement or an Applied permit; the same-Prepared source
    /// validator independently checks the capability and current record.
    fn delivery_declaration(&self, authenticated: &AuthenticatedRecord,
        room_capability: u64) -> Result<Value> {
        let record = &authenticated.record;
        let attestation = self.attestation.as_ref().ok_or("delivery must be signed")?;
        let recipient = record.attestation.as_ref().ok_or("recipient record must be signed")?;
        if self.member != record.member || self.gen != record.key_epoch
            || self.enc_pub != record.enc_pub || self.epoch != attestation.certificate.epoch
            || recipient.room != attestation.certificate.room
            || recipient.keys != attestation.certificate.keys {
            return Err("delivery differs from its authenticated recipient or certificate scope".into());
        }
        Ok(json!({"member":self.member.to_string(),
            "recordHex":hex(&record.canonical_signed_payload()?),
            "roomCapability":room_capability.to_string(),"entitlementEnvelopeHex":"",
            "ciphertextCommitmentHex":hex(&self.payload_commitment()?),
            "atom":wrap_atom_id(self.epoch, self.gen, self.member)}))
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

    /// Signature checking alone does not authorize an epoch or a delivery.
    /// Both keys and permissions must come from the protected source verifier.
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
            enc_pub: payload[..32].try_into().expect("32 bytes"),
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

    pub(crate) fn open(&self, room: &str, secret: &StaticSecret) -> Result<RoomKey> {
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
    walk(view, &wrap_schema(), &mut found);
    walk(view, &private::schema_decimal_of(WRAP_FRAME), &mut found);
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
    // Legacy records remain editable, but they are never recipient authority.
    walk(view, &private::schema_decimal_of(RECORD_FRAME), &mut found);
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

/// The room's epoch: the largest epoch any wrap names.
pub(crate) fn current_epoch(wraps: &[WrapAtom]) -> Option<u32> {
    wraps.iter().map(|w| w.epoch).max()
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

/// Select only authenticated recipients. Neither an unsigned record nor the
/// key beside an operator-served old wrap can authorize disclosure of a key.
pub(crate) fn wrap_target(
    records: &BTreeMap<u64, AuthenticatedRecord>,
    member: u64,
) -> Result<(u32, [u8; 32])> {
    let authenticated = records.get(&member)
        .ok_or_else(|| format!("member {member} lacks an authenticated current recipient-key record"))?;
    let record = &authenticated.record;
    match &authenticated.authority {
        RecipientAuthority::Current(authority) => {
            let attestation = record.attestation.as_ref().ok_or("signed recipient attestation missing")?;
            if attestation.signing_public != authority.signing_public() || record.key_epoch != authority.epoch() {
                return Err("recipient record differs from retained current source selection".into());
            }
        }
        #[cfg(test)]
        RecipientAuthority::TrustedFixture => {},
    }
    Ok((record.key_epoch, record.enc_pub))
}

/// Current member authority must come from an independently rooted authority
/// proof. The current Host key-status response is unsigned; neither it nor an
/// embedded record key can supply that proof. The locked custody reader checks
/// the current protected source and returns a private authority token; this is
/// recipient authentication, not permission to publish a room key.
fn authenticate_current_recipient(root: &Path, workspace: &Value, room: &str,
    keys: &str, record: &EncRecord) -> Result<AuthenticatedRecord> {
    let authority = super::receipt_continuity::current_recipient_source(root, workspace, room,
        keys, &record.member.to_string(), &record.canonical_signed_payload()?)?;
    let checked = record.authenticate(room, keys, &authority.signing_public(), authority.epoch())?;
    Ok(AuthenticatedRecord { record: checked.0, authority: RecipientAuthority::Current(authority) })
}

/// The wraps a rotation writes: a fresh key at `epoch + 1` for every member at
/// `epoch` who is still `current` and is not `dropped`, each to its RECORDED key
/// (`wrap_target`). Returns the new key, the wraps, and the members left out.
pub(crate) fn rotation(
    room: &str,
    wraps: &[WrapAtom],
    records: &BTreeMap<u64, AuthenticatedRecord>,
    current: &BTreeSet<u64>,
    dropped: Option<u64>,
) -> Result<(RoomKey, Vec<WrapAtom>, Vec<u64>)> {
    let epoch = current_epoch(wraps).ok_or("the room has no keys yet")?;
    let next = RoomKey::generate(epoch.checked_add(1).ok_or("room-key epoch exhausted")?)?;
    let mut out = Vec::new();
    let mut left = Vec::new();
    for (member, _newest) in members_at(wraps, epoch) {
        if Some(member) == dropped || !current.contains(&member) {
            left.push(member);
            continue;
        }
        let (gen, enc_pub) = wrap_target(records, member)?;
        let grant = grant_of(wraps, member);
        out.push(WrapAtom::new(room, &member.to_string(), &PublicKey::from(enc_pub), gen, grant, &next)?);
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

/// Every X25519 secret this workspace opens with: the current one, then every
/// past one its keyring kept across signing-key rotations.
fn own_secrets(workspace: &Value) -> Result<Vec<StaticSecret>> {
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
    pub(crate) records: BTreeMap<u64, EncRecord>,
    pub(crate) ring: Keyring,
    pub(crate) learned: Vec<u32>,
    head: Option<EpochHead>,
}

impl Synced {
    pub(crate) fn epoch(&self) -> Option<u32> {
        self.head.as_ref().map(|head| head.epoch)
    }
}

/// Read the keys cell with this workspace's room grant and store every epoch
/// wrapped for this subject that the cache does not hold (and has not forgotten).
pub(crate) fn sync(root: &Path, workspace: &Value, room_name: &str) -> Result<Synced> {
    let passphrase = passphrase()?;
    let (room_ref, room, keys) = private_room(root, room_name)?;
    let (view, _, signed_observation) = signed_view(root, workspace, &keys_view_ref(&room_ref, &keys)?, "resource")?;
    let AuthenticatedWraps { wraps, latest_certificate, source_evidence } = authenticate_current_wraps(root, workspace, &room, &keys, &signed_observation, wraps_in_view(&view)?)?;
    let retained = read_epoch_head(root, &room, &keys)?;
    let head = check_source_latest(&room, &keys, &wraps, retained.as_ref().map(|(_, head)| head), latest_certificate.as_ref())?;
    let records = records_in_view(&view);
    let mut ring = load_ring(root, &passphrase)?;
    if head.as_ref().is_some_and(|head| ring.latest(&room).is_some_and(|key| key.epoch() > head.epoch)) {
        return Err("served room lineage is older than this client's retained key epochs".into());
    }
    // Preserve the authenticated epoch even if the latest wrap cannot open or
    // the client later forgets its decryption keys. Never fall back to an older
    // epoch on either condition.
    if let Some(head) = &head {
        retain_epoch_head(root, &room, &keys, retained.as_ref().map(|(value, _)| value), head, &source_evidence)?;
    }
    let me = subject_number(member(workspace, "subject")?)?;
    let secrets = own_secrets(workspace)?;
    let mut learned = Vec::new();
    let mut unopened = BTreeSet::new();
    // A member may hold several wraps at one epoch (re-wraps after it rotated):
    // the newest generation first, with whichever keyring secret it names.
    let mut mine: Vec<&WrapAtom> = wraps.iter().filter(|w| w.member == me).collect();
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
        let Some(secret) = secrets.iter().find(|s| PublicKey::from(*s).as_bytes() == &wrap.enc_pub) else {
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
    Ok(Synced { room, wraps, records, ring, learned, head })
}

/// The key a writer seals under: the room's current epoch, which this client
/// must hold. A member who was never wrapped at it, or was kicked, refuses here.
pub(crate) fn current_key(root: &Path, workspace: &Value, room_name: &str) -> Result<(String, RoomKey)> {
    let synced = sync(root, workspace, room_name)?;
    let head = synced.head.as_ref().ok_or("room has no source-applied epoch: nothing is sealed")?;
    let certificate = synced.wraps.iter().find(|wrap| wrap.epoch == head.epoch)
        .and_then(|wrap| wrap.attestation.as_ref()).map(|attestation| &attestation.certificate)
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

fn write_wraps(root: &Path, workspace: &Value, keys_ref: &str, proposal_id: &str, wraps: &[WrapAtom]) -> Result<()> {
    if wraps.is_empty() || wraps.len() > 64 {
        return Err(format!("one keys write carries 1..64 wraps, not {}", wraps.len()));
    }
    if wraps.iter().any(|wrap| wrap.attestation.is_none()) {
        return Err("room key release requires an authorized signed epoch certificate and signed delivery; unsigned wraps are not published".into());
    }
    // A ciphertext for an already used epoch is itself a release. Verification
    // after sending it cannot undo disclosure to a substituted recipient. The
    // shared guarded release producer must authorize its digest first.
    authorize_wrap_publication(root, workspace, keys_ref, proposal_id, wraps)?;
    let actions: Vec<Value> = wraps.iter().map(WrapAtom::action).collect();
    turn(root, workspace, proposal_id, &json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":[{"name":keys_ref,"payload":{"type":"content","actions":actions}}]}))
}

/// Custody of the original release operation, not permission to disclose it.
/// The draft key is encrypted separately from the ordinary sealing cache and
/// never installed there merely because a draft exists.
struct RetainedReleaseDraft {
    directory: PathBuf,
    manifest: Value,
}

impl RetainedReleaseDraft {
    fn directory(root: &Path, operation: &[u8; 32]) -> PathBuf {
        root.join("private").join("room-releases").join(hex(operation))
    }

    fn load(root: &Path, operation: &[u8; 32]) -> Result<Option<Self>> {
        let directory = Self::directory(root, operation);
        if !directory.exists() { return Ok(None); }
        super::private_dir(&directory)?;
        let manifest_path = directory.join("draft.json");
        if !manifest_path.exists() {
            return Err("room release draft is incomplete; recover its retained key before creating another operation".into());
        }
        let manifest = bounded_json(&manifest_path)?;
        if member(&manifest, "type")? != "minidregg-retained-room-release-v1"
            || member(&manifest, "operationHex")? != hex(operation) {
            return Err("retained room release operation differs".into());
        }
        let certificate = EpochCertificate::from_bytes(&crate::decode_hex(member(&manifest, "certificateHex")?)?)?;
        if certificate.room.to_string() != member(&manifest, "room")?
            || certificate.keys.to_string() != member(&manifest, "keysCell")? {
            return Err("retained release certificate scope differs".into());
        }
        let encrypted = fs::read(directory.join("draft-key.cache")).map_err(|error| error.to_string())?;
        if hex(&lineage_digest(&[b"DREGG/PRIVATE-ROOM-DRAFT-CACHE/v1", &encrypted]))
            != member(&manifest, "encryptedKeyCommitmentHex")? {
            return Err("retained release encrypted key differs; nothing is disclosed".into());
        }
        Ok(Some(Self { directory, manifest }))
    }

    fn key(&self, passphrase: &[u8]) -> Result<RoomKey> {
        let certificate = EpochCertificate::from_bytes(&crate::decode_hex(member(&self.manifest, "certificateHex")?)?)?;
        let room = member(&self.manifest, "room")?;
        let ring = private::load_cache(&self.directory.join("draft-key.cache"), passphrase)?;
        if ring.epochs(room) != vec![certificate.epoch] {
            return Err("retained release cache must contain exactly its committed epoch".into());
        }
        let key = ring.get(room, certificate.epoch).ok_or("retained release key absent")?;
        if certificate.key_commitment != EpochCertificate::commitment(certificate.room, certificate.keys, &key) {
            return Err("retained draft key differs from the signed epoch commitment".into());
        }
        Ok(key)
    }

    fn stage(root: &Path, operation: &[u8; 32], request_bytes: &[u8],
        certificate: &EpochCertificate, wraps: &[WrapAtom], key: &RoomKey,
        passphrase: &[u8]) -> Result<Self> {
        if request_bytes.is_empty() || request_bytes.len() > 64 * 1024
            || wraps.is_empty() || wraps.len() > 64
            || certificate.epoch > MAX_EPOCH
            || key.epoch() != certificate.epoch
            || certificate.key_commitment != EpochCertificate::commitment(certificate.room, certificate.keys, key) {
            return Err("invalid retained room release draft".into());
        }
        let mut addresses = BTreeSet::new();
        for wrap in wraps {
            let attestation = wrap.attestation.as_ref().ok_or("release draft requires signed delivery bytes")?;
            wrap.payload_commitment()?;
            if attestation.certificate != *certificate || wrap.epoch != certificate.epoch
                || !addresses.insert(wrap_atom_id(wrap.epoch, wrap.gen, wrap.member)) {
                return Err("retained deliveries differ from their one epoch certificate or repeat an address".into());
            }
        }
        let private = root.join("private");
        if !private.exists() { make_private_dir(&private)?; }
        let parent = private.join("room-releases");
        if !parent.exists() { make_private_dir(&parent)?; }
        let directory = Self::directory(root, operation);
        // The per-operation lock survives a missing/incomplete draft. Concurrent
        // creators cannot replace its key or canonical request.
        let _lock = crate::transport::service_lock(&parent.join(format!("{}.lock", hex(operation))))?;
        let semantic = json!({"type":"minidregg-retained-room-release-v1",
            "operationHex":hex(operation),"room":certificate.room.to_string(),
            "keysCell":certificate.keys.to_string(),"certificateHex":hex(&certificate.bytes()),
            "requestHex":hex(request_bytes),"deliveries":wraps.iter().map(WrapAtom::action).collect::<Vec<_>>()});
        if serde_json::to_vec_pretty(&semantic).map_err(|error| error.to_string())?.len() > 240 * 1024 {
            return Err("room release draft exceeds the bounded custody record capacity".into());
        }
        if let Some(existing) = Self::load(root, operation)? {
            let mut original = existing.manifest.clone();
            original.as_object_mut().ok_or("release draft is not an object")?.remove("encryptedKeyCommitmentHex");
            if original != semantic || existing.key(passphrase)?.secret_bytes() != key.secret_bytes() {
                return Err("room release operation already retains a different request, ciphertext or key; recover the original".into());
            }
            return Ok(existing);
        }
        make_private_dir(&directory)?;
        let mut draft_ring = Keyring::default();
        draft_ring.insert(&certificate.room.to_string(), key);
        private::save_cache(&directory.join("draft-key.cache"), passphrase, &draft_ring)?;
        // save_cache syncs its staged file; the draft directory is synced before
        // the immutable manifest makes its encrypted sidecar reachable.
        fs::File::open(&directory).and_then(|file| file.sync_all()).map_err(|error| error.to_string())?;
        let encrypted = fs::read(directory.join("draft-key.cache")).map_err(|error| error.to_string())?;
        let mut manifest = semantic;
        manifest["encryptedKeyCommitmentHex"] = json!(hex(&lineage_digest(&[b"DREGG/PRIVATE-ROOM-DRAFT-CACHE/v1", &encrypted])));
        super::publish_retained_json(&directory.join("draft.json"), &manifest, None)?;
        Self::load(root, operation)?.ok_or_else(|| "retained room release draft disappeared".into())
    }

    /// Bind a phase's already authored intent exactly once. A pending native
    /// call recovers this intent and its original attempt; it never reauthors
    /// random nonces or different ciphertexts. This method grants no Applied
    /// release permission and is not used to transmit the publication phase.
    fn bind_release_intent(&self, intent: &Value, attempt: &str) -> Result<()> {
        validate_name(attempt)?;
        let command = &intent["purpose"]["draft"]["command"];
        if intent["purpose"]["draft"]["type"] != "invoke"
            || command["family"]["route"] != "roomRelease"
            || command["family"]["contextBytes"] != self.manifest["requestHex"] {
            return Err("release intent must bind the exact retained roomRelease statement".into());
        }
        let row = json!({"type":"minidregg-retained-room-release-phase-v1",
            "operationHex":self.manifest["operationHex"],"attempt":attempt,"intent":intent});
        super::publish_retained_json(&self.directory.join("release-intent.json"), &row, None)
    }
}

fn authorize_wrap_publication(_root: &Path, _workspace: &Value, _keys_ref: &str,
    _proposal_id: &str, _wraps: &[WrapAtom]) -> Result<()> {
    Err("room key publication requires the exact current recipient/rotor authority guarded release receipt before ciphertext disclosure".into())
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
    let gen = synced
        .records
        .get(&me)
        .filter(|r| &r.enc_pub == public.as_bytes())
        .map_or(0, |r| r.key_epoch);
    let mut wraps = Vec::new();
    for epoch in synced.ring.epochs(&room) {
        if !mine.contains(&epoch) {
            let key = synced.ring.get(&room, epoch).expect("listed epoch");
            wraps.push(WrapAtom::new(&room, &founder, &public, gen, 0, &key)?);
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
    let encryption = enc_public(&*seed_of(&member_path(workspace, "key")?)?);
    let payload = EncRecord::signed_payload(room, keys, subject_number(subject)?, epoch,
        encryption.as_bytes(), &signer)?;
    Ok(json!({"type":"minidregg-signed-room-recipient-v2","member":subject,
        "room":room,"keysCell":keys,"keyEpoch":key_epoch,"recordHex":hex(&payload),
        "authority":"requires-current-source-verification"}))
}

/// Shared shell/chat transport parsing. This function never authenticates a
/// recipient: all authority comes from the later protected current-source check.
pub(crate) fn recipient_argument(text: &str) -> Result<String> {
    let text = text.trim();
    if text.len() > 4096 { return Err("recipient declaration exceeds its transport bound".into()); }
    let declaration = if text.starts_with('{') {
        let value: Value = serde_json::from_str(text).map_err(|error| error.to_string())?;
        if member(&value, "type")? != "minidregg-signed-room-recipient-v2" {
            return Err("unknown signed room recipient declaration".into());
        }
        let record_hex = member(&value, "recordHex")?;
        let bytes = crate::decode_hex(record_hex)?;
        let record = EncRecord::from_atom(member(&value, "member")?, &bytes, &Value::Null)?;
        let attestation = record.attestation.as_ref().ok_or("recipient JSON requires signed148 record")?;
        if attestation.room.to_string() != member(&value, "room")?
            || attestation.keys.to_string() != member(&value, "keysCell")?
            || record.key_epoch.to_string() != member(&value, "keyEpoch")? {
            return Err("recipient declaration metadata differs from its signed record".into());
        }
        record_hex.to_owned()
    } else { text.to_owned() };
    let bytes = crate::decode_hex(&declaration)?;
    if bytes.len() != 32 && bytes.len() != SIGNED_RECORD_LEN {
        return Err("recipient declaration must be signed148bytes or an existing-record32byte selector".into());
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
            let stored = stored.ok_or("first invite requires the member's full signed148 recipient declaration; a bare encryption key cannot authorize disclosure")?;
            if bytes != stored.enc_pub { return Err("named encryption key differs from recipient record".into()); }
            Ok(stored.clone())
        }
        _ => Err("invite encryption declaration must be a signed148-byte record, or32bytes matching an existing signed record".into()),
    }
}

/// Check the signed declaration and current source/head before an invitation
/// creates a room grant. This is a preflight only; the later release rechecks
/// membership, keys, lineage and authority on its actual admitted source image.
pub(crate) fn invite_preflight(root: &Path, workspace: &Value, room_name: &str,
    invitee: &str, declaration_hex: &str, i_know: bool) -> Result<()> {
    check_invitee(invitee, i_know)?;
    let (_, room, keys) = private_room(root, room_name)?;
    let synced = sync(root, workspace, room_name)?;
    let epoch = synced.epoch().ok_or("private room has no authenticated source epoch yet")?;
    if synced.ring.get(&room, epoch).is_none() {
        return Err("inviter does not hold the authenticated current room key".into());
    }
    let number = subject_number(invitee)?;
    let record = invitation_record(number, declaration_hex, synced.records.get(&number))?;
    authenticate_current_recipient(root, workspace, &room, &keys, &record)?;
    Ok(())
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
    let (room_ref, room, keys) = private_room(root, room_name)?;
    let synced = sync(root, workspace, room_name)?;
    let epoch = synced.epoch().ok_or_else(|| format!("{room_name} has no keys yet"))?;
    if synced.ring.get(&room, epoch).is_none() {
        return Err(format!("{room_name} is at epoch {epoch} and this client holds no key for it"));
    }
    // The first invitation can carry a member-authored signed declaration
    // before the member holds any keys grant. Raw public keys remain usable
    // only as selectors for an existing independently authenticated record.
    let invitee_number = subject_number(invitee)?;
    let record = invitation_record(invitee_number, enc_pub_hex, synced.records.get(&invitee_number))?;
    let authenticated = authenticate_current_recipient(root, workspace, &room, &keys, &record)?;
    let enc = PublicKey::from(authenticated.record.enc_pub);
    let gen = authenticated.record.key_epoch;
    let epochs: Vec<u32> = if past {
        synced.ring.epochs(&room).into_iter().filter(|e| *e <= epoch).collect()
    } else {
        vec![epoch]
    };
    let keys_ref = writable_keys_ref(root, room_name, &room_ref, &keys)?;
    // Only the founder (whose keys reference carries the cell's control) can
    // delegate the keys grant; anyone else's wrap write is the law's to refuse.
    let founder = reference(root, &keys_ref)?
        .get("controlCapability")
        .is_some_and(|control| !control.is_null());
    let grant = match grant_of(&synced.wraps, invitee_number) {
        0 if founder => keys_grant(root, workspace, &keys_ref, invitee, &format!("{proposal_id}-grant"))?,
        known => known,
    };
    let mut wraps = Vec::new();
    for e in epochs {
        let held: Vec<&WrapAtom> = synced
            .wraps
            .iter()
            .filter(|w| w.member == invitee_number && w.epoch == e)
            .collect();
        if held.iter().any(|w| &w.enc_pub == enc.as_bytes()) {
            eprintln!("room {room_name}: {invitee} already holds a wrap at epoch {e} to this key");
            continue;
        }
        if held.iter().any(|w| w.gen == gen) {
            return Err(format!(
                "{invitee} holds a wrap at epoch {e} to another key at generation {gen}: only a key {invitee} publishes as its record (`room register`, or `rotate-key`) can be wrapped again"
            ));
        }
        let key = synced.ring.get(&room, e).expect("listed epoch");
        wraps.push(WrapAtom::new(&room, invitee, &enc, gen, grant, &key)?);
    }
    if wraps.is_empty() {
        return Err(format!("{invitee} already holds a wrap to this key at every epoch asked for"));
    }
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
    // Authenticate every kept recipient before generating or releasing the next
    // room key. Missing records refuse the whole rotation, not a silent omission.
    let recipients = members_at(&synced.wraps, synced.epoch().ok_or("room has no keys")?)
        .keys().filter(|member| Some(**member) != dropped && current.contains(member))
        .map(|member| {
            let record = synced.records.get(member)
                .ok_or_else(|| format!("member {member} must publish a signed recipient-key record"))?;
            Ok((*member, authenticate_current_recipient(root, workspace, &room, &keys, record)?))
        }).collect::<Result<BTreeMap<_, _>>>()?;
    let (next, wraps, left) = rotation(&room, &synced.wraps, &recipients, &current, dropped)?;
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

/// Write (create, or edit to the current key) this subject's encryption-key
/// record in one private room's keys cell. One signed line: the law admits it
/// from this subject only, at its own number. Returns what it did.
pub(crate) fn register(root: &Path, workspace: &Value, room_name: &str, key_epoch: &str, proposal_id: &str) -> Result<Value> {
    let key_epoch: u32 = key_epoch.parse().map_err(|_| format!("key epoch {key_epoch} is not a 32-bit decimal"))?;
    let (room_ref, room, keys) = private_room(root, room_name)?;
    let (view, _, _) = signed_view(root, workspace, &keys_view_ref(&room_ref, &keys)?, "resource")?;
    let me = subject_number(member(workspace, "subject")?)?;
    let public = PublicKey::from(&own_secret(workspace)?);
    let wraps = wraps_in_view(&view)?;
    let signer = crate::read_secret(&member_path(workspace, "key")?)?;
    let payload = EncRecord::signed_payload(&room, &keys, me, key_epoch, public.as_bytes(), &signer)?;
    let kind = json!({"type":"inlineObject","schema":record_schema()});
    let action = match records_in_view(&view).remove(&me) {
        Some(record) if record.enc_pub == *public.as_bytes() && record.key_epoch == key_epoch
            && record.authenticate(&room, &keys, &signer.verifying_key().to_bytes(), key_epoch).is_ok() => {
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
        "encryptionKey":hex(public.as_bytes())}))
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
    let mut rooms: Vec<String> = fs::read_dir(root.join("refs"))
        .map(|entries| {
            entries
                .flatten()
                .filter_map(|entry| entry.file_name().into_string().ok())
                .filter_map(|name| name.strip_suffix(".json").map(str::to_owned))
                .filter(|name| !name.starts_with('.'))
                .collect()
        })
        .unwrap_or_default();
    rooms.sort();
    let mut out = Vec::new();
    for name in rooms {
        let Ok(reference) = reference(root, &name) else { continue };
        if reference.get("private").and_then(|p| p.get("keys")).is_none() {
            continue;
        }
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

/// `room rewrap ID ROOM SUBJECT` (the founder): wrap every epoch this founder
/// holds again to SUBJECT's recorded key, where SUBJECT holds no wrap to it --
/// the repair for a member who rotated its signing key.
pub(crate) fn rewrap(root: &Path, workspace: &Value, room_name: &str, subject: &str, proposal_id: &str) -> Result<()> {
    let number = subject_number(subject)?;
    let (room_ref, room, keys) = private_room(root, room_name)?;
    let synced = sync(root, workspace, room_name)?;
    let record = synced.records.get(&number).ok_or_else(|| {
        format!("{subject} has published no encryption-key record in {room_name}: it runs `room register {room_name}` first")
    })?;
    let authenticated = authenticate_current_recipient(root, workspace, &room, &keys, record)?;
    let record = &authenticated.record;
    let mut wraps = Vec::new();
    for epoch in synced.ring.epochs(&room) {
        let held: Vec<&WrapAtom> = synced.wraps.iter().filter(|w| w.member == number && w.epoch == epoch).collect();
        if held.is_empty() || held.iter().any(|w| w.enc_pub == record.enc_pub || w.gen == record.key_epoch) {
            continue;
        }
        let key = synced.ring.get(&room, epoch).expect("listed epoch");
        wraps.push(WrapAtom::new(&room, subject, &PublicKey::from(record.enc_pub), record.key_epoch,
            grant_of(&synced.wraps, number), &key)?);
    }
    if wraps.is_empty() {
        return Err(format!("{subject} already holds a wrap to its recorded key at every epoch it was wrapped at"));
    }
    let epochs: Vec<u32> = wraps.iter().map(|w| w.epoch).collect();
    let keys_ref = writable_keys_ref(root, room_name, &room_ref, &keys)?;
    write_wraps(root, workspace, &keys_ref, proposal_id, &wraps)?;
    println!("{}", serde_json::to_string_pretty(&json!({"type":"minidregg-room-rewrap-v1",
        "room":room_name,"member":subject,"epochs":epochs,"generation":record.key_epoch,
        "encryptionKey":hex(&record.enc_pub)})).map_err(|e| e.to_string())?);
    Ok(())
}

/// `room kick` in a private room: the K-ROOM revoke, then the rotation.
pub(crate) fn kick(root: &Path, workspace: &Value, room_name: &str, subject: &str, proposal_id: &str) -> Result<()> {
    let (_, room, keys) = private_room(root, room_name)?;
    // Do not revoke and then discover that recipient authentication is missing:
    // a partial kick would leave the former member holding the active epoch.
    // This is a preflight only; rotate checks current authority again afterwards.
    let dropped = subject_number(subject)?;
    let synced = sync(root, workspace, room_name)?;
    let epoch = synced.epoch().ok_or("room has no keys")?;
    for member in members_at(&synced.wraps, epoch).keys().filter(|member| **member != dropped) {
        let record = synced.records.get(member)
            .ok_or_else(|| format!("member {member} must publish a signed recipient-key record before kick"))?;
        authenticate_current_recipient(root, workspace, &room, &keys, record)?;
    }
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

    fn wrap_for(seed: u8, member: &str, key: &RoomKey) -> WrapAtom {
        WrapAtom::new(ROOM, member, &enc_public(&[seed; 32]), 0, 0, key).unwrap()
    }

    fn authenticated(seed: u8, member: u64, epoch: u32) -> AuthenticatedRecord {
        let signer = SigningKey::from_bytes(&[seed; 32]);
        let payload = EncRecord::signed_payload(ROOM, "72", member, epoch,
            enc_public(&[seed; 32]).as_bytes(), &signer).unwrap();
        let record = EncRecord::from_atom(&member.to_string(), &payload, &json!({})).unwrap();
        let checked = record.authenticate(ROOM, "72", &signer.verifying_key().to_bytes(), epoch).unwrap();
        AuthenticatedRecord { record: checked.0, authority: RecipientAuthority::TrustedFixture }
    }

    fn initial_recipients(entries: &[(u64, u8)]) -> BTreeMap<u64, AuthenticatedRecord> {
        entries.iter().map(|(member, seed)| (*member, authenticated(*seed, *member, 0))).collect()
    }

    #[test]
    fn operator_minted_next_wrap_fails_and_independently_authorized_rotation_decrypts() {
        let founder = SigningKey::from_bytes(&[1; 32]);
        let rotor = SigningKey::from_bytes(&[2; 32]);
        let operator = SigningKey::from_bytes(&[8; 32]);
        let e0 = RoomKey::generate(0).unwrap();
        let c0 = EpochCertificate::sign(ROOM, "72", &e0, [0; 32], 11, 0, &founder).unwrap();
        let w0 = wrap_for(3, "13", &e0).sign(&c0, 11, 0, &founder).unwrap();
        w0.check_signatures(ROOM, "72", &founder.verifying_key().to_bytes(),
            &founder.verifying_key().to_bytes()).unwrap();
        let e1 = RoomKey::generate(1).unwrap();
        // A governed source may admit a rotor other than the founder. The
        // protocol binds that independently selected authority explicitly.
        let c1 = EpochCertificate::sign(ROOM, "72", &e1, c0.identity(), 12, 1, &rotor).unwrap();
        let w1 = wrap_for(3, "13", &e1).sign(&c1, 12, 1, &rotor).unwrap();
        w1.check_signatures(ROOM, "72", &rotor.verifying_key().to_bytes(),
            &rotor.verifying_key().to_bytes()).unwrap();
        let parsed = WrapAtom::from_atom(&wrap_atom_id(1, 0, 13), &w1.payload()).unwrap();
        assert_eq!(parsed, w1);
        assert_eq!(parsed.open(ROOM, &derive_enc_key(&[3; 32])).unwrap().bytes(), e1.bytes());
        let head = check_epoch_chain(&[w0.clone(), w1.clone()], None).unwrap();
        assert_eq!(head, EpochHead { epoch: 1, identity: c1.identity() });
        let minted = RoomKey::generate(2).unwrap();
        let fake = EpochCertificate::sign(ROOM, "72", &minted, c1.identity(), 12, 1, &operator).unwrap();
        let attacker_wrap = wrap_for(3, "13", &minted).sign(&fake, 12, 1, &operator).unwrap();
        assert!(attacker_wrap.check_signatures(ROOM, "72", &rotor.verifying_key().to_bytes(),
            &rotor.verifying_key().to_bytes()).is_err(), "operator self-signing is not rooted rotation authority");
        let mut replaced = w1.clone();
        replaced.wrapped = wrap_for(3, "13", &minted).wrapped;
        assert!(replaced.check_signatures(ROOM, "72", &rotor.verifying_key().to_bytes(),
            &rotor.verifying_key().to_bytes()).is_err());
        assert!(wrap_for(3, "13", &minted).check_signatures(ROOM, "72",
            &rotor.verifying_key().to_bytes(), &rotor.verifying_key().to_bytes()).is_err());
        assert!(w1.check_signatures(ROOM, "73", &rotor.verifying_key().to_bytes(),
            &rotor.verifying_key().to_bytes()).is_err());
        assert!(check_epoch_chain(&[w1], None).is_err(), "first contact cannot infer its missing genesis anchor");
    }

    #[test]
    fn rollback_to_pre_kick_epoch_and_forgetting_never_select_an_old_sealing_key() {
        let signer = SigningKey::from_bytes(&[1; 32]);
        let e0 = RoomKey::generate(0).unwrap();
        let c0 = EpochCertificate::sign(ROOM, "72", &e0, [0; 32], 11, 0, &signer).unwrap();
        let e1 = RoomKey::generate(1).unwrap();
        let c1 = EpochCertificate::sign(ROOM, "72", &e1, c0.identity(), 11, 0, &signer).unwrap();
        let w0 = wrap_for(3, "13", &e0).sign(&c0, 11, 0, &signer).unwrap();
        let w1 = wrap_for(3, "13", &e1).sign(&c1, 11, 0, &signer).unwrap();
        let head = check_epoch_chain(&[w0.clone(), w1], None).unwrap();
        assert!(check_epoch_chain(&[w0], Some(&head)).is_err(), "operator cannot return the pre-kick prefix");
        let mut ring = Keyring::default();
        ring.insert(ROOM, &e0);
        ring.insert(ROOM, &e1);
        let key = select_current_key(&ring, ROOM, &head, &c1).unwrap();
        let payload = seal_for_room(&key, ROOM, "80", "1", b"after kick").unwrap();
        let mut kicked = Keyring::default();
        kicked.insert(ROOM, &e0);
        assert!(open_in_room(Some(&kicked), ROOM, "80", "1", &payload).is_string());
        ring.forget(ROOM, 1);
        assert!(select_current_key(&ring, ROOM, &head, &c1).is_err(), "forgetting current key does not authorize sealing under epoch zero");
        let mut poisoned_cache = Keyring::default();
        poisoned_cache.insert(ROOM, &RoomKey::generate(1).unwrap());
        assert!(select_current_key(&poisoned_cache, ROOM, &head, &c1).is_err(), "an operator key cached before migration cannot become a sealing key");
        let forged_same_epoch = EpochHead { epoch: 1, identity: [8; 32] };
        assert!(advance_head(Some(&head), &forged_same_epoch).is_err());
    }

    #[test]
    fn first_contact_refuses_valid_old_prefix_and_empty_source_cannot_erase_a_head() {
        let signer = SigningKey::from_bytes(&[1; 32]);
        let e0 = RoomKey::generate(0).unwrap();
        let c0 = EpochCertificate::sign(ROOM, "72", &e0, [0; 32], 11, 0, &signer).unwrap();
        let e1 = RoomKey::generate(1).unwrap();
        let c1 = EpochCertificate::sign(ROOM, "72", &e1, c0.identity(), 11, 0, &signer).unwrap();
        let w0 = wrap_for(3, "13", &e0).sign(&c0, 11, 0, &signer).unwrap();
        let w1 = wrap_for(3, "13", &e1).sign(&c1, 11, 0, &signer).unwrap();
        let latest = EpochHead { epoch: 1, identity: c1.identity() };
        assert!(check_epoch_chain(&[w0.clone()], None).is_ok());
        assert!(check_source_head(&[w0.clone()], None, Some(&latest)).is_err(),
            "even valid genesis cannot impersonate the independently current source on first contact");
        assert_eq!(check_source_head(&[w0, w1], None, Some(&latest)).unwrap(), Some(latest.clone()));
        assert_eq!(check_source_head(&[], None, None).unwrap(), None,
            "an independently authenticated newly empty keys cell may initialize genesis");
        assert!(check_source_head(&[], Some(&latest), None).is_err());
        assert!(check_source_head(&[], None, Some(&latest)).is_err());
    }

    #[test]
    fn applied_release_advances_head_before_ciphertext_delivery_without_old_key_fallback() {
        let signer = SigningKey::from_bytes(&[1; 32]);
        let e0 = RoomKey::generate(0).unwrap();
        let c0 = EpochCertificate::sign(ROOM, "72", &e0, [0; 32], 11, 0, &signer).unwrap();
        let e1 = RoomKey::generate(1).unwrap();
        let c1 = EpochCertificate::sign(ROOM, "72", &e1, c0.identity(), 11, 0, &signer).unwrap();
        let w0 = wrap_for(3, "13", &e0).sign(&c0, 11, 0, &signer).unwrap();
        // Here c1 is selected by the independently rooted source query after
        // release Applied; only the old ciphertext has been published so far.
        let head = check_source_latest(ROOM, "72", &[w0], None, Some(&c1)).unwrap().unwrap();
        assert_eq!(head.epoch, 1);
        let mut ring = Keyring::default();
        ring.insert(ROOM, &e0);
        assert!(select_current_key(&ring, ROOM, &head, &c1).is_err());
        assert!(check_source_latest(ROOM, "72", &[], Some(&head), Some(&c0)).is_err());
        assert!(check_source_latest(ROOM, "73", &[], None, Some(&c1)).is_err());
        assert!(check_source_latest(ROOM, "72", &[], Some(&head), None).is_err());
    }

    #[test]
    fn recipient_signature_rejects_operator_substitution_and_accepts_legitimate_rotation() {
        let signer = SigningKey::from_bytes(&[9; 32]);
        let trusted_public = signer.verifying_key().to_bytes();
        let payload = EncRecord::signed_payload(ROOM, "72", 11, 2,
            enc_public(&[9; 32]).as_bytes(), &signer).unwrap();
        let parse = |bytes: &[u8]| EncRecord::from_atom("11", bytes, &json!({})).unwrap();
        let checked = parse(&payload).authenticate(ROOM, "72", &trusted_public, 2).unwrap();
        let legitimate = AuthenticatedRecord { record: checked.0, authority: RecipientAuthority::TrustedFixture };
        let old_key = RoomKey::generate(0).unwrap();
        let wraps = [wrap_for(1, "11", &old_key)];
        let recipients = [(11, legitimate)].into_iter().collect();
        let (new_key, released, _) = rotation(ROOM, &wraps, &recipients,
            &[11].into_iter().collect(), None).unwrap();
        assert_eq!(released[0].open(ROOM, &derive_enc_key(&[9; 32])).unwrap().bytes(), new_key.bytes());
        assert!(released[0].open(ROOM, &derive_enc_key(&[8; 32])).is_err());
        let mut substituted = payload.clone();
        substituted[4..36].copy_from_slice(enc_public(&[8; 32]).as_bytes());
        assert!(parse(&substituted).authenticate(ROOM, "72", &trusted_public, 2).is_err());
        let operator = SigningKey::from_bytes(&[8; 32]);
        let forged = EncRecord::signed_payload(ROOM, "72", 11, 2,
            enc_public(&[8; 32]).as_bytes(), &operator).unwrap();
        assert!(parse(&forged).authenticate(ROOM, "72", &trusted_public, 2).is_err(),
            "self-signing an operator-selected replacement is not member authority");
        assert!(parse(&payload).authenticate(ROOM, "72", &trusted_public, 3).is_err());
        assert!(parse(&payload).authenticate("70", "72", &trusted_public, 2).is_err());
        assert!(parse(&payload).authenticate(ROOM, "73", &trusted_public, 2).is_err());
        let relabelled = EncRecord::from_atom("12", &payload, &json!({})).unwrap();
        assert!(relabelled.authenticate(ROOM, "72", &trusted_public, 2).is_err());
        let legacy = [&2u32.to_be_bytes()[..], enc_public(&[9; 32]).as_bytes()].concat();
        assert!(parse(&legacy).authenticate(ROOM, "72", &trusted_public, 2).is_err());
        assert!(authenticate_current_recipient(Path::new("unused"), &json!({}), ROOM,
            "72", &parse(&payload)).is_err(), "absence of rooted authority never downgrades to endpoint trust");
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
        assert_eq!(parsed[0].action()["atom"], wrap_atom_id(0, 0, 11));
        let key = parsed[1].open(ROOM, &derive_enc_key(&[2; 32])).unwrap();
        assert_eq!((key.epoch(), key.bytes()), (0, e0.bytes()));
        assert!(parsed[1].open(ROOM, &derive_enc_key(&[1; 32])).is_err(), "a member cannot open another's wrap");
        assert!(parsed[1].open("70", &derive_enc_key(&[2; 32])).is_err(), "a wrap is bound to its room");
    }

    #[test]
    fn wrap_atom_ids_name_one_epoch_generation_and_member_and_refuse_noncanonical_forms() {
        // Kernel/PrivateRoomKeys.lean wrapAtomId: (epoch + 1) * 2^96 + gen * 2^64 + member.
        assert_eq!(wrap_atom_id(0, 0, 12), ((1u128 << 96) + 12).to_string());
        assert_eq!(wrap_atom_id(1, 2, 12), ((2u128 << 96) + (2u128 << 64) + 12).to_string());
        assert_eq!(parse_wrap_atom_id(&wrap_atom_id(7, 3, u64::MAX)).unwrap(), (7, 3, u64::MAX));
        assert_eq!(parse_wrap_atom_id(&wrap_atom_id(MAX_EPOCH, u32::MAX, 1)).unwrap(), (MAX_EPOCH, u32::MAX, 1));
        assert_ne!(wrap_atom_id(4, 1, 12), wrap_atom_id(4, 2, 12), "a re-wrap is a new atom");
        assert!(parse_wrap_atom_id("012").is_err());
        assert!(parse_wrap_atom_id("12").is_err(), "the record region is not a wrap");
        assert!(parse_wrap_atom_id(&((1u128 << 127) + (1u128 << 96)).to_string()).is_err());
        let e3 = RoomKey::generate(3).unwrap();
        let id = wrap_atom_id(3, 0, 11);
        let mut payload = wrap_for(1, "11", &e3).payload();
        assert!(WrapAtom::from_atom(&id, &payload[..payload.len() - 1]).is_err());
        payload.push(0);
        assert!(WrapAtom::from_atom(&id, &payload).is_err());
    }

    #[test]
    fn a_member_who_rotated_is_rewrapped_to_its_record_and_opens_with_its_keyring() {
        let e0 = RoomKey::generate(0).unwrap();
        let mut old = wrap_for(1, "11", &e0);
        old.grant = 900;
        let wraps0 = vec![wrap_for(2, "12", &e0), old.clone()];
        // 11 rotated: its record names the key of seed 9 at key epoch 2.
        let records = [(11, authenticated(9, 11, 2)), (12, authenticated(2, 12, 0))]
            .into_iter().collect();
        let current: BTreeSet<u64> = [11, 12].into_iter().collect();
        let (e1, wraps1, _) = rotation(ROOM, &wraps0, &records, &current, None).unwrap();
        let mine = wraps1.iter().find(|w| w.member == 11).unwrap();
        assert_eq!((mine.gen, mine.grant), (2, 900), "to the record, carrying the keys grant");
        assert!(mine.open(ROOM, &derive_enc_key(&[1; 32])).is_err(), "the OLD secret cannot open the new epoch");
        assert_eq!(mine.open(ROOM, &derive_enc_key(&[9; 32])).unwrap().bytes(), e1.bytes());
        // The past stays open with the kept secret.
        assert_eq!(old.open(ROOM, &derive_enc_key(&[1; 32])).unwrap().bytes(), e0.bytes());
        // An operator-served old wrap cannot substitute for current authority.
        assert!(rotation(ROOM, &wraps0, &BTreeMap::new(), &current, None).is_err());
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
        let (e1, wraps1, left) = rotation(ROOM, &wraps0,
            &initial_recipients(&[(11, 1), (13, 3)]), &current, Some(12)).unwrap();
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
        let (_, wraps1, left) = rotation(ROOM, &wraps0,
            &initial_recipients(&[(11, 1)]), &only_a, None).unwrap();
        assert_eq!(wraps1.len(), 1);
        assert_eq!(left, vec![12]);
        assert!(rotation(ROOM, &[], &BTreeMap::new(), &only_a, None).is_err());
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
        let relabelled = WrapAtom::from_atom(&wrap_atom_id(1, 0, 11), &w.payload()).unwrap();
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
    fn first_invite_signed_descriptor_needs_current_authority_but_no_prior_wrap_or_record() {
        let signer = SigningKey::from_bytes(&[9; 32]);
        let encryption = enc_public(&[9; 32]);
        let payload = EncRecord::signed_payload(ROOM, "72", 9, 0, encryption.as_bytes(), &signer).unwrap();
        assert!(invitation_record(9, &hex(encryption.as_bytes()), None).is_err());
        let declaration = json!({"type":"minidregg-signed-room-recipient-v2","member":"9",
            "room":ROOM,"keysCell":"72","keyEpoch":"0","recordHex":hex(&payload)});
        assert_eq!(recipient_argument(&declaration.to_string()).unwrap(), hex(&payload));
        let mut wrong_metadata = declaration.clone(); wrong_metadata["room"] = json!("73");
        assert!(recipient_argument(&wrong_metadata.to_string()).is_err());
        let declared = invitation_record(9, &declaration.to_string(), None).unwrap();
        assert!(declared.authenticate(ROOM, "72", &signer.verifying_key().to_bytes(), 0).is_ok());
        assert!(declared.authenticate(ROOM, "72", &SigningKey::from_bytes(&[8; 32]).verifying_key().to_bytes(), 0).is_err());
        assert!(declared.authenticate(ROOM, "72", &signer.verifying_key().to_bytes(), 1).is_err());
        assert!(declared.authenticate(ROOM, "73", &signer.verifying_key().to_bytes(), 0).is_err());
        assert!(invitation_record(9, &hex(encryption.as_bytes()), Some(&declared)).is_ok());
        let mut substituted = payload.clone(); substituted[4] ^= 1;
        assert!(invitation_record(9, &hex(&substituted), Some(&declared)).is_err());
    }

    #[test]
    fn delivery_commitment_binds_complete_wrap_and_exact_recipient_address() {
        let key = RoomKey::generate(1).unwrap();
        let issuer = SigningKey::from_bytes(&[7; 32]);
        let certificate = EpochCertificate::sign(ROOM, "72", &key, [1; 32], 7, 0, &issuer).unwrap();
        let recipient_signer = SigningKey::from_bytes(&[9; 32]);
        let encryption = enc_public(&[9; 32]);
        let record_payload = EncRecord::signed_payload(ROOM, "72", 9, 3,
            encryption.as_bytes(), &recipient_signer).unwrap();
        let record = EncRecord::from_atom("9", &record_payload, &Value::Null).unwrap();
        let authenticated = AuthenticatedRecord { record: record.authenticate(ROOM, "72",
            &recipient_signer.verifying_key().to_bytes(), 3).unwrap().0,
            authority: RecipientAuthority::TrustedFixture };
        let unsigned = WrapAtom::new(ROOM, "9", &encryption, 3, 23, &key).unwrap();
        assert!(unsigned.payload_commitment().is_err());
        let signed = unsigned.sign(&certificate, 7, 0, &issuer).unwrap();
        let payload = signed.payload();
        assert_eq!(payload.len(), 444);
        assert_eq!(signed.payload_commitment().unwrap(), lineage_digest(&[&payload]));
        let declaration = signed.delivery_declaration(&authenticated, 37).unwrap();
        assert_eq!(declaration["atom"], wrap_atom_id(1, 3, 9));
        assert_eq!(declaration["roomCapability"], "37");
        assert_eq!(declaration["ciphertextCommitmentHex"], hex(&signed.payload_commitment().unwrap()));
        // The commitment includes grant, certificate, signer and signature,
        // not merely the 104-byte encrypted component.
        for offset in [0, 32, 136, 144, 336, 344, 348, 380, 443] {
            let mut substituted = payload.clone(); substituted[offset] ^= 1;
            let altered = WrapAtom::from_atom(&wrap_atom_id(1, 3, 9), &substituted).unwrap();
            assert_ne!(altered.payload_commitment().unwrap(), signed.payload_commitment().unwrap());
        }
        let mut wrong_address = signed.clone(); wrong_address.gen = 2;
        assert!(wrong_address.delivery_declaration(&authenticated, 37).is_err());
        let mut wrong_recipient = authenticated;
        wrong_recipient.record.member = 8;
        assert!(signed.delivery_declaration(&wrong_recipient, 37).is_err());
    }

    #[test]
    fn release_draft_recovers_original_key_ciphertext_and_nonce_without_sealing_permission() {
        let root = std::env::temp_dir().join(format!("mini-release-draft-{}-{}",
            std::process::id(), super::super::random_nonce().unwrap()));
        super::super::make_private_dir(&root).unwrap();
        let key = RoomKey::generate(1).unwrap();
        let signer = SigningKey::from_bytes(&[7; 32]);
        let certificate = EpochCertificate::sign(ROOM, "72", &key, [1; 32], 7, 0, &signer).unwrap();
        let public = PublicKey::from(&derive_enc_key(&[9; 32]));
        let wrap = WrapAtom::new(ROOM, "9", &public, 0, 23, &key).unwrap()
            .sign(&certificate, 7, 0, &signer).unwrap();
        let operation = [5; 32];
        let request = b"canonical request from the native author";
        let draft = RetainedReleaseDraft::stage(&root, &operation, request, &certificate,
            &[wrap.clone()], &key, b"pass").unwrap();
        assert_eq!(draft.key(b"pass").unwrap().bytes(), key.bytes());
        assert!(load_ring(&root, b"pass").unwrap().get(ROOM, 1).is_none(),
            "staging must not install a key in the ordinary sealing cache");
        assert!(draft.key(b"wrong pass").is_err());
        let prior = fs::read(draft.directory.join("draft.json")).unwrap();
        let retry = RetainedReleaseDraft::stage(&root, &operation, request, &certificate,
            &[wrap.clone()], &key, b"pass").unwrap();
        assert_eq!(retry.manifest, draft.manifest);
        assert_eq!(fs::read(draft.directory.join("draft.json")).unwrap(), prior);
        assert!(RetainedReleaseDraft::stage(&root, &operation, b"different operation",
            &certificate, &[wrap], &key, b"pass").is_err());
        let intent = json!({"subject":"7","nonce":"19","purpose":{"type":"prepare",
            "draft":{"type":"invoke","command":{"subject":"7","nonce":"29","targets":[],
                "family":{"route":"roomRelease","contextBytes":hex(request)}}}}});
        draft.bind_release_intent(&intent, "original-attempt").unwrap();
        draft.bind_release_intent(&intent, "original-attempt").unwrap();
        let mut changed = intent.clone();
        changed["purpose"]["draft"]["command"]["nonce"] = json!("31");
        assert!(draft.bind_release_intent(&changed, "original-attempt").is_err());
        assert!(draft.bind_release_intent(&intent, "replacement-attempt").is_err());
        let cache = draft.directory.join("draft-key.cache");
        let mut poison = fs::read(&cache).unwrap(); poison[0] ^= 1;
        fs::write(&cache, poison).unwrap();
        assert!(RetainedReleaseDraft::load(&root, &operation).is_err());
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
