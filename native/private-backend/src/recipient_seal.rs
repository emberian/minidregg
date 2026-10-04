//! Recipient-only sealed AUTH. Crypto provider is the exact shared transit module.
//! Source-visible fields are public committee context, sequence/key epoch/binding,
//! fixed padding class and semantic commitment. No plaintext protocol body in wire.
//! Decryption proves confidentiality/integrity binding, NOT native source authority.
use crate::{
    authenticated_ingress::{CommitteeParty, Envelope},
    codec::{bad, bytes, Nat, Reader},
    crypto_transit,
};
use sha2::{Digest, Sha512};
use std::{
    fs::File,
    io::{Read, Result},
};
const FRAME: &[u8] = b"DREGG.PRIVATE.SEALED.INGRESS\x03";
/// The v2 frame (pure ML-KEM-768 recipient suite, algorithm 1): refused by name.
const FRAME_V2: &[u8] = b"DREGG.PRIVATE.SEALED.INGRESS\x02";
/// The recipient suite id: 2 = hybrid X25519 + ML-KEM-768 (`hybrid_kem`). Suite 1
/// was pure ML-KEM-768 and is refused.
const ALGORITHM_HYBRID: u64 = 2;
const SIGN: &[u8] = b"DREGG.PRIVATE.SEALED.SOURCE.SIGN\x03";
const PAD: &[u8] = b"DREGG.PRIVATE.RECIPIENT.PAD\x02";
pub const MAX_PLAINTEXT: usize = 131168;
pub const MAX_SEALED: usize = 262078;
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecipientSpec {
    pub algorithm: Nat,
    pub key_epoch: Nat,
    pub key_id: Vec<u8>,
    pub plaintext_bound: usize,
}
impl RecipientSpec {
    pub fn validate(&self) -> Result<()> {
        if self.algorithm == Nat::new(1) {
            return Err(bad(
                "recipient algorithm 1 is the pre-hybrid pure ML-KEM-768 suite: refused; the suite is algorithm 2, hybrid X25519 + ML-KEM-768",
            ));
        }
        if self.algorithm != Nat::new(ALGORITHM_HYBRID)
            || self.key_id.is_empty()
            || self.key_id.len() > 128
            || self.plaintext_bound < PAD.len() + 37
            || self.plaintext_bound > MAX_PLAINTEXT
        {
            return Err(bad("recipient suite/key/padding profile"));
        }
        Ok(())
    }
    pub fn epoch_bytes(&self) -> Vec<u8> {
        let mut b = vec![];
        self.key_epoch.put(&mut b);
        b
    }
}
pub fn recipient_key_id(public_key: &[u8]) -> Vec<u8> {
    let mut b = b"DREGG.PRIVATE.RECIPIENT.KEY.ID\x03".to_vec();
    bytes(public_key, &mut b);
    Sha512::digest(&b).to_vec()
}
/// Exact native INNER semantic marker. The closed source producer derives
/// this from the retained admitted capsule; plaintext SIGN/nonce never crosses
/// the shared native host boundary. A marker alone is NOT a native credential.
pub fn opaque_message_marker(
    party: &CommitteeParty,
    sequence: u64,
    semantic: &[u8; 64],
) -> Vec<u8> {
    let mut b = b"DREGG.PRIVATE.OPAQUE.MESSAGE\x01".to_vec();
    bytes(&party.encode(), &mut b);
    b.extend(sequence.to_le_bytes());
    b.extend(semantic);
    b
}
/// Public pre-seal authoring projection. This is a claim, never an admitted
/// source packet. Its hiding commitment comes from the retained endpoint draft.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DraftPublic {
    pub party: CommitteeParty,
    pub sequence: u64,
    pub recipient: RecipientSpec,
    pub semantic_commitment: [u8; 64],
}
impl DraftPublic {
    pub fn encode(&self) -> Result<Vec<u8>> {
        self.recipient.validate()?;
        let mut b = b"DREGG.PRIVATE.SEALED.DRAFT\x01".to_vec();
        bytes(&self.party.encode(), &mut b);
        b.extend(self.sequence.to_le_bytes());
        self.recipient.algorithm.put(&mut b);
        self.recipient.key_epoch.put(&mut b);
        bytes(&self.recipient.key_id, &mut b);
        Nat::new(self.recipient.plaintext_bound as u64).put(&mut b);
        b.extend(self.semantic_commitment);
        if b.len() > MAX_SEALED {
            return Err(bad("public draft capacity"));
        }
        Ok(b)
    }
    pub fn decode(b: &[u8]) -> Result<Self> {
        const FRAME: &[u8] = b"DREGG.PRIVATE.SEALED.DRAFT\x01";
        if b.len() > MAX_SEALED || !b.starts_with(FRAME) {
            return Err(bad("public draft frame/capacity"));
        }
        let mut c = crate::consensus_wire::Cursor::new(&b[FRAME.len()..])?;
        let party = CommitteeParty::decode(&c.bytes()?)?;
        let sequence = c.u64()?;
        let recipient = RecipientSpec {
            algorithm: cursor_nat(&mut c)?,
            key_epoch: cursor_nat(&mut c)?,
            key_id: c.bytes()?,
            plaintext_bound: usize::try_from(cursor_nat(&mut c)?.value()?)
                .map_err(|_| bad("draft padding bound"))?,
        };
        let semantic_commitment = c.take(64)?.try_into().unwrap();
        c.finish()?;
        let out = Self {
            party,
            sequence,
            recipient,
            semantic_commitment,
        };
        if out.encode()? != b {
            return Err(bad("public draft canonical"));
        }
        Ok(out)
    }
    pub fn inner_native_marker(&self) -> Vec<u8> {
        opaque_message_marker(&self.party, self.sequence, &self.semantic_commitment)
    }
    /// Public field equality only; the source still verifies both native
    /// credentials/current admission, and only a recipient decrypts the body.
    pub fn matches_capsule(&self, c: &SealedIngress) -> bool {
        self.party == c.party
            && self.sequence == c.sequence
            && self.recipient == c.recipient
            && self.semantic_commitment == c.semantic_commitment
    }
}
pub fn semantic_commitment(hiding_nonce: &[u8; 32], signing: &[u8]) -> [u8; 64] {
    let mut b = b"DREGG.PRIVATE.SEALED.SEMANTIC\x02".to_vec();
    b.extend(hiding_nonce);
    bytes(signing, &mut b);
    Sha512::digest(&b).into()
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SealedIngress {
    pub party: CommitteeParty,
    pub sequence: u64,
    pub recipient: RecipientSpec,
    pub semantic_commitment: [u8; 64],
    pub hybrid_ciphertext: [u8; crypto_transit::HYBRID_CIPHERTEXT_BYTES],
    pub nonce: [u8; 24],
    pub key_cipher_commitment: [u8; 32],
    pub ciphertext: Vec<u8>,
    pub outer_native_credential: Vec<u8>,
}
impl SealedIngress {
    /// The source and primitive both bind this exact public prefix. The source
    /// separately checks it against a currently selected enrollment/padding class.
    pub fn public_binding(&self) -> Vec<u8> {
        let mut b = FRAME.to_vec();
        bytes(&self.party.encode(), &mut b);
        b.extend(self.sequence.to_le_bytes());
        self.recipient.algorithm.put(&mut b);
        self.recipient.key_epoch.put(&mut b);
        bytes(&self.recipient.key_id, &mut b);
        Nat::new(self.recipient.plaintext_bound as u64).put(&mut b);
        b.extend(self.semantic_commitment);
        b
    }
    pub fn inner_native_marker(&self) -> Vec<u8> {
        opaque_message_marker(&self.party, self.sequence, &self.semantic_commitment)
    }
    pub fn source_signing_bytes(&self) -> Vec<u8> {
        let mut b = SIGN.to_vec();
        bytes(&self.public_binding(), &mut b);
        b.extend(self.hybrid_ciphertext);
        b.extend(self.nonce);
        b.extend(self.key_cipher_commitment);
        bytes(&self.ciphertext, &mut b);
        b
    }
    pub fn encode(&self) -> Result<Vec<u8>> {
        self.recipient.validate()?;
        if self.ciphertext.len() != self.recipient.plaintext_bound + 16 {
            return Err(bad("recipient fixed ciphertext shape"));
        }
        let mut b = self.public_binding();
        b.extend(self.hybrid_ciphertext);
        b.extend(self.nonce);
        b.extend(self.key_cipher_commitment);
        bytes(&self.ciphertext, &mut b);
        bytes(&self.outer_native_credential, &mut b);
        if b.len() > MAX_SEALED {
            return Err(bad("sealed ingress capacity"));
        }
        Ok(b)
    }
    pub fn decode(b: &[u8]) -> Result<Self> {
        if b.starts_with(FRAME_V2) {
            return Err(bad(
                "sealed ingress is a v2 frame (pure ML-KEM-768 recipient suite): refused; the frame is v3, hybrid X25519 + ML-KEM-768",
            ));
        }
        if b.len() > MAX_SEALED || !b.starts_with(FRAME) {
            return Err(bad("sealed ingress frame/capacity"));
        }
        let mut c = crate::consensus_wire::Cursor::new(&b[FRAME.len()..])?;
        let party = CommitteeParty::decode(&c.bytes()?)?;
        let sequence = c.u64()?;
        let algorithm = cursor_nat(&mut c)?;
        let key_epoch = cursor_nat(&mut c)?;
        let key_id = c.bytes()?;
        let plaintext_bound = cursor_nat(&mut c)?.value()? as usize;
        let semantic_commitment = c.take(64)?.try_into().unwrap();
        let hybrid_ciphertext = c.take(crypto_transit::HYBRID_CIPHERTEXT_BYTES)?.try_into().unwrap();
        let nonce = c.take(24)?.try_into().unwrap();
        let key_cipher_commitment = c.take(32)?.try_into().unwrap();
        let ciphertext = c.bytes()?;
        let outer_native_credential = c.bytes()?;
        c.finish()?;
        let out = Self {
            party,
            sequence,
            recipient: RecipientSpec {
                algorithm,
                key_epoch,
                key_id,
                plaintext_bound,
            },
            semantic_commitment,
            hybrid_ciphertext,
            nonce,
            key_cipher_commitment,
            ciphertext,
            outer_native_credential,
        };
        if out.encode()? != b {
            return Err(bad("sealed ingress canonical"));
        }
        Ok(out)
    }
    /// Expected role/context/key are selected by the actual native source
    /// receipt and endpoint-owned key custody, never by trusting this claim.
    pub fn open(
        &self,
        secret_key: &[u8],
        retained_public_key: &[u8],
        expected_party: &CommitteeParty,
        expected_sequence: u64,
        expected_recipient: &RecipientSpec,
    ) -> Result<DecryptedEnvelope> {
        if &self.party != expected_party
            || self.sequence != expected_sequence
            || &self.recipient != expected_recipient
        {
            return Err(bad("sealed recipient/source context mismatch"));
        }
        self.encode()?;
        if recipient_key_id(retained_public_key) != expected_recipient.key_id {
            return Err(bad("recipient retained public enrollment key binding"));
        }
        // The secret is a seed, so the ORIGINAL endpoint-retained public key is
        // checked against the public key the secret regenerates; never infer it
        // from network claims or a latest-key lookup.
        crypto_transit::validate_keypair(secret_key, retained_public_key)
            .map_err(|_| bad("recipient retained key pair refused"))?;
        let parts = crypto_transit::SealedParts {
            hybrid_ciphertext: self.hybrid_ciphertext,
            nonce: self.nonce,
            commitment: self.key_cipher_commitment,
            ciphertext: self.ciphertext.clone(),
        };
        let plaintext = crypto_transit::open(
            secret_key,
            &self.recipient.epoch_bytes(),
            &self.public_binding(),
            parts.as_ref(),
        )
        .map_err(|_| bad("recipient authentication refused"))?;
        if plaintext.len() != self.recipient.plaintext_bound || !plaintext.starts_with(PAD) {
            return Err(bad("recipient padding frame/shape"));
        }
        let len =
            u32::from_le_bytes(plaintext[PAD.len()..PAD.len() + 4].try_into().unwrap()) as usize;
        let hiding_nonce: [u8; 32] = plaintext[PAD.len() + 4..PAD.len() + 36].try_into().unwrap();
        let start = PAD.len() + 36;
        let end = start
            .checked_add(len)
            .filter(|n| *n <= plaintext.len())
            .ok_or_else(|| bad("recipient plaintext length"))?;
        if plaintext[end..].iter().any(|x| *x != 0) {
            return Err(bad("recipient noncanonical padding"));
        }
        let inner = Envelope::decode(&plaintext[start..end])?;
        if inner.party != self.party
            || inner.sequence != self.sequence
            || semantic_commitment(&hiding_nonce, &inner.signing_bytes())
                != self.semantic_commitment
        {
            return Err(bad("recipient inner semantic commitment mismatch"));
        }
        Ok(DecryptedEnvelope {
            inner,
            hiding_nonce,
            semantic_commitment: self.semantic_commitment,
            original_sealed_bytes: self.encode()?,
        })
    }
}
/// No Debug/Clone and private constructor: do not accidentally log the body.
/// This token is actual decryption/binding only, not VerifiedPacket/Applied.
pub struct DecryptedEnvelope {
    inner: Envelope,
    hiding_nonce: [u8; 32],
    semantic_commitment: [u8; 64],
    original_sealed_bytes: Vec<u8>,
}
impl DecryptedEnvelope {
    pub fn inner(&self) -> &Envelope {
        &self.inner
    }
    /// Endpoint-only witness for hidden-body native marker checks. Never send
    /// this nonce or the clear signing preimage to a shared controller.
    pub fn hiding_nonce(&self) -> &[u8; 32] {
        &self.hiding_nonce
    }
    pub fn semantic_commitment(&self) -> [u8; 64] {
        self.semantic_commitment
    }
    pub fn inner_native_marker(&self) -> Vec<u8> {
        opaque_message_marker(
            &self.inner.party,
            self.inner.sequence,
            &self.semantic_commitment,
        )
    }
    pub fn original_sealed_bytes(&self) -> &[u8] {
        &self.original_sealed_bytes
    }
    pub fn into_inner(self) -> Envelope {
        self.inner
    }
}
fn cursor_nat(c: &mut crate::consensus_wire::Cursor<'_>) -> Result<Nat> {
    let mut b = vec![];
    loop {
        let v = c.byte()?;
        b.push(v);
        if v == 255 {
            break;
        }
    }
    let mut r = Reader::new(&b)?;
    let n = r.nat()?;
    r.finish()?;
    Ok(n)
}
/// Endpoint-local private message commitment. Its nonce is sampled before the
/// native INNER credential is signed; public commitment is hiding, not merely a
/// deterministic body hash. No Debug/Clone; durable seal storage freezes it.
pub struct HidingDraft {
    party: CommitteeParty,
    sequence: u64,
    message: Vec<u8>,
    recipient: RecipientSpec,
    hiding_nonce: [u8; 32],
    commitment: [u8; 64],
}
impl HidingDraft {
    pub fn new(
        party: CommitteeParty,
        sequence: u64,
        message: Vec<u8>,
        recipient: RecipientSpec,
    ) -> Result<Self> {
        recipient.validate()?;
        let mut hiding_nonce = [0; 32];
        File::open("/dev/urandom")?.read_exact(&mut hiding_nonce)?;
        Self::from_retained(party, sequence, message, recipient, hiding_nonce)
    }
    pub(crate) fn from_retained(
        party: CommitteeParty,
        sequence: u64,
        message: Vec<u8>,
        recipient: RecipientSpec,
        hiding_nonce: [u8; 32],
    ) -> Result<Self> {
        recipient.validate()?;
        let probe = Envelope {
            party: party.clone(),
            sequence,
            message: message.clone(),
            credential: vec![1],
        };
        probe.encode()?;
        let commitment = semantic_commitment(&hiding_nonce, &probe.signing_bytes());
        Ok(Self {
            party,
            sequence,
            message,
            recipient,
            hiding_nonce,
            commitment,
        })
    }
    pub(crate) fn nonce_for_private_wal(&self) -> [u8; 32] {
        self.hiding_nonce
    }
    pub fn semantic_commitment(&self) -> [u8; 64] {
        self.commitment
    }
    pub fn inner_native_marker(&self) -> Vec<u8> {
        opaque_message_marker(&self.party, self.sequence, &self.commitment)
    }
    pub fn public_draft(&self) -> DraftPublic {
        DraftPublic {
            party: self.party.clone(),
            sequence: self.sequence,
            recipient: self.recipient.clone(),
            semantic_commitment: self.commitment,
        }
    }
    pub fn party(&self) -> &CommitteeParty {
        &self.party
    }
    pub fn sequence(&self) -> u64 {
        self.sequence
    }
    /// Credential must be the actual native INNER opaque-message purpose over
    /// public context+this hiding commitment. This method does not grant it.
    pub fn seal(
        self,
        inner_native_credential: Vec<u8>,
        public_key: &[u8],
    ) -> Result<SealedIngress> {
        if recipient_key_id(public_key) != self.recipient.key_id {
            return Err(bad("recipient public enrollment key binding"));
        }
        let inner = Envelope {
            party: self.party,
            sequence: self.sequence,
            message: self.message,
            credential: inner_native_credential,
        };
        let auth = inner.encode()?;
        if PAD.len() + 36 + auth.len() > self.recipient.plaintext_bound {
            return Err(bad("AUTH exceeds source-pinned padding class"));
        }
        let mut plaintext = PAD.to_vec();
        plaintext.extend((auth.len() as u32).to_le_bytes());
        plaintext.extend(self.hiding_nonce);
        plaintext.extend(auth);
        plaintext.resize(self.recipient.plaintext_bound, 0);
        let mut out = SealedIngress {
            party: inner.party,
            sequence: inner.sequence,
            recipient: self.recipient,
            semantic_commitment: self.commitment,
            hybrid_ciphertext: [0; crypto_transit::HYBRID_CIPHERTEXT_BYTES],
            nonce: [0; 24],
            key_cipher_commitment: [0; 32],
            ciphertext: vec![],
            outer_native_credential: vec![],
        };
        let parts = crypto_transit::seal(
            public_key,
            &out.recipient.epoch_bytes(),
            &out.public_binding(),
            &plaintext,
        )
        .map_err(|_| bad("recipient encryption refused"))?;
        out.hybrid_ciphertext = parts.hybrid_ciphertext;
        out.nonce = parts.nonce;
        out.key_cipher_commitment = parts.commitment;
        out.ciphertext = parts.ciphertext;
        out.encode()?;
        Ok(out)
    }
}

/// Endpoint-owned persistent recipient keys. Honest crash/private disk is the
/// premise; a key record is not member enrollment or source authority. Old keys
/// are retained for old admitted work; rotation never silently selects latest.
#[derive(Clone)]
struct KeyState {
    keys: std::collections::BTreeMap<Nat, (Vec<u8>, Vec<u8>)>,
    capacity: usize,
}
impl crate::transition_journal::Machine for KeyState {
    fn apply(&mut self, event: &[u8]) -> Result<Vec<u8>> {
        let mut c = crate::consensus_wire::Cursor::new(event)?;
        let epoch = cursor_nat(&mut c)?;
        let secret = c.bytes()?;
        let public = c.bytes()?;
        c.finish()?;
        if self.keys.contains_key(&epoch) || self.keys.len() >= self.capacity {
            return Err(bad("recipient key epoch reuse/capacity"));
        }
        crypto_transit::validate_keypair(&secret, &public)
            .map_err(|_| bad("recipient retained generated key pair mismatch"))?;
        self.keys.insert(epoch, (secret, public.clone()));
        Ok(public)
    }
}
pub struct RecipientKeyCustody {
    journal: crate::transition_journal::Journal<KeyState>,
}
pub struct KeyRecord {
    epoch: Nat,
    public_key: Vec<u8>,
}
impl KeyRecord {
    pub fn epoch(&self) -> &Nat {
        &self.epoch
    }
    pub fn public_key(&self) -> &[u8] {
        &self.public_key
    }
    pub fn recipient_spec(&self, plaintext_bound: usize) -> Result<RecipientSpec> {
        let spec = RecipientSpec {
            algorithm: Nat::new(ALGORITHM_HYBRID),
            key_epoch: self.epoch.clone(),
            key_id: recipient_key_id(&self.public_key),
            plaintext_bound,
        };
        spec.validate()?;
        Ok(spec)
    }
}
impl RecipientKeyCustody {
    pub fn open(path: &std::path::Path, endpoint_identity: &[u8], capacity: usize) -> Result<Self> {
        if capacity == 0 || capacity > 65536 || endpoint_identity.is_empty() {
            return Err(bad("recipient key custody public bound/identity"));
        }
        let mut id = b"DREGG.PRIVATE.RECIPIENT.KEY.WAL\x02".to_vec();
        bytes(endpoint_identity, &mut id);
        Nat::new(capacity as u64).put(&mut id);
        Ok(Self {
            journal: crate::transition_journal::Journal::open(
                path,
                &id,
                KeyState {
                    keys: std::collections::BTreeMap::new(),
                    capacity,
                },
            )?,
        })
    }
    /// Generate on the designated endpoint, fsync/read back before publishing
    /// the public enrollment candidate. The source must separately admit it.
    pub fn generate_epoch(&mut self, epoch: Nat) -> Result<KeyRecord> {
        if let Some((_, public_key)) = self.journal.state().keys.get(&epoch) {
            return Ok(KeyRecord {
                epoch,
                public_key: public_key.clone(),
            });
        }
        if self.journal.state().keys.len() >= self.journal.state().capacity {
            return Err(bad("recipient key custody exhausted"));
        }
        let key =
            crypto_transit::generate_keypair().map_err(|_| bad("recipient key generation"))?;
        let mut event = vec![];
        epoch.put(&mut event);
        bytes(&key.secret, &mut event);
        bytes(&key.public, &mut event);
        let public_key = self.journal.append(&event)?;
        Ok(KeyRecord { epoch, public_key })
    }
    /// Exact retained epoch and enrollment key binding, never a latest-key fallback.
    pub fn open_capsule(
        &self,
        capsule: &SealedIngress,
        party: &CommitteeParty,
        sequence: u64,
        expected: &RecipientSpec,
    ) -> Result<DecryptedEnvelope> {
        let (secret, public) = self
            .journal
            .state()
            .keys
            .get(&expected.key_epoch)
            .ok_or_else(|| bad("recipient retained epoch missing"))?;
        if recipient_key_id(public) != expected.key_id {
            return Err(bad("recipient current/retained key enrollment mismatch"));
        }
        capsule.open(secret, public, party, sequence, expected)
    }
}
