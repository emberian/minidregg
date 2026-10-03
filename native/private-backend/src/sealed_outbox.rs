//! Endpoint-private durable drafts/capsules. Nonces, messages and exact ciphertext
//! are committed before offer; duplicate nullifiers return the original bytes.
//! Honest crash WAL only, no native authority or independent rollback claim.
use crate::{
    authenticated_ingress::{CommitteeParty, Outcome},
    codec::{bad, bytes, Nat, Reader},
    consensus_wire::Cursor,
    recipient_seal::{self, DecryptedEnvelope, HidingDraft, RecipientSpec, SealedIngress},
    transition_journal::{Journal, Machine},
};
use sha2::{Digest, Sha512};
use std::{
    collections::BTreeMap,
    io::{Error, ErrorKind, Result},
    path::Path,
};
pub fn nullifier(party: &CommitteeParty, sequence: u64) -> Vec<u8> {
    let mut b = b"DREGG.PRIVATE.SEALED.NULLIFIER\x02".to_vec();
    b.push(party.context.protocol as u8);
    party.context.generation.put(&mut b);
    bytes(&party.context.session, &mut b);
    b.extend(party.party.to_le_bytes());
    b.extend(sequence.to_le_bytes());
    b
}
fn nat(c: &mut Cursor<'_>) -> Result<Nat> {
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
fn put_spec(s: &RecipientSpec, b: &mut Vec<u8>) {
    s.algorithm.put(b);
    s.key_epoch.put(b);
    bytes(&s.key_id, b);
    Nat::new(s.plaintext_bound as u64).put(b);
}
fn get_spec(c: &mut Cursor<'_>) -> Result<RecipientSpec> {
    let s = RecipientSpec {
        algorithm: nat(c)?,
        key_epoch: nat(c)?,
        key_id: c.bytes()?,
        plaintext_bound: usize::try_from(nat(c)?.value()?).map_err(|_| bad("padding bound"))?,
    };
    s.validate()?;
    Ok(s)
}
#[derive(Clone)]
struct Entry {
    party: CommitteeParty,
    sequence: u64,
    message: Vec<u8>,
    recipient: RecipientSpec,
    public_key: Vec<u8>,
    hiding_nonce: [u8; 32],
    commitment: [u8; 64],
    capsule: Option<Vec<u8>>,
    inner_credential: Option<Vec<u8>>,
    final_capsule: Option<Vec<u8>>,
}
impl Entry {
    fn draft(&self) -> Result<HidingDraft> {
        HidingDraft::from_retained(
            self.party.clone(),
            self.sequence,
            self.message.clone(),
            self.recipient.clone(),
            self.hiding_nonce,
        )
    }
}
#[derive(Clone)]
struct State {
    entries: BTreeMap<Vec<u8>, Entry>,
    max_entries: usize,
}
impl Machine for State {
    fn apply(&mut self, event: &[u8]) -> Result<Vec<u8>> {
        let mut c = Cursor::new(event)?;
        match c.byte()? {
            0 => {
                let party = CommitteeParty::decode(&c.bytes()?)?;
                let sequence = c.u64()?;
                let recipient = get_spec(&mut c)?;
                let public_key = c.bytes()?;
                let hiding_nonce = c.take(32)?.try_into().unwrap();
                let message = c.bytes()?;
                c.finish()?;
                let key = nullifier(&party, sequence);
                if self.entries.contains_key(&key) || self.entries.len() >= self.max_entries {
                    return Err(bad("duplicate/capacity draft event"));
                }
                if recipient_seal::recipient_key_id(&public_key) != recipient.key_id {
                    return Err(bad("draft recipient enrollment binding"));
                }
                let draft = HidingDraft::from_retained(
                    party.clone(),
                    sequence,
                    message.clone(),
                    recipient.clone(),
                    hiding_nonce,
                )?;
                let commitment = draft.semantic_commitment();
                self.entries.insert(
                    key,
                    Entry {
                        party,
                        sequence,
                        message,
                        recipient,
                        public_key,
                        hiding_nonce,
                        commitment,
                        capsule: None,
                        inner_credential: None,
                        final_capsule: None,
                    },
                );
                Ok(commitment.to_vec())
            }
            1 => {
                let key = c.bytes()?;
                let credential = c.bytes()?;
                let capsule = c.bytes()?;
                c.finish()?;
                let entry = self
                    .entries
                    .get_mut(&key)
                    .ok_or_else(|| bad("unknown draft"))?;
                let sealed = SealedIngress::decode(&capsule)?;
                if entry.capsule.is_some()
                    || credential.is_empty()
                    || sealed.party != entry.party
                    || sealed.sequence != entry.sequence
                    || sealed.recipient != entry.recipient
                    || sealed.semantic_commitment != entry.commitment
                    || !sealed.outer_native_credential.is_empty()
                {
                    return Err(bad("sealed draft binding/conflicting retry"));
                }
                entry.inner_credential = Some(credential);
                entry.capsule = Some(capsule.clone());
                Ok(capsule)
            }
            2 => {
                let key = c.bytes()?;
                let credential = c.bytes()?;
                c.finish()?;
                let entry = self
                    .entries
                    .get_mut(&key)
                    .ok_or_else(|| bad("unknown outer draft"))?;
                if credential.is_empty() || entry.final_capsule.is_some() {
                    return Err(bad("outer credential duplicate/empty"));
                }
                let raw = entry
                    .capsule
                    .as_ref()
                    .ok_or_else(|| Error::new(ErrorKind::WouldBlock, "inner seal pending"))?;
                let mut sealed = SealedIngress::decode(raw)?;
                sealed.outer_native_credential = credential;
                let final_bytes = sealed.encode()?;
                entry.final_capsule = Some(final_bytes.clone());
                Ok(final_bytes)
            }
            _ => Err(bad("sealed draft event")),
        }
    }
}
/// Typed actual local WAL readback, not current source permission. Hiding nonce
/// and body stay private; public signing targets expose only a hiding commitment.
pub struct DraftReceipt {
    key: Vec<u8>,
    party: CommitteeParty,
    sequence: u64,
    commitment: [u8; 64],
}
impl DraftReceipt {
    pub fn party(&self) -> &CommitteeParty {
        &self.party
    }
    pub fn sequence(&self) -> u64 {
        self.sequence
    }
    pub fn semantic_commitment(&self) -> [u8; 64] {
        self.commitment
    }
}
pub struct Store {
    journal: Journal<State>,
}
impl Store {
    pub fn open(path: &Path, source_identity: &[u8], max_entries: usize) -> Result<Self> {
        if max_entries == 0 || max_entries > 65536 {
            return Err(bad("sealed draft public capacity"));
        }
        let mut id = b"DREGG.PRIVATE.SEALED.OUTBOX.WAL\x02".to_vec();
        bytes(source_identity, &mut id);
        Nat::new(max_entries as u64).put(&mut id);
        Ok(Self {
            journal: Journal::open(
                path,
                &id,
                State {
                    entries: BTreeMap::new(),
                    max_entries,
                },
            )?,
        })
    }
    pub fn prepare(
        &mut self,
        party: CommitteeParty,
        sequence: u64,
        message: Vec<u8>,
        recipient: RecipientSpec,
        public_key: Vec<u8>,
    ) -> Result<DraftReceipt> {
        let key = nullifier(&party, sequence);
        if let Some(old) = self.journal.state().entries.get(&key) {
            if old.party != party
                || old.message != message
                || old.recipient != recipient
                || old.public_key != public_key
            {
                return Err(bad("public nullifier body/recipient/key conflict"));
            }
            return Ok(DraftReceipt {
                key,
                party,
                sequence,
                commitment: old.commitment,
            });
        }
        let draft = HidingDraft::new(party.clone(), sequence, message.clone(), recipient.clone())?;
        let mut event = vec![0];
        bytes(&party.encode(), &mut event);
        event.extend(sequence.to_le_bytes());
        put_spec(&recipient, &mut event);
        bytes(&public_key, &mut event);
        event.extend(draft.nonce_for_private_wal());
        bytes(&message, &mut event);
        self.journal.append(&event)?;
        let actual = &self.journal.state().entries[&key];
        Ok(DraftReceipt {
            key,
            party,
            sequence,
            commitment: actual.commitment,
        })
    }
    /// Actual caller-provided native INNER credential still needs source
    /// verification. No permission is inferred from this byte attachment.
    pub fn seal(
        &mut self,
        receipt: &DraftReceipt,
        inner_native_credential: Vec<u8>,
    ) -> Result<Vec<u8>> {
        let entry = self
            .journal
            .state()
            .entries
            .get(&receipt.key)
            .ok_or_else(|| bad("draft receipt scope"))?;
        if entry.commitment != receipt.commitment {
            return Err(bad("draft receipt semantic scope"));
        }
        if let Some(raw) = &entry.capsule {
            return Ok(raw.clone());
        }
        let sealed = entry
            .draft()?
            .seal(inner_native_credential.clone(), &entry.public_key)?;
        let raw = sealed.encode()?;
        let mut event = vec![1];
        bytes(&receipt.key, &mut event);
        bytes(&inner_native_credential, &mut event);
        bytes(&raw, &mut event);
        self.journal.append(&event)
    }
    pub fn attach_outer(
        &mut self,
        receipt: &DraftReceipt,
        outer_native_credential: Vec<u8>,
    ) -> Result<Vec<u8>> {
        let entry = self
            .journal
            .state()
            .entries
            .get(&receipt.key)
            .ok_or_else(|| bad("draft outer receipt scope"))?;
        if entry.commitment != receipt.commitment {
            return Err(bad("draft outer semantic scope"));
        }
        if let Some(raw) = &entry.final_capsule {
            return Ok(raw.clone());
        }
        let mut event = vec![2];
        bytes(&receipt.key, &mut event);
        bytes(&outer_native_credential, &mut event);
        self.journal.append(&event)
    }
    /// Bind every retained ciphertext to the ACTUAL recursive protocol outbox,
    /// in its original order, before constructing a progress witness. Source
    /// enrollment/native credentials remain independently checked permissions.
    pub fn batch_for_outcome(
        &self,
        outcome: &Outcome,
        opened: &DecryptedEnvelope,
        receipts: &[&DraftReceipt],
    ) -> Result<SealedBatchReceipt> {
        if outcome.progress_claim().signing_bytes != opened.inner().signing_bytes() {
            return Err(bad("outbox original received protocol binding"));
        }
        let mut cursor = Cursor::new(outcome.outbox())?;
        let count = usize::try_from(nat(&mut cursor)?.value()?).map_err(|_| bad("outbox count"))?;
        if count != receipts.len() || count > 65536 {
            return Err(bad("actual recursive outbox count"));
        }
        let mut bytes_out = vec![];
        Nat::new(count as u64).put(&mut bytes_out);
        let mut keys = std::collections::BTreeSet::new();
        let original = &opened.inner().party.context;
        for receipt in receipts {
            let to = cursor.u16()?;
            let message = cursor.bytes()?;
            if !keys.insert(&receipt.key) {
                return Err(bad("sealed outbox row alias"));
            }
            let entry = self
                .journal
                .state()
                .entries
                .get(&receipt.key)
                .ok_or_else(|| bad("sealed batch draft scope"))?;
            let c = &entry.party.context;
            if entry.commitment != receipt.commitment
                || entry.message != message
                || c.recipient != to
                || entry.party.party != original.recipient
                || c.protocol != original.protocol
                || c.generation != original.generation
                || c.authority_epoch != original.authority_epoch
                || c.session != original.session
            {
                return Err(bad("sealed actual outbox body/recipient/context mismatch"));
            }
            let raw = entry
                .final_capsule
                .as_ref()
                .ok_or_else(|| Error::new(ErrorKind::WouldBlock, "outer credential pending"))?;
            bytes(raw, &mut bytes_out);
        }
        cursor.finish()?;
        if bytes_out.len() > crate::codec::MAX {
            return Err(bad("sealed batch fixed capacity"));
        }
        Ok(SealedBatchReceipt {
            capsules: bytes_out,
            count: count as u64,
            original_outbox: outcome.outbox().to_vec(),
            received_semantic: opened.inner().signing_bytes(),
        })
    }
}
/// Private actual sealed-WAL producer. Raw network decode cannot construct this.
pub struct SealedBatchReceipt {
    capsules: Vec<u8>,
    count: u64,
    original_outbox: Vec<u8>,
    received_semantic: Vec<u8>,
}
impl SealedBatchReceipt {
    pub fn capsule_bytes(&self) -> &[u8] {
        &self.capsules
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgressDigestClaim {
    pub semantic_commitment: [u8; 64],
    pub sealed_outbox_digest: [u8; 64],
    pub sealed_outbox_bytes: u64,
    pub public_message_count: u64,
}
impl ProgressDigestClaim {
    pub fn encode(&self) -> Result<Vec<u8>> {
        if self.sealed_outbox_bytes > crate::codec::MAX as u64 || self.public_message_count > 65536
        {
            return Err(bad("sealed progress public capacity"));
        }
        let mut b = b"DREGG.PRIVATE.PROTOCOL.PROGRESS\x02".to_vec();
        b.extend(self.semantic_commitment);
        b.extend(self.sealed_outbox_digest);
        b.extend(self.sealed_outbox_bytes.to_le_bytes());
        b.extend(self.public_message_count.to_le_bytes());
        Ok(b)
    }
    pub fn decode(b: &[u8]) -> Result<Self> {
        let frame = b"DREGG.PRIVATE.PROTOCOL.PROGRESS\x02";
        let mut c = Cursor::new(b)?;
        if c.take(frame.len())? != frame {
            return Err(bad("sealed progress frame"));
        }
        let out = Self {
            semantic_commitment: c.take(64)?.try_into().unwrap(),
            sealed_outbox_digest: c.take(64)?.try_into().unwrap(),
            sealed_outbox_bytes: c.u64()?,
            public_message_count: c.u64()?,
        };
        c.finish()?;
        if out.encode()? != b {
            return Err(bad("sealed progress canonical"));
        }
        Ok(out)
    }
}
pub struct ActualProgress {
    claim: ProgressDigestClaim,
}
impl ActualProgress {
    /// ONLY actual protocol WAL outcome + actual sealed outbox WAL batch +
    /// recipient-only decryption witness. Body/signing hash is never published.
    /// Source current/funded admission remains separate. Exact body/recipient
    /// mapping is checked by batch_for_outcome against retained private WAL.
    pub fn new(
        outcome: &Outcome,
        opened: &DecryptedEnvelope,
        sealed: &SealedBatchReceipt,
    ) -> Result<Self> {
        let raw = outcome.progress_claim();
        if raw.signing_bytes != opened.inner().signing_bytes()
            || sealed.received_semantic != raw.signing_bytes
            || sealed.original_outbox != outcome.outbox()
        {
            return Err(bad("sealed progress actual protocol binding"));
        }
        // Digest ciphertext, never low-entropy plaintext outbox. Count/shape
        // belong to an explicitly public fixed protocol profile.
        let mut bound = b"DREGG.PRIVATE.SEALED.OUTBOX.COMMIT\x02".to_vec();
        bytes(&sealed.capsules, &mut bound);
        Ok(Self {
            claim: ProgressDigestClaim {
                semantic_commitment: opened.semantic_commitment(),
                sealed_outbox_digest: Sha512::digest(bound).into(),
                sealed_outbox_bytes: sealed.capsules.len() as u64,
                public_message_count: sealed.count,
            },
        })
    }
    pub fn claim(&self) -> &ProgressDigestClaim {
        &self.claim
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        authenticated_ingress::{Context, Envelope, Protocol, Receiver, SourcePartyAuthority},
        codec::Generation,
        crypto_transit,
        recipient_seal::{semantic_commitment, RecipientKeyCustody},
    };
    use std::{
        fs,
        time::{SystemTime, UNIX_EPOCH},
    };
    fn path(label: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "mini-sealed-{label}-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&dir).unwrap();
        dir.join("wal")
    }
    fn party(protocol: Protocol, sender: u16, recipient: u16) -> CommitteeParty {
        CommitteeParty {
            context: Context {
                protocol,
                generation: Generation {
                    invocation: Nat::from_be(&[255; 32]),
                    command: vec![3],
                    attempt: Nat::new(7),
                    generation: Nat::new(11),
                    configuration: Nat::from_be(&[254; 32]),
                },
                authority_epoch: Nat::new(9),
                session: vec![23; 32],
                recipient,
                recipient_role: b"backend-party".to_vec(),
            },
            party: sender,
            subject: format!("independent-party-{sender}").into_bytes(),
            key_epoch: Nat::new(3),
            key_binding: vec![sender as u8 + 7; 32],
            credential_purpose: b"inner-opaque-message".to_vec(),
        }
    }
    fn spec(public: &[u8]) -> RecipientSpec {
        RecipientSpec {
            algorithm: Nat::new(1),
            key_epoch: Nat::from_be(&[255; 32]),
            key_id: recipient_seal::recipient_key_id(public),
            plaintext_bound: 4096,
        }
    }
    fn contains(hay: &[u8], needle: &[u8]) -> bool {
        hay.windows(needle.len()).any(|w| w == needle)
    }
    #[test]
    fn real_recipient_capsule_rejects_wrong_key_epoch_party_sequence_and_tamper() {
        let k = crypto_transit::generate_keypair().unwrap();
        let other = crypto_transit::generate_keypair().unwrap();
        let p = party(Protocol::PrivateSend, 1, 2);
        let sp = spec(&k.public);
        let message = b"LOW_ENTROPY_PRIVATE_SHARE_00000000".to_vec();
        let d = HidingDraft::new(p.clone(), 7, message.clone(), sp.clone()).unwrap();
        let commitment = d.semantic_commitment();
        let sealed = d.seal(vec![1; 32], &k.public).unwrap();
        let raw = sealed.encode().unwrap();
        assert!(!contains(&raw, &message));
        let opened = sealed.open(&k.secret, &k.public, &p, 7, &sp).unwrap();
        assert_eq!(opened.inner().message, message);
        assert_eq!(opened.semantic_commitment(), commitment);
        // Chosen low-entropy candidate hashes cannot test the PUBLIC commitment
        // without the endpoint-only 256-bit hiding nonce.
        for v in 0..256u16 {
            let e = Envelope {
                party: p.clone(),
                sequence: 7,
                message: vec![v as u8; 32],
                credential: vec![],
            };
            assert_ne!(
                semantic_commitment(&[0; 32], &e.signing_bytes()),
                commitment
            );
        }
        assert_ne!(
            semantic_commitment(&[0; 32], &opened.inner().signing_bytes()),
            commitment
        );
        assert!(sealed.open(&other.secret, &k.public, &p, 7, &sp).is_err());
        let mut epoch = sp.clone();
        epoch.key_epoch = Nat::new(4);
        assert!(sealed.open(&k.secret, &k.public, &p, 7, &epoch).is_err());
        let mut wrong = p.clone();
        wrong.context.recipient = 3;
        assert!(sealed.open(&k.secret, &k.public, &wrong, 7, &sp).is_err());
        let mut wrong = p.clone();
        wrong.context.protocol = Protocol::Dzk;
        assert!(sealed.open(&k.secret, &k.public, &wrong, 7, &sp).is_err());
        assert!(sealed.open(&k.secret, &k.public, &p, 8, &sp).is_err());
        for field in 0..5 {
            let mut bad = sealed.clone();
            match field {
                0 => bad.kem_ciphertext[0] ^= 1,
                1 => bad.nonce[0] ^= 1,
                2 => bad.key_cipher_commitment[0] ^= 1,
                3 => bad.ciphertext[0] ^= 1,
                _ => bad.semantic_commitment[0] ^= 1,
            }
            assert!(bad.open(&k.secret, &k.public, &p, 7, &sp).is_err());
        }
        let mut suffix = raw;
        suffix.push(0);
        assert!(SealedIngress::decode(&suffix).is_err());
    }
    #[test]
    fn recipient_key_and_cached_ciphertext_survive_rotation_restart_and_torn_outer_tail() {
        let kp = path("keys");
        let wp = path("drafts");
        let p = party(Protocol::PrivateSend, 1, 2);
        let (public, sp, raw, commitment, outer_start);
        {
            let mut custody = RecipientKeyCustody::open(&kp, b"party-2", 3).unwrap();
            let key = custody.generate_epoch(Nat::new(7)).unwrap();
            public = key.public_key().to_vec();
            sp = key.recipient_spec(4096).unwrap();
            let mut store = Store::open(&wp, b"party-1", 4).unwrap();
            let receipt = store
                .prepare(p.clone(), 9, vec![42; 32], sp.clone(), public.clone())
                .unwrap();
            commitment = receipt.semantic_commitment();
            raw = store.seal(&receipt, vec![3; 32]).unwrap();
            assert_eq!(store.seal(&receipt, vec![4; 32]).unwrap(), raw);
            outer_start = fs::metadata(&wp).unwrap().len();
            store.attach_outer(&receipt, vec![8; 32]).unwrap();
            custody.generate_epoch(Nat::new(8)).unwrap();
        }
        // Simulate an incomplete UNRELEASED outer attachment. Retained sealed
        // bytes from the completed prior event must not be rerandomized.
        let n = fs::metadata(&wp).unwrap().len();
        fs::OpenOptions::new()
            .write(true)
            .open(&wp)
            .unwrap()
            .set_len(n - 1)
            .unwrap();
        let mut store = Store::open(&wp, b"party-1", 4).unwrap();
        assert_eq!(fs::metadata(&wp).unwrap().len(), outer_start);
        let r = store
            .prepare(p.clone(), 9, vec![42; 32], sp.clone(), public.clone())
            .unwrap();
        assert_eq!(r.semantic_commitment(), commitment);
        assert_eq!(store.seal(&r, vec![99; 32]).unwrap(), raw);
        let final_raw = store.attach_outer(&r, vec![8; 32]).unwrap();
        assert_eq!(store.attach_outer(&r, vec![9; 32]).unwrap(), final_raw);
        assert!(store
            .prepare(p.clone(), 9, vec![43; 32], sp.clone(), public.clone())
            .is_err());
        let mut another = p.clone();
        another.context.recipient = 3;
        assert!(store
            .prepare(another, 9, vec![42; 32], sp.clone(), public.clone())
            .is_err());
        let mut custody = RecipientKeyCustody::open(&kp, b"party-2", 3).unwrap();
        assert_eq!(
            custody.generate_epoch(Nat::new(7)).unwrap().public_key(),
            public
        );
        let sealed = SealedIngress::decode(&final_raw).unwrap();
        assert_eq!(
            custody
                .open_capsule(&sealed, &p, 9, &sp)
                .unwrap()
                .inner()
                .message,
            vec![42; 32]
        );
        let rotated = custody
            .generate_epoch(Nat::new(8))
            .unwrap()
            .recipient_spec(4096)
            .unwrap();
        assert!(custody.open_capsule(&sealed, &p, 9, &rotated).is_err());
    }
    // Native source admission is NOT implemented by this fixture. It models a
    // separately authorized opaque commitment signature inside the endpoint.
    struct OpaqueFixture {
        party: CommitteeParty,
        nonce: [u8; 32],
        key: [u8; 32],
    }
    fn sign(key: &[u8; 32], commitment: &[u8; 64]) -> Vec<u8> {
        ring::hmac::sign(
            &ring::hmac::Key::new(ring::hmac::HMAC_SHA256, key),
            commitment,
        )
        .as_ref()
        .to_vec()
    }
    impl SourcePartyAuthority for OpaqueFixture {
        fn verify_enrolled_packet(
            &self,
            p: &CommitteeParty,
            body: &[u8],
            credential: &[u8],
        ) -> Result<()> {
            if p != &self.party {
                return Err(bad("fixture enrollment"));
            }
            let c = semantic_commitment(&self.nonce, body);
            ring::hmac::verify(
                &ring::hmac::Key::new(ring::hmac::HMAC_SHA256, &self.key),
                &c,
                credential,
            )
            .map_err(|_| bad("fixture opaque commitment signature"))
        }
    }
    #[test]
    fn actual_private_share_bidirectional_transit_capture_and_exact_outbox_binding() {
        use crate::{
            asks::{self, PhaseMessage},
            private_send::{Body, Message, PrivateSend},
            private_send_store::{encode_message, DeliveryMachine},
            reconstruction::Field,
        };
        let p = party(Protocol::PrivateSend, 1, 2);
        let g = &p.context.generation;
        let mut dealer = PrivateSend::new(1, 1, 4, 1, g, 64).unwrap();
        let packets = dealer
            .dealer_with_coefficients(
                &[31; 64],
                &[vec![Field(42), Field(7)], vec![Field(91), Field(11)]],
            )
            .unwrap();
        let share = packets
            .iter()
            .find(|p| {
                p.to == 2
                    && matches!(
                        &p.message.body,
                        Body::Key(asks::Message {
                            body: asks::Body::PrivateShare(_),
                            ..
                        })
                    )
            })
            .unwrap()
            .message
            .clone();
        let message = encode_message(&share);
        let (instance, commit_bytes) = packets
            .iter()
            .find_map(|p| match &p.message.body {
                Body::Key(asks::Message {
                    instance,
                    body: asks::Body::Commit(PhaseMessage::Init(b)),
                }) => Some((*instance, b.clone())),
                _ => None,
            })
            .unwrap();
        // Actual prior PUBLIC RBC prefix, before this one sealed private-share
        // exchange. No private share or backend result is supplied by a callback.
        let mut state = PrivateSend::new(2, 1, 4, 1, g, 64).unwrap();
        for from in [1, 2, 3] {
            for phase in [
                PhaseMessage::Echo(commit_bytes.clone()),
                PhaseMessage::Ready(commit_bytes.clone()),
            ] {
                state
                    .receive(
                        from,
                        Message {
                            context: state.context,
                            body: Body::Key(asks::Message {
                                instance,
                                body: asks::Body::Commit(phase),
                            }),
                        },
                    )
                    .unwrap();
            }
        }
        let mut keys: Vec<_> = (0..4)
            .map(|_| crypto_transit::generate_keypair().unwrap())
            .collect();
        let sp = spec(&keys[2].public);
        let mut sender = Store::open(&path("sender"), b"sender-1", 32).unwrap();
        let draft = sender
            .prepare(
                p.clone(),
                0,
                message.clone(),
                sp.clone(),
                keys[2].public.clone(),
            )
            .unwrap();
        let credential = sign(&[7; 32], &draft.semantic_commitment());
        let capsule = sender.seal(&draft, credential).unwrap();
        let offered = sender.attach_outer(&draft, vec![17; 32]).unwrap();
        let public_capsule = SealedIngress::decode(&offered).unwrap();
        let opened = public_capsule
            .open(&keys[2].secret, &keys[2].public, &p, 0, &sp)
            .unwrap();
        let fixture = OpaqueFixture {
            party: p.clone(),
            nonce: *opened.hiding_nonce(),
            key: [7; 32],
        };
        let mut receiver = Receiver::open(
            &path("receiver"),
            p.context.clone(),
            4,
            32,
            DeliveryMachine { state },
        )
        .unwrap();
        let outcome = receiver
            .receive(&fixture, &opened.inner().encode().unwrap())
            .unwrap();
        assert!(outcome.outbox().len() > 2);
        let mut cursor = Cursor::new(outcome.outbox()).unwrap();
        let count = nat(&mut cursor).unwrap().value().unwrap();
        assert_eq!(count, 4);
        let mut outgoing = Store::open(&path("outgoing"), b"party-2", 32).unwrap();
        let mut receipts = vec![];
        let mut captured = vec![offered.clone()];
        let mut outgoing_messages = vec![];
        for seq in 1..=count {
            let to = cursor.u16().unwrap();
            let m = cursor.bytes().unwrap();
            let op = party(Protocol::PrivateSend, 2, to);
            let os = spec(&keys[to as usize].public);
            let receipt = outgoing
                .prepare(
                    op.clone(),
                    seq,
                    m.clone(),
                    os.clone(),
                    keys[to as usize].public.clone(),
                )
                .unwrap();
            outgoing.seal(&receipt, vec![7; 32]).unwrap();
            let final_raw = outgoing.attach_outer(&receipt, vec![17; 32]).unwrap();
            let decoded = SealedIngress::decode(&final_raw).unwrap();
            assert_eq!(
                decoded
                    .open(
                        &keys[to as usize].secret,
                        &keys[to as usize].public,
                        &op,
                        seq,
                        &os
                    )
                    .unwrap()
                    .inner()
                    .message,
                m
            );
            outgoing_messages.push(m);
            captured.push(final_raw);
            receipts.push(receipt);
        }
        cursor.finish().unwrap();
        let refs: Vec<_> = receipts.iter().collect();
        let batch = outgoing
            .batch_for_outcome(&outcome, &opened, &refs)
            .unwrap();
        let progress = ActualProgress::new(&outcome, &opened, &batch)
            .unwrap()
            .claim()
            .encode()
            .unwrap();
        assert_eq!(
            ProgressDigestClaim::decode(&progress)
                .unwrap()
                .public_message_count,
            4
        );
        captured.push(progress.clone());
        // Public refusal/debug traces carry only fixed classification, never
        // a returned Debug representation of decrypted AUTH or its private WAL.
        let mut tampered = public_capsule.clone();
        tampered.ciphertext[0] ^= 1;
        let refusal = tampered
            .open(&keys[2].secret, &keys[2].public, &p, 0, &sp)
            .err()
            .unwrap()
            .to_string()
            .into_bytes();
        captured.push(refusal);
        for wire in &captured {
            assert!(!contains(wire, &message));
            assert!(!contains(wire, &opened.inner().signing_bytes()));
            assert!(!contains(wire, opened.hiding_nonce()));
        }
        assert_ne!(progress, outcome.progress_claim().encode().unwrap());
        assert!(ProgressDigestClaim::decode(&outcome.progress_claim().encode().unwrap()).is_err());
        // A separately retained/sealed wrong body, wrong destination or reversed
        // order may not certify the actual protocol outbox.
        let mut reversed = refs.clone();
        reversed.reverse();
        assert!(outgoing
            .batch_for_outcome(&outcome, &opened, &reversed)
            .is_err());
        assert!(outgoing
            .batch_for_outcome(&outcome, &opened, &refs[..3])
            .is_err());
        let wrong = outgoing
            .prepare(
                party(Protocol::PrivateSend, 2, 0),
                99,
                vec![0; 32],
                spec(&keys[0].public),
                keys[0].public.clone(),
            )
            .unwrap();
        outgoing.seal(&wrong, vec![7; 32]).unwrap();
        outgoing.attach_outer(&wrong, vec![17; 32]).unwrap();
        let mut bogus = refs;
        bogus[0] = &wrong;
        assert!(outgoing
            .batch_for_outcome(&outcome, &opened, &bogus)
            .is_err());
        assert_eq!(sender.seal(&draft, vec![22; 32]).unwrap(), capsule);
        // Explicitly declared leakage here: public committee/context, message
        // count/padding class. This test is not native funded admission or MPC.
        keys.clear();
    }
}
