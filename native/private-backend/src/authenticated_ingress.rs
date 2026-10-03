//! End-to-end enrolled-party packets for shuffled opaque transport.
//! No mix slot is a sender. Production signatures and current subject enrollment
//! come from SourcePartyAuthority on one actual native source snapshot.
//! The trait is an integration seam, not an implemented source authority.
//! Replay/protocol/outbox commit atomically in the existing honest-crash WAL.
//! Relays see only the externally encrypted opaque carrier; this codec is not encryption.
use crate::{
    codec::{bad, bytes, Generation, Nat, Reader},
    consensus_wire::Cursor,
    transition_journal::{Journal, Machine},
};
use std::{collections::BTreeMap, io::Result, path::Path};
pub const MAX_PACKET: usize = 131072;
pub const MAX_CARRIER: usize = 131100;
const PARTY: &[u8] = b"DREGG.PRIVATE.COMMITTEE.PARTY\x01";
const AUTH: &[u8] = b"DREGG.PRIVATE.AUTH\x01";
const SIGN: &[u8] = b"DREGG.PRIVATE.AUTH.SIGN\x01";
const INGRESS: &[u8] = b"DREGG.PRIVATE.INGRESS\x01";
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Protocol {
    Acs = 0,
    PrivateSend = 1,
    AcssId = 2,
    Dzk = 3,
    FieldNetwork = 4,
    PrivateOutput = 5,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    pub protocol: Protocol,
    pub generation: Generation,
    pub authority_epoch: Nat,
    pub session: Vec<u8>,
    pub recipient: u16,
    pub recipient_role: Vec<u8>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommitteeParty {
    pub context: Context,
    pub party: u16,
    pub subject: Vec<u8>,
    pub key_epoch: Nat,
    pub key_binding: Vec<u8>,
    pub credential_purpose: Vec<u8>,
}
impl CommitteeParty {
    pub fn encode(&self) -> Vec<u8> {
        let mut b = PARTY.to_vec();
        b.push(self.context.protocol as u8);
        let mut g = vec![];
        self.context.generation.put(&mut g);
        bytes(&g, &mut b);
        self.context.authority_epoch.put(&mut b);
        bytes(&self.context.session, &mut b);
        b.extend(self.party.to_le_bytes());
        b.extend(self.context.recipient.to_le_bytes());
        bytes(&self.context.recipient_role, &mut b);
        bytes(&self.subject, &mut b);
        self.key_epoch.put(&mut b);
        bytes(&self.key_binding, &mut b);
        bytes(&self.credential_purpose, &mut b);
        b
    }
    pub fn decode(b: &[u8]) -> Result<Self> {
        let mut c = Cursor::new(b)?;
        if c.take(PARTY.len())? != PARTY {
            return Err(bad("party record domain"));
        }
        let protocol = match c.byte()? {
            0 => Protocol::Acs,
            1 => Protocol::PrivateSend,
            2 => Protocol::AcssId,
            3 => Protocol::Dzk,
            4 => Protocol::FieldNetwork,
            5 => Protocol::PrivateOutput,
            _ => return Err(bad("protocol tag")),
        };
        let g = c.bytes()?;
        let mut r = Reader::new(&g)?;
        let generation = Generation::get(&mut r)?;
        r.finish()?;
        let authority_epoch = get_nat(&mut c)?;
        let session = c.bytes()?;
        let party = c.u16()?;
        let recipient = c.u16()?;
        let recipient_role = c.bytes()?;
        let subject = c.bytes()?;
        let key_epoch = get_nat(&mut c)?;
        let key_binding = c.bytes()?;
        let credential_purpose = c.bytes()?;
        c.finish()?;
        let v = Self {
            context: Context {
                protocol,
                generation,
                authority_epoch,
                session,
                recipient,
                recipient_role,
            },
            party,
            subject,
            key_epoch,
            key_binding,
            credential_purpose,
        };
        if v.encode() != b
            || v.context.session.is_empty()
            || v.context.recipient_role.is_empty()
            || v.subject.is_empty()
            || v.key_binding.is_empty()
            || v.credential_purpose.is_empty()
        {
            return Err(bad("noncanonical/empty enrolled context"));
        }
        Ok(v)
    }
}
fn get_nat(c: &mut Cursor<'_>) -> Result<Nat> {
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Envelope {
    pub party: CommitteeParty,
    pub sequence: u64,
    pub message: Vec<u8>,
    pub credential: Vec<u8>,
}
impl Envelope {
    pub fn signing_bytes(&self) -> Vec<u8> {
        let mut b = SIGN.to_vec();
        bytes(&self.party.encode(), &mut b);
        b.extend(self.sequence.to_le_bytes());
        bytes(&self.message, &mut b);
        b
    }
    pub fn encode(&self) -> Result<Vec<u8>> {
        let mut b = AUTH.to_vec();
        bytes(&self.party.encode(), &mut b);
        b.extend(self.sequence.to_le_bytes());
        bytes(&self.message, &mut b);
        bytes(&self.credential, &mut b);
        if b.len() > MAX_PACKET {
            return Err(bad("authenticated packet capacity"));
        }
        Ok(b)
    }
    pub fn decode(b: &[u8]) -> Result<Self> {
        if b.len() > MAX_PACKET {
            return Err(bad("authenticated packet capacity"));
        }
        let mut c = Cursor::new(b)?;
        if c.take(AUTH.len())? != AUTH {
            return Err(bad("authenticated packet domain"));
        }
        let party = CommitteeParty::decode(&c.bytes()?)?;
        let sequence = c.u64()?;
        let message = c.bytes()?;
        let credential = c.bytes()?;
        c.finish()?;
        let v = Self {
            party,
            sequence,
            message,
            credential,
        };
        if v.message.is_empty() || v.credential.is_empty() || v.encode()? != b {
            return Err(bad("authenticated packet canonical/empty"));
        }
        Ok(v)
    }
}
/// Implement using actual NativeHost.Opened + source-owned CommitteeParty
/// selection + current CredentialSignatureAdmission.verifyNative on that SAME
/// source snapshot, exact purpose and exact signing bytes. A raw record/key list,
/// successful mix admission or caller boolean is not an implementation.
/// Captured old-epoch liabilities require their separate governed promise path.
pub trait SourcePartyAuthority {
    fn verify_enrolled_packet(
        &self,
        party: &CommitteeParty,
        signing_bytes: &[u8],
        credential: &[u8],
    ) -> Result<()>;
}
pub struct VerifiedPacket {
    envelope: Envelope,
    canonical: Vec<u8>,
}
impl VerifiedPacket {
    pub fn sender(&self) -> u16 {
        self.envelope.party.party
    }
    pub fn message(&self) -> &[u8] {
        &self.envelope.message
    }
}
pub fn verify_packet<A: SourcePartyAuthority>(
    expected: &Context,
    n: usize,
    authority: &A,
    b: &[u8],
) -> Result<VerifiedPacket> {
    let envelope = Envelope::decode(b)?;
    if envelope.party.context != *expected
        || envelope.party.party as usize >= n
        || expected.recipient as usize >= n
        || n == 0
        || n > 16
    {
        return Err(bad(
            "wrong protocol/configuration/epoch/session/party/recipient",
        ));
    }
    authority.verify_enrolled_packet(
        &envelope.party,
        &envelope.signing_bytes(),
        &envelope.credential,
    )?;
    Ok(VerifiedPacket {
        envelope,
        canonical: b.to_vec(),
    })
}
/// Carrier for a separately source-approved native ingress operation. Existing
/// ordinary Host public_envelope does NOT currently admit or dispatch this frame.
pub fn carrier(envelope: &[u8]) -> Result<Vec<u8>> {
    Envelope::decode(envelope)?;
    let mut b = INGRESS.to_vec();
    bytes(envelope, &mut b);
    if b.len() > MAX_CARRIER {
        return Err(bad("ingress carrier capacity"));
    }
    Ok(b)
}
pub fn public_ingress_gate(b: &[u8]) -> Result<Vec<u8>> {
    if b.len() > MAX_CARRIER {
        return Err(bad("ingress carrier capacity"));
    }
    let mut c = Cursor::new(b)?;
    if c.take(INGRESS.len())? != INGRESS {
        return Err(bad("ingress operation"));
    }
    let e = c.bytes()?;
    c.finish()?;
    Envelope::decode(&e)?;
    if carrier(&e)? != b {
        return Err(bad("ingress carrier canonical"));
    }
    Ok(e)
}
#[derive(Clone)]
struct ReplayEntry {
    semantic: Vec<u8>,
    outbox: Vec<u8>,
}
#[derive(Clone)]
struct AuthenticatedMachine<M: Machine> {
    inner: M,
    context: Context,
    n: usize,
    capacity_per_party: usize,
    accepted: BTreeMap<(u16, u64), ReplayEntry>,
}
impl<M: Machine> Machine for AuthenticatedMachine<M> {
    fn apply(&mut self, event: &[u8]) -> Result<Vec<u8>> {
        // Events are PRIVATE WAL records previously verified at receive().
        // Honest crash storage is the premise; checksum is not an authenticator.
        let envelope = Envelope::decode(event)?;
        if envelope.party.context != self.context || envelope.party.party as usize >= self.n {
            return Err(bad("WAL context"));
        }
        let id = (envelope.party.party, envelope.sequence);
        if let Some(old) = self.accepted.get(&id) {
            if old.semantic != envelope.signing_bytes() {
                return Err(bad("conflicting replay"));
            }
            return Ok(old.outbox.clone());
        }
        // A sender-selected sequence may consume only that party's funded quota.
        // Retain old IDs: deleting them would allow a replay to reapply effects.
        if self
            .accepted
            .keys()
            .filter(|(sender, _)| *sender == envelope.party.party)
            .count()
            >= self.capacity_per_party
        {
            return Err(bad("funded ingress party replay capacity exhausted"));
        }
        let mut e = vec![2];
        e.extend(envelope.party.party.to_le_bytes());
        bytes(&envelope.message, &mut e);
        let outbox = self.inner.apply(&e)?;
        self.accepted.insert(
            id,
            ReplayEntry {
                semantic: envelope.signing_bytes(),
                outbox: outbox.clone(),
            },
        );
        Ok(outbox)
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Disposition {
    Applied,
    Replayed,
}
pub struct Outcome {
    pub disposition: Disposition,
    outbox: Vec<u8>,
    semantic: Vec<u8>,
}

/// Bounded actual backend progress ABI. It is NOT source admission, a funded
/// receipt, terminal MPC output or a Qualified successor. A native source endpoint
/// must bind this exact frame to its original typed Pending/Appended authority.
/// Full recursive outbox remains private WAL state and is fetched per message.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgressClaim {
    pub signing_bytes: Vec<u8>,
    pub outbox_digest: [u8; 32],
    pub outbox_bytes: u64,
}
impl ProgressClaim {
    pub fn encode(&self) -> Result<Vec<u8>> {
        let mut b = b"DREGG.PRIVATE.PROTOCOL.PROGRESS\x01".to_vec();
        bytes(&self.signing_bytes, &mut b);
        b.extend(self.outbox_digest);
        b.extend(self.outbox_bytes.to_le_bytes());
        if b.len() > MAX_CARRIER {
            return Err(bad("progress capacity"));
        }
        Ok(b)
    }
    pub fn decode(b: &[u8]) -> Result<Self> {
        if b.len() > MAX_CARRIER {
            return Err(bad("progress capacity"));
        }
        let mut c = Cursor::new(b)?;
        let frame = b"DREGG.PRIVATE.PROTOCOL.PROGRESS\x01";
        if c.take(frame.len())? != frame {
            return Err(bad("progress domain"));
        }
        let signing_bytes = c.bytes()?;
        let outbox_digest = c.fixed32()?;
        let outbox_bytes = c.u64()?;
        c.finish()?;
        let v = Self {
            signing_bytes,
            outbox_digest,
            outbox_bytes,
        };
        let mut body = Cursor::new(&v.signing_bytes)?;
        if body.take(SIGN.len())? != SIGN {
            return Err(bad("progress signing domain"));
        }
        let party = CommitteeParty::decode(&body.bytes()?)?;
        let sequence = body.u64()?;
        let message = body.bytes()?;
        body.finish()?;
        let semantic = Envelope {
            party,
            sequence,
            message,
            credential: vec![],
        };
        if semantic.message.is_empty() || semantic.signing_bytes() != v.signing_bytes {
            return Err(bad("progress semantic binding"));
        }
        if v.encode()? != b || v.outbox_bytes > crate::codec::MAX as u64 {
            return Err(bad("progress canonical/outbox capacity"));
        }
        Ok(v)
    }
}
impl Outcome {
    pub fn outbox(&self) -> &[u8] {
        &self.outbox
    }
    pub fn into_outbox(self) -> Vec<u8> {
        self.outbox
    }
    pub fn progress_claim(&self) -> ProgressClaim {
        ProgressClaim {
            signing_bytes: self.semantic.clone(),
            outbox_digest: crate::custody::hash(&self.outbox),
            outbox_bytes: self.outbox.len() as u64,
        }
    }
}

/// The chosen endpoint must be tied to the ACTUAL protocol machine and its
/// exact generation-derived context; a generic caller-selected tag is not enough.
pub trait IngressMachine: Machine {
    fn validate_ingress_context(&self, context: &Context, n: usize) -> Result<()>;
}
impl IngressMachine for crate::acs_store::AcsMachine {
    fn validate_ingress_context(&self, c: &Context, n: usize) -> Result<()> {
        let s = &self.state;
        let expected = crate::acs::Acs::new(c.recipient, n, s.f, &c.generation)?;
        if c.protocol != Protocol::Acs
            || s.me != c.recipient
            || s.n != n
            || s.context != expected.context
        {
            return Err(bad("ACS actual receiver binding"));
        }
        Ok(())
    }
}
impl IngressMachine for crate::private_send_store::DeliveryMachine {
    fn validate_ingress_context(&self, c: &Context, n: usize) -> Result<()> {
        let s = &self.state;
        let expected = crate::private_send::PrivateSend::new(
            c.recipient,
            s.dealer,
            n,
            s.f,
            &c.generation,
            s.length(),
        )?;
        if c.protocol != Protocol::PrivateSend
            || s.me != c.recipient
            || s.n != n
            || s.context != expected.context
        {
            return Err(bad("private delivery actual receiver binding"));
        }
        Ok(())
    }
}
impl IngressMachine for crate::acss_id_store::AcssMachine {
    fn validate_ingress_context(&self, c: &Context, n: usize) -> Result<()> {
        let s = &self.state;
        let expected =
            crate::acss_id::AcssId::new(c.recipient, s.dealer, n, s.f, &c.generation, s.count)?;
        if c.protocol != Protocol::AcssId
            || s.me != c.recipient
            || s.n != n
            || s.context != expected.context
        {
            return Err(bad("ACSS actual receiver binding"));
        }
        Ok(())
    }
}
impl IngressMachine for crate::dzk_store::DzkMachine {
    fn validate_ingress_context(&self, c: &Context, n: usize) -> Result<()> {
        let s = &self.state;
        let p = crate::dzk::Profile::new(
            n,
            s.profile.f,
            s.profile.dealer,
            &c.generation,
            s.profile.count,
            s.profile.degree,
        )?;
        if c.protocol != Protocol::Dzk
            || s.me != c.recipient
            || s.profile.n != n
            || s.profile.context != p.context
        {
            return Err(bad("dZK actual receiver binding"));
        }
        Ok(())
    }
}

pub struct Receiver<M: IngressMachine> {
    journal: Journal<AuthenticatedMachine<M>>,
}
impl<M: IngressMachine> Receiver<M> {
    /// `capacity` is the fixed reserved quota PER party, total n*capacity.
    /// Source funding must admit this full public bound before opening the worker.
    /// This supports a finite generation lifetime, not indefinitely many packets.
    /// Old IDs are retained; extending lifetime needs new source-admitted context.
    pub fn open(
        path: &Path,
        context: Context,
        n: usize,
        capacity: usize,
        inner: M,
    ) -> Result<Self> {
        if n == 0 || n > 16 || context.recipient as usize >= n || capacity == 0 || capacity > 65536
        {
            return Err(bad("receiver funded bounds"));
        }
        inner.validate_ingress_context(&context, n)?;
        let mut identity = b"DREGG.PRIVATE.AUTH.RECEIVER\x02".to_vec();
        identity.push(context.protocol as u8);
        context.generation.put(&mut identity);
        context.authority_epoch.put(&mut identity);
        bytes(&context.session, &mut identity);
        identity.extend(context.recipient.to_le_bytes());
        bytes(&context.recipient_role, &mut identity);
        identity.extend((n as u64).to_le_bytes());
        identity.extend((capacity as u64).to_le_bytes());
        let machine = AuthenticatedMachine {
            inner,
            context,
            n,
            capacity_per_party: capacity,
            accepted: BTreeMap::new(),
        };
        Ok(Self {
            journal: Journal::open(path, &identity, machine)?,
        })
    }
    pub fn state(&self) -> &M {
        &self.journal.state().inner
    }
    pub fn receive<A: SourcePartyAuthority>(
        &mut self,
        authority: &A,
        packet: &[u8],
    ) -> Result<Outcome> {
        let m = self.journal.state();
        // Revalidate CURRENT authority even for exact duplicates. Revocation
        // cannot be bypassed by consulting a stale accepted invocation/cache.
        let verified = verify_packet(&m.context, m.n, authority, packet)?;
        let id = (verified.sender(), verified.envelope.sequence);
        if let Some(old) = m.accepted.get(&id) {
            if old.semantic != verified.envelope.signing_bytes() {
                return Err(bad("conflicting replay"));
            }
            return Ok(Outcome {
                disposition: Disposition::Replayed,
                outbox: old.outbox.clone(),
                semantic: verified.envelope.signing_bytes(),
            });
        }
        let outbox = self.journal.append(&verified.canonical)?;
        Ok(Outcome {
            disposition: Disposition::Applied,
            outbox,
            semantic: verified.envelope.signing_bytes(),
        })
    }
    pub fn replay_outboxes(&self) -> &[Vec<u8>] {
        self.journal.replay_outboxes()
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use sha2::{Digest, Sha256};
    use std::{
        fs,
        time::{SystemTime, UNIX_EPOCH},
    };
    // Concrete fixture only. Production consumer uses native credential admission;
    // it must NOT install this fixture as a source authority.
    fn hmac(key: &[u8; 32], m: &[u8]) -> Vec<u8> {
        let mut i = [0x36u8; 64];
        let mut o = [0x5cu8; 64];
        for j in 0..32 {
            i[j] ^= key[j];
            o[j] ^= key[j];
        }
        let mut h = Sha256::new();
        h.update(i);
        h.update(m);
        let inner = h.finalize();
        let mut h = Sha256::new();
        h.update(o);
        h.update(inner);
        h.finalize().to_vec()
    }
    struct Fixture {
        party: CommitteeParty,
        key: [u8; 32],
        active: bool,
    }
    impl SourcePartyAuthority for Fixture {
        fn verify_enrolled_packet(
            &self,
            p: &CommitteeParty,
            m: &[u8],
            credential: &[u8],
        ) -> Result<()> {
            if !self.active || p != &self.party {
                return Err(bad("not current exact enrollment"));
            }
            if credential.len() != 40 {
                return Err(bad("credential length"));
            }
            let mut salted = m.to_vec();
            salted.extend(&credential[..8]);
            let expected = hmac(&self.key, &salted);
            if credential[8..].len() != expected.len() {
                return Err(bad("credential length"));
            }
            let different = credential[8..]
                .iter()
                .zip(expected)
                .fold(0u8, |a, (x, y)| a | (*x ^ y));
            if different != 0 {
                return Err(bad("credential verification"));
            }
            Ok(())
        }
    }
    fn fixture(protocol: Protocol) -> Fixture {
        Fixture {
            party: CommitteeParty {
                context: Context {
                    protocol,
                    generation: Generation {
                        invocation: Nat::from_be(&[255; 32]),
                        command: vec![1, 9],
                        attempt: Nat::new(0),
                        generation: Nat::new(1),
                        configuration: Nat::from_be(&[254; 32]),
                    },
                    authority_epoch: Nat::new(9),
                    session: vec![17; 32],
                    recipient: 2,
                    recipient_role: b"backend-party".to_vec(),
                },
                party: 1,
                subject: b"actual-test-subject".to_vec(),
                key_epoch: Nat::new(3),
                key_binding: vec![11; 32],
                credential_purpose: b"private-backend-packet".to_vec(),
            },
            key: [7; 32],
            active: true,
        }
    }
    fn packet(f: &Fixture, sequence: u64, message: Vec<u8>) -> Envelope {
        let mut e = Envelope {
            party: f.party.clone(),
            sequence,
            message,
            credential: vec![],
        };
        let mut preimage = e.signing_bytes();
        preimage.extend(0u64.to_le_bytes());
        e.credential = 0u64.to_le_bytes().to_vec();
        e.credential.extend(hmac(&f.key, &preimage));
        e
    }
    #[test]
    fn canonical_carrier_preserves_full_generation_and_signed_bytes() {
        let f = fixture(Protocol::Acs);
        let e = packet(&f, 4, vec![8; 65536]);
        let b = e.encode().unwrap();
        assert_eq!(public_ingress_gate(&carrier(&b).unwrap()).unwrap(), b);
        assert_eq!(Envelope::decode(&b).unwrap(), e);
        assert_eq!(
            verify_packet(&f.party.context, 4, &f, &b).unwrap().sender(),
            1
        );
        let mut trailing = b.clone();
        trailing.push(0);
        assert!(public_ingress_gate(&trailing).is_err());
        let mut over = e;
        over.message = vec![0; MAX_PACKET];
        assert!(over.encode().is_err());

        // Compose the same receiver with the ACTUAL private delivery machine,
        // not just the counter fixture used to expose atomic replay behavior.
        use crate::{
            private_send::{Body, PrivateSend},
            private_send_store::{encode_message, DeliveryMachine},
            reconstruction::Field,
        };
        let df = fixture(Protocol::PrivateSend);
        let g = &df.party.context.generation;
        let mut dealer = PrivateSend::new(1, 1, 4, 1, g, 64).unwrap();
        let packets = dealer
            .dealer_with_coefficients(
                &[31; 64],
                &[vec![Field(42), Field(7)], vec![Field(91), Field(11)]],
            )
            .unwrap();
        let ciphertext = packets
            .iter()
            .find(|p| p.to == 2 && matches!(&p.message.body, Body::Cipher(_)))
            .unwrap();
        let body = encode_message(&ciphertext.message);
        let mut wrong = df.party.context.clone();
        wrong.protocol = Protocol::Acs;
        assert!(Receiver::open(
            &path(),
            wrong,
            4,
            8,
            DeliveryMachine {
                state: PrivateSend::new(2, 1, 4, 1, g, 64).unwrap()
            }
        )
        .is_err());
        let mut wrong = df.party.context.clone();
        wrong.generation.command.push(0);
        assert!(Receiver::open(
            &path(),
            wrong,
            4,
            8,
            DeliveryMachine {
                state: PrivateSend::new(2, 1, 4, 1, g, 64).unwrap()
            }
        )
        .is_err());

        let mut receiver = Receiver::open(
            &path(),
            df.party.context.clone(),
            4,
            8,
            DeliveryMachine {
                state: PrivateSend::new(2, 1, 4, 1, g, 64).unwrap(),
            },
        )
        .unwrap();
        let envelope = packet(&df, 0, body).encode().unwrap();
        let applied = receiver.receive(&df, &envelope).unwrap();
        assert_eq!(applied.disposition, Disposition::Applied);
        assert!(applied.outbox.len() > 1); // actual ciphertext RBC Echo outbox
        assert_eq!(
            receiver.receive(&df, &envelope).unwrap().outbox,
            applied.outbox
        );
    }
    #[test]
    fn wrong_party_epoch_protocol_recipient_and_subject_refuse() {
        let f = fixture(Protocol::Acs);
        let e = packet(&f, 0, vec![9]);
        let mut variants = vec![];
        let mut v = e.clone();
        v.party.party = 0;
        variants.push(v);
        let mut v = e.clone();
        v.party.context.authority_epoch = Nat::new(10);
        variants.push(v);
        let mut v = e.clone();
        v.party.context.protocol = Protocol::PrivateSend;
        variants.push(v);
        let mut v = e.clone();
        v.party.context.recipient = 3;
        variants.push(v);
        let mut v = e.clone();
        v.party.subject = b"different".to_vec();
        variants.push(v);
        let mut v = e.clone();
        v.party.context.generation.command.push(0);
        variants.push(v);
        let mut v = e.clone();
        v.party.context.session[0] ^= 1;
        variants.push(v);
        let mut v = e.clone();
        v.message[0] ^= 1;
        variants.push(v);
        for v in variants {
            assert!(verify_packet(&f.party.context, 4, &f, &v.encode().unwrap()).is_err());
        }
        let off = Fixture {
            active: false,
            ..fixture(Protocol::Acs)
        };
        assert!(verify_packet(&f.party.context, 4, &off, &e.encode().unwrap()).is_err());
    }
    #[derive(Clone)]
    struct Counter {
        value: u64,
    }
    impl Machine for Counter {
        fn apply(&mut self, b: &[u8]) -> Result<Vec<u8>> {
            let mut c = Cursor::new(b)?;
            if c.byte()? != 2 || c.u16()? >= 4 {
                return Err(bad("counter authenticated sender"));
            }
            let message = c.bytes()?;
            c.finish()?;
            if message.len() != 8 {
                return Err(bad("counter message"));
            }
            self.value += u64::from_le_bytes(message.try_into().unwrap());
            Ok(self.value.to_le_bytes().to_vec())
        }
    }
    impl IngressMachine for Counter {
        fn validate_ingress_context(&self, c: &Context, n: usize) -> Result<()> {
            if c.protocol != Protocol::Acs || c.recipient != 2 || n != 4 {
                return Err(bad("counter actual receiver context"));
            }
            Ok(())
        }
    }
    fn path() -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!(
            "mini-authenticated-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&p).unwrap();
        p.join("wal")
    }
    #[test]
    fn replay_and_protocol_transition_are_one_durable_record() {
        let f = fixture(Protocol::Acs);
        let p = path();
        let e = packet(&f, 5, 7u64.to_le_bytes().to_vec()).encode().unwrap();
        let original;
        {
            let mut r =
                Receiver::open(&p, f.party.context.clone(), 4, 3, Counter { value: 0 }).unwrap();
            let out = r.receive(&f, &e).unwrap();
            assert_eq!(out.disposition, Disposition::Applied);
            let frame = out.progress_claim().encode().unwrap();
            assert_eq!(ProgressClaim::decode(&frame).unwrap(), out.progress_claim());
            assert_eq!(
                out.progress_claim().signing_bytes,
                Envelope::decode(&e).unwrap().signing_bytes()
            );
            original = out.outbox;
        }
        let mut r =
            Receiver::open(&p, f.party.context.clone(), 4, 3, Counter { value: 0 }).unwrap();
        let len = fs::metadata(&p).unwrap().len();
        let out = r.receive(&f, &e).unwrap();
        assert_eq!(out.disposition, Disposition::Replayed);
        assert_eq!(out.outbox, original);
        assert_eq!(r.state().value, 7);
        assert_eq!(fs::metadata(&p).unwrap().len(), len);
        // A freshly issued randomized native credential for the SAME semantic
        // packet must replay, rather than apply it twice or create a conflict.
        let mut fresh = Envelope::decode(&e).unwrap();
        let mut signed = fresh.signing_bytes();
        signed.extend(19u64.to_le_bytes());
        fresh.credential = 19u64.to_le_bytes().to_vec();
        fresh.credential.extend(hmac(&f.key, &signed));
        assert_eq!(
            r.receive(&f, &fresh.encode().unwrap()).unwrap().disposition,
            Disposition::Replayed
        );
        assert_eq!(fs::metadata(&p).unwrap().len(), len);
        let conflict = packet(&f, 5, 8u64.to_le_bytes().to_vec()).encode().unwrap();
        assert!(r.receive(&f, &conflict).is_err());
        assert_eq!(r.state().value, 7);
        let off = Fixture {
            active: false,
            ..fixture(Protocol::Acs)
        };
        assert!(r.receive(&off, &e).is_err());
        let bad = packet(&f, 6, vec![1]).encode().unwrap();
        assert!(r.receive(&f, &bad).is_err());
        assert_eq!(fs::metadata(&p).unwrap().len(), len);
    }
    #[test]
    fn out_of_order_sequences_and_explicit_capacity_refusal() {
        let f = fixture(Protocol::Acs);
        let mut r =
            Receiver::open(&path(), f.party.context.clone(), 4, 2, Counter { value: 0 }).unwrap();
        for seq in [17, 2] {
            r.receive(
                &f,
                &packet(&f, seq, 1u64.to_le_bytes().to_vec())
                    .encode()
                    .unwrap(),
            )
            .unwrap();
        }
        assert_eq!(r.state().value, 2);
        assert!(r
            .receive(
                &f,
                &packet(&f, 3, 1u64.to_le_bytes().to_vec()).encode().unwrap()
            )
            .is_err());
        assert_eq!(r.state().value, 2);
    }
    #[test]
    fn byzantine_sender_quota_cannot_starve_honest_party_after_restart() {
        let faulty = fixture(Protocol::Acs);
        let mut honest = fixture(Protocol::Acs);
        honest.party.party = 0;
        honest.party.subject = b"independent-honest-subject".to_vec();
        honest.key = [29; 32];
        let p = path();
        let original;
        {
            let mut r =
                Receiver::open(&p, faulty.party.context.clone(), 4, 2, Counter { value: 0 })
                    .unwrap();
            for seq in [u64::MAX, 100000] {
                r.receive(
                    &faulty,
                    &packet(&faulty, seq, 0u64.to_le_bytes().to_vec())
                        .encode()
                        .unwrap(),
                )
                .unwrap();
            }
            for seq in 0..4 {
                assert!(r
                    .receive(
                        &faulty,
                        &packet(&faulty, seq, 0u64.to_le_bytes().to_vec())
                            .encode()
                            .unwrap()
                    )
                    .is_err());
            }
            original = r
                .receive(
                    &honest,
                    &packet(&honest, 9, 7u64.to_le_bytes().to_vec())
                        .encode()
                        .unwrap(),
                )
                .unwrap()
                .outbox;
            assert_eq!(r.state().value, 7);
        }
        let mut r =
            Receiver::open(&p, faulty.party.context.clone(), 4, 2, Counter { value: 0 }).unwrap();
        let len = fs::metadata(&p).unwrap().len();
        assert_eq!(
            r.receive(
                &honest,
                &packet(&honest, 9, 7u64.to_le_bytes().to_vec())
                    .encode()
                    .unwrap()
            )
            .unwrap()
            .outbox,
            original
        );
        assert_eq!(fs::metadata(&p).unwrap().len(), len);
        r.receive(
            &honest,
            &packet(&honest, 1, 11u64.to_le_bytes().to_vec())
                .encode()
                .unwrap(),
        )
        .unwrap();
        assert_eq!(r.state().value, 18);
        assert!(r
            .receive(
                &honest,
                &packet(&honest, 2, 1u64.to_le_bytes().to_vec())
                    .encode()
                    .unwrap()
            )
            .is_err());
    }
}
