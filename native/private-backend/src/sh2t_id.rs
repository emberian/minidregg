//! Actual §6.1 Sh2t-Id: degree-2f values with random degree-2f masks,
//! salted share commitment matrix, real PrivSend, immutable acceptance before RA,
//! and recipient-restricted reconstruction checked against ALL committed shares.
//! Static f, classical SHA256 ROM/reference GF128; no QROM/PQ/simulator claim.
//! Protocol environment requests do not manufacture native release authority.
use crate::{
    asks::{Bracha, PhaseMessage},
    codec::{bad, Generation, Nat},
    custody::hash,
    private_send::{self, PrivateSend},
    reconstruction::Field,
};
use std::{
    collections::BTreeMap,
    io::{Error, ErrorKind, Result},
};
fn eval(p: &[Field], x: Field) -> Field {
    p.iter().rev().fold(Field(0), |a, c| a.mul(x).add(*c))
}
fn alpha(i: usize) -> Field {
    Field(i as u128 + 1)
}
fn entropy(seed: [u8; 32], context: [u8; 32], tag: u8, index: usize) -> [u8; 32] {
    let mut b = b"DREGG.SH2T.ID.RANDOM.V1".to_vec();
    b.extend(seed);
    b.extend(context);
    b.push(tag);
    b.extend((index as u64).to_le_bytes());
    hash(&b)
}
fn child(g: &Generation, context: [u8; 32], i: usize) -> Generation {
    let mut b = b"DREGG.SH2T.ID.CHILD.V1".to_vec();
    b.extend(context);
    b.extend((i as u64).to_le_bytes());
    let mut h = g.clone();
    h.invocation = Nat::from_be(&hash(&b));
    h
}
fn point_hash(
    context: [u8; 32],
    group: usize,
    holder: usize,
    v: &[Field],
    m: &[Field],
) -> [u8; 32] {
    let mut b = b"DREGG.SH2T.ID.POINT.V1".to_vec();
    b.extend(context);
    b.extend((group as u64).to_le_bytes());
    b.extend((holder as u64).to_le_bytes());
    b.extend((v.len() as u64).to_le_bytes());
    for x in v.iter().chain(m) {
        b.extend(x.0.to_le_bytes());
    }
    hash(&b)
}
fn block_hash(context: [u8; 32], holder: usize, receiver: usize, hs: &[[u8; 32]]) -> [u8; 32] {
    let mut b = b"DREGG.SH2T.ID.BLOCK.V1".to_vec();
    b.extend(context);
    b.extend((holder as u64).to_le_bytes());
    b.extend((receiver as u64).to_le_bytes());
    for h in hs {
        b.extend(h);
    }
    hash(&b)
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AcceptedSharing {
    context: [u8; 32],
    holder: u16,
    values: Vec<Field>,
    masks: Vec<Field>,
    group_count: usize,
    per_group: usize,
}
impl AcceptedSharing {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn holder(&self) -> u16 {
        self.holder
    }
    pub fn values(&self) -> &[Field] {
        &self.values
    }
    pub fn mask_values(&self) -> &[Field] {
        &self.masks
    }
    pub fn group_count(&self) -> usize {
        self.group_count
    }
    pub fn per_group(&self) -> usize {
        self.per_group
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RejectedSharing {
    context: [u8; 32],
    holder: u16,
    evidence_hash: [u8; 32],
}
impl RejectedSharing {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn holder(&self) -> u16 {
        self.holder
    }
    pub fn evidence_hash(&self) -> [u8; 32] {
        self.evidence_hash
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LocalSharing {
    Accepted(AcceptedSharing),
    Rejected(RejectedSharing),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FaultParty {
    Dealer(u16),
    Accuser(u16),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Accusation {
    context: [u8; 32],
    dealer: u16,
    holder: u16,
    fault: FaultParty,
    commitment_bytes: Vec<u8>,
    private_bytes: Vec<u8>,
}
impl Accusation {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn dealer(&self) -> u16 {
        self.dealer
    }
    pub fn holder(&self) -> u16 {
        self.holder
    }
    pub fn fault(&self) -> FaultParty {
        self.fault
    }
    pub fn commitment_bytes(&self) -> &[u8] {
        &self.commitment_bytes
    }
    pub fn private_bytes(&self) -> &[u8] {
        &self.private_bytes
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AgreedAccusation {
    context: [u8; 32],
    dealer: u16,
    holder: u16,
}
impl AgreedAccusation {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn dealer(&self) -> u16 {
        self.dealer
    }
    pub fn holder(&self) -> u16 {
        self.holder
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PrivateReconstructed {
    context: [u8; 32],
    group: usize,
    receiver: u16,
    polynomials: Vec<Vec<Field>>,
    mask_polynomials: Vec<Vec<Field>>,
    commitment_bytes: Vec<u8>,
    accepted_holders: Vec<u16>,
}
impl PrivateReconstructed {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn group(&self) -> usize {
        self.group
    }
    pub fn receiver(&self) -> u16 {
        self.receiver
    }
    pub fn polynomials(&self) -> &[Vec<Field>] {
        &self.polynomials
    }
    pub fn mask_polynomials(&self) -> &[Vec<Field>] {
        &self.mask_polynomials
    }
    pub fn commitment_bytes(&self) -> &[u8] {
        &self.commitment_bytes
    }
    pub fn commitment_hash(&self) -> [u8; 32] {
        hash(&self.commitment_bytes)
    }
    pub fn accepted_holders(&self) -> &[u16] {
        &self.accepted_holders
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InvalidReconstruction {
    context: [u8; 32],
    group: usize,
    receiver: u16,
    evidence_hash: [u8; 32],
    commitment_bytes: Vec<u8>,
    committed_group_hashes: Vec<[u8; 32]>,
    candidate_polynomials: Vec<Vec<Field>>,
    candidate_mask_polynomials: Vec<Vec<Field>>,
    accepted_holders: Vec<u16>,
}
impl InvalidReconstruction {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn group(&self) -> usize {
        self.group
    }
    pub fn receiver(&self) -> u16 {
        self.receiver
    }
    pub fn evidence_hash(&self) -> [u8; 32] {
        self.evidence_hash
    }
    /// Retained private verification evidence, not permission to publish it.
    pub fn commitment_bytes(&self) -> &[u8] {
        &self.commitment_bytes
    }
    pub fn committed_group_hashes(&self) -> &[[u8; 32]] {
        &self.committed_group_hashes
    }
    pub fn candidate_polynomials(&self) -> &[Vec<Field>] {
        &self.candidate_polynomials
    }
    pub fn candidate_mask_polynomials(&self) -> &[Vec<Field>] {
        &self.candidate_mask_polynomials
    }
    pub fn accepted_holders(&self) -> &[u16] {
        &self.accepted_holders
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Reconstruction {
    Verified(PrivateReconstructed),
    Invalid(InvalidReconstruction),
    AgreedAccusation(AgreedAccusation),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Body {
    Commitment(PhaseMessage),
    Private {
        holder: u16,
        message: private_send::Message,
    },
    Termination(PhaseMessage),
    Complaint {
        holder: u16,
        phase: PhaseMessage,
    },
    OpenRequest {
        holder: u16,
        requester: u16,
        phase: PhaseMessage,
    },
    ReconRequest {
        group: usize,
        receiver: u16,
        requester: u16,
        phase: PhaseMessage,
    },
    AgreementAccusation {
        holder: u16,
        phase: PhaseMessage,
    },
    Point {
        group: usize,
        receiver: u16,
        values: Vec<Field>,
        masks: Vec<Field>,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Message {
    pub context: [u8; 32],
    pub body: Body,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Send {
    pub to: u16,
    pub message: Message,
}
#[derive(Clone, Debug)]
struct Payload {
    values: Vec<Field>,
    masks: Vec<Field>,
    hashes: Vec<[u8; 32]>,
}
#[derive(Clone)]
pub struct Sh2tId {
    original_generation: Generation,
    pub me: u16,
    pub dealer: u16,
    pub n: usize,
    pub f: usize,
    pub context: [u8; 32],
    pub per_group: usize,
    private: Vec<PrivateSend>,
    matrix: Bracha,
    ra: Bracha,
    complaints: Vec<Bracha>,
    open_requests: Vec<Vec<Bracha>>,
    agreements: Vec<Bracha>,
    recon_requests: Vec<Vec<Bracha>>,
    started: bool,
    local_requested: bool,
    local: Option<LocalSharing>,
    accepted: Option<Payload>,
    open_requested: Vec<bool>,
    opening_started: Vec<bool>,
    accusations: BTreeMap<u16, Accusation>,
    agreement_requested: Vec<bool>,
    requested: Vec<bool>,
    point_sent: Vec<bool>,
    points: Vec<BTreeMap<u16, (Vec<Field>, Vec<Field>)>>,
    pending: Vec<BTreeMap<u16, (Vec<Field>, Vec<Field>)>>,
    reconstructed: BTreeMap<usize, Reconstruction>,
    dealer_inputs: Option<Vec<Vec<Field>>>,
}
impl Sh2tId {
    pub fn new(
        me: u16,
        dealer: u16,
        n: usize,
        f: usize,
        g: &Generation,
        per_group: usize,
    ) -> Result<Self> {
        if n != 3 * f + 1
            || !(4..=16).contains(&n)
            || me as usize >= n
            || dealer as usize >= n
            || per_group == 0
            || per_group > 128
        {
            return Err(bad("Sh2t roster/group bound"));
        }
        let count = n * n * per_group;
        let length = 32 * (count + n * n);
        // Actual PrivSend payload and the aggregate recursive dealer WAL event/outbox.
        // Public parameters refuse before any secret input/randomness is consumed.
        if length > 65536
            || n * n * (length + 4096) + count * (2 * f + 1) * 16 + 65536 > crate::codec::MAX
        {
            return Err(bad("Sh2t fixed payload/aggregate WAL capacity"));
        }
        let mut b = b"DREGG.SH2T.ID.GF128.V1".to_vec();
        g.put(&mut b);
        b.extend(dealer.to_le_bytes());
        for v in [n, f, per_group] {
            b.extend((v as u64).to_le_bytes());
        }
        let context = hash(&b);
        let private = (0..n)
            .map(|i| PrivateSend::new(me, dealer, n, f, &child(g, context, i), length))
            .collect::<Result<_>>()?;
        Ok(Self {
            original_generation: g.clone(),
            me,
            dealer,
            n,
            f,
            context,
            per_group,
            private,
            matrix: Bracha::new(n, f, Some(dealer)),
            ra: Bracha::new(n, f, None),
            complaints: (0..n).map(|i| Bracha::new(n, f, Some(i as u16))).collect(),
            open_requests: (0..n)
                .map(|_| (0..n).map(|i| Bracha::new(n, f, Some(i as u16))).collect())
                .collect(),
            agreements: (0..n).map(|_| Bracha::new(n, f, None)).collect(),
            recon_requests: (0..n * n)
                .map(|_| (0..n).map(|i| Bracha::new(n, f, Some(i as u16))).collect())
                .collect(),
            started: false,
            local_requested: false,
            local: None,
            accepted: None,
            open_requested: vec![false; n],
            opening_started: vec![false; n],
            accusations: BTreeMap::new(),
            agreement_requested: vec![false; n],
            requested: vec![false; n * n],
            point_sent: vec![false; n * n],
            points: vec![BTreeMap::new(); n * n],
            pending: vec![BTreeMap::new(); n * n],
            reconstructed: BTreeMap::new(),
            dealer_inputs: None,
        })
    }
    pub fn original_generation(&self) -> &Generation {
        &self.original_generation
    }
    pub fn commitment_bytes(&self) -> Option<&[u8]> {
        self.matrix.output.as_deref()
    }
    /// Returns only bytes already delivered to this party by actual PrivSend.
    /// This read-only access does not authorize further public release.
    pub fn private_view(&self, holder: u16) -> Option<&[u8]> {
        self.private.get(holder as usize)?.delivered.as_deref()
    }
    pub fn group_count(&self) -> usize {
        self.n * self.n
    }
    pub fn count(&self) -> usize {
        self.group_count() * self.per_group
    }
    pub fn payload_length(&self) -> usize {
        32 * (self.count() + self.n * self.n)
    }
    fn all(&self, body: Body) -> Vec<Send> {
        (0..self.n)
            .map(|i| Send {
                to: i as u16,
                message: Message {
                    context: self.context,
                    body: body.clone(),
                },
            })
            .collect()
    }
    fn private_out(&self, holder: u16, ps: Vec<private_send::Send>) -> Vec<Send> {
        ps.into_iter()
            .map(|p| Send {
                to: p.to,
                message: Message {
                    context: self.context,
                    body: Body::Private {
                        holder,
                        message: p.message,
                    },
                },
            })
            .collect()
    }
    fn matrix_values(&self) -> Option<Vec<[u8; 32]>> {
        let b = self.matrix.output.as_ref()?;
        if b.len() != self.n * self.n * 32 {
            return None;
        }
        Some(b.chunks_exact(32).map(|x| x.try_into().unwrap()).collect())
    }
    fn parse_payload(&self, b: &[u8]) -> Option<Payload> {
        if b.len() != self.payload_length() {
            return None;
        }
        let count = self.count();
        let fields = b[..count * 32]
            .chunks_exact(16)
            .map(|x| Field(u128::from_le_bytes(x.try_into().unwrap())))
            .collect::<Vec<_>>();
        Some(Payload {
            values: fields[..count].to_vec(),
            masks: fields[count..].to_vec(),
            hashes: b[count * 32..]
                .chunks_exact(32)
                .map(|x| x.try_into().unwrap())
                .collect(),
        })
    }
    fn payload(&self, holder: usize) -> Option<Payload> {
        self.parse_payload(self.private[holder].delivered.as_ref()?)
    }
    fn valid_payload(&self, holder: usize, p: &Payload) -> bool {
        let Some(com) = self.matrix_values() else {
            return false;
        };
        for receiver in 0..self.n {
            let hs = (receiver * self.n..(receiver + 1) * self.n)
                .map(|group| {
                    let lo = group * self.per_group;
                    point_hash(
                        self.context,
                        group,
                        holder,
                        &p.values[lo..lo + self.per_group],
                        &p.masks[lo..lo + self.per_group],
                    )
                })
                .collect::<Vec<_>>();
            if block_hash(self.context, holder, receiver, &hs) != com[holder * self.n + receiver] {
                return false;
            }
        }
        for i in 0..self.n {
            let hs = (0..self.n)
                .map(|off| p.hashes[off * self.n + i])
                .collect::<Vec<_>>();
            if block_hash(self.context, i, holder, &hs) != com[i * self.n + holder] {
                return false;
            }
        }
        true
    }
    /// Caller/store persists seed, exact inputs and entire recursive outbox before publication.
    pub fn dealer(&mut self, polys: &[Vec<Field>], seed: [u8; 32]) -> Result<Vec<Send>> {
        if self.me != self.dealer
            || self.started
            || polys.len() != self.count()
            || polys.iter().any(|p| p.len() != 2 * self.f + 1)
        {
            return Err(bad("Sh2t dealer/count/degree/retry"));
        }
        let masks = (0..self.count())
            .map(|i| {
                (0..=2 * self.f)
                    .map(|k| {
                        Field(u128::from_le_bytes(
                            entropy(seed, self.context, 0, i * (2 * self.f + 1) + k)[..16]
                                .try_into()
                                .unwrap(),
                        ))
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let rows = (0..self.n)
            .map(|i| Payload {
                values: polys.iter().map(|p| eval(p, alpha(i))).collect(),
                masks: masks.iter().map(|p| eval(p, alpha(i))).collect(),
                hashes: vec![],
            })
            .collect::<Vec<_>>();
        let hs = (0..self.group_count())
            .map(|group| {
                (0..self.n)
                    .map(|i| {
                        let lo = group * self.per_group;
                        point_hash(
                            self.context,
                            group,
                            i,
                            &rows[i].values[lo..lo + self.per_group],
                            &rows[i].masks[lo..lo + self.per_group],
                        )
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut com = vec![];
        for i in 0..self.n {
            for j in 0..self.n {
                com.extend(block_hash(
                    self.context,
                    i,
                    j,
                    &(j * self.n..(j + 1) * self.n)
                        .map(|k| hs[k][i])
                        .collect::<Vec<_>>(),
                ));
            }
        }
        let mut out = self.all(Body::Commitment(PhaseMessage::Init(com)));
        for i in 0..self.n {
            let mut payload = vec![];
            for x in rows[i].values.iter().chain(&rows[i].masks) {
                payload.extend(x.0.to_le_bytes());
            }
            for row in &hs[i * self.n..(i + 1) * self.n] {
                for h in row {
                    payload.extend(h);
                }
            }
            let keys = (0..2)
                .map(|k| {
                    (0..=self.f)
                        .map(|j| {
                            Field(u128::from_le_bytes(
                                entropy(seed, self.context, 1, i * 32 + k * 16 + j)[..16]
                                    .try_into()
                                    .unwrap(),
                            ))
                        })
                        .collect()
                })
                .collect::<Vec<_>>();
            let ps = self.private[i].dealer_with_coefficients(&payload, &keys)?;
            out.extend(self.private_out(i as u16, ps));
        }
        self.dealer_inputs = Some(polys.to_vec());
        self.started = true;
        out.extend(self.progress()?);
        Ok(out)
    }
    pub(crate) fn dealer_inputs(&self) -> Option<&[Vec<Field>]> {
        self.dealer_inputs.as_deref()
    }
    pub fn receive(&mut self, sender: u16, m: Message) -> Result<Vec<Send>> {
        if sender as usize >= self.n || m.context != self.context {
            return Err(bad("Sh2t sender/context"));
        }
        let mut out = vec![];
        match m.body {
            Body::Commitment(p) => {
                if phase_bytes(&p).len() != self.n * self.n * 32 {
                    return Err(bad("Sh2t matrix shape"));
                }
                for p in self.matrix.receive(sender, p) {
                    out.extend(self.all(Body::Commitment(p)));
                }
            }
            Body::Private { holder, message } => {
                if holder as usize >= self.n {
                    return Err(bad("Sh2t holder"));
                }
                let ps = self.private[holder as usize].receive(sender, message)?;
                out.extend(self.private_out(holder, ps));
            }
            Body::Termination(p) => {
                valid_one(&p, false)?;
                for p in self.ra.receive(sender, p) {
                    out.extend(self.all(Body::Termination(p)));
                }
            }
            Body::Complaint { holder, phase } => {
                if holder as usize >= self.n {
                    return Err(bad("complaint holder"));
                }
                valid_one(&phase, true)?;
                for p in self.complaints[holder as usize].receive(sender, phase) {
                    out.extend(self.all(Body::Complaint { holder, phase: p }));
                }
            }
            Body::OpenRequest {
                holder,
                requester,
                phase,
            } => {
                if holder as usize >= self.n || requester as usize >= self.n {
                    return Err(bad("opening roster"));
                }
                valid_one(&phase, true)?;
                for p in
                    self.open_requests[holder as usize][requester as usize].receive(sender, phase)
                {
                    out.extend(self.all(Body::OpenRequest {
                        holder,
                        requester,
                        phase: p,
                    }));
                }
            }
            Body::AgreementAccusation { holder, phase } => {
                if holder as usize >= self.n {
                    return Err(bad("accusation holder"));
                }
                valid_one(&phase, false)?;
                for p in self.agreements[holder as usize].receive(sender, phase) {
                    out.extend(self.all(Body::AgreementAccusation { holder, phase: p }));
                }
            }
            Body::ReconRequest {
                group,
                receiver,
                requester,
                phase,
            } => {
                self.check_group(group, receiver)?;
                if requester as usize >= self.n {
                    return Err(bad("recon requester"));
                }
                valid_one(&phase, true)?;
                for p in self.recon_requests[group][requester as usize].receive(sender, phase) {
                    out.extend(self.all(Body::ReconRequest {
                        group,
                        receiver,
                        requester,
                        phase: p,
                    }));
                }
            }
            Body::Point {
                group,
                receiver,
                values,
                masks,
            } => {
                self.check_group(group, receiver)?;
                if receiver != self.me
                    || values.len() != self.per_group
                    || masks.len() != self.per_group
                {
                    return Err(bad("private point recipient/shape"));
                }
                if self.sharing_complete() && self.authorized(group) {
                    self.accept_point(group, sender, values, masks);
                } else {
                    self.pending[group].entry(sender).or_insert((values, masks));
                }
            }
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    fn check_group(&self, group: usize, receiver: u16) -> Result<()> {
        if group >= self.group_count()
            || receiver as usize >= self.n
            || group / self.n != receiver as usize
        {
            Err(bad("Sh2t recipient-restricted group"))
        } else {
            Ok(())
        }
    }
    fn authorized(&self, group: usize) -> bool {
        self.recon_requests[group]
            .iter()
            .filter(|r| r.output == Some(vec![1]))
            .count()
            > self.f
    }
    fn accept_point(&mut self, group: usize, holder: u16, values: Vec<Field>, masks: Vec<Field>) {
        let Some(p) = self.accepted.as_ref() else {
            return;
        };
        let Some(com) = self.matrix_values() else {
            return;
        };
        let off = group % self.n;
        let hs = (0..self.n)
            .map(|o| p.hashes[o * self.n + holder as usize])
            .collect::<Vec<_>>();
        if point_hash(self.context, group, holder as usize, &values, &masks)
            == p.hashes[off * self.n + holder as usize]
            && block_hash(self.context, holder as usize, self.me as usize, &hs)
                == com[holder as usize * self.n + self.me as usize]
        {
            self.points[group].entry(holder).or_insert((values, masks));
        }
    }
    fn progress(&mut self) -> Result<Vec<Send>> {
        let mut out = vec![];
        let dispersed = self.matrix_values().is_some() && self.private.iter().all(|p| p.dispersed);
        if dispersed && !self.local_requested {
            self.local_requested = true;
            for i in 0..self.n {
                let ps = self.private[i].request_delivery(i as u16)?;
                out.extend(self.private_out(i as u16, ps));
            }
        }
        if dispersed && self.local.is_none() {
            if let Some(p) = self.payload(self.me as usize) {
                if self.valid_payload(self.me as usize, &p) {
                    self.local = Some(LocalSharing::Accepted(AcceptedSharing {
                        context: self.context,
                        holder: self.me,
                        values: p.values.clone(),
                        masks: p.masks.clone(),
                        group_count: self.group_count(),
                        per_group: self.per_group,
                    }));
                    self.accepted = Some(p); // immutable retained point BEFORE RA Echo
                    for p in self.ra.input_ra(vec![1]) {
                        out.extend(self.all(Body::Termination(p)));
                    }
                } else {
                    let mut b = self.matrix.output.clone().unwrap();
                    b.extend(self.private[self.me as usize].delivered.as_ref().unwrap());
                    self.local = Some(LocalSharing::Rejected(RejectedSharing {
                        context: self.context,
                        holder: self.me,
                        evidence_hash: hash(&b),
                    }));
                    out.extend(self.all(Body::Complaint {
                        holder: self.me,
                        phase: PhaseMessage::Init(vec![1]),
                    }));
                }
            }
        }
        if !self.sharing_complete() {
            return Ok(out);
        }
        for holder in 0..self.n {
            let authorized = self.open_requests[holder]
                .iter()
                .filter(|r| r.output == Some(vec![1]))
                .count()
                > self.f;
            if authorized
                && self.complaints[holder].output == Some(vec![1])
                && !self.opening_started[holder]
            {
                self.opening_started[holder] = true;
                for receiver in 0..self.n {
                    let ps = self.private[holder].request_delivery(receiver as u16)?;
                    out.extend(self.private_out(holder as u16, ps));
                }
            }
            if self.opening_started[holder] && !self.accusations.contains_key(&(holder as u16)) {
                if let Some(p) = self.payload(holder) {
                    let fault = if self.valid_payload(holder, &p) {
                        FaultParty::Accuser(holder as u16)
                    } else {
                        FaultParty::Dealer(self.dealer)
                    };
                    self.accusations.insert(
                        holder as u16,
                        Accusation {
                            context: self.context,
                            dealer: self.dealer,
                            holder: holder as u16,
                            fault,
                            commitment_bytes: self.matrix.output.clone().unwrap(),
                            private_bytes: self.private[holder].delivered.clone().unwrap(),
                        },
                    );
                }
            }
        }
        for group in 0..self.group_count() {
            if !self.authorized(group) {
                continue;
            }
            if !self.point_sent[group] {
                self.point_sent[group] = true;
                if let Some(p) = self.accepted.as_ref() {
                    let lo = group * self.per_group;
                    out.push(Send {
                        to: (group / self.n) as u16,
                        message: Message {
                            context: self.context,
                            body: Body::Point {
                                group,
                                receiver: (group / self.n) as u16,
                                values: p.values[lo..lo + self.per_group].to_vec(),
                                masks: p.masks[lo..lo + self.per_group].to_vec(),
                            },
                        },
                    });
                }
            }
            if group / self.n != self.me as usize || self.reconstructed.contains_key(&group) {
                continue;
            }
            for (holder, (v, m)) in std::mem::take(&mut self.pending[group]) {
                self.accept_point(group, holder, v, m);
            }
            if self.points[group].len() >= 2 * self.f + 1 {
                let pts = self.points[group]
                    .iter()
                    .take(2 * self.f + 1)
                    .map(|(i, (v, m))| (*i, v.clone(), m.clone()))
                    .collect::<Vec<_>>();
                let vp = interpolate(&pts, self.per_group, false)?;
                let mp = interpolate(&pts, self.per_group, true)?;
                let own = self
                    .accepted
                    .as_ref()
                    .ok_or_else(|| bad("reconstruction accepted receiver"))?;
                let all = (0..self.n).all(|i| {
                    point_hash(
                        self.context,
                        group,
                        i,
                        &vp.iter().map(|p| eval(p, alpha(i))).collect::<Vec<_>>(),
                        &mp.iter().map(|p| eval(p, alpha(i))).collect::<Vec<_>>(),
                    ) == own.hashes[(group % self.n) * self.n + i]
                });
                let r = if all {
                    Reconstruction::Verified(PrivateReconstructed {
                        context: self.context,
                        group,
                        receiver: self.me,
                        polynomials: vp,
                        mask_polynomials: mp,
                        commitment_bytes: self.matrix.output.clone().unwrap(),
                        accepted_holders: pts.iter().map(|p| p.0).collect(),
                    })
                } else {
                    let mut b = b"DREGG.SH2T.ID.INVALID.V1".to_vec();
                    b.extend(self.context);
                    b.extend((group as u64).to_le_bytes());
                    b.extend(self.me.to_le_bytes());
                    b.extend(self.matrix.output.as_ref().unwrap());
                    for (i, v, m) in &pts {
                        b.extend(i.to_le_bytes());
                        for x in v.iter().chain(m) {
                            b.extend(x.0.to_le_bytes());
                        }
                    }
                    Reconstruction::Invalid(InvalidReconstruction {
                        context: self.context,
                        group,
                        receiver: self.me,
                        evidence_hash: hash(&b),
                        commitment_bytes: self.matrix.output.clone().unwrap(),
                        committed_group_hashes: (0..self.n)
                            .map(|i| own.hashes[(group % self.n) * self.n + i])
                            .collect(),
                        candidate_polynomials: vp,
                        candidate_mask_polynomials: mp,
                        accepted_holders: pts.iter().map(|p| p.0).collect(),
                    })
                };
                self.reconstructed.insert(group, r);
            } else if let Some(holder) =
                (0..self.n).find(|h| self.agreements[*h].output == Some(vec![1]))
            {
                self.reconstructed.insert(
                    group,
                    Reconstruction::AgreedAccusation(AgreedAccusation {
                        context: self.context,
                        dealer: self.dealer,
                        holder: holder as u16,
                    }),
                );
            }
        }
        Ok(out)
    }
    pub fn sharing_complete(&self) -> bool {
        self.ra.output == Some(vec![1]) && self.local.is_some()
    }
    pub fn local_sharing(&self) -> Option<&LocalSharing> {
        if self.sharing_complete() {
            self.local.as_ref()
        } else {
            None
        }
    }
    /// Source environment request. Native authority is a separate receiving obligation.
    pub fn request_open(&mut self, holder: u16) -> Result<Vec<Send>> {
        self.require_complaint(holder)?;
        let mut out = vec![];
        if !self.open_requested[holder as usize] {
            self.open_requested[holder as usize] = true;
            out.extend(self.all(Body::OpenRequest {
                holder,
                requester: self.me,
                phase: PhaseMessage::Init(vec![1]),
            }));
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    fn require_complaint(&self, holder: u16) -> Result<()> {
        if holder as usize >= self.n {
            return Err(bad("accused holder"));
        }
        if !self.sharing_complete() || self.complaints[holder as usize].output != Some(vec![1]) {
            return Err(Error::new(
                ErrorKind::WouldBlock,
                "sharing/authenticated holder complaint pending",
            ));
        }
        Ok(())
    }
    pub fn accusation(&self, holder: u16) -> Option<&Accusation> {
        self.accusations.get(&holder)
    }
    /// Actual source/dispute request + authenticated holder complaint before honest RA input.
    pub fn request_accusation(&mut self, holder: u16) -> Result<Vec<Send>> {
        self.require_complaint(holder)?;
        let mut out = vec![];
        if !self.agreement_requested[holder as usize] {
            self.agreement_requested[holder as usize] = true;
            for p in self.agreements[holder as usize].input_ra(vec![1]) {
                out.extend(self.all(Body::AgreementAccusation { holder, phase: p }));
            }
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    pub fn request_private_reconstruction(
        &mut self,
        group: usize,
        receiver: u16,
    ) -> Result<Vec<Send>> {
        self.check_group(group, receiver)?;
        if !self.sharing_complete() {
            return Err(Error::new(ErrorKind::WouldBlock, "Sh2t sharing pending"));
        }
        let mut out = vec![];
        if !self.requested[group] {
            self.requested[group] = true;
            out.extend(self.all(Body::ReconRequest {
                group,
                receiver,
                requester: self.me,
                phase: PhaseMessage::Init(vec![1]),
            }));
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    pub fn private_reconstruction(&self, group: usize) -> Option<&Reconstruction> {
        self.reconstructed.get(&group)
    }
}
fn phase_bytes(p: &PhaseMessage) -> &[u8] {
    match p {
        PhaseMessage::Init(b) | PhaseMessage::Echo(b) | PhaseMessage::Ready(b) => b,
    }
}
fn valid_one(p: &PhaseMessage, init: bool) -> Result<()> {
    if phase_bytes(p) != &[1] || (!init && matches!(p, PhaseMessage::Init(_))) {
        Err(bad("Sh2t request/RA value"))
    } else {
        Ok(())
    }
}
fn interpolate(
    points: &[(u16, Vec<Field>, Vec<Field>)],
    count: usize,
    masks: bool,
) -> Result<Vec<Vec<Field>>> {
    let mut out = vec![vec![Field(0); points.len()]; count];
    for (i, (holder, v, m)) in points.iter().enumerate() {
        let vals = if masks { m } else { v };
        if vals.len() != count {
            return Err(bad("point length"));
        }
        let xi = alpha(*holder as usize);
        let mut basis = vec![Field(1)];
        let mut denom = Field(1);
        for (j, (other, _, _)) in points.iter().enumerate() {
            if i != j {
                let xj = alpha(*other as usize);
                let mut next = vec![Field(0); basis.len() + 1];
                for (k, c) in basis.iter().enumerate() {
                    next[k] = next[k].add(c.mul(xj));
                    next[k + 1] = next[k + 1].add(*c);
                }
                basis = next;
                denom = denom.mul(xi.add(xj));
            }
        }
        let inv = denom.inv()?;
        for (ell, value) in vals.iter().enumerate() {
            for (k, c) in basis.iter().enumerate() {
                out[ell][k] = out[ell][k].add(value.mul(*c).mul(inv));
            }
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;
    pub(super) fn generation() -> Generation {
        Generation {
            invocation: Nat::new(72),
            command: vec![4],
            attempt: Nat::new(0),
            generation: Nat::new(1),
            configuration: Nat::new(9),
        }
    }
    pub(super) fn polys(n: usize, per: usize) -> Vec<Vec<Field>> {
        (0..n * n * per)
            .map(|i| vec![Field(0), Field(i as u128 + 3), Field(i as u128 + 19)])
            .collect()
    }
    fn parties() -> Vec<Sh2tId> {
        (0..4)
            .map(|i| Sh2tId::new(i, 0, 4, 1, &generation(), 1).unwrap())
            .collect()
    }
    // Queue sender is the processing party, not the next packet's destination.
    fn run(ns: &mut [Sh2tId], q: &mut VecDeque<(u16, Send)>, gone: Option<u16>) {
        let mut steps = 0;
        while let Some((from, p)) = q.pop_front() {
            steps += 1;
            assert!(steps < 100000);
            if Some(from) == gone || Some(p.to) == gone {
                continue;
            }
            let to = p.to;
            let out = ns[to as usize].receive(from, p.message).unwrap();
            q.extend(out.into_iter().map(|p| (to, p)));
        }
    }
    fn start() -> Vec<Sh2tId> {
        let mut ns = parties();
        let ps = ns[0].dealer(&polys(4, 1), [12; 32]).unwrap();
        let mut q = ps.into_iter().map(|p| (0, p)).collect();
        run(&mut ns, &mut q, None);
        ns
    }
    fn request(ns: &mut [Sh2tId], who: &[usize], group: usize, receiver: u16, gone: Option<u16>) {
        let mut q = VecDeque::new();
        for &i in who {
            q.extend(
                ns[i]
                    .request_private_reconstruction(group, receiver)
                    .unwrap()
                    .into_iter()
                    .map(|p| (i as u16, p)),
            );
        }
        run(ns, &mut q, gone);
    }
    #[test]
    fn real_privsend_salted_matrix_and_recipient_only_verified_degree_2f() {
        let mut ns = start();
        let expected = polys(4, 1);
        for (i, n) in ns.iter().enumerate() {
            let Some(LocalSharing::Accepted(s)) = n.local_sharing() else {
                panic!("not accepted")
            };
            assert_eq!(
                s.values(),
                &expected
                    .iter()
                    .map(|p| eval(p, alpha(i)))
                    .collect::<Vec<_>>()
            );
        }
        request(&mut ns, &[1], 9, 2, None);
        assert!(ns.iter().all(|n| n.private_reconstruction(9).is_none()));
        request(&mut ns, &[3], 9, 2, None);
        let Some(Reconstruction::Verified(r)) = ns[2].private_reconstruction(9) else {
            panic!("no reconstruction")
        };
        assert_eq!(r.polynomials(), &[expected[9].clone()]);
        assert_eq!(r.receiver(), 2);
        assert_eq!(r.group(), 9);
        assert_eq!(r.accepted_holders().len(), 3);
        assert!(r.polynomials().iter().all(|p| p[0] == Field(0)));
        for i in [0, 1, 3] {
            assert!(ns[i].private_reconstruction(9).is_none());
        }
    }
    #[test]
    fn malformed_point_salt_context_and_recipient_cannot_create_support() {
        let mut ns = start();
        let mut q = VecDeque::new();
        for i in [1, 2] {
            q.extend(
                ns[i]
                    .request_private_reconstruction(15, 3)
                    .unwrap()
                    .into_iter()
                    .map(|p| (i as u16, p)),
            );
        }
        // Corrupt sender0 alters its own retained-point transfer; three honest holders suffice.
        let mut steps = 0;
        while let Some((from, mut p)) = q.pop_front() {
            steps += 1;
            assert!(steps < 100000);
            if from == 0 {
                if let Body::Point { masks, .. } = &mut p.message.body {
                    masks[0] = masks[0].add(Field(1));
                }
            }
            let to = p.to;
            let out = ns[to as usize].receive(from, p.message).unwrap();
            q.extend(out.into_iter().map(|p| (to, p)));
        }
        let Some(Reconstruction::Verified(r)) = ns[3].private_reconstruction(15) else {
            panic!("honest support missing")
        };
        assert_eq!(r.accepted_holders(), [1, 2, 3]);
        assert_eq!(r.polynomials(), &[polys(4, 1)[15].clone()]);
        let c = ns[3].context;
        assert!(ns[3]
            .receive(
                1,
                Message {
                    context: c,
                    body: Body::Point {
                        group: 0,
                        receiver: 3,
                        values: vec![Field(0)],
                        masks: vec![Field(0)]
                    }
                }
            )
            .is_err());
        assert!(ns[2]
            .receive(
                1,
                Message {
                    context: c,
                    body: Body::Point {
                        group: 15,
                        receiver: 3,
                        values: vec![Field(0)],
                        masks: vec![Field(0)]
                    }
                }
            )
            .is_err());
        assert!(ns[3]
            .receive(
                1,
                Message {
                    context: [8; 32],
                    body: Body::Point {
                        group: 15,
                        receiver: 3,
                        values: vec![Field(0)],
                        masks: vec![Field(0)]
                    }
                }
            )
            .is_err());
    }
    // Malicious dealer creates a coherent commitment matrix over arbitrary points.
    // This is actual PrivSend/RBC distribution, never an ideal degree proof callback.
    fn malicious_rows(n: &mut Sh2tId) -> Vec<Send> {
        let pp = polys(4, 1);
        let mut rows = (0..4)
            .map(|i| Payload {
                values: pp.iter().map(|p| eval(p, alpha(i))).collect(),
                masks: pp
                    .iter()
                    .map(|_| eval(&[Field(100), Field(11), Field(7)], alpha(i)))
                    .collect(),
                hashes: vec![],
            })
            .collect::<Vec<_>>();
        rows[3].values[1] = rows[3].values[1].add(Field(1));
        let hs = (0..16)
            .map(|g| {
                (0..4)
                    .map(|i| point_hash(n.context, g, i, &[rows[i].values[g]], &[rows[i].masks[g]]))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut com = vec![];
        for i in 0..4 {
            for j in 0..4 {
                com.extend(block_hash(
                    n.context,
                    i,
                    j,
                    &(j * 4..(j + 1) * 4).map(|g| hs[g][i]).collect::<Vec<_>>(),
                ));
            }
        }
        let mut out = n.all(Body::Commitment(PhaseMessage::Init(com)));
        for i in 0..4 {
            let mut bytes = vec![];
            for x in rows[i].values.iter().chain(&rows[i].masks) {
                bytes.extend(x.0.to_le_bytes());
            }
            for group in &hs[i * 4..(i + 1) * 4] {
                for h in group {
                    bytes.extend(h);
                }
            }
            let ps = n.private[i]
                .dealer_with_coefficients(
                    &bytes,
                    &[
                        vec![Field(10 + i as u128), Field(2)],
                        vec![Field(70 + i as u128), Field(3)],
                    ],
                )
                .unwrap();
            out.extend(n.private_out(i as u16, ps));
        }
        out
    }
    #[test]
    fn coherent_committed_nonpolynomial_points_accept_then_fail_all_position_check() {
        let mut ns = parties();
        let ps = malicious_rows(&mut ns[0]);
        let mut q = ps.into_iter().map(|p| (0, p)).collect();
        run(&mut ns, &mut q, None);
        assert!(ns
            .iter()
            .all(|n| matches!(n.local_sharing(), Some(LocalSharing::Accepted(_)))));
        request(&mut ns, &[1, 2], 1, 0, None);
        let Some(Reconstruction::Invalid(r)) = ns[0].private_reconstruction(1) else {
            panic!("incoherent points accepted")
        };
        assert_eq!(r.committed_group_hashes().len(), 4);
        assert_eq!(r.accepted_holders().len(), 3);
        assert_eq!(r.candidate_polynomials().len(), 1);
        assert!(!r.commitment_bytes().is_empty());
        assert_eq!(ns[0].original_generation(), &generation());
        assert!(ns[0].private_view(0).is_some());
    }
    #[test]
    fn changed_private_row_open_identifies_dealer_and_accusation_replaces_missing_points() {
        let mut ns = parties();
        let mut ps = ns[0].dealer(&polys(4, 1), [19; 32]).unwrap();
        for p in &mut ps {
            if let Body::Private { holder: 1, message } = &mut p.message.body {
                if let private_send::Body::Cipher(PhaseMessage::Init(b)) = &mut message.body {
                    b[0] ^= 1;
                }
            }
        }
        let mut q = ps.into_iter().map(|p| (0, p)).collect();
        run(&mut ns, &mut q, None);
        assert!(matches!(
            ns[1].local_sharing(),
            Some(LocalSharing::Rejected(_))
        ));
        for i in [1, 2] {
            q.extend(
                ns[i]
                    .request_open(1)
                    .unwrap()
                    .into_iter()
                    .map(|p| (i as u16, p)),
            );
        }
        run(&mut ns, &mut q, None);
        for n in &ns {
            assert_eq!(n.accusation(1).unwrap().fault(), FaultParty::Dealer(0));
        }
        // With the corrupt dealer gone and holder1 locally rejected only two honest
        // point supports remain, below 2f+1. Agreement must terminate the requested
        // private reconstruction with the authenticated accusation, not wait forever.
        request(&mut ns, &[1, 2, 3], 8, 2, Some(0));
        assert!(ns[2].private_reconstruction(8).is_none());
        for i in [1, 2, 3] {
            q.extend(
                ns[i]
                    .request_accusation(1)
                    .unwrap()
                    .into_iter()
                    .map(|p| (i as u16, p)),
            );
        }
        run(&mut ns, &mut q, Some(0));
        let Some(Reconstruction::AgreedAccusation(a)) = ns[2].private_reconstruction(8) else {
            panic!("missing abort branch")
        };
        assert_eq!(a.dealer(), 0);
        assert_eq!(a.holder(), 1);
    }
    #[test]
    fn authenticated_false_accuser_requires_f_plus_one_open_requests() {
        let mut ns = start();
        let ps = ns[0].all(Body::Complaint {
            holder: 0,
            phase: PhaseMessage::Init(vec![1]),
        });
        let mut q = ps.into_iter().map(|p| (0, p)).collect();
        run(&mut ns, &mut q, None);
        q.extend(ns[1].request_open(0).unwrap().into_iter().map(|p| (1, p)));
        run(&mut ns, &mut q, None);
        assert!(ns.iter().all(|n| n.accusation(0).is_none()));
        q.extend(ns[2].request_open(0).unwrap().into_iter().map(|p| (2, p)));
        run(&mut ns, &mut q, None);
        for n in &ns {
            assert_eq!(n.accusation(0).unwrap().fault(), FaultParty::Accuser(0));
        }
    }
    #[test]
    fn degree_four_seven_party_reconstruction_survives_two_withheld_parties() {
        let mut ns = (0..7)
            .map(|i| Sh2tId::new(i, 0, 7, 2, &generation(), 1).unwrap())
            .collect::<Vec<_>>();
        let pp = (0..49)
            .map(|i| {
                (0..5)
                    .map(|k| Field(if k == 0 { 0 } else { (i * 7 + k + 1) as u128 }))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut q = ns[0]
            .dealer(&pp, [27; 32])
            .unwrap()
            .into_iter()
            .map(|p| (0, p))
            .collect::<VecDeque<_>>();
        let pump = |ns: &mut [Sh2tId], q: &mut VecDeque<(u16, Send)>| {
            let mut steps = 0;
            while let Some((from, p)) = q.pop_front() {
                steps += 1;
                assert!(steps < 100000);
                if from >= 5 || p.to >= 5 {
                    continue;
                }
                let to = p.to;
                let out = ns[to as usize].receive(from, p.message).unwrap();
                q.extend(out.into_iter().map(|p| (to, p)));
            }
        };
        pump(&mut ns, &mut q);
        assert!(ns[..5]
            .iter()
            .all(|n| matches!(n.local_sharing(), Some(LocalSharing::Accepted(_)))));
        for i in 0..5 {
            q.extend(
                ns[i]
                    .request_private_reconstruction(33, 4)
                    .unwrap()
                    .into_iter()
                    .map(|p| (i as u16, p)),
            );
        }
        pump(&mut ns, &mut q);
        let Some(Reconstruction::Verified(r)) = ns[4].private_reconstruction(33) else {
            panic!("five retained degree-four supports missing")
        };
        assert_eq!(r.polynomials(), &[pp[33].clone()]);
        assert_eq!(r.accepted_holders(), [0, 1, 2, 3, 4]);
        assert_eq!(r.mask_polynomials()[0].len(), 5);
    }
    #[test]
    fn public_capacity_and_early_authority_refuse_before_secret_work() {
        assert!(Sh2tId::new(0, 0, 16, 5, &generation(), 128).is_err());
        let mut n = Sh2tId::new(0, 0, 16, 5, &generation(), 1).unwrap();
        assert_eq!(n.count(), 256);
        assert!(n.request_open(0).is_err());
        assert!(n.request_accusation(0).is_err());
        assert!(n.request_private_reconstruction(0, 0).is_err());
        assert!(n.request_private_reconstruction(0, 1).is_err());
    }
}
