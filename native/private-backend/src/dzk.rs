//! Appendix B hash-based distributed degree proof, compression u=2.
//! Classical SHA256 random-oracle/static-corruption reference profile over GF128.
//! The paper's larger G is NOT silently replaced with a 128-bit security claim:
//! subset and Fiat-Shamir grinding loss apply (at least n bits, plus N/round/query
//! factors). This bounded implementation is not QROM/PQ qualification.
//! Channels are authenticated/confidential. PrivSend and crash storage retain
//! their explicit receiving premises. Delivered means bytes AVAILABLE, not valid.
use crate::{
    asks::{Bracha, PhaseMessage},
    codec::{bad, bytes, Generation, Nat},
    consensus_wire::Cursor,
    custody::hash,
    private_send::{self, PrivateSend},
    reconstruction::Field,
};
use std::{
    collections::BTreeMap,
    io::{Error, ErrorKind, Result},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Profile {
    pub n: usize,
    pub f: usize,
    pub dealer: u16,
    pub count: usize,
    pub degree: usize,
    pub context: [u8; 32],
}
impl Profile {
    pub fn new(
        n: usize,
        f: usize,
        dealer: u16,
        g: &Generation,
        count: usize,
        degree: usize,
    ) -> Result<Self> {
        if n != 3 * f + 1
            || !(4..=16).contains(&n)
            || dealer as usize >= n
            || !(1..=128).contains(&count)
            || degree >= n
        {
            return Err(bad("dZK reference roster/count/degree bound"));
        }
        let mut b = b"DREGG.DZK.GF128.U2.V1".to_vec();
        g.put(&mut b);
        for v in [n, f, count, degree] {
            b.extend((v as u64).to_le_bytes());
        }
        b.extend(dealer.to_le_bytes());
        Ok(Self {
            n,
            f,
            dealer,
            count,
            degree,
            context: hash(&b),
        })
    }
    pub fn degrees(&self) -> Vec<usize> {
        let mut ds = vec![self.degree];
        while *ds.last().unwrap() > 1 {
            ds.push((ds.last().unwrap() + 1) / 2);
        }
        ds
    }
    pub fn path_len(&self) -> usize {
        self.n.next_power_of_two().trailing_zeros() as usize
    }
    pub fn private_len(&self) -> usize {
        // domain + context + holder + f0 + 2 block values/round + salt/path per root
        18 + 32
            + 2
            + 16
            + (self.degrees().len() - 1) * 32
            + self.degrees().len() * (32 + self.path_len() * 32)
    }
    pub fn public_len(&self) -> usize {
        17 + 32 + 1 + self.degrees().len() * 32 + 1 + (self.degrees().last().unwrap() + 1) * 16
    }
    pub fn holder_generation(&self, g: &Generation, holder: u16) -> Generation {
        let mut b = b"DREGG.DZK.PRIVATE.INSTANCE.V1".to_vec();
        b.extend(self.context);
        b.extend(holder.to_le_bytes());
        let mut result = g.clone();
        result.invocation = Nat::from_be(&hash(&b));
        result
    }
}
fn eval(p: &[Field], x: Field) -> Field {
    p.iter().rev().fold(Field(0), |a, c| a.mul(x).add(*c))
}
fn pow(mut x: Field, mut e: usize) -> Field {
    let mut y = Field(1);
    while e > 0 {
        if e & 1 != 0 {
            y = y.mul(x);
        }
        x = x.mul(x);
        e >>= 1;
    }
    y
}
fn fields(b: &mut Vec<u8>, xs: &[Field]) {
    for x in xs {
        b.extend(x.0.to_le_bytes());
    }
}
fn read_fields(c: &mut Cursor, count: usize) -> Result<Vec<Field>> {
    (0..count)
        .map(|_| Ok(Field(u128::from_le_bytes(c.take(16)?.try_into().unwrap()))))
        .collect()
}
fn phase_bytes(p: &PhaseMessage) -> &[u8] {
    match p {
        PhaseMessage::Init(b) | PhaseMessage::Echo(b) | PhaseMessage::Ready(b) => b,
    }
}
fn entropy(seed: [u8; 32], context: [u8; 32], tag: u8, index: usize) -> [u8; 32] {
    let mut b = b"DREGG.DZK.RANDOM.V1".to_vec();
    b.extend(seed);
    b.extend(context);
    b.push(tag);
    b.extend((index as u64).to_le_bytes());
    hash(&b)
}
fn challenge(p: &Profile, roots: &[[u8; 32]]) -> Field {
    let mut b = b"DREGG.DZK.CHALLENGE.V1".to_vec();
    b.extend(p.context);
    b.extend((roots.len() as u64).to_le_bytes());
    for r in roots {
        b.extend(r);
    }
    Field(u128::from_le_bytes(hash(&b)[..16].try_into().unwrap()))
}
fn leaf(p: &Profile, stage: usize, holder: usize, values: &[Field], salt: [u8; 32]) -> [u8; 32] {
    let mut b = b"DREGG.DZK.LEAF.V1".to_vec();
    b.extend(p.context);
    b.extend((stage as u64).to_le_bytes());
    b.extend((holder as u64).to_le_bytes());
    b.extend((values.len() as u64).to_le_bytes());
    fields(&mut b, values);
    b.extend(salt);
    hash(&b)
}
fn node(p: &Profile, stage: usize, left: [u8; 32], right: [u8; 32]) -> [u8; 32] {
    let mut b = b"DREGG.DZK.NODE.V1".to_vec();
    b.extend(p.context);
    b.extend((stage as u64).to_le_bytes());
    b.extend(left);
    b.extend(right);
    hash(&b)
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Opening {
    salt: [u8; 32],
    path: Vec<[u8; 32]>,
}
fn tree(
    p: &Profile,
    stage: usize,
    rows: &[Vec<Field>],
    seed: [u8; 32],
) -> ([u8; 32], Vec<Opening>) {
    let width = p.n.next_power_of_two();
    let mut salts = vec![];
    let mut level = vec![];
    for i in 0..width {
        let salt = entropy(seed, p.context, 1, stage * 32 + i);
        salts.push(salt);
        level.push(leaf(
            p,
            stage,
            i,
            rows.get(i).map(Vec::as_slice).unwrap_or(&[]),
            salt,
        ));
    }
    let mut levels = vec![level];
    while levels.last().unwrap().len() > 1 {
        let next = levels
            .last()
            .unwrap()
            .chunks_exact(2)
            .map(|v| node(p, stage, v[0], v[1]))
            .collect();
        levels.push(next);
    }
    let opens = (0..p.n)
        .map(|i| {
            let mut j = i;
            let mut path = vec![];
            for l in &levels[..levels.len() - 1] {
                path.push(l[j ^ 1]);
                j /= 2;
            }
            Opening {
                salt: salts[i],
                path,
            }
        })
        .collect();
    (levels.last().unwrap()[0], opens)
}
fn check_opening(
    p: &Profile,
    stage: usize,
    holder: u16,
    values: &[Field],
    opening: &Opening,
    root: [u8; 32],
) -> bool {
    if holder as usize >= p.n || opening.path.len() != p.path_len() {
        return false;
    }
    let mut h = leaf(p, stage, holder as usize, values, opening.salt);
    let mut j = holder as usize;
    for sibling in &opening.path {
        h = if j & 1 == 0 {
            node(p, stage, h, *sibling)
        } else {
            node(p, stage, *sibling, h)
        };
        j /= 2;
    }
    h == root
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PublicProof {
    roots: Vec<[u8; 32]>,
    final_poly: Vec<Field>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PrivateProof {
    holder: u16,
    mask: Field,
    blocks: Vec<[Field; 2]>,
    openings: Vec<Opening>,
}
pub fn encode_public(p: &Profile, v: &PublicProof) -> Vec<u8> {
    let mut b = b"DREGG.DZK.PUBLIC\x01".to_vec();
    b.extend(p.context);
    b.push(v.roots.len() as u8);
    for r in &v.roots {
        b.extend(r);
    }
    b.push(v.final_poly.len() as u8);
    fields(&mut b, &v.final_poly);
    b
}
pub fn decode_public(p: &Profile, b: &[u8]) -> Result<PublicProof> {
    let mut c = Cursor::new(b)?;
    if b.len() != p.public_len()
        || c.take(17)? != b"DREGG.DZK.PUBLIC\x01"
        || c.fixed32()? != p.context
        || c.byte()? as usize != p.degrees().len()
    {
        return Err(bad("dZK public context/shape"));
    }
    let roots = (0..p.degrees().len())
        .map(|_| c.fixed32())
        .collect::<Result<_>>()?;
    let count = c.byte()? as usize;
    if count != p.degrees().last().unwrap() + 1 {
        return Err(bad("dZK final degree"));
    }
    let final_poly = read_fields(&mut c, count)?;
    c.finish()?;
    Ok(PublicProof { roots, final_poly })
}
pub fn encode_private(p: &Profile, v: &PrivateProof) -> Vec<u8> {
    let mut b = b"DREGG.DZK.PRIVATE\x01".to_vec();
    b.extend(p.context);
    b.extend(v.holder.to_le_bytes());
    fields(&mut b, &[v.mask]);
    for pair in &v.blocks {
        fields(&mut b, pair);
    }
    for opening in &v.openings {
        b.extend(opening.salt);
        for sibling in &opening.path {
            b.extend(sibling);
        }
    }
    b
}
pub fn decode_private(p: &Profile, b: &[u8]) -> Result<PrivateProof> {
    let mut c = Cursor::new(b)?;
    if b.len() != p.private_len()
        || c.take(18)? != b"DREGG.DZK.PRIVATE\x01"
        || c.fixed32()? != p.context
    {
        return Err(bad("dZK private context/shape"));
    }
    let holder = c.u16()?;
    if holder as usize >= p.n {
        return Err(bad("dZK private holder"));
    }
    let mask = read_fields(&mut c, 1)?[0];
    let mut blocks = vec![];
    for _ in 1..p.degrees().len() {
        let pair = read_fields(&mut c, 2)?;
        blocks.push([pair[0], pair[1]]);
    }
    let mut openings = vec![];
    for _ in 0..p.degrees().len() {
        let salt = c.fixed32()?;
        let path = (0..p.path_len())
            .map(|_| c.fixed32())
            .collect::<Result<_>>()?;
        openings.push(Opening { salt, path });
    }
    c.finish()?;
    Ok(PrivateProof {
        holder,
        mask,
        blocks,
        openings,
    })
}
/// Deterministic from retained high-entropy seed and exact polynomial coefficients.
/// Each randomness draw is domain-separated; the seed itself is never transmitted.
pub fn prove(
    p: &Profile,
    polys: &[Vec<Field>],
    seed: [u8; 32],
) -> Result<(PublicProof, Vec<PrivateProof>)> {
    if polys.len() != p.count || polys.iter().any(|f| f.len() != p.degree + 1) {
        return Err(bad("dZK polynomial count/degree"));
    }
    let random_poly: Vec<_> = (0..=p.degree)
        .map(|i| {
            Field(u128::from_le_bytes(
                entropy(seed, p.context, 0, i)[..16].try_into().unwrap(),
            ))
        })
        .collect();
    let mut rows = vec![];
    for i in 0..p.n {
        let x = Field(i as u128 + 1);
        let mut row = vec![eval(&random_poly, x)];
        row.extend(polys.iter().map(|f| eval(f, x)));
        rows.push(row);
    }
    let (r0, opening0) = tree(p, 0, &rows, seed);
    let mut roots = vec![r0];
    let mut privates: Vec<_> = (0..p.n)
        .map(|i| PrivateProof {
            holder: i as u16,
            mask: rows[i][0],
            blocks: vec![],
            openings: vec![opening0[i].clone()],
        })
        .collect();
    let mu = challenge(p, &roots);
    let mut current = random_poly;
    let mut power = mu;
    for f in polys {
        for (z, c) in current.iter_mut().zip(f) {
            *z = z.add(power.mul(*c));
        }
        power = power.mul(mu);
    }
    let ds = p.degrees();
    for stage in 1..ds.len() {
        let shift = ds[stage - 1] - ds[stage];
        // f = g0 + X^shift*g1, including odd-degree boundaries.
        let mut g0 = vec![Field(0); ds[stage] + 1];
        let mut g1 = g0.clone();
        for (i, c) in current.iter().enumerate() {
            if i < shift {
                g0[i] = *c;
            } else {
                g1[i - shift] = *c;
            }
        }
        let rows: Vec<_> = (0..p.n)
            .map(|i| {
                vec![
                    eval(&g0, Field(i as u128 + 1)),
                    eval(&g1, Field(i as u128 + 1)),
                ]
            })
            .collect();
        let (r, opens) = tree(p, stage, &rows, seed);
        roots.push(r);
        for i in 0..p.n {
            privates[i].blocks.push([rows[i][0], rows[i][1]]);
            privates[i].openings.push(opens[i].clone());
        }
        let mu = challenge(p, &roots);
        current = g0
            .into_iter()
            .zip(g1)
            .map(|(a, b)| a.add(mu.mul(b)))
            .collect();
    }
    Ok((
        PublicProof {
            roots,
            final_poly: current,
        },
        privates,
    ))
}
fn verify(
    p: &Profile,
    public: &PublicProof,
    private: &PrivateProof,
    holder: u16,
    shares: &[Field],
) -> bool {
    let ds = p.degrees();
    if holder as usize >= p.n
        || private.holder != holder
        || shares.len() != p.count
        || public.roots.len() != ds.len()
        || public.final_poly.len() != ds.last().unwrap() + 1
        || private.blocks.len() + 1 != ds.len()
        || private.openings.len() != ds.len()
    {
        return false;
    }
    let mut row = vec![private.mask];
    row.extend(shares);
    if !check_opening(p, 0, holder, &row, &private.openings[0], public.roots[0]) {
        return false;
    }
    let x = Field(holder as u128 + 1);
    let mu0 = challenge(p, &public.roots[..1]);
    let mut initial = private.mask;
    let mut power = mu0;
    for s in shares {
        initial = initial.add(power.mul(*s));
        power = power.mul(mu0);
    }
    let mut previous = initial;
    for stage in 1..ds.len() {
        let pair = private.blocks[stage - 1];
        if !check_opening(
            p,
            stage,
            holder,
            &pair,
            &private.openings[stage],
            public.roots[stage],
        ) || previous != pair[0].add(pow(x, ds[stage - 1] - ds[stage]).mul(pair[1]))
        {
            return false;
        }
        previous = pair[0].add(challenge(p, &public.roots[..=stage]).mul(pair[1]));
    }
    previous == eval(&public.final_poly, x)
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Delivered {
    context: [u8; 32],
    public_bytes: Vec<u8>,
    local_bytes: Vec<u8>,
}
impl Delivered {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn public_bytes(&self) -> &[u8] {
        &self.public_bytes
    }
    pub fn local_bytes(&self) -> &[u8] {
        &self.local_bytes
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedShares {
    context: [u8; 32],
    holder: u16,
    receiver: u16,
    values: Vec<Field>,
    public_hash: [u8; 32],
}
impl VerifiedShares {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn holder(&self) -> u16 {
        self.holder
    }
    pub fn receiver(&self) -> u16 {
        self.receiver
    }
    pub fn values(&self) -> &[Field] {
        &self.values
    }
    pub fn public_hash(&self) -> [u8; 32] {
        self.public_hash
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RejectedProof {
    context: [u8; 32],
    holder: u16,
    receiver: u16,
    evidence_hash: [u8; 32],
}
impl RejectedProof {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn holder(&self) -> u16 {
        self.holder
    }
    pub fn receiver(&self) -> u16 {
        self.receiver
    }
    pub fn evidence_hash(&self) -> [u8; 32] {
        self.evidence_hash
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Verification {
    Accepted(VerifiedShares),
    Rejected(RejectedProof),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OpenProof {
    verification: Verification,
    public_bytes: Vec<u8>,
    private_bytes: Vec<u8>,
    values: Vec<Field>,
}
impl OpenProof {
    pub fn verification(&self) -> &Verification {
        &self.verification
    }
    pub fn public_bytes(&self) -> &[u8] {
        &self.public_bytes
    }
    pub fn private_bytes(&self) -> &[u8] {
        &self.private_bytes
    }
    pub fn values(&self) -> &[Field] {
        &self.values
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Transferred {
    context: [u8; 32],
    holder: u16,
    receiver: u16,
    public_hash: [u8; 32],
}
impl Transferred {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn holder(&self) -> u16 {
        self.holder
    }
    pub fn receiver(&self) -> u16 {
        self.receiver
    }
    pub fn public_hash(&self) -> [u8; 32] {
        self.public_hash
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Body {
    Public(PhaseMessage),
    Private {
        holder: u16,
        message: private_send::Message,
    },
    Transfer {
        receiver: u16,
        holder: u16,
        values: Vec<Field>,
        proof: Vec<u8>,
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
#[derive(Clone)]
pub struct Dzk {
    pub me: u16,
    pub profile: Profile,
    public: Bracha,
    private: Vec<PrivateSend>,
    started: bool,
    local_requested: bool,
    pending: BTreeMap<u16, (Vec<Field>, Vec<u8>)>,
    received: BTreeMap<u16, VerifiedShares>,
    dealer_inputs: Option<Vec<Vec<Field>>>,
}
impl Dzk {
    pub fn new(
        me: u16,
        dealer: u16,
        n: usize,
        f: usize,
        g: &Generation,
        count: usize,
        degree: usize,
    ) -> Result<Self> {
        let p = Profile::new(n, f, dealer, g, count, degree)?;
        if me as usize >= n {
            return Err(bad("dZK local party"));
        }
        let private = (0..n)
            .map(|j| {
                PrivateSend::new(
                    me,
                    dealer,
                    n,
                    f,
                    &p.holder_generation(g, j as u16),
                    p.private_len(),
                )
            })
            .collect::<Result<_>>()?;
        Ok(Self {
            me,
            profile: p,
            public: Bracha::new(n, f, Some(dealer)),
            private,
            started: false,
            local_requested: false,
            pending: BTreeMap::new(),
            received: BTreeMap::new(),
            dealer_inputs: None,
        })
    }
    fn wrap_private(&self, holder: u16, ps: Vec<private_send::Send>) -> Vec<Send> {
        ps.into_iter()
            .map(|s| Send {
                to: s.to,
                message: Message {
                    context: self.profile.context,
                    body: Body::Private {
                        holder,
                        message: s.message,
                    },
                },
            })
            .collect()
    }
    fn all(&self, body: Body) -> Vec<Send> {
        (0..self.profile.n)
            .map(|i| Send {
                to: i as u16,
                message: Message {
                    context: self.profile.context,
                    body: body.clone(),
                },
            })
            .collect()
    }
    /// Caller MUST persist seed, coefficients and exact outbox before transmitting.
    pub fn dealer(&mut self, polys: &[Vec<Field>], seed: [u8; 32]) -> Result<Vec<Send>> {
        if self.me != self.profile.dealer || self.started {
            return Err(bad("dZK dealer/replay"));
        }
        let (public, private) = prove(&self.profile, polys, seed)?;
        let mut out = vec![];
        for (j, proof) in private.iter().enumerate() {
            let mut coeff = vec![vec![]; 2];
            for (k, p) in coeff.iter_mut().enumerate() {
                for l in 0..=self.profile.f {
                    p.push(Field(u128::from_le_bytes(
                        entropy(seed, self.profile.context, 2, j * 32 + k * 16 + l)[..16]
                            .try_into()
                            .unwrap(),
                    )));
                }
            }
            let ps = self.private[j]
                .dealer_with_coefficients(&encode_private(&self.profile, proof), &coeff)?;
            out.extend(self.wrap_private(j as u16, ps));
        }
        out.extend(self.all(Body::Public(PhaseMessage::Init(encode_public(
            &self.profile,
            &public,
        )))));
        self.dealer_inputs = Some(polys.to_vec());
        self.started = true;
        Ok(out)
    }
    /// Exact environment/source request, NOT a serialized permission bool.
    pub fn authorize_verification(&mut self, holder: u16, receiver: u16) -> Result<Vec<Send>> {
        if holder as usize >= self.profile.n || receiver as usize >= self.profile.n {
            return Err(bad("dZK verification roster"));
        }
        let ps = self.private[holder as usize].request_delivery(receiver)?;
        let mut out = self.wrap_private(holder, ps);
        out.extend(self.progress()?);
        Ok(out)
    }
    pub fn receive(&mut self, sender: u16, m: Message) -> Result<Vec<Send>> {
        if sender as usize >= self.profile.n || m.context != self.profile.context {
            return Err(bad("dZK foreign sender/context"));
        }
        let mut out = vec![];
        match m.body {
            Body::Public(phase) => {
                if phase_bytes(&phase).len() != self.profile.public_len() {
                    return Err(bad("dZK public frame shape"));
                }
                for phase in self.public.receive(sender, phase) {
                    out.extend(self.all(Body::Public(phase)));
                }
            }
            Body::Private { holder, message } => {
                if holder as usize >= self.profile.n {
                    return Err(bad("dZK private instance"));
                }
                let ps = self.private[holder as usize].receive(sender, message)?;
                out.extend(self.wrap_private(holder, ps));
            }
            Body::Transfer {
                receiver,
                holder,
                values,
                proof,
            } => {
                if receiver != self.me
                    || holder != sender
                    || values.len() != self.profile.count
                    || proof.len() != self.profile.private_len()
                {
                    return Err(bad("dZK transfer sender/recipient/shape"));
                }
                if self.delivered().is_some() {
                    let public = self.public.output.as_ref().unwrap();
                    let v = self.check_bytes(holder, &values, &proof, public);
                    if let Verification::Accepted(accepted) = v {
                        self.received.entry(holder).or_insert(accepted);
                    }
                } else {
                    self.pending.entry(holder).or_insert((values, proof));
                }
            }
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    fn progress(&mut self) -> Result<Vec<Send>> {
        let mut out = vec![];
        if !self.local_requested && self.private.iter().all(|s| s.dispersed) {
            self.local_requested = true;
            for j in 0..self.profile.n {
                let ps = self.private[j].request_delivery(j as u16)?;
                out.extend(self.wrap_private(j as u16, ps));
            }
        }
        if self.delivered().is_some() {
            let public = self.public.output.clone().unwrap();
            let pending = std::mem::take(&mut self.pending);
            for (holder, (values, proof)) in pending {
                if let Verification::Accepted(v) =
                    self.check_bytes(holder, &values, &proof, &public)
                {
                    self.received.entry(holder).or_insert(v);
                }
            }
        }
        Ok(out)
    }
    pub fn delivered(&self) -> Option<Delivered> {
        if !self.private.iter().all(|s| s.dispersed) {
            return None;
        }
        Some(Delivered {
            context: self.profile.context,
            public_bytes: self.public.output.clone()?,
            local_bytes: self.private[self.me as usize].delivered.clone()?,
        })
    }
    fn check_bytes(
        &self,
        holder: u16,
        values: &[Field],
        proof: &[u8],
        public: &[u8],
    ) -> Verification {
        let accepted = decode_public(&self.profile, public)
            .and_then(|p| {
                decode_private(&self.profile, proof)
                    .map(|v| verify(&self.profile, &p, &v, holder, values))
            })
            .unwrap_or(false);
        if accepted {
            Verification::Accepted(VerifiedShares {
                context: self.profile.context,
                holder,
                receiver: self.me,
                values: values.to_vec(),
                public_hash: hash(public),
            })
        } else {
            let mut b = b"DREGG.DZK.REJECTION.V1".to_vec();
            b.extend(self.profile.context);
            b.extend(holder.to_le_bytes());
            b.extend(self.me.to_le_bytes());
            bytes(public, &mut b);
            bytes(proof, &mut b);
            fields(&mut b, values);
            Verification::Rejected(RejectedProof {
                context: self.profile.context,
                holder,
                receiver: self.me,
                evidence_hash: hash(&b),
            })
        }
    }
    pub(crate) fn dealer_inputs(&self) -> Option<&[Vec<Field>]> {
        self.dealer_inputs.as_deref()
    }
    pub fn verify_private(&self, holder: u16, values: &[Field]) -> Result<Verification> {
        if self.delivered().is_none() {
            return Err(Error::new(
                ErrorKind::WouldBlock,
                "dZK distributing phase not delivered",
            ));
        }
        if holder as usize >= self.profile.n || values.len() != self.profile.count {
            return Err(bad("dZK share roster/count"));
        }
        let public = self
            .public
            .output
            .as_ref()
            .ok_or_else(|| Error::new(ErrorKind::WouldBlock, "dZK public not delivered"))?;
        let private = self.private[holder as usize]
            .delivered
            .as_ref()
            .ok_or_else(|| {
                Error::new(
                    ErrorKind::WouldBlock,
                    "dZK private proof not delivered to verifier",
                )
            })?;
        Ok(self.check_bytes(holder, values, private, public))
    }
    /// Only source-authorized callers may publicly release this private view.
    /// This method supplies evidence; it does not itself grant declassification.
    pub fn open_proof(&self, holder: u16, values: &[Field]) -> Result<OpenProof> {
        let verification = self.verify_private(holder, values)?;
        Ok(OpenProof {
            verification,
            public_bytes: self.public.output.clone().unwrap(),
            private_bytes: self.private[holder as usize].delivered.clone().unwrap(),
            values: values.to_vec(),
        })
    }
    pub fn transfer(&self, receiver: u16, values: &[Field]) -> Result<(Transferred, Vec<Send>)> {
        if receiver as usize >= self.profile.n {
            return Err(bad("dZK transfer receiver"));
        }
        let accepted = match self.verify_private(self.me, values)? {
            Verification::Accepted(v) => v,
            Verification::Rejected(_) => {
                return Err(bad("dZK invalid local proof cannot transfer"))
            }
        };
        Ok((
            Transferred {
                context: self.profile.context,
                holder: self.me,
                receiver,
                public_hash: accepted.public_hash,
            },
            vec![Send {
                to: receiver,
                message: Message {
                    context: self.profile.context,
                    body: Body::Transfer {
                        receiver,
                        holder: self.me,
                        values: values.to_vec(),
                        proof: self.private[self.me as usize].delivered.clone().unwrap(),
                    },
                },
            }],
        ))
    }
    pub fn transferred(&self, holder: u16) -> Option<&VerifiedShares> {
        self.received.get(&holder)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;
    pub(super) fn generation() -> Generation {
        Generation {
            invocation: Nat::new(91),
            command: vec![9],
            attempt: Nat::new(0),
            generation: Nat::new(1),
            configuration: Nat::new(7),
        }
    }
    fn p(degree: usize, count: usize) -> Profile {
        Profile::new(4, 1, 0, &generation(), count, degree).unwrap()
    }
    fn polys(d: usize, n: usize) -> Vec<Vec<Field>> {
        (0..n)
            .map(|j| {
                (0..=d)
                    .map(|k| Field((1 + j * 13 + k * 7) as u128))
                    .collect()
            })
            .collect()
    }
    fn drain(ns: &mut [Dzk], q: &mut VecDeque<(u16, Send)>, drop: Option<u16>) {
        let mut count = 0;
        while let Some((sender, s)) = q.pop_back() {
            count += 1;
            assert!(count < 200000);
            if Some(sender) == drop || Some(s.to) == drop {
                continue;
            }
            let to = s.to;
            let out = ns[to as usize].receive(sender, s.message).unwrap();
            q.extend(out.into_iter().map(|s| (to, s)));
        }
    }
    #[test]
    fn compression_all_degrees_and_malformed_share_opening_final_polynomial() {
        for degree in 0..4 {
            let profile = p(degree, 3);
            let polys = polys(degree, 3);
            let (public, private) = prove(&profile, &polys, [37; 32]).unwrap();
            for i in 0..4 {
                let values: Vec<_> = polys
                    .iter()
                    .map(|f| eval(f, Field(i as u128 + 1)))
                    .collect();
                assert!(verify(&profile, &public, &private[i], i as u16, &values));
                let mut wrong = values.clone();
                wrong[0] = wrong[0].add(Field(1));
                assert!(!verify(&profile, &public, &private[i], i as u16, &wrong));
                let mut bad = private[i].clone();
                bad.openings[0].salt[0] ^= 1;
                assert!(!verify(&profile, &public, &bad, i as u16, &values));
                let mut bad = public.clone();
                bad.final_poly[0] = bad.final_poly[0].add(Field(1));
                assert!(!verify(&profile, &bad, &private[i], i as u16, &values));
                assert_eq!(
                    decode_private(&profile, &encode_private(&profile, &private[i])).unwrap(),
                    private[i]
                );
            }
            assert_eq!(
                decode_public(&profile, &encode_public(&profile, &public)).unwrap(),
                public
            );
        }
    }
    #[test]
    fn real_privsend_delivery_verification_transfer_and_openproof() {
        let g = generation();
        let fs = polys(1, 2);
        let mut ns: Vec<_> = (0..4)
            .map(|i| Dzk::new(i, 0, 4, 1, &g, 2, 1).unwrap())
            .collect();
        let mut q: VecDeque<_> = ns[0]
            .dealer(&fs, [31; 32])
            .unwrap()
            .into_iter()
            .map(|s| (0, s))
            .collect();
        drain(&mut ns, &mut q, None);
        assert!(ns.iter().all(|n| n.delivered().is_some()));
        let values: Vec<_> = fs.iter().map(|f| eval(f, Field(2))).collect();
        assert!(ns[2].verify_private(1, &values).is_err());
        for node in &mut ns {
            let me = node.me;
            for s in node.authorize_verification(1, 2).unwrap() {
                q.push_back((me, s));
            }
        }
        drain(&mut ns, &mut q, Some(3));
        assert!(matches!(
            ns[2].verify_private(1, &values).unwrap(),
            Verification::Accepted(_)
        ));
        let opened = ns[2].open_proof(1, &values).unwrap();
        assert!(matches!(opened.verification(), Verification::Accepted(_)));
        let mut wrong = values.clone();
        wrong[0] = wrong[0].add(Field(1));
        assert!(matches!(
            ns[2].open_proof(1, &wrong).unwrap().verification(),
            Verification::Rejected(_)
        ));
        let (receipt, sends) = ns[1].transfer(2, &values).unwrap();
        assert_eq!(receipt.holder(), 1);
        for send in sends {
            let mut cross = send.message.clone();
            if let Body::Transfer { receiver, .. } = &mut cross.body {
                *receiver = 3;
            }
            assert!(ns[2].receive(1, cross).is_err());
            let mut forged = send.message.clone();
            if let Body::Transfer { holder, .. } = &mut forged.body {
                *holder = 0;
            }
            assert!(ns[2].receive(1, forged).is_err());
            let mut tamper = send.message.clone();
            tamper.context[0] ^= 1;
            assert!(ns[2].receive(1, tamper).is_err());
            ns[2].receive(1, send.message).unwrap();
        }
        assert_eq!(ns[2].transferred(1).unwrap().values(), values);
        assert!(ns[1].transfer(2, &wrong).is_err());
    }
    #[test]
    fn compressed_seven_party_pipeline_survives_two_withheld_parties() {
        let g = generation();
        let fs = polys(2, 2);
        let mut ns: Vec<_> = (0..7)
            .map(|i| Dzk::new(i, 0, 7, 2, &g, 2, 2).unwrap())
            .collect();
        let mut q: VecDeque<_> = ns[0]
            .dealer(&fs, [71; 32])
            .unwrap()
            .into_iter()
            .map(|s| (0, s))
            .collect();
        // Two corrupted parties contribute nothing; five honest parties suffice.
        let mut steps = 0;
        while let Some((sender, s)) = q.pop_back() {
            steps += 1;
            assert!(steps < 200000);
            if sender >= 5 || s.to >= 5 {
                continue;
            }
            let to = s.to;
            let out = ns[to as usize].receive(sender, s.message).unwrap();
            q.extend(out.into_iter().map(|s| (to, s)));
        }
        for (i, node) in ns[..5].iter().enumerate() {
            assert!(node.delivered().is_some());
            let values: Vec<_> = fs.iter().map(|f| eval(f, Field(i as u128 + 1))).collect();
            assert!(matches!(
                node.verify_private(i as u16, &values).unwrap(),
                Verification::Accepted(_)
            ));
        }
    }
    #[test]
    fn malformed_dealer_public_proof_is_delivered_but_rejected_not_success() {
        let g = generation();
        let fs = polys(1, 2);
        let mut ns: Vec<_> = (0..4)
            .map(|i| Dzk::new(i, 0, 4, 1, &g, 2, 1).unwrap())
            .collect();
        let mut out = ns[0].dealer(&fs, [31; 32]).unwrap();
        for s in &mut out {
            if let Body::Public(PhaseMessage::Init(b)) = &mut s.message.body {
                let last = b.len() - 1;
                b[last] ^= 1;
            }
        }
        let mut q = out.into_iter().map(|s| (0, s)).collect();
        drain(&mut ns, &mut q, None);
        for (i, node) in ns.iter().enumerate() {
            assert!(node.delivered().is_some());
            let values: Vec<_> = fs.iter().map(|f| eval(f, Field(i as u128 + 1))).collect();
            assert!(matches!(
                node.open_proof(i as u16, &values).unwrap().verification(),
                Verification::Rejected(_)
            ));
            assert!(node.transfer(2, &values).is_err());
        }
    }
    #[test]
    fn malformed_and_early_transfer_are_reverified_against_delivered_public_proof() {
        let g = generation();
        let fs = polys(1, 1);
        let mut ns: Vec<_> = (0..4)
            .map(|i| Dzk::new(i, 0, 4, 1, &g, 1, 1).unwrap())
            .collect();
        let initial = ns[0].dealer(&fs, [81; 32]).unwrap();
        let mut q = initial.clone().into_iter().map(|s| (0, s)).collect();
        drain(&mut ns, &mut q, None);
        let values = vec![eval(&fs[0], Field(2))];
        let transfer = ns[1].transfer(2, &values).unwrap().1[0].message.clone();
        let mut bad = transfer.clone();
        if let Body::Transfer { proof, .. } = &mut bad.body {
            let last = proof.len() - 1;
            proof[last] ^= 1;
        }
        ns[2].receive(1, bad).unwrap();
        assert!(ns[2].transferred(1).is_none());
        // A genuine transfer reaches party2 before its own distribution traffic.
        let mut late = Dzk::new(2, 0, 4, 1, &g, 1, 1).unwrap();
        late.receive(1, transfer).unwrap();
        assert!(late.transferred(1).is_none());
        ns[2] = late;
        let mut q = initial.into_iter().map(|s| (0, s)).collect();
        // Honest other nodes replay their retained deterministic outboxes by running
        // a fresh protocol population; only the genuine early transfer is retained.
        let late = ns[2].clone();
        ns = (0..4)
            .map(|i| Dzk::new(i, 0, 4, 1, &g, 1, 1).unwrap())
            .collect();
        ns[2] = late;
        drain(&mut ns, &mut q, None);
        assert_eq!(ns[2].transferred(1).unwrap().values(), values);
    }
    #[test]
    fn cross_generation_and_noncanonical_proof_shape_refuse() {
        let a = p(1, 1);
        let (public, private) = prove(&a, &polys(1, 1), [17; 32]).unwrap();
        let mut g = generation();
        g.attempt = Nat::new(2);
        let b = Profile::new(4, 1, 0, &g, 1, 1).unwrap();
        assert!(decode_public(&b, &encode_public(&a, &public)).is_err());
        assert!(decode_private(&b, &encode_private(&a, &private[0])).is_err());
        let mut encoded = encode_private(&a, &private[0]);
        encoded.push(0);
        assert!(decode_private(&a, &encoded).is_err());
        assert!(prove(&a, &[vec![Field(1)]], [0; 32]).is_err());
    }
}
