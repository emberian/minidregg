//! Concrete TripleKingDN random extraction and asynchronous polynomial check.
//! Consumes actual accepted ACSS/Sh2t material, never an ideal triple supplier.
//! Stable preprocessing identities are durably burned before share extraction.
//! Static GF128/classical ROM reference. Failed checks can privately reconstruct
//! actual Sh2t zero material and publish a retained dispute pair. Full accusation
//! availability, dispute elimination/ACS, simulator and GOD MPC remain open.
use crate::{
    acss_id::{self, AcssId},
    asks::{Bracha, PhaseMessage},
    codec::{bad, bytes, Correlation, Generation, Journal, Nat, Purpose},
    custody::{self, hash},
    reconstruction::Field,
    sh2t_id::{self, Sh2tId},
};
use std::{
    collections::BTreeMap,
    io::{Error, ErrorKind, Result},
    path::Path,
};
fn eval(p: &[Field], x: Field) -> Field {
    p.iter().rev().fold(Field(0), |a, c| a.mul(x).add(*c))
}
fn power(x: Field, n: usize) -> Field {
    (0..n).fold(Field(1), |a, _| a.mul(x))
}
pub fn per_group(n_triples: usize, f: usize) -> Result<usize> {
    if n_triples == 0 || n_triples > 32 || f == 0 {
        return Err(bad("triple public count"));
    }
    Ok((2 * n_triples + 1 + f) / (f + 1))
}
pub fn acss_seed_count(n_triples: usize, f: usize) -> Result<usize> {
    let count = 3 * per_group(n_triples, f)? + 1;
    Ok((count + f) / (f + 1) * (f + 1))
}
#[derive(Clone)]
pub struct PreparedSource {
    degree_f_generation: Generation,
    degree_2f_generation: Generation,
    acss: AcssId,
    sh2t: Sh2tId,
}
impl PreparedSource {
    /// Exact actual protocol states and declared full generations, not decoded
    /// local-sharing claims. Native source manifest/one-use group authorization
    /// remains required; this constructor does not grant it.
    pub fn new(
        acss: AcssId,
        sh2t: Sh2tId,
        degree_f_generation: Generation,
        degree_2f_generation: Generation,
    ) -> Result<Self> {
        if acss.me != sh2t.me || acss.dealer != sh2t.dealer || acss.n != sh2t.n || acss.f != sh2t.f
        {
            return Err(bad("preparation profile mismatch"));
        }
        let expected = AcssId::new(
            acss.me,
            acss.dealer,
            acss.n,
            acss.f,
            &degree_f_generation,
            acss.count,
        )?;
        let expected2 = Sh2tId::new(
            sh2t.me,
            sh2t.dealer,
            sh2t.n,
            sh2t.f,
            &degree_2f_generation,
            sh2t.per_group,
        )?;
        if expected.context != acss.context || expected2.context != sh2t.context {
            return Err(bad("exact preparation generation context"));
        }
        Ok(Self {
            acss,
            sh2t,
            degree_f_generation,
            degree_2f_generation,
        })
    }
}
#[derive(Clone)]
struct RandomShares {
    a: Vec<Field>,
    b: Vec<Field>,
    r: Vec<Field>,
    o: Vec<Field>,
    check_r: Field,
}
#[derive(Clone)]
pub struct PreparedBasis {
    me: u16,
    n: usize,
    f: usize,
    king: u16,
    count: usize,
    group: usize,
    sources: Vec<PreparedSource>,
    random: RandomShares,
    bytes: Vec<u8>,
    consumer_generation: Generation,
    preparation_rows: Vec<Correlation>,
}
impl PreparedBasis {
    /// Local coherent degree-f / committed degree-2f inputs. Neither zero
    /// correctness nor uniform entropy follows from a malicious dealer label.
    /// Honest dealer randomness and later full zero/triple checks are premises.
    pub fn reserve_new(
        consumer: &Generation,
        king: u16,
        count: usize,
        group: usize,
        mut sources: Vec<PreparedSource>,
        anchor: &Path,
        local: &Path,
    ) -> Result<Self> {
        if sources.is_empty() {
            return Err(bad("empty preparation basis"));
        }
        let n = sources[0].acss.n;
        let f = sources[0].acss.f;
        let me = sources[0].acss.me;
        let batch = per_group(count, f)?;
        let seed_count = acss_seed_count(count, f)?;
        if sources.len() != 2 * f + 1
            || king as usize >= n
            || group / n != king as usize
            || group >= n * n
        {
            return Err(bad("public king/dealer/group mapping"));
        }
        sources.sort_by_key(|s| s.acss.dealer);
        if sources
            .windows(2)
            .any(|p| p[0].acss.dealer == p[1].acss.dealer)
        {
            return Err(bad("duplicate source dealer"));
        }
        // PUBLIC manifest preflight: no accepted share getter before the entire
        // fixed allocation is anchored. IDs omit consumer attempt/epoch so a
        // fresh consumer cannot relabel an already used preparation as fresh.
        let mut binding = b"DREGG.TRIPLE.KING.PREPARED.V2".to_vec();
        let mut ids = vec![];
        for source in &sources {
            let a = &source.acss;
            let o = &source.sh2t;
            if a.me != me || a.n != n || a.f != f || a.count < seed_count || o.per_group != batch {
                return Err(bad("prepared public source capacity"));
            }
            binding.extend(a.dealer.to_le_bytes());
            source.degree_f_generation.put(&mut binding);
            source.degree_2f_generation.put(&mut binding);
            binding.extend(a.context);
            binding.extend(o.context);
            for (domain, g, context, row) in [
                (
                    &b"DREGG.PREPARATION.ACSS.SEEDS.V1"[..],
                    &source.degree_f_generation,
                    a.context,
                    0,
                ),
                (
                    &b"DREGG.PREPARATION.SH2T.GROUP.V1"[..],
                    &source.degree_2f_generation,
                    o.context,
                    group,
                ),
            ] {
                let mut identity = vec![];
                bytes(domain, &mut identity);
                g.put(&mut identity);
                identity.extend(context);
                ids.push(Correlation {
                    pool: Nat::from_be(&hash(&identity)),
                    row: Nat::new(row as u64),
                });
            }
        }
        for v in [n, f, count, group] {
            binding.extend((v as u64).to_le_bytes());
        }
        binding.extend(king.to_le_bytes());
        burn_preparation(&ids, consumer, &binding, anchor, local)?;
        let mut degree_f = vec![];
        let mut degree_2f = vec![];
        let mut bytes = b"DREGG.TRIPLE.KING.PREPARED.V2".to_vec();
        for source in &sources {
            let a = &source.acss;
            let o = &source.sh2t;
            if a.me != me || a.n != n || a.f != f || a.count < seed_count || o.per_group != batch {
                return Err(bad("prepared source capacity"));
            }
            let accepted = match a.local_sharing() {
                Some(acss_id::LocalSharing::Accepted(v)) => v,
                Some(acss_id::LocalSharing::Rejected(_)) => {
                    return Err(Error::new(
                        ErrorKind::InvalidData,
                        "actual ACSS rejection requires accusation continuation",
                    ))
                }
                None => return Err(Error::new(ErrorKind::WouldBlock, "ACSS incomplete")),
            };
            let accepted2 = match o.local_sharing() {
                Some(sh2t_id::LocalSharing::Accepted(v)) => v,
                Some(sh2t_id::LocalSharing::Rejected(_)) => {
                    return Err(Error::new(
                        ErrorKind::InvalidData,
                        "actual Sh2t rejection requires accusation continuation",
                    ))
                }
                None => return Err(Error::new(ErrorKind::WouldBlock, "Sh2t incomplete")),
            };
            if accepted.holder() != me
                || accepted.context() != a.context
                || accepted2.holder() != me
                || accepted2.context() != o.context
            {
                return Err(bad("prepared local accepted holder"));
            }
            degree_f.push(accepted.shares().to_vec());
            degree_2f.push(accepted2.values()[group * batch..(group + 1) * batch].to_vec());
            bytes.extend(a.dealer.to_le_bytes());
            source.degree_f_generation.put(&mut bytes);
            source.degree_2f_generation.put(&mut bytes);
            bytes.extend(a.context);
            bytes.extend(o.context);
        }
        for v in [n, f, count, group] {
            bytes.extend((v as u64).to_le_bytes());
        }
        bytes.extend(king.to_le_bytes());
        let m = 2 * count + 1;
        let extract = |seeds: &[Vec<Field>], offset: usize| -> Vec<Field> {
            let mut out = vec![];
            for index in 0..batch {
                for row in 0..=f {
                    let v = seeds.iter().enumerate().fold(Field(0), |sum, (column, s)| {
                        sum.add(power(Field(column as u128 + 1), row).mul(s[offset + index]))
                    });
                    out.push(v);
                }
            }
            out.truncate(m);
            out
        };
        let a = extract(&degree_f, 0);
        let b = extract(&degree_f, batch);
        let r = extract(&degree_f, 2 * batch);
        let o = extract(&degree_2f, 0);
        let check_r = degree_f.iter().fold(Field(0), |v, s| v.add(s[3 * batch]));
        Ok(Self {
            me,
            n,
            f,
            king,
            count,
            group,
            sources,
            random: RandomShares {
                a,
                b,
                r,
                o,
                check_r,
            },
            bytes,
            consumer_generation: consumer.clone(),
            preparation_rows: ids,
        })
    }
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
    pub fn group(&self) -> usize {
        self.group
    }
    pub fn sources(&self) -> &[PreparedSource] {
        &self.sources
    }
}
/// Local rollback-service implementation tests crash ordering, not an
/// independently protected malicious-storage anchor or native funded authority.
pub(crate) fn burn_preparation(
    ids: &[Correlation],
    g: &Generation,
    binding: &[u8],
    anchor: &Path,
    local: &Path,
) -> Result<()> {
    let _guard = custody::lock(&local.with_extension("preparation.lock"))?;
    let before = Journal::decode(&custody::rpc(anchor, &[0])?)?;
    before.reserve_batch(ids, g.clone(), Purpose::Triple)?;
    let mut req = vec![2];
    req.extend(crate::codec::batch_request(ids, g, Purpose::Triple));
    let confirmed = Journal::decode(&custody::rpc(anchor, &req)?)?;
    let indexed = confirmed
        .allocations
        .iter()
        .map(|a| (&a.id, a))
        .collect::<std::collections::BTreeMap<_, _>>();
    if !confirmed.extends(&before)
        || !confirmed.preserves_allocations(&before)
        || ids.iter().any(|id| {
            indexed
                .get(id)
                .is_none_or(|a| a.generation != *g || a.purpose != Purpose::Triple || a.consumed)
        })
    {
        return Err(bad("preparation batch allocation binding/retention"));
    }
    // Persist exact original manifest with the whole completed reservation.
    let mut receipt = b"DREGG.PREPARATION.BURN.V1".to_vec();
    bytes(binding, &mut receipt);
    g.put(&mut receipt);
    bytes(&confirmed.encode(), &mut receipt);
    custody::snapshot(local, &receipt)?;
    if std::fs::read(local)? != receipt {
        return Err(bad("preparation burn readback"));
    }
    let latest = Journal::decode(&custody::rpc(anchor, &[0])?)?;
    if !latest.extends(&confirmed) || !latest.preserves_allocations(&confirmed) {
        return Err(bad("preparation anchor regression"));
    }
    Ok(())
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Body {
    InitialPoint(Vec<Field>),
    InitialResult(PhaseMessage),
    MaskedPoint(Vec<Field>),
    MaskedResult(PhaseMessage),
    ChallengePoint(Field),
    ChallengeResult(PhaseMessage),
    ChallengeAgreement(PhaseMessage),
    CheckPoint(Vec<Field>),
    CheckResult(PhaseMessage),
    CheckAgreement(PhaseMessage),
    FaultPoint(Vec<Field>),
    FaultSh2t {
        dealer: u16,
        message: sh2t_id::Message,
    },
    FaultResult(PhaseMessage),
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
pub struct CheckedTriples {
    generation: Generation,
    n: usize,
    f: usize,
    count: usize,
    context: [u8; 32],
    basis_bytes: Vec<u8>,
    preparation_rows: Vec<Correlation>,
    holder: u16,
    triples: Vec<(Field, Field, Field)>,
}
impl CheckedTriples {
    pub fn generation(&self) -> &Generation {
        &self.generation
    }
    pub fn roster(&self) -> (usize, usize) {
        (self.n, self.f)
    }
    pub fn count(&self) -> usize {
        self.count
    }
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn basis_bytes(&self) -> &[u8] {
        &self.basis_bytes
    }
    /// Public identities burned before the King seed getters. Relabeling a
    /// consumer generation does not make these original seeds independent.
    pub fn preparation_rows(&self) -> &[Correlation] {
        &self.preparation_rows
    }
    pub fn holder(&self) -> u16 {
        self.holder
    }
    pub fn triples(&self) -> &[(Field, Field, Field)] {
        &self.triples
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CheckFailure {
    ChallengeInInterpolationSet,
    PolynomialIdentityFailed,
}
#[derive(Clone)]
pub enum LocalizationDecision {
    /// An authenticated king's reliably broadcast pair: at least one member is
    /// faulty under the protocol proof, never a certificate both are corrupt.
    Dispute { party: u16, king: u16 },
    /// Actual Sh2t opening verified locally before accepting this decision.
    Accusation { dealer: u16, holder: u16 },
}
#[derive(Clone)]
pub struct VerifiedLocalization {
    context: [u8; 32],
    decision: LocalizationDecision,
    accusation: Option<sh2t_id::Accusation>,
}
impl VerifiedLocalization {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn decision(&self) -> &LocalizationDecision {
        &self.decision
    }
    /// Dealer/Accuser guilt comes from the actual verified Sh2t opening, never
    /// from the king's accusation-label alone.
    pub fn verified_accusation(&self) -> Option<&sh2t_id::Accusation> {
        self.accusation.as_ref()
    }
}
#[derive(Clone)]
pub struct TripleKing {
    pub context: [u8; 32],
    basis: PreparedBasis,
    started: bool,
    initial: Bracha,
    masked: Bracha,
    challenge: Bracha,
    check: Bracha,
    challenge_ra: Bracha,
    check_ra: Bracha,
    initial_points: BTreeMap<u16, Vec<Field>>,
    masked_points: BTreeMap<u16, Vec<Field>>,
    challenge_points: BTreeMap<u16, Vec<Field>>,
    check_points: BTreeMap<u16, Vec<Field>>,
    initial_published: bool,
    masked_published: bool,
    challenge_published: bool,
    check_published: bool,
    masked_sent: bool,
    challenge_sent: bool,
    check_sent: bool,
    local_c: Option<Vec<Field>>,
    fg: Option<(Vec<Field>, Vec<Field>)>,
    h: Option<Vec<Field>>,
    output: Option<CheckedTriples>,
    failure: Option<CheckFailure>,
    fault_started: bool,
    fault_points: BTreeMap<u16, Vec<Field>>,
    fault_result: Bracha,
    fault_published: bool,
    localization: Option<VerifiedLocalization>,
    fault_open_requested: std::collections::BTreeSet<(u16, u16)>,
}
impl TripleKing {
    pub fn new(g: &Generation, basis: PreparedBasis) -> Result<Self> {
        if *g != basis.consumer_generation {
            return Err(bad("burned basis consumer generation"));
        }
        let mut b = b"DREGG.TRIPLE.KING.DN.V1".to_vec();
        g.put(&mut b);
        b.extend(basis.bytes());
        let context = hash(&b);
        let n = basis.n;
        let f = basis.f;
        let king = basis.king;
        Ok(Self {
            context,
            basis,
            started: false,
            initial: Bracha::new(n, f, Some(king)),
            masked: Bracha::new(n, f, Some(king)),
            challenge: Bracha::new(n, f, Some(king)),
            check: Bracha::new(n, f, Some(king)),
            challenge_ra: Bracha::new(n, f, None),
            check_ra: Bracha::new(n, f, None),
            initial_points: BTreeMap::new(),
            masked_points: BTreeMap::new(),
            challenge_points: BTreeMap::new(),
            check_points: BTreeMap::new(),
            initial_published: false,
            masked_published: false,
            challenge_published: false,
            check_published: false,
            masked_sent: false,
            challenge_sent: false,
            check_sent: false,
            local_c: None,
            fg: None,
            h: None,
            output: None,
            failure: None,
            fault_started: false,
            fault_points: BTreeMap::new(),
            fault_result: Bracha::new(n, f, Some(king)),
            fault_published: false,
            localization: None,
            fault_open_requested: std::collections::BTreeSet::new(),
        })
    }
    fn all(&self, body: Body) -> Vec<Send> {
        (0..self.basis.n)
            .map(|i| Send {
                to: i as u16,
                message: Message {
                    context: self.context,
                    body: body.clone(),
                },
            })
            .collect()
    }
    fn to_king(&self, body: Body) -> Vec<Send> {
        vec![Send {
            to: self.basis.king,
            message: Message {
                context: self.context,
                body,
            },
        }]
    }
    /// Physical group identities were burned by reserve_new before extraction.
    /// Native funded source admission is still a separate required join.
    pub fn start(&mut self) -> Result<Vec<Send>> {
        if self.started {
            return Err(bad("triple group already started"));
        }
        self.started = true;
        let s = &self.basis.random;
        let z = (0..s.a.len())
            .map(|i| s.a[i].mul(s.b[i]).add(s.r[i]).add(s.o[i]))
            .collect();
        let mut out = self.to_king(Body::InitialPoint(z));
        out.extend(self.progress()?);
        Ok(out)
    }
    pub fn receive(&mut self, sender: u16, m: Message) -> Result<Vec<Send>> {
        if sender as usize >= self.basis.n || m.context != self.context {
            return Err(bad("foreign triple sender/context"));
        }
        let me = self.basis.me;
        let count = self.basis.count;
        let f = self.basis.f;
        let mut out = vec![];
        match m.body {
            Body::InitialPoint(v) => {
                if me != self.basis.king || v.len() != 2 * count + 1 {
                    return Err(bad("initial private point"));
                }
                self.initial_points.entry(sender).or_insert(v);
            }
            Body::MaskedPoint(v) => {
                if me != self.basis.king || v.len() != 2 * count {
                    return Err(bad("masked private point"));
                }
                self.masked_points.entry(sender).or_insert(v);
            }
            Body::ChallengePoint(v) => {
                if me != self.basis.king {
                    return Err(bad("challenge private point"));
                }
                self.challenge_points.entry(sender).or_insert(vec![v]);
            }
            Body::CheckPoint(v) => {
                if me != self.basis.king || v.len() != 3 {
                    return Err(bad("check private point"));
                }
                self.check_points.entry(sender).or_insert(v);
            }
            Body::InitialResult(p) => {
                shape(&p, (2 * count + 1) * 16)?;
                for p in self.initial.receive(sender, p) {
                    out.extend(self.all(Body::InitialResult(p)));
                }
            }
            Body::MaskedResult(p) => {
                shape(&p, 2 * count * 16)?;
                for p in self.masked.receive(sender, p) {
                    out.extend(self.all(Body::MaskedResult(p)));
                }
            }
            Body::ChallengeResult(p) => {
                shape(&p, (f + 1) * 16)?;
                for p in self.challenge.receive(sender, p) {
                    out.extend(self.all(Body::ChallengeResult(p)));
                }
            }
            Body::CheckResult(p) => {
                shape(&p, 3 * (f + 1) * 16)?;
                for p in self.check.receive(sender, p) {
                    out.extend(self.all(Body::CheckResult(p)));
                }
            }
            Body::ChallengeAgreement(p) => {
                one(&p)?;
                for p in self.challenge_ra.receive(sender, p) {
                    out.extend(self.all(Body::ChallengeAgreement(p)));
                }
            }
            Body::CheckAgreement(p) => {
                one(&p)?;
                for p in self.check_ra.receive(sender, p) {
                    out.extend(self.all(Body::CheckAgreement(p)));
                }
            }
            Body::FaultPoint(v) => {
                if me != self.basis.king || v.len() != 3 * (2 * count + 1) {
                    return Err(bad("fault private point"));
                }
                self.fault_points.entry(sender).or_insert(v);
            }
            Body::FaultSh2t { dealer, message } => {
                let index = self
                    .basis
                    .sources
                    .iter()
                    .position(|v| v.acss.dealer == dealer)
                    .ok_or_else(|| bad("fault source dealer outside basis"))?;
                let child = self.basis.sources[index].sh2t.receive(sender, message)?;
                out.extend(self.sh2t_out(dealer, child));
            }
            Body::FaultResult(p) => {
                shape(&p, 5)?;
                parse_localization(phase_value(&p), self.basis.n, self.basis.king)?;
                for q in self.fault_result.receive(sender, p) {
                    out.extend(self.all(Body::FaultResult(q)));
                }
            }
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    fn progress(&mut self) -> Result<Vec<Send>> {
        let mut out = vec![];
        let b = &self.basis;
        let n = b.n;
        let f = b.f;
        let count = b.count;
        let me = b.me;
        let king = b.king;
        if me == king && !self.initial_published && self.initial_points.len() >= 2 * f + 1 {
            // This optimistic first2f+1 reconstruction is NOT accepted as a coin
            // or qualified value; malformed sender/king is checked below.
            let points = self
                .initial_points
                .iter()
                .take(2 * f + 1)
                .map(|(h, v)| (*h, v.clone()))
                .collect::<Vec<_>>();
            let polys = acss_id::polynomial(&points, 2 * count + 1)?;
            let values = polys.iter().map(|p| p[0]).collect::<Vec<_>>();
            if !self.initial_published {
                self.initial_published = true;
                out.extend(self.all(Body::InitialResult(PhaseMessage::Init(fields(&values)))));
            }
        }
        if self.local_c.is_none() {
            if let Some(bytes) = &self.initial.output {
                let z = parse_fields(bytes);
                let c = z
                    .iter()
                    .zip(&self.basis.random.r)
                    .map(|(z, r)| z.add(*r))
                    .collect::<Vec<_>>();
                let points = (0..=count)
                    .map(|i| {
                        (
                            i as u16,
                            vec![self.basis.random.a[i], self.basis.random.b[i]],
                        )
                    })
                    .collect::<Vec<_>>();
                let polys = acss_id::polynomial(&points, 2)?;
                let mut masked = vec![];
                for i in count + 1..=2 * count {
                    let at = Field(i as u128 + 1);
                    masked.push(eval(&polys[0], at).add(self.basis.random.a[i]));
                    masked.push(eval(&polys[1], at).add(self.basis.random.b[i]));
                }
                self.local_c = Some(c);
                self.fg = Some((polys[0].clone(), polys[1].clone()));
                out.extend(self.to_king(Body::MaskedPoint(masked)));
            }
        }
        if me == king && !self.masked_published {
            if let Some((polys, _)) =
                acss_id::correct_polynomials(&self.masked_points, f, n - f, 2 * count)?
            {
                if !self.masked_published {
                    self.masked_published = true;
                    out.extend(self.all(Body::MaskedResult(PhaseMessage::Init(fields(
                        &polys.iter().map(|p| p[0]).collect::<Vec<_>>(),
                    )))));
                }
            }
        }
        if self.h.is_none() {
            if let (Some(bytes), Some(c)) = (&self.masked.output, &self.local_c) {
                let xy = parse_fields(bytes);
                let mut points = vec![];
                for i in 0..=count {
                    points.push((i as u16, vec![c[i]]));
                }
                for i in count + 1..=2 * count {
                    let x = xy[2 * (i - count - 1)];
                    let y = xy[2 * (i - count - 1) + 1];
                    let value = x
                        .mul(y)
                        .add(x.mul(self.basis.random.b[i]))
                        .add(y.mul(self.basis.random.a[i]))
                        .add(c[i]);
                    points.push((i as u16, vec![value]));
                }
                self.h = Some(acss_id::polynomial(&points, 1)?[0].clone());
                self.masked_sent = true;
                out.extend(self.to_king(Body::ChallengePoint(self.basis.random.check_r)));
            }
        }
        if me == king && !self.challenge_published {
            if let Some((polys, _)) =
                acss_id::correct_polynomials(&self.challenge_points, f, n - f, 1)?
            {
                if !self.challenge_published {
                    self.challenge_published = true;
                    out.extend(
                        self.all(Body::ChallengeResult(PhaseMessage::Init(fields(&polys[0])))),
                    );
                }
            }
        }
        if let Some(bytes) = &self.challenge.output {
            let polynomial = parse_fields(bytes);
            if eval(&polynomial, Field(me as u128 + 1)) == self.basis.random.check_r {
                for p in self.challenge_ra.input_ra(vec![1]) {
                    out.extend(self.all(Body::ChallengeAgreement(p)));
                }
            }
        }
        if self.challenge_ra.output == Some(vec![1])
            && !self.challenge_sent
            && self.h.is_some()
            && self.challenge.output.is_some()
        {
            let r = parse_fields(
                self.challenge
                    .output
                    .as_ref()
                    .ok_or_else(|| bad("challenge RA before local RBC"))?,
            )[0];
            self.challenge_sent = true;
            if (1..=2 * count + 1).any(|i| r == Field(i as u128)) {
                self.failure = Some(CheckFailure::ChallengeInInterpolationSet);
            } else {
                let (ff, gg) = self.fg.as_ref().unwrap();
                let h = self.h.as_ref().unwrap();
                out.extend(self.to_king(Body::CheckPoint(vec![
                    eval(ff, r),
                    eval(gg, r),
                    eval(h, r),
                ])));
            }
        }
        if me == king && !self.check_published {
            if let Some((polys, _)) = acss_id::correct_polynomials(&self.check_points, f, n - f, 3)?
            {
                if !self.check_published {
                    self.check_published = true;
                    out.extend(self.all(Body::CheckResult(PhaseMessage::Init(fields(
                        &polys.into_iter().flatten().collect::<Vec<_>>(),
                    )))));
                }
            }
        }
        if let (Some(bytes), Some(h), Some((ff, gg)), Some(r_bytes)) = (
            &self.check.output,
            &self.h,
            &self.fg,
            &self.challenge.output,
        ) {
            let polys = parse_fields(bytes)
                .chunks_exact(f + 1)
                .map(|p| p.to_vec())
                .collect::<Vec<_>>();
            let r = parse_fields(r_bytes)[0];
            let expected = [eval(ff, r), eval(gg, r), eval(h, r)];
            if (0..3).all(|i| eval(&polys[i], Field(me as u128 + 1)) == expected[i]) {
                for p in self.check_ra.input_ra(vec![1]) {
                    out.extend(self.all(Body::CheckAgreement(p)));
                }
            }
        }
        if self.check_ra.output == Some(vec![1]) && !self.check_sent && self.check.output.is_some()
        {
            self.check_sent = true;
            let bytes = parse_fields(self.check.output.as_ref().unwrap());
            if bytes[2 * (f + 1)] == bytes[0].mul(bytes[f + 1]) {
                let c = self
                    .local_c
                    .as_ref()
                    .ok_or_else(|| bad("check before local triples"))?;
                let triples = (1..=count)
                    .map(|i| (self.basis.random.a[i], self.basis.random.b[i], c[i]))
                    .collect();
                self.output = Some(CheckedTriples {
                    generation: self.basis.consumer_generation.clone(),
                    n: self.basis.n,
                    f: self.basis.f,
                    count: self.basis.count,
                    context: self.context,
                    basis_bytes: self.basis.bytes.clone(),
                    preparation_rows: self.basis.preparation_rows.clone(),
                    holder: me,
                    triples,
                });
            } else {
                self.failure = Some(CheckFailure::PolynomialIdentityFailed);
            }
        }
        out.extend(self.progress_fault()?);
        Ok(out)
    }
    fn sh2t_out(&self, dealer: u16, ps: Vec<sh2t_id::Send>) -> Vec<Send> {
        ps.into_iter()
            .map(|p| Send {
                to: p.to,
                message: Message {
                    context: self.context,
                    body: Body::FaultSh2t {
                        dealer,
                        message: p.message,
                    },
                },
            })
            .collect()
    }
    /// Protocol environment must admit/fund this fixed public fault phase.
    /// This method is not itself source authority to open arbitrary material.
    pub fn begin_fault_localization(&mut self) -> Result<Vec<Send>> {
        if self.failure != Some(CheckFailure::PolynomialIdentityFailed) {
            return Err(Error::new(
                ErrorKind::WouldBlock,
                "no agreed failed polynomial check",
            ));
        }
        if self.fault_started {
            return Err(bad("fault phase already started"));
        }
        self.fault_started = true;
        let mut v = vec![];
        v.extend(&self.basis.random.a);
        v.extend(&self.basis.random.b);
        v.extend(&self.basis.random.r);
        let mut out = self.to_king(Body::FaultPoint(v));
        for i in 0..self.basis.sources.len() {
            let dealer = self.basis.sources[i].acss.dealer;
            let ps = self.basis.sources[i]
                .sh2t
                .request_private_reconstruction(self.basis.group, self.basis.king)?;
            out.extend(self.sh2t_out(dealer, ps));
        }
        out.extend(self.progress_fault()?);
        Ok(out)
    }
    fn publish_fault(&mut self, decision: LocalizationDecision) -> Vec<Send> {
        if self.fault_published {
            return vec![];
        }
        self.fault_published = true;
        let mut b = vec![];
        match decision {
            LocalizationDecision::Dispute { party, king } => {
                b.push(0);
                b.extend(party.to_le_bytes());
                b.extend(king.to_le_bytes());
            }
            LocalizationDecision::Accusation { dealer, holder } => {
                b.push(1);
                b.extend(dealer.to_le_bytes());
                b.extend(holder.to_le_bytes());
            }
        }
        self.all(Body::FaultResult(PhaseMessage::Init(b)))
    }
    fn progress_fault(&mut self) -> Result<Vec<Send>> {
        let mut out = vec![];
        if !self.fault_started {
            return Ok(out);
        }
        let king = self.basis.king;
        let n = self.basis.n;
        let f = self.basis.f;
        let m = 2 * self.basis.count + 1;
        if self.basis.me == king && !self.fault_published {
            let mut verified = vec![];
            for source in &self.basis.sources {
                match source.sh2t.private_reconstruction(self.basis.group) {
                    Some(sh2t_id::Reconstruction::Verified(v)) => {
                        if v.receiver() != king
                            || v.group() != self.basis.group
                            || v.context() != source.sh2t.context
                        {
                            return Err(bad("fault exact private reconstruction binding"));
                        }
                        if v.polynomials().iter().any(|p| p[0] != Field(0)) {
                            let d = source.acss.dealer;
                            out.extend(
                                self.publish_fault(LocalizationDecision::Dispute {
                                    party: d,
                                    king,
                                }),
                            );
                            return Ok(out);
                        }
                        verified.push(v.polynomials().to_vec());
                    }
                    Some(sh2t_id::Reconstruction::Invalid(_)) => {
                        let d = source.acss.dealer;
                        out.extend(
                            self.publish_fault(LocalizationDecision::Dispute { party: d, king }),
                        );
                        return Ok(out);
                    }
                    Some(sh2t_id::Reconstruction::AgreedAccusation(v)) => {
                        let decision = LocalizationDecision::Accusation {
                            dealer: v.dealer(),
                            holder: v.holder(),
                        };
                        out.extend(self.publish_fault(decision));
                        return Ok(out);
                    }
                    None => return Ok(out),
                }
            }
            if let Some((polys, _)) =
                acss_id::correct_polynomials(&self.fault_points, f, n - f, 3 * m)?
            {
                let batch = per_group(self.basis.count, f)?;
                let mut zeros = vec![];
                for index in 0..batch {
                    for row in 0..=f {
                        let mut p = vec![Field(0); 2 * f + 1];
                        for (col, v) in verified.iter().enumerate() {
                            let coefficient = power(Field(col as u128 + 1), row);
                            for degree in 0..=2 * f {
                                p[degree] = p[degree].add(coefficient.mul(v[index][degree]));
                            }
                        }
                        zeros.push(p);
                    }
                }
                zeros.truncate(m);
                for (party, z) in &self.initial_points {
                    let at = Field(*party as u128 + 1);
                    if (0..m).any(|i| {
                        z[i] != eval(&polys[i], at)
                            .mul(eval(&polys[m + i], at))
                            .add(eval(&polys[2 * m + i], at))
                            .add(eval(&zeros[i], at))
                    }) {
                        let decision = LocalizationDecision::Dispute {
                            party: *party,
                            king,
                        };
                        out.extend(self.publish_fault(decision));
                        break;
                    }
                }
            }
        }
        if let Some(bytes) = &self.fault_result.output {
            let decision = parse_localization(bytes, n, king)?;
            match &decision {
                LocalizationDecision::Dispute { .. } => {
                    self.localization = Some(VerifiedLocalization {
                        context: self.context,
                        decision,
                        accusation: None,
                    });
                }
                LocalizationDecision::Accusation { dealer, holder } => {
                    let index = self
                        .basis
                        .sources
                        .iter()
                        .position(|s| s.acss.dealer == *dealer)
                        .ok_or_else(|| bad("fault accusation outside prepared basis"))?;
                    if self.basis.sources[index].sh2t.accusation(*holder).is_some() {
                        let accusation =
                            self.basis.sources[index].sh2t.accusation(*holder).cloned();
                        self.localization = Some(VerifiedLocalization {
                            context: self.context,
                            decision,
                            accusation,
                        });
                    } else if !self.fault_open_requested.contains(&(*dealer, *holder)) {
                        match self.basis.sources[index].sh2t.request_open(*holder) {
                            Ok(ps) => {
                                self.fault_open_requested.insert((*dealer, *holder));
                                out.extend(self.sh2t_out(*dealer, ps));
                            }
                            Err(e) if e.kind() == ErrorKind::WouldBlock => {}
                            Err(e) => return Err(e),
                        }
                    }
                }
            }
        }
        Ok(out)
    }
    pub fn localization(&self) -> Option<&VerifiedLocalization> {
        self.localization.as_ref()
    }
    pub fn checked_triples(&self) -> Option<&CheckedTriples> {
        self.output.as_ref()
    }
    /// A check failure retains every basis/input/RBC/point record. It is NOT a
    /// terminal source refusal or permission to reuse any consumed preparation.
    pub fn failure(&self) -> Option<&CheckFailure> {
        self.failure.as_ref()
    }
    pub fn retained_basis(&self) -> &PreparedBasis {
        &self.basis
    }
}
fn phase_value(p: &PhaseMessage) -> &[u8] {
    match p {
        PhaseMessage::Init(b) | PhaseMessage::Echo(b) | PhaseMessage::Ready(b) => b,
    }
}
fn parse_localization(b: &[u8], n: usize, king: u16) -> Result<LocalizationDecision> {
    if b.len() != 5 {
        return Err(bad("localization byte shape"));
    }
    let a = u16::from_le_bytes(b[1..3].try_into().unwrap());
    let c = u16::from_le_bytes(b[3..5].try_into().unwrap());
    if a as usize >= n || c as usize >= n {
        return Err(bad("localization roster"));
    }
    match b[0] {
        0 if c == king && a != king => Ok(LocalizationDecision::Dispute { party: a, king: c }),
        1 => Ok(LocalizationDecision::Accusation {
            dealer: a,
            holder: c,
        }),
        _ => Err(bad("localization tag or king")),
    }
}
fn fields(v: &[Field]) -> Vec<u8> {
    v.iter().flat_map(|x| x.0.to_le_bytes()).collect()
}
fn parse_fields(b: &[u8]) -> Vec<Field> {
    b.chunks_exact(16)
        .map(|b| Field(u128::from_le_bytes(b.try_into().unwrap())))
        .collect()
}
fn shape(p: &PhaseMessage, len: usize) -> Result<()> {
    let b = match p {
        PhaseMessage::Init(b) | PhaseMessage::Echo(b) | PhaseMessage::Ready(b) => b,
    };
    if b.len() != len {
        return Err(bad("triple RBC shape"));
    }
    Ok(())
}
fn one(p: &PhaseMessage) -> Result<()> {
    match p {
        PhaseMessage::Echo(b) | PhaseMessage::Ready(b) if b == &[1] => Ok(()),
        _ => Err(bad("triple reliableagreement value")),
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use std::{
        collections::VecDeque,
        fs,
        os::unix::net::UnixListener,
        sync::{
            atomic::{AtomicBool, Ordering},
            Arc,
        },
        thread,
        time::{Duration, SystemTime, UNIX_EPOCH},
    };
    fn generation(tag: u64) -> Generation {
        Generation {
            invocation: Nat::new(tag),
            command: vec![4],
            attempt: Nat::new(0),
            generation: Nat::new(1),
            configuration: Nat::new(9),
        }
    }
    fn root(label: &str) -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!(
            "mini-king-{label}-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&p).unwrap();
        p
    }
    pub(crate) struct AnchorFixture {
        sock: std::path::PathBuf,
        stop: Arc<AtomicBool>,
        task: Option<thread::JoinHandle<Journal>>,
    }
    impl AnchorFixture {
        fn new(root: &Path) -> Self {
            let sock = root.join("anchor.sock");
            let listener = UnixListener::bind(&sock).unwrap();
            listener.set_nonblocking(true).unwrap();
            let stop = Arc::new(AtomicBool::new(false));
            let halt = stop.clone();
            let authority = root.join("authority");
            let task = thread::spawn(move || {
                let mut a = custody::Anchor::open(&authority).unwrap();
                while !halt.load(Ordering::SeqCst) {
                    match listener.accept() {
                        Ok((mut s, _)) => {
                            let b = custody::read_packet(&mut s).unwrap();
                            let out = a.handle(&b);
                            let mut reply = vec![];
                            match out {
                                Ok(b) => {
                                    reply.push(0);
                                    reply.extend(b)
                                }
                                Err(e) => {
                                    reply.push(1);
                                    reply.extend(e.to_string().as_bytes())
                                }
                            }
                            custody::write_packet(&mut s, &reply).unwrap();
                        }
                        Err(e) if e.kind() == ErrorKind::WouldBlock => {
                            thread::sleep(Duration::from_millis(1))
                        }
                        Err(e) => panic!("{e}"),
                    }
                }
                a.journal
            });
            Self {
                sock,
                stop,
                task: Some(task),
            }
        }
    }
    impl AnchorFixture {
        pub(crate) fn socket(&self) -> &Path {
            &self.sock
        }
    }
    impl Drop for AnchorFixture {
        fn drop(&mut self) {
            self.stop.store(true, Ordering::SeqCst);
            self.task.take().unwrap().join().unwrap();
        }
    }
    fn prepared() -> Vec<Vec<PreparedSource>> {
        prepared_with_zero_fault(None)
    }
    fn prepared_with_zero_fault(fault: Option<u16>) -> Vec<Vec<PreparedSource>> {
        prepared_count(1, fault)
    }
    fn prepared_count(count: usize, fault: Option<u16>) -> Vec<Vec<PreparedSource>> {
        prepared_count_instance(count, fault, 0)
    }
    fn prepared_count_instance(
        count: usize,
        fault: Option<u16>,
        instance: u64,
    ) -> Vec<Vec<PreparedSource>> {
        let mut holders = vec![vec![]; 4];
        for dealer in 0..3u16 {
            let ag = generation(100 + dealer as u64 + 1000 * instance);
            let og = generation(200 + dealer as u64 + 1000 * instance);
            let mut aa = (0..4)
                .map(|i| {
                    AcssId::new(i, dealer, 4, 1, &ag, acss_seed_count(count, 1).unwrap()).unwrap()
                })
                .collect::<Vec<_>>();
            let polys = (0..acss_seed_count(count, 1).unwrap())
                .map(|i| {
                    vec![
                        Field(
                            0x10000
                                + dealer as u128 * 157
                                + i as u128 * 31
                                + instance as u128 * 419,
                        ),
                        Field(i as u128 + 17),
                    ]
                })
                .collect::<Vec<_>>();
            let mut q = aa[dealer as usize]
                .dealer(&polys, [dealer as u8 + 1; 32])
                .unwrap()
                .into_iter()
                .map(|p| (dealer, p))
                .collect::<VecDeque<_>>();
            let mut steps = 0;
            while let Some((from, p)) = q.pop_front() {
                steps += 1;
                assert!(steps < 500000);
                let to = p.to;
                q.extend(
                    aa[to as usize]
                        .receive(from, p.message)
                        .unwrap()
                        .into_iter()
                        .map(|p| (to, p)),
                );
            }
            let mut oo = (0..4)
                .map(|i| Sh2tId::new(i, dealer, 4, 1, &og, per_group(count, 1).unwrap()).unwrap())
                .collect::<Vec<_>>();
            let zeros = (0..16 * per_group(count, 1).unwrap())
                .map(|i| {
                    vec![
                        Field(if fault == Some(dealer) { 9 } else { 0 }),
                        Field(i as u128 + 13),
                        Field(i as u128 + 71),
                    ]
                })
                .collect::<Vec<_>>();
            let mut q = oo[dealer as usize]
                .dealer(&zeros, [dealer as u8 + 7; 32])
                .unwrap()
                .into_iter()
                .map(|p| (dealer, p))
                .collect::<VecDeque<_>>();
            let mut steps = 0;
            while let Some((from, p)) = q.pop_front() {
                steps += 1;
                assert!(steps < 500000);
                let to = p.to;
                q.extend(
                    oo[to as usize]
                        .receive(from, p.message)
                        .unwrap()
                        .into_iter()
                        .map(|p| (to, p)),
                );
            }
            for i in 0..4 {
                assert!(matches!(
                    aa[i].local_sharing(),
                    Some(acss_id::LocalSharing::Accepted(_))
                ));
                assert!(matches!(
                    oo[i].local_sharing(),
                    Some(sh2t_id::LocalSharing::Accepted(_))
                ));
                holders[i].push(
                    PreparedSource::new(aa[i].clone(), oo[i].clone(), ag.clone(), og.clone())
                        .unwrap(),
                );
            }
        }
        holders
    }
    fn kings() -> (
        Vec<TripleKing>,
        Vec<AnchorFixture>,
        Vec<Vec<PreparedSource>>,
    ) {
        let material = prepared();
        let mut anchors = vec![];
        let mut nodes = vec![];
        for (i, sources) in material.iter().enumerate() {
            let r = root(&i.to_string());
            let a = AnchorFixture::new(&r);
            let basis = PreparedBasis::reserve_new(
                &generation(300),
                0,
                1,
                0,
                sources.clone(),
                &a.sock,
                &r.join("burn"),
            )
            .unwrap();
            nodes.push(TripleKing::new(&generation(300), basis).unwrap());
            anchors.push(a);
        }
        (nodes, anchors, material)
    }
    fn drive(
        nodes: &mut [TripleKing],
        q: &mut VecDeque<(u16, Send)>,
        hold_to: Option<u16>,
    ) -> VecDeque<(u16, Send)> {
        let mut held = VecDeque::new();
        let mut steps = 0;
        while let Some((from, p)) = q.pop_front() {
            steps += 1;
            assert!(steps < 100000);
            if hold_to == Some(p.to) && matches!(&p.message.body, Body::ChallengeResult(_)) {
                held.push_back((from, p));
                continue;
            }
            let to = p.to;
            q.extend(
                nodes[to as usize]
                    .receive(from, p.message)
                    .unwrap()
                    .into_iter()
                    .map(|p| (to, p)),
            );
        }
        held
    }
    fn start(nodes: &mut [TripleKing]) -> VecDeque<(u16, Send)> {
        let mut q = VecDeque::new();
        for (i, n) in nodes.iter_mut().enumerate() {
            q.extend(n.start().unwrap().into_iter().map(|p| (i as u16, p)));
        }
        q
    }
    fn verify_exact_product(nodes: &[TripleKing]) {
        for n in nodes {
            assert!(n.failure().is_none());
            assert!(n.checked_triples().is_some());
        }
        let points = nodes
            .iter()
            .take(2)
            .map(|n| {
                let (a, b, c) = n.checked_triples().unwrap().triples()[0];
                (n.basis.me, vec![a, b, c])
            })
            .collect::<Vec<_>>();
        let polys = acss_id::polynomial(&points, 3).unwrap();
        assert_ne!(polys[0][0], Field(0));
        assert_ne!(polys[1][0], Field(0));
        assert_eq!(polys[0][0].mul(polys[1][0]), polys[2][0]);
        for n in nodes {
            let tuple = n.checked_triples().unwrap().triples()[0];
            for (i, v) in [tuple.0, tuple.1, tuple.2].iter().enumerate() {
                assert_eq!(*v, eval(&polys[i], Field(n.basis.me as u128 + 1)));
            }
        }
    }
    #[test]
    fn actual_acss_sh2t_basis_checked_product_and_consumer_reuse_refused() {
        let (mut nodes, anchors, material) = kings();
        let mut q = start(&mut nodes);
        drive(&mut nodes, &mut q, None);
        verify_exact_product(&nodes);
        let basis = nodes[0].basis.clone();
        assert!(TripleKing::new(&generation(301), basis).is_err());
        assert!(nodes[0].start().is_err());
        let p = root("retry");
        assert!(PreparedBasis::reserve_new(
            &generation(301),
            0,
            1,
            0,
            material[0].clone(),
            &anchors[0].sock,
            &p.join("burn")
        )
        .is_err());
        let j = Journal::decode(&custody::rpc(&anchors[0].sock, &[0]).unwrap()).unwrap();
        assert_eq!(j.spent.len(), 6);
    }
    #[test]
    fn early_challenge_agreement_retained_until_delayed_local_broadcast() {
        let (mut nodes, _anchors, _) = kings();
        let mut q = start(&mut nodes);
        let mut held = drive(&mut nodes, &mut q, Some(3));
        assert!(!held.is_empty());
        assert_eq!(nodes[3].challenge_ra.output, Some(vec![1]));
        assert!(nodes[3].challenge.output.is_none());
        assert!(!nodes[3].challenge_sent);
        drive(&mut nodes, &mut held, None);
        assert!(nodes[3].challenge_sent);
        verify_exact_product(&nodes);
    }
    #[test]
    fn malicious_king_changed_exported_triple_is_rejected_deterministically() {
        let (mut nodes, _anchors, _) = kings();
        let mut q = start(&mut nodes);
        let mut changed = 0;
        let mut steps = 0;
        while let Some((from, mut p)) = q.pop_front() {
            steps += 1;
            assert!(steps < 100000);
            if from == 0 {
                if let Body::InitialResult(PhaseMessage::Init(v)) = &mut p.message.body {
                    v[16] ^= 1;
                    changed += 1;
                }
            }
            let to = p.to;
            q.extend(
                nodes[to as usize]
                    .receive(from, p.message)
                    .unwrap()
                    .into_iter()
                    .map(|p| (to, p)),
            );
        }
        assert_eq!(changed, 4);
        for n in &nodes[1..] {
            assert_eq!(n.failure(), Some(&CheckFailure::PolynomialIdentityFailed));
            assert!(n.checked_triples().is_none());
            assert_eq!(n.retained_basis().sources().len(), 3);
            assert!(n.local_c.is_some() && n.h.is_some());
        }
    }
    #[test]
    fn bad_initial_point_localizes_via_real_sh2t_zero_reconstruction() {
        let (mut nodes, _anchors, _) = kings();
        let mut q = start(&mut nodes);
        let mut changed = 0;
        let mut steps = 0;
        while let Some((from, mut p)) = q.pop_front() {
            steps += 1;
            assert!(steps < 100000);
            if from == 1 && p.to == 0 {
                if let Body::InitialPoint(v) = &mut p.message.body {
                    v[1] = v[1].add(Field(1));
                    changed += 1;
                }
            }
            let to = p.to;
            q.extend(
                nodes[to as usize]
                    .receive(from, p.message)
                    .unwrap()
                    .into_iter()
                    .map(|p| (to, p)),
            );
        }
        assert_eq!(changed, 1);
        for n in &nodes {
            assert_eq!(n.failure(), Some(&CheckFailure::PolynomialIdentityFailed));
            assert!(n.checked_triples().is_none());
        }
        let mut q = VecDeque::new();
        for (i, n) in nodes.iter_mut().enumerate() {
            q.extend(
                n.begin_fault_localization()
                    .unwrap()
                    .into_iter()
                    .map(|p| (i as u16, p)),
            );
        }
        drive(&mut nodes, &mut q, None);
        for n in &nodes {
            assert!(matches!(
                n.localization().unwrap().decision(),
                LocalizationDecision::Dispute { party: 1, king: 0 }
            ));
            assert!(n.checked_triples().is_none());
            for source in &nodes[0].basis.sources {
                let Some(sh2t_id::Reconstruction::Verified(v)) =
                    source.sh2t.private_reconstruction(0)
                else {
                    panic!("actual zero proof not reconstructed")
                };
                assert!(v.polynomials().iter().all(|p| p[0] == Field(0)));
                assert!(v.accepted_holders().len() >= 3);
            }
        }
    }
    #[test]
    fn coherent_nonzero_sh2t_dealer_localized_by_honest_king() {
        let material = prepared_with_zero_fault(Some(0));
        let mut anchors = vec![];
        let mut nodes = vec![];
        for (i, sources) in material.iter().enumerate() {
            let r = root(&format!("nonzero-{i}"));
            let a = AnchorFixture::new(&r);
            let basis = PreparedBasis::reserve_new(
                &generation(500),
                3,
                1,
                12,
                sources.clone(),
                &a.sock,
                &r.join("burn"),
            )
            .unwrap();
            nodes.push(TripleKing::new(&generation(500), basis).unwrap());
            anchors.push(a);
        }
        let mut q = start(&mut nodes);
        drive(&mut nodes, &mut q, None);
        for n in &nodes {
            assert_eq!(n.failure(), Some(&CheckFailure::PolynomialIdentityFailed));
            assert!(n.checked_triples().is_none());
        }
        let mut q = VecDeque::new();
        for (i, n) in nodes.iter_mut().enumerate() {
            q.extend(
                n.begin_fault_localization()
                    .unwrap()
                    .into_iter()
                    .map(|p| (i as u16, p)),
            );
        }
        drive(&mut nodes, &mut q, None);
        for n in &nodes[1..] {
            assert!(matches!(
                n.localization().unwrap().decision(),
                LocalizationDecision::Dispute { party: 0, king: 3 }
            ));
            assert!(n.checked_triples().is_none());
        }
        let Some(sh2t_id::Reconstruction::Verified(v)) =
            nodes[3].basis.sources[0].sh2t.private_reconstruction(12)
        else {
            panic!("missing actual verification")
        };
        assert!(v.polynomials().iter().all(|p| p[0] == Field(9)));
        assert!(v.accepted_holders().len() >= 3);
    }
    #[test]
    fn incomplete_preparation_burns_fixed_manifest_before_first_share_read() {
        let ag = generation(401);
        let og = generation(402);
        let sources = (0..3)
            .map(|d| {
                PreparedSource::new(
                    AcssId::new(0, d, 4, 1, &ag, 8).unwrap(),
                    Sh2tId::new(0, d, 4, 1, &og, 2).unwrap(),
                    ag.clone(),
                    og.clone(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let r = root("incomplete");
        let a = AnchorFixture::new(&r);
        let e = PreparedBasis::reserve_new(
            &generation(403),
            0,
            1,
            0,
            sources.clone(),
            &a.sock,
            &r.join("burn"),
        )
        .err()
        .unwrap();
        assert_eq!(e.kind(), ErrorKind::WouldBlock);
        let j = Journal::decode(&custody::rpc(&a.sock, &[0]).unwrap()).unwrap();
        assert_eq!(j.spent.len(), 6);
        assert!(r.join("burn").exists());
        assert!(PreparedBasis::reserve_new(
            &generation(404),
            0,
            1,
            0,
            sources,
            &a.sock,
            &r.join("burn2")
        )
        .is_err());
    }
    pub(crate) fn checked_for_consumer(count: usize) -> Vec<CheckedTriples> {
        checked_inventory(count, 0)
    }
    pub(crate) fn checked_inventory(count: usize, instance: u64) -> Vec<CheckedTriples> {
        let material = prepared_count_instance(count, None, instance);
        let mut anchors = vec![];
        let mut nodes = vec![];
        for (i, sources) in material.iter().enumerate() {
            let r = root(&format!("consumer-{i}"));
            let a = AnchorFixture::new(&r);
            let basis = PreparedBasis::reserve_new(
                &generation(300 + 1000 * instance),
                0,
                count,
                0,
                sources.clone(),
                &a.sock,
                &r.join("burn"),
            )
            .unwrap();
            nodes.push(TripleKing::new(&generation(300 + 1000 * instance), basis).unwrap());
            anchors.push(a);
        }
        let mut q = start(&mut nodes);
        drive(&mut nodes, &mut q, None);
        nodes
            .into_iter()
            .map(|n| n.output.expect("actual checked King construction"))
            .collect()
    }

    pub(crate) fn evaluator_anchor(
        label: &str,
    ) -> (AnchorFixture, std::path::PathBuf, std::path::PathBuf) {
        let r = root(label);
        let a = AnchorFixture::new(&r);
        let sock = a.sock.clone();
        (a, sock, r)
    }
}
