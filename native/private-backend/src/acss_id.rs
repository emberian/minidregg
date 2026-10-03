//! Actual bivariate ACSS-Id consumer for Appendix B dZK + recipient PrivSend.
//! Static f<n/3, authenticated private reliable channels, classical ROM reference.
//! No source capability, complete simulator, native Qualified or GOD theorem.
//! Locally accepted row/proof is immutable before RA Echo. Reconstruction uses
//! reverified transferred dZK points and online n-f error correction, not raw shares.
use crate::{
    asks::{Bracha, PhaseMessage},
    codec::{bad, Generation, Nat},
    custody::hash,
    dzk::{self, Dzk, RejectedProof, Verification, VerifiedShares},
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
fn child(g: &Generation, context: [u8; 32], tag: u8, index: usize) -> Generation {
    let mut b = b"DREGG.ACSS.ID.CHILD.V1".to_vec();
    b.extend(context);
    b.push(tag);
    b.extend((index as u64).to_le_bytes());
    let mut h = g.clone();
    h.invocation = Nat::from_be(&hash(&b));
    h
}
fn random(seed: [u8; 32], context: [u8; 32], tag: u8, index: usize) -> [u8; 32] {
    let mut b = b"DREGG.ACSS.ID.RANDOM.V1".to_vec();
    b.extend(seed);
    b.extend(context);
    b.push(tag);
    b.extend((index as u64).to_le_bytes());
    hash(&b)
}
#[derive(Clone)]
pub struct AcceptedSharing {
    context: [u8; 32],
    holder: u16,
    shares: Vec<Field>,
    proofs: Vec<VerifiedShares>,
}
impl AcceptedSharing {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn holder(&self) -> u16 {
        self.holder
    }
    pub fn shares(&self) -> &[Field] {
        &self.shares
    }
    pub fn column_proofs(&self) -> &[VerifiedShares] {
        &self.proofs
    }
}
#[derive(Clone)]
pub struct RejectedSharing {
    context: [u8; 32],
    holder: u16,
    evidence: Vec<RejectedProof>,
}
impl RejectedSharing {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn holder(&self) -> u16 {
        self.holder
    }
    pub fn evidence(&self) -> &[RejectedProof] {
        &self.evidence
    }
}
#[derive(Clone)]
pub enum LocalSharing {
    Accepted(AcceptedSharing),
    Rejected(RejectedSharing),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Body {
    Row {
        holder: u16,
        message: private_send::Message,
    },
    Column {
        column: u16,
        message: dzk::Message,
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
    ReconstructionRequest {
        requester: u16,
        phase: PhaseMessage,
    },
    PublicColumn {
        column: u16,
        values: Vec<Field>,
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
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PublicReconstruction {
    context: [u8; 32],
    secrets: Vec<Field>,
    support: Vec<u16>,
}
impl PublicReconstruction {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn secrets(&self) -> &[Field] {
        &self.secrets
    }
    pub fn support(&self) -> &[u16] {
        &self.support
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FaultParty {
    Dealer(u16),
    Accuser(u16),
}
#[derive(Clone)]
pub struct Accusation {
    context: [u8; 32],
    holder: u16,
    fault: FaultParty,
    columns: Vec<dzk::OpenProof>,
}
impl Accusation {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn holder(&self) -> u16 {
        self.holder
    }
    pub fn fault(&self) -> FaultParty {
        self.fault
    }
    pub fn proofs(&self) -> &[dzk::OpenProof] {
        &self.columns
    }
}
#[derive(Clone)]
pub struct AcssId {
    pub me: u16,
    pub dealer: u16,
    pub n: usize,
    pub f: usize,
    pub count: usize,
    pub context: [u8; 32],
    groups: usize,
    rows: Vec<PrivateSend>,
    columns: Vec<Dzk>,
    ra: Bracha,
    complaints: Vec<Bracha>,
    open_requests: Vec<Vec<Bracha>>,
    reconstruction_requests: Vec<Bracha>,
    started: bool,
    verification_requested: bool,
    complaint_sent: bool,
    local: Option<LocalSharing>,
    accepted_row: Option<Vec<Vec<Field>>>,
    opening_requested: Vec<bool>,
    opening_started: Vec<bool>,
    accusations: BTreeMap<u16, Accusation>,
    recon_requested: bool,
    recon_started: bool,
    column_sent: bool,
    public_points: BTreeMap<u16, Vec<Field>>,
    reconstructed: Option<PublicReconstruction>,
}
impl AcssId {
    pub fn new(
        me: u16,
        dealer: u16,
        n: usize,
        f: usize,
        g: &Generation,
        count: usize,
    ) -> Result<Self> {
        if n != 3 * f + 1
            || !(4..=16).contains(&n)
            || me as usize >= n
            || dealer as usize >= n
            || count == 0
            || count % (f + 1) != 0
            || count / (f + 1) > 128
        {
            return Err(bad("ACSS-Id roster/count/degree"));
        }
        let groups = count / (f + 1);
        let mut b = b"DREGG.ACSS.ID.V1".to_vec();
        g.put(&mut b);
        b.extend(dealer.to_le_bytes());
        for v in [n, f, count] {
            b.extend((v as u64).to_le_bytes());
        }
        let context = hash(&b);
        let rows = (0..n)
            .map(|j| PrivateSend::new(me, dealer, n, f, &child(g, context, 0, j), count * 16))
            .collect::<Result<_>>()?;
        let columns = (0..n)
            .map(|j| Dzk::new(me, dealer, n, f, &child(g, context, 1, j), groups, f))
            .collect::<Result<_>>()?;
        Ok(Self {
            me,
            dealer,
            n,
            f,
            count,
            context,
            groups,
            rows,
            columns,
            ra: Bracha::new(n, f, None),
            complaints: (0..n).map(|j| Bracha::new(n, f, Some(j as u16))).collect(),
            open_requests: (0..n)
                .map(|_| (0..n).map(|j| Bracha::new(n, f, Some(j as u16))).collect())
                .collect(),
            reconstruction_requests: (0..n).map(|j| Bracha::new(n, f, Some(j as u16))).collect(),
            started: false,
            verification_requested: false,
            complaint_sent: false,
            local: None,
            accepted_row: None,
            opening_requested: vec![false; n],
            opening_started: vec![false; n],
            accusations: BTreeMap::new(),
            recon_requested: false,
            recon_started: false,
            column_sent: false,
            public_points: BTreeMap::new(),
            reconstructed: None,
        })
    }
    fn all(&self, body: Body) -> Vec<Send> {
        (0..self.n)
            .map(|j| Send {
                to: j as u16,
                message: Message {
                    context: self.context,
                    body: body.clone(),
                },
            })
            .collect()
    }
    fn row_out(&self, holder: u16, ps: Vec<private_send::Send>) -> Vec<Send> {
        ps.into_iter()
            .map(|p| Send {
                to: p.to,
                message: Message {
                    context: self.context,
                    body: Body::Row {
                        holder,
                        message: p.message,
                    },
                },
            })
            .collect()
    }
    fn column_out(&self, column: u16, ps: Vec<dzk::Send>) -> Vec<Send> {
        ps.into_iter()
            .map(|p| Send {
                to: p.to,
                message: Message {
                    context: self.context,
                    body: Body::Column {
                        column,
                        message: p.message,
                    },
                },
            })
            .collect()
    }
    /// Native external source input; seed/polys/outbox MUST commit before publication.
    /// Polynomials are group-major, ell-minor, exactly f+1 coefficients each.
    pub fn dealer(&mut self, polys: &[Vec<Field>], seed: [u8; 32]) -> Result<Vec<Send>> {
        if self.me != self.dealer
            || self.started
            || polys.len() != self.count
            || polys.iter().any(|p| p.len() != self.f + 1)
        {
            return Err(bad("ACSS-Id dealer/degree/retry"));
        }
        let mut out = vec![];
        for j in 0..self.n {
            let at = Field(j as u128 + 1);
            // Row g(alpha_j,Y) coefficient k is f^(k)_ell(alpha_j).
            let mut row = vec![];
            for ell in 0..self.groups {
                for k in 0..=self.f {
                    row.extend(eval(&polys[k * self.groups + ell], at).0.to_le_bytes());
                }
            }
            let coeff = (0..2)
                .map(|k| {
                    (0..=self.f)
                        .map(|i| {
                            Field(u128::from_le_bytes(
                                random(seed, self.context, 0, j * 32 + k * 16 + i)[..16]
                                    .try_into()
                                    .unwrap(),
                            ))
                        })
                        .collect()
                })
                .collect::<Vec<Vec<Field>>>();
            let ps = self.rows[j].dealer_with_coefficients(&row, &coeff)?;
            out.extend(self.row_out(j as u16, ps));
            // Column g(X,alpha_j), L' degree-f polynomials.
            let col = (0..self.groups)
                .map(|ell| {
                    (0..=self.f)
                        .map(|degree| {
                            (0..=self.f).rev().fold(Field(0), |v, k| {
                                v.mul(at).add(polys[k * self.groups + ell][degree])
                            })
                        })
                        .collect()
                })
                .collect::<Vec<Vec<Field>>>();
            let ps = self.columns[j].dealer(&col, random(seed, self.context, 1, j))?;
            out.extend(self.column_out(j as u16, ps));
        }
        self.started = true;
        out.extend(self.progress()?);
        Ok(out)
    }
    pub fn receive(&mut self, sender: u16, m: Message) -> Result<Vec<Send>> {
        if sender as usize >= self.n || m.context != self.context {
            return Err(bad("ACSS-Id foreign sender/context"));
        }
        let mut out = vec![];
        match m.body {
            Body::Row { holder, message } => {
                if holder as usize >= self.n {
                    return Err(bad("ACSS row range"));
                }
                let ps = self.rows[holder as usize].receive(sender, message)?;
                out.extend(self.row_out(holder, ps));
            }
            Body::Column { column, message } => {
                if column as usize >= self.n {
                    return Err(bad("ACSS column range"));
                }
                let ps = self.columns[column as usize].receive(sender, message)?;
                out.extend(self.column_out(column, ps));
            }
            Body::Termination(phase) => {
                valid_one(&phase, false)?;
                for p in self.ra.receive(sender, phase) {
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
                    return Err(bad("open request range"));
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
            Body::ReconstructionRequest { requester, phase } => {
                if requester as usize >= self.n {
                    return Err(bad("reconstruction requester"));
                }
                valid_one(&phase, true)?;
                for p in self.reconstruction_requests[requester as usize].receive(sender, phase) {
                    out.extend(self.all(Body::ReconstructionRequest {
                        requester,
                        phase: p,
                    }));
                }
            }
            Body::PublicColumn { column, values } => {
                if column != sender || values.len() != self.groups {
                    return Err(bad("public column authenticated sender/shape"));
                }
                self.public_points.entry(column).or_insert(values);
            }
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    fn row_values(&self, holder: usize) -> Option<Vec<Vec<Field>>> {
        let b = self.rows[holder].delivered.as_ref()?;
        if b.len() != self.count * 16 {
            return None;
        }
        Some(
            b.chunks_exact((self.f + 1) * 16)
                .map(|row| {
                    row.chunks_exact(16)
                        .map(|b| Field(u128::from_le_bytes(b.try_into().unwrap())))
                        .collect()
                })
                .collect(),
        )
    }
    fn verification(&self, holder: u16, row: &[Vec<Field>]) -> Result<Vec<Verification>> {
        if row.len() != self.groups || row.iter().any(|p| p.len() != self.f + 1) {
            return Err(bad("row degree"));
        }
        self.columns
            .iter()
            .enumerate()
            .map(|(j, c)| {
                c.verify_private(
                    holder,
                    &row.iter()
                        .map(|p| eval(p, Field(j as u128 + 1)))
                        .collect::<Vec<_>>(),
                )
            })
            .collect()
    }
    fn progress(&mut self) -> Result<Vec<Send>> {
        let mut out = vec![];
        let dispersed = self.rows.iter().all(|r| r.dispersed)
            && self.columns.iter().all(|c| c.delivered().is_some());
        if dispersed && !self.verification_requested {
            self.verification_requested = true;
            // Every honest requester asks delivery of row_i to i and proof_i to i.
            for holder in 0..self.n {
                let ps = self.rows[holder].request_delivery(holder as u16)?;
                out.extend(self.row_out(holder as u16, ps));
                for j in 0..self.n {
                    let ps =
                        self.columns[j].authorize_verification(holder as u16, holder as u16)?;
                    out.extend(self.column_out(j as u16, ps));
                }
            }
        }
        if dispersed && self.local.is_none() {
            if let Some(row) = self.row_values(self.me as usize) {
                match self.verification(self.me, &row) {
                    Ok(proofs) => {
                        let mut accepted = vec![];
                        let mut rejected = vec![];
                        for p in proofs {
                            match p {
                                Verification::Accepted(p) => accepted.push(p),
                                Verification::Rejected(p) => rejected.push(p),
                            }
                        }
                        if rejected.is_empty() {
                            let mut shares = vec![];
                            for k in 0..=self.f {
                                for p in &row {
                                    shares.push(p[k]);
                                }
                            }
                            self.accepted_row = Some(row); // freeze BEFORE RA input
                            self.local = Some(LocalSharing::Accepted(AcceptedSharing {
                                context: self.context,
                                holder: self.me,
                                shares,
                                proofs: accepted,
                            }));
                            for p in self.ra.input_ra(vec![1]) {
                                out.extend(self.all(Body::Termination(p)));
                            }
                        } else {
                            self.local = Some(LocalSharing::Rejected(RejectedSharing {
                                context: self.context,
                                holder: self.me,
                                evidence: rejected,
                            }));
                            if !self.complaint_sent {
                                self.complaint_sent = true;
                                out.extend(self.all(Body::Complaint {
                                    holder: self.me,
                                    phase: PhaseMessage::Init(vec![1]),
                                }));
                            }
                        }
                    }
                    Err(e) if e.kind() == ErrorKind::WouldBlock => {}
                    Err(e) => return Err(e),
                }
            }
        }
        if self.sharing_complete() {
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
                        let ps = self.rows[holder].request_delivery(receiver as u16)?;
                        out.extend(self.row_out(holder as u16, ps));
                        for j in 0..self.n {
                            let ps = self.columns[j]
                                .authorize_verification(holder as u16, receiver as u16)?;
                            out.extend(self.column_out(j as u16, ps));
                        }
                    }
                }
                if self.opening_started[holder] && !self.accusations.contains_key(&(holder as u16))
                {
                    if let Some(row) = self.row_values(holder) {
                        let values = (0..self.n)
                            .map(|j| {
                                row.iter()
                                    .map(|p| eval(p, Field(j as u128 + 1)))
                                    .collect::<Vec<_>>()
                            })
                            .collect::<Vec<Vec<Field>>>();
                        let mut proofs = vec![];
                        let mut waiting = false;
                        for (j, column) in self.columns.iter().enumerate() {
                            match column.open_proof(holder as u16, &values[j]) {
                                Ok(p) => proofs.push(p),
                                Err(e) if e.kind() == ErrorKind::WouldBlock => {
                                    waiting = true;
                                    break;
                                }
                                Err(e) => return Err(e),
                            }
                        }
                        if !waiting {
                            let invalid = proofs
                                .iter()
                                .any(|p| matches!(p.verification(), Verification::Rejected(_)));
                            let fault = if invalid {
                                FaultParty::Dealer(self.dealer)
                            } else {
                                FaultParty::Accuser(holder as u16)
                            };
                            self.accusations.insert(
                                holder as u16,
                                Accusation {
                                    context: self.context,
                                    holder: holder as u16,
                                    fault,
                                    columns: proofs,
                                },
                            );
                        }
                    }
                }
            }
            let recon = self
                .reconstruction_requests
                .iter()
                .filter(|r| r.output == Some(vec![1]))
                .count()
                > self.f;
            if recon && !self.recon_started {
                self.recon_started = true;
                if let Some(row) = &self.accepted_row {
                    for j in 0..self.n {
                        let values = row
                            .iter()
                            .map(|p| eval(p, Field(j as u128 + 1)))
                            .collect::<Vec<_>>();
                        let (_, ps) = self.columns[j].transfer(j as u16, &values)?;
                        out.extend(self.column_out(j as u16, ps));
                    }
                }
            }
            if self.recon_started && !self.column_sent {
                let my_column = &self.columns[self.me as usize];
                let points = (0..self.n)
                    .filter_map(|h| {
                        my_column
                            .transferred(h as u16)
                            .map(|v| (h as u16, v.values().to_vec()))
                    })
                    .take(self.f + 1)
                    .collect::<Vec<_>>();
                if points.len() == self.f + 1 {
                    let at_zero = interpolate_at(&points, Field(0), self.groups)?;
                    self.column_sent = true;
                    out.extend(self.all(Body::PublicColumn {
                        column: self.me,
                        values: at_zero,
                    }));
                }
            }
            if self.recon_started
                && self.reconstructed.is_none()
                && self.public_points.len() >= self.n - self.f
            {
                if let Some((polys, support)) =
                    correct_polynomials(&self.public_points, self.f, self.n - self.f, self.groups)?
                {
                    let mut secrets = vec![];
                    for k in 0..=self.f {
                        for p in &polys {
                            secrets.push(p[k]);
                        }
                    }
                    self.reconstructed = Some(PublicReconstruction {
                        context: self.context,
                        secrets,
                        support,
                    });
                }
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
    /// Exact current-source environment request, not a peer body permission flag.
    /// An authenticated holder complaint must exist before honest view disclosure.
    pub fn request_open(&mut self, holder: u16) -> Result<Vec<Send>> {
        if holder as usize >= self.n {
            return Err(bad("open holder"));
        }
        if !self.sharing_complete() || self.complaints[holder as usize].output != Some(vec![1]) {
            return Err(Error::new(
                ErrorKind::WouldBlock,
                "sharing/holder complaint not delivered",
            ));
        }
        let mut out = vec![];
        if !self.opening_requested[holder as usize] {
            self.opening_requested[holder as usize] = true;
            out.extend(self.all(Body::OpenRequest {
                holder,
                requester: self.me,
                phase: PhaseMessage::Init(vec![1]),
            }));
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    pub fn accusation(&self, holder: u16) -> Option<&Accusation> {
        self.accusations.get(&holder)
    }
    pub fn request_public_reconstruction(&mut self) -> Result<Vec<Send>> {
        if !self.sharing_complete() {
            return Err(Error::new(ErrorKind::WouldBlock, "sharing incomplete"));
        }
        let mut out = vec![];
        if !self.recon_requested {
            self.recon_requested = true;
            out.extend(self.all(Body::ReconstructionRequest {
                requester: self.me,
                phase: PhaseMessage::Init(vec![1]),
            }));
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    pub fn public_reconstruction(&self) -> Option<&PublicReconstruction> {
        self.reconstructed.as_ref()
    }
}
fn valid_one(p: &PhaseMessage, init: bool) -> Result<()> {
    let b = match p {
        PhaseMessage::Init(b) if init => b,
        PhaseMessage::Echo(b) | PhaseMessage::Ready(b) => b,
        _ => return Err(bad("RA Init forbidden")),
    };
    if b != &[1] {
        return Err(bad("ACSS request/RA value"));
    }
    Ok(())
}
fn interpolate_at(points: &[(u16, Vec<Field>)], at: Field, count: usize) -> Result<Vec<Field>> {
    let mut out = vec![Field(0); count];
    for (i, (holder, values)) in points.iter().enumerate() {
        if values.len() != count {
            return Err(bad("point vector"));
        }
        let xi = Field(*holder as u128 + 1);
        let mut coefficient = Field(1);
        for (j, (other, _)) in points.iter().enumerate() {
            if i != j {
                let xj = Field(*other as u128 + 1);
                coefficient = coefficient.mul(at.add(xj)).mul(xi.add(xj).inv()?);
            }
        }
        for k in 0..count {
            out[k] = out[k].add(coefficient.mul(values[k]));
        }
    }
    Ok(out)
}
fn polynomial(points: &[(u16, Vec<Field>)], count: usize) -> Result<Vec<Vec<Field>>> {
    let mut out = vec![vec![Field(0); points.len()]; count];
    for (i, (holder, values)) in points.iter().enumerate() {
        if values.len() != count {
            return Err(bad("polynomial vector"));
        }
        let xi = Field(*holder as u128 + 1);
        let mut basis = vec![Field(1)];
        let mut denominator = Field(1);
        for (j, (other, _)) in points.iter().enumerate() {
            if i != j {
                let xj = Field(*other as u128 + 1);
                denominator = denominator.mul(xi.add(xj));
                let mut next = vec![Field(0); basis.len() + 1];
                for (k, c) in basis.iter().enumerate() {
                    next[k] = next[k].add(c.mul(xj));
                    next[k + 1] = next[k + 1].add(*c);
                }
                basis = next;
            }
        }
        let inverse = denominator.inv()?;
        for ell in 0..count {
            let scale = values[ell].mul(inverse);
            for k in 0..basis.len() {
                out[ell][k] = out[ell][k].add(basis[k].mul(scale));
            }
        }
    }
    Ok(out)
}
fn correct_polynomials(
    points: &BTreeMap<u16, Vec<Field>>,
    degree: usize,
    required: usize,
    count: usize,
) -> Result<Option<(Vec<Vec<Field>>, Vec<u16>)>> {
    let ps = points
        .iter()
        .map(|(h, v)| (*h, v.clone()))
        .collect::<Vec<_>>();
    let k = degree + 1;
    if ps.len() < required || ps.len() < k {
        return Ok(None);
    }
    let mut indices = (0..k).collect::<Vec<_>>();
    loop {
        let subset = indices.iter().map(|i| ps[*i].clone()).collect::<Vec<_>>();
        let candidate = polynomial(&subset, count)?;
        let support = ps
            .iter()
            .filter(|(h, v)| {
                candidate
                    .iter()
                    .enumerate()
                    .all(|(ell, p)| eval(p, Field(*h as u128 + 1)) == v[ell])
            })
            .map(|(h, _)| *h)
            .collect::<Vec<_>>();
        if support.len() >= required {
            return Ok(Some((candidate, support)));
        }
        let mut i = k;
        while i > 0 && indices[i - 1] == ps.len() - k + i - 1 {
            i -= 1;
        }
        if i == 0 {
            break;
        }
        indices[i - 1] += 1;
        for j in i..k {
            indices[j] = indices[j - 1] + 1;
        }
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;
    fn generation() -> Generation {
        Generation {
            invocation: Nat::new(19),
            command: vec![3, 4],
            attempt: Nat::new(0),
            generation: Nat::new(1),
            configuration: Nat::from_be(&[254; 32]),
        }
    }
    fn polys() -> Vec<Vec<Field>> {
        vec![vec![Field(42), Field(7)], vec![Field(91), Field(11)]]
    }
    fn drain(ns: &mut [AcssId], q: &mut VecDeque<(u16, Send)>, drop: Option<u16>) {
        let mut steps = 0;
        while let Some((sender, p)) = q.pop_front() {
            steps += 1;
            assert!(steps < 500000, "actual ACSS progress");
            if Some(sender) == drop || Some(p.to) == drop {
                continue;
            }
            let receiver = p.to;
            let out = ns[receiver as usize].receive(sender, p.message).unwrap();
            q.extend(out.into_iter().map(|p| (receiver, p)));
        }
    }
    fn distribute() -> Vec<AcssId> {
        let mut ns = (0..4)
            .map(|i| AcssId::new(i, 0, 4, 1, &generation(), 2).unwrap())
            .collect::<Vec<_>>();
        let out = ns[0].dealer(&polys(), [19; 32]).unwrap();
        let mut q = out.into_iter().map(|p| (0, p)).collect::<VecDeque<_>>();
        drain(&mut ns, &mut q, None);
        for n in &ns {
            assert!(n.sharing_complete());
            match n.local_sharing().unwrap() {
                LocalSharing::Accepted(v) => {
                    assert_eq!(v.holder(), n.me);
                    assert_eq!(
                        v.shares(),
                        polys()
                            .iter()
                            .map(|p| eval(p, Field(n.me as u128 + 1)))
                            .collect::<Vec<_>>()
                    );
                    assert_eq!(v.column_proofs().len(), 4);
                }
                LocalSharing::Rejected(_) => panic!("honest dealer rejected"),
            }
        }
        ns
    }
    #[test]
    fn bivariate_real_private_rows_and_dzk_accept_exact_local_shares() {
        distribute();
    }
    #[test]
    fn dealer_disappearance_and_one_bad_public_column_reconstruct_exact_secrets() {
        let mut ns = distribute();
        let mut q = VecDeque::new();
        for n in &mut ns[1..] {
            let id = n.me;
            q.extend(
                n.request_public_reconstruction()
                    .unwrap()
                    .into_iter()
                    .map(|p| (id, p)),
            );
        }
        // Corrupt holder0 can equivocate/publicly inject arbitrary field vectors.
        for n in &mut ns[1..] {
            n.receive(
                0,
                Message {
                    context: n.context,
                    body: Body::PublicColumn {
                        column: 0,
                        values: vec![Field(666)],
                    },
                },
            )
            .unwrap();
        }
        drain(&mut ns, &mut q, Some(0));
        for n in &ns[1..] {
            let output = n.public_reconstruction().unwrap();
            assert_eq!(output.secrets(), [Field(42), Field(91)]);
            assert!(!output.support().contains(&0));
        }
    }
    #[test]
    fn complaint_and_f_plus_one_environment_requests_gate_opening_and_false_accuser() {
        let mut ns = distribute();
        assert!(ns[1].request_open(0).is_err());
        // Byzantine holder0 authenticates its own false complaint.
        let mut q = ns[0]
            .all(Body::Complaint {
                holder: 0,
                phase: PhaseMessage::Init(vec![1]),
            })
            .into_iter()
            .map(|p| (0, p))
            .collect::<VecDeque<_>>();
        drain(&mut ns, &mut q, None);
        q.extend(ns[0].request_open(0).unwrap().into_iter().map(|p| (0, p)));
        drain(&mut ns, &mut q, None);
        assert!(ns.iter().all(|n| n.accusation(0).is_none())); // f requests alone never disclose
        q.extend(ns[1].request_open(0).unwrap().into_iter().map(|p| (1, p)));
        drain(&mut ns, &mut q, None);
        for n in &ns {
            assert_eq!(n.accusation(0).unwrap().fault(), FaultParty::Accuser(0));
        }
    }
    #[test]
    fn robust_polynomial_decoding_waits_for_n_minus_f_matching_points() {
        let mut points = BTreeMap::new();
        points.insert(0, vec![Field(777)]);
        for holder in 1..=2 {
            points.insert(
                holder,
                vec![eval(&[Field(42), Field(7)], Field(holder as u128 + 1))],
            );
        }
        assert!(correct_polynomials(&points, 1, 3, 1).unwrap().is_none());
        points.insert(3, vec![eval(&[Field(42), Field(7)], Field(4))]);
        let (polys, support) = correct_polynomials(&points, 1, 3, 1).unwrap().unwrap();
        assert_eq!(polys, vec![vec![Field(42), Field(7)]]);
        assert_eq!(support, vec![1, 2, 3]);
        let mut n = AcssId::new(1, 0, 4, 1, &generation(), 2).unwrap();
        assert!(n.request_public_reconstruction().is_err());
        assert!(n
            .receive(
                0,
                Message {
                    context: [0; 32],
                    body: Body::PublicColumn {
                        column: 0,
                        values: vec![Field(1)]
                    }
                }
            )
            .is_err());
        let c = n.context;
        assert!(n
            .receive(
                1,
                Message {
                    context: c,
                    body: Body::PublicColumn {
                        column: 0,
                        values: vec![Field(1)]
                    }
                }
            )
            .is_err());
    }
}
