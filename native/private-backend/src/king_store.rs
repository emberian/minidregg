//! One crash-durable composite for a holder's whole King preparation and check:
//! the three dealers' ACSS-Id and Sh2t-Id instances, the preparation burn
//! receipt, and the TripleKing, all behind ONE transition journal. A killed
//! process recovers from this file alone.
//!
//! Ordering is the point. Every dealer input and every received frame is a
//! journaled event; the burn receipt is journaled before the King can read an
//! accepted share; recovery replays events and never re-deals or re-burns.
//! A crash between the anchor burn and the journal append is repaired from the
//! retained local receipt: `PreparedBasis::from_burned` verifies it against the
//! exact manifest and allocates nothing.
//!
//! A receive event identical to one already journaled is dropped before it is
//! appended, so a peer that replays its whole outbox after a restart costs one
//! hash lookup per frame, not a journal record.
//!
//! Honest crash disk only, as `transition_journal`. The anchor is a separate
//! retained authority; `open` and `burn` check that it still stands behind the
//! burn receipt, which is a regression check, not an independent custody proof.
use crate::{
    acss_id::{self, AcssId},
    acss_id_store::{self, AcssMachine},
    asks::PhaseMessage,
    codec::{bad, bytes, Generation, Nat},
    consensus_wire::Cursor,
    custody::hash,
    entropy::Entropy,
    reconstruction::Field,
    sh2t_id::{self, Sh2tId},
    sh2t_id_store::{self, Sh2tMachine},
    transition_journal::{Journal, Machine},
    triple_king::{
        self, acss_seed_count, per_group, Body, CheckFailure, CheckedTriples, Message,
        PreparedBasis, PreparedSource, TripleKing,
    },
};
use std::{
    collections::BTreeSet,
    fs,
    io::Result,
    path::{Path, PathBuf},
};

const WIRE: &[u8] = b"DREGG.TRIPLE.KING.WIRE\x01";

fn put_fields(v: &[Field], b: &mut Vec<u8>) {
    sh2t_id_store::put_fields(v, b)
}
/// Canonical wire form of one King frame.
pub fn encode_message(m: &Message) -> Vec<u8> {
    let mut b = WIRE.to_vec();
    b.extend(m.context);
    match &m.body {
        Body::InitialPoint(v) => {
            b.push(0);
            put_fields(v, &mut b);
        }
        Body::InitialResult(p) => {
            b.push(1);
            sh2t_id_store::put_phase(p, &mut b);
        }
        Body::MaskedPoint(v) => {
            b.push(2);
            put_fields(v, &mut b);
        }
        Body::MaskedResult(p) => {
            b.push(3);
            sh2t_id_store::put_phase(p, &mut b);
        }
        Body::ChallengePoint(x) => {
            b.push(4);
            b.extend(x.0.to_le_bytes());
        }
        Body::ChallengeResult(p) => {
            b.push(5);
            sh2t_id_store::put_phase(p, &mut b);
        }
        Body::ChallengeAgreement(p) => {
            b.push(6);
            sh2t_id_store::put_phase(p, &mut b);
        }
        Body::CheckPoint(v) => {
            b.push(7);
            put_fields(v, &mut b);
        }
        Body::CheckResult(p) => {
            b.push(8);
            sh2t_id_store::put_phase(p, &mut b);
        }
        Body::CheckAgreement(p) => {
            b.push(9);
            sh2t_id_store::put_phase(p, &mut b);
        }
        Body::FaultPoint(v) => {
            b.push(10);
            put_fields(v, &mut b);
        }
        Body::FaultSh2t { dealer, message } => {
            b.push(11);
            b.extend(dealer.to_le_bytes());
            bytes(&sh2t_id_store::encode_message(message), &mut b);
        }
        Body::FaultResult(p) => {
            b.push(12);
            sh2t_id_store::put_phase(p, &mut b);
        }
    }
    b
}
pub fn decode_message(b: &[u8]) -> Result<Message> {
    let mut c = Cursor::new(b)?;
    if c.take(WIRE.len())? != WIRE {
        return Err(bad("King wire domain"));
    }
    let context = c.fixed32()?;
    let phase = |c: &mut Cursor| -> Result<PhaseMessage> { sh2t_id_store::phase(c) };
    let body = match c.byte()? {
        0 => Body::InitialPoint(sh2t_id_store::fields(&mut c)?),
        1 => Body::InitialResult(phase(&mut c)?),
        2 => Body::MaskedPoint(sh2t_id_store::fields(&mut c)?),
        3 => Body::MaskedResult(phase(&mut c)?),
        4 => Body::ChallengePoint(Field(u128::from_le_bytes(c.take(16)?.try_into().unwrap()))),
        5 => Body::ChallengeResult(phase(&mut c)?),
        6 => Body::ChallengeAgreement(phase(&mut c)?),
        7 => Body::CheckPoint(sh2t_id_store::fields(&mut c)?),
        8 => Body::CheckResult(phase(&mut c)?),
        9 => Body::CheckAgreement(phase(&mut c)?),
        10 => Body::FaultPoint(sh2t_id_store::fields(&mut c)?),
        11 => Body::FaultSh2t {
            dealer: c.u16()?,
            message: sh2t_id_store::decode_message(&c.bytes()?)?,
        },
        12 => Body::FaultResult(phase(&mut c)?),
        _ => return Err(bad("King wire tag")),
    };
    c.finish()?;
    let m = Message { context, body };
    if encode_message(&m) != b {
        return Err(bad("King wire canonical"));
    }
    Ok(m)
}
fn king_outbox(ps: &[triple_king::Send]) -> Vec<u8> {
    let mut b = vec![];
    Nat::new(ps.len() as u64).put(&mut b);
    for p in ps {
        b.extend(p.to.to_le_bytes());
        bytes(&encode_message(&p.message), &mut b);
    }
    b
}
fn parse_king_outbox(b: &[u8], n: usize) -> Result<Vec<triple_king::Send>> {
    let mut c = Cursor::new(b)?;
    let len = acss_id_store::count(&mut c)?;
    if len > crate::codec::MAX / 40 {
        return Err(bad("King outbox bound"));
    }
    let mut out = vec![];
    for _ in 0..len {
        let to = c.u16()?;
        if to as usize >= n {
            return Err(bad("King outbox recipient"));
        }
        out.push(triple_king::Send {
            to,
            message: decode_message(&c.bytes()?)?,
        });
    }
    c.finish()?;
    if king_outbox(&out) != b {
        return Err(bad("King outbox canonical"));
    }
    Ok(out)
}

/// One preparation source: the public identity of the dealer whose ACSS-Id
/// (degree f) and Sh2t-Id (degree 2f) instances this holder takes part in.
#[derive(Clone)]
pub struct Source {
    pub dealer: u16,
    pub degree_f: Generation,
    pub degree_2f: Generation,
}
/// The public shape of one holder's composite. Nothing secret.
#[derive(Clone)]
pub struct Shape {
    pub me: u16,
    pub n: usize,
    pub f: usize,
    pub king: u16,
    pub count: usize,
    pub group: usize,
    pub consumer: Generation,
    pub sources: Vec<Source>,
}
impl Shape {
    fn identity(&self) -> Vec<u8> {
        let mut b = b"DREGG.TRIPLE.KING.PARTY.WAL.V1".to_vec();
        for v in [
            self.me as u64,
            self.n as u64,
            self.f as u64,
            self.king as u64,
        ] {
            b.extend(v.to_le_bytes());
        }
        for v in [self.count as u64, self.group as u64] {
            b.extend(v.to_le_bytes());
        }
        self.consumer.put(&mut b);
        for s in &self.sources {
            b.extend(s.dealer.to_le_bytes());
            s.degree_f.put(&mut b);
            s.degree_2f.put(&mut b);
        }
        let mut id = b"DREGG.TRIPLE.KING.PARTY.WAL.IDENTITY\x01".to_vec();
        id.extend(hash(&b));
        id
    }
}

/// A message this holder must deliver, tagged with the instance it belongs to.
#[derive(Clone, Debug)]
pub enum Out {
    /// ACSS-Id instance of source `k`.
    Acss {
        k: usize,
        send: acss_id::Send,
    },
    /// Sh2t-Id instance of source `k`.
    Sh2t {
        k: usize,
        send: sh2t_id::Send,
    },
    King(triple_king::Send),
}
impl Out {
    pub fn to(&self) -> u16 {
        match self {
            Out::Acss { send, .. } => send.to,
            Out::Sh2t { send, .. } => send.to,
            Out::King(send) => send.to,
        }
    }
}
fn wrap(tag: u8, k: usize, inner: &[u8]) -> Vec<u8> {
    let mut o = vec![tag, k as u8];
    bytes(inner, &mut o);
    o
}
fn parse_outbox(b: &[u8], n: usize) -> Result<Vec<Out>> {
    let mut c = Cursor::new(b)?;
    let tag = c.byte()?;
    match tag {
        0 | 1 => {
            let k = c.byte()? as usize;
            let inner = c.bytes()?;
            c.finish()?;
            if tag == 0 {
                Ok(acss_id_store::parse_outbox(&inner, n)?
                    .into_iter()
                    .map(|send| Out::Acss { k, send })
                    .collect())
            } else {
                Ok(sh2t_id_store::parse_outbox(&inner, n)?
                    .into_iter()
                    .map(|send| Out::Sh2t { k, send })
                    .collect())
            }
        }
        2 => {
            c.finish()?;
            Ok(vec![])
        }
        3..=5 => {
            let inner = c.bytes()?;
            c.finish()?;
            Ok(parse_king_outbox(&inner, n)?
                .into_iter()
                .map(Out::King)
                .collect())
        }
        _ => Err(bad("King store outbox tag")),
    }
}

#[derive(Clone)]
pub struct KingMachine {
    shape: Shape,
    acss: Vec<AcssMachine>,
    sh2t: Vec<Sh2tMachine>,
    dealt_acss: Vec<bool>,
    dealt_sh2t: Vec<bool>,
    king: Option<TripleKing>,
    king_started: bool,
    seen: BTreeSet<[u8; 32]>,
}
impl KingMachine {
    fn new(shape: Shape) -> Result<Self> {
        let seeds = acss_seed_count(shape.count, shape.f)?;
        let batch = per_group(shape.count, shape.f)?;
        if shape.sources.len() != 2 * shape.f + 1 || shape.sources.len() > 255 {
            return Err(bad("King store source count"));
        }
        let mut acss = vec![];
        let mut sh2t = vec![];
        for s in &shape.sources {
            acss.push(AcssMachine {
                state: AcssId::new(shape.me, s.dealer, shape.n, shape.f, &s.degree_f, seeds)?,
            });
            sh2t.push(Sh2tMachine {
                state: Sh2tId::new(shape.me, s.dealer, shape.n, shape.f, &s.degree_2f, batch)?,
            });
        }
        let k = shape.sources.len();
        Ok(Self {
            shape,
            acss,
            sh2t,
            dealt_acss: vec![false; k],
            dealt_sh2t: vec![false; k],
            king: None,
            king_started: false,
            seen: BTreeSet::new(),
        })
    }
    fn source(&self, k: u8) -> Result<usize> {
        let k = k as usize;
        if k >= self.shape.sources.len() {
            return Err(bad("King store source index"));
        }
        Ok(k)
    }
    /// An event that delivers a frame: refused if an identical one was applied.
    fn note_receive(&mut self, event: &[u8]) -> Result<()> {
        if !self.seen.insert(hash(event)) {
            return Err(bad("duplicate receive event"));
        }
        Ok(())
    }
    fn already_received(&self, event: &[u8]) -> bool {
        self.seen.contains(&hash(event))
    }
    fn prepared_sources(&self) -> Result<Vec<PreparedSource>> {
        self.shape
            .sources
            .iter()
            .enumerate()
            .map(|(k, s)| {
                PreparedSource::new(
                    self.acss[k].state.clone(),
                    self.sh2t[k].state.clone(),
                    s.degree_f.clone(),
                    s.degree_2f.clone(),
                )
            })
            .collect()
    }
}
impl Machine for KingMachine {
    fn apply(&mut self, event: &[u8]) -> Result<Vec<u8>> {
        let mut c = Cursor::new(event)?;
        match c.byte()? {
            tag @ (0 | 1) => {
                let k = self.source(c.byte()?)?;
                let inner = c.bytes()?;
                c.finish()?;
                let inner_tag = *inner.first().ok_or_else(|| bad("King store empty event"))?;
                if inner_tag == 2 {
                    self.note_receive(event)?;
                }
                let out = if tag == 0 {
                    let out = self.acss[k].apply(&inner)?;
                    self.dealt_acss[k] |= inner_tag == 0;
                    out
                } else {
                    let out = self.sh2t[k].apply(&inner)?;
                    self.dealt_sh2t[k] |= inner_tag == 0;
                    out
                };
                Ok(wrap(tag, k, &out))
            }
            2 => {
                let receipt = c.bytes()?;
                c.finish()?;
                if self.king.is_some() {
                    return Err(bad("preparation already burned into the King"));
                }
                let s = &self.shape;
                let basis = PreparedBasis::from_burned(
                    &s.consumer,
                    s.king,
                    s.count,
                    s.group,
                    self.prepared_sources()?,
                    receipt,
                )?;
                self.king = Some(TripleKing::new(&s.consumer, basis)?);
                Ok(vec![2])
            }
            3 => {
                c.finish()?;
                let king = self
                    .king
                    .as_mut()
                    .ok_or_else(|| bad("King start before burn"))?;
                let out = king.start()?;
                self.king_started = true;
                Ok(wrap_king(3, &out))
            }
            4 => {
                let sender = c.u16()?;
                let m = decode_message(&c.bytes()?)?;
                c.finish()?;
                self.note_receive(event)?;
                let king = self
                    .king
                    .as_mut()
                    .ok_or_else(|| bad("King frame before burn"))?;
                Ok(wrap_king(4, &king.receive(sender, m)?))
            }
            5 => {
                c.finish()?;
                let king = self
                    .king
                    .as_mut()
                    .ok_or_else(|| bad("King fault localization before burn"))?;
                Ok(wrap_king(5, &king.begin_fault_localization()?))
            }
            _ => Err(bad("King store event tag")),
        }
    }
}
fn wrap_king(tag: u8, out: &[triple_king::Send]) -> Vec<u8> {
    let mut o = vec![tag];
    bytes(&king_outbox(out), &mut o);
    o
}

pub struct KingStore {
    journal: Journal<KingMachine>,
    anchor: PathBuf,
    local: PathBuf,
}
impl KingStore {
    /// Open or recover. If the journal already holds the burn, the anchor must
    /// still retain every allocation of the receipt.
    pub fn open(path: &Path, shape: Shape, anchor: &Path, local: &Path) -> Result<Self> {
        let identity = shape.identity();
        let journal = Journal::open(path, &identity, KingMachine::new(shape)?)?;
        let s = Self {
            journal,
            anchor: anchor.to_path_buf(),
            local: local.to_path_buf(),
        };
        s.verify_standing()?;
        Ok(s)
    }
    fn machine(&self) -> &KingMachine {
        self.journal.state()
    }
    fn verify_standing(&self) -> Result<()> {
        match self.machine().king.as_ref() {
            Some(k) => k.retained_basis().verify_burn_standing(&self.anchor),
            None => Ok(()),
        }
    }
    fn apply(&mut self, event: &[u8]) -> Result<Vec<Out>> {
        let out = self.journal.append(event)?;
        parse_outbox(&out, self.machine().shape.n)
    }
    /// A receive event is journaled once: an identical one returns no sends.
    fn apply_receive(&mut self, event: Vec<u8>) -> Result<Vec<Out>> {
        if self.machine().already_received(&event) {
            return Ok(vec![]);
        }
        self.apply(&event)
    }
    fn source_of_me(&self) -> Result<usize> {
        let me = self.machine().shape.me;
        self.machine()
            .shape
            .sources
            .iter()
            .position(|s| s.dealer == me)
            .ok_or_else(|| bad("this holder deals no preparation source"))
    }
    /// Deal this holder's own preparation instances from its own entropy stream:
    /// uniform degree-f ACSS secrets and coefficients, degree-2f Sh2t zero
    /// polynomials (constant term zero, uniform higher coefficients), and the two
    /// dealing seeds. Each instance is dealt once; a call after a crash between
    /// the two journal records deals only what is missing, and the sends of what
    /// was already dealt are in `replay_outboxes`.
    pub fn deal_preparation(&mut self, e: &mut Entropy) -> Result<Vec<Out>> {
        let k = self.source_of_me()?;
        let f = self.machine().shape.f;
        let mut out = vec![];
        if !self.machine().dealt_acss[k] {
            let polys = (0..self.machine().acss[k].state.count)
                .map(|_| (0..=f).map(|_| e.field()).collect::<Vec<_>>())
                .collect::<Vec<_>>();
            let seed = e.bytes32();
            out.extend(self.acss_dealer(k, &polys, seed)?);
        }
        if !self.machine().dealt_sh2t[k] {
            let polys = (0..self.machine().sh2t[k].state.count())
                .map(|_| {
                    let mut p = vec![Field(0)];
                    p.extend((0..2 * f).map(|_| e.field()));
                    p
                })
                .collect::<Vec<_>>();
            let seed = e.bytes32();
            out.extend(self.sh2t_dealer(k, &polys, seed)?);
        }
        Ok(out)
    }
    /// Journal the dealer inputs of source `k` (this holder must be its dealer).
    pub fn acss_dealer(
        &mut self,
        k: usize,
        polys: &[Vec<Field>],
        seed: [u8; 32],
    ) -> Result<Vec<Out>> {
        let k = self.machine().source(k as u8)?;
        let mut e = vec![0, k as u8];
        bytes(&acss_id_store::dealer_event(seed, polys), &mut e);
        self.apply(&e)
    }
    pub fn sh2t_dealer(
        &mut self,
        k: usize,
        polys: &[Vec<Field>],
        seed: [u8; 32],
    ) -> Result<Vec<Out>> {
        let k = self.machine().source(k as u8)?;
        let mut e = vec![1, k as u8];
        bytes(&sh2t_id_store::dealer_event(seed, polys), &mut e);
        self.apply(&e)
    }
    pub fn acss_receive(
        &mut self,
        k: usize,
        sender: u16,
        m: &acss_id::Message,
    ) -> Result<Vec<Out>> {
        let k = self.machine().source(k as u8)?;
        let mut inner = vec![2];
        inner.extend(sender.to_le_bytes());
        bytes(&acss_id_store::encode_message(m), &mut inner);
        let mut e = vec![0, k as u8];
        bytes(&inner, &mut e);
        self.apply_receive(e)
    }
    pub fn sh2t_receive(
        &mut self,
        k: usize,
        sender: u16,
        m: &sh2t_id::Message,
    ) -> Result<Vec<Out>> {
        let k = self.machine().source(k as u8)?;
        let mut inner = vec![2];
        inner.extend(sender.to_le_bytes());
        bytes(&sh2t_id_store::encode_message(m), &mut inner);
        let mut e = vec![1, k as u8];
        bytes(&inner, &mut e);
        self.apply_receive(e)
    }
    /// Burn the preparation manifest at the anchor (once, ever) and journal the
    /// receipt. If a receipt for this holder is already on disk, the anchor burn
    /// happened and only the journal record is missing: it is read back and
    /// verified against the exact manifest, and nothing is allocated.
    pub fn burn(&mut self) -> Result<()> {
        if self.machine().king.is_none() {
            let receipt = if self.local.exists() {
                fs::read(&self.local)?
            } else {
                let s = &self.machine().shape;
                let basis = PreparedBasis::reserve_new(
                    &s.consumer,
                    s.king,
                    s.count,
                    s.group,
                    self.machine().prepared_sources()?,
                    &self.anchor,
                    &self.local,
                )?;
                basis.burn_receipt().to_vec()
            };
            let mut e = vec![2];
            bytes(&receipt, &mut e);
            self.apply(&e)?;
        }
        self.verify_standing()
    }
    pub fn king_start(&mut self) -> Result<Vec<Out>> {
        if self.machine().king_started {
            return Ok(vec![]);
        }
        self.apply(&[3])
    }
    pub fn king_receive(&mut self, sender: u16, m: &Message) -> Result<Vec<Out>> {
        let mut e = vec![4];
        e.extend(sender.to_le_bytes());
        bytes(&encode_message(m), &mut e);
        self.apply_receive(e)
    }
    pub fn begin_fault_localization(&mut self) -> Result<Vec<Out>> {
        self.apply(&[5])
    }
    /// Every send of every journaled event, in order. After a restart the
    /// holder re-publishes these; receivers drop what they already journaled.
    pub fn replay_outboxes(&self) -> Result<Vec<Out>> {
        let mut out = vec![];
        for b in self.journal.replay_outboxes() {
            out.extend(parse_outbox(b, self.machine().shape.n)?);
        }
        Ok(out)
    }
    pub fn is_burned(&self) -> bool {
        self.machine().king.is_some()
    }
    pub fn king_started(&self) -> bool {
        self.machine().king_started
    }
    pub fn acss_state(&self, k: usize) -> &AcssId {
        &self.machine().acss[k].state
    }
    pub fn sh2t_state(&self, k: usize) -> &Sh2tId {
        &self.machine().sh2t[k].state
    }
    pub fn checked_triples(&self) -> Option<&CheckedTriples> {
        self.machine()
            .king
            .as_ref()
            .and_then(TripleKing::checked_triples)
    }
    pub fn failure(&self) -> Option<&CheckFailure> {
        self.machine().king.as_ref().and_then(TripleKing::failure)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        reconstruction::Field,
        triple_king::tests::{test_generation, AnchorFixture},
    };
    use std::{
        collections::VecDeque,
        os::unix::process::ExitStatusExt,
        process::{Command, Stdio},
        time::{Duration, Instant, SystemTime, UNIX_EPOCH},
    };

    const N: usize = 4;
    const COUNT: usize = 1;
    const DIR: &str = "MINI_KING_STORE_DIR";
    const MARKER_AFTER_KING_FRAMES: usize = 8;
    const KILL_TEST: &str = "king_store::tests::kill9_child_runs_the_king_until_killed";

    fn shape(me: u16) -> Shape {
        Shape {
            me,
            n: N,
            f: 1,
            king: 0,
            count: COUNT,
            group: 0,
            consumer: test_generation(300),
            sources: (0..3u16)
                .map(|d| Source {
                    dealer: d,
                    degree_f: test_generation(100 + d as u64),
                    degree_2f: test_generation(200 + d as u64),
                })
                .collect(),
        }
    }
    fn scratch(label: &str) -> PathBuf {
        let p = std::env::temp_dir().join(format!(
            "mini-king-store-{label}-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir_all(&p).unwrap();
        p
    }
    struct Cluster {
        stores: Vec<KingStore>,
        anchors: Vec<AnchorFixture>,
        roots: Vec<PathBuf>,
        queue: VecDeque<(u16, Out)>,
    }
    impl Cluster {
        /// Open (or reopen after a kill) all four holders under `dir`.
        fn open(dir: &Path) -> Self {
            let roots = (0..N)
                .map(|i| {
                    let r = dir.join(format!("holder{i}"));
                    fs::create_dir_all(&r).unwrap();
                    r
                })
                .collect::<Vec<_>>();
            let anchors = roots
                .iter()
                .map(|r| AnchorFixture::new(r))
                .collect::<Vec<_>>();
            let stores = (0..N)
                .map(|i| {
                    KingStore::open(
                        &roots[i].join("king.wal"),
                        shape(i as u16),
                        anchors[i].socket(),
                        &roots[i].join("burn"),
                    )
                    .unwrap()
                })
                .collect();
            Self {
                stores,
                anchors,
                roots,
                queue: VecDeque::new(),
            }
        }
        fn push(&mut self, from: u16, outs: Vec<Out>) {
            self.queue.extend(outs.into_iter().map(|o| (from, o)));
        }
        fn deal_all(&mut self, root: &Entropy) {
            for i in 0..3u16 {
                let mut e = root.fork(&[b'd', i as u8]);
                let outs = self.stores[i as usize].deal_preparation(&mut e).unwrap();
                self.push(i, outs);
            }
        }
        /// Deliver one queued frame; returns true if it was a King frame.
        fn step(&mut self) -> Option<bool> {
            let (from, out) = self.queue.pop_front()?;
            let to = out.to();
            let (outs, king) = match &out {
                Out::Acss { k, send } => (
                    self.stores[to as usize]
                        .acss_receive(*k, from, &send.message)
                        .unwrap(),
                    false,
                ),
                Out::Sh2t { k, send } => (
                    self.stores[to as usize]
                        .sh2t_receive(*k, from, &send.message)
                        .unwrap(),
                    false,
                ),
                Out::King(send) => (
                    self.stores[to as usize]
                        .king_receive(from, &send.message)
                        .unwrap(),
                    true,
                ),
            };
            self.push(to, outs);
            Some(king)
        }
        fn drain(&mut self, mut after: impl FnMut(bool)) {
            let mut steps = 0;
            while let Some(king) = self.step() {
                steps += 1;
                assert!(steps < 2_000_000);
                after(king);
            }
        }
        fn burn_all(&mut self) {
            for s in &mut self.stores {
                s.burn().unwrap();
            }
        }
        fn start_all(&mut self) {
            for i in 0..N {
                let outs = self.stores[i].king_start().unwrap();
                self.push(i as u16, outs);
            }
        }
        fn allocations(&self, holder: usize) -> usize {
            let j = crate::codec::Journal::decode(
                &crate::custody::rpc(self.anchors[holder].socket(), &[0]).unwrap(),
            )
            .unwrap();
            j.allocations.len()
        }
        fn wal(&self, holder: usize) -> PathBuf {
            self.roots[holder].join("king.wal")
        }
    }
    /// Every journaled event of a King WAL (test-side parse of the on-disk format).
    fn wal_events(path: &Path) -> Vec<Vec<u8>> {
        let all = fs::read(path).unwrap();
        let mut c = Cursor::new(&all).unwrap();
        c.take(b"DREGG.TRANSITION.WAL\x01".len()).unwrap();
        c.bytes().unwrap();
        c.take(32).unwrap();
        let mut events = vec![];
        loop {
            let Ok(len) = c.take(8) else { break };
            let n = u64::from_le_bytes(len.try_into().unwrap()) as usize;
            let Ok(body) = c.take(n) else { break };
            if c.take(32).is_err() {
                break;
            }
            let mut r = Cursor::new(body).unwrap();
            events.push(r.bytes().unwrap());
        }
        events
    }
    /// (acss dealer events, sh2t dealer events) per source index k.
    fn dealer_events(path: &Path) -> Vec<(usize, usize)> {
        let mut per = vec![(0, 0); 3];
        for e in wal_events(path) {
            let mut c = Cursor::new(&e).unwrap();
            let tag = c.byte().unwrap();
            if tag > 1 {
                continue;
            }
            let k = c.byte().unwrap() as usize;
            if c.bytes().unwrap()[0] == 0 {
                if tag == 0 {
                    per[k].0 += 1;
                } else {
                    per[k].1 += 1;
                }
            }
        }
        per
    }
    /// The checked triples of the four holders are one coherent degree-f sharing
    /// of (a, b, c) with c = a*b.
    fn assert_exact_product(c: &Cluster) {
        let triples = c
            .stores
            .iter()
            .map(|s| s.checked_triples().expect("checked triples").clone())
            .collect::<Vec<_>>();
        let points = triples
            .iter()
            .take(2)
            .map(|t| {
                let (a, b, cc) = t.triples()[0];
                (t.holder(), vec![a, b, cc])
            })
            .collect::<Vec<_>>();
        let polys = acss_id::polynomial(&points, 3).unwrap();
        assert_ne!(polys[0][0], Field(0));
        assert_ne!(polys[1][0], Field(0));
        assert_eq!(polys[0][0].mul(polys[1][0]), polys[2][0]);
        for t in &triples {
            let tuple = t.triples()[0];
            for (i, v) in [tuple.0, tuple.1, tuple.2].iter().enumerate() {
                let x = Field(t.holder() as u128 + 1);
                let at = polys[i]
                    .iter()
                    .rev()
                    .fold(Field(0), |a, k| a.mul(x).add(*k));
                assert_eq!(*v, at, "holder {} component {i}", t.holder());
            }
        }
    }
    fn prepared(dir: &Path) -> Cluster {
        let root = crate::entropy::test_root();
        let mut c = Cluster::open(dir);
        c.deal_all(&root);
        c.drain(|_| {});
        c.burn_all();
        c
    }

    #[test]
    fn king_wire_codec_roundtrips_every_body_and_refuses_noncanonical() {
        let ctx = [7; 32];
        let ph = PhaseMessage::Echo(vec![1, 2, 3]);
        let sh = sh2t_id::Message {
            context: [9; 32],
            body: sh2t_id::Body::Termination(PhaseMessage::Ready(vec![4])),
        };
        let bodies = vec![
            Body::InitialPoint(vec![Field(1), Field(u128::MAX)]),
            Body::InitialResult(ph.clone()),
            Body::MaskedPoint(vec![Field(2)]),
            Body::MaskedResult(ph.clone()),
            Body::ChallengePoint(Field(5)),
            Body::ChallengeResult(ph.clone()),
            Body::ChallengeAgreement(ph.clone()),
            Body::CheckPoint(vec![Field(3), Field(4)]),
            Body::CheckResult(ph.clone()),
            Body::CheckAgreement(ph.clone()),
            Body::FaultPoint(vec![Field(6)]),
            Body::FaultSh2t {
                dealer: 2,
                message: sh,
            },
            Body::FaultResult(ph),
        ];
        assert_eq!(bodies.len(), 13);
        for body in bodies {
            let m = Message { context: ctx, body };
            let b = encode_message(&m);
            assert_eq!(decode_message(&b).unwrap(), m);
            let mut t = b.clone();
            t.push(0);
            assert!(decode_message(&t).is_err());
            let mut bad_domain = b;
            bad_domain[0] ^= 1;
            assert!(decode_message(&bad_domain).is_err());
        }
    }

    #[test]
    fn clean_run_reopens_to_identical_checked_triples_and_one_dealer_event_each() {
        let dir = scratch("clean");
        let mut c = prepared(&dir);
        c.start_all();
        c.drain(|_| {});
        assert_exact_product(&c);
        let before = c
            .stores
            .iter()
            .map(|s| s.checked_triples().unwrap().triples().to_vec())
            .collect::<Vec<_>>();
        for h in 0..N {
            assert_eq!(c.allocations(h), 6, "3 sources x (ACSS seeds + Sh2t group)");
        }
        drop(c);
        let c = Cluster::open(&dir);
        for (h, s) in c.stores.iter().enumerate() {
            assert!(s.is_burned() && s.king_started());
            assert_eq!(s.checked_triples().unwrap().triples(), &before[h][..]);
            let want = if h < 3 { (1, 1) } else { (0, 0) };
            let got = dealer_events(&c.wal(h));
            for (k, g) in got.iter().enumerate() {
                assert_eq!(
                    *g,
                    if k == h { want } else { (0, 0) },
                    "holder {h} source {k}"
                );
            }
        }
        assert_exact_product(&c);
    }

    #[test]
    fn identical_receive_event_is_dropped_before_the_journal() {
        let dir = scratch("dedupe");
        let root = crate::entropy::test_root();
        let mut c = Cluster::open(&dir);
        c.deal_all(&root);
        let (from, out) = c.queue.iter().find(|(_, o)| o.to() == 3).cloned().unwrap();
        let Out::Acss { k, send } = out else {
            panic!("first dealer frame to holder 3 is an ACSS frame");
        };
        let len = |c: &Cluster| fs::metadata(c.wal(3)).unwrap().len();
        let first = c.stores[3].acss_receive(k, from, &send.message).unwrap();
        let after_first = len(&c);
        let again = c.stores[3].acss_receive(k, from, &send.message).unwrap();
        assert!(again.is_empty(), "the replayed frame produces no sends");
        assert_eq!(len(&c), after_first, "and no journal record");
        assert!(!first.is_empty() || after_first > 0);
        // The refusal also holds across a restart: the seen set is rebuilt by replay.
        drop(c);
        let mut c = Cluster::open(&dir);
        assert!(c.stores[3]
            .acss_receive(k, from, &send.message)
            .unwrap()
            .is_empty());
        assert_eq!(len(&c), after_first);
    }

    #[test]
    fn burn_is_repaired_from_the_local_receipt_without_a_second_allocation() {
        let dir = scratch("burn-gap");
        let root = crate::entropy::test_root();
        let mut c = Cluster::open(&dir);
        c.deal_all(&root);
        c.drain(|_| {});
        assert_eq!(c.allocations(1), 0);
        // The process dies after the anchor burn and the local receipt, before
        // the journal record: do exactly the burn, journal nothing.
        let s = &c.stores[1];
        let m = s.machine();
        PreparedBasis::reserve_new(
            &m.shape.consumer,
            m.shape.king,
            m.shape.count,
            m.shape.group,
            m.prepared_sources().unwrap(),
            &s.anchor,
            &s.local,
        )
        .unwrap();
        assert!(!s.is_burned());
        assert_eq!(c.allocations(1), 6);
        // A fresh attempt to burn the same manifest is refused by the anchor...
        assert!(PreparedBasis::reserve_new(
            &m.shape.consumer,
            m.shape.king,
            m.shape.count,
            m.shape.group,
            m.prepared_sources().unwrap(),
            &s.anchor,
            &dir.join("holder1").join("second-burn"),
        )
        .is_err());
        assert_eq!(c.allocations(1), 6);
        // ...and the store repairs the journal from the retained receipt.
        c.stores[1].burn().unwrap();
        assert!(c.stores[1].is_burned());
        assert_eq!(c.allocations(1), 6, "recovery allocated nothing");
        drop(c);
        let c = Cluster::open(&dir);
        assert!(c.stores[1].is_burned());
    }

    #[test]
    fn a_receipt_for_another_consumer_generation_or_a_flipped_byte_is_refused() {
        let dir = scratch("receipt");
        let c = prepared(&dir);
        let s = &c.stores[0];
        let basis = s.machine().king.as_ref().unwrap().retained_basis().clone();
        let receipt = basis.burn_receipt().to_vec();
        let m = s.machine();
        let sources = || m.prepared_sources().unwrap();
        assert!(PreparedBasis::from_burned(
            &m.shape.consumer,
            m.shape.king,
            m.shape.count,
            m.shape.group,
            sources(),
            receipt.clone()
        )
        .is_ok());
        assert!(PreparedBasis::from_burned(
            &test_generation(301),
            m.shape.king,
            m.shape.count,
            m.shape.group,
            sources(),
            receipt.clone()
        )
        .is_err());
        for at in [30, receipt.len() / 2, receipt.len() - 1] {
            let mut t = receipt.clone();
            t[at] ^= 1;
            assert!(
                PreparedBasis::from_burned(
                    &m.shape.consumer,
                    m.shape.king,
                    m.shape.count,
                    m.shape.group,
                    sources(),
                    t
                )
                .is_err(),
                "flipped byte {at}"
            );
        }
    }

    /// The child half of the kill test: runs preparation, burn and the King,
    /// slowing down once the King is under way so the parent can kill it
    /// mid-King. Only meaningful under the parent, hence #[ignore].
    #[test]
    #[ignore]
    fn kill9_child_runs_the_king_until_killed() {
        let dir = PathBuf::from(std::env::var_os(DIR).expect("run by the kill9 parent test"));
        let root = crate::entropy::test_root();
        let mut c = Cluster::open(&dir);
        c.deal_all(&root);
        c.drain(|_| {});
        c.burn_all();
        c.start_all();
        let mut king_frames = 0;
        let marker = dir.join("marker");
        c.drain(|king| {
            if king {
                king_frames += 1;
                if king_frames == MARKER_AFTER_KING_FRAMES {
                    fs::write(&marker, b"king under way").unwrap();
                }
                if king_frames >= MARKER_AFTER_KING_FRAMES {
                    std::thread::sleep(Duration::from_millis(20));
                }
            }
        });
        fs::write(dir.join("completed"), b"the child was not killed").unwrap();
    }

    #[test]
    fn kill9_mid_king_recovers_with_one_dealer_event_per_instance_no_new_allocations_and_complete_triples(
    ) {
        let dir = scratch("kill9");
        let log = fs::File::create(dir.join("child.log")).unwrap();
        let mut child = Command::new(std::env::current_exe().unwrap())
            .args(["--ignored", "--exact", KILL_TEST, "--nocapture"])
            .env(DIR, &dir)
            .stdout(Stdio::from(log.try_clone().unwrap()))
            .stderr(Stdio::from(log))
            .spawn()
            .unwrap();
        let start = Instant::now();
        while !dir.join("marker").exists() {
            if let Some(status) = child.try_wait().unwrap() {
                panic!(
                    "child exited ({status}) before the King was under way:\n{}",
                    fs::read_to_string(dir.join("child.log")).unwrap_or_default()
                );
            }
            assert!(
                start.elapsed() < Duration::from_secs(600),
                "child never reached the King"
            );
            std::thread::sleep(Duration::from_millis(10));
        }
        child.kill().unwrap();
        let status = child.wait().unwrap();
        assert_eq!(
            status.signal(),
            Some(9),
            "killed by SIGKILL, not a clean exit"
        );
        assert!(!dir.join("completed").exists(), "the kill landed mid-King");

        // Recover from disk alone.
        let mut c = Cluster::open(&dir);
        for s in &c.stores {
            assert!(
                s.is_burned(),
                "the burn was journaled before the King read a share"
            );
        }
        assert!(
            c.stores.iter().any(|s| s.checked_triples().is_none()),
            "at least one holder had not finished the King when it was killed"
        );
        let allocations = (0..N).map(|h| c.allocations(h)).collect::<Vec<_>>();
        assert_eq!(
            allocations,
            vec![6; N],
            "the burn happened exactly once per holder"
        );

        // A naive restart would deal again from fresh entropy. The journal knows
        // each instance was dealt, so nothing is dealt and nothing is sent.
        let again = crate::entropy::test_root().fork(b"restart-redeal");
        for i in 0..3 {
            let mut e = again.fork(&[i as u8]);
            assert!(
                c.stores[i].deal_preparation(&mut e).unwrap().is_empty(),
                "holder {i}"
            );
        }
        // Peers re-publish every journaled send; receivers drop what they have.
        let mut republished = vec![];
        for (i, s) in c.stores.iter().enumerate() {
            republished.push((i as u16, s.replay_outboxes().unwrap()));
        }
        for (i, outs) in republished {
            c.push(i, outs);
        }
        c.burn_all();
        for i in 0..N {
            let outs = c.stores[i].king_start().unwrap();
            c.push(i as u16, outs);
        }
        c.drain(|_| {});

        for (h, s) in c.stores.iter().enumerate() {
            assert!(s.failure().is_none(), "holder {h}");
            assert!(
                s.checked_triples().is_some(),
                "holder {h} checked triples complete"
            );
        }
        assert_exact_product(&c);
        let after = (0..N).map(|h| c.allocations(h)).collect::<Vec<_>>();
        assert_eq!(
            after, allocations,
            "recovery allocated nothing at any anchor"
        );
        let mut total = (0, 0);
        for h in 0..N {
            for (k, (a, o)) in dealer_events(&c.wal(h)).into_iter().enumerate() {
                let expected = usize::from(k == h);
                assert_eq!((a, o), (expected, expected), "holder {h} source {k}");
                total = (total.0 + a, total.1 + o);
            }
        }
        assert_eq!(
            total,
            (3, 3),
            "one dealer event per ACSS and per Sh2t instance"
        );
    }
}
