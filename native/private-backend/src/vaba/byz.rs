//! Deterministic adversarial schedule harness for IndexVABA and IndexACS.
//!
//! Everything here is `cfg(test)`. One seed fixes the validation order of every
//! party, the dealer coefficients, the Byzantine behaviours and the delivery
//! schedule, so a failing run is reproduced by its seed alone.
//!
//! Model: static corruption of at most `f` of `n = 3f+1` parties; authenticated
//! reliable channels (an honest-to-honest packet is eventually delivered unless
//! the run injects a [`Fault`], which deliberately violates that premise and is
//! then checked for SAFETY only); external validation is monotone and complete
//! (every index validated by one honest party is eventually validated by all).
//!
//! A Byzantine party is a controller around one or two REAL honest state
//! machines ("copies"). Their outbound traffic is routed per recipient (twin /
//! equivocation), mutated, withheld until a view change, replayed, or silenced.
//! Copies speak only sentences a real party could author, but may author
//! conflicting ones to different recipients; a fuzzer additionally injects
//! arbitrary well-formed frames under the Byzantine sender identity.
//!
//! Run (always filtered; sweeps are CPU-bound, use --release for big ranges):
//!   BYZ_FROM=<first seed> BYZ_SEEDS=<count> cargo test --release --lib byz_vaba_n4_f1_sweep
//! Default is 12 seeds (4 at n=7). Invariants checked on every run: agreement,
//! RA-input agreement (Lemma 5.3), the n-f-matching LOCK on later views (Lemma
//! 5.2), per-view RBC / ASKS commitment / ASKS key agreement, ASKS validity for
//! honest dealers, ICG binding core and binding cover, VABA/ACS validity,
//! termination when the stated assumptions hold, and absence of panics.
//! `Knobs` (rank chaos, literal printed predicates) are instruments, not behaviour.
//! Mutation controls run against this harness (a mutant must turn it red):
//! Alg5 most-frequent check, justification subset check, RA-input quorum, Bracha
//! output quorum and echo quorum, ASKS coherence check, vote admission, frozen
//! justification size, ICG withdraw quorum are each killed; the Gather ACK quorum
//! mutant (f+1 for n-f) is NOT killed by any adversary here.
use super::*;
use crate::{
    acs::{self, Acs},
    codec::{Generation, Nat},
    reconstruction::Field,
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone)]
pub(crate) struct Rng(u64);
impl Rng {
    pub(crate) fn new(seed: u64) -> Self {
        let mut r = Rng(seed ^ 0x9E37_79B9_7F4A_7C15);
        r.next();
        r
    }
    pub(crate) fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    pub(crate) fn below(&mut self, n: usize) -> usize {
        (self.next() % n.max(1) as u64) as usize
    }
    pub(crate) fn chance(&mut self, num: u64, den: u64) -> bool {
        self.next() % den < num
    }
    pub(crate) fn shuffle<T>(&mut self, v: &mut [T]) {
        for i in (1..v.len()).rev() {
            v.swap(i, self.below(i + 1));
        }
    }
}
fn mix(parts: &[u64]) -> u64 {
    let mut r = Rng::new(0);
    for p in parts {
        r.0 ^= *p;
        r.next();
    }
    r.next()
}

type Out<M> = Vec<(u16, M)>;

/// The one interface the harness needs from IndexVABA and from IndexACS.
pub(crate) trait Proto: Clone {
    type Msg: Clone + std::fmt::Debug;
    fn create(me: u16, n: usize, f: usize, g: &Generation) -> Self;
    fn p_validate(&mut self, j: u16) -> Result<Out<Self::Msg>>;
    fn p_receive(&mut self, from: u16, m: Self::Msg) -> Result<Out<Self::Msg>>;
    fn p_entropy(&self) -> Vec<u64>;
    fn p_dealer(&mut self, v: u64, c: &[Vec<Field>]) -> Result<Out<Self::Msg>>;
    fn decision(&self) -> Option<Vec<u16>>;
    fn vaba(&self) -> &Vaba;
    fn view_of(m: &Self::Msg) -> Option<u64>;
    fn is_final(m: &Self::Msg) -> bool;
    fn vmsg_mut(m: &mut Self::Msg) -> Option<&mut Message>;
    fn selector_mut(m: &mut Self::Msg) -> Option<&mut PhaseMessage>;
    fn selector_outputs(&self) -> Vec<Option<Vec<u8>>>;
    fn set_knobs(&mut self, k: Knobs);
    /// A random well-formed (and sometimes ill-formed) frame addressed to this party's protocol.
    fn fuzz_msg(&self, r: &mut Rng) -> Self::Msg;
}
fn conv(v: Vec<Send>) -> Out<Message> {
    v.into_iter().map(|s| (s.to, s.message)).collect()
}
impl Proto for Vaba {
    type Msg = Message;
    fn create(me: u16, n: usize, f: usize, g: &Generation) -> Self {
        Vaba::new(me, n, f, g).unwrap()
    }
    fn p_validate(&mut self, j: u16) -> Result<Out<Message>> {
        self.validate(j).map(conv)
    }
    fn p_receive(&mut self, from: u16, m: Message) -> Result<Out<Message>> {
        self.receive(from, m).map(conv)
    }
    fn p_entropy(&self) -> Vec<u64> {
        self.entropy_needed()
    }
    fn p_dealer(&mut self, v: u64, c: &[Vec<Field>]) -> Result<Out<Message>> {
        self.dealer(v, c).map(conv)
    }
    fn decision(&self) -> Option<Vec<u16>> {
        self.output.map(|k| vec![k])
    }
    fn vaba(&self) -> &Vaba {
        self
    }
    fn view_of(m: &Message) -> Option<u64> {
        if matches!(m.body, Body::Final(_)) {
            None
        } else {
            Some(m.view)
        }
    }
    fn is_final(m: &Message) -> bool {
        matches!(m.body, Body::Final(_))
    }
    fn vmsg_mut(m: &mut Message) -> Option<&mut Message> {
        Some(m)
    }
    fn selector_mut(_: &mut Message) -> Option<&mut PhaseMessage> {
        None
    }
    fn selector_outputs(&self) -> Vec<Option<Vec<u8>>> {
        vec![]
    }
    fn set_knobs(&mut self, k: Knobs) {
        self.knobs = k;
    }
    fn fuzz_msg(&self, r: &mut Rng) -> Message {
        fuzz_vaba(self, r)
    }
}
impl Proto for Acs {
    type Msg = acs::Message;
    fn create(me: u16, n: usize, f: usize, g: &Generation) -> Self {
        Acs::new(me, n, f, g).unwrap()
    }
    fn p_validate(&mut self, j: u16) -> Result<Out<acs::Message>> {
        self.validate(j)
            .map(|v| v.into_iter().map(|s| (s.to, s.message)).collect())
    }
    fn p_receive(&mut self, from: u16, m: acs::Message) -> Result<Out<acs::Message>> {
        self.receive(from, m)
            .map(|v| v.into_iter().map(|s| (s.to, s.message)).collect())
    }
    fn p_entropy(&self) -> Vec<u64> {
        self.entropy_needed()
    }
    fn p_dealer(&mut self, v: u64, c: &[Vec<Field>]) -> Result<Out<acs::Message>> {
        self.dealer(v, c)
            .map(|v| v.into_iter().map(|s| (s.to, s.message)).collect())
    }
    fn decision(&self) -> Option<Vec<u16>> {
        self.output.as_ref().map(|s| s.iter().copied().collect())
    }
    fn vaba(&self) -> &Vaba {
        &self.vaba
    }
    fn view_of(m: &acs::Message) -> Option<u64> {
        match &m.body {
            acs::Body::Vaba(v) => <Vaba as Proto>::view_of(v),
            acs::Body::Selector(..) => None,
        }
    }
    fn is_final(m: &acs::Message) -> bool {
        matches!(&m.body, acs::Body::Vaba(v) if matches!(v.body, Body::Final(_)))
    }
    fn vmsg_mut(m: &mut acs::Message) -> Option<&mut Message> {
        match &mut m.body {
            acs::Body::Vaba(v) => Some(v),
            _ => None,
        }
    }
    fn selector_mut(m: &mut acs::Message) -> Option<&mut PhaseMessage> {
        match &mut m.body {
            acs::Body::Selector(_, p) => Some(p),
            _ => None,
        }
    }
    fn selector_outputs(&self) -> Vec<Option<Vec<u8>>> {
        self.selector_outputs_for_test()
    }
    fn set_knobs(&mut self, k: Knobs) {
        self.vaba.knobs = k;
    }
    fn fuzz_msg(&self, r: &mut Rng) -> acs::Message {
        if r.chance(1, 4) {
            let n = self.n;
            let j = r.below(n) as u16;
            let set: Set = (0..n as u16).filter(|_| r.chance(2, 3)).collect();
            let b = if r.chance(7, 8) {
                acs::set_bytes(&set)
            } else {
                vec![r.next() as u8; r.below(5)]
            };
            let p = match r.below(3) {
                0 => PhaseMessage::Init(b),
                1 => PhaseMessage::Echo(b),
                _ => PhaseMessage::Ready(b),
            };
            acs::Message {
                context: self.context,
                body: acs::Body::Selector(j, p),
            }
        } else {
            acs::Message {
                context: self.context,
                body: acs::Body::Vaba(fuzz_vaba(&self.vaba, r)),
            }
        }
    }
}

fn rand_set(r: &mut Rng, n: usize, min: usize) -> Set {
    let mut s: Set = (0..n as u16).filter(|_| r.chance(3, 4)).collect();
    let mut i = 0;
    while s.len() < min {
        s.insert((i % n) as u16);
        i += 1;
    }
    s
}
fn rand_phase(kind: usize, b: Vec<u8>) -> PhaseMessage {
    match kind {
        0 => PhaseMessage::Init(b),
        1 => PhaseMessage::Echo(b),
        _ => PhaseMessage::Ready(b),
    }
}
/// A random frame for `template`'s protocol instance. Mostly well-formed so the
/// frame reaches deep state, sometimes malformed.
fn fuzz_vaba(template: &Vaba, r: &mut Rng) -> Message {
    let (n, f) = (template.n, template.f);
    let nviews = template.views.len() as u64;
    let view = r.below(nviews as usize + 1) as u64;
    let d = if r.chance(1, 40) {
        n as u16 + r.below(3) as u16
    } else {
        r.below(n) as u16
    };
    let body = match r.below(7) {
        0 => {
            let instance = template
                .views
                .get(&view)
                .and_then(|s| s.asks.get(d as usize))
                .map_or([r.next() as u8; 32], |a| a.instance);
            let ab = match r.below(4) {
                0 => {
                    let k = r.below(3);
                    let v: Vec<u8> = (0..n * 32).map(|_| r.next() as u8).collect();
                    asks::Body::Commit(rand_phase(k, v))
                }
                1 => {
                    asks::Body::PrivateShare(vec![Field(r.next() as u128), Field(r.next() as u128)])
                }
                2 => asks::Body::Ra(rand_phase(r.below(3), vec![1])),
                _ => {
                    asks::Body::Reconstruct(vec![Field(r.next() as u128), Field(r.next() as u128)])
                }
            };
            Body::Asks(d, asks::Message { instance, body: ab })
        }
        1 => {
            let keys = rand_set(r, n, 0);
            let mut justification = Votes::new();
            if r.chance(1, 2) {
                for j in 0..n as u16 {
                    if r.chance(3, 4) {
                        justification.insert(j, r.below(n) as u16);
                    }
                }
            }
            let p = Proposal {
                value: r.below(n) as u16,
                keys,
                justification,
            };
            Body::Pre(d, rand_phase(r.below(3), proposal_bytes(&p)))
        }
        2 => {
            let k = r.below(3);
            Body::Vote(d, rand_phase(k, vote_bytes(r.below(n + 1) as u16)))
        }
        3 | 4 => {
            let ctx = template
                .views
                .get(&view)
                .map_or(template.context, |s| s.context);
            let gb = match r.below(6) {
                0 => {
                    let min = n - f - r.below(2).min(1);
                    gather::Body::Gather(gather::IgBody::Inform(rand_set(r, n, min)))
                }
                1 => gather::Body::Gather(gather::IgBody::Ack),
                2 => gather::Body::Gather(gather::IgBody::Prepare(rand_set(r, n, n - f))),
                3 => gather::Body::Ra(d, rand_phase(r.below(3), vec![1])),
                4 => gather::Body::Withdraw,
                _ => {
                    let k = r.below(3);
                    gather::Body::Ra(d, rand_phase(k, vec![r.next() as u8]))
                }
            };
            Body::Cover(gather::Message {
                context: ctx,
                body: gb,
            })
        }
        _ => {
            let k = r.below(3);
            Body::Final(rand_phase(k, vote_bytes(r.below(n + 1) as u16)))
        }
    };
    Message {
        context: template.context,
        view,
        body,
    }
}

// ---------------------------------------------------------------- scheduling
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Base {
    Fifo,
    Lifo,
    Random,
    /// Per-link random latency; some links are orders of magnitude slower.
    Latency,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ViewPref {
    None,
    High,
    Low,
}
#[derive(Clone, Debug)]
pub(crate) struct Sched {
    pub base: Base,
    /// Deliver FINAL-RA traffic only when nothing else is deliverable.
    pub hold_final: bool,
    /// Honest parties whose inbound traffic is delayed until all others quiesce.
    pub starve: BTreeSet<u16>,
    pub pref: ViewPref,
    pub link_scale: Vec<u64>,
}
impl Sched {
    pub(crate) fn fifo() -> Self {
        Sched {
            base: Base::Fifo,
            hold_final: false,
            starve: BTreeSet::new(),
            pref: ViewPref::None,
            link_scale: vec![],
        }
    }
}

// ---------------------------------------------------------------- adversary
#[derive(Clone, Debug)]
pub(crate) enum Mut {
    /// The private ASKS share sent to these recipients is corrupted.
    FlipShare(BTreeSet<u16>),
    /// The ASKS commitment vector sent to these recipients differs (conflicting commitments).
    SplitCommit(BTreeSet<u16>),
    /// Reconstruction shares are garbage.
    FlipRecon,
    /// Every vote-phase payload sent to these recipients carries `value`.
    ForgeVote(BTreeSet<u16>, u16),
    /// Every prevote-phase payload sent to these recipients carries `value`
    /// (and, when `justify`, a fabricated n-f justification for it).
    ForgePre(BTreeSet<u16>, u16, bool),
    /// Final-RA payloads carry `value`.
    ForgeFinal(u16),
    /// ACS selector payloads sent to these recipients carry this set.
    ForgeSelector(BTreeSet<u16>, BTreeSet<u16>),
    /// The `view` label of a VABA frame is shifted.
    Relabel(i64),
    /// The Byzantine dealer's sharing is NOT a degree-f polynomial: party p's
    /// share is perturbed and the commitment vector is recomputed to match, so
    /// every share still verifies against its commitment.
    NonPoly(u16),
    /// Vote for `value` and, from view 1 on, propose it justified by ONE real vote
    /// (the Byzantine party's own vote for `value` in the previous view).
    Minority(u16),
}
#[derive(Clone, Debug)]
pub(crate) struct Twin {
    /// Recipients served by copy B; everyone else is served by copy A.
    pub group_b: BTreeSet<u16>,
    pub b_order: Vec<u16>,
}
#[derive(Clone, Debug, Default)]
pub(crate) struct ByzSpec {
    pub silent: bool,
    pub crash_after: Option<usize>,
    pub hold_until_view: Option<u64>,
    pub twin: Option<Twin>,
    pub mutations: Vec<Mut>,
    pub replay: u8,
    /// Inject frames for views 1..=flood into every honest party at start.
    pub flood: u64,
    /// Fuzzer: after each frame this party receives, inject a random frame with probability fuzz/16.
    pub fuzz: u8,
}
#[derive(Clone, Debug)]
pub(crate) enum Fault {
    None,
    /// Drop every honest-to-honest packet independently.
    Lossy {
        per_mille: u64,
    },
    /// After `after` steps, honest parties in `side` can no longer exchange packets with the rest.
    Partition {
        side: BTreeSet<u16>,
        after: u64,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct Config {
    pub n: usize,
    pub f: usize,
    pub seed: u64,
    /// Indices externally validated (eventually, by every honest party).
    pub valid: BTreeSet<u16>,
    /// Validation order per party (A copy for Byzantine parties).
    pub orders: BTreeMap<u16, Vec<u16>>,
    pub byz: BTreeMap<u16, ByzSpec>,
    pub sched: Sched,
    pub fault: Fault,
    pub max_steps: usize,
    pub knobs: Knobs,
}
impl Config {
    pub(crate) fn honest(&self) -> Vec<u16> {
        (0..self.n as u16)
            .filter(|i| !self.byz.contains_key(i))
            .collect()
    }
    pub(crate) fn expects_termination(&self) -> bool {
        matches!(self.fault, Fault::None) && self.knobs.chaos.is_none()
    }
}

pub(crate) fn generation(seed: u64) -> Generation {
    Generation {
        invocation: Nat::from_be(&[255; 32]),
        command: seed.to_le_bytes().to_vec(),
        attempt: Nat::new(0),
        generation: Nat::new(1),
        configuration: Nat::new(7),
    }
}
fn coefficients(seed: u64, me: u16, copy: u8, view: u64, f: usize) -> Vec<Vec<Field>> {
    let mut r = Rng::new(mix(&[seed, me as u64, copy as u64, view, 0xC0EF]));
    (0..2)
        .map(|_| {
            (0..=f)
                .map(|_| Field(((r.next() as u128) << 64) | r.next() as u128))
                .collect()
        })
        .collect()
}

// ------------------------------------------------------------------- engine
enum Ev<M> {
    Init {
        who: u16,
        copy: u8,
    },
    Validate {
        who: u16,
        copy: u8,
        j: u16,
    },
    Deliver {
        from: u16,
        to: u16,
        msg: M,
        only: Option<u8>,
    },
}
struct Item<M> {
    id: u64,
    ready: u64,
    ev: Ev<M>,
}
struct Slot<P: Proto> {
    p: P,
    validated: BTreeSet<u16>,
    blocked: Vec<(u16, P::Msg)>,
    seen_view: u64,
}
struct Byz<P: Proto> {
    spec: ByzSpec,
    copies: Vec<Slot<P>>,
    group_b: BTreeSet<u16>,
    sent: usize,
    held: Vec<(u16, P::Msg)>,
    bank: Vec<(u16, P::Msg)>,
    /// Injection budgets: unbounded noise would be a critical branching process, not an adversary.
    noise_left: usize,
}
enum Node<P: Proto> {
    Honest(Slot<P>),
    Byz(Byz<P>),
}
pub(crate) struct Report {
    pub seed: u64,
    pub steps: usize,
    pub quiesced: bool,
    pub decisions: BTreeMap<u16, Option<Vec<u16>>>,
    /// Highest view any honest party entered.
    pub max_view: u64,
    /// Smallest view in which an honest party found n-f matching votes (None: nobody did).
    pub first_match_view: Option<u64>,
    pub dropped: usize,
    pub refused_from_byz: usize,
    pub blocked_max: usize,
    /// Views in which an honest ICG output escaped the paper's literal cover Y (union of honest IGValid at the first output).
    pub literal_cover_escapes: Vec<u64>,
    pub violations: Vec<String>,
}
impl Report {
    pub(crate) fn all_decided(&self) -> bool {
        self.decisions.values().all(|d| d.is_some())
    }
}

pub(crate) struct Sim<P: Proto> {
    cfg: Config,
    nodes: Vec<Node<P>>,
    pool: Vec<Item<P::Msg>>,
    next_id: u64,
    clock: u64,
    rng: Rng,
    steps: usize,
    dropped: usize,
    refused: usize,
    blocked_max: usize,
    violations: Vec<String>,
    /// Per view: union of honest IGValid sets at the instant the first honest ICG output appeared (the cover set Y).
    cover_y: BTreeMap<u64, Set>,
    /// The same instant, but the paper's literal Y := union of honest IGValid.
    cover_y_literal: BTreeMap<u64, Set>,
}
enum Applied<M> {
    Out(Out<M>),
    Blocked,
    Refused(String),
}

impl<P: Proto> Sim<P> {
    pub(crate) fn new(cfg: Config) -> Self {
        let g = generation(cfg.seed);
        let mk = |me: u16| Slot::<P> {
            p: {
                let mut p = P::create(me, cfg.n, cfg.f, &g);
                p.set_knobs(cfg.knobs);
                p
            },
            validated: BTreeSet::new(),
            blocked: vec![],
            seen_view: 0,
        };
        let nodes = (0..cfg.n as u16)
            .map(|i| match cfg.byz.get(&i) {
                None => Node::Honest(mk(i)),
                Some(spec) => {
                    let mut copies = vec![mk(i)];
                    let mut group_b = BTreeSet::new();
                    if let Some(t) = &spec.twin {
                        copies.push(mk(i));
                        group_b = t.group_b.clone();
                    }
                    Node::Byz(Byz {
                        spec: spec.clone(),
                        copies,
                        group_b,
                        sent: 0,
                        held: vec![],
                        bank: vec![],
                        noise_left: 600,
                    })
                }
            })
            .collect();
        let mut s = Sim {
            rng: Rng::new(mix(&[cfg.seed, 0x5CED])),
            cfg,
            nodes,
            pool: vec![],
            next_id: 0,
            clock: 0,
            steps: 0,
            dropped: 0,
            refused: 0,
            blocked_max: 0,
            violations: vec![],
            cover_y: BTreeMap::new(),
            cover_y_literal: BTreeMap::new(),
        };
        s.seed_events();
        s
    }
    fn push(&mut self, ev: Ev<P::Msg>) {
        let scale = match (&ev, self.cfg.sched.base) {
            (Ev::Deliver { from, to, .. }, Base::Latency) => {
                let n = self.cfg.n;
                self.cfg
                    .sched
                    .link_scale
                    .get(*from as usize * n + *to as usize)
                    .copied()
                    .unwrap_or(1)
            }
            (_, Base::Latency) => 4,
            _ => 1,
        };
        let ready = self.clock + 1 + self.rng.next() % scale.max(1);
        self.pool.push(Item {
            id: self.next_id,
            ready,
            ev,
        });
        self.next_id += 1;
    }
    fn seed_events(&mut self) {
        for who in 0..self.cfg.n as u16 {
            let copies = match &self.nodes[who as usize] {
                Node::Honest(_) => 1,
                Node::Byz(b) => b.copies.len() as u8,
            };
            for copy in 0..copies {
                self.push(Ev::Init { who, copy });
                let order = match (&self.cfg.byz.get(&who), copy) {
                    (Some(ByzSpec { twin: Some(t), .. }), 1) => t.b_order.clone(),
                    _ => self.cfg.orders[&who].clone(),
                };
                for j in order {
                    self.push(Ev::Validate { who, copy, j });
                }
            }
        }
        // Future-view flood from Byzantine parties.
        let flood: Vec<(u16, u64)> = self
            .cfg
            .byz
            .iter()
            .filter(|(_, s)| s.flood > 0)
            .map(|(i, s)| (*i, s.flood))
            .collect();
        for (b, views) in flood {
            for v in 1..=views {
                for to in self.cfg.honest() {
                    let m = self.flood_frame(v);
                    if let Some(m) = m {
                        self.push(Ev::Deliver {
                            from: b,
                            to,
                            msg: m,
                            only: None,
                        });
                    }
                }
            }
        }
    }
    fn flood_frame(&self, v: u64) -> Option<P::Msg> {
        // Borrow a real frame of the right wire type from a throwaway instance.
        let mut probe = P::create(0, self.cfg.n, self.cfg.f, &generation(self.cfg.seed));
        let mut out = probe.p_validate(0).ok()?;
        out.extend(
            probe
                .p_dealer(0, &coefficients(0, 0, 0, 0, self.cfg.f))
                .ok()?,
        );
        let (_, mut m) = out
            .into_iter()
            .find(|(_, m)| P::vmsg_mut(&mut m.clone()).is_some() && !P::is_final(m))?;
        P::vmsg_mut(&mut m)?.view = v;
        Some(m)
    }

    fn apply(
        slot: &mut Slot<P>,
        cfg: &Config,
        me: u16,
        copy: u8,
        byz_sender: bool,
        op: impl FnOnce(&mut P) -> Result<Out<P::Msg>>,
    ) -> Applied<P::Msg> {
        // Production applies events to a clone (Journal::append); a refused
        // Byzantine frame must leave honest state untouched, so model that.
        let backup = byz_sender.then(|| slot.p.clone());
        match op(&mut slot.p) {
            Ok(mut out) => {
                let mut rounds = 0;
                loop {
                    let needed = slot.p.p_entropy();
                    if needed.is_empty() {
                        break;
                    }
                    rounds += 1;
                    if rounds > 64 {
                        return Applied::Refused(
                            "RUNAWAY: one event entered more than 64 views".into(),
                        );
                    }
                    for v in needed {
                        let c = coefficients(cfg.seed, me, copy, v, cfg.f);
                        match slot.p.p_dealer(v, &c) {
                            Ok(o) => out.extend(o),
                            Err(e) => return Applied::Refused(format!("dealer: {e}")),
                        }
                    }
                }
                Applied::Out(out)
            }
            Err(e) => {
                if let Some(b) = backup {
                    slot.p = b;
                }
                if e.kind() == ErrorKind::WouldBlock {
                    Applied::Blocked
                } else {
                    Applied::Refused(e.to_string())
                }
            }
        }
    }

    /// Run one op on slot `idx` of node `who`, returning packets to enqueue.
    fn drive(
        &mut self,
        who: u16,
        copy: u8,
        from: Option<u16>,
        op: impl FnOnce(&mut P) -> Result<Out<P::Msg>>,
        blocked_frame: Option<(u16, P::Msg)>,
    ) -> Option<Out<P::Msg>> {
        let byz_sender = from.map_or(false, |f| self.cfg.byz.contains_key(&f));
        let cfg = &self.cfg;
        let slot = match &mut self.nodes[who as usize] {
            Node::Honest(s) => s,
            Node::Byz(b) => &mut b.copies[copy as usize],
        };
        match Self::apply(slot, cfg, who, copy, byz_sender, op) {
            Applied::Out(out) => {
                let v = slot.p.vaba().current;
                let mut again = vec![];
                if v != slot.seen_view {
                    slot.seen_view = v;
                    again = std::mem::take(&mut slot.blocked);
                }
                let honest = matches!(self.nodes[who as usize], Node::Honest(_));
                for (f, m) in again {
                    self.push(Ev::Deliver {
                        from: f,
                        to: who,
                        msg: m,
                        only: Some(copy),
                    });
                    let _ = honest;
                }
                Some(out)
            }
            Applied::Blocked => {
                if let Some(b) = blocked_frame {
                    slot.blocked.push(b);
                    let total: usize = match &self.nodes[who as usize] {
                        Node::Honest(s) => s.blocked.len(),
                        Node::Byz(b) => b.copies.iter().map(|c| c.blocked.len()).sum(),
                    };
                    self.blocked_max = self.blocked_max.max(total);
                }
                None
            }
            Applied::Refused(e) => {
                if byz_sender {
                    self.refused += 1;
                } else {
                    self.violations.push(format!(
                        "step {}: party {who} refused an honest-origin event: {e}",
                        self.steps
                    ));
                }
                None
            }
        }
    }

    fn emit_honest(&mut self, from: u16, out: Out<P::Msg>) {
        for (to, msg) in out {
            self.push(Ev::Deliver {
                from,
                to,
                msg,
                only: None,
            });
        }
    }

    fn mutate(&mut self, spec: &ByzSpec, who: u16, to: u16, msg: &mut P::Msg) {
        let n = self.cfg.n;
        for m in &spec.mutations {
            match m {
                Mut::FlipShare(t) if t.contains(&to) => {
                    if let Some(v) = P::vmsg_mut(msg) {
                        if let Body::Asks(_, a) = &mut v.body {
                            if let asks::Body::PrivateShare(w) = &mut a.body {
                                w[0] = Field(w[0].0 ^ 1);
                            }
                        }
                    }
                }
                Mut::SplitCommit(t) if t.contains(&to) => {
                    if let Some(v) = P::vmsg_mut(msg) {
                        if let Body::Asks(_, a) = &mut v.body {
                            if let asks::Body::Commit(p) = &mut a.body {
                                let b = match p {
                                    PhaseMessage::Init(b)
                                    | PhaseMessage::Echo(b)
                                    | PhaseMessage::Ready(b) => b,
                                };
                                if !b.is_empty() {
                                    b[0] ^= 0x55;
                                }
                            }
                        }
                    }
                }
                Mut::Minority(value) => {
                    if let Some(v) = P::vmsg_mut(msg) {
                        let view = v.view;
                        match &mut v.body {
                            Body::Vote(_, p) => {
                                let b = vote_bytes(*value);
                                *p = match p {
                                    PhaseMessage::Init(_) => PhaseMessage::Init(b),
                                    PhaseMessage::Echo(_) => PhaseMessage::Echo(b),
                                    PhaseMessage::Ready(_) => PhaseMessage::Ready(b),
                                };
                            }
                            Body::Pre(_, p) => {
                                let old = match p {
                                    PhaseMessage::Init(b)
                                    | PhaseMessage::Echo(b)
                                    | PhaseMessage::Ready(b) => b.clone(),
                                };
                                if let Ok(mut prop) = read_proposal(&old, n) {
                                    prop.value = *value;
                                    if view >= 1 {
                                        prop.justification = Votes::from([(who, *value)]);
                                    }
                                    let b = proposal_bytes(&prop);
                                    *p = match p {
                                        PhaseMessage::Init(_) => PhaseMessage::Init(b),
                                        PhaseMessage::Echo(_) => PhaseMessage::Echo(b),
                                        PhaseMessage::Ready(_) => PhaseMessage::Ready(b),
                                    };
                                }
                            }
                            _ => {}
                        }
                    }
                }
                Mut::FlipRecon => {
                    if let Some(v) = P::vmsg_mut(msg) {
                        if let Body::Asks(_, a) = &mut v.body {
                            if let asks::Body::Reconstruct(w) = &mut a.body {
                                w[1] = Field(w[1].0 ^ 3);
                            }
                        }
                    }
                }
                Mut::ForgeVote(t, value) if t.contains(&to) => {
                    if let Some(v) = P::vmsg_mut(msg) {
                        if let Body::Vote(_, p) = &mut v.body {
                            let b = vote_bytes(*value);
                            *p = match p {
                                PhaseMessage::Init(_) => PhaseMessage::Init(b),
                                PhaseMessage::Echo(_) => PhaseMessage::Echo(b),
                                PhaseMessage::Ready(_) => PhaseMessage::Ready(b),
                            };
                        }
                    }
                }
                Mut::ForgePre(t, value, justify) if t.contains(&to) => {
                    if let Some(v) = P::vmsg_mut(msg) {
                        if let Body::Pre(_, p) = &mut v.body {
                            let old = match p {
                                PhaseMessage::Init(b)
                                | PhaseMessage::Echo(b)
                                | PhaseMessage::Ready(b) => b.clone(),
                            };
                            if let Ok(mut prop) = read_proposal(&old, n) {
                                prop.value = *value;
                                if *justify {
                                    prop.justification =
                                        (0..(n - self.cfg.f) as u16).map(|j| (j, *value)).collect();
                                }
                                let b = proposal_bytes(&prop);
                                *p = match p {
                                    PhaseMessage::Init(_) => PhaseMessage::Init(b),
                                    PhaseMessage::Echo(_) => PhaseMessage::Echo(b),
                                    PhaseMessage::Ready(_) => PhaseMessage::Ready(b),
                                };
                            }
                        }
                    }
                }
                Mut::ForgeFinal(value) => {
                    if let Some(v) = P::vmsg_mut(msg) {
                        if let Body::Final(p) = &mut v.body {
                            let b = vote_bytes(*value);
                            *p = match p {
                                PhaseMessage::Init(_) => PhaseMessage::Init(b),
                                PhaseMessage::Echo(_) => PhaseMessage::Echo(b),
                                PhaseMessage::Ready(_) => PhaseMessage::Ready(b),
                            };
                        }
                    }
                }
                Mut::ForgeSelector(t, set) if t.contains(&to) => {
                    if let Some(p) = P::selector_mut(msg) {
                        let b = acs::set_bytes(set);
                        *p = match p {
                            PhaseMessage::Init(_) => PhaseMessage::Init(b),
                            PhaseMessage::Echo(_) => PhaseMessage::Echo(b),
                            PhaseMessage::Ready(_) => PhaseMessage::Ready(b),
                        };
                    }
                }
                Mut::Relabel(d) => {
                    if let Some(v) = P::vmsg_mut(msg) {
                        if !matches!(v.body, Body::Final(_)) {
                            v.view = (v.view as i64 + d).max(0) as u64;
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn nonpoly_batch(&self, spec: &ByzSpec, mut out: Out<P::Msg>) -> Out<P::Msg> {
        for m in &spec.mutations {
            let Mut::NonPoly(p) = m else { continue };
            // Learn the perturbed share per (instance) from the private-share packets.
            let mut perturbed: BTreeMap<[u8; 32], Vec<Field>> = BTreeMap::new();
            let mut original: BTreeMap<[u8; 32], Vec<Field>> = BTreeMap::new();
            for (to, msg) in out.iter_mut() {
                if *to != *p {
                    continue;
                }
                if let Some(v) = P::vmsg_mut(msg) {
                    if let Body::Asks(_, a) = &mut v.body {
                        if let asks::Body::PrivateShare(w) = &mut a.body {
                            original.insert(a.instance, w.clone());
                            w[0] = Field(w[0].0 ^ 1);
                            perturbed.insert(a.instance, w.clone());
                        }
                    }
                }
            }
            for (_, msg) in out.iter_mut() {
                if let Some(v) = P::vmsg_mut(msg) {
                    if let Body::Asks(_, a) = &mut v.body {
                        if let asks::Body::Commit(PhaseMessage::Init(c)) = &mut a.body {
                            if let Some(w) = perturbed.get(&a.instance) {
                                let at = *p as usize * 32;
                                if c.len() >= at + 32 {
                                    assert_eq!(
                                        &c[at..at + 32],
                                        &asks_h(a.instance, *p + 1, &original[&a.instance]),
                                        "harness drift: asks_h no longer mirrors Asks::h"
                                    );
                                    c[at..at + 32].copy_from_slice(&asks_h(a.instance, *p + 1, w));
                                }
                            }
                        }
                    }
                }
            }
        }
        out
    }

    /// Route one outbound packet of Byzantine party `who` produced by `copy`.
    fn byz_emit(&mut self, who: u16, copy: u8, out: Out<P::Msg>) {
        let spec = match &self.nodes[who as usize] {
            Node::Byz(b) => b.spec.clone(),
            _ => unreachable!(),
        };
        let group_b = match &self.nodes[who as usize] {
            Node::Byz(b) => b.group_b.clone(),
            _ => unreachable!(),
        };
        let out = self.nonpoly_batch(&spec, out);
        for (to, mut msg) in out {
            if to == who {
                // A copy talks to itself directly; copies never see each other.
                self.push(Ev::Deliver {
                    from: who,
                    to: who,
                    msg: msg.clone(),
                    only: Some(copy),
                });
                continue;
            }
            if spec.twin.is_some() && (copy == 1) != group_b.contains(&to) {
                continue;
            }
            if spec.silent {
                continue;
            }
            let sent = match &mut self.nodes[who as usize] {
                Node::Byz(b) => {
                    b.sent += 1;
                    b.sent
                }
                _ => unreachable!(),
            };
            if spec.crash_after.map_or(false, |k| sent > k) {
                continue;
            }
            self.mutate(&spec, who, to, &mut msg);
            if let Node::Byz(b) = &mut self.nodes[who as usize] {
                if spec.replay > 0 {
                    b.bank.push((to, msg.clone()));
                }
                if spec.hold_until_view.is_some() {
                    b.held.push((to, msg));
                    continue;
                }
            }
            for _ in 0..=spec.replay.min(1) {
                self.push(Ev::Deliver {
                    from: who,
                    to,
                    msg: msg.clone(),
                    only: None,
                });
            }
        }
    }

    fn release_held(&mut self, force: bool) -> bool {
        let max_view = self
            .cfg
            .honest()
            .iter()
            .map(|i| match &self.nodes[*i as usize] {
                Node::Honest(s) => s.p.vaba().current,
                _ => 0,
            })
            .max()
            .unwrap_or(0);
        let mut released = vec![];
        for (i, node) in self.nodes.iter_mut().enumerate() {
            if let Node::Byz(b) = node {
                if let Some(v) = b.spec.hold_until_view {
                    if (force || max_view >= v) && !b.held.is_empty() {
                        for (to, m) in std::mem::take(&mut b.held) {
                            released.push((i as u16, to, m));
                        }
                    }
                }
            }
        }
        let any = !released.is_empty();
        for (from, to, msg) in released {
            self.push(Ev::Deliver {
                from,
                to,
                msg,
                only: None,
            });
        }
        any
    }

    fn pick(&mut self) -> usize {
        let s = self.cfg.sched.clone();
        let to_of = |ev: &Ev<P::Msg>| match ev {
            Ev::Init { who, .. } | Ev::Validate { who, .. } => *who,
            Ev::Deliver { to, .. } => *to,
        };
        let mut cand: Vec<usize> = (0..self.pool.len()).collect();
        let keep: Vec<usize> = cand
            .iter()
            .copied()
            .filter(|i| !s.starve.contains(&to_of(&self.pool[*i].ev)))
            .collect();
        if !keep.is_empty() {
            cand = keep;
        }
        if s.hold_final {
            let keep: Vec<usize> = cand
                .iter()
                .copied()
                .filter(
                    |i| !matches!(&self.pool[*i].ev, Ev::Deliver { msg, .. } if P::is_final(msg)),
                )
                .collect();
            if !keep.is_empty() {
                cand = keep;
            }
        }
        if s.pref != ViewPref::None {
            let key = |i: &usize| match &self.pool[*i].ev {
                Ev::Deliver { msg, .. } => P::view_of(msg).map_or(0, |v| v + 1),
                _ => 0,
            };
            let target = match s.pref {
                ViewPref::High => cand.iter().map(key).max(),
                _ => cand.iter().map(key).min(),
            };
            if let Some(t) = target {
                cand.retain(|i| key(i) == t);
            }
        }
        match s.base {
            Base::Fifo => *cand.iter().min_by_key(|i| self.pool[**i].id).unwrap(),
            Base::Lifo => *cand.iter().max_by_key(|i| self.pool[**i].id).unwrap(),
            Base::Random => cand[self.rng.below(cand.len())],
            Base::Latency => *cand
                .iter()
                .min_by_key(|i| (self.pool[**i].ready, self.pool[**i].id))
                .unwrap(),
        }
    }

    fn drop_packet(&mut self, from: u16, to: u16) -> bool {
        if self.cfg.byz.contains_key(&from) || self.cfg.byz.contains_key(&to) {
            return false;
        }
        match self.cfg.fault.clone() {
            Fault::None => false,
            Fault::Lossy { per_mille } => self.rng.next() % 1000 < per_mille,
            Fault::Partition { side, after } => {
                self.steps as u64 >= after && side.contains(&from) != side.contains(&to)
            }
        }
    }

    pub(crate) fn run(mut self) -> Report {
        let mut quiesced = false;
        while self.steps < self.cfg.max_steps {
            if self.pool.is_empty() {
                if self.release_held(true) {
                    continue;
                }
                quiesced = true;
                break;
            }
            if self.steps % 32 == 0 {
                self.release_held(false);
            }
            let idx = self.pick();
            let item = self.pool.swap_remove(idx);
            self.clock = self.clock.max(item.ready);
            self.steps += 1;
            match item.ev {
                Ev::Init { who, copy } => {
                    let out = self.drive(who, copy, None, |p: &mut P| Ok(init_noop::<P>(p)), None);
                    self.route(who, copy, out);
                }
                Ev::Validate { who, copy, j } => {
                    let out = self.drive(who, copy, None, |p| p.p_validate(j), None);
                    match &mut self.nodes[who as usize] {
                        Node::Honest(s) => {
                            s.validated.insert(j);
                        }
                        Node::Byz(b) => {
                            b.copies[copy as usize].validated.insert(j);
                        }
                    }
                    self.route(who, copy, out);
                }
                Ev::Deliver {
                    from,
                    to,
                    msg,
                    only,
                } => {
                    if self.drop_packet(from, to) {
                        self.dropped += 1;
                        continue;
                    }
                    let copies = match &self.nodes[to as usize] {
                        Node::Honest(_) => 1,
                        Node::Byz(b) => b.copies.len() as u8,
                    };
                    if let Node::Byz(b) = &mut self.nodes[to as usize] {
                        if b.spec.replay > 0 && from != to {
                            b.bank.push((from, msg.clone()));
                        }
                    }
                    for copy in 0..copies {
                        if only.map_or(false, |c| c != copy) {
                            continue;
                        }
                        let m = msg.clone();
                        let out = self.drive(
                            to,
                            copy,
                            Some(from),
                            move |p| p.p_receive(from, m),
                            Some((from, msg.clone())),
                        );
                        self.route(to, copy, out);
                    }
                    self.replay_noise();
                    self.fuzz_noise();
                }
            }
            self.quick_checks();
            if !self.violations.is_empty() {
                break;
            }
        }
        self.finish(quiesced)
    }

    fn fuzz_noise(&mut self) {
        let fuzzers: Vec<(u16, u8)> = self
            .cfg
            .byz
            .iter()
            .filter(|(_, s)| s.fuzz > 0 && !s.silent)
            .map(|(i, s)| (*i, s.fuzz))
            .collect();
        for (b, rate) in fuzzers {
            if !self.rng.chance(rate as u64, 16) {
                continue;
            }
            match &mut self.nodes[b as usize] {
                Node::Byz(x) if x.noise_left > 0 => x.noise_left -= 1,
                _ => continue,
            }
            let honest = self.cfg.honest();
            if honest.is_empty() {
                continue;
            }
            let to = honest[self.rng.below(honest.len())];
            let msg = match &self.nodes[to as usize] {
                Node::Honest(s) => s.p.fuzz_msg(&mut self.rng),
                _ => continue,
            };
            self.push(Ev::Deliver {
                from: b,
                to,
                msg,
                only: None,
            });
        }
    }
    fn replay_noise(&mut self) {
        // Re-inject banked traffic: own old packets, and honest packets re-sent
        // under the Byzantine sender's authenticated identity to random parties.
        let n = self.cfg.n;
        let byz: Vec<u16> = self.cfg.byz.keys().copied().collect();
        for b in byz {
            let pick = match &self.nodes[b as usize] {
                Node::Byz(x) if x.spec.replay > 0 && !x.bank.is_empty() => {
                    Some((x.spec.replay, x.bank.len()))
                }
                _ => None,
            };
            if let Some((rate, len)) = pick {
                if self.rng.chance(rate as u64, 8) {
                    match &mut self.nodes[b as usize] {
                        Node::Byz(x) if x.noise_left > 0 => x.noise_left -= 1,
                        _ => continue,
                    }
                    let k = self.rng.below(len);
                    let (to, msg) = match &self.nodes[b as usize] {
                        Node::Byz(x) => x.bank[k].clone(),
                        _ => unreachable!(),
                    };
                    let to = if self.rng.chance(1, 2) {
                        to
                    } else {
                        self.rng.below(n) as u16
                    };
                    if to != b {
                        self.push(Ev::Deliver {
                            from: b,
                            to,
                            msg,
                            only: None,
                        });
                    }
                }
            }
        }
    }

    fn route(&mut self, who: u16, copy: u8, out: Option<Out<P::Msg>>) {
        if let Some(out) = out {
            match &self.nodes[who as usize] {
                Node::Honest(_) => self.emit_honest(who, out),
                Node::Byz(_) => self.byz_emit(who, copy, out),
            }
        }
    }

    fn honest_vabas(&self) -> Vec<(u16, &Vaba)> {
        self.cfg
            .honest()
            .into_iter()
            .map(|i| match &self.nodes[i as usize] {
                Node::Honest(s) => (i, s.p.vaba()),
                _ => unreachable!(),
            })
            .collect()
    }
    fn honest_slots(&self) -> Vec<(u16, &Slot<P>)> {
        self.cfg
            .honest()
            .into_iter()
            .map(|i| match &self.nodes[i as usize] {
                Node::Honest(s) => (i, s),
                _ => unreachable!(),
            })
            .collect()
    }

    /// Checks cheap enough for every step.
    fn quick_checks(&mut self) {
        let slots = self.honest_slots();
        let mut seen: Option<(u16, Vec<u16>)> = None;
        let mut bad = vec![];
        for (i, s) in &slots {
            if let Some(d) = s.p.decision() {
                match &seen {
                    None => seen = Some((*i, d)),
                    Some((j, e)) if *e != d => bad.push(format!(
                        "AGREEMENT: party {j} decided {e:?} but party {i} decided {d:?}"
                    )),
                    _ => {}
                }
            }
        }
        let mut input: Option<(u16, Vec<u8>)> = None;
        for (i, s) in &slots {
            if let Some(e) = &s.p.vaba().final_ra.echo_sent {
                match &input {
                    None => input = Some((*i, e.clone())),
                    Some((j, x)) if x != e => bad.push(format!(
                        "RA-INPUT (Lemma 5.3): honest {j} input {x:?} and honest {i} input {e:?}"
                    )),
                    _ => {}
                }
            }
        }
        self.violations.extend(bad);
        self.snapshot_cover();
        if self.steps % 256 == 0 {
            let v = self.deep_checks();
            self.violations.extend(v);
        }
    }

    fn snapshot_cover(&mut self) {
        let mut fresh: Vec<(u64, Set, Set)> = vec![];
        {
            let hs = self.honest_vabas();
            let views: BTreeSet<u64> = hs
                .iter()
                .flat_map(|(_, v)| v.views.keys().copied())
                .collect();
            for v in views {
                if self.cover_y.contains_key(&v) {
                    continue;
                }
                if hs
                    .iter()
                    .any(|(_, h)| h.views.get(&v).map_or(false, |s| s.cover.output.is_some()))
                {
                    let mut y = Set::new();
                    let mut lit = Set::new();
                    for (_, h) in &hs {
                        if let Some(s) = h.views.get(&v) {
                            lit.extend(s.cover.ig_valid.iter().copied());
                            y.extend(s.locally_validated.iter().copied());
                        }
                    }
                    fresh.push((v, y, lit));
                }
            }
        }
        for (v, y, lit) in fresh {
            self.cover_y.insert(v, y);
            self.cover_y_literal.insert(v, lit);
        }
    }

    /// Cross-party structural invariants of the sub-protocols.
    fn deep_checks(&self) -> Vec<String> {
        let (n, f) = (self.cfg.n, self.cfg.f);
        let hs = self.honest_vabas();
        let mut bad = vec![];
        let views: BTreeSet<u64> = hs
            .iter()
            .flat_map(|(_, v)| v.views.keys().copied())
            .collect();
        // Union of vote-RBC outputs per view, and the lock it implies.
        let mut lock: BTreeMap<u64, u16> = BTreeMap::new();
        for v in &views {
            let mut votes: BTreeMap<u16, u16> = BTreeMap::new();
            for d in 0..n {
                let mut pre_out: Option<(u16, &Vec<u8>)> = None;
                let mut vote_out: Option<(u16, &Vec<u8>)> = None;
                let mut commits: Option<(u16, Vec<[u8; 32]>)> = None;
                let mut key: Option<(u16, [u8; 32])> = None;
                for (i, h) in &hs {
                    let Some(s) = h.views.get(v) else { continue };
                    if let Some(o) = &s.pre[d].output {
                        match pre_out {
                            Some((j, x)) if x != o => bad.push(format!(
                                "PREVOTE RBC (view {v} dealer {d}): honest {j} and {i} output different payloads"
                            )),
                            None => pre_out = Some((*i, o)),
                            _ => {}
                        }
                    }
                    if let Some(o) = &s.votes[d].output {
                        match vote_out {
                            Some((j, x)) if x != o => bad.push(format!(
                                "VOTE RBC (view {v} dealer {d}): honest {j} and {i} output different payloads"
                            )),
                            None => {
                                vote_out = Some((*i, o));
                                if let Ok(x) = read_vote(o, n) {
                                    votes.insert(d as u16, x);
                                }
                            }
                            _ => {}
                        }
                    }
                    if let Some(sh) = &s.asks[d].sharing {
                        match &commits {
                            Some((j, c)) if *c != sh.commitments => bad.push(format!(
                                "ASKS commitment (view {v} dealer {d}): honest {j} and {i} froze different commitment vectors"
                            )),
                            None => commits = Some((*i, sh.commitments.clone())),
                            _ => {}
                        }
                    }
                    if let Some(k) = s.asks[d].key {
                        if !self.cfg.byz.contains_key(&(d as u16)) {
                            let want = s.asks[d]
                                .dealer_key(&coefficients(self.cfg.seed, d as u16, 0, *v, f))
                                .unwrap();
                            if k != want {
                                bad.push(format!(
                                    "ASKS VALIDITY (view {v}): honest {i} reconstructed {k:02x?} for honest dealer {d}, who shared {want:02x?}"
                                ));
                            }
                        }
                        match key {
                            Some((j, x)) if x != k => bad.push(format!(
                                "ASKS key (view {v} dealer {d}): honest {j} and {i} reconstructed different keys"
                            )),
                            None => key = Some((*i, k)),
                            _ => {}
                        }
                    }
                }
            }
            // Binding core: any two honest ICG outputs share at least n-f indices.
            let outs: Vec<(u16, &Set)> = hs
                .iter()
                .filter_map(|(i, h)| h.views.get(v)?.cover.output.as_ref().map(|o| (*i, o)))
                .collect();
            if !outs.is_empty() {
                let mut core = outs[0].1.clone();
                for (_, o) in &outs {
                    core = core.intersection(o).copied().collect();
                }
                if core.len() < n - f {
                    bad.push(format!(
                        "BINDING CORE (view {v}): intersection of {} honest ICG outputs has {} < n-f members",
                        outs.len(),
                        core.len()
                    ));
                }
            }
            // Binding cover: every honest output lies inside the cover set fixed at the first output.
            if let Some(y) = self.cover_y.get(v) {
                for (i, o) in &outs {
                    if !o.is_subset(y) {
                        bad.push(format!(
                            "BINDING COVER (view {v}): honest {i} ICG output {o:?} escapes the cover set {y:?} (union of honest locally validated sets) fixed at the first honest output"
                        ));
                    }
                }
            }
            // Tally entries agree with the unique vote-RBC output.
            for (i, h) in &hs {
                if let Some(s) = h.views.get(v) {
                    for (j, x) in &s.tally {
                        if votes.get(j) != Some(x) && votes.contains_key(j) {
                            bad.push(format!(
                                "TALLY (view {v}): honest {i} counts vote {j}->{x} against RBC output {:?}",
                                votes.get(j)
                            ));
                        }
                    }
                }
            }
            let mut counts: BTreeMap<u16, usize> = BTreeMap::new();
            for x in votes.values() {
                *counts.entry(*x).or_default() += 1;
            }
            if let Some((k, _)) = counts.iter().find(|(_, c)| **c >= n - f) {
                lock.insert(*v, *k);
            }
        }
        // Lemma 5.2: n-f matching vote outputs in view v lock every later view.
        for (v, k) in &lock {
            for (i, h) in &hs {
                for (u, s) in h.views.range(v + 1..) {
                    for (j, x) in &s.tally {
                        if x != k {
                            bad.push(format!(
                                "LOCK (Lemma 5.2): value {k} had n-f matching votes in view {v}, but honest {i} counts vote {j}->{x} in view {u}"
                            ));
                        }
                    }
                    for j in &s.locally_validated {
                        if s.proposals[j].value != *k {
                            bad.push(format!(
                                "LOCK (Lemma 5.2): value {k} locked in view {v}, but honest {i} validated a view-{u} prevote of {j} for {}",
                                s.proposals[j].value
                            ));
                        }
                    }
                }
                if let Some(o) = h.output {
                    if o != *k {
                        bad.push(format!(
                            "LOCK: value {k} locked in view {v} but honest {i} output {o}"
                        ));
                    }
                }
            }
        }
        // Selector RBC agreement (ACS).
        let sels: Vec<(u16, Vec<Option<Vec<u8>>>)> = self
            .honest_slots()
            .iter()
            .map(|(i, s)| (*i, s.p.selector_outputs()))
            .collect();
        for d in 0..n {
            let mut first: Option<(u16, &Vec<u8>)> = None;
            for (i, o) in &sels {
                if let Some(Some(b)) = o.get(d) {
                    match first {
                        Some((j, x)) if x != b => bad.push(format!(
                            "SELECTOR RBC {d}: honest {j} and {i} output different sets"
                        )),
                        None => first = Some((*i, b)),
                        _ => {}
                    }
                }
            }
        }
        bad
    }

    fn finish(mut self, quiesced: bool) -> Report {
        let mut v = self.deep_checks();
        self.violations.append(&mut v);
        let n = self.cfg.n;
        let f = self.cfg.f;
        let mut decisions = BTreeMap::new();
        let mut max_view = 0;
        let mut mviews: Vec<u64> = vec![];
        for (i, s) in self.honest_slots() {
            if let Some(a) = s.p.vaba().stop_after {
                mviews.push(a - 1);
            }
            let d = s.p.decision();
            max_view = max_view.max(s.p.vaba().current);
            decisions.insert(i, d);
        }
        // Validity / quality of decisions.
        let valid = self.cfg.valid.clone();
        let mut bad = vec![];
        for (i, s) in self.honest_slots() {
            if let Some(d) = s.p.decision() {
                if s.p.selector_outputs().is_empty() {
                    // plain VABA: the index is externally valid
                    if !d.iter().all(|k| valid.contains(k)) {
                        bad.push(format!(
                            "VABA VALIDITY: honest {i} output {d:?} outside valid set {valid:?}"
                        ));
                    }
                } else {
                    // ACS: at least n-f indices, each externally valid at the decider
                    if d.len() < n - f || !d.iter().all(|k| s.validated.contains(k)) {
                        bad.push(format!(
                            "ACS VALIDITY: honest {i} output {d:?} (need >= {} indices, all validated {:?})",
                            n - f,
                            s.validated
                        ));
                    }
                }
            }
        }
        self.violations.extend(bad);
        if self.cfg.expects_termination() && quiesced && !decisions.values().all(|d| d.is_some()) {
            self.violations.push(format!(
                "TERMINATION: quiescent with undecided honest parties {decisions:?}"
            ));
        }
        if self.cfg.expects_termination() && !quiesced {
            self.violations.push(format!(
                "TERMINATION: step budget {} exhausted before quiescence",
                self.cfg.max_steps
            ));
        }
        let mut esc = vec![];
        for (v, lit) in &self.cover_y_literal {
            let escaped = self.honest_vabas().iter().any(|(_, h)| {
                h.views
                    .get(v)
                    .and_then(|s| s.cover.output.as_ref())
                    .map_or(false, |o| !o.is_subset(lit))
            });
            if escaped {
                esc.push(*v);
            }
        }
        Report {
            seed: self.cfg.seed,
            steps: self.steps,
            quiesced,
            decisions,
            max_view,
            first_match_view: mviews.iter().min().copied(),
            dropped: self.dropped,
            refused_from_byz: self.refused,
            blocked_max: self.blocked_max,
            literal_cover_escapes: esc,
            violations: self.violations,
        }
    }
}
/// Mirror of `Asks::h`, used to build commitments to a perturbed share.
fn asks_h(instance: [u8; 32], index: u16, words: &[Field]) -> [u8; 32] {
    let mut b = b"DREGG.ASKS.H.V2".to_vec();
    b.extend(instance);
    b.extend(index.to_le_bytes());
    for w in words {
        b.extend(w.0.to_le_bytes());
    }
    crate::custody::hash(&b)
}
fn init_noop<P: Proto>(_: &mut P) -> Out<P::Msg> {
    vec![]
}

// ----------------------------------------------------------- configurations
fn subset(r: &mut Rng, universe: &[u16], k: usize) -> BTreeSet<u16> {
    let mut v = universe.to_vec();
    r.shuffle(&mut v);
    v.into_iter().take(k).collect()
}

/// Derive a complete adversarial configuration from one seed.
pub(crate) fn gen_config(seed: u64, f: usize, max_steps: usize) -> Config {
    let n = 3 * f + 1;
    let mut r = Rng::new(mix(&[seed, f as u64, 0xC0F1]));
    let all: Vec<u16> = (0..n as u16).collect();
    let nbyz = if r.chance(1, 8) { r.below(f + 1) } else { f };
    let byz_ids = subset(&mut r, &all, nbyz);
    let honest: Vec<u16> = all
        .iter()
        .copied()
        .filter(|i| !byz_ids.contains(i))
        .collect();
    let mut valid: BTreeSet<u16> = honest.iter().copied().collect();
    for b in &byz_ids {
        if r.chance(1, 2) {
            valid.insert(*b);
        }
    }
    let valid_vec: Vec<u16> = valid.iter().copied().collect();
    let mut orders = BTreeMap::new();
    for i in &all {
        let mut o = valid_vec.clone();
        r.shuffle(&mut o);
        orders.insert(*i, o);
    }
    let mut byz = BTreeMap::new();
    for b in &byz_ids {
        let mut spec = ByzSpec::default();
        let others: Vec<u16> = all.iter().copied().filter(|i| i != b).collect();
        match r.below(8) {
            0 => spec.silent = true,
            1 => spec.crash_after = Some(r.below(400)),
            _ => {}
        }
        if r.chance(1, 3) {
            spec.hold_until_view = Some(1 + r.below(2) as u64);
        }
        if r.chance(1, 2) {
            let k = 1 + r.below(others.len());
            let mut order = all.clone();
            r.shuffle(&mut order);
            // Copy B may validate an index honest parties never will.
            let mut b_order = if r.chance(1, 2) {
                order.clone()
            } else {
                valid_vec.clone()
            };
            r.shuffle(&mut b_order);
            spec.twin = Some(Twin {
                group_b: subset(&mut r, &others, k),
                b_order,
            });
        }
        let nm = r.below(4);
        for _ in 0..nm {
            let to = {
                let k = 1 + r.below(others.len());
                subset(&mut r, &others, k)
            };
            let value = r.below(n) as u16;
            spec.mutations.push(match r.below(11) {
                0 => Mut::FlipShare(to),
                1 => Mut::SplitCommit(to),
                2 => Mut::FlipRecon,
                3 => Mut::ForgeVote(to, value),
                4 => Mut::ForgePre(to, value, r.chance(1, 2)),
                5 => Mut::ForgeFinal(value),
                6 => Mut::ForgeSelector(to, {
                    let k = 1 + r.below(n);
                    subset(&mut r, &all, k)
                }),
                8 => Mut::NonPoly(others[r.below(others.len())]),
                9 | 10 => Mut::Minority(value),
                _ => Mut::Relabel(if r.chance(1, 2) { 1 } else { -1 }),
            });
        }
        if r.chance(1, 4) {
            spec.replay = 1 + r.below(3) as u8;
        }
        if r.chance(1, 8) {
            spec.flood = 1 + r.below(3) as u64;
        }
        if r.chance(1, 3) {
            spec.fuzz = 1 + r.below(8) as u8;
        }
        byz.insert(*b, spec);
    }
    let base = match r.below(4) {
        0 => Base::Fifo,
        1 => Base::Lifo,
        2 => Base::Random,
        _ => Base::Latency,
    };
    let starve = if !honest.is_empty() && r.chance(1, 3) {
        {
            let k = 1 + r.below(f.max(1));
            subset(&mut r, &honest, k)
        }
    } else {
        BTreeSet::new()
    };
    let link_scale = (0..n * n)
        .map(|_| [1u64, 4, 64, 4096][r.below(4)])
        .collect();
    let sched = Sched {
        base,
        hold_final: r.chance(1, 3),
        starve,
        pref: [ViewPref::None, ViewPref::High, ViewPref::Low][r.below(3)],
        link_scale,
    };
    Config {
        n,
        f,
        seed,
        valid,
        orders,
        byz,
        sched,
        fault: Fault::None,
        max_steps,
        knobs: Knobs::default(),
    }
}

/// Same adversary, but the leader choice is partly or wholly adversarial.
pub(crate) fn gen_chaos(seed: u64, f: usize, max_steps: usize, per_mille: u64) -> Config {
    let mut c = gen_config(seed, f, max_steps);
    c.knobs.chaos = Some((mix(&[seed, 0xCA05]), per_mille));
    c
}

/// Same adversary, but the channel premise is violated.
pub(crate) fn gen_faulty(seed: u64, f: usize, max_steps: usize) -> Config {
    let mut c = gen_config(seed, f, max_steps);
    let mut r = Rng::new(mix(&[seed, 0xFA17]));
    let honest = c.honest();
    c.fault = if r.chance(1, 2) {
        Fault::Lossy {
            per_mille: 20 + r.below(400) as u64,
        }
    } else {
        Fault::Partition {
            side: {
                let k = 1 + r.below(honest.len().max(2) - 1);
                subset(&mut r, &honest, k)
            },
            after: r.below(3000) as u64,
        }
    };
    c
}

/// A panic inside protocol code is a remotely triggerable crash when a
/// Byzantine frame caused it: report it as a violation with the seed.
fn guarded(seed: u64, f: impl FnOnce() -> Report) -> Report {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(r) => r,
        Err(e) => {
            let msg = e
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default();
            Report {
                seed,
                steps: 0,
                quiesced: false,
                decisions: BTreeMap::new(),
                max_view: 0,
                first_match_view: None,
                dropped: 0,
                refused_from_byz: 0,
                blocked_max: 0,
                literal_cover_escapes: vec![],
                violations: vec![format!("PANIC in protocol code: {msg}")],
            }
        }
    }
}
pub(crate) fn run_vaba(cfg: Config) -> Report {
    let seed = cfg.seed;
    guarded(seed, || Sim::<Vaba>::new(cfg).run())
}
pub(crate) fn run_acs(cfg: Config) -> Report {
    let seed = cfg.seed;
    guarded(seed, || Sim::<Acs>::new(cfg).run())
}

#[derive(Default, Debug)]
pub(crate) struct Stats {
    pub runs: usize,
    pub decided: usize,
    pub view_changed: usize,
    pub view0_failed: usize,
    pub match_view_hist: BTreeMap<u64, usize>,
    pub view_change_seeds: Vec<(u64, u64)>,
    pub literal_cover_escape_seeds: Vec<u64>,
    pub deepest: u64,
    pub steps: usize,
    pub refused_from_byz: usize,
    pub dropped: usize,
    pub blocked_max: usize,
}
impl Stats {
    pub(crate) fn add(&mut self, r: &Report) {
        self.runs += 1;
        self.decided += r.all_decided() as usize;
        self.view_changed += (r.max_view >= 1) as usize;
        if !r.literal_cover_escapes.is_empty() {
            self.literal_cover_escape_seeds.push(r.seed);
        }
        self.view0_failed += r.first_match_view.map_or(0, |v| (v >= 1) as usize);
        if let Some(v) = r.first_match_view {
            if v >= 1 {
                self.view_change_seeds.push((r.seed, v));
            }
            *self.match_view_hist.entry(v).or_default() += 1;
        }
        self.deepest = self.deepest.max(r.max_view);
        self.steps += r.steps;
        self.refused_from_byz += r.refused_from_byz;
        self.dropped += r.dropped;
        self.blocked_max = self.blocked_max.max(r.blocked_max);
    }
}
pub(crate) fn seeds() -> std::ops::Range<u64> {
    let n: u64 = std::env::var("BYZ_SEEDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(12);
    let from: u64 = std::env::var("BYZ_FROM")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    from..from + n
}
/// n=7 runs are ~10x dearer: a third of the seed budget.
pub(crate) fn seeds7() -> std::ops::Range<u64> {
    let r = seeds();
    r.start..r.start + ((r.end - r.start) / 3).max(2)
}
pub(crate) fn expect_clean(cfg: &Config, r: &Report) {
    assert!(
        r.violations.is_empty(),
        "seed {} (n={}) violated: {:#?}\nconfig: {:#?}\nsteps {} quiesced {} decisions {:?}",
        cfg.seed,
        cfg.n,
        r.violations,
        cfg,
        r.steps,
        r.quiesced,
        r.decisions
    );
}

#[cfg(test)]
mod sweeps {
    use super::*;

    fn sweep<F: Fn(Config) -> Report>(f: usize, faulty: bool, run: F, label: &str) -> Stats {
        let mut st = Stats::default();
        for seed in if f == 2 { seeds7() } else { seeds() } {
            let cfg = if faulty {
                gen_faulty(seed, f, 400_000)
            } else {
                gen_config(seed, f, 2_000_000)
            };
            let rep = run(cfg.clone());
            expect_clean(&cfg, &rep);
            st.add(&rep);
        }
        eprintln!("[byz-sweep {label}] {st:?}");
        st
    }
    fn chaos_sweep<F: Fn(Config) -> Report>(f: usize, pm: u64, run: F, label: &str) -> Stats {
        let mut st = Stats::default();
        for seed in if f == 2 { seeds7() } else { seeds() } {
            let cfg = gen_chaos(seed, f, 600_000, pm);
            let rep = run(cfg.clone());
            expect_clean(&cfg, &rep);
            st.add(&rep);
        }
        eprintln!("[byz-chaos {label} {pm}pm] {st:?}");
        st
    }
    #[test]
    fn byz_vaba_n4_adversarial_leader_half() {
        let st = chaos_sweep(1, 500, run_vaba, "vaba n4");
        assert!(
            st.view0_failed > 0,
            "no view change executed: the sweep is not exercising the view-change path"
        );
    }
    #[test]
    fn byz_vaba_n4_adversarial_leader_full() {
        let st = chaos_sweep(1, 1000, run_vaba, "vaba n4");
        assert!(
            st.view0_failed > 0,
            "no view change executed: the sweep is not exercising the view-change path"
        );
    }
    #[test]
    fn byz_vaba_n4_adversarial_leader_rotation() {
        let st = chaos_sweep(1, 2000, run_vaba, "vaba n4");
        assert!(
            st.view0_failed > 0,
            "no view change executed: the sweep is not exercising the view-change path"
        );
    }
    #[test]
    fn byz_acs_n4_adversarial_leader_half() {
        let st = chaos_sweep(1, 500, run_acs, "acs n4");
        assert!(
            st.view0_failed > 0,
            "no view change executed: the sweep is not exercising the view-change path"
        );
    }
    #[test]
    fn byz_vaba_n7_adversarial_leader_half() {
        let st = chaos_sweep(2, 500, run_vaba, "vaba n7");
        assert!(
            st.view0_failed > 0,
            "no view change executed: the sweep is not exercising the view-change path"
        );
    }
    #[test]
    fn byz_vaba_n4_f1_sweep() {
        let st = sweep(1, false, run_vaba, "vaba n4");
        assert_eq!(st.decided, st.runs);
    }
    #[test]
    fn byz_acs_n4_f1_sweep() {
        let st = sweep(1, false, run_acs, "acs n4");
        assert_eq!(st.decided, st.runs);
    }
    #[test]
    fn byz_vaba_n7_f2_sweep() {
        let st = sweep(2, false, run_vaba, "vaba n7");
        assert_eq!(st.decided, st.runs);
    }
    #[test]
    fn byz_acs_n7_f2_sweep() {
        let st = sweep(2, false, run_acs, "acs n7");
        assert_eq!(st.decided, st.runs);
    }
    #[test]
    fn byz_vaba_n4_safety_without_liveness() {
        sweep(1, true, run_vaba, "vaba n4 faulty");
    }
    #[test]
    fn byz_acs_n4_safety_without_liveness() {
        sweep(1, true, run_acs, "acs n4 faulty");
    }
    #[test]
    fn byz_vaba_n7_safety_without_liveness() {
        sweep(2, true, run_vaba, "vaba n7 faulty");
    }
}

/// Hand-built scenario: the validated set and the Byzantine parties are given,
/// validation orders are seeded.
pub(crate) fn scenario(
    f: usize,
    seed: u64,
    valid: &[u16],
    byz: Vec<(u16, ByzSpec)>,
    sched: Sched,
) -> Config {
    let n = 3 * f + 1;
    let mut orders = BTreeMap::new();
    for i in 0..n as u16 {
        let mut o = valid.to_vec();
        Rng::new(mix(&[seed, i as u64, 0x0DE5])).shuffle(&mut o);
        orders.insert(i, o);
    }
    Config {
        n,
        f,
        seed,
        valid: valid.iter().copied().collect(),
        orders,
        byz: byz.into_iter().collect(),
        sched,
        fault: Fault::None,
        max_steps: 300_000,
        knobs: Knobs::default(),
    }
}
pub(crate) fn sched_for(seed: u64, n: usize) -> Sched {
    let mut r = Rng::new(mix(&[seed, 0x5C4E]));
    let base = [Base::Fifo, Base::Lifo, Base::Random, Base::Latency][(seed % 4) as usize];
    Sched {
        base,
        hold_final: false,
        starve: BTreeSet::new(),
        pref: ViewPref::None,
        link_scale: (0..n * n).map(|_| [1u64, 4, 64][r.below(3)]).collect(),
    }
}
/// Everything except TERMINATION: what a literal-predicate run may still be held to.
pub(crate) fn safety_violations(r: &Report) -> Vec<&String> {
    r.violations
        .iter()
        .filter(|v| !v.starts_with("TERMINATION"))
        .collect()
}

#[cfg(test)]
mod printed_predicates {
    use super::*;

    /// Alg6 L11 printed: `P_j subset Valid_i`. Implemented: `P_j subset Shared_i`.
    /// Party 0 completes its ASKS dealing like an honest dealer but its index is
    /// not externally valid (in ACS: its selector never validates). Honest
    /// proposers take the f+1 lowest completed dealers, so P_j names party 0.
    #[test]
    fn availability_printed_valid_stalls_where_shared_decides() {
        let mut stalled_printed = 0;
        let mut decided_impl = 0;
        let total = 48;
        for seed in 0..total {
            let cfg = scenario(
                1,
                seed,
                &[1, 2, 3],
                vec![(0, ByzSpec::default())],
                sched_for(seed, 4),
            );
            let imp = run_vaba(cfg.clone());
            expect_clean(&cfg, &imp);
            assert!(imp.all_decided());
            decided_impl += 1;
            for d in imp.decisions.values() {
                assert!(d.as_ref().unwrap().iter().all(|k| [1, 2, 3].contains(k)));
            }
            let mut lit = cfg.clone();
            lit.knobs.printed_availability = true;
            let rep = run_vaba(lit.clone());
            assert!(
                safety_violations(&rep).is_empty(),
                "literal predicate must still be SAFE: {:?}",
                rep.violations
            );
            if !rep.all_decided() {
                assert!(
                    rep.quiesced,
                    "seed {seed}: a stall is quiescence, not a budget"
                );
                stalled_printed += 1;
            }
        }
        eprintln!("[printed-availability] impl decided {decided_impl}/{total}; printed-literal stalled {stalled_printed}/{total}");
        assert_eq!(decided_impl, total);
        assert!(
            stalled_printed > 0,
            "the printed predicate was expected to lose termination in at least one schedule"
        );
    }

    /// Alg5 L18 printed: `vote_j in IGValid_i`, the vote read as a broadcaster
    /// index. Party 0 is externally valid and every honest party prevotes for it
    /// first, but party 0 never speaks in the VABA, so it is never in IGValid.
    #[test]
    fn vote_membership_printed_index_stalls_where_value_membership_decides() {
        let silent = ByzSpec {
            silent: true,
            ..ByzSpec::default()
        };
        let total = 48;
        let mut stalled_printed = 0;
        for seed in 0..total {
            // FIFO delivery keeps each party's own validation order, so the
            // first-validated value really is party 0 everywhere.
            let mut cfg = scenario(
                1,
                seed,
                &[0, 1, 2, 3],
                vec![(0, silent.clone())],
                Sched::fifo(),
            );
            for i in 1..4u16 {
                let o = cfg.orders.get_mut(&i).unwrap();
                o.retain(|j| *j != 0);
                o.insert(0, 0); // every honest party validates party 0 first
            }
            let imp = run_vaba(cfg.clone());
            expect_clean(&cfg, &imp);
            assert!(imp.all_decided());
            assert!(
                imp.decisions
                    .values()
                    .all(|d| d.as_deref() == Some(&[0][..])),
                "seed {seed}: {:?}",
                imp.decisions
            );
            let mut lit = cfg.clone();
            lit.knobs.printed_vote_membership = true;
            let rep = run_vaba(lit);
            assert!(safety_violations(&rep).is_empty(), "{:?}", rep.violations);
            if !rep.all_decided() {
                assert!(rep.quiesced);
                stalled_printed += 1;
            }
        }
        eprintln!("[printed-vote] impl decided {total}/{total}; printed-literal stalled {stalled_printed}/{total}");
        assert_eq!(stalled_printed, total);
    }
}

#[cfg(test)]
mod pinned {
    use super::*;

    /// Seeds that exhibit a behaviour are tried first; if a change to the
    /// protocol moves them, the scan finds fresh ones, so a pin cannot go stale
    /// into a vacuous pass.
    fn first_matching(
        pinned: &[u64],
        scan: std::ops::Range<u64>,
        want: usize,
        hit: impl Fn(u64) -> bool,
    ) -> Vec<u64> {
        let mut found: Vec<u64> = pinned.iter().copied().filter(|s| hit(*s)).collect();
        if found.len() < want {
            found.clear();
            for s in scan {
                if hit(s) {
                    found.push(s);
                    if found.len() == want {
                        break;
                    }
                }
            }
        }
        found
    }

    /// Honest ranks, no instrument: a decision reached only after a view change,
    /// with Byzantine equivocation, forged votes and replay in the schedule. The
    /// natural rate is about 0.5 percent.
    #[test]
    fn byz_vaba_n4_decides_after_view_change_with_honest_ranks() {
        let found = first_matching(&[100_070, 100_191], 100_000..104_000, 2, |seed| {
            let cfg = gen_config(seed, 1, 2_000_000);
            let rep = run_vaba(cfg.clone());
            expect_clean(&cfg, &rep);
            let changed = rep.first_match_view.map_or(false, |v| v >= 1);
            if changed {
                assert!(rep.all_decided(), "seed {seed}");
            }
            changed
        });
        eprintln!("[view-change honest ranks] seeds {found:?}");
        assert_eq!(found.len(), 2, "no two view-change runs found");
    }

    /// Alg4/Lemma 4.5 define the cover set Y as the union of the honest IGValid
    /// sets at the first honest output. An output can contain an index that is in
    /// no honest IGValid at that instant, because RA_j may still be undelivered
    /// while f+1 honest parties have already input 1 for j. The set that does bind
    /// every output is the union of the honest LOCALLY VALIDATED sets: an RA output
    /// of 1 needs f+1 honest inputs, at most f honest parties have not withdrawn,
    /// so one input was cast before the first output.
    #[test]
    fn icg_cover_is_union_of_locally_validated_not_of_igvalid() {
        let found = first_matching(&[100_458], 100_000..106_000, 1, |seed| {
            let cfg = gen_config(seed, 1, 2_000_000);
            let rep = run_vaba(cfg.clone());
            // `expect_clean` includes the corrected BINDING COVER check.
            expect_clean(&cfg, &rep);
            !rep.literal_cover_escapes.is_empty()
        });
        eprintln!("[icg literal cover escape] seed {found:?}");
        assert_eq!(found.len(), 1, "no schedule escaped the literal Y");
    }
}
