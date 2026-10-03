//! Concrete IndexVABA composition (ePrint2024/677 Algorithms5–6).
//! Static n=3f+1, n<=16; authenticated private reliable channels required.
//! No ideal rank oracle/stock: every newly entered view uses fresh ASKS.
//! The author-code availability/value adapters below differ from two printed
//! predicates; this implementation does not claim the printed theorem transfers.
//! Pure transition state: caller must persist event + exact outbox BEFORE send,
//! and entropy coefficients BEFORE their first emitted share. Use vaba_store.
use crate::{
    asks::{self, Asks, Bracha, PhaseMessage},
    codec::{bad, Generation, Nat},
    custody::hash,
    gather::{self, CoverGather},
    reconstruction::Field,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    io::{Error, ErrorKind, Result},
};
pub type Set = BTreeSet<u16>;
pub type Votes = BTreeMap<u16, u16>;
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Proposal {
    pub value: u16,
    pub keys: Set,
    pub justification: Votes,
}
fn proposal_bytes(p: &Proposal) -> Vec<u8> {
    let mut b = p.value.to_le_bytes().to_vec();
    b.push(p.keys.len() as u8);
    for x in &p.keys {
        b.extend(x.to_le_bytes())
    }
    b.push(p.justification.len() as u8);
    for (j, v) in &p.justification {
        b.extend(j.to_le_bytes());
        b.extend(v.to_le_bytes())
    }
    b
}
fn read_proposal(b: &[u8], n: usize) -> Result<Proposal> {
    if b.len() < 4 {
        return Err(bad("short prevote"));
    }
    let value = u16::from_le_bytes(b[..2].try_into().unwrap());
    let count = b[2] as usize;
    if count > n {
        return Err(bad("prevote key count"));
    }
    let end = 3 + 2 * count;
    if end >= b.len() {
        return Err(bad("prevote key bytes"));
    }
    let mut keys = Set::new();
    for c in b[3..end].chunks_exact(2) {
        keys.insert(u16::from_le_bytes(c.try_into().unwrap()));
    }
    let k = b[end] as usize;
    if k > n || b.len() != end + 1 + 4 * k {
        return Err(bad("prevote justification length"));
    }
    let mut justification = Votes::new();
    for c in b[end + 1..].chunks_exact(4) {
        justification.insert(
            u16::from_le_bytes(c[..2].try_into().unwrap()),
            u16::from_le_bytes(c[2..].try_into().unwrap()),
        );
    }
    let p = Proposal {
        value,
        keys,
        justification,
    };
    if value as usize >= n
        || p.keys.iter().any(|x| *x as usize >= n)
        || p.justification
            .iter()
            .any(|(j, v)| *j as usize >= n || *v as usize >= n)
        || proposal_bytes(&p) != b
    {
        return Err(bad("noncanonical/range prevote"));
    }
    Ok(p)
}
fn vote_bytes(v: u16) -> Vec<u8> {
    v.to_le_bytes().to_vec()
}
fn read_vote(b: &[u8], n: usize) -> Result<u16> {
    if b.len() != 2 {
        return Err(bad("vote length"));
    }
    let v = u16::from_le_bytes(b.try_into().unwrap());
    if v as usize >= n {
        return Err(bad("vote range"));
    }
    Ok(v)
}
fn phase_payload(p: &PhaseMessage) -> &[u8] {
    match p {
        PhaseMessage::Init(v) | PhaseMessage::Echo(v) | PhaseMessage::Ready(v) => v,
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Body {
    Asks(u16, asks::Message),
    Pre(u16, PhaseMessage),
    Vote(u16, PhaseMessage),
    Cover(gather::Message),
    Final(PhaseMessage),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Message {
    pub context: [u8; 32],
    pub view: u64,
    pub body: Body,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Send {
    pub to: u16,
    pub message: Message,
}
#[derive(Clone, Debug)]
struct View {
    context: [u8; 32],
    asks: Vec<Asks>,
    started: bool,
    shared: Set,
    pre: Vec<Bracha>,
    votes: Vec<Bracha>,
    proposals: BTreeMap<u16, Proposal>,
    cover: CoverGather,
    locally_validated: Set,
    proposed: bool,
    vote_sent: bool,
    tally: Votes,
    next_started: bool,
    local_pre: Option<u16>,
    justification: Votes,
}
#[derive(Clone, Debug)]
pub struct Vaba {
    pub me: u16,
    pub n: usize,
    pub f: usize,
    pub context: [u8; 32],
    generation: Generation,
    valid: Set,
    first: Option<u16>,
    views: BTreeMap<u64, View>,
    pub current: u64,
    final_ra: Bracha,
    stop_after: Option<u64>,
    pub output: Option<u16>,
}
impl Vaba {
    pub fn new(me: u16, n: usize, f: usize, g: &Generation) -> Result<Self> {
        if n != 3 * f + 1 || n > 16 || me as usize >= n {
            return Err(bad("VABA access structure"));
        }
        let mut b = b"DREGG.INDEX.VABA.V1".to_vec();
        g.put(&mut b);
        b.extend((n as u64).to_le_bytes());
        b.extend((f as u64).to_le_bytes());
        let mut s = Self {
            me,
            n,
            f,
            context: hash(&b),
            generation: g.clone(),
            valid: Set::new(),
            first: None,
            views: BTreeMap::new(),
            current: 0,
            final_ra: Bracha::new(n, f, None),
            stop_after: None,
            output: None,
        };
        s.add_view(0, None, Votes::new())?;
        Ok(s)
    }
    fn add_view(&mut self, v: u64, pre: Option<u16>, justification: Votes) -> Result<()> {
        let mut b = b"DREGG.VABA.VIEW.V1".to_vec();
        b.extend(self.context);
        b.extend(v.to_le_bytes());
        let context = hash(&b);
        let mut g = self.generation.clone();
        g.invocation = Nat::from_be(&context);
        let asks = (0..self.n)
            .map(|j| Asks::new(self.me, j as u16, self.n, self.f, &g))
            .collect::<Result<Vec<_>>>()?;
        self.views.insert(
            v,
            View {
                context,
                asks,
                started: false,
                shared: Set::new(),
                pre: (0..self.n)
                    .map(|j| Bracha::new(self.n, self.f, Some(j as u16)))
                    .collect(),
                votes: (0..self.n)
                    .map(|j| Bracha::new(self.n, self.f, Some(j as u16)))
                    .collect(),
                proposals: BTreeMap::new(),
                cover: CoverGather::new(self.me, self.n, self.f, context)?,
                locally_validated: Set::new(),
                proposed: false,
                vote_sent: false,
                tally: Votes::new(),
                next_started: false,
                local_pre: pre,
                justification,
            },
        );
        self.current = v;
        Ok(())
    }
    /// One event per view; durable driver stores fresh coefficients first.
    pub fn entropy_needed(&self) -> Vec<u64> {
        self.views
            .iter()
            .filter(|(_, s)| !s.started)
            .map(|(v, _)| *v)
            .collect()
    }
    fn all(&self, view: u64, body: Body) -> Vec<Send> {
        (0..self.n)
            .map(|i| Send {
                to: i as u16,
                message: Message {
                    context: self.context,
                    view,
                    body: body.clone(),
                },
            })
            .collect()
    }
    fn asks_packets(&self, v: u64, d: u16, out: Vec<asks::Send>) -> Vec<Send> {
        out.into_iter()
            .map(|s| Send {
                to: s.recipient,
                message: Message {
                    context: self.context,
                    view: v,
                    body: Body::Asks(d, s.message),
                },
            })
            .collect()
    }
    fn cover_packets(&self, v: u64, out: Vec<gather::Send>) -> Vec<Send> {
        out.into_iter()
            .map(|s| Send {
                to: s.to,
                message: Message {
                    context: self.context,
                    view: v,
                    body: Body::Cover(s.message),
                },
            })
            .collect()
    }
    pub fn dealer(&mut self, v: u64, coefficients: &[Vec<Field>]) -> Result<Vec<Send>> {
        let s = self
            .views
            .get_mut(&v)
            .ok_or_else(|| bad("unentered dealer view"))?;
        if s.started {
            return Err(bad("cannot regenerate view entropy"));
        }
        let packets = s.asks[self.me as usize].dealer_with_coefficients(coefficients)?;
        s.started = true;
        let mut out = self.asks_packets(v, self.me, packets);
        out.extend(self.progress()?);
        Ok(out)
    }
    pub fn validate(&mut self, j: u16) -> Result<Vec<Send>> {
        if j as usize >= self.n {
            return Err(bad("external validation index"));
        }
        self.valid.insert(j);
        if self.first.is_none() {
            self.first = Some(j);
            self.views.get_mut(&0).unwrap().local_pre = Some(j)
        }
        self.progress()
    }
    pub fn receive(&mut self, sender: u16, m: Message) -> Result<Vec<Send>> {
        if sender as usize >= self.n || m.context != self.context {
            return Err(bad("VABA sender/context"));
        }
        let mut out = vec![];
        if let Body::Final(p) = m.body {
            if matches!(p, PhaseMessage::Init(_)) {
                return Err(bad("final RA has no init"));
            }
            read_vote(phase_payload(&p), self.n)?;
            for p in self.final_ra.receive(sender, p) {
                out.extend(self.all(0, Body::Final(p)))
            }
        } else {
            // Transport MUST retain/retry WouldBlock frames; this is backpressure,
            // not acceptance+drop. It avoids Byzantine speculative-view allocation.
            let s = self.views.get_mut(&m.view).ok_or_else(|| {
                Error::new(
                    ErrorKind::WouldBlock,
                    "view not entered; retain reliable frame",
                )
            })?;
            match m.body {
                Body::Asks(d, p) => {
                    if d as usize >= self.n {
                        return Err(bad("ASKS dealer index"));
                    }
                    let packets = s.asks[d as usize].receive(sender, p)?;
                    out.extend(self.asks_packets(m.view, d, packets));
                }
                Body::Pre(d, p) => {
                    if d as usize >= self.n {
                        return Err(bad("prevote dealer index"));
                    }
                    read_proposal(phase_payload(&p), self.n)?;
                    let ps = s.pre[d as usize].receive(sender, p);
                    for p in ps {
                        out.extend(self.all(m.view, Body::Pre(d, p)))
                    }
                }
                Body::Vote(d, p) => {
                    if d as usize >= self.n {
                        return Err(bad("vote dealer index"));
                    }
                    read_vote(phase_payload(&p), self.n)?;
                    let ps = s.votes[d as usize].receive(sender, p);
                    for p in ps {
                        out.extend(self.all(m.view, Body::Vote(d, p)))
                    }
                }
                Body::Cover(p) => {
                    let ps = s.cover.receive(sender, p)?;
                    out.extend(self.cover_packets(m.view, ps));
                }
                Body::Final(_) => unreachable!(),
            }
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    fn progress(&mut self) -> Result<Vec<Send>> {
        let mut out = vec![];
        // Process all entered views because late vote evidence can justify a
        // newer view and late completed ASKS must still reconstruct after ICG.
        let view_ids: Vec<_> = self.views.keys().copied().collect();
        let mut next = None;
        for v in view_ids {
            let previous = if v == 0 {
                Votes::new()
            } else {
                self.views[&(v - 1)].tally.clone()
            };
            let s = self.views.get_mut(&v).unwrap();
            for j in 0..self.n {
                if s.asks[j].sharing.is_some() {
                    s.shared.insert(j as u16);
                }
            }
            let mut bodies = vec![];
            let mut asks_out = vec![];
            let mut cover_out = vec![];
            if !s.proposed && s.local_pre.is_some() && s.shared.len() > self.f {
                let p = Proposal {
                    value: s.local_pre.unwrap(),
                    keys: s.shared.iter().take(self.f + 1).copied().collect(),
                    justification: s.justification.clone(),
                };
                s.proposed = true;
                bodies.push(Body::Pre(self.me, PhaseMessage::Init(proposal_bytes(&p))));
            }
            for j in 0..self.n {
                if let Some(b) = &s.pre[j].output {
                    s.proposals
                        .entry(j as u16)
                        .or_insert(read_proposal(b, self.n)?);
                }
            }
            let candidates: Vec<_> = s.proposals.iter().map(|(j, p)| (*j, p.clone())).collect();
            for (j, p) in candidates {
                // Availability is Shared, not external Valid (printed Alg6 L11).
                let prior_ok = if v == 0 {
                    p.justification.is_empty()
                } else {
                    let previous = &previous;
                    p.justification.len() >= self.n - self.f
                        && p.justification
                            .iter()
                            .all(|(k, x)| previous.get(k) == Some(x))
                        && is_most_frequent(&p.justification, p.value)
                };
                if self.valid.contains(&p.value)
                    && p.keys.len() > self.f
                    && p.keys.is_subset(&s.shared)
                    && prior_ok
                {
                    s.locally_validated.insert(j);
                    cover_out.extend(s.cover.validate(j)?);
                }
            }
            if let Some(x) = s.cover.output.clone() {
                // Opening is gated by a real ICG output, not a caller flag.
                for j in &s.shared {
                    if !s.asks[*j as usize].reconstruct_started {
                        for p in s.asks[*j as usize].start_reconstruction()? {
                            asks_out.push((*j, p));
                        }
                    }
                }
                if !s.vote_sent {
                    let all_open = x.iter().all(|j| {
                        s.locally_validated.contains(j)
                            && s.proposals[j]
                                .keys
                                .iter()
                                .all(|k| s.asks[*k as usize].key.is_some())
                    });
                    if all_open {
                        let leader = x
                            .iter()
                            .max_by_key(|j| {
                                (rank(s.context, **j, &s.proposals[*j].keys, &s.asks), **j)
                            })
                            .unwrap();
                        s.vote_sent = true;
                        bodies.push(Body::Vote(
                            self.me,
                            PhaseMessage::Init(vote_bytes(s.proposals[leader].value)),
                        ));
                    }
                }
            }
            for j in 0..self.n {
                if let Some(b) = &s.votes[j].output {
                    let value = read_vote(b, self.n)?;
                    // Proposal VALUE versus broadcaster index. Author predicate:
                    // exists completed validated prevote with this value.
                    if s.proposals.iter().any(|(k, p)| {
                        s.locally_validated.contains(k)
                            && s.cover.ig_valid.contains(k)
                            && p.value == value
                    }) {
                        s.tally.entry(j as u16).or_insert(value);
                    }
                }
            }
            let tally = s.tally.clone();
            if self.final_ra.echo_sent.is_none() {
                if let Some(k) = matching(&tally, self.n - self.f) {
                    for p in self.final_ra.input_ra(vote_bytes(k)) {
                        bodies.push(Body::Final(p));
                    }
                    self.stop_after = Some(
                        v.checked_add(1)
                            .ok_or_else(|| bad("view capacity exhausted"))?,
                    );
                }
            }
            if !s.next_started
                && v == self.current
                && s.tally.len() >= self.n - self.f
                && self.output.is_none()
                && self.stop_after.map_or(true, |last| v < last)
            {
                // Exactly n-f votes frozen for next-view justification. Late
                // votes remain in tally for safety evidence and matching trigger.
                let just: Votes = s
                    .tally
                    .iter()
                    .take(self.n - self.f)
                    .map(|(j, x)| (*j, *x))
                    .collect();
                s.next_started = true;
                next = Some((
                    v.checked_add(1)
                        .ok_or_else(|| bad("view capacity exhausted"))?,
                    most_frequent(&just),
                    just,
                ));
            }
            let _ = s;
            for body in bodies {
                out.extend(self.all(if matches!(body, Body::Final(_)) { 0 } else { v }, body));
            }
            for (d, p) in asks_out {
                out.extend(self.asks_packets(v, d, vec![p]));
            }
            out.extend(self.cover_packets(v, cover_out));
        }
        if let Some((v, pre, just)) = next {
            self.add_view(v, pre, just)?;
        }
        if let Some(b) = &self.final_ra.output {
            let k = read_vote(b, self.n)?;
            if self.valid.contains(&k) {
                self.output = Some(k)
            }
        }
        Ok(out)
    }
    pub fn external_valid(&self) -> &Set {
        &self.valid
    }
    pub fn completed_sharings(&self, v: u64) -> Option<&Set> {
        self.views.get(&v).map(|s| &s.shared)
    }
    pub fn cover_output(&self, v: u64) -> Option<&Set> {
        self.views.get(&v)?.cover.output.as_ref()
    }
}
fn is_most_frequent(v: &Votes, x: u16) -> bool {
    let count = v.values().filter(|a| **a == x).count();
    count > 0
        && v.values()
            .all(|y| v.values().filter(|a| *a == y).count() <= count)
}
fn matching(v: &Votes, q: usize) -> Option<u16> {
    let mut counts = BTreeMap::new();
    for x in v.values() {
        *counts.entry(*x).or_insert(0usize) += 1;
    }
    counts.into_iter().find(|(_, c)| *c >= q).map(|(x, _)| x)
}
fn most_frequent(v: &Votes) -> Option<u16> {
    let mut counts: BTreeMap<u16, usize> = BTreeMap::new();
    for x in v.values() {
        *counts.entry(*x).or_default() += 1;
    }
    let best = counts.values().copied().max()?;
    counts.into_iter().find(|(_, c)| *c == best).map(|(x, _)| x)
}
fn rank(context: [u8; 32], j: u16, keys: &Set, asks: &[Asks]) -> [u8; 32] {
    // Sum independent hash outputs in Z/(2^256), using byte carry. Caller has
    // checked all ASKS keys present. No bare key sum / lossy scalar conversion.
    let mut sum = [0u8; 32];
    for k in keys {
        let mut b = b"DREGG.VABA.RANK.V1".to_vec();
        b.extend(context);
        b.extend(j.to_le_bytes());
        b.extend(asks[*k as usize].key.unwrap());
        let h = hash(&b);
        let mut carry = 0u16;
        for i in (0..32).rev() {
            let v = sum[i] as u16 + h[i] as u16 + carry;
            sum[i] = v as u8;
            carry = v >> 8;
        }
    }
    sum
}
#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;
    fn generation() -> Generation {
        Generation {
            invocation: Nat::from_be(&[255; 32]),
            command: vec![1, 2],
            attempt: Nat::new(0),
            generation: Nat::new(1),
            configuration: Nat::new(7),
        }
    }
    fn nodes() -> Vec<Vaba> {
        (0..4)
            .map(|me| Vaba::new(me, 4, 1, &generation()).unwrap())
            .collect()
    }
    fn coeff(d: u16, v: u64) -> Vec<Vec<Field>> {
        vec![
            vec![Field(42 + d as u128 + 100 * v as u128), Field(17)],
            vec![Field(7 + d as u128), Field(13)],
        ]
    }
    fn drain(ns: &mut [Vaba], q: &mut VecDeque<(u16, Send)>, drop: u16) {
        let mut steps = 0;
        let mut stalled = 0;
        while let Some((from, send)) = q.pop_front() {
            steps += 1;
            assert!(steps < 100000, "protocol stall");
            if from == drop || send.to == drop {
                continue;
            }
            let to = send.to;
            match ns[to as usize].receive(from, send.message.clone()) {
                Ok(out) => {
                    stalled = 0;
                    q.extend(out.into_iter().map(|s| (to, s)));
                    for v in ns[to as usize].entropy_needed() {
                        q.extend(
                            ns[to as usize]
                                .dealer(v, &coeff(to, v))
                                .unwrap()
                                .into_iter()
                                .map(|s| (to, s)),
                        );
                    }
                }
                Err(e) if e.kind() == ErrorKind::WouldBlock => {
                    q.push_back((from, send));
                    stalled += 1;
                    assert!(stalled <= q.len() + 100, "all frames await unopened views");
                }
                Err(e) => panic!("{e}"),
            }
        }
    }
    #[test]
    fn silent_broadcaster_of_valid_value_does_not_stall_votes() {
        let mut ns = nodes();
        let mut q = VecDeque::new();
        // Static faulty party0 withholds all its protocol traffic, but external action
        // validates it. Honest1..3 all first choose proposal VALUE0.
        for n in &mut ns[1..] {
            for j in [0, 1, 2] {
                q.extend(n.validate(j).unwrap().into_iter().map(|s| (n.me, s)));
            }
            q.extend(
                n.dealer(0, &coeff(n.me, 0))
                    .unwrap()
                    .into_iter()
                    .map(|s| (n.me, s)),
            );
        }
        drain(&mut ns, &mut q, 0);
        for n in &ns[1..] {
            assert_eq!(n.output, Some(0));
            let s = &n.views[&0];
            assert!(!s.cover.ig_valid.contains(&0));
            assert!(s.tally.values().all(|v| *v == 0));
        }
    }
    #[test]
    fn reconstruct_is_gated_by_icg_and_view_binding() {
        let mut n = nodes().remove(1);
        n.validate(0).unwrap();
        n.dealer(0, &coeff(1, 0)).unwrap();
        assert!(n.views[&0].asks.iter().all(|s| !s.reconstruct_started));
        let mut wrong = Message {
            context: n.context,
            view: 0,
            body: Body::Final(PhaseMessage::Echo(vote_bytes(0))),
        };
        wrong.context[0] ^= 1;
        assert!(n.receive(2, wrong).is_err());
        let future = Message {
            context: n.context,
            view: 999,
            body: Body::Vote(2, PhaseMessage::Echo(vote_bytes(0))),
        };
        assert_eq!(
            n.receive(2, future).unwrap_err().kind(),
            ErrorKind::WouldBlock
        );
        assert_eq!(n.views.len(), 1);
        assert!(n.dealer(0, &coeff(1, 0)).is_err());
    }
    #[test]
    fn independent_view_keys_and_prevotes_await_actual_availability() {
        let mut n = nodes().remove(1);
        let old = n.views[&0].asks[2].instance;
        n.add_view(1, Some(0), Votes::from([(1, 0), (2, 0), (3, 0)]))
            .unwrap();
        assert_ne!(old, n.views[&1].asks[2].instance);
        let p = Proposal {
            value: 0,
            keys: Set::from([1, 2]),
            justification: Votes::new(),
        };
        assert_eq!(read_proposal(&proposal_bytes(&p), 4).unwrap(), p);
        n.valid.insert(0);
        n.views.get_mut(&0).unwrap().proposals.insert(2, p);
        n.progress().unwrap();
        assert!(!n.views[&0].cover.ig_valid.contains(&2));
    }
}
