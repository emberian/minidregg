//! Coin-free IndexGather and IndexCoverGather from ePrint2024/677 Algorithms3–4.
//! External validation is monotone and must satisfy the source protocol's
//! completeness premise. This module provides no ideal rank/coin callback.
use crate::{
    asks::{Bracha, PhaseMessage},
    codec::bad,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    io::Result,
};
type Set = BTreeSet<u16>;
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IgBody {
    Inform(Set),
    Ack,
    Prepare(Set),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Body {
    Gather(IgBody),
    Ra(u16, PhaseMessage),
    Withdraw,
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
pub struct Gather {
    me: u16,
    n: usize,
    f: usize,
    valid: Set,
    inform_sent: bool,
    prepare_sent: bool,
    informs: BTreeMap<u16, Set>,
    prepares: BTreeMap<u16, Set>,
    acked: Set,
    acks: Set,
    accepted: Set,
    pub output: Option<Set>,
    /// Test instrument for the adversarial harness (vaba/byz_targeted.rs): lowers the
    /// ACK quorum by this many, so a targeted adversary can be shown to bite. Production
    /// is always 0; nothing outside `cfg(test)` can name or set it.
    #[cfg(test)]
    pub(crate) ack_slack: usize,
}
impl Gather {
    pub fn new(me: u16, n: usize, f: usize) -> Result<Self> {
        if n != 3 * f + 1 || n > 16 || me as usize >= n {
            return Err(bad("gather access structure"));
        }
        Ok(Self {
            me,
            n,
            f,
            valid: Set::new(),
            inform_sent: false,
            prepare_sent: false,
            informs: BTreeMap::new(),
            prepares: BTreeMap::new(),
            acked: Set::new(),
            acks: Set::new(),
            accepted: Set::new(),
            output: None,
            #[cfg(test)]
            ack_slack: 0,
        })
    }
    /// ACKs of the party's own INFORM needed before it sends PREPARE: n-f. Binding core
    /// (Lemma 4.2) rests on it: the first honest PREPARE has n-f ACKs, hence f+1 honest
    /// ackers, each of whose later PREPARE contains the first sender's INFORM set, and any
    /// n-f accepted PREPAREs meet those f+1 (n-f + f+1 > n).
    fn ack_quorum(&self) -> usize {
        #[cfg(test)]
        let slack = self.ack_slack;
        #[cfg(not(test))]
        let slack = 0;
        self.n - self.f - slack
    }
    fn all(&self, body: IgBody) -> Vec<(u16, IgBody)> {
        (0..self.n).map(|i| (i as u16, body.clone())).collect()
    }
    fn check(&self, s: &Set) -> Result<()> {
        if s.len() < self.n - self.f || s.iter().any(|i| *i as usize >= self.n) {
            Err(bad("gather set quality/range"))
        } else {
            Ok(())
        }
    }
    pub fn validate(&mut self, index: u16) -> Result<Vec<(u16, IgBody)>> {
        if index as usize >= self.n {
            return Err(bad("validation index"));
        }
        self.valid.insert(index);
        Ok(self.progress())
    }
    pub fn receive(&mut self, sender: u16, message: IgBody) -> Result<Vec<(u16, IgBody)>> {
        if sender as usize >= self.n {
            return Err(bad("gather sender"));
        }
        match message {
            IgBody::Inform(s) => {
                self.check(&s)?;
                self.informs.entry(sender).or_insert(s);
            }
            IgBody::Prepare(s) => {
                self.check(&s)?;
                self.prepares.entry(sender).or_insert(s);
            }
            IgBody::Ack => {
                self.acks.insert(sender);
            }
        }
        Ok(self.progress())
    }
    fn progress(&mut self) -> Vec<(u16, IgBody)> {
        let mut out = vec![];
        if self.valid.len() >= self.n - self.f && !self.inform_sent {
            self.inform_sent = true;
            out.extend(self.all(IgBody::Inform(self.valid.clone())));
        }
        for (j, s) in &self.informs {
            if s.is_subset(&self.valid) && self.acked.insert(*j) {
                out.push((*j, IgBody::Ack));
            }
        }
        if self.inform_sent && self.acks.len() >= self.ack_quorum() && !self.prepare_sent {
            self.prepare_sent = true;
            out.extend(self.all(IgBody::Prepare(self.valid.clone())));
        }
        for (j, s) in &self.prepares {
            if s.is_subset(&self.valid) {
                self.accepted.insert(*j);
            }
        }
        if self.output.is_none() && self.accepted.len() >= self.n - self.f {
            // Freeze the first n-f validated PREPARE senders. Do not let late arrivals
            // mutate the output or semantic floor already consumed by rank opening.
            let mut result = Set::new();
            for j in self.accepted.iter().take(self.n - self.f) {
                result.extend(&self.prepares[j]);
            }
            self.output = Some(result);
        }
        out
    }
    pub fn party(&self) -> u16 {
        self.me
    }
}
#[derive(Clone, Debug)]
pub struct CoverGather {
    pub me: u16,
    pub n: usize,
    pub f: usize,
    pub context: [u8; 32],
    validated: Set,
    ra: Vec<Bracha>,
    gather: Gather,
    pub ig_valid: Set,
    pub withdrawn: bool,
    withdrawals: Set,
    pub output: Option<Set>,
}
impl CoverGather {
    pub fn new(me: u16, n: usize, f: usize, context: [u8; 32]) -> Result<Self> {
        let gather = Gather::new(me, n, f)?;
        Ok(Self {
            me,
            n,
            f,
            context,
            validated: Set::new(),
            ra: (0..n).map(|_| Bracha::new(n, f, None)).collect(),
            gather,
            ig_valid: Set::new(),
            withdrawn: false,
            withdrawals: Set::new(),
            output: None,
        })
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
    fn gather_packets(&self, out: Vec<(u16, IgBody)>) -> Vec<Send> {
        out.into_iter()
            .map(|(to, b)| Send {
                to,
                message: Message {
                    context: self.context,
                    body: Body::Gather(b),
                },
            })
            .collect()
    }
    pub fn validate(&mut self, index: u16) -> Result<Vec<Send>> {
        if index as usize >= self.n {
            return Err(bad("cover validation index"));
        }
        let mut out = vec![];
        if self.validated.insert(index) && !self.withdrawn {
            for p in self.ra[index as usize].input_ra(vec![1]) {
                out.extend(self.all(Body::Ra(index, p)));
            }
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    pub fn receive(&mut self, sender: u16, message: Message) -> Result<Vec<Send>> {
        if sender as usize >= self.n || message.context != self.context {
            return Err(bad("cover sender/context"));
        }
        let mut out = vec![];
        match message.body {
            Body::Gather(b) => {
                let produced = self.gather.receive(sender, b)?;
                out.extend(self.gather_packets(produced));
            }
            Body::Ra(index, p) => {
                if index as usize >= self.n {
                    return Err(bad("cover RA index"));
                }
                let v = match &p {
                    PhaseMessage::Init(v) | PhaseMessage::Echo(v) | PhaseMessage::Ready(v) => v,
                };
                if v != &[1] || matches!(p, PhaseMessage::Init(_)) {
                    return Err(bad("cover RA domain"));
                }
                // READY relay continues after withdrawal, even without local input.
                for p in self.ra[index as usize].receive(sender, p) {
                    out.extend(self.all(Body::Ra(index, p)));
                }
            }
            Body::Withdraw => {
                self.withdrawals.insert(sender);
            }
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    fn progress(&mut self) -> Result<Vec<Send>> {
        let mut out = vec![];
        for index in 0..self.n {
            if self.ra[index].output == Some(vec![1]) && self.ig_valid.insert(index as u16) {
                let produced = self.gather.validate(index as u16)?;
                out.extend(self.gather_packets(produced));
            }
        }
        if self.ig_valid.len() >= self.n - self.f && !self.withdrawn {
            self.withdrawn = true;
            out.extend(self.all(Body::Withdraw));
        }
        if self.output.is_none() && self.withdrawals.len() >= self.n - self.f {
            self.output = self.gather.output.clone();
        }
        Ok(out)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;
    fn nodes() -> Vec<CoverGather> {
        (0..4)
            .map(|i| CoverGather::new(i, 4, 1, [7; 32]).unwrap())
            .collect()
    }
    fn drain(ns: &mut [CoverGather], q: &mut VecDeque<(u16, Send)>, drop: u16) {
        let mut steps = 0;
        while let Some((sender, s)) = q.pop_back() {
            steps += 1;
            assert!(steps < 10000);
            if sender == drop || s.to == drop {
                continue;
            }
            let to = s.to;
            for packet in ns[to as usize].receive(sender, s.message).unwrap() {
                q.push_front((to, packet));
            }
        }
    }
    #[test]
    fn withheld_party_and_cover_freeze() {
        let mut ns = nodes();
        let mut q = VecDeque::new();
        for n in &mut ns[..3] {
            for i in [0, 1, 2] {
                for s in n.validate(i).unwrap() {
                    q.push_back((n.me, s));
                }
            }
        }
        drain(&mut ns, &mut q, 3);
        for n in &ns[..3] {
            assert_eq!(n.output, Some(Set::from([0, 1, 2])));
        }
        let before: Vec<_> = ns[..3].iter().map(|n| n.output.clone()).collect();
        for n in &mut ns[..3] {
            let out = n.validate(3).unwrap();
            assert!(!out
                .iter()
                .any(|s| matches!(s.message.body, Body::Ra(3, PhaseMessage::Echo(_)))));
            q.extend(out.into_iter().map(|s| (n.me, s)));
        }
        drain(&mut ns, &mut q, 3);
        assert_eq!(
            before,
            ns[..3].iter().map(|n| n.output.clone()).collect::<Vec<_>>()
        );
    }
    #[test]
    fn ready_relay_survives_withdrawal() {
        let mut node = CoverGather::new(2, 4, 1, [7; 32]).unwrap();
        node.withdrawn = true;
        let m = Message {
            context: [7; 32],
            body: Body::Ra(3, PhaseMessage::Ready(vec![1])),
        };
        assert!(node.receive(0, m.clone()).unwrap().is_empty());
        let out = node.receive(1, m).unwrap();
        assert!(out
            .iter()
            .any(|s| matches!(s.message.body, Body::Ra(3, PhaseMessage::Ready(_)))));
        assert!(node.ra[3].echo_sent.is_none());
    }
    #[test]
    fn malformed_and_foreign_sets_refuse() {
        let mut node = CoverGather::new(0, 4, 1, [7; 32]).unwrap();
        assert!(node
            .receive(
                1,
                Message {
                    context: [7; 32],
                    body: Body::Gather(IgBody::Prepare(Set::from([0, 1])))
                }
            )
            .is_err());
        assert!(node
            .receive(
                1,
                Message {
                    context: [8; 32],
                    body: Body::Withdraw
                }
            )
            .is_err());
    }
    #[test]
    fn shared_availability_is_not_external_input_validity() {
        use crate::{
            asks::{Asks, Body as AsksBody},
            codec::{Generation, Nat},
            reconstruction::Field,
        };
        let g = Generation {
            invocation: Nat::new(9),
            command: vec![1],
            attempt: Nat::new(0),
            generation: Nat::new(1),
            configuration: Nat::new(7),
        };
        let mut sessions: Vec<_> = (0..4)
            .map(|dealer| {
                (0..4)
                    .map(|me| Asks::new(me, dealer, 4, 1, &g).unwrap())
                    .collect::<Vec<_>>()
            })
            .collect();
        // Dealer0 is outside the external input set but can complete ASKS,
        // as permitted even for a corrupt dealer that distributes valid shares.
        let external_valid = Set::from([1, 2, 3]);
        let mut completed = Set::new();
        for dealer in [0u16, 1] {
            let mut queue: VecDeque<_> = sessions[dealer as usize][dealer as usize]
                .dealer_with_coefficients(&[vec![Field(42), Field(17)], vec![Field(7), Field(13)]])
                .unwrap()
                .into_iter()
                .map(|s| (dealer, s))
                .collect();
            while let Some((sender, s)) = queue.pop_front() {
                let to = s.recipient;
                let output = sessions[dealer as usize][to as usize]
                    .receive(sender, s.message)
                    .unwrap();
                queue.extend(output.into_iter().map(|s| (to, s)));
            }
            assert!(sessions[dealer as usize][1].sharing.is_some());
            assert!(sessions[dealer as usize][1].key.is_none());
            completed.insert(dealer);
        }
        assert_eq!(completed.len(), 2);
        // No reconstruction or ideal coin was used. Literal printed Valid_i
        // condition would reject the first actual completed-sharing proposal.
        assert!(!completed.is_subset(&external_valid));
        assert!(completed
            .iter()
            .all(|d| sessions[*d as usize][1].sharing.is_some()));
    }
}
