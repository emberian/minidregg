//! ASKS Algorithm 2 and Reliable Agreement Algorithm 1 from ePrint2024/677.
//! Includes concrete Bracha reliable broadcast. All sender IDs MUST originate
//! from authenticated confidential channels; this is a state machine, not a
//! replacement for the channel. ASKS permits a fixed malicious-dealer default:
//! it is intentionally NOT complete VSS or a drop-in AMPC prior-state sharing.
use crate::{
    codec::{bad, Generation},
    custody::hash,
    reconstruction::Field,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    io::{Read, Result},
};
const WORDS: usize = 2; // Independent 128-bit coordinates; 256-bit hidden entropy.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PhaseMessage {
    Init(Vec<u8>),
    Echo(Vec<u8>),
    Ready(Vec<u8>),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Body {
    Commit(PhaseMessage),
    PrivateShare(Vec<Field>),
    Ra(PhaseMessage),
    Reconstruct(Vec<Field>),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Message {
    pub instance: [u8; 32],
    pub body: Body,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Send {
    pub recipient: u16,
    pub message: Message,
}
#[derive(Clone, Debug)]
pub(crate) struct Bracha {
    n: usize,
    f: usize,
    dealer: Option<u16>,
    pub(crate) echo_sent: Option<Vec<u8>>,
    ready_sent: Option<Vec<u8>>,
    echo_senders: BTreeSet<u16>,
    ready_senders: BTreeSet<u16>,
    echos: BTreeMap<Vec<u8>, BTreeSet<u16>>,
    readies: BTreeMap<Vec<u8>, BTreeSet<u16>>,
    pub(crate) output: Option<Vec<u8>>,
}
impl Bracha {
    pub(crate) fn new(n: usize, f: usize, dealer: Option<u16>) -> Self {
        Self {
            n,
            f,
            dealer,
            echo_sent: None,
            ready_sent: None,
            echo_senders: BTreeSet::new(),
            ready_senders: BTreeSet::new(),
            echos: BTreeMap::new(),
            readies: BTreeMap::new(),
            output: None,
        }
    }
    pub(crate) fn input_ra(&mut self, v: Vec<u8>) -> Vec<PhaseMessage> {
        if self.dealer.is_none() && self.echo_sent.is_none() {
            self.echo_sent = Some(v.clone());
            vec![PhaseMessage::Echo(v)]
        } else {
            vec![]
        }
    }
    pub(crate) fn receive(&mut self, sender: u16, m: PhaseMessage) -> Vec<PhaseMessage> {
        let mut out = vec![];
        match m {
            PhaseMessage::Init(v) => {
                if self.dealer == Some(sender) && self.echo_sent.is_none() {
                    self.echo_sent = Some(v.clone());
                    out.push(PhaseMessage::Echo(v));
                }
            }
            PhaseMessage::Echo(v) => {
                if self.echo_senders.insert(sender) {
                    self.echos.entry(v).or_default().insert(sender);
                }
            }
            PhaseMessage::Ready(v) => {
                if self.ready_senders.insert(sender) {
                    self.readies.entry(v).or_default().insert(sender);
                }
            }
        }
        if self.ready_sent.is_none() {
            let eligible = self
                .echos
                .iter()
                .find(|(_, s)| s.len() >= self.n - self.f)
                .map(|(v, _)| v.clone())
                .or_else(|| {
                    self.readies
                        .iter()
                        .find(|(_, s)| s.len() > self.f)
                        .map(|(v, _)| v.clone())
                });
            if let Some(v) = eligible {
                self.ready_sent = Some(v.clone());
                out.push(PhaseMessage::Ready(v));
            }
        }
        if self.output.is_none() {
            if let Some((v, _)) = self
                .readies
                .iter()
                .find(|(_, s)| s.len() >= self.n - self.f)
            {
                self.output = Some(v.clone());
            }
        }
        out
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SharingOutput {
    pub commitments: Vec<[u8; 32]>,
    pub local_share: Option<Vec<Field>>,
}
#[derive(Clone, Debug)]
pub struct Asks {
    pub me: u16,
    pub dealer: u16,
    pub n: usize,
    pub f: usize,
    pub instance: [u8; 32],
    rbc: Bracha,
    ra: Bracha,
    private_share: Option<Vec<Field>>,
    accepted_share: Option<Vec<Field>>,
    pending: BTreeMap<u16, Vec<Field>>,
    valid: BTreeMap<u16, Vec<Field>>,
    pub sharing: Option<SharingOutput>,
    pub reconstruct_started: bool,
    pub key: Option<[u8; 32]>,
}
impl Asks {
    pub fn new(me: u16, dealer: u16, n: usize, f: usize, g: &Generation) -> Result<Self> {
        if n != 3 * f + 1 || n > 16 || me as usize >= n || dealer as usize >= n {
            return Err(bad("ASKS access structure"));
        }
        let mut b = b"DREGG.ASKS.V2".to_vec();
        g.put(&mut b);
        b.extend((n as u64).to_le_bytes());
        b.extend((f as u64).to_le_bytes());
        b.extend(dealer.to_le_bytes());
        Ok(Self {
            me,
            dealer,
            n,
            f,
            instance: hash(&b),
            rbc: Bracha::new(n, f, Some(dealer)),
            ra: Bracha::new(n, f, None),
            private_share: None,
            accepted_share: None,
            pending: BTreeMap::new(),
            valid: BTreeMap::new(),
            sharing: None,
            reconstruct_started: false,
            key: None,
        })
    }
    pub(crate) fn dealer_key(&self, coefficients: &[Vec<Field>]) -> Result<[u8; 32]> {
        if coefficients.len() != WORDS || coefficients.iter().any(|p| p.len() != self.f + 1) {
            return Err(bad("dealer key degree/dimensions"));
        }
        Ok(self.h(0, &coefficients.iter().map(|p| p[0]).collect::<Vec<_>>()))
    }
    fn h(&self, index: u16, words: &[Field]) -> [u8; 32] {
        let mut b = b"DREGG.ASKS.H.V2".to_vec();
        b.extend(self.instance);
        b.extend(index.to_le_bytes());
        for w in words {
            b.extend(w.0.to_le_bytes());
        }
        hash(&b)
    }
    fn all(&self, body: Body) -> Vec<Send> {
        (0..self.n)
            .map(|i| Send {
                recipient: i as u16,
                message: Message {
                    instance: self.instance,
                    body: body.clone(),
                },
            })
            .collect()
    }
    fn commits(&self) -> Option<Vec<[u8; 32]>> {
        let b = self.rbc.output.as_ref()?;
        if b.len() != self.n * 32 {
            return None;
        }
        Some(b.chunks_exact(32).map(|x| x.try_into().unwrap()).collect())
    }
    fn private_valid(&self, commits: &[[u8; 32]]) -> Option<Vec<Field>> {
        self.accepted_share
            .as_ref()
            .or(self.private_share.as_ref())
            .filter(|s| self.h(self.me + 1, s) == commits[self.me as usize])
            .cloned()
    }
    /// Real entropy from OS for dealer fixture. The party must persist the selected
    /// polynomial and this outbound list before transmitting; regenerating after
    /// uncertainty is an equivocation. Caller owns the durable transcript adapter.
    pub fn dealer_start(&self) -> Result<Vec<Send>> {
        if self.me != self.dealer {
            return Err(bad("not dealer"));
        }
        let mut coefficients = vec![vec![Field(0); self.f + 1]; WORDS];
        let mut rng = std::fs::File::open("/dev/urandom")?;
        for p in &mut coefficients {
            for c in p {
                let mut b = [0; 16];
                rng.read_exact(&mut b)?;
                *c = Field(u128::from_le_bytes(b));
            }
        }
        self.dealer_with_coefficients(&coefficients)
    }
    pub fn dealer_with_coefficients(&self, coefficients: &[Vec<Field>]) -> Result<Vec<Send>> {
        if self.me != self.dealer
            || coefficients.len() != WORDS
            || coefficients.iter().any(|p| p.len() != self.f + 1)
        {
            return Err(bad("dealer dimensions"));
        }
        let mut commitments = vec![];
        let mut out = vec![];
        for i in 0..self.n {
            let x = Field(i as u128 + 1);
            let words: Vec<_> = coefficients
                .iter()
                .map(|p| p.iter().rev().fold(Field(0), |z, c| z.mul(x).add(*c)))
                .collect();
            commitments.extend(self.h(i as u16 + 1, &words));
            out.push(Send {
                recipient: i as u16,
                message: Message {
                    instance: self.instance,
                    body: Body::PrivateShare(words),
                },
            });
        }
        out.extend(self.all(Body::Commit(PhaseMessage::Init(commitments))));
        Ok(out)
    }
    /// The sender is provided by the channel, not by serialized Message data.
    pub fn receive(&mut self, sender: u16, msg: Message) -> Result<Vec<Send>> {
        if sender as usize >= self.n || msg.instance != self.instance {
            return Err(bad("foreign sender/instance"));
        }
        let mut out = vec![];
        match msg.body {
            Body::Commit(m) => {
                let v = match &m {
                    PhaseMessage::Init(v) | PhaseMessage::Echo(v) | PhaseMessage::Ready(v) => v,
                };
                if v.len() != self.n * 32 {
                    return Err(bad("commit vector dimensions"));
                }
                for m in self.rbc.receive(sender, m) {
                    out.extend(self.all(Body::Commit(m)));
                }
            }
            Body::Ra(m) => {
                let v = match &m {
                    PhaseMessage::Init(v) | PhaseMessage::Echo(v) | PhaseMessage::Ready(v) => v,
                };
                if v != &[1] || matches!(m, PhaseMessage::Init(_)) {
                    return Err(bad("RA input domain"));
                }
                for m in self.ra.receive(sender, m) {
                    out.extend(self.all(Body::Ra(m)));
                }
            }
            Body::PrivateShare(s) => {
                if sender != self.dealer || s.len() != WORDS {
                    return Err(bad("private share sender/dimensions"));
                }
                // A malicious dealer can send replacements. Only a commitment-matching
                // share can ever trigger RA. Freeze the sharing output when it terminates.
                if self.sharing.is_none() && self.accepted_share.is_none() {
                    self.private_share = Some(s);
                }
            }
            Body::Reconstruct(s) => {
                if s.len() != WORDS {
                    return Err(bad("reconstruction dimensions"));
                }
                if !self.valid.contains_key(&sender) {
                    self.pending.insert(sender, s);
                }
            }
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    fn progress(&mut self) -> Result<Vec<Send>> {
        let mut out = vec![];
        if let Some(commits) = self.commits() {
            if let Some(valid) = self.private_valid(&commits) {
                if self.accepted_share.is_none() {
                    self.accepted_share = Some(valid);
                }
                for m in self.ra.input_ra(vec![1]) {
                    out.extend(self.all(Body::Ra(m)));
                }
            }
            if self.sharing.is_none() && self.ra.output == Some(vec![1]) {
                self.sharing = Some(SharingOutput {
                    local_share: self.private_valid(&commits),
                    commitments: commits,
                });
            }
        }
        if self.reconstruct_started {
            if let Some(shared) = &self.sharing {
                for (sender, s) in &self.pending {
                    if self.h(*sender + 1, s) == shared.commitments[*sender as usize] {
                        self.valid.entry(*sender).or_insert_with(|| s.clone());
                    }
                }
                if self.key.is_none() && self.valid.len() > self.f {
                    let points: Vec<_> = self
                        .valid
                        .iter()
                        .take(self.f + 1)
                        .map(|(i, s)| (*i, s))
                        .collect();
                    let interpolate_at = |at: Field| -> Result<Vec<Field>> {
                        let mut result = vec![Field(0); WORDS];
                        for (i, (sender, words)) in points.iter().enumerate() {
                            let xi = Field(*sender as u128 + 1);
                            let mut coefficient = Field(1);
                            for (j, (other, _)) in points.iter().enumerate() {
                                if i != j {
                                    let xj = Field(*other as u128 + 1);
                                    coefficient =
                                        coefficient.mul(at.add(xj)).mul(xi.add(xj).inv()?);
                                }
                            }
                            for (k, w) in words.iter().enumerate() {
                                result[k] = result[k].add(coefficient.mul(*w));
                            }
                        }
                        Ok(result)
                    };
                    let mut coherent = true;
                    for i in 0..self.n {
                        if self.h(i as u16 + 1, &interpolate_at(Field(i as u128 + 1))?)
                            != shared.commitments[i]
                        {
                            coherent = false;
                        }
                    }
                    self.key = Some(if coherent {
                        self.h(0, &interpolate_at(Field(0))?)
                    } else {
                        [0; 32]
                    });
                }
            }
        }
        Ok(out)
    }
    pub fn start_reconstruction(&mut self) -> Result<Vec<Send>> {
        if self.sharing.is_none() {
            return Err(bad("reconstruction before sharing finished"));
        }
        if self.reconstruct_started {
            return Ok(vec![]);
        }
        self.reconstruct_started = true;
        let mut out = match self.sharing.as_ref().unwrap().local_share.clone() {
            Some(s) => self.all(Body::Reconstruct(s)),
            None => vec![],
        };
        out.extend(self.progress()?);
        Ok(out)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::codec::Nat;
    use std::collections::VecDeque;
    fn g() -> Generation {
        Generation {
            invocation: Nat::new(1),
            command: vec![9],
            attempt: Nat::new(1),
            generation: Nat::new(2),
            configuration: Nat::new(3),
        }
    }
    fn nodes() -> Vec<Asks> {
        (0..4)
            .map(|i| Asks::new(i, 0, 4, 1, &g()).unwrap())
            .collect()
    }
    fn deliver(nodes: &mut [Asks], queue: &mut VecDeque<(u16, Send)>, drop_holder: Option<u16>) {
        let mut steps = 0;
        while let Some((sender, s)) = queue.pop_back() {
            steps += 1;
            assert!(steps < 10000);
            if Some(sender) == drop_holder || Some(s.recipient) == drop_holder {
                continue;
            }
            let recipient = s.recipient;
            let produced = nodes[recipient as usize]
                .receive(sender, s.message)
                .unwrap();
            for p in produced {
                queue.push_front((recipient, p));
            }
        }
    }
    fn start(nodes: &[Asks]) -> VecDeque<(u16, Send)> {
        nodes[0]
            .dealer_with_coefficients(&[vec![Field(42), Field(17)], vec![Field(7), Field(13)]])
            .unwrap()
            .into_iter()
            .map(|s| (0, s))
            .collect()
    }
    #[test]
    fn complete_sharing_then_byzantine_withhold() {
        let mut ns = nodes();
        let mut q = start(&ns);
        deliver(&mut ns, &mut q, Some(3));
        for n in &ns[..3] {
            assert!(n.sharing.is_some());
            assert!(n.key.is_none());
        }
        for n in &mut ns[..3] {
            for s in n.start_reconstruction().unwrap() {
                q.push_back((n.me, s));
            }
        }
        deliver(&mut ns, &mut q, Some(3));
        assert!(ns[..3].iter().all(|n| n.key.is_some()));
        assert!(ns[..3].windows(2).all(|n| n[0].key == n[1].key));
        assert_ne!(ns[0].key, Some([0; 32]));
    }
    #[test]
    fn invalid_reconstruction_ignored() {
        let mut ns = nodes();
        let mut q = start(&ns);
        deliver(&mut ns, &mut q, None);
        let badmsg = Message {
            instance: ns[0].instance,
            body: Body::Reconstruct(vec![Field(100), Field(200)]),
        };
        for n in &mut ns[..3] {
            n.start_reconstruction().unwrap();
            n.receive(3, badmsg.clone()).unwrap();
            assert!(!n.valid.contains_key(&3));
        }
        let good = ns[1].all(Body::Reconstruct(
            ns[1].sharing.as_ref().unwrap().local_share.clone().unwrap(),
        ));
        let good2 = ns[2].all(Body::Reconstruct(
            ns[2].sharing.as_ref().unwrap().local_share.clone().unwrap(),
        ));
        q.extend(good.into_iter().map(|s| (1, s)));
        q.extend(good2.into_iter().map(|s| (2, s)));
        deliver(&mut ns, &mut q, Some(3));
        assert!(ns[..3].iter().all(|n| n.key.is_some()));
    }
    #[test]
    fn malformed_dealer_fixed_default_not_private_state() {
        let mut ns = nodes();
        let mut q = start(&ns);
        for (sender, s) in &mut q {
            if let Body::Commit(PhaseMessage::Init(v)) = &mut s.message.body {
                v[3 * 32] ^= 1;
            }
            assert_eq!(*sender, 0);
        }
        deliver(&mut ns, &mut q, None);
        assert!(ns.iter().all(|n| n.sharing.is_some()));
        for n in &mut ns {
            for s in n.start_reconstruction().unwrap() {
                q.push_back((n.me, s));
            }
        }
        deliver(&mut ns, &mut q, None);
        assert!(ns.iter().all(|n| n.key == Some([0; 32])));
    }
    #[test]
    fn receiver_rejects_foreign_and_premature() {
        let mut n = nodes().remove(1);
        assert!(n.start_reconstruction().is_err());
        let m = Message {
            instance: [0; 32],
            body: Body::PrivateShare(vec![Field(1); 2]),
        };
        assert!(n.receive(0, m).is_err());
        let m = Message {
            instance: n.instance,
            body: Body::PrivateShare(vec![Field(1); 2]),
        };
        assert!(n.receive(2, m).is_err());
    }
    #[test]
    fn malicious_replacement_after_ra_echo_cannot_erase_recovery_share() {
        let mut ns = nodes();
        let mut q = start(&ns);
        let mut held_ra = VecDeque::new();
        // Finish commitment RBC and local RA inputs, but hold every RA packet.
        while let Some((sender, send)) = q.pop_front() {
            if matches!(&send.message.body, Body::Ra(_)) {
                held_ra.push_back((sender, send));
                continue;
            }
            let recipient = send.recipient;
            let produced = ns[recipient as usize]
                .receive(sender, send.message)
                .unwrap();
            q.extend(produced.into_iter().map(|s| (recipient, s)));
        }
        for node in &ns[1..] {
            assert!(node.ra.echo_sent.is_some());
            assert!(node.sharing.is_none());
            assert!(node.accepted_share.is_some());
        }
        // Corrupt dealer replaces every honest party's share after its RA Echo.
        for node in &mut ns[1..] {
            let original = node.accepted_share.clone();
            let replacement = Message {
                instance: node.instance,
                body: Body::PrivateShare(vec![Field(100), Field(200)]),
            };
            let out = node.receive(0, replacement).unwrap();
            assert_eq!(node.accepted_share, original);
            held_ra.extend(out.into_iter().map(|s| (node.me, s)));
        }
        deliver(&mut ns, &mut held_ra, None);
        for node in &mut ns[1..] {
            assert!(node.sharing.as_ref().unwrap().local_share.is_some());
            for send in node.start_reconstruction().unwrap() {
                held_ra.push_back((node.me, send));
            }
        }
        // Dealer disappears: only the three honest parties finish reconstruction.
        deliver(&mut ns, &mut held_ra, Some(0));
        assert!(ns[1..]
            .iter()
            .all(|n| n.key.is_some() && n.key != Some([0; 32])));
        assert!(ns[1..].windows(2).all(|n| n[0].key == n[1].key));
        let expected = ns[1].h(0, &[Field(42), Field(7)]);
        assert!(ns[1..].iter().all(|n| n.key == Some(expected)));
    }
    #[test]
    fn ra_does_not_become_full_byzantine_agreement() {
        let mut ra = Bracha::new(4, 1, None);
        ra.input_ra(vec![1]);
        for i in 0..2 {
            ra.receive(i, PhaseMessage::Echo(vec![1]));
        }
        assert!(ra.output.is_none());
        assert!(ra.ready_sent.is_none());
    }
}

// Exact wire framing for authenticated channel payloads. Sender identity is NOT
// encoded here; the receiving channel supplies it.
pub fn encode_message(m: &Message) -> Vec<u8> {
    let mut o = b"DREGG.ASKS.WIRE\x02".to_vec();
    o.extend(m.instance);
    match &m.body {
        Body::Commit(p) | Body::Ra(p) => {
            o.push(if matches!(&m.body, Body::Commit(_)) {
                0
            } else {
                1
            });
            match p {
                PhaseMessage::Init(v) => {
                    o.push(0);
                    crate::codec::bytes(v, &mut o)
                }
                PhaseMessage::Echo(v) => {
                    o.push(1);
                    crate::codec::bytes(v, &mut o)
                }
                PhaseMessage::Ready(v) => {
                    o.push(2);
                    crate::codec::bytes(v, &mut o)
                }
            }
        }
        Body::PrivateShare(s) | Body::Reconstruct(s) => {
            o.push(if matches!(&m.body, Body::PrivateShare(_)) {
                2
            } else {
                3
            });
            crate::codec::Nat::new(s.len() as u64).put(&mut o);
            for x in s {
                o.extend(x.0.to_le_bytes());
            }
        }
    }
    o
}
pub fn decode_message(bytes: &[u8]) -> Result<Message> {
    let prefix = b"DREGG.ASKS.WIRE\x02";
    if !bytes.starts_with(prefix) || bytes.len() < prefix.len() + 33 || bytes.len() > 4096 {
        return Err(bad("ASKS wire frame"));
    }
    let instance = bytes[prefix.len()..prefix.len() + 32].try_into().unwrap();
    let tag = bytes[prefix.len() + 32];
    let tail = &bytes[prefix.len() + 33..];
    let body = match tag {
        0 | 1 => {
            let phase = *tail.first().ok_or_else(|| bad("ASKS phase"))?;
            let mut r = crate::codec::Reader::new(&tail[1..])?;
            let v = r.bytes()?;
            r.finish()?;
            let p = match phase {
                0 => PhaseMessage::Init(v),
                1 => PhaseMessage::Echo(v),
                2 => PhaseMessage::Ready(v),
                _ => return Err(bad("ASKS phase tag")),
            };
            if tag == 0 {
                Body::Commit(p)
            } else {
                Body::Ra(p)
            }
        }
        2 | 3 => {
            let mut r = crate::codec::Reader::new(tail)?;
            if r.nat()?.value()? != WORDS as u64 {
                return Err(bad("ASKS word count"));
            }
            // Nat WORDS has one digit plus terminator in this bounded suite.
            if tail.len() != 2 + WORDS * 16 {
                return Err(bad("ASKS words/trailing data"));
            }
            let s = tail[2..]
                .chunks_exact(16)
                .map(|b| Field(u128::from_le_bytes(b.try_into().unwrap())))
                .collect();
            if tag == 2 {
                Body::PrivateShare(s)
            } else {
                Body::Reconstruct(s)
            }
        }
        _ => return Err(bad("ASKS body tag")),
    };
    let m = Message { instance, body };
    if encode_message(&m) != bytes {
        return Err(bad("noncanonical ASKS message"));
    }
    Ok(m)
}
#[cfg(test)]
mod wire_tests {
    use super::*;
    #[test]
    fn roundtrip_and_instance_bytes() {
        let messages = [
            Message {
                instance: [7; 32],
                body: Body::Commit(PhaseMessage::Echo(vec![9; 128])),
            },
            Message {
                instance: [8; 32],
                body: Body::PrivateShare(vec![Field(0), Field(u128::MAX)]),
            },
            Message {
                instance: [9; 32],
                body: Body::Reconstruct(vec![Field(3), Field(4)]),
            },
        ];
        for m in messages {
            let b = encode_message(&m);
            assert_eq!(decode_message(&b).unwrap(), m);
            let mut bad = b;
            bad.push(0);
            assert!(decode_message(&bad).is_err());
        }
    }
}
