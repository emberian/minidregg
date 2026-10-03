//! IndexACS Algorithm7: selector RBC + concrete IndexVABA, not an ideal callback.
use crate::{
    asks::{Bracha, PhaseMessage},
    codec::{bad, Generation, Nat},
    custody::hash,
    vaba::{self, Set, Vaba},
};
use std::io::Result;
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Body {
    Selector(u16, PhaseMessage),
    Vaba(vaba::Message),
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
pub(crate) fn set_bytes(s: &Set) -> Vec<u8> {
    let mut b = vec![s.len() as u8];
    for j in s {
        b.extend(j.to_le_bytes());
    }
    b
}
pub(crate) fn read_set(b: &[u8], n: usize) -> Result<Set> {
    if b.is_empty() || b[0] as usize > n || b.len() != 1 + 2 * b[0] as usize {
        return Err(bad("ACS selector shape"));
    }
    let s: Set = b[1..]
        .chunks_exact(2)
        .map(|p| u16::from_le_bytes(p.try_into().unwrap()))
        .collect();
    if s.iter().any(|j| *j as usize >= n) || set_bytes(&s) != b {
        return Err(bad("ACS selector canonical/range"));
    }
    Ok(s)
}
#[derive(Clone, Debug)]
pub struct Acs {
    pub me: u16,
    pub n: usize,
    pub f: usize,
    pub context: [u8; 32],
    valid: Set,
    proposed: bool,
    selectors: Vec<Bracha>,
    admitted: Set,
    pub(crate) vaba: Vaba,
    pub output: Option<Set>,
}
impl Acs {
    pub fn new(me: u16, n: usize, f: usize, g: &Generation) -> Result<Self> {
        let mut b = b"DREGG.INDEX.ACS.V1".to_vec();
        g.put(&mut b);
        b.extend((n as u64).to_le_bytes());
        b.extend((f as u64).to_le_bytes());
        let context = hash(&b);
        let mut vg = g.clone();
        vg.invocation = Nat::from_be(&context);
        let vaba = Vaba::new(me, n, f, &vg)?;
        Ok(Self {
            me,
            n,
            f,
            context,
            valid: Set::new(),
            proposed: false,
            selectors: (0..n).map(|j| Bracha::new(n, f, Some(j as u16))).collect(),
            admitted: Set::new(),
            vaba,
            output: None,
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
    fn packets(&self, out: Vec<vaba::Send>) -> Vec<Send> {
        out.into_iter()
            .map(|p| Send {
                to: p.to,
                message: Message {
                    context: self.context,
                    body: Body::Vaba(p.message),
                },
            })
            .collect()
    }
    pub fn entropy_needed(&self) -> Vec<u64> {
        self.vaba.entropy_needed()
    }
    pub fn dealer(&mut self, v: u64, c: &[Vec<crate::reconstruction::Field>]) -> Result<Vec<Send>> {
        let out = self.vaba.dealer(v, c)?;
        let mut out = self.packets(out);
        out.extend(self.progress()?);
        Ok(out)
    }
    pub fn validate(&mut self, j: u16) -> Result<Vec<Send>> {
        if j as usize >= self.n {
            return Err(bad("ACS validation index"));
        }
        self.valid.insert(j);
        self.progress()
    }
    pub fn receive(&mut self, sender: u16, m: Message) -> Result<Vec<Send>> {
        if sender as usize >= self.n || m.context != self.context {
            return Err(bad("ACS sender/context"));
        }
        let mut out = vec![];
        match m.body {
            Body::Selector(j, p) => {
                if j as usize >= self.n {
                    return Err(bad("selector dealer"));
                }
                let b = match &p {
                    PhaseMessage::Init(b) | PhaseMessage::Echo(b) | PhaseMessage::Ready(b) => b,
                };
                read_set(b, self.n)?;
                let ps = self.selectors[j as usize].receive(sender, p);
                for p in ps {
                    out.extend(self.all(Body::Selector(j, p)));
                }
            }
            Body::Vaba(p) => {
                let ps = self.vaba.receive(sender, p)?;
                out.extend(self.packets(ps));
            }
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    fn progress(&mut self) -> Result<Vec<Send>> {
        let mut out = vec![];
        if !self.proposed && self.valid.len() >= self.n - self.f {
            self.proposed = true;
            let frozen: Set = self.valid.iter().take(self.n - self.f).copied().collect();
            out.extend(self.all(Body::Selector(
                self.me,
                PhaseMessage::Init(set_bytes(&frozen)),
            )));
        }
        for j in 0..self.n {
            if let Some(b) = &self.selectors[j].output {
                let s = read_set(b, self.n)?;
                if s.len() >= self.n - self.f
                    && s.is_subset(&self.valid)
                    && self.admitted.insert(j as u16)
                {
                    let ps = self.vaba.validate(j as u16)?;
                    out.extend(self.packets(ps));
                }
            }
        }
        if let Some(j) = self.vaba.output {
            if let Some(b) = &self.selectors[j as usize].output {
                let s = read_set(b, self.n)?;
                if s.len() >= self.n - self.f && s.is_subset(&self.valid) {
                    self.output = Some(s);
                }
            }
        }
        Ok(out)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{codec::Nat, reconstruction::Field};
    use std::{collections::VecDeque, io::ErrorKind};
    fn g() -> Generation {
        Generation {
            invocation: Nat::new(1),
            command: vec![9],
            attempt: Nat::new(0),
            generation: Nat::new(1),
            configuration: Nat::new(7),
        }
    }
    fn coeff(j: u16, v: u64) -> Vec<Vec<Field>> {
        vec![
            vec![Field(42 + j as u128 + 100 * v as u128), Field(17)],
            vec![Field(7 + j as u128), Field(13)],
        ]
    }
    #[test]
    fn actual_acs_three_honest_withholds_faulty_party() {
        let mut ns: Vec<_> = (0..4).map(|i| Acs::new(i, 4, 1, &g()).unwrap()).collect();
        let mut q = VecDeque::new();
        for n in &mut ns[1..] {
            for j in [1, 2, 3] {
                q.extend(n.validate(j).unwrap().into_iter().map(|p| (n.me, p)));
            }
            q.extend(
                n.dealer(0, &coeff(n.me, 0))
                    .unwrap()
                    .into_iter()
                    .map(|p| (n.me, p)),
            );
        }
        let mut steps = 0;
        let mut stalled = 0;
        while let Some((from, p)) = q.pop_back() {
            steps += 1;
            assert!(steps < 100000);
            if from == 0 || p.to == 0 {
                continue;
            }
            let to = p.to;
            match ns[to as usize].receive(from, p.message.clone()) {
                Ok(ps) => {
                    stalled = 0;
                    q.extend(ps.into_iter().map(|p| (to, p)));
                    for v in ns[to as usize].entropy_needed() {
                        q.extend(
                            ns[to as usize]
                                .dealer(v, &coeff(to, v))
                                .unwrap()
                                .into_iter()
                                .map(|p| (to, p)),
                        );
                    }
                }
                Err(e) if e.kind() == ErrorKind::WouldBlock => {
                    q.push_front((from, p));
                    stalled += 1;
                    assert!(stalled < q.len() + 100);
                }
                Err(e) => panic!("{e}"),
            }
        }
        for n in &ns[1..] {
            assert_eq!(n.output, Some(Set::from([1, 2, 3])));
        }
    }
    #[test]
    fn malformed_selector_cannot_admit_vaba_input() {
        let mut n = Acs::new(1, 4, 1, &g()).unwrap();
        assert!(n
            .receive(
                2,
                Message {
                    context: n.context,
                    body: Body::Selector(2, PhaseMessage::Init(vec![3, 0, 0, 0, 0, 1, 0]))
                }
            )
            .is_err());
        assert!(n.admitted.is_empty());
        assert!(n.vaba.external_valid().is_empty());
    }
    #[test]
    fn equivocating_selector_and_duplicate_faulty_echo_do_not_split_acs() {
        let mut ns: Vec<_> = (0..4).map(|i| Acs::new(i, 4, 1, &g()).unwrap()).collect();
        let mut q = VecDeque::new();
        for n in &mut ns[1..] {
            for j in [0, 1, 2, 3] {
                q.extend(n.validate(j).unwrap().into_iter().map(|p| (n.me, p)));
            }
            q.extend(
                n.dealer(0, &coeff(n.me, 0))
                    .unwrap()
                    .into_iter()
                    .map(|p| (n.me, p)),
            );
        }
        for to in 1..4 {
            let s: Set = (0..4).filter(|i| *i != (to - 1) as u16).collect();
            for phase in [
                PhaseMessage::Init(set_bytes(&s)),
                PhaseMessage::Echo(set_bytes(&s)),
                PhaseMessage::Ready(set_bytes(&s)),
            ] {
                for _ in 0..3 {
                    q.push_back((
                        0,
                        Send {
                            to,
                            message: Message {
                                context: ns[to as usize].context,
                                body: Body::Selector(0, phase.clone()),
                            },
                        },
                    ));
                }
            }
        }
        let mut steps = 0;
        while let Some((from, p)) = q.pop_back() {
            steps += 1;
            assert!(steps < 200000);
            if p.to == 0 {
                continue;
            }
            let to = p.to;
            match ns[to as usize].receive(from, p.message.clone()) {
                Ok(out) => {
                    q.extend(out.into_iter().map(|p| (to, p)));
                    for v in ns[to as usize].entropy_needed() {
                        q.extend(
                            ns[to as usize]
                                .dealer(v, &coeff(to, v))
                                .unwrap()
                                .into_iter()
                                .map(|p| (to, p)),
                        );
                    }
                }
                Err(e) if e.kind() == ErrorKind::WouldBlock => q.push_front((from, p)),
                Err(e) => panic!("{e}"),
            }
        }
        let expected = ns[1].output.clone().expect("actual ACS termination");
        assert_eq!(expected.len(), 3);
        for n in &ns[1..] {
            assert_eq!(n.output.as_ref(), Some(&expected));
            assert!(n.selectors[0].output.is_none());
        }
    }
}
