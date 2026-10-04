//! Targeted adversaries for the Byzantine harness (`cfg(test)` only).
//!
//! `byz.rs` finds bugs by volume: seeded random schedules. A mutant that only
//! bites on a narrow schedule survives it (the Gather ACK quorum did, across
//! ~10^5 seeds at n=4 and n=7). The adversaries here are constructed instead:
//! each is derived from the property it attacks, so a mutant of exactly that
//! mechanism fails deterministically.

use crate::gather::{Gather, IgBody};
use std::collections::BTreeSet;

type Set = BTreeSet<u16>;

fn set(v: &[u16]) -> Set {
    v.iter().copied().collect()
}

// ------------------------------------------------- Gather ACK quorum (n-f)
//
// IndexGather binding core (ePrint 2024/677 Lemma 4.2). The core is S_i for the
// first honest party i to SEND PREPARE (the lemma text says "to output"; its
// proof uses the first PREPARE): i holds n-f ACKs, so at least n-2f = f+1 of
// the ackers are honest, and each of them acked S_i BEFORE its own PREPARE, so
// S_i is inside T_j for every such j. Any honest output unions n-f PREPAREs,
// which meets those f+1 senders (n-f + f+1 > n). Pairwise intersection of two
// outputs needs no ACKs at all (two sets of n-f PREPAREs share an honest
// sender), which is why random schedules rarely distinguish a lowered quorum:
// the damage is in the intersection of THREE or more outputs.
//
// The adversary below, at n=7 f=2 (honest 0..=4, Byzantine 5 and 6), makes three
// honest parties 0, 1, 2 freeze outputs that exclude one index each:
//
//   a = {2,3,4,5,6}  sent by honest 0,1      (T = Valid at ACK quorum, no more)
//   b = {1,3,4,5,6}  sent by honest 2,3
//   c = {0,3,4,5,6}  sent by honest 4
//   X_0 = a u b = {1..6}   X_1 = a u c = {0,2..6}   X_2 = b u c = {0,1,3..6}
//   X_0 n X_1 n X_2 = {3,4,5,6}: 4 < n-f = 5.
//
// Two honest PREPARE senders can only be shared across outputs if their sets
// agree, so each pair of victims is joined by a different honest sender and the
// Byzantine parties send each victim the PREPARE that keeps it inside its own
// exclusion. Every honest PREPARE above needs only n-f-1 ACKs to be sent: two
// Byzantine ACKs, itself and one honest acker that has since validated enough.
// With the real quorum n-f = 5 the Byzantine pair plus every honest acker the
// schedule can recruit without letting the ackers' later PREPAREs cover the
// INFORM set is one short, nothing is sent, and the three outputs form later
// and agree.
const N: usize = 7;
const F: usize = 2;
const HONEST: u16 = 5;

struct Net {
    g: Vec<Gather>,
    /// (from, to, body) in flight, honest recipients only.
    pool: Vec<(u16, u16, IgBody)>,
    /// PREPARE sets each honest party has sent, with the number of ACKs it had
    /// received when it did.
    prepared: Vec<Option<(Set, usize)>>,
    acks_seen: Vec<usize>,
}

impl Net {
    fn new(slack: usize) -> Self {
        let g = (0..HONEST)
            .map(|i| {
                let mut g = Gather::new(i, N, F).unwrap();
                g.ack_slack = slack;
                g
            })
            .collect();
        Net {
            g,
            pool: vec![],
            prepared: vec![None; HONEST as usize],
            acks_seen: vec![0; HONEST as usize],
        }
    }
    fn absorb(&mut self, from: u16, out: Vec<(u16, IgBody)>) {
        for (to, body) in out {
            if let IgBody::Prepare(p) = &body {
                if to == from && self.prepared[from as usize].is_none() {
                    self.prepared[from as usize] = Some((p.clone(), self.acks_seen[from as usize]));
                }
            }
            if to < HONEST {
                self.pool.push((from, to, body));
            }
        }
    }
    fn validate(&mut self, who: u16, idx: &[u16]) {
        for i in idx {
            let out = self.g[who as usize].validate(*i).unwrap();
            self.absorb(who, out);
        }
    }
    /// Deliver the first in-flight packet matching (from, to, kind); false if none.
    fn deliver(&mut self, from: u16, to: u16, kind: fn(&IgBody) -> bool) -> bool {
        let Some(at) = self
            .pool
            .iter()
            .position(|(f, t, b)| *f == from && *t == to && kind(b))
        else {
            return false;
        };
        let (_, _, body) = self.pool.remove(at);
        if matches!(body, IgBody::Ack) {
            self.acks_seen[to as usize] += 1;
        }
        let out = self.g[to as usize].receive(from, body).unwrap();
        self.absorb(to, out);
        true
    }
    /// A Byzantine party sends `body` to honest `to` (Byzantine parties run no state machine).
    fn byz(&mut self, from: u16, to: u16, body: IgBody) {
        if matches!(body, IgBody::Ack) {
            self.acks_seen[to as usize] += 1;
        }
        let out = self.g[to as usize].receive(from, body).unwrap();
        self.absorb(to, out);
    }
    fn inform(b: &IgBody) -> bool {
        matches!(b, IgBody::Inform(_))
    }
    fn ack(b: &IgBody) -> bool {
        matches!(b, IgBody::Ack)
    }
    fn prepare(b: &IgBody) -> bool {
        matches!(b, IgBody::Prepare(_))
    }
    /// Collect ACKs for `j`: each acker receives j's INFORM (and acks it once it has
    /// validated S_j), then j receives the Byzantine ACKs, its own, then the other
    /// honest ackers', stopping as soon as j sends PREPARE.
    fn collect(&mut self, j: u16, honest_ackers: &[u16]) {
        for a in honest_ackers {
            self.deliver(j, *a, Self::inform);
        }
        for b in [5u16, 6] {
            if self.prepared[j as usize].is_none() {
                self.byz(b, j, IgBody::Ack);
            }
        }
        for a in honest_ackers {
            if self.prepared[j as usize].is_some() {
                break;
            }
            self.deliver(*a, j, Self::ack);
        }
    }
    fn output(&self, i: u16) -> Option<Set> {
        self.g[i as usize].output.clone()
    }
}

struct Outcome {
    prepared: Vec<Option<(Set, usize)>>,
    outputs: Vec<Option<Set>>,
    /// Frozen at the instant each victim first output, before completion.
    victims: Vec<Option<Set>>,
}
impl Outcome {
    fn core(&self) -> Set {
        let mut it = self.outputs.iter().map(|o| o.clone().expect("every honest party outputs"));
        let first = it.next().unwrap();
        it.fold(first, |a, b| a.intersection(&b).copied().collect())
    }
}

/// The three-way split. Steps whose packets do not exist (because the quorum
/// withheld a PREPARE) are skipped: the adversary does what it can, then the
/// schedule is completed fairly and every output is compared.
fn split_core(slack: usize) -> Outcome {
    let a = [2u16, 3, 4, 5, 6];
    let b = [1u16, 3, 4, 5, 6];
    let c = [0u16, 3, 4, 5, 6];
    let mut net = Net::new(slack);
    // 1. Each honest party validates exactly its group's set: INFORM(S_j), |S_j| = n-f.
    for j in [0u16, 1] {
        net.validate(j, &a);
    }
    for j in [2u16, 3] {
        net.validate(j, &b);
    }
    net.validate(4, &c);
    // 2. A and B groups ACK each other (same set), PREPARE with exactly their set.
    net.collect(0, &[0, 1]);
    net.collect(1, &[1, 0]);
    net.collect(2, &[2, 3]);
    net.collect(3, &[3, 2]);
    // Party 3 has PREPAREd {b}; only now does it validate 0, so it can ACK INFORM(c).
    net.validate(3, &[0]);
    net.collect(4, &[4, 3]);
    // 3. Victims 0, 1, 2 widen their own validated set to what they will accept.
    net.validate(0, &[1]);
    net.validate(1, &[0]);
    net.validate(2, &[0]);
    // 4. Byzantine PREPAREs keep each victim inside its exclusion; then the honest
    //    PREPAREs that join each pair, delivered first-n-f exactly.
    let ap = IgBody::Prepare(set(&a));
    let bp = IgBody::Prepare(set(&b));
    for byz in [5u16, 6] {
        net.byz(byz, 0, ap.clone());
        net.byz(byz, 1, ap.clone());
        net.byz(byz, 2, bp.clone());
    }
    for (from, to) in [(0u16, 0u16), (1, 0), (2, 0), (0, 1), (1, 1), (4, 1), (2, 2), (3, 2), (4, 2)] {
        net.deliver(from, to, Net::prepare);
    }
    let victims = (0..3).map(|i| net.output(i)).collect();
    // 5. Fair completion: every honest party validates everything, everything in
    //    flight is delivered, Byzantine parties stay silent from here on.
    for i in 0..HONEST {
        net.validate(i, &[0, 1, 2, 3, 4, 5, 6]);
    }
    let mut guard = 0;
    while !net.pool.is_empty() {
        guard += 1;
        assert!(guard < 100_000, "completion did not quiesce");
        let (from, to, _) = net.pool[0].clone();
        net.deliver(from, to, |_| true);
    }
    Outcome {
        prepared: net.prepared.clone(),
        outputs: (0..HONEST).map(|i| net.output(i)).collect(),
        victims,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The real quorum (n-f = 5 ACKs): the schedule that splits the core against a
    /// lowered quorum gets no honest PREPARE out of its n-f-1 = 4 ACKs, and every
    /// honest output keeps the n-f core. Mutants lowering the ACK quorum by one (or
    /// to f+1) turn the first assertion red: see `byz_gather_n7_lowered_ack_quorum_splits_core`
    /// for the same adversary against the instrumented mutant.
    #[test]
    fn byz_gather_n7_ack_quorum_targeted_core() {
        let o = split_core(0);
        let core = o.core();
        assert!(
            core.len() >= N - F,
            "BINDING CORE: intersection of the five honest outputs {:?} is {core:?} ({} < n-f = {}); victim outputs {:?}",
            o.outputs,
            core.len(),
            N - F,
            o.victims
        );
        // Non-vacuity: the adversary got the first honest PREPAREs to the edge of the
        // quorum and was refused there. Exactly n-f-1 ACKs were in hand when it stopped
        // delivering for j=0 (two Byzantine, itself, the other A-group party), and the
        // PREPARE came only with the n-f'th.
        let (set0, acks0) = o.prepared[0].clone().expect("party 0 PREPAREs after fair completion");
        assert_eq!(acks0, N - F, "party 0 sent PREPARE on {acks0} ACKs, not on exactly n-f");
        assert_ne!(set0, set(&[2, 3, 4, 5, 6]), "party 0's PREPARE must not be the minimal set a lowered quorum would send");
        assert!(o.victims.iter().all(|v| v.is_none()), "no victim may output on the lowered-quorum schedule: {:?}", o.victims);
    }

    /// The same adversary against Gather instrumented with the quorum lowered by
    /// one, and by two (f+1, the mutant the random sweeps could not kill): the three
    /// victims freeze the three sets above and the core is {3,4,5,6}.
    #[test]
    fn byz_gather_n7_lowered_ack_quorum_splits_core() {
        for slack in [1usize, 2] {
            let o = split_core(slack);
            assert_eq!(o.victims[0], Some(set(&[1, 2, 3, 4, 5, 6])), "slack {slack}");
            assert_eq!(o.victims[1], Some(set(&[0, 2, 3, 4, 5, 6])), "slack {slack}");
            assert_eq!(o.victims[2], Some(set(&[0, 1, 3, 4, 5, 6])), "slack {slack}");
            assert_eq!(o.core(), set(&[3, 4, 5, 6]), "slack {slack}");
            assert!(o.core().len() < N - F);
        }
    }
}
