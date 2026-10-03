//! Recipient-private payload delivery, adapted from1666 AppendixC.
//! Actual ciphertext RBC replaces AVID with explicit O(L*n^2) replication.
//! Repaired two-coordinate ASKS replaces PrepKey's challenge list with RA
//! retained-share support. A substitution/simulation proof remains ours.
//! Static f<n/3; authenticated PRIVATE reliable channels; SHA256 ROM profile.
//! No QROM/PQ-level or native current-source authorization claim.
use crate::{
    asks::{self, Asks, Bracha, PhaseMessage},
    codec::{bad, Generation, Nat},
    custody::hash,
    reconstruction::Field,
    vaba::Set,
};
use std::{collections::BTreeMap, io::Result};
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Body {
    Key(asks::Message),
    Cipher(PhaseMessage),
    Request {
        receiver: u16,
        requester: u16,
        phase: PhaseMessage,
    },
    Transfer {
        receiver: u16,
        share: Vec<Field>,
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
#[derive(Clone, Debug)]
pub struct PrivateSend {
    pub me: u16,
    pub dealer: u16,
    pub n: usize,
    pub f: usize,
    pub context: [u8; 32],
    length: usize,
    key: Asks,
    cipher: Bracha,
    requests: Vec<Vec<Bracha>>,
    requested: Set,
    authorized: Set,
    disclosed: Set,
    pending: BTreeMap<u16, Vec<Field>>,
    started: bool,
    pub dispersed: bool,
    pub delivered: Option<Vec<u8>>,
}
impl PrivateSend {
    pub fn length(&self) -> usize {
        self.length
    }

    pub fn new(
        me: u16,
        dealer: u16,
        n: usize,
        f: usize,
        g: &Generation,
        length: usize,
    ) -> Result<Self> {
        if length == 0 || length > 65536 {
            return Err(bad("fixed private payload capacity"));
        }
        let mut b = b"DREGG.PRIVATE.SEND.V1".to_vec();
        g.put(&mut b);
        b.extend(dealer.to_le_bytes());
        b.extend((n as u64).to_le_bytes());
        b.extend((f as u64).to_le_bytes());
        b.extend((length as u64).to_le_bytes());
        let context = hash(&b);
        let mut kg = g.clone();
        kg.invocation = Nat::from_be(&context);
        let key = Asks::new(me, dealer, n, f, &kg)?;
        Ok(Self {
            me,
            dealer,
            n,
            f,
            context,
            length,
            key,
            cipher: Bracha::new(n, f, Some(dealer)),
            requests: (0..n)
                .map(|_| (0..n).map(|j| Bracha::new(n, f, Some(j as u16))).collect())
                .collect(),
            requested: Set::new(),
            authorized: Set::new(),
            disclosed: Set::new(),
            pending: BTreeMap::new(),
            started: false,
            dispersed: false,
            delivered: None,
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
    fn key_packets(&self, ps: Vec<asks::Send>) -> Vec<Send> {
        ps.into_iter()
            .map(|p| Send {
                to: p.recipient,
                message: Message {
                    context: self.context,
                    body: Body::Key(p.message),
                },
            })
            .collect()
    }
    /// Caller must journal coefficients+plaintext and exact outbox before send.
    pub fn dealer_with_coefficients(
        &mut self,
        plaintext: &[u8],
        coeff: &[Vec<Field>],
    ) -> Result<Vec<Send>> {
        if self.me != self.dealer || self.started || plaintext.len() != self.length {
            return Err(bad("private sender role/replay/fixed length"));
        }
        let ps = self.key.dealer_with_coefficients(coeff)?;
        let key = self.key.dealer_key(coeff)?;
        let ciphertext = mask(self.context, key, plaintext);
        self.started = true;
        let mut out = self.key_packets(ps);
        out.extend(self.all(Body::Cipher(PhaseMessage::Init(ciphertext))));
        Ok(out)
    }
    /// Environment/source-controller request, not an untrusted permission bool.
    /// The eventual native adapter must prove exact job/recipient/epoch authority.
    pub fn request_delivery(&mut self, receiver: u16) -> Result<Vec<Send>> {
        if receiver as usize >= self.n {
            return Err(bad("private recipient range"));
        }
        let mut out = vec![];
        if self.requested.insert(receiver) {
            out.extend(self.all(Body::Request {
                receiver,
                requester: self.me,
                phase: PhaseMessage::Init(vec![1]),
            }));
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    pub fn receive(&mut self, sender: u16, m: Message) -> Result<Vec<Send>> {
        if sender as usize >= self.n || m.context != self.context {
            return Err(bad("private delivery sender/context"));
        }
        let mut out = vec![];
        match m.body {
            Body::Key(p) => {
                // Public ASKS openings are NEVER admitted by this private-delivery wrapper.
                if matches!(p.body, asks::Body::Reconstruct(_)) {
                    return Err(bad("public key opening forbidden"));
                }
                let ps = self.key.receive(sender, p)?;
                out.extend(self.key_packets(ps));
            }
            Body::Cipher(p) => {
                let b = match &p {
                    PhaseMessage::Init(b) | PhaseMessage::Echo(b) | PhaseMessage::Ready(b) => b,
                };
                if b.len() != self.length {
                    return Err(bad("private ciphertext fixed length"));
                }
                for p in self.cipher.receive(sender, p) {
                    out.extend(self.all(Body::Cipher(p)))
                }
            }
            Body::Request {
                receiver,
                requester,
                phase,
            } => {
                if receiver as usize >= self.n || requester as usize >= self.n {
                    return Err(bad("private request roster"));
                }
                let b = match &phase {
                    PhaseMessage::Init(b) | PhaseMessage::Echo(b) | PhaseMessage::Ready(b) => b,
                };
                if b != &[1] {
                    return Err(bad("private request domain"));
                }
                for phase in
                    self.requests[receiver as usize][requester as usize].receive(sender, phase)
                {
                    out.extend(self.all(Body::Request {
                        receiver,
                        requester,
                        phase,
                    }));
                }
            }
            Body::Transfer { receiver, share } => {
                if receiver != self.me || share.len() != 2 {
                    return Err(bad("private opening addressed to another recipient"));
                }
                // Bounded authenticated sender buffer. Honest transfer can precede this
                // receiver's own request-RBC outputs due to asynchronous delivery ordering.
                self.pending.entry(sender).or_insert(share);
            }
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    fn progress(&mut self) -> Result<Vec<Send>> {
        let mut out = vec![];
        // Both immutable ciphertext and key-sharing commitment precede reveal.
        self.dispersed = self.key.sharing.is_some() && self.cipher.output.is_some();
        if !self.dispersed {
            return Ok(out);
        }
        for receiver in 0..self.n {
            let count = self.requests[receiver]
                .iter()
                .filter(|r| r.output == Some(vec![1]))
                .count();
            if count > self.f {
                self.authorized.insert(receiver as u16);
            }
        }
        for r in &self.authorized {
            if self.disclosed.insert(*r) {
                if let Some(s) = self.key.sharing.as_ref().unwrap().local_share.clone() {
                    out.push(Send {
                        to: *r,
                        message: Message {
                            context: self.context,
                            body: Body::Transfer {
                                receiver: *r,
                                share: s,
                            },
                        },
                    });
                }
            }
        }
        if self.authorized.contains(&self.me) {
            if !self.key.reconstruct_started {
                // This method computes internal state; discard ALL public packets. Only
                // the explicit recipient-addressed transfer above may reach transport.
                let generated = self.key.start_reconstruction()?;
                if generated
                    .iter()
                    .any(|p| !matches!(p.message.body, asks::Body::Reconstruct(_)))
                {
                    return Err(bad("unexpected private key opening side effect"));
                }
            }
            for (j, s) in &self.pending {
                let generated = self.key.receive(
                    *j,
                    asks::Message {
                        instance: self.key.instance,
                        body: asks::Body::Reconstruct(s.clone()),
                    },
                )?;
                if !generated.is_empty() {
                    return Err(bad("private key reconstruction emitted public traffic"));
                }
            }
            if self.delivered.is_none() {
                if let Some(key) = self.key.key {
                    // Corrupt sender's inconsistent commitment polynomial has common ASKS
                    // key0 fallback. It defines deterministic receiver-independent plaintext
                    // from the immutable ciphertext; no entropy claim for corrupt sender.
                    self.delivered = Some(mask(
                        self.context,
                        key,
                        self.cipher.output.as_ref().unwrap(),
                    ));
                }
            }
        }
        Ok(out)
    }
}
fn mask(context: [u8; 32], key: [u8; 32], input: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(input.len());
    for (i, chunk) in input.chunks(32).enumerate() {
        let mut b = b"DREGG.PRIVATE.SEND.PAD.V1".to_vec();
        b.extend(context);
        b.extend(key);
        b.extend((i as u64).to_le_bytes());
        let pad = hash(&b);
        out.extend(chunk.iter().zip(pad).map(|(x, p)| *x ^ p));
    }
    out
}
#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;
    fn g() -> Generation {
        Generation {
            invocation: Nat::from_be(&[255; 32]),
            command: vec![9],
            attempt: Nat::new(0),
            generation: Nat::new(1),
            configuration: Nat::new(7),
        }
    }
    fn coeff() -> Vec<Vec<Field>> {
        vec![vec![Field(42), Field(17)], vec![Field(7), Field(13)]]
    }
    fn nodes() -> Vec<PrivateSend> {
        (0..4)
            .map(|i| PrivateSend::new(i, 0, 4, 1, &g(), 64).unwrap())
            .collect()
    }
    fn drain(
        ns: &mut [PrivateSend],
        q: &mut VecDeque<(u16, Send)>,
        drop: Option<u16>,
        transfers: &mut Vec<(u16, u16)>,
    ) {
        let mut steps = 0;
        while let Some((from, p)) = q.pop_back() {
            steps += 1;
            assert!(steps < 20000);
            if Some(from) == drop || Some(p.to) == drop {
                continue;
            }
            if let Body::Transfer { receiver, .. } = &p.message.body {
                assert_eq!(*receiver, p.to);
                transfers.push((from, p.to));
            }
            let to = p.to;
            let ps = ns[to as usize].receive(from, p.message).unwrap();
            q.extend(ps.into_iter().map(|p| (to, p)));
        }
    }
    #[test]
    fn dealer_disappears_private_recipient_recovers_no_other_key_release() {
        let mut ns = nodes();
        let message = vec![61; 64];
        let mut q: VecDeque<_> = ns[0]
            .dealer_with_coefficients(&message, &coeff())
            .unwrap()
            .into_iter()
            .map(|p| (0, p))
            .collect();
        let mut transfers = vec![];
        drain(&mut ns, &mut q, None, &mut transfers);
        assert!(ns.iter().all(|n| n.dispersed));
        assert!(transfers.is_empty());
        for n in &mut ns[1..3] {
            q.extend(
                n.request_delivery(2)
                    .unwrap()
                    .into_iter()
                    .map(|p| (n.me, p)),
            );
        }
        drain(&mut ns, &mut q, Some(0), &mut transfers);
        assert_eq!(ns[2].delivered, Some(message));
        assert!(ns
            .iter()
            .enumerate()
            .all(|(i, n)| i == 2 || n.delivered.is_none()));
        assert!(transfers.iter().all(|(_, to)| *to == 2));
        assert!(ns
            .iter()
            .enumerate()
            .all(|(i, n)| i == 2 || n.key.key.is_none()));
    }
    #[test]
    fn f_corrupt_requests_alone_cannot_reveal_and_public_open_refuses() {
        let mut ns = nodes();
        let mut q: VecDeque<_> = ns[0]
            .dealer_with_coefficients(&[61; 64], &coeff())
            .unwrap()
            .into_iter()
            .map(|p| (0, p))
            .collect();
        let mut transfers = vec![];
        drain(&mut ns, &mut q, None, &mut transfers);
        q.extend(
            ns[0]
                .request_delivery(3)
                .unwrap()
                .into_iter()
                .map(|p| (0, p)),
        );
        drain(&mut ns, &mut q, None, &mut transfers);
        assert!(transfers.is_empty());
        assert!(ns.iter().all(|n| n.delivered.is_none()));
        let bad = Message {
            context: ns[1].context,
            body: Body::Key(asks::Message {
                instance: ns[1].key.instance,
                body: asks::Body::Reconstruct(vec![Field(1); 2]),
            }),
        };
        assert!(ns[1].receive(0, bad).is_err());
    }
    #[test]
    fn stale_epoch_and_cross_recipient_transfer_refuse() {
        let mut n = nodes().remove(1);
        let wrong = Message {
            context: n.context,
            body: Body::Transfer {
                receiver: 2,
                share: vec![Field(1); 2],
            },
        };
        assert!(n.receive(0, wrong).is_err());
        let mut wrong = Message {
            context: n.context,
            body: Body::Cipher(PhaseMessage::Echo(vec![1; 64])),
        };
        wrong.context[0] ^= 1;
        assert!(n.receive(0, wrong).is_err());
        assert!(n.dealer_with_coefficients(&[1; 64], &coeff()).is_err());
    }

    #[test]
    fn corrupt_dealer_fallback_plaintext_is_receiver_independent() {
        let mut ns = nodes();
        let mut q: VecDeque<_> = ns[0]
            .dealer_with_coefficients(&[61; 64], &coeff())
            .unwrap()
            .into_iter()
            .map(|p| (0, p))
            .collect();
        // Corrupt dealer broadcasts a commitment inconsistent at holder3.
        for (_, p) in &mut q {
            if let Body::Key(asks::Message {
                body: asks::Body::Commit(PhaseMessage::Init(v)),
                ..
            }) = &mut p.message.body
            {
                v[3 * 32] ^= 1;
            }
        }
        let mut transfers = vec![];
        drain(&mut ns, &mut q, None, &mut transfers);
        assert!(ns.iter().all(|n| n.dispersed));
        for requester in 0..2 {
            for receiver in [1, 2] {
                q.extend(
                    ns[requester]
                        .request_delivery(receiver)
                        .unwrap()
                        .into_iter()
                        .map(|p| (requester as u16, p)),
                );
            }
        }
        drain(&mut ns, &mut q, None, &mut transfers);
        assert!(ns[1].delivered.is_some());
        assert_eq!(ns[1].delivered, ns[2].delivered);
        assert_eq!(ns[1].key.key, Some([0; 32]));
        assert_eq!(ns[2].key.key, Some([0; 32]));
        let expected = mask(
            ns[1].context,
            [0; 32],
            ns[1].cipher.output.as_ref().unwrap(),
        );
        assert_eq!(ns[1].delivered, Some(expected));
    }
}
