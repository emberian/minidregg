//! Composite private-output WAL: exact original shares/descriptor/anchor and
//! OS key polynomial coefficients + recursive outbox before publication.
//! Native current release authority is NOT supplied by these byte codecs.
use crate::{
    codec::{bad, bytes, Generation, Nat, Reader},
    consensus_wire::Cursor,
    custody,
    private_initial::Initial,
    private_output::{self, Message, PrivateOutput, Send},
    reconstruction::Field,
    transition_journal::{Journal, Machine},
};
use std::{
    fs::File,
    io::{Read, Result},
    path::Path,
};
const DOMAIN: &[u8] = b"DREGG.PRIVATE.OUTPUT.INIT.FILE\x01";
fn nat(c: &mut Cursor) -> Result<usize> {
    let mut ds = vec![];
    loop {
        let v = c.byte()?;
        ds.push(v);
        if v == 255 {
            break;
        }
    }
    let mut r = Reader::new(&ds)?;
    let n = r.count()?;
    r.finish()?;
    Ok(n)
}
fn outbox(ps: &[Send]) -> Vec<u8> {
    let mut b = vec![];
    Nat::new(ps.len() as u64).put(&mut b);
    for p in ps {
        b.extend(p.to.to_le_bytes());
        bytes(&private_output::encode_message(&p.message), &mut b)
    }
    b
}
fn packets(b: &[u8], n: usize) -> Result<Vec<Send>> {
    let mut c = Cursor::new(b)?;
    let count = nat(&mut c)?;
    if count > 65536 {
        return Err(bad("output recursive outbox capacity"));
    }
    let mut ps = vec![];
    for _ in 0..count {
        let to = c.u16()?;
        if to as usize >= n {
            return Err(bad("output outbox recipient"));
        }
        ps.push(Send {
            to,
            message: private_output::decode_message(&c.bytes()?)?,
        });
    }
    c.finish()?;
    if outbox(&ps) != b {
        return Err(bad("output outbox canonical"));
    }
    Ok(ps)
}
#[derive(Clone)]
pub struct OutputMachine {
    pub state: PrivateOutput,
}
impl Machine for OutputMachine {
    fn apply(&mut self, event: &[u8]) -> Result<Vec<u8>> {
        let mut c = Cursor::new(event)?;
        let ps = match c.byte()? {
            0 => {
                let mut coeff = vec![];
                for _ in 0..2 {
                    let mut row = vec![];
                    for _ in 0..=self.state.roster().1 {
                        row.push(Field(u128::from_le_bytes(c.take(16)?.try_into().unwrap())))
                    }
                    coeff.push(row);
                }
                c.finish()?;
                self.state.start_with_coefficients(&coeff)?
            }
            1 => {
                c.finish()?;
                self.state.request_delivery()?
            }
            2 => {
                let sender = c.u16()?;
                let m = private_output::decode_message(&c.bytes()?)?;
                c.finish()?;
                self.state.receive(sender, m)?
            }
            _ => return Err(bad("output event tag")),
        };
        Ok(outbox(&ps))
    }
}
impl crate::authenticated_ingress::IngressMachine for OutputMachine {
    fn validate_ingress_context(
        &self,
        c: &crate::authenticated_ingress::Context,
        n: usize,
    ) -> Result<()> {
        if c.protocol != crate::authenticated_ingress::Protocol::PrivateOutput
            || c.recipient != self.state.holder()
            || &c.generation != self.state.generation()
            || n != self.state.roster().0
        {
            return Err(bad("actual output receiver generation/holder/profile"));
        }
        Ok(())
    }
}
pub struct Store {
    journal: Journal<OutputMachine>,
    _initial: Initial,
}
fn identity(initial: &[u8]) -> Vec<u8> {
    let mut b = b"DREGG.PRIVATE.OUTPUT.PARTY.WAL\x01".to_vec();
    b.extend(custody::hash(initial));
    b
}
impl Store {
    pub fn create(path: &Path, state: PrivateOutput) -> Result<Self> {
        let original = Initial::create(path, DOMAIN, &state.initial_bytes()?)?;
        let journal = Journal::open(path, &identity(&original.bytes), OutputMachine { state })?;
        Ok(Self {
            journal,
            _initial: original,
        })
    }
    pub fn reopen(
        path: &Path,
        g: &Generation,
        context: [u8; 32],
        holder: u16,
        recipient: u16,
        anchor: &Path,
    ) -> Result<Self> {
        let original = Initial::load(path, DOMAIN)?;
        let state =
            PrivateOutput::restore_initial(&original.bytes, g, context, holder, recipient, anchor)?;
        let journal = Journal::open(path, &identity(&original.bytes), OutputMachine { state })?;
        Ok(Self {
            journal,
            _initial: original,
        })
    }
    pub fn state(&self) -> &PrivateOutput {
        &self.journal.state().state
    }
    fn apply(&mut self, b: &[u8]) -> Result<Vec<Send>> {
        packets(&self.journal.append(b)?, self.state().roster().0)
    }
    pub fn start(&mut self) -> Result<Vec<Send>> {
        let mut b = vec![0];
        let mut random = vec![0; 32 * (self.state().roster().1 + 1)];
        File::open("/dev/urandom")?.read_exact(&mut random)?;
        b.extend(random);
        self.apply(&b)
    }
    /// Requires real fresh source release; this method is only environment input.
    pub fn request_delivery(&mut self) -> Result<Vec<Send>> {
        self.apply(&[1])
    }
    pub fn receive(&mut self, sender: u16, m: &Message) -> Result<Vec<Send>> {
        let mut b = vec![2];
        b.extend(sender.to_le_bytes());
        bytes(&private_output::encode_message(m), &mut b);
        self.apply(&b)
    }
    pub fn replay_outboxes(&self) -> Result<Vec<Send>> {
        let mut out = vec![];
        for b in self.journal.replay_outboxes() {
            out.extend(packets(b, self.state().roster().0)?)
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        arithmetic_reference,
        asks::PhaseMessage,
        codec::Purpose,
        private_send::{self, Body},
    };
    use std::{
        collections::VecDeque,
        fs,
        path::PathBuf,
        time::{SystemTime, UNIX_EPOCH},
    };
    fn path(label: &str) -> PathBuf {
        let d = std::env::temp_dir().join(format!(
            "mini-output-{label}-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&d).unwrap();
        d.join("events")
    }
    fn output_stores(
        left: u8,
        right: u8,
        instance: u64,
    ) -> (
        Vec<Option<Store>>,
        Vec<crate::triple_king::tests::AnchorFixture>,
        Vec<PathBuf>,
    ) {
        let (completed, anchors) = arithmetic_reference::tests::completed(left, right, instance);
        let paths = (0..4)
            .map(|i| path(&format!("{instance}-{i}")))
            .collect::<Vec<_>>();
        let descriptor = b"fixed reference addition/result recipient1; no native release grant";
        let stores = completed
            .iter()
            .enumerate()
            .map(|(i, parent)| {
                let local = paths[i].with_extension("output-burn");
                let state =
                    PrivateOutput::reserve(parent, 1, descriptor, anchors[i].socket(), &local)
                        .unwrap();
                assert!(PrivateOutput::reserve(
                    parent,
                    1,
                    b"changed output descriptor",
                    anchors[i].socket(),
                    &paths[i].with_extension("retry")
                )
                .is_err());
                Some(Store::create(&paths[i], state).unwrap())
            })
            .collect();
        (stores, anchors, paths)
    }
    fn drive(
        stores: &mut [Option<Store>],
        q: &mut VecDeque<(u16, Send)>,
        change_cipher: bool,
        drop_zero: bool,
    ) {
        let mut steps = 0;
        while let Some((sender, mut p)) = q.pop_front() {
            steps += 1;
            assert!(steps < 500000);
            if drop_zero && sender == 0 {
                continue;
            }
            if change_cipher && sender == 0 && p.message.dealer == 0 {
                if let Body::Cipher(PhaseMessage::Init(ref mut raw)) = p.message.message.body {
                    raw[0] ^= 1;
                }
            }
            let raw = private_output::encode_message(&p.message);
            let m = private_output::decode_message(&raw).unwrap();
            let to = p.to;
            q.extend(
                stores[to as usize]
                    .as_mut()
                    .unwrap()
                    .receive(sender, &m)
                    .unwrap()
                    .into_iter()
                    .map(|p| (to, p)),
            );
        }
    }
    #[test]
    fn actual_shared_addition_private_result_and_pending_then_completed_recovery() {
        for (left, right, instance) in [(1, 2, 80), (3, 1, 81), (3, 3, 82)] {
            let (mut stores, anchors, paths) = output_stores(left, right, instance);
            let context = stores[1].as_ref().unwrap().state().context();
            let g = stores[1].as_ref().unwrap().state().generation().clone();
            let mut q = VecDeque::new();
            let mut original = vec![];
            for (i, s) in stores.iter_mut().enumerate() {
                let ps = s.as_mut().unwrap().start().unwrap();
                if i == 1 {
                    original = ps.clone()
                }
                q.extend(ps.into_iter().map(|p| (i as u16, p)));
            }
            drop(stores[1].take());
            assert!(Store::reopen(&paths[1], &g, context, 1, 2, anchors[1].socket()).is_err());
            let reopened =
                Store::reopen(&paths[1], &g, context, 1, 1, anchors[1].socket()).unwrap();
            assert_eq!(
                reopened.replay_outboxes().unwrap(),
                original,
                "no new key polynomial/ciphertext after reply loss"
            );
            q.extend(original.into_iter().map(|p| (1, p)));
            stores[1] = Some(reopened);
            drive(&mut stores, &mut q, false, false);
            assert!(
                stores
                    .iter()
                    .all(|s| s.as_ref().unwrap().state().result().is_none()),
                "dispersal is not release"
            );
            // Environment stands for the still-required fresh native ReleaseAdmission.
            for (i, s) in stores.iter_mut().enumerate() {
                q.extend(
                    s.as_mut()
                        .unwrap()
                        .request_delivery()
                        .unwrap()
                        .into_iter()
                        .map(|p| (i as u16, p)),
                );
            }
            drive(&mut stores, &mut q, false, false);
            let result = stores[1].as_ref().unwrap().state().result().unwrap();
            let value = result
                .bits()
                .iter()
                .enumerate()
                .fold(0u8, |v, (i, b)| v | ((*b as u8) << i));
            assert_eq!(value, left + right);
            assert!(stores
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != 1)
                .all(|(_, s)| s.as_ref().unwrap().state().result().is_none()));
            assert_eq!(result.recipient(), 1);
            assert_eq!(result.generation(), &g);
            drop(stores[1].take());
            let reopened =
                Store::reopen(&paths[1], &g, context, 1, 1, anchors[1].socket()).unwrap();
            assert_eq!(
                reopened
                    .state()
                    .result()
                    .unwrap()
                    .bits()
                    .iter()
                    .enumerate()
                    .fold(0u8, |v, (i, b)| v | ((*b as u8) << i)),
                left + right
            );
            let journal =
                crate::codec::Journal::decode(&custody::rpc(anchors[1].socket(), &[0]).unwrap())
                    .unwrap();
            assert!(journal
                .allocations
                .iter()
                .any(|a| a.purpose == Purpose::HolderPad));
        }
    }
    #[test]
    fn malformed_corrupt_output_sender_is_rejected_and_remaining_honest_deliver() {
        let (mut stores, anchors, _paths) = output_stores(3, 3, 83);
        let mut q = VecDeque::new();
        for (i, s) in stores.iter_mut().enumerate() {
            q.extend(
                s.as_mut()
                    .unwrap()
                    .start()
                    .unwrap()
                    .into_iter()
                    .map(|p| (i as u16, p)),
            );
        }
        drive(&mut stores, &mut q, true, false);
        let state = stores[1].as_ref().unwrap().state();
        let crossed = Message {
            context: state.context(),
            dealer: 0,
            message: private_send::Message {
                context: [0; 32],
                body: Body::Request {
                    receiver: 2,
                    requester: 3,
                    phase: PhaseMessage::Init(vec![1]),
                },
            },
        };
        assert!(stores[1].as_mut().unwrap().receive(3, &crossed).is_err());
        // Corrupt sender0 disappears; f+1 real honest requests still drive delivery.
        for i in 1..4 {
            q.extend(
                stores[i]
                    .as_mut()
                    .unwrap()
                    .request_delivery()
                    .unwrap()
                    .into_iter()
                    .map(|p| (i as u16, p)),
            );
        }
        drive(&mut stores, &mut q, false, true);
        let state = stores[1].as_ref().unwrap().state();
        assert!(
            state.rejected_holders().contains(&0),
            "malformed ciphertext plaintext retained without rolling back RA"
        );
        assert_eq!(state.result().unwrap().bits(), &[false, true, true]);
        assert!(stores
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != 1)
            .all(|(_, s)| s.as_ref().unwrap().state().result().is_none()));
        drop(anchors);
    }
}
