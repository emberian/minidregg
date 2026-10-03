//! Actual crash-durable ACS driver. Each dealer coefficient vector and resulting
//! share/outbox is in the WAL before returned to the channel. Replay never obtains
//! new entropy for an already entered view. Static adversary, honest crash disk,
//! private authenticated reliable transport premises remain explicit.
use crate::{
    acs::{Acs, Message, Send},
    codec::{bad, Generation},
    consensus_wire::{self, Cursor},
    reconstruction::Field,
    transition_journal::{Journal, Machine},
};
use std::{
    fs::File,
    io::{Read, Result},
    path::Path,
};
#[derive(Clone)]
pub struct AcsMachine {
    pub state: Acs,
}
impl Machine for AcsMachine {
    fn apply(&mut self, event: &[u8]) -> Result<Vec<u8>> {
        let mut c = Cursor::new(event)?;
        let out = match c.byte()? {
            0 => {
                let index = c.u16()?;
                c.finish()?;
                self.state.validate(index)?
            }
            1 => {
                let view = c.u64()?;
                let mut coeff = vec![];
                // Supported two-coordinate GF128 suite, exactly degree f per coordinate.
                for _ in 0..2 {
                    let mut p = vec![];
                    for _ in 0..=self.state.f {
                        p.push(Field(u128::from_le_bytes(c.take(16)?.try_into().unwrap())))
                    }
                    coeff.push(p);
                }
                c.finish()?;
                self.state.dealer(view, &coeff)?
            }
            2 => {
                let sender = c.u16()?;
                let m = consensus_wire::decode_acs(&c.bytes()?, self.state.n)?;
                c.finish()?;
                self.state.receive(sender, m)?
            }
            _ => return Err(bad("ACS event tag")),
        };
        Ok(consensus_wire::encode_outbox(&out))
    }
}
pub struct Store {
    journal: Journal<AcsMachine>,
}
impl Store {
    pub fn open(path: &Path, me: u16, n: usize, f: usize, g: &Generation) -> Result<Self> {
        let state = Acs::new(me, n, f, g)?;
        let mut identity = b"DREGG.ACS.PARTY.V1".to_vec();
        g.put(&mut identity);
        identity.extend(me.to_le_bytes());
        identity.extend((n as u64).to_le_bytes());
        identity.extend((f as u64).to_le_bytes());
        Ok(Self {
            journal: Journal::open(path, &identity, AcsMachine { state })?,
        })
    }
    fn apply(&mut self, event: &[u8]) -> Result<Vec<Send>> {
        let out = self.journal.append(event)?;
        consensus_wire::decode_outbox(&out, self.state().n)
    }
    pub fn state(&self) -> &Acs {
        &self.journal.state().state
    }
    /// Caller supplies an actual monotone external validation completion, not a
    /// user boolean or malicious-AVSS qualification substitute.
    pub fn validate(&mut self, j: u16) -> Result<Vec<Send>> {
        let mut event = vec![0];
        event.extend(j.to_le_bytes());
        self.apply(&event)
    }
    /// Sender is the channel-authenticated peer, not the packet's selector dealer.
    pub fn receive(&mut self, sender: u16, m: &Message) -> Result<Vec<Send>> {
        let mut event = vec![2];
        event.extend(sender.to_le_bytes());
        crate::codec::bytes(&consensus_wire::encode_acs(m), &mut event);
        self.apply(&event)
    }
    pub fn start_pending(&mut self) -> Result<Vec<Send>> {
        let mut out = vec![];
        for view in self.state().entropy_needed() {
            let mut event = vec![1];
            event.extend(view.to_le_bytes());
            let mut random = vec![0u8; 2 * (self.state().f + 1) * 16];
            File::open("/dev/urandom")?.read_exact(&mut random)?;
            event.extend(random);
            out.extend(self.apply(&event)?);
        }
        Ok(out)
    }
    /// Durable outbox replay is safe to duplicate; transport must persist delivery
    /// cursors/ACKs before reclaiming. No destructive reclamation is implemented.
    pub fn replay_outboxes(&self) -> Result<Vec<Send>> {
        let mut out = vec![];
        for b in self.journal.replay_outboxes() {
            out.extend(consensus_wire::decode_outbox(b, self.state().n)?)
        }
        Ok(out)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::codec::Nat;
    use std::{
        fs,
        time::{SystemTime, UNIX_EPOCH},
    };
    fn path() -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!(
            "mini-acs-store-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&p).unwrap();
        p.join("journal")
    }
    fn g() -> Generation {
        Generation {
            invocation: Nat::from_be(&[254; 32]),
            command: vec![1],
            attempt: Nat::new(0),
            generation: Nat::new(1),
            configuration: Nat::new(7),
        }
    }
    #[test]
    fn dropped_dealer_reply_restores_exact_random_share_messages() {
        let p = path();
        let first;
        {
            let mut store = Store::open(&p, 1, 4, 1, &g()).unwrap();
            first = store.start_pending().unwrap();
            assert!(!first.is_empty());
        }
        let mut store = Store::open(&p, 1, 4, 1, &g()).unwrap();
        assert!(store.start_pending().unwrap().is_empty());
        assert_eq!(store.replay_outboxes().unwrap(), first);
    }
    #[test]
    fn changed_command_cannot_replay_same_party_protocol() {
        let p = path();
        {
            let mut s = Store::open(&p, 1, 4, 1, &g()).unwrap();
            s.start_pending().unwrap();
        }
        let mut wrong = g();
        wrong.command.push(9);
        assert!(Store::open(&p, 1, 4, 1, &wrong).is_err());
    }
}
