//! Original typed field-machine initialization + deterministic event/outbox WAL.
//! Honest endpoint-private crash storage and retained full-plan anchor are premises.
//! Restore is passive protocol recovery, NOT reachability from arbitrary bytes,
//! Native authorization, successor privateRecovery or permission to dispatch.
use crate::{
    circuit_batch::Plan,
    codec::{bad, bytes},
    consensus_wire::Cursor,
    custody,
    field_network::{Message, Send},
    transition_journal::{Journal, Machine},
};
use std::{
    fs::File,
    io::{Read, Result},
    path::{Path, PathBuf},
};
mod runtime_seal {
    pub trait Sealed {}
    impl Sealed for crate::field_network_layers::LayerEngine {}
}
/// Closed runtime family, not a callback-based cryptographic qualification.
pub trait FieldRuntime: runtime_seal::Sealed + Clone {
    fn plan(&self) -> &Plan;
    fn holder(&self) -> u16;
    fn roster(&self) -> (usize, usize);
    fn initial_bytes(&self) -> Result<Vec<u8>>;
    fn restore_initial(b: &[u8], p: &Plan, h: u16, anchor: &Path) -> Result<Self>;
    fn start(&mut self) -> Result<Vec<Send>>;
    fn receive(&mut self, sender: u16, m: Message) -> Result<Vec<Send>>;
    fn encode_message(m: &Message) -> Vec<u8>;
    fn decode_message(b: &[u8]) -> Result<Message>;
    fn wal_domain() -> &'static [u8];
    fn file_domain() -> &'static [u8];
}
impl FieldRuntime for crate::field_network_layers::LayerEngine {
    fn plan(&self) -> &Plan {
        Self::plan(self)
    }
    fn holder(&self) -> u16 {
        Self::holder(self)
    }
    fn roster(&self) -> (usize, usize) {
        Self::roster(self)
    }
    fn initial_bytes(&self) -> Result<Vec<u8>> {
        Self::initial_bytes(self)
    }
    fn restore_initial(b: &[u8], p: &Plan, h: u16, a: &Path) -> Result<Self> {
        Self::restore_initial(b, p, h, a)
    }
    fn start(&mut self) -> Result<Vec<Send>> {
        Self::start(self)
    }
    fn receive(&mut self, s: u16, m: Message) -> Result<Vec<Send>> {
        Self::receive(self, s, m)
    }
    fn encode_message(m: &Message) -> Vec<u8> {
        crate::field_network_layers::encode_message(m)
    }
    fn decode_message(b: &[u8]) -> Result<Message> {
        crate::field_network_layers::decode_message(b)
    }
    fn wal_domain() -> &'static [u8] {
        b"DREGG.PRIVATE.FIELD.LAYERS.PARTY.WAL\x01"
    }
    fn file_domain() -> &'static [u8] {
        b"DREGG.PRIVATE.FIELD.LAYERS.INIT.FILE\x01"
    }
}
#[derive(Clone)]
pub struct RuntimeMachine<R: FieldRuntime> {
    pub state: R,
}
fn outbox<R: FieldRuntime>(ps: &[Send]) -> Vec<u8> {
    crate::consensus_wire::put_outbox(ps, R::encode_message)
}
fn decode_outbox_for<R: FieldRuntime>(b: &[u8], n: usize) -> Result<Vec<Send>> {
    crate::consensus_wire::get_outbox(b, n, 65536, "field", R::decode_message, R::encode_message)
}
impl<R: FieldRuntime> Machine for RuntimeMachine<R> {
    fn apply(&mut self, event: &[u8]) -> Result<Vec<u8>> {
        let mut c = Cursor::new(event)?;
        let out = match c.byte()? {
            0 => {
                c.finish()?;
                self.state.start()?
            }
            2 => {
                let sender = c.u16()?;
                let m = R::decode_message(&c.bytes()?)?;
                c.finish()?;
                self.state.receive(sender, m)?
            }
            _ => return Err(bad("field event tag")),
        };
        Ok(outbox::<R>(&out))
    }
}
impl<R: FieldRuntime> crate::authenticated_ingress::IngressMachine for RuntimeMachine<R> {
    fn validate_ingress_context(
        &self,
        c: &crate::authenticated_ingress::Context,
        n: usize,
    ) -> Result<()> {
        if c.protocol != crate::authenticated_ingress::Protocol::FieldNetwork
            || c.recipient != self.state.holder()
            || c.generation != self.state.plan().generation
            || n != self.state.roster().0
        {
            return Err(bad("field actual receiver generation/plan holder"));
        }
        Ok(())
    }
}
pub struct RuntimeStore<R: FieldRuntime> {
    journal: Journal<RuntimeMachine<R>>,
    _initial_lock: File,
    n: usize,
}
pub type LayerStore = RuntimeStore<crate::field_network_layers::LayerEngine>;
fn initial_path(path: &Path) -> PathBuf {
    path.with_extension("initial")
}
fn identity<R: FieldRuntime>(initial: &[u8]) -> Vec<u8> {
    let mut b = R::wal_domain().to_vec();
    b.extend(custody::hash(initial));
    b
}
impl<R: FieldRuntime> RuntimeStore<R> {
    /// Takes an actual fully burned/typed Engine. Original private initialization
    /// is written before any protocol effect/outbox is returned. Existing files
    /// refuse; crash recovery uses reopen rather than regenerating material.
    pub fn create(path: &Path, state: R) -> Result<Self> {
        let guard = custody::lock(&path.with_extension("initial.lock"))?;
        if path.exists() {
            return Err(bad("field WAL already exists; recover original"));
        }
        let initial = state.initial_bytes()?;
        let mut framed = R::file_domain().to_vec();
        bytes(&initial, &mut framed);
        framed.extend(custody::hash(&framed));
        if framed.len() > crate::codec::MAX {
            return Err(bad("field initial framed capacity"));
        }
        let initial_file = initial_path(path);
        crate::private_initial::write_new_durable(&initial_file, &framed)?;
        let n = state.roster().0;
        let journal = Journal::open(path, &identity::<R>(&initial), RuntimeMachine { state })?;
        Ok(Self {
            journal,
            _initial_lock: guard,
            n,
        })
    }
    pub fn reopen(path: &Path, expected_plan: &Plan, holder: u16, anchor: &Path) -> Result<Self> {
        let guard = custody::lock(&path.with_extension("initial.lock"))?;
        let mut f = File::open(initial_path(path))?;
        if f.metadata()?.len() > crate::codec::MAX as u64 + 100 {
            return Err(bad("field initial file bound"));
        }
        let mut framed = vec![];
        f.read_to_end(&mut framed)?;
        if framed.len() < 32 {
            return Err(bad("field initial incomplete; source repair required"));
        }
        let end = framed.len() - 32;
        if custody::hash(&framed[..end]) != framed[end..] {
            return Err(bad("field initial checksum"));
        }
        let mut c = Cursor::new(&framed[..end])?;
        let tag = R::file_domain();
        if c.take(tag.len())? != tag {
            return Err(bad("field initial file frame"));
        }
        let initial = c.bytes()?;
        c.finish()?;
        let state = R::restore_initial(&initial, expected_plan, holder, anchor)?;
        let n = state.roster().0;
        Ok(Self {
            journal: Journal::open(path, &identity::<R>(&initial), RuntimeMachine { state })?,
            _initial_lock: guard,
            n,
        })
    }
    pub fn state(&self) -> &R {
        &self.journal.state().state
    }
    pub fn start(&mut self) -> Result<Vec<Send>> {
        decode_outbox_for::<R>(&self.journal.append(&[0])?, self.n)
    }
    /// Sender has already passed the actual original-prefix endpoint authority.
    /// This low-level store does not implement that authority by accepting u16.
    pub fn receive(&mut self, sender: u16, m: &Message) -> Result<Vec<Send>> {
        let mut e = vec![2];
        e.extend(sender.to_le_bytes());
        bytes(&R::encode_message(m), &mut e);
        decode_outbox_for::<R>(&self.journal.append(&e)?, self.n)
    }
    pub fn replay_outboxes(&self) -> Result<Vec<Send>> {
        let mut ps = vec![];
        for b in self.journal.replay_outboxes() {
            ps.extend(decode_outbox_for::<R>(b, self.n)?);
        }
        Ok(ps)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field_network_layers::LayerEngine;
    use std::fs;
    use crate::reconstruction::Field;
    use std::{
        time::{SystemTime, UNIX_EPOCH},
    };
    fn path(label: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "mini-field-store-{label}-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&dir).unwrap();
        dir.join("events")
    }
    #[test]
    fn original_initialization_corruption_or_missing_anchor_refuses_recovery() {
        let (mut engines, anchors) = crate::field_network::tests::engine_nodes(Field(1), Field(0));
        let engine = engines.remove(0);
        let plan = engine.plan().clone();
        let p = path("initial");
        drop(LayerStore::create(&p, LayerEngine::new(engine).unwrap()).unwrap());
        let initial = fs::read(initial_path(&p)).unwrap();
        let mut changed = initial.clone();
        let index = changed.len() - 40;
        changed[index] ^= 1;
        fs::write(initial_path(&p), changed).unwrap();
        assert!(LayerStore::reopen(&p, &plan, 0, anchors[0].socket()).is_err());
        fs::write(initial_path(&p), &initial).unwrap();
        let (_empty, socket, _root) =
            crate::triple_king::tests::evaluator_anchor("missing-field-prefix");
        assert!(LayerStore::reopen(&p, &plan, 0, &socket).is_err());
        assert!(LayerStore::reopen(&p, &plan, 0, anchors[0].socket()).is_ok());
    }
}

#[cfg(test)]
mod pin_wire {
    use super::*;
    use crate::asks::PhaseMessage as PinPhase;
    fn pin_sends() -> Vec<Send> {
        vec![
            Send { to: 1, message: Message { context: [7; 32], body: crate::field_network::Body::Bits { holder: 1, phase: PinPhase::Echo(vec![1]) } } },
            Send { to: 3, message: Message { context: [7; 32], body: crate::field_network::Body::Bits { holder: 1, phase: PinPhase::Ready(vec![1]) } } },
        ]
    }
    /// Outbox wire: Nat count, then per packet u16 LE recipient and the
    /// length-prefixed message wire; canonical, bounded, recipient-checked.
    #[test]
    fn pin_outbox_wire() {
        let ps = pin_sends();
        let b = outbox::<crate::field_network_layers::LayerEngine>(&ps);
        let mut want = vec![2, 255];
        for s in &ps {
            want.extend(s.to.to_le_bytes());
            let m = <crate::field_network_layers::LayerEngine as FieldRuntime>::encode_message(&s.message);
            crate::codec::Nat::new(m.len() as u64).put(&mut want);
            want.extend(m);
        }
        assert_eq!(&b[..4], &[2, 255, 1, 0]);
        assert_eq!(b, want);
        assert_eq!(decode_outbox_for::<crate::field_network_layers::LayerEngine>(&b, 4).unwrap(), ps);
        assert!(decode_outbox_for::<crate::field_network_layers::LayerEngine>(&b, 3).is_err(), "recipient 3 is outside n = 3");
        let mut trailing = b.clone();
        trailing.push(0);
        let b = trailing;
        assert!(decode_outbox_for::<crate::field_network_layers::LayerEngine>(&b, 4).is_err(), "trailing bytes refuse");
        let mut huge = vec![];
        crate::codec::Nat::new(crate::codec::MAX as u64).put(&mut huge);
        let b = huge;
        assert!(decode_outbox_for::<crate::field_network_layers::LayerEngine>(&b, 4).is_err(), "an absurd count refuses");
    }
}
