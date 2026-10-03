//! Original typed field-machine initialization + deterministic event/outbox WAL.
//! Honest endpoint-private crash storage and retained full-plan anchor are premises.
//! Restore is passive protocol recovery, NOT reachability from arbitrary bytes,
//! Native authorization, successor privateRecovery or permission to dispatch.
use crate::{
    circuit_batch::Plan,
    codec::{bad, bytes, Nat},
    consensus_wire::Cursor,
    custody,
    field_network::{self, Engine, Message, Send},
    transition_journal::{Journal, Machine},
};
use std::{
    fs::{self, File, OpenOptions},
    io::{Read, Result, Write},
    os::unix::fs::OpenOptionsExt,
    path::{Path, PathBuf},
};
#[derive(Clone)]
pub struct FieldMachine {
    pub state: Engine,
}
fn outbox(ps: &[Send]) -> Vec<u8> {
    let mut b = vec![];
    Nat::new(ps.len() as u64).put(&mut b);
    for p in ps {
        b.extend(p.to.to_le_bytes());
        bytes(&field_network::encode_message(&p.message), &mut b);
    }
    b
}
pub fn decode_outbox(b: &[u8], n: usize) -> Result<Vec<Send>> {
    let mut c = Cursor::new(b)?;
    let mut ds = vec![];
    loop {
        let v = c.byte()?;
        ds.push(v);
        if v == 255 {
            break;
        }
    }
    let mut r = crate::codec::Reader::new(&ds)?;
    let count = r.count()?;
    r.finish()?;
    if count > 65536 {
        return Err(bad("field outbox count"));
    }
    let mut ps = vec![];
    for _ in 0..count {
        let to = c.u16()?;
        if to as usize >= n {
            return Err(bad("field outbox recipient"));
        }
        ps.push(Send {
            to,
            message: field_network::decode_message(&c.bytes()?)?,
        });
    }
    c.finish()?;
    if outbox(&ps) != b {
        return Err(bad("field outbox canonical"));
    }
    Ok(ps)
}
impl Machine for FieldMachine {
    fn apply(&mut self, event: &[u8]) -> Result<Vec<u8>> {
        let mut c = Cursor::new(event)?;
        let out = match c.byte()? {
            0 => {
                c.finish()?;
                self.state.start()?
            }
            2 => {
                let sender = c.u16()?;
                let m = field_network::decode_message(&c.bytes()?)?;
                c.finish()?;
                self.state.receive(sender, m)?
            }
            _ => return Err(bad("field event tag")),
        };
        Ok(outbox(&out))
    }
}
impl crate::authenticated_ingress::IngressMachine for FieldMachine {
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
pub struct Store {
    journal: Journal<FieldMachine>,
    _initial_lock: File,
    n: usize,
}
fn initial_path(path: &Path) -> PathBuf {
    path.with_extension("initial")
}
fn identity(initial: &[u8]) -> Vec<u8> {
    let mut b = b"DREGG.PRIVATE.FIELD.PARTY.WAL\x01".to_vec();
    b.extend(custody::hash(initial));
    b
}
impl Store {
    /// Takes an actual fully burned/typed Engine. Original private initialization
    /// is fsynced before any protocol effect/outbox is returned. Existing files
    /// refuse; crash recovery uses reopen rather than regenerating material.
    pub fn create(path: &Path, state: Engine) -> Result<Self> {
        let guard = custody::lock(&path.with_extension("initial.lock"))?;
        if path.exists() {
            return Err(bad("field WAL already exists; recover original"));
        }
        let initial = state.initial_bytes()?;
        let mut framed = b"DREGG.PRIVATE.FIELD.INIT.FILE\x01".to_vec();
        bytes(&initial, &mut framed);
        framed.extend(custody::hash(&framed));
        if framed.len() > crate::codec::MAX {
            return Err(bad("field initial framed capacity"));
        }
        let initial_file = initial_path(path);
        let mut f = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&initial_file)?;
        f.write_all(&framed)?;
        f.sync_all()?;
        File::open(
            initial_file
                .parent()
                .ok_or_else(|| bad("field initial parent"))?,
        )?
        .sync_all()?;
        if fs::read(&initial_file)? != framed {
            return Err(bad("field initial durable readback"));
        }
        let n = state.roster().0;
        let journal = Journal::open(path, &identity(&initial), FieldMachine { state })?;
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
        let tag = b"DREGG.PRIVATE.FIELD.INIT.FILE\x01";
        if c.take(tag.len())? != tag {
            return Err(bad("field initial file frame"));
        }
        let initial = c.bytes()?;
        c.finish()?;
        let state = Engine::restore_initial(&initial, expected_plan, holder, anchor)?;
        let n = state.roster().0;
        Ok(Self {
            journal: Journal::open(path, &identity(&initial), FieldMachine { state })?,
            _initial_lock: guard,
            n,
        })
    }
    pub fn state(&self) -> &Engine {
        &self.journal.state().state
    }
    pub fn start(&mut self) -> Result<Vec<Send>> {
        decode_outbox(&self.journal.append(&[0])?, self.n)
    }
    /// Sender has already passed the actual original-prefix endpoint authority.
    /// This low-level store does not implement that authority by accepting u16.
    pub fn receive(&mut self, sender: u16, m: &Message) -> Result<Vec<Send>> {
        let mut e = vec![2];
        e.extend(sender.to_le_bytes());
        bytes(&field_network::encode_message(m), &mut e);
        decode_outbox(&self.journal.append(&e)?, self.n)
    }
    pub fn replay_outboxes(&self) -> Result<Vec<Send>> {
        let mut ps = vec![];
        for b in self.journal.replay_outboxes() {
            ps.extend(decode_outbox(b, self.n)?);
        }
        Ok(ps)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reconstruction::Field;
    use std::{
        collections::VecDeque,
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
    fn actual_field_machine_restart_replays_original_outbox_and_completes() {
        let (engines, anchors) = crate::field_network::tests::engine_nodes(Field(1), Field(1));
        let plans = engines.iter().map(|e| e.plan().clone()).collect::<Vec<_>>();
        let paths = (0..4)
            .map(|i| path(&format!("node-{i}")))
            .collect::<Vec<_>>();
        let mut stores = engines
            .into_iter()
            .enumerate()
            .map(|(i, e)| Some(Store::create(&paths[i], e).unwrap()))
            .collect::<Vec<_>>();
        let mut q = VecDeque::new();
        let mut old = vec![];
        for (i, s) in stores.iter_mut().enumerate() {
            let ps = s.as_mut().unwrap().start().unwrap();
            if i == 1 {
                old = ps.clone();
            }
            q.extend(ps.into_iter().map(|p| (i as u16, p)));
        }
        let length = fs::metadata(&paths[1]).unwrap().len();
        drop(stores[1].take());
        let mut wrong = plans[1].clone();
        wrong.generation.command.push(0);
        assert!(Store::reopen(&paths[1], &wrong, 1, anchors[1].socket()).is_err());
        assert!(Store::reopen(&paths[1], &plans[1], 2, anchors[1].socket()).is_err());
        let reopened = Store::reopen(&paths[1], &plans[1], 1, anchors[1].socket()).unwrap();
        assert_eq!(reopened.replay_outboxes().unwrap(), old);
        assert_eq!(fs::metadata(&paths[1]).unwrap().len(), length);
        // Retained retransmit, no rerandomization or new material reservation.
        q.extend(old.into_iter().map(|p| (1, p)));
        stores[1] = Some(reopened);
        let mut steps = 0;
        while let Some((from, p)) = q.pop_front() {
            steps += 1;
            assert!(steps < 200000);
            let to = p.to;
            q.extend(
                stores[to as usize]
                    .as_mut()
                    .unwrap()
                    .receive(from, &p.message)
                    .unwrap()
                    .into_iter()
                    .map(|p| (to, p)),
            );
        }
        for (i, s) in stores.iter().enumerate() {
            assert!(s.as_ref().unwrap().state().output().is_some());
            assert_eq!(
                crate::codec::Journal::decode(&custody::rpc(anchors[i].socket(), &[0]).unwrap())
                    .unwrap()
                    .allocations
                    .len(),
                3
            );
        }
        let points = stores
            .iter()
            .take(2)
            .enumerate()
            .map(|(i, s)| {
                (
                    i as u16,
                    s.as_ref()
                        .unwrap()
                        .state()
                        .output()
                        .unwrap()
                        .shares()
                        .to_vec(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            crate::acss_id::polynomial(&points, 1).unwrap()[0][0],
            Field(1)
        );
        drop(stores[1].take());
        let mut reopened = Store::reopen(&paths[1], &plans[1], 1, anchors[1].socket()).unwrap();
        assert!(reopened.state().output().is_some());
        assert!(
            reopened.start().unwrap().is_empty(),
            "complete replay must not emit another masked opening"
        );
    }
    #[test]
    fn original_initialization_corruption_or_missing_anchor_refuses_recovery() {
        let (mut engines, anchors) = crate::field_network::tests::engine_nodes(Field(1), Field(0));
        let engine = engines.remove(0);
        let plan = engine.plan().clone();
        let p = path("initial");
        drop(Store::create(&p, engine).unwrap());
        let initial = fs::read(initial_path(&p)).unwrap();
        let mut changed = initial.clone();
        let index = changed.len() - 40;
        changed[index] ^= 1;
        fs::write(initial_path(&p), changed).unwrap();
        assert!(Store::reopen(&p, &plan, 0, anchors[0].socket()).is_err());
        fs::write(initial_path(&p), &initial).unwrap();
        let (_empty, socket, _root) =
            crate::triple_king::tests::evaluator_anchor("missing-field-prefix");
        assert!(Store::reopen(&p, &plan, 0, &socket).is_err());
        assert!(Store::reopen(&p, &plan, 0, anchors[0].socket()).is_ok());
    }
}
