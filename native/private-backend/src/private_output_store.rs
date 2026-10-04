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
        stores_from_completed(completed, anchors, instance)
    }
    fn stores_from_completed(
        completed: Vec<crate::field_network_layers::LayerEngine>,
        anchors: Vec<crate::triple_king::tests::AnchorFixture>,
        instance: u64,
    ) -> (
        Vec<Option<Store>>,
        Vec<crate::triple_king::tests::AnchorFixture>,
        Vec<PathBuf>,
    ) {
        stores_from_completed_descriptor(
            completed,
            anchors,
            instance,
            b"fixed reference addition/result recipient1; no native release grant",
        )
    }
    fn stores_from_completed_descriptor(
        completed: Vec<crate::field_network_layers::LayerEngine>,
        anchors: Vec<crate::triple_king::tests::AnchorFixture>,
        instance: u64,
        descriptor: &[u8],
    ) -> (
        Vec<Option<Store>>,
        Vec<crate::triple_king::tests::AnchorFixture>,
        Vec<PathBuf>,
    ) {
        let paths = (0..4)
            .map(|i| path(&format!("{instance}-{i}")))
            .collect::<Vec<_>>();
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
    /// Restricted public-input integration fixture. An optional protected export
    /// consumes exact source-authored Generation bytes; it never enrolls a party,
    /// supplies source permission, or creates Qualified successor evidence.
    #[test]
    fn source_generation_bootstrap_retains_real_output_wal_and_recursive_packet() {
        use std::io::Write;
        use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
        let supplied = std::env::var_os("MINI_PRIVATE_SOURCE_GENERATION");
        let destination = std::env::var_os("MINI_PRIVATE_BOOTSTRAP_DEST");
        let source_descriptor = std::env::var_os("MINI_PRIVATE_SOURCE_DESCRIPTOR");
        assert_eq!(supplied.is_some(), destination.is_some());
        assert_eq!(supplied.is_some(), source_descriptor.is_some());
        let g = if let Some(path) = supplied {
            let raw = fs::read(path).unwrap();
            let mut reader = crate::codec::Reader::new(&raw).unwrap();
            let g = crate::codec::Generation::get(&mut reader).unwrap();
            reader.finish().unwrap();
            let mut canonical = vec![];
            g.put(&mut canonical);
            assert_eq!(canonical, raw);
            g
        } else {
            crate::codec::Generation {
                invocation: crate::codec::Nat::from_be(&[9; 64]),
                command: vec![6; 300],
                attempt: crate::codec::Nat::new(2),
                generation: crate::codec::Nat::new(1),
                configuration: crate::codec::Nat::from_be(&[7; 64]),
            }
        };
        // Canonical descriptor authority belongs to the source producer. Here
        // retain its entire original bytes and verify the exact generation prefix;
        // this mechanical comparison creates no source admission or recovery proof.
        let mut generation_bytes = vec![];
        g.put(&mut generation_bytes);
        let descriptor = if let Some(path) = source_descriptor {
            let raw = fs::read(path).unwrap();
            assert!(raw.len() > generation_bytes.len() && raw.len() <= 65536);
            assert!(raw.starts_with(&generation_bytes));
            raw
        } else {
            let mut raw = generation_bytes.clone();
            crate::codec::bytes(b"explicit unqualified reference descriptor", &mut raw);
            raw
        };
        let source = include_bytes!("../fixtures/addition-network-8-plan.bin");
        let network = crate::field_network::with_boolean_inputs(
            &crate::circuit_batch::Plan::decode(source).unwrap().network,
        )
        .unwrap();
        let (completed, anchors) = arithmetic_reference::tests::completed_word_network_generation(
            255,
            1,
            96,
            network,
            source,
            Some(&g),
        );
        let (mut stores, anchors, paths) =
            stores_from_completed_descriptor(completed, anchors, 96, &descriptor);
        let mut sent = vec![];
        for (i, s) in stores.iter_mut().enumerate() {
            let state = s.as_ref().unwrap().state();
            assert_eq!(state.generation(), &g);
            assert_eq!(state.descriptor_bytes(), descriptor);
            assert!(state.result().is_none());
            sent.push(s.as_mut().unwrap().start().unwrap());
            assert!(!sent[i].is_empty());
            assert_eq!(
                s.as_ref().unwrap().replay_outboxes().unwrap().len(),
                sent[i].len()
            );
        }
        let packet = sent[0].iter().find(|p| p.to == 1).unwrap();
        let wire = private_output::encode_message(&packet.message);
        assert_eq!(
            private_output::encode_message(&private_output::decode_message(&wire).unwrap()),
            wire
        );
        let context = stores[1].as_ref().unwrap().state().context();
        drop(stores[1].take());
        stores[1] = Some(Store::reopen(&paths[1], &g, context, 1, 1, anchors[1].socket()).unwrap());
        assert!(stores[1].as_ref().unwrap().state().result().is_none());
        assert_eq!(
            stores[1].as_ref().unwrap().state().descriptor_bytes(),
            descriptor
        );
        if let Some(destination) = destination {
            let root = PathBuf::from(destination);
            assert!(root.is_absolute() && !root.exists());
            fs::create_dir(&root).unwrap();
            fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
            fn write(path: &std::path::Path, bytes: &[u8]) {
                let mut f = fs::OpenOptions::new()
                    .write(true)
                    .create_new(true)
                    .mode(0o600)
                    .open(path)
                    .unwrap();
                f.write_all(bytes).unwrap();
                f.sync_all().unwrap();
                std::fs::File::open(path.parent().unwrap())
                    .unwrap()
                    .sync_all()
                    .unwrap();
                assert_eq!(fs::read(path).unwrap(), bytes);
            }
            let mut canonical = vec![];
            g.put(&mut canonical);
            write(&root.join("generation.bin"), &canonical);
            write(&root.join("source-descriptor.bin"), &descriptor);
            write(&root.join("message-sender0-recipient1.bin"), &wire);
            for i in 0..4 {
                let d = root.join(format!("party-{i}"));
                fs::create_dir(&d).unwrap();
                fs::set_permissions(&d, fs::Permissions::from_mode(0o700)).unwrap();
                let wal = fs::read(&paths[i]).unwrap();
                write(&d.join("output.wal"), &wal);
                write(
                    &d.join("output.initial"),
                    &fs::read(paths[i].with_extension("initial")).unwrap(),
                );
                write(
                    &d.join("output-context.bin"),
                    &stores[i].as_ref().unwrap().state().context(),
                );
                write(&d.join("output-bootstrap-sha256.bin"), &custody::hash(&wal));
                write(&d.join("source-descriptor.bin"), &descriptor);
                let a = d.join("anchor");
                fs::create_dir(&a).unwrap();
                fs::set_permissions(&a, fs::Permissions::from_mode(0o700)).unwrap();
                let original = anchors[i]
                    .socket()
                    .parent()
                    .unwrap()
                    .join("authority/authority.log");
                write(&a.join("authority.log"), &fs::read(original).unwrap());
                // Reopening the exported physical log proves its full spent prefix;
                // it does not invent a new monotonic deployment authority.
                let exported = custody::Anchor::open(&a).unwrap();
                let live = crate::codec::Journal::decode(
                    &custody::rpc(anchors[i].socket(), &[0]).unwrap(),
                )
                .unwrap();
                assert_eq!(exported.journal, live);
            }
            write(&root.join("PROFILE.txt"),b"PUBLIC255+1 reference integration fixture; actual ACSS/Sh2t/King/LayerMPC/output WAL; deterministic reference preprocessing, no general private-production entropy claim. All original outboxes/spent retained. No source authority, recipient enrollment, current release, Qualified successor, GOD/PQ claim.
");
        }
    }
    /// Complete current Objective identity source diagnostic. The public
    /// compiler emits full final state+handled, so this synthetic fixture checks
    /// the entire vector at its sole diagnostic recipient. Production audiences
    /// require a separate authorized result projection and fresh release law.
    #[test]
    fn actual_compiler_origin_objective_identity_acss_mpc_private_diagnostic_recovery() {
        use crate::codec::{bytes, Correlation, Generation, Nat};
        let source = include_bytes!("../fixtures/objective-identity-source.bin");
        let network_bytes = include_bytes!("../fixtures/objective-identity-network.bin");
        let input = include_bytes!("../fixtures/objective-identity-input.bin");
        let expected = include_bytes!("../fixtures/objective-identity-expected.bin");
        assert_eq!(input.len(), 153);
        assert_eq!(expected.len(), 154);
        assert!(input.iter().chain(expected.iter()).all(|b| *b <= 1));
        let g = Generation {
            invocation: Nat::new(7101),
            command: source.to_vec(),
            attempt: Nat::new(0),
            generation: Nat::new(1),
            configuration: Nat::from_be(&crate::custody::hash(source)),
        };
        // Surround exact actual Lean-produced network bytes with an explicitly
        // synthetic Rust Plan; no alleged source-produced allocation authority.
        let mut encoded = vec![];
        bytes(b"DREGG.PRIVATE.CIRCUIT.ALLOCATION\x01", &mut encoded);
        g.put(&mut encoded);
        encoded.extend_from_slice(network_bytes);
        Nat::new(1).put(&mut encoded);
        bytes(source, &mut encoded);
        Nat::new(13563).put(&mut encoded);
        for i in 0..13563 {
            Correlation {
                pool: Nat::new(0),
                row: Nat::new(i),
            }
            .put(&mut encoded);
        }
        let public = crate::circuit_batch::Plan::decode(&encoded).unwrap();
        assert_eq!(public.encode(), encoded);
        assert_eq!(public.network.gates.len(), 34696);
        assert_eq!(public.network.outputs.len(), 154);
        let network = crate::field_network::with_boolean_inputs(&public.network).unwrap();
        assert_eq!(
            network
                .gates
                .iter()
                .filter(|v| matches!(v, crate::circuit_batch::Op::And(..)))
                .count(),
            13716
        );
        let bits = input.iter().map(|b| *b == 1).collect::<Vec<_>>();
        eprintln!(
            "public Objective identity:153 ACSS inputs,429 checked stocks,13716 anchored tuples"
        );
        let (completed, anchors) = arithmetic_reference::tests::completed_boolean_network_many(
            &bits, 7200, network, source, &g,
        );
        eprintln!("public Objective identity: actual LayerMPC completed, beginning private diagnostic delivery");
        let (mut stores,anchors,paths)=stores_from_completed_descriptor(completed,anchors,7200,
            b"public Objective identity synthetic whole-state diagnostic; no native release or successor qualification");
        let mut q = VecDeque::new();
        for (holder, store) in stores.iter_mut().enumerate() {
            q.extend(
                store
                    .as_mut()
                    .unwrap()
                    .start()
                    .unwrap()
                    .into_iter()
                    .map(|p| (holder as u16, p)),
            );
        }
        drive(&mut stores, &mut q, false, false);
        for (holder, store) in stores.iter_mut().enumerate() {
            q.extend(
                store
                    .as_mut()
                    .unwrap()
                    .request_delivery()
                    .unwrap()
                    .into_iter()
                    .map(|p| (holder as u16, p)),
            );
        }
        drive(&mut stores, &mut q, false, false);
        let wanted = expected.iter().map(|b| *b == 1).collect::<Vec<_>>();
        let result = stores[1].as_ref().unwrap().state().result().unwrap();
        assert_eq!(result.bits(), wanted);
        assert!(result.bits()[0] && !result.bits()[1]);
        assert_eq!(&result.bits()[2..5], &[true, false, true]);
        assert_eq!(&result.bits()[14..17], &[true, false, false]);
        assert_eq!(
            &result.bits()[17..20],
            &[true, true, false],
            "actual current Objective Nat3"
        );
        for holder in [0, 2, 3] {
            assert!(stores[holder].as_ref().unwrap().state().result().is_none());
        }
        let context = stores[1].as_ref().unwrap().state().context();
        drop(stores[1].take());
        stores[1] = Some(Store::reopen(&paths[1], &g, context, 1, 1, anchors[1].socket()).unwrap());
        assert_eq!(
            stores[1].as_ref().unwrap().state().result().unwrap().bits(),
            wanted
        );
    }
    #[test]
    fn actual_170_boolean_inputs_distinct_acss_chunks_checked_stocks_private_result() {
        let bits = (0..170).map(|i| i % 7 == 0).collect::<Vec<_>>();
        let mut raw = crate::circuit_batch::Network {
            input_count: 170,
            gates: vec![crate::circuit_batch::Op::Constant(false)],
            outputs: vec![],
        };
        let mut accumulator = 170;
        for input in 0..170 {
            let next = raw.input_count + raw.gates.len() as u64;
            raw.gates
                .push(crate::circuit_batch::Op::Xor(accumulator, input));
            accumulator = next;
        }
        raw.outputs.push(accumulator);
        let network = crate::field_network::with_boolean_inputs(&raw).unwrap();
        let g = crate::codec::Generation {
            invocation: crate::codec::Nat::new(7001),
            command: b"fixed public170 parity reference".to_vec(),
            attempt: crate::codec::Nat::new(0),
            generation: crate::codec::Nat::new(1),
            configuration: crate::codec::Nat::new(7001),
        };
        let (completed, anchors) = arithmetic_reference::tests::completed_boolean_network_many(
            &bits,
            700,
            network,
            b"public fixed170 input capacity/parity; no Objective or native authority",
            &g,
        );
        let (mut stores, anchors, paths) = stores_from_completed(completed, anchors, 700);
        let mut q = VecDeque::new();
        for (holder, store) in stores.iter_mut().enumerate() {
            q.extend(
                store
                    .as_mut()
                    .unwrap()
                    .start()
                    .unwrap()
                    .into_iter()
                    .map(|p| (holder as u16, p)),
            );
        }
        drive(&mut stores, &mut q, false, false);
        for (holder, store) in stores.iter_mut().enumerate() {
            q.extend(
                store
                    .as_mut()
                    .unwrap()
                    .request_delivery()
                    .unwrap()
                    .into_iter()
                    .map(|p| (holder as u16, p)),
            );
        }
        drive(&mut stores, &mut q, false, false);
        let expected = bits.iter().fold(false, |a, b| a ^ b);
        assert!(expected);
        assert_eq!(
            stores[1].as_ref().unwrap().state().result().unwrap().bits(),
            &[expected]
        );
        for holder in [0, 2, 3] {
            assert!(stores[holder].as_ref().unwrap().state().result().is_none());
        }
        let context = stores[1].as_ref().unwrap().state().context();
        drop(stores[1].take());
        stores[1] = Some(Store::reopen(&paths[1], &g, context, 1, 1, anchors[1].socket()).unwrap());
        assert_eq!(
            stores[1].as_ref().unwrap().state().result().unwrap().bits(),
            &[expected]
        );
    }
    #[test]
    fn actual_generic_lean_width8_private_addition_full_carry_and_recovery() {
        let bytes = include_bytes!("../fixtures/addition-network-8-plan.bin");
        let fixture = crate::circuit_batch::Plan::decode(bytes).unwrap();
        assert_eq!(fixture.encode(), bytes);
        assert_eq!(fixture.network.input_count, 16);
        assert_eq!(fixture.network.gates.len(), 41);
        assert_eq!(
            fixture.network.outputs,
            vec![18, 23, 28, 33, 38, 43, 48, 53, 56]
        );
        assert_eq!(fixture.public_ticks, 1);
        assert_eq!(fixture.rows.len(), 16);
        let network = crate::field_network::with_boolean_inputs(&fixture.network).unwrap();
        assert_eq!(network.gates.len(), 74);
        let (completed, anchors) =
            arithmetic_reference::tests::completed_word_network(255, 1, 85, network, bytes);
        let (mut stores, anchors, paths) = stores_from_completed(completed, anchors, 85);
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
        drive(&mut stores, &mut q, false, false);
        assert!(stores
            .iter()
            .all(|s| s.as_ref().unwrap().state().result().is_none()));
        // Reference release environment, not a fabricated Native grant.
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
        let state = stores[1].as_ref().unwrap().state();
        let g = state.generation().clone();
        let context = state.context();
        let expected = vec![false, false, false, false, false, false, false, false, true];
        assert_eq!(state.result().unwrap().bits(), &expected);
        assert!(stores
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != 1)
            .all(|(_, s)| s.as_ref().unwrap().state().result().is_none()));
        drop(stores[1].take());
        let reopened = Store::reopen(&paths[1], &g, context, 1, 1, anchors[1].socket()).unwrap();
        assert_eq!(reopened.state().result().unwrap().bits(), &expected);
        assert_eq!(
            expected
                .iter()
                .enumerate()
                .fold(0u16, |v, (i, b)| v | ((*b as u16) << i)),
            256
        );
    }
    #[test]
    fn actual_lean_compiler_addition_graph_private_result_and_recipient_recovery() {
        let bytes = include_bytes!("../fixtures/addition-network-2-plan.bin");
        let fixture = crate::circuit_batch::Plan::decode(bytes).unwrap();
        assert_eq!(fixture.encode(), bytes);
        assert_eq!(fixture.network.input_count, 4);
        assert_eq!(fixture.network.gates.len(), 11);
        assert_eq!(fixture.network.outputs, vec![6, 11, 14]);
        assert_eq!(fixture.public_ticks, 1);
        assert_eq!(fixture.rows.len(), 4);
        let network = crate::field_network::with_boolean_inputs(&fixture.network).unwrap();
        assert_eq!(network.gates.len(), 20);
        let (completed, anchors) =
            arithmetic_reference::tests::completed_network(3, 3, 84, network, bytes);
        let (mut stores, anchors, paths) = stores_from_completed(completed, anchors, 84);
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
        drive(&mut stores, &mut q, false, false);
        assert!(stores
            .iter()
            .all(|s| s.as_ref().unwrap().state().result().is_none()));
        // Explicit reference environment release request. Native current
        // audience/AppliedReady admission remains independently required.
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
        let state = stores[1].as_ref().unwrap().state();
        let g = state.generation().clone();
        let context = state.context();
        assert_eq!(state.result().unwrap().bits(), &[false, true, true]);
        assert!(stores
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != 1)
            .all(|(_, s)| s.as_ref().unwrap().state().result().is_none()));
        drop(stores[1].take());
        let recovered = Store::reopen(&paths[1], &g, context, 1, 1, anchors[1].socket()).unwrap();
        assert_eq!(
            recovered.state().result().unwrap().bits(),
            &[false, true, true]
        );
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
