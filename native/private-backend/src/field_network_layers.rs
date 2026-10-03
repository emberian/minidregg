//! Actual vector masked openings by PUBLIC AND dependency layers. Exact Plan
//! gate->row assignments are unchanged. All material comes from a pristine
//! whole-plan-burned Engine; no ideal multiplication/private getter callback.
//! Static f<n/3/classical ROM/reference variable-time GF128 and independently
//! authenticated confidential party channels remain premises. This does not
//! construct native admission, GOD, audience release or successor privateRecovery.
use crate::{
    acss_id,
    asks::{Bracha, PhaseMessage},
    circuit_batch::{Network, Op, Plan},
    codec::{bad, bytes, Nat},
    consensus_wire::Cursor,
    custody::hash,
    field_network::{
        self, bit_prefix, field_bytes, fields, values, BitnessFailure, Body, Engine, Message, Send,
    },
    reconstruction::Field,
};
use std::{collections::BTreeMap, io::Result};

/// Public vector capacity, irrespective of witness/refusal/early completion.
pub const MAX_BATCH_ANDS: usize = 1024;
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Schedule {
    pub batches: Vec<Vec<usize>>,
    pub and_depth: usize,
    tuple_positions: Vec<Option<usize>>,
}
impl Schedule {
    pub fn for_network(net: &Network) -> Result<Self> {
        if net.input_count > 65536 || net.gates.len() > 65536 {
            return Err(bad("layer graph capacity"));
        }
        let mut depths = vec![0usize; net.input_count as usize];
        let mut by_depth: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        let mut tuple_positions = vec![];
        let mut tuples = 0;
        for (index, op) in net.gates.iter().enumerate() {
            let depth = match op {
                Op::Constant(_) => 0,
                Op::Xor(a, b) | Op::And(a, b) => {
                    if *a >= depths.len() as u64 || *b >= depths.len() as u64 {
                        return Err(bad("layer forward operand"));
                    }
                    let d = depths[*a as usize].max(depths[*b as usize]);
                    if matches!(op, Op::And(..)) {
                        d + 1
                    } else {
                        d
                    }
                }
            };
            if matches!(op, Op::And(..)) {
                by_depth.entry(depth).or_default().push(index);
                tuple_positions.push(Some(tuples));
                tuples += 1;
            } else {
                tuple_positions.push(None);
            }
            depths.push(depth);
        }
        if net.outputs.iter().any(|w| *w >= depths.len() as u64) {
            return Err(bad("layer output range"));
        }
        let and_depth = by_depth.keys().copied().max().unwrap_or(0);
        let batches = by_depth
            .values()
            .flat_map(|positions| positions.chunks(MAX_BATCH_ANDS).map(|x| x.to_vec()))
            .collect();
        Ok(Self {
            batches,
            and_depth,
            tuple_positions,
        })
    }
    pub fn encode(&self) -> Vec<u8> {
        let mut b = b"DREGG.PRIVATE.FIELD.LAYERS.SCHEDULE\x01".to_vec();
        Nat::new(MAX_BATCH_ANDS as u64).put(&mut b);
        Nat::new(self.batches.len() as u64).put(&mut b);
        for batch in &self.batches {
            Nat::new(batch.len() as u64).put(&mut b);
            for gate in batch {
                Nat::new(*gate as u64).put(&mut b);
            }
        }
        b
    }
}
#[derive(Clone)]
pub struct SharedOutput {
    context: [u8; 32],
    holder: u16,
    values: Vec<Field>,
}
impl SharedOutput {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn holder(&self) -> u16 {
        self.holder
    }
    /// Endpoint-local shares only; no public/audience release grant.
    pub fn shares(&self) -> &[Field] {
        &self.values
    }
}
#[derive(Clone)]
pub struct LayerEngine {
    origin: Engine,
    context: [u8; 32],
    schedule: Schedule,
    wires: Vec<Option<Field>>,
    triples: Vec<(Field, Field, Field)>,
    bit_positions: Vec<usize>,
    me: u16,
    n: usize,
    f: usize,
    next_batch: usize,
    started: bool,
    opening_sent: bool,
    openings: BTreeMap<(usize, u16), Bracha>,
    bits: Vec<Bracha>,
    bits_sent: bool,
    output: Option<SharedOutput>,
    failure: Option<BitnessFailure>,
}
impl LayerEngine {
    pub fn new(origin: Engine) -> Result<Self> {
        let (input, triples) = origin.pristine_material()?;
        let mut wires = input.iter().copied().map(Some).collect::<Vec<_>>();
        wires.resize(input.len() + origin.plan().network.gates.len(), None);
        let schedule = Schedule::for_network(&origin.plan().network)?;
        if schedule
            .tuple_positions
            .iter()
            .filter(|v| v.is_some())
            .count()
            != triples.len()
        {
            return Err(bad("exact gate->tuple layer assignment"));
        }
        let bit_positions = bit_prefix(&origin.plan().network)?;
        let mut binding = b"DREGG.PRIVATE.FIELD.LAYERS\x01".to_vec();
        bytes(&origin.plan().encode(), &mut binding);
        bytes(&schedule.encode(), &mut binding);
        let (n, f) = origin.roster();
        let me = origin.holder();
        let triples = triples.to_vec();
        Ok(Self {
            origin,
            context: hash(&binding),
            schedule,
            wires,
            triples,
            bit_positions,
            me,
            n,
            f,
            next_batch: 0,
            started: false,
            opening_sent: false,
            openings: BTreeMap::new(),
            bits: (0..n).map(|h| Bracha::new(n, f, Some(h as u16))).collect(),
            bits_sent: false,
            output: None,
            failure: None,
        })
    }
    pub fn plan(&self) -> &Plan {
        self.origin.plan()
    }
    pub fn holder(&self) -> u16 {
        self.me
    }
    pub fn roster(&self) -> (usize, usize) {
        (self.n, self.f)
    }
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn schedule(&self) -> &Schedule {
        &self.schedule
    }
    pub fn completed_batches(&self) -> usize {
        self.next_batch
    }
    pub fn output(&self) -> Option<&SharedOutput> {
        self.output.as_ref()
    }
    pub fn failure(&self) -> Option<&BitnessFailure> {
        self.failure.as_ref()
    }
    pub(crate) fn initial_bytes(&self) -> Result<Vec<u8>> {
        if self.started || self.next_batch != 0 || !self.openings.is_empty() || self.bits_sent {
            return Err(bad("layer original initialization only"));
        }
        self.origin.initial_bytes()
    }
    pub(crate) fn restore_initial(
        b: &[u8],
        p: &Plan,
        h: u16,
        anchor: &std::path::Path,
    ) -> Result<Self> {
        Self::new(Engine::restore_initial(b, p, h, anchor)?)
    }
    fn all(&self, body: Body) -> Vec<Send> {
        (0..self.n)
            .map(|to| Send {
                to: to as u16,
                message: Message {
                    context: self.context,
                    body: body.clone(),
                },
            })
            .collect()
    }
    pub fn start(&mut self) -> Result<Vec<Send>> {
        if self.started {
            return Ok(vec![]);
        }
        self.started = true;
        self.progress()
    }
    pub fn receive(&mut self, sender: u16, m: Message) -> Result<Vec<Send>> {
        if sender as usize >= self.n || m.context != self.context {
            return Err(bad("layer authenticated sender/context"));
        }
        let mut out = vec![];
        match m.body {
            Body::Opening {
                gate: batch,
                holder,
                phase,
            } => {
                let positions = self
                    .schedule
                    .batches
                    .get(batch)
                    .ok_or_else(|| bad("layer batch index"))?;
                if holder as usize >= self.n {
                    return Err(bad("layer opening holder"));
                }
                fields(values(&phase), 2 * positions.len())?;
                let ps = self
                    .openings
                    .entry((batch, holder))
                    .or_insert_with(|| Bracha::new(self.n, self.f, Some(holder)))
                    .receive(sender, phase);
                for phase in ps {
                    out.extend(self.all(Body::Opening {
                        gate: batch,
                        holder,
                        phase,
                    }));
                }
            }
            Body::Bits { holder, phase } => {
                if holder as usize >= self.n {
                    return Err(bad("layer bit holder"));
                }
                fields(values(&phase), self.bit_positions.len())?;
                for phase in self.bits[holder as usize].receive(sender, phase) {
                    out.extend(self.all(Body::Bits { holder, phase }));
                }
            }
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    /// One forward scan computes every ready XOR/constant because references
    /// strictly precede gates. Pending ANDs remain empty; no secret readiness
    /// selects batches (the complete schedule is public before reservation).
    fn linear(&mut self) {
        let base = self.plan().network.input_count as usize;
        for (index, op) in self.origin.plan().network.gates.iter().enumerate() {
            if self.wires[base + index].is_some() {
                continue;
            }
            self.wires[base + index] = match op {
                Op::Constant(v) => Some(Field(*v as u128)),
                Op::Xor(a, b) => match (self.wires[*a as usize], self.wires[*b as usize]) {
                    (Some(a), Some(b)) => Some(a.add(b)),
                    _ => None,
                },
                Op::And(..) => None,
            };
        }
    }
    fn progress(&mut self) -> Result<Vec<Send>> {
        let mut out = vec![];
        if !self.started {
            return Ok(out);
        }
        while self.next_batch < self.schedule.batches.len() {
            self.linear();
            let batch = self.next_batch;
            let positions = &self.schedule.batches[batch];
            let mut masked = vec![];
            for gate in positions {
                let Op::And(a, b) = self.plan().network.gates[*gate] else {
                    return Err(bad("layer assignment op"));
                };
                let (ta, tb, _) = self.triples[self.schedule.tuple_positions[*gate].unwrap()];
                let x =
                    self.wires[a as usize].ok_or_else(|| bad("public layer unresolved operand"))?;
                let y =
                    self.wires[b as usize].ok_or_else(|| bad("public layer unresolved operand"))?;
                masked.extend([x.add(ta), y.add(tb)]);
            }
            if !self.opening_sent {
                out.extend(self.all(Body::Opening {
                    gate: batch,
                    holder: self.me,
                    phase: PhaseMessage::Init(field_bytes(&masked)),
                }));
                self.opening_sent = true;
            }
            let mut points = BTreeMap::new();
            for h in 0..self.n as u16 {
                if let Some(raw) = self
                    .openings
                    .get(&(batch, h))
                    .and_then(|r| r.output.as_ref())
                {
                    points.insert(h, fields(raw, masked.len())?);
                }
            }
            // ONE degree-f vector polynomial must match n-f authenticated
            // holders across EVERY component. No component-wise subset choice.
            let Some((polys, _)) =
                acss_id::correct_polynomials(&points, self.f, self.n - self.f, masked.len())?
            else {
                return Ok(out);
            };
            let base = self.plan().network.input_count as usize;
            for (i, gate) in positions.iter().enumerate() {
                let (ta, tb, tc) = self.triples[self.schedule.tuple_positions[*gate].unwrap()];
                let (d, e) = (polys[2 * i][0], polys[2 * i + 1][0]);
                self.wires[base + gate] = Some(tc.add(d.mul(tb)).add(e.mul(ta)).add(d.mul(e)));
            }
            self.next_batch += 1;
            self.opening_sent = false;
        }
        self.linear();
        if self.wires.iter().any(Option::is_none) {
            return Err(bad("complete layer graph unresolved wire"));
        }
        if !self.bits_sent {
            let base = self.plan().network.input_count as usize;
            let vs = self
                .bit_positions
                .iter()
                .map(|g| self.wires[base + g].unwrap())
                .collect::<Vec<_>>();
            out.extend(self.all(Body::Bits {
                holder: self.me,
                phase: PhaseMessage::Init(field_bytes(&vs)),
            }));
            self.bits_sent = true;
        }
        if self.output.is_none() && self.failure.is_none() {
            let points = self
                .bits
                .iter()
                .enumerate()
                .filter_map(|(h, r)| {
                    r.output
                        .as_ref()
                        .map(|b| fields(b, self.bit_positions.len()).map(|v| (h as u16, v)))
                })
                .collect::<Result<BTreeMap<_, _>>>()?;
            if let Some((polys, _)) = acss_id::correct_polynomials(
                &points,
                self.f,
                self.n - self.f,
                self.bit_positions.len(),
            )? {
                let checks = polys.iter().map(|p| p[0]).collect::<Vec<_>>();
                if checks.iter().all(|x| *x == Field(0)) {
                    self.output = Some(SharedOutput {
                        context: self.context,
                        holder: self.me,
                        values: self
                            .plan()
                            .network
                            .outputs
                            .iter()
                            .map(|w| self.wires[*w as usize].unwrap())
                            .collect(),
                    });
                } else {
                    self.failure = Some(BitnessFailure {
                        opened_checks: checks,
                    });
                }
            }
        }
        Ok(out)
    }
}
/// Distinct wire domain: the Opening.gate field means PUBLIC batch index in
/// this layer protocol, never a silently reinterpreted sequential Engine wire.
pub fn encode_message(m: &Message) -> Vec<u8> {
    let mut b = b"DREGG.PRIVATE.FIELD.LAYERS.WIRE\x01".to_vec();
    bytes(&field_network::encode_message(m), &mut b);
    b
}
pub fn decode_message(b: &[u8]) -> Result<Message> {
    let tag = b"DREGG.PRIVATE.FIELD.LAYERS.WIRE\x01";
    let mut c = Cursor::new(b)?;
    if c.take(tag.len())? != tag {
        return Err(bad("layer wire domain"));
    }
    let m = field_network::decode_message(&c.bytes()?)?;
    c.finish()?;
    if encode_message(&m) != b {
        return Err(bad("layer canonical"));
    }
    Ok(m)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::field_network_store::{LayerStore, Store};
    use std::{
        collections::VecDeque,
        fs,
        path::PathBuf,
        time::{SystemTime, UNIX_EPOCH},
    };
    fn path(i: usize) -> PathBuf {
        let d = std::env::temp_dir().join(format!(
            "mini-layer-{}-{i}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&d).unwrap();
        d.join("events")
    }
    pub(crate) fn nodes() -> (
        Vec<LayerEngine>,
        Vec<crate::triple_king::tests::AnchorFixture>,
    ) {
        let (engines, anchors) = crate::field_network::tests::engine_nodes(Field(1), Field(1));
        (
            engines
                .into_iter()
                .map(|e| LayerEngine::new(e).unwrap())
                .collect(),
            anchors,
        )
    }
    fn start(ns: &mut [LayerEngine]) -> VecDeque<(u16, Send)> {
        let mut q = VecDeque::new();
        for n in ns {
            q.extend(n.start().unwrap().into_iter().map(|p| (n.holder(), p)));
        }
        q
    }
    fn drive(
        ns: &mut [LayerEngine],
        q: &mut VecDeque<(u16, Send)>,
        bad: bool,
        hold: bool,
    ) -> VecDeque<(u16, Send)> {
        let mut held = VecDeque::new();
        let mut steps = 0;
        while let Some((sender, mut p)) = q.pop_front() {
            steps += 1;
            assert!(steps < 200000);
            if hold
                && matches!(
                    p.message.body,
                    Body::Opening {
                        gate: 0,
                        holder: 2,
                        phase: PhaseMessage::Init(_)
                    }
                )
            {
                held.push_back((sender, p));
                continue;
            }
            if bad && sender == 3 {
                if let Body::Opening {
                    holder: 3,
                    phase: PhaseMessage::Init(ref mut raw),
                    ..
                } = p.message.body
                {
                    raw[0] ^= 1;
                }
            }
            let raw = encode_message(&p.message);
            assert!(
                field_network::decode_message(&raw).is_err(),
                "different domain, not legacy reinterpretation"
            );
            let m = decode_message(&raw).unwrap();
            let to = p.to;
            q.extend(
                ns[to as usize]
                    .receive(sender, m)
                    .unwrap()
                    .into_iter()
                    .map(|p| (to, p)),
            );
        }
        held
    }
    fn output(ns: &[LayerEngine]) -> Field {
        let ps = ns
            .iter()
            .take(3)
            .map(|n| (n.holder(), n.output().unwrap().shares().to_vec()))
            .collect::<Vec<_>>();
        let poly = acss_id::polynomial(&ps[..2], 1).unwrap();
        for (h, v) in ps {
            assert_eq!(
                v[0],
                poly[0]
                    .iter()
                    .rev()
                    .fold(Field(0), |s, c| s.mul(Field(h as u128 + 1)).add(*c))
            );
        }
        poly[0][0]
    }
    #[test]
    fn actual_native_full_controller_plan_codec_and_public_layer_schedule_match() {
        let raw = include_bytes!("../fixtures/public-minimal-plan.bin");
        let plan = Plan::decode(raw).unwrap();
        assert_eq!(plan.encode(), raw);
        assert_eq!(plan.network.gates.len(), 13237);
        assert_eq!(plan.public_ticks, 2);
        assert_eq!(plan.rows.len(), 9418);
        let schedule = Schedule::for_network(&plan.network).unwrap();
        assert_eq!(schedule.and_depth, 29);
        assert_eq!(schedule.batches.len(), 29);
        assert_eq!(schedule.batches.iter().map(Vec::len).sum::<usize>(), 4709);
        assert_eq!(schedule.batches.iter().map(Vec::len).max(), Some(565));
        let expected = vec![
            483, 565, 433, 326, 253, 222, 180, 233, 252, 236, 249, 222, 189, 144, 99, 75, 41, 54,
            54, 15, 51, 9, 80, 2, 83, 44, 40, 40, 35,
        ];
        assert_eq!(
            schedule.batches.iter().map(Vec::len).collect::<Vec<_>>(),
            expected
        );
        let mut gates = schedule
            .batches
            .iter()
            .flatten()
            .copied()
            .collect::<Vec<_>>();
        gates.sort_unstable();
        let actual = plan
            .network
            .gates
            .iter()
            .enumerate()
            .filter_map(|(i, g)| matches!(g, Op::And(..)).then_some(i))
            .collect::<Vec<_>>();
        assert_eq!(gates, actual, "every canonical AND position exactly once");
        for (i, g) in actual.iter().enumerate() {
            assert_eq!(schedule.tuple_positions[*g], Some(i));
        }
        let mut crossed = raw.to_vec();
        crossed.push(0);
        assert!(Plan::decode(&crossed).is_err());
        // This fixture is public synthetic inventory, not a qualified execution.
        // reserve() also requires actual checked stocks + ticks1 full unroll.
    }
    #[test]
    fn real_checked_parallel_masked_vector_uses_one_public_wave_for_three_ands() {
        let (mut ns, _anchors) = nodes();
        for n in &ns {
            assert_eq!(n.schedule().batches, vec![vec![2, 4, 5]]);
            assert_eq!(n.schedule().and_depth, 1);
            assert_eq!(
                n.plan().rows.len(),
                3,
                "exact original gate->tuple positions"
            );
        }
        let mut q = start(&mut ns);
        drive(&mut ns, &mut q, false, false);
        assert_eq!(output(&ns), Field(1));
        assert!(ns
            .iter()
            .all(|n| n.completed_batches() == 1 && n.output().is_some()));
        let (old, _) = crate::field_network::tests::engine_nodes(Field(0), Field(1));
        let mut started = old.into_iter().next().unwrap();
        started.start().unwrap();
        assert!(
            LayerEngine::new(started).is_err(),
            "cannot reinterpret a protocol already opening shares"
        );
    }
    #[test]
    fn corrupt_early_vector_waits_for_late_honest_full_vector_and_rejects_shape() {
        let (mut ns, _anchors) = nodes();
        let m = Message {
            context: ns[0].context(),
            body: Body::Opening {
                gate: 0,
                holder: 0,
                phase: PhaseMessage::Init(vec![0; 32]),
            },
        };
        assert!(
            ns[0].receive(0, m).is_err(),
            "all components bound, not an independently chosen subset"
        );
        let mut q = start(&mut ns);
        let mut held = drive(&mut ns, &mut q, true, true);
        assert!(!held.is_empty());
        assert!(ns[..3]
            .iter()
            .all(|n| n.completed_batches() == 0 && n.output().is_none()));
        drive(&mut ns, &mut held, false, false);
        assert_eq!(output(&ns), Field(1));
    }
    #[test]
    fn layer_vector_wal_replays_pending_original_outbox_then_completes() {
        let (ns, anchors) = nodes();
        let plans = ns.iter().map(|n| n.plan().clone()).collect::<Vec<_>>();
        let paths = (0..4).map(path).collect::<Vec<_>>();
        let mut stores = ns
            .into_iter()
            .enumerate()
            .map(|(i, n)| Some(LayerStore::create(&paths[i], n).unwrap()))
            .collect::<Vec<_>>();
        let mut q = VecDeque::new();
        let mut saved = vec![];
        for (i, s) in stores.iter_mut().enumerate() {
            let ps = s.as_mut().unwrap().start().unwrap();
            if i == 1 {
                saved = ps.clone();
            }
            q.extend(ps.into_iter().map(|p| (i as u16, p)));
        }
        drop(stores[1].take());
        assert!(
            Store::reopen(&paths[1], &plans[1], 1, anchors[1].socket()).is_err(),
            "sequential WAL cannot reinterpret layer wire events"
        );
        let reopened = LayerStore::reopen(&paths[1], &plans[1], 1, anchors[1].socket()).unwrap();
        assert_eq!(reopened.replay_outboxes().unwrap(), saved);
        q.extend(saved.into_iter().map(|p| (1, p)));
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
        let ps = stores
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
        assert_eq!(acss_id::polynomial(&ps, 1).unwrap()[0][0], Field(1));
        assert!(stores
            .iter()
            .all(|s| s.as_ref().unwrap().state().completed_batches() == 1));
        drop(stores[1].take());
        assert!(
            LayerStore::reopen(&paths[1], &plans[1], 1, anchors[1].socket())
                .unwrap()
                .state()
                .output()
                .is_some()
        );
    }
}
