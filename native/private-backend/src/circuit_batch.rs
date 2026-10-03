//! Canonical native PrivateCircuitAllocation plan + fixed batch reserve.
//! Private material release requires the complete public plan's rows anchored;
//! partial prefix crashes burn rows and cannot turn retries into fresh material.
//! This is material custody, not checked triples/authenticated wires/MPC.
use crate::{
    codec::{bad, bytes, Correlation, Generation, Journal, Nat, Purpose, Reader},
    custody::{self, Pool},
};
use std::{
    collections::BTreeSet,
    io::{Error, ErrorKind, Result},
    path::Path,
};
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Op {
    Constant(bool),
    Xor(u64, u64),
    And(u64, u64),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Network {
    pub input_count: u64,
    pub gates: Vec<Op>,
    pub outputs: Vec<u64>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Plan {
    pub generation: Generation,
    pub network: Network,
    pub public_ticks: u64,
    pub binding_bytes: Vec<u8>,
    pub rows: Vec<Correlation>,
}
impl Plan {
    pub fn assignments(&self) -> Vec<(u64, usize, &Correlation)> {
        let mut out = vec![];
        let mut i = 0;
        for tick in 0..self.public_ticks {
            for (gate, op) in self.network.gates.iter().enumerate() {
                if matches!(op, Op::And(..)) {
                    if let Some(row) = self.rows.get(i) {
                        out.push((tick, gate, row));
                    }
                    i += 1;
                }
            }
        }
        out
    }
    pub fn validate(&self) -> Result<()> {
        if self.network.gates.len() > 65536
            || self.network.input_count > 65536
            || self.public_ticks > 4096
            || self.rows.len() > 65536
            || self.binding_bytes.is_empty()
        {
            return Err(bad("physical circuit capacity/profile"));
        }
        for (i, op) in self.network.gates.iter().enumerate() {
            let bound = self.network.input_count + i as u64;
            if let Op::Xor(a, b) | Op::And(a, b) = op {
                if *a >= bound || *b >= bound {
                    return Err(bad("forward gate operand"));
                }
            }
        }
        let bound = self.network.input_count + self.network.gates.len() as u64;
        if self.network.outputs.iter().any(|i| *i >= bound) {
            return Err(bad("output wire range"));
        }
        let count = self
            .network
            .gates
            .iter()
            .filter(|op| matches!(op, Op::And(..)))
            .count() as u64;
        if self.public_ticks.checked_mul(count) != Some(self.rows.len() as u64) {
            return Err(bad("fixed circuit correlation count"));
        }
        let mut ids = BTreeSet::new();
        for row in &self.rows {
            let mut b = vec![];
            row.put(&mut b);
            if !ids.insert(b) {
                return Err(bad("physical row alias"));
            }
        }
        Ok(())
    }
    pub fn encode(&self) -> Vec<u8> {
        let mut b = vec![];
        bytes(b"DREGG.PRIVATE.CIRCUIT.ALLOCATION\x01", &mut b);
        self.generation.put(&mut b);
        Nat::new(self.network.input_count).put(&mut b);
        Nat::new(self.network.gates.len() as u64).put(&mut b);
        for op in &self.network.gates {
            let (tag, a, c) = match op {
                Op::Constant(false) => (0, 0, 0),
                Op::Constant(true) => (1, 0, 0),
                Op::Xor(a, c) => (2, *a, *c),
                Op::And(a, c) => (3, *a, *c),
            };
            for v in [tag, a, c] {
                Nat::new(v).put(&mut b);
            }
        }
        Nat::new(self.network.outputs.len() as u64).put(&mut b);
        for v in &self.network.outputs {
            Nat::new(*v).put(&mut b);
        }
        Nat::new(self.public_ticks).put(&mut b);
        bytes(&self.binding_bytes, &mut b);
        Nat::new(self.rows.len() as u64).put(&mut b);
        for row in &self.rows {
            row.put(&mut b);
        }
        b
    }
    pub fn decode(b: &[u8]) -> Result<Self> {
        let mut r = Reader::new(b)?;
        if r.bytes()? != b"DREGG.PRIVATE.CIRCUIT.ALLOCATION\x01" {
            return Err(bad("circuit plan frame"));
        }
        let generation = Generation::get(&mut r)?;
        let input_count = r.nat()?.value()?;
        let gate_count = r.count()?;
        if gate_count > 65536 {
            return Err(bad("gate count bound"));
        }
        let mut gates = vec![];
        for _ in 0..gate_count {
            let tag = r.nat()?.value()?;
            let a = r.nat()?.value()?;
            let c = r.nat()?.value()?;
            gates.push(match (tag, a, c) {
                (0, 0, 0) => Op::Constant(false),
                (1, 0, 0) => Op::Constant(true),
                (2, a, c) => Op::Xor(a, c),
                (3, a, c) => Op::And(a, c),
                _ => return Err(bad("noncanonical gate")),
            });
        }
        let outputs_count = r.count()?;
        if outputs_count > 65536 {
            return Err(bad("output count"));
        }
        let mut outputs = vec![];
        for _ in 0..outputs_count {
            outputs.push(r.nat()?.value()?);
        }
        let public_ticks = r.nat()?.value()?;
        let binding_bytes = r.bytes()?;
        let row_count = r.count()?;
        if row_count > 65536 {
            return Err(bad("row count"));
        }
        let mut rows = vec![];
        for _ in 0..row_count {
            rows.push(Correlation::get(&mut r)?);
        }
        r.finish()?;
        let v = Self {
            generation,
            network: Network {
                input_count,
                gates,
                outputs,
            },
            public_ticks,
            binding_bytes,
            rows,
        };
        v.validate()?;
        if v.encode() != b {
            return Err(bad("circuit plan canonical"));
        }
        Ok(v)
    }
}
pub struct CompletedBatch {
    plan_bytes: Vec<u8>,
    anchored_journal: Journal,
    material: Vec<Vec<u8>>,
}
impl CompletedBatch {
    pub fn plan_bytes(&self) -> &[u8] {
        &self.plan_bytes
    }
    pub fn anchored_journal(&self) -> &Journal {
        &self.anchored_journal
    }
    pub fn into_material(self) -> Vec<Vec<u8>> {
        self.material
    }
}
/// Privileged source adapter MUST approve exact Plan binding/Generation/full row
/// manifest and fund fixed public row bytes. This low-level method supplies no
/// SourceYES authority or checked-triple/privateRecovery evidence.
/// Lost completed reply is NOT permission to release this batch again.
pub fn reserve_plan_release(
    plan: &Plan,
    pool: &Pool,
    anchor: &Path,
    local: &Path,
    public_row_bytes: usize,
) -> Result<CompletedBatch> {
    plan.validate()?;
    if public_row_bytes == 0
        || plan
            .rows
            .len()
            .checked_mul(public_row_bytes)
            .filter(|n| *n <= crate::codec::MAX)
            .is_none()
    {
        return Err(bad("funded batch secret capacity"));
    }
    let _guard = custody::lock(&local.with_extension("reservation.lock"))?;
    let before = Journal::decode(&custody::rpc(anchor, &[0])?)?;
    let mut prospective = before.clone();
    // Validate ALL profile/stock/alias/spent checks before consuming any rows.
    for id in &plan.rows {
        if id.pool != pool.id || id.row.value()? as u128 >= pool.len() as u128 {
            return Err(Error::new(
                ErrorKind::UnexpectedEof,
                "plan pool/stock mismatch",
            ));
        }
        prospective = prospective.reserve(id.clone(), plan.generation.clone(), Purpose::Triple)?;
    }
    let mut confirmed = before.clone();
    for id in &plan.rows {
        let mut req = vec![1];
        req.extend(crate::codec::request(id, &plan.generation, Purpose::Triple));
        let next = Journal::decode(&custody::rpc(anchor, &req)?)?;
        if !next.extends(&confirmed)
            || !confirmed
                .allocations
                .iter()
                .all(|a| next.allocations.contains(a))
            || !next.allocations.iter().any(|a| {
                a.id == *id
                    && a.generation == plan.generation
                    && a.purpose == Purpose::Triple
                    && !a.consumed
            })
        {
            return Err(bad("batch allocation binding/retention"));
        }
        confirmed = next;
    }
    // The fixed public prefix is complete before snapshot or FIRST secret row.
    custody::snapshot(local, &confirmed.encode())?;
    if std::fs::read(local)? != confirmed.encode() {
        return Err(bad("batch snapshot readback"));
    }
    let latest = Journal::decode(&custody::rpc(anchor, &[0])?)?;
    if !latest.extends(&confirmed)
        || !confirmed
            .allocations
            .iter()
            .all(|a| latest.allocations.contains(a))
    {
        return Err(bad("batch anchor regression"));
    }
    let mut material = vec![];
    for id in &plan.rows {
        let b = pool.row_fixed(id.row.value()?, public_row_bytes)?;
        if b.len() != public_row_bytes {
            return Err(bad("fixed material row byte shape; full plan burned"));
        }
        material.push(b);
    }
    Ok(CompletedBatch {
        plan_bytes: plan.encode(),
        anchored_journal: latest,
        material,
    })
}
#[cfg(test)]
mod tests {
    use super::*;
    fn g() -> Generation {
        Generation {
            invocation: Nat::from_be(&[255; 32]),
            command: vec![3],
            attempt: Nat::new(0),
            generation: Nat::new(1),
            configuration: Nat::from_be(&[254; 32]),
        }
    }
    fn plan() -> Plan {
        Plan {
            generation: g(),
            network: Network {
                input_count: 2,
                gates: vec![Op::Xor(0, 1), Op::And(0, 2)],
                outputs: vec![3],
            },
            public_ticks: 2,
            binding_bytes: vec![9],
            rows: (0..2)
                .map(|i| Correlation {
                    pool: Nat::new(42),
                    row: Nat::new(i),
                })
                .collect(),
        }
    }
    #[test]
    fn actual_native_plan_fixture_byte_identity_and_schedule() {
        // Host.PrivateCircuitPlanFixture main ACTUALLY EXECUTED 2026-10-03:
        // JSON SHA e80d449066f9d8e1e2902dd9e63cec0be785eb88517b5e130ef5e2840fb72788.
        // These bytes are generated by the native codec, not this Rust encode.
        let bytes: Vec<u8> = vec![
            33, 255, 68, 82, 69, 71, 71, 46, 80, 82, 73, 86, 65, 84, 69, 46, 67, 73, 82, 67, 85,
            73, 84, 46, 65, 76, 76, 79, 67, 65, 84, 73, 79, 78, 1, 255, 1, 255, 3, 7, 255, 11, 255,
            255, 2, 255, 2, 255, 2, 255, 255, 1, 255, 3, 255, 255, 2, 255, 1, 255, 3, 255, 2, 255,
            1, 255, 9, 2, 255, 42, 255, 255, 42, 255, 1, 255,
        ];
        let p = Plan::decode(&bytes).unwrap();
        assert_eq!(p.encode(), bytes);
        assert_eq!(
            p.generation,
            Generation {
                invocation: Nat::new(0),
                command: vec![3],
                attempt: Nat::new(7),
                generation: Nat::new(11),
                configuration: Nat::new(0)
            }
        );
        assert_eq!(
            p.network,
            Network {
                input_count: 2,
                gates: vec![Op::Xor(0, 1), Op::And(0, 2)],
                outputs: vec![3]
            }
        );
        assert_eq!(p.public_ticks, 2);
        assert_eq!(p.binding_bytes, vec![9]);
        assert_eq!(
            p.rows,
            vec![
                Correlation {
                    pool: Nat::new(42),
                    row: Nat::new(0)
                },
                Correlation {
                    pool: Nat::new(42),
                    row: Nat::new(1)
                }
            ]
        );
        assert_eq!(
            p.assignments()
                .iter()
                .map(|(tick, gate, _)| (*tick, *gate))
                .collect::<Vec<_>>(),
            vec![(0, 1), (1, 1)]
        );
    }
    #[test]
    fn exact_circuit_plan_order_count_aliases_and_unchanged_generation() {
        let p = plan();
        assert_eq!(Plan::decode(&p.encode()).unwrap(), p);
        assert_eq!(
            p.assignments()
                .iter()
                .map(|(tick, gate, _)| (*tick, *gate))
                .collect::<Vec<_>>(),
            vec![(0, 1), (1, 1)]
        );
        let mut wrong = p.clone();
        wrong.rows[1] = wrong.rows[0].clone();
        assert!(wrong.validate().is_err());
        let mut wrong = p.clone();
        wrong.network.gates[0] = Op::Xor(3, 1);
        assert!(wrong.validate().is_err());
        let mut wrong = p.clone();
        wrong.public_ticks = 3;
        assert!(wrong.validate().is_err());
        let mut trailing = p.encode();
        trailing.push(0);
        assert!(Plan::decode(&trailing).is_err());
        assert_eq!(p.generation.command, vec![3]); // plan lives separately from accepted native command
    }
    #[test]
    fn complete_public_batch_burns_before_any_shape_failure_and_retry_refuses() {
        use std::{
            fs,
            os::unix::net::UnixListener,
            thread,
            time::{SystemTime, UNIX_EPOCH},
        };
        let root = std::env::temp_dir().join(format!(
            "mini-batch-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&root).unwrap();
        let pool = Pool::provision(
            &root.join("pool"),
            &[vec![1; 4], vec![2; 3], vec![3; 4], vec![4; 4]],
        )
        .unwrap();
        let sock = root.join("anchor.sock");
        let listener = UnixListener::bind(&sock).unwrap();
        let anchor_root = root.join("authority");
        let h = thread::spawn(move || {
            let mut a = custody::Anchor::open(&anchor_root).unwrap();
            // Four actual fixed batch RPCs: snapshot, reserve0,reserve1,readback.
            for _ in 0..4 {
                let (mut s, _) = listener.accept().unwrap();
                let b = custody::read_packet(&mut s).unwrap();
                let out = match b[0] {
                    0 => a.journal.encode(),
                    1 => {
                        let (id, g, p) = crate::codec::parse_request(&b[1..]).unwrap();
                        a.reserve(id, g, p).unwrap()
                    }
                    _ => panic!("rpc"),
                };
                let mut reply = vec![0];
                reply.extend(out);
                custody::write_packet(&mut s, &reply).unwrap();
            }
            a.journal
        });
        let mut p = plan();
        for r in &mut p.rows {
            r.pool = pool.id.clone();
        }
        assert!(reserve_plan_release(&p, &pool, &sock, &root.join("snapshot"), 4).is_err());
        let j = h.join().unwrap();
        assert_eq!(j.spent.len(), 2);
        assert!(j
            .reserve(p.rows[0].clone(), p.generation.clone(), Purpose::Triple)
            .is_err());
        assert!(j
            .reserve(p.rows[1].clone(), p.generation.clone(), Purpose::Triple)
            .is_err());
        assert_eq!(
            Journal::decode(&fs::read(root.join("snapshot")).unwrap()).unwrap(),
            j
        );
    }
}
