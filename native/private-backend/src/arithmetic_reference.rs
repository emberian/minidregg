//! Public two-bit addition program over the SAME constant/XOR/AND network.
//! This is an explicit reference program, not a claim that the new Objective
//! source compiler/type/demand semantics have been refined to this graph.
use crate::circuit_batch::{Network, Op};
pub fn two_bit_addition() -> Network {
    let mut net = Network {
        input_count: 4,
        gates: vec![Op::Constant(true)],
        outputs: vec![],
    };
    // Counted input Boolean qualification precedes all arithmetic and consumes
    // the SAME full Plan; failure never returns those rows.
    for input in 0..4 {
        let x = emit(&mut net, Op::Xor(input, 4));
        emit(&mut net, Op::And(input, x));
    }
    let mut carry = emit(&mut net, Op::Constant(false));
    let mut sums = vec![];
    for bit in 0..2 {
        let (a, b) = (bit, bit + 2);
        let p = emit(&mut net, Op::Xor(a, b));
        sums.push(emit(&mut net, Op::Xor(p, carry)));
        let ab = emit(&mut net, Op::And(a, b));
        let pc = emit(&mut net, Op::And(p, carry));
        carry = emit(&mut net, Op::Xor(ab, pc));
    }
    sums.push(carry);
    net.outputs = sums;
    net
}
fn emit(n: &mut Network, op: Op) -> u64 {
    let wire = n.input_count + n.gates.len() as u64;
    n.gates.push(op);
    wire
}
#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::{
        acss_id::AcssId,
        field_network::{binding, Engine, InputRef, Send, TripleManifest},
        field_network_layers::LayerEngine,
        reconstruction::Field,
        triple_king,
    };
    use std::collections::VecDeque;
    pub(crate) fn completed(
        left: u8,
        right: u8,
        instance: u64,
    ) -> (Vec<LayerEngine>, Vec<triple_king::tests::AnchorFixture>) {
        completed_network(
            left,
            right,
            instance,
            two_bit_addition(),
            b"REFERENCE.NAT2.ADD/carry.retained/qualified4bits",
        )
    }
    pub(crate) fn completed_network(
        left: u8,
        right: u8,
        instance: u64,
        network: Network,
        source_binding: &[u8],
    ) -> (Vec<LayerEngine>, Vec<triple_king::tests::AnchorFixture>) {
        assert!(left < 4 && right < 4);
        assert_eq!(network.input_count, 4);
        assert_eq!(
            network
                .gates
                .iter()
                .filter(|op| matches!(op, Op::And(..)))
                .count(),
            8
        );
        let stocks = triple_king::tests::checked_inventory(8, instance);
        let g = stocks[0].generation().clone();
        let mut inputs = (0..4)
            .map(|me| AcssId::new(me, 0, 4, 1, &g, 4).unwrap())
            .collect::<Vec<_>>();
        let bits = [left & 1, (left >> 1) & 1, right & 1, (right >> 1) & 1];
        let polys = bits
            .iter()
            .enumerate()
            .map(|(i, v)| vec![Field(*v as u128), Field(37 + i as u128)])
            .collect::<Vec<_>>();
        let mut q = inputs[0]
            .dealer(&polys, [71; 32])
            .unwrap()
            .into_iter()
            .map(|p| (0, p))
            .collect::<VecDeque<_>>();
        while let Some((sender, p)) = q.pop_front() {
            let to = p.to;
            q.extend(
                inputs[to as usize]
                    .receive(sender, p.message)
                    .unwrap()
                    .into_iter()
                    .map(|p| (to, p)),
            );
        }
        let mut ns = vec![];
        let mut anchors = vec![];
        for i in 0..4 {
            let refs = (0..4)
                .map(|index| InputRef::new(inputs[i].clone(), g.clone(), index).unwrap())
                .collect::<Vec<_>>();
            let manifest = TripleManifest::from_checked(&stocks[i]);
            let plan = crate::circuit_batch::Plan {
                generation: g.clone(),
                network: network.clone(),
                public_ticks: 1,
                binding_bytes: binding(&manifest, &refs, source_binding).unwrap(),
                rows: (0..8).map(|j| manifest.row(j).unwrap()).collect(),
            };
            let (a, sock, root) =
                triple_king::tests::evaluator_anchor(&format!("nat2-{instance}-{i}"));
            let origin = Engine::reserve(
                plan,
                &stocks[i],
                refs,
                source_binding,
                &sock,
                &root.join("burn"),
            )
            .unwrap();
            ns.push(LayerEngine::new(origin).unwrap());
            anchors.push(a);
        }
        let mut q: VecDeque<(u16, Send)> = VecDeque::new();
        for n in &mut ns {
            q.extend(n.start().unwrap().into_iter().map(|p| (n.holder(), p)));
        }
        let mut steps = 0;
        while let Some((sender, p)) = q.pop_front() {
            steps += 1;
            assert!(steps < 200000);
            let to = p.to;
            q.extend(
                ns[to as usize]
                    .receive(sender, p.message)
                    .unwrap()
                    .into_iter()
                    .map(|p| (to, p)),
            );
        }
        assert!(ns
            .iter()
            .all(|n| n.output().is_some() && n.failure().is_none()));
        (ns, anchors)
    }
}
