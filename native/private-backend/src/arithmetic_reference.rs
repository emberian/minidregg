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
        completed_word_network(left as u64, right as u64, instance, network, source_binding)
    }
    pub(crate) fn completed_word_network(
        left: u64,
        right: u64,
        instance: u64,
        network: Network,
        source_binding: &[u8],
    ) -> (Vec<LayerEngine>, Vec<triple_king::tests::AnchorFixture>) {
        completed_word_network_generation(left, right, instance, network, source_binding, None)
    }
    pub(crate) fn completed_word_network_generation(
        left: u64,
        right: u64,
        instance: u64,
        network: Network,
        source_binding: &[u8],
        generation: Option<&crate::codec::Generation>,
    ) -> (Vec<LayerEngine>, Vec<triple_king::tests::AnchorFixture>) {
        let input_count = network.input_count as usize;
        assert!(input_count > 0 && input_count % 2 == 0);
        let width = input_count / 2;
        assert!(width <= 8 && left < (1 << width) && right < (1 << width));
        let and_count = network
            .gates
            .iter()
            .filter(|op| matches!(op, Op::And(..)))
            .count();
        assert!(and_count > 0 && and_count <= 32);
        let stocks = match generation {
            Some(g) => triple_king::tests::checked_inventory_generation(and_count, instance, g),
            None => triple_king::tests::checked_inventory(and_count, instance),
        };
        let g = stocks[0].generation().clone();
        let mut inputs = (0..4)
            .map(|me| AcssId::new(me, 0, 4, 1, &g, input_count).unwrap())
            .collect::<Vec<_>>();
        let bits = (0..width)
            .map(|i| (left >> i) & 1)
            .chain((0..width).map(|i| (right >> i) & 1))
            .collect::<Vec<_>>();
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
            let refs = (0..input_count)
                .map(|index| InputRef::new(inputs[i].clone(), g.clone(), index).unwrap())
                .collect::<Vec<_>>();
            let manifest = TripleManifest::from_checked(&stocks[i]);
            let plan = crate::circuit_batch::Plan {
                generation: g.clone(),
                network: network.clone(),
                public_ticks: 1,
                binding_bytes: binding(&manifest, &refs, source_binding).unwrap(),
                rows: (0..and_count).map(|j| manifest.row(j).unwrap()).collect(),
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
    /// Fixed public capacity composition: each ACSS keeps its actual <=128
    /// even-count bound. Distinct chunk lengths avoid aliasing count-bound child
    /// contexts; a real fixed zero pad makes an odd logical input count even.
    /// Private Boolean values never select the partition or inventory count.
    pub(crate) fn completed_boolean_network_many(
        bits: &[bool],
        instance: u64,
        network: Network,
        source_binding: &[u8],
        g: &crate::codec::Generation,
    ) -> (Vec<LayerEngine>, Vec<triple_king::tests::AnchorFixture>) {
        assert!(!bits.is_empty() && bits.len() <= 256);
        assert_eq!(network.input_count as usize, bits.len());
        let count = network
            .gates
            .iter()
            .filter(|v| matches!(v, Op::And(..)))
            .count();
        assert!(count > 0 && count <= 65536);
        let stock_count = count.div_ceil(32);
        assert!(stock_count <= 2048);
        let mut physical_bits = bits.to_vec();
        physical_bits.resize(bits.len().next_multiple_of(2), false);
        let mut chunks = vec![];
        let mut remaining = physical_bits.len();
        let mut used = std::collections::BTreeSet::new();
        while remaining > 0 {
            let size = (2..=128)
                .rev()
                .filter(|n| n % 2 == 0)
                .find(|n| *n <= remaining && !used.contains(n))
                .unwrap();
            used.insert(size);
            chunks.push(size);
            remaining -= size;
        }
        // Public actual ACSS shape refusal precedes any seed extraction/burn.
        let mut profiles = chunks
            .iter()
            .map(|size| {
                (0..4)
                    .map(|me| AcssId::new(me, 0, 4, 1, g, *size).unwrap())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut source_partition = b"DREGG.REFERENCE.BOOLEAN.INPUT.PARTITION\x01".to_vec();
        crate::codec::bytes(source_binding, &mut source_partition);
        for n in [bits.len(), physical_bits.len(), chunks.len()] {
            crate::codec::Nat::new(n as u64).put(&mut source_partition);
        }
        for size in &chunks {
            crate::codec::Nat::new(*size as u64).put(&mut source_partition);
        }
        let mut stocks = vec![];
        for group in 0..stock_count {
            let width = (count - 32 * group).min(32);
            if stock_count > 32 && group % 32 == 0 {
                eprintln!("public reference preprocessing: {group}/{stock_count} stocks");
            }
            stocks.push(triple_king::tests::checked_inventory_generation(
                width,
                instance + group as u64,
                g,
            ));
        }
        let mut inputs_by_chunk = vec![];
        let mut offset = 0;
        for (chunk_index, size) in chunks.iter().enumerate() {
            let mut parties = std::mem::take(&mut profiles[chunk_index]);
            let polys = physical_bits[offset..offset + size]
                .iter()
                .enumerate()
                .map(|(i, b)| vec![Field(*b as u128), Field(37 + offset as u128 + i as u128)])
                .collect::<Vec<_>>();
            let mut q = parties[0]
                .dealer(&polys, [71; 32])
                .unwrap()
                .into_iter()
                .map(|p| (0, p))
                .collect::<VecDeque<_>>();
            while let Some((sender, p)) = q.pop_front() {
                let to = p.to;
                let wire = crate::acss_id_store::encode_message(&p.message);
                let decoded = crate::acss_id_store::decode_message(&wire).unwrap();
                q.extend(
                    parties[to as usize]
                        .receive(sender, decoded)
                        .unwrap()
                        .into_iter()
                        .map(|p| (to, p)),
                );
            }
            inputs_by_chunk.push(parties);
            offset += size;
        }
        let mut parties = vec![];
        let mut anchors = vec![];
        for holder in 0..4 {
            let mut refs = vec![];
            for (chunk, size) in inputs_by_chunk.iter().zip(&chunks) {
                for index in 0..*size {
                    if refs.len() == bits.len() {
                        break;
                    }
                    refs.push(InputRef::new(chunk[holder].clone(), g.clone(), index).unwrap());
                }
            }
            assert_eq!(refs.len(), bits.len());
            let checked = stocks.iter().map(|s| &s[holder]).collect::<Vec<_>>();
            let rows = checked
                .iter()
                .flat_map(|s| {
                    let manifest = TripleManifest::from_checked(s);
                    (0..s.count()).map(move |i| manifest.row(i).unwrap())
                })
                .collect::<Vec<_>>();
            assert_eq!(rows.len(), count);
            let plan = crate::circuit_batch::Plan {
                generation: g.clone(),
                network: network.clone(),
                public_ticks: 1,
                binding_bytes: crate::field_network::binding_many(
                    &checked,
                    &refs,
                    &source_partition,
                )
                .unwrap(),
                rows,
            };
            let (a, sock, root) =
                triple_king::tests::evaluator_anchor(&format!("boolean-many-{instance}-{holder}"));
            let origin = Engine::reserve_many(
                plan,
                &checked,
                refs,
                &source_partition,
                &sock,
                &root.join("burn"),
            )
            .unwrap();
            parties.push(LayerEngine::new(origin).unwrap());
            anchors.push(a);
        }
        let mut q = VecDeque::<(u16, Send)>::new();
        for p in &mut parties {
            q.extend(p.start().unwrap().into_iter().map(|v| (p.holder(), v)));
        }
        let mut steps = 0;
        while let Some((sender, p)) = q.pop_front() {
            steps += 1;
            assert!(steps < 2000000);
            let to = p.to;
            let wire = crate::field_network_layers::encode_message(&p.message);
            let decoded = crate::field_network_layers::decode_message(&wire).unwrap();
            q.extend(
                parties[to as usize]
                    .receive(sender, decoded)
                    .unwrap()
                    .into_iter()
                    .map(|v| (to, v)),
            );
        }
        assert!(parties
            .iter()
            .all(|v| v.output().is_some() && v.failure().is_none()));
        (parties, anchors)
    }
}
