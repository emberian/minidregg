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
        acss_id::{self, AcssId},
        codec::Generation,
        entropy::Entropy,
        field_network::{binding, Engine, InputRef, Send, TripleManifest},
        field_network_layers::LayerEngine,
        reconstruction::Field,
        transcript::{Tap, Wire},
        triple_king::{self, CheckedTriples},
    };
    use std::collections::VecDeque;

    /// An input party. Its private value exists only as the constant terms of
    /// the degree-f polynomials it draws from its OWN entropy stream and keeps
    /// here; the harness gets the party's dealer outbox (what a network carries),
    /// never the value, the polynomials or the dealing seed.
    pub(crate) struct InputParty {
        dealer: u16,
        polys: Vec<Vec<Field>>,
        seed: [u8; 32],
    }
    impl InputParty {
        /// `width` low bits of `value`, least significant first.
        pub(crate) fn new(dealer: u16, value: u64, width: usize, e: &mut Entropy) -> Self {
            assert!(width > 0 && width <= 64 && (width == 64 || value < (1 << width)));
            let bits = (0..width).map(|i| (value >> i) & 1 == 1).collect::<Vec<_>>();
            Self::from_bits(dealer, &bits, e)
        }
        pub(crate) fn from_bits(dealer: u16, bits: &[bool], e: &mut Entropy) -> Self {
            assert!(!bits.is_empty() && bits.len() % 2 == 0 && bits.len() <= 256);
            let polys = bits
                .iter()
                .map(|b| vec![Field(*b as u128), e.field()])
                .collect::<Vec<_>>();
            Self {
                dealer,
                polys,
                seed: e.bytes32(),
            }
        }
        /// FALSIFIER ONLY: the retired r31 dealing, whose degree-1 coefficient was
        /// the public constant 37+i and whose seed was [71;32]. One share then
        /// determines the bit. Kept so the secrecy check can be shown to go red.
        pub(crate) fn retired_public_coefficient_dealing(dealer: u16, value: u64, width: usize) -> Self {
            Self {
                dealer,
                polys: (0..width)
                    .map(|i| vec![Field(((value >> i) & 1) as u128), Field(37 + i as u128)])
                    .collect(),
                seed: [71; 32],
            }
        }
        pub(crate) fn dealer(&self) -> u16 {
            self.dealer
        }
        pub(crate) fn count(&self) -> usize {
            self.polys.len()
        }
        /// Party-local act: deal into this party's own ACSS instance.
        fn deal(&self, own: &mut AcssId) -> Vec<acss_id::Send> {
            assert_eq!(own.me, self.dealer);
            own.dealer(&self.polys, self.seed).unwrap()
        }
        /// SIMULATOR WITNESS, not a party operation: the same dealing with the
        /// value replaced, every polynomial moved by delta*L where L(0)=1 and
        /// L(alpha_curious)=0. The curious holder's points are unchanged; the
        /// dealing seed (PrivSend keys, dZK masks) is unchanged.
        pub(crate) fn equivocate(&self, value: u64, curious: u16) -> Self {
            let width = self.polys.len();
            let slope = Field(curious as u128 + 1).inv().unwrap();
            let polys = self
                .polys
                .iter()
                .enumerate()
                .map(|(i, p)| {
                    let wanted = Field(((value >> i) & 1) as u128);
                    let delta = wanted.add(p[0]);
                    vec![wanted, p[1].add(delta.mul(slope))]
                })
                .collect::<Vec<_>>();
            assert!(width == 64 || value < (1 << width));
            Self {
                dealer: self.dealer,
                polys,
                seed: self.seed,
            }
        }
    }

    /// Run every input party's actual ACSS-Id among four holders. Instances are
    /// distinguished by (dealer, count) in their public context.
    pub(crate) fn share_inputs(
        parties: &[&InputParty],
        g: &Generation,
        tap: &mut Tap,
    ) -> Vec<Vec<AcssId>> {
        let mut seen = std::collections::BTreeSet::new();
        parties
            .iter()
            .map(|party| {
                assert!(seen.insert((party.dealer(), party.count())), "aliased input instance");
                let mut states = (0..4)
                    .map(|me| AcssId::new(me, party.dealer(), 4, 1, g, party.count()).unwrap())
                    .collect::<Vec<_>>();
                let dealer = party.dealer();
                let mut q = party
                    .deal(&mut states[dealer as usize])
                    .into_iter()
                    .map(|p| (dealer, p))
                    .collect::<VecDeque<_>>();
                let mut steps = 0;
                while let Some((sender, p)) = q.pop_front() {
                    steps += 1;
                    assert!(steps < 2000000);
                    let wire = crate::acss_id_store::encode_message(&p.message);
                    let decoded = crate::acss_id_store::decode_message(&wire).unwrap();
                    let to = p.to;
                    tap.see("input-acss", to, sender, || Wire::Acss(decoded.clone()));
                    q.extend(
                        states[to as usize]
                            .receive(sender, decoded)
                            .unwrap()
                            .into_iter()
                            .map(|p| (to, p)),
                    );
                }
                states
            })
            .collect()
    }

    /// Actual layered MPC over privately dealt inputs. `stocks[holder]` are that
    /// holder's checked King inventories; plan rows take every tuple in order.
    pub(crate) fn completed_private_inputs(
        parties: &[&InputParty],
        network: Network,
        source_binding: &[u8],
        g: &Generation,
        stocks: &[Vec<CheckedTriples>],
        label: &str,
        tap: &mut Tap,
    ) -> (Vec<LayerEngine>, Vec<triple_king::tests::AnchorFixture>) {
        let (engines, anchors, _) =
            completed_private_inputs_with_states(parties, network, source_binding, g, stocks, label, tap);
        (engines, anchors)
    }
    /// As above, also returning every holder's actual input ACSS state (for an
    /// auditor that must read honest holders' shares, never for the harness path).
    pub(crate) fn completed_private_inputs_with_states(
        parties: &[&InputParty],
        network: Network,
        source_binding: &[u8],
        g: &Generation,
        stocks: &[Vec<CheckedTriples>],
        label: &str,
        tap: &mut Tap,
    ) -> (
        Vec<LayerEngine>,
        Vec<triple_king::tests::AnchorFixture>,
        Vec<Vec<AcssId>>,
    ) {
        let input_count = network.input_count as usize;
        assert_eq!(
            parties.iter().map(|p| p.count()).sum::<usize>(),
            input_count,
            "every network input is some party's private bit"
        );
        let count = network
            .gates
            .iter()
            .filter(|v| matches!(v, Op::And(..)))
            .count();
        let shared = share_inputs(parties, g, tap);
        let mut engines = vec![];
        let mut anchors = vec![];
        for holder in 0..4 {
            let refs = shared
                .iter()
                .flat_map(|states| {
                    let s = states[holder].clone();
                    (0..s.count).map(move |i| InputRef::new(s.clone(), g.clone(), i).unwrap())
                })
                .collect::<Vec<_>>();
            let checked = stocks[holder].iter().collect::<Vec<_>>();
            let rows = checked
                .iter()
                .flat_map(|s| {
                    let manifest = TripleManifest::from_checked(s);
                    (0..s.count()).map(move |i| manifest.row(i).unwrap())
                })
                .collect::<Vec<_>>();
            assert_eq!(rows.len(), count);
            let single = checked.len() == 1;
            let binding_bytes = if single {
                binding(&TripleManifest::from_checked(checked[0]), &refs, source_binding).unwrap()
            } else {
                crate::field_network::binding_many(&checked, &refs, source_binding).unwrap()
            };
            let plan = crate::circuit_batch::Plan {
                generation: g.clone(),
                network: network.clone(),
                public_ticks: 1,
                binding_bytes,
                rows,
            };
            let (a, sock, root) =
                triple_king::tests::evaluator_anchor(&format!("{label}-{holder}"));
            let origin = if single {
                Engine::reserve(plan, checked[0], refs, source_binding, &sock, &root.join("burn"))
            } else {
                Engine::reserve_many(plan, &checked, refs, source_binding, &sock, &root.join("burn"))
            }
            .unwrap();
            engines.push(LayerEngine::new(origin).unwrap());
            anchors.push(a);
        }
        let mut q = VecDeque::<(u16, Send)>::new();
        for n in &mut engines {
            q.extend(n.start().unwrap().into_iter().map(|p| (n.holder(), p)));
        }
        let mut steps = 0;
        while let Some((sender, p)) = q.pop_front() {
            steps += 1;
            assert!(steps < 2000000);
            let wire = crate::field_network_layers::encode_message(&p.message);
            let decoded = crate::field_network_layers::decode_message(&wire).unwrap();
            let to = p.to;
            tap.see("layer-mpc", to, sender, || Wire::Layer(decoded.clone()));
            q.extend(
                engines[to as usize]
                    .receive(sender, decoded)
                    .unwrap()
                    .into_iter()
                    .map(|p| (to, p)),
            );
        }
        assert!(engines
            .iter()
            .all(|n| n.output().is_some() && n.failure().is_none()));
        (engines, anchors, shared)
    }

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
    /// Two input parties: holder 0 privately deals `left`, holder 2 privately
    /// deals `right`, each from its own entropy stream. King preprocessing draws
    /// every dealer's randomness from that dealer's own stream.
    pub(crate) fn completed_word_network_generation(
        left: u64,
        right: u64,
        instance: u64,
        network: Network,
        source_binding: &[u8],
        generation: Option<&Generation>,
    ) -> (Vec<LayerEngine>, Vec<triple_king::tests::AnchorFixture>) {
        let input_count = network.input_count as usize;
        // Two parties, each an even-count ACSS instance of width bits.
        assert!(input_count > 0 && input_count % 4 == 0);
        let width = input_count / 2;
        assert!(width <= 8 && left < (1 << width) && right < (1 << width));
        let and_count = network
            .gates
            .iter()
            .filter(|op| matches!(op, Op::And(..)))
            .count();
        assert!(and_count > 0 && and_count <= 32);
        let g = generation
            .cloned()
            .unwrap_or_else(|| triple_king::tests::test_generation(300 + 1000 * instance));
        let stocks = triple_king::tests::checked_inventory_generation(and_count, instance, &g)
            .into_iter()
            .map(|s| vec![s])
            .collect::<Vec<_>>();
        let root = crate::entropy::test_root();
        let l = InputParty::new(0, left, width, &mut root.fork(format!("input/{instance}/left").as_bytes()));
        let r = InputParty::new(2, right, width, &mut root.fork(format!("input/{instance}/right").as_bytes()));
        completed_private_inputs(
            &[&l, &r],
            network,
            source_binding,
            &g,
            &stocks,
            &format!("nat2-{instance}"),
            &mut Tap::none(),
        )
    }
    /// Fixed public capacity composition: each ACSS keeps its actual <=128
    /// even-count bound. Distinct chunk lengths avoid aliasing count-bound child
    /// contexts; a real fixed zero pad makes an odd logical input count even.
    /// Private Boolean values never select the partition or inventory count.
    /// Holder 0 is the single input party; each chunk draws from its own stream.
    pub(crate) fn completed_boolean_network_many(
        bits: &[bool],
        instance: u64,
        network: Network,
        source_binding: &[u8],
        g: &Generation,
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
        for size in &chunks {
            for me in 0..4 {
                AcssId::new(me, 0, 4, 1, g, *size).unwrap();
            }
        }
        let mut source_partition = b"DREGG.REFERENCE.BOOLEAN.INPUT.PARTITION\x01".to_vec();
        crate::codec::bytes(source_binding, &mut source_partition);
        for n in [bits.len(), physical_bits.len(), chunks.len()] {
            crate::codec::Nat::new(n as u64).put(&mut source_partition);
        }
        for size in &chunks {
            crate::codec::Nat::new(*size as u64).put(&mut source_partition);
        }
        let mut by_holder = vec![vec![]; 4];
        for group in 0..stock_count {
            let width = (count - 32 * group).min(32);
            if stock_count > 32 && group % 32 == 0 {
                eprintln!("reference preprocessing (OS/seeded entropy): {group}/{stock_count} stocks");
            }
            for (holder, s) in triple_king::tests::checked_inventory_generation(
                width,
                instance + group as u64,
                g,
            )
            .into_iter()
            .enumerate()
            {
                by_holder[holder].push(s);
            }
        }
        let root = crate::entropy::test_root();
        let mut offset = 0;
        let parties = chunks
            .iter()
            .enumerate()
            .map(|(chunk, size)| {
                let label = format!("boolean-many/{instance}/{chunk}");
                let p = InputParty::from_bits(
                    0,
                    &physical_bits[offset..offset + size],
                    &mut root.fork(label.as_bytes()),
                );
                offset += size;
                p
            })
            .collect::<Vec<_>>();
        // The single zero pad is a real shared input never referenced by the graph.
        let shared = share_inputs(&parties.iter().collect::<Vec<_>>(), g, &mut Tap::none());
        let mut engines = vec![];
        let mut anchors = vec![];
        for holder in 0..4 {
            let mut refs = vec![];
            for states in &shared {
                for index in 0..states[holder].count {
                    if refs.len() == bits.len() {
                        break;
                    }
                    refs.push(InputRef::new(states[holder].clone(), g.clone(), index).unwrap());
                }
            }
            assert_eq!(refs.len(), bits.len());
            let checked = by_holder[holder].iter().collect::<Vec<_>>();
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
            engines.push(LayerEngine::new(origin).unwrap());
            anchors.push(a);
        }
        let mut q = VecDeque::<(u16, Send)>::new();
        for p in &mut engines {
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
                engines[to as usize]
                    .receive(sender, decoded)
                    .unwrap()
                    .into_iter()
                    .map(|v| (to, v)),
            );
        }
        assert!(engines
            .iter()
            .all(|v| v.output().is_some() && v.failure().is_none()));
        (engines, anchors)
    }
}
