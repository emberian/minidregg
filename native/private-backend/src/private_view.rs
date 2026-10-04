//! Input secrecy against one honest-but-curious party, checked on the recorded
//! transcript of the width-8 private adder.
//!
//! Holder 0 privately deals `left`, holder 2 privately deals `right`; holder 1 is
//! the only output recipient; holder 0 is the King. Holder 3 (CURIOUS) follows
//! the protocol and logs every message delivered to it, in order, across the
//! input ACSS, the King preprocessing ACSS/Sh2t, the King, the layered MPC and
//! the recipient-output phase.
//!
//! The check is a constructed alternative world. From world A's honest
//! randomness the simulator below builds world B with DIFFERENT inputs (and the
//! same sum, so the output phase is comparable too): every honest dealing
//! polynomial is moved by delta*L(X) with L(0)=1, L(alpha_3)=0, so holder 3's
//! points never move, and the King extraction/check randomness is moved so that
//! every opened value (DN products, masked check points, challenge, check
//! polynomials, every MPC opening and bit check) is unchanged. World B is then
//! RUN through the actual protocol, and holder 3's two transcripts are compared
//! frame by frame.
//!
//! What equality covers: every frame except two classes, which are asserted to
//! be the only differences —
//!   * PrivSend ciphertexts of ACSS rows addressed to OTHER holders: a SHA-256
//!     pad keyed by an ASKS key of which holder 3 holds one degree-f share;
//!   * dZK column-proof frames: salted Merkle roots and challenge-dependent folds.
//! Their hiding is the classical-ROM property of those components; this test
//! does not simulate them. So the statement is: holder 3's view, apart from
//! ROM-hidden frames, is byte-for-byte consistent with at least two distinct
//! input pairs. That is not a simulator proof, and says nothing about the King's
//! (holder 0's) richer view, a malicious party, or a coalition.
#![cfg(test)]
use crate::{
    acss_id::{self, AcssId},
    arithmetic_reference::tests::{completed_private_inputs_with_states, share_inputs, InputParty},
    circuit_batch::{Network, Op, Plan},
    codec::Generation,
    entropy::Entropy,
    private_output_store::tests::{drive_tapped, stores_from_completed_descriptor},
    reconstruction::Field,
    transcript::{Frame, Tap, Wire},
    triple_king::{
        acss_seed_count, per_group,
        tests::{checked_from_material, prepared_from, test_generation, PrepDealing},
    },
};
use std::collections::{BTreeMap, VecDeque};

const CURIOUS: u16 = 3;
const RECIPIENT: u16 = 1;
const COUNT: usize = 32;

fn alpha(holder: u16) -> Field {
    Field(holder as u128 + 1)
}
fn bits(value: u64, width: usize) -> Vec<bool> {
    (0..width).map(|i| (value >> i) & 1 == 1).collect()
}
/// Every wire value of the qualified network in the clear (simulator only).
fn wires(net: &Network, inputs: &[bool]) -> Vec<Field> {
    let mut w = inputs.iter().map(|b| Field(*b as u128)).collect::<Vec<_>>();
    for op in &net.gates {
        let v = match *op {
            Op::Constant(c) => Field(c as u128),
            Op::Xor(a, b) => w[a as usize].add(w[b as usize]),
            Op::And(a, b) => w[a as usize].mul(w[b as usize]),
        };
        w.push(v);
    }
    w
}
/// Per tuple position (k-th AND in gate order, the Schedule assignment): the
/// change of its left and right operand between the two worlds.
fn operand_deltas(net: &Network, a: &[bool], b: &[bool]) -> (Vec<Field>, Vec<Field>) {
    let (wa, wb) = (wires(net, a), wires(net, b));
    let (mut dl, mut dr) = (vec![], vec![]);
    for op in &net.gates {
        if let Op::And(l, r) = *op {
            dl.push(wa[l as usize].add(wb[l as usize]));
            dr.push(wa[r as usize].add(wb[r as usize]));
        }
    }
    (dl, dr)
}
fn lagrange(xs: &[Field], k: usize, t: Field) -> Field {
    let mut num = Field(1);
    let mut den = Field(1);
    for (j, x) in xs.iter().enumerate() {
        if j != k {
            num = num.mul(t.add(*x));
            den = den.mul(xs[k].add(*x));
        }
    }
    num.mul(den.inv().unwrap())
}
/// King extraction exactly as PreparedBasis::reserve_new computes it, applied to
/// the dealers' secrets (constant terms) — the simulator knows honest dealings.
fn extract(dealings: &[PrepDealing], offset: usize, batch: usize, m: usize) -> Vec<Field> {
    let mut out = vec![];
    for index in 0..batch {
        for row in 0..2u32 {
            let v = dealings.iter().enumerate().fold(Field(0), |sum, (col, d)| {
                let a = if row == 0 { Field(1) } else { alpha(col as u16) };
                sum.add(a.mul(d.acss[offset + index][0]))
            });
            out.push(v);
        }
    }
    out.truncate(m);
    out
}
/// SIMULATOR WITNESS for the King preprocessing: given world A's dealings and
/// the required per-tuple changes of a and b (operand deltas), return dealings
/// for world B whose holder-3 points and every opened King value are unchanged
/// while each used triple is a'=a+da, b'=b+db, c'=a'b'.
fn equivocate_preparation(
    a: &[PrepDealing],
    da: &[Field],
    db: &[Field],
) -> Vec<PrepDealing> {
    let batch = per_group(COUNT, 1).unwrap();
    let m = 2 * COUNT + 1;
    assert_eq!(a.len(), 3);
    assert!(a.iter().enumerate().all(|(i, d)| d.dealer == i as u16));
    assert!(a.iter().all(|d| d.acss.len() == acss_seed_count(COUNT, 1).unwrap()));
    let va = extract(a, 0, batch, m);
    let vb = extract(a, batch, batch, m);
    // The public challenge is the sum of the dealers' check secrets; untouched.
    let r = a.iter().fold(Field(0), |s, d| s.add(d.acss[3 * batch][0]));
    let xs = (0..=COUNT).map(|i| Field(i as u128 + 1)).collect::<Vec<_>>();
    assert!(!(1..=m).any(|i| r == Field(i as u128)), "challenge in interpolation set");
    // Tuple k is King index k+1. Index 0 is chosen so the interpolated change
    // F' - F vanishes at the challenge; each mask index i in count+1..=2count
    // follows the change at its point so the opened masked values stay put.
    let complete = |used: &[Field]| -> Vec<Field> {
        let mut d = vec![Field(0); m];
        d[1..=COUNT].copy_from_slice(used);
        let rest = (1..=COUNT).fold(Field(0), |s, k| s.add(d[k].mul(lagrange(&xs, k, r))));
        d[0] = rest.mul(lagrange(&xs, 0, r).inv().unwrap());
        for i in COUNT + 1..m {
            let at = Field(i as u128 + 1);
            d[i] = (0..=COUNT).fold(Field(0), |s, k| s.add(d[k].mul(lagrange(&xs, k, at))));
        }
        let at_r = (0..=COUNT).fold(Field(0), |s, k| s.add(d[k].mul(lagrange(&xs, k, r))));
        assert_eq!(at_r, Field(0));
        d
    };
    let delta_a = complete(da);
    let delta_b = complete(db);
    let delta_r = (0..m)
        .map(|i| {
            let (a1, b1) = (va[i].add(delta_a[i]), vb[i].add(delta_b[i]));
            a1.mul(b1).add(va[i].mul(vb[i]))
        })
        .collect::<Vec<_>>();
    let slope = alpha(CURIOUS).inv().unwrap();
    let three = Field(1).add(alpha(1)).inv().unwrap();
    let mut out = a.to_vec();
    for (offset, delta) in [(0, &delta_a), (batch, &delta_b), (2 * batch, &delta_r)] {
        for index in 0..batch {
            let d0 = delta[2 * index];
            let d1 = if 2 * index + 1 < m { delta[2 * index + 1] } else { Field(0) };
            // Columns 0 (alpha 1) and 1 (alpha 2) absorb (row0,row1) = (d0,d1).
            let s1 = d0.add(d1).mul(three);
            let s0 = d0.add(s1);
            for (col, s) in [(0, s0), (1, s1)] {
                let p = &mut out[col].acss[offset + index];
                p[0] = p[0].add(s);
                p[1] = p[1].add(s.mul(slope));
            }
        }
    }
    let (va2, vb2) = (extract(&out, 0, batch, m), extract(&out, batch, batch, m));
    for k in 0..COUNT {
        assert_eq!(va2[k + 1], va[k + 1].add(da[k]));
        assert_eq!(vb2[k + 1], vb[k + 1].add(db[k]));
    }
    out
}

struct World {
    frames: Vec<Frame>,
    result: Vec<bool>,
    inputs: Vec<Vec<AcssId>>,
}
fn run_world(
    left: &InputParty,
    right: &InputParty,
    preparation: &[PrepDealing],
    output_seed: [u8; 32],
    instance: u64,
) -> World {
    let source = include_bytes!("../fixtures/addition-network-8-plan.bin");
    let network =
        crate::field_network::with_boolean_inputs(&Plan::decode(source).unwrap().network).unwrap();
    let g: Generation = test_generation(300 + 1000 * instance);
    let mut tap = Tap::on(CURIOUS);
    let material = prepared_from(preparation, COUNT, instance, &mut tap);
    let stocks = checked_from_material(material, COUNT, &g, &mut tap)
        .into_iter()
        .map(|s| vec![s])
        .collect::<Vec<_>>();
    let (completed, anchors, inputs) = completed_private_inputs_with_states(
        &[left, right],
        network,
        source,
        &g,
        &stocks,
        &format!("view{instance}"),
        &mut tap,
    );
    let (mut stores, _anchors, _paths) = stores_from_completed_descriptor(
        completed,
        anchors,
        instance,
        b"private-input width8 addition; result to holder 1 only; no native release grant",
    );
    let keys = Entropy::from_seed(output_seed);
    let mut q = VecDeque::new();
    for (holder, s) in stores.iter_mut().enumerate() {
        let mut e = keys.fork(&[holder as u8]);
        q.extend(
            s.as_mut()
                .unwrap()
                .start_with_entropy(&mut e)
                .unwrap()
                .into_iter()
                .map(|p| (holder as u16, p)),
        );
    }
    drive_tapped(&mut stores, &mut q, false, false, &mut tap);
    for (holder, s) in stores.iter_mut().enumerate() {
        q.extend(
            s.as_mut()
                .unwrap()
                .request_delivery()
                .unwrap()
                .into_iter()
                .map(|p| (holder as u16, p)),
        );
    }
    drive_tapped(&mut stores, &mut q, false, false, &mut tap);
    for (holder, s) in stores.iter().enumerate() {
        assert_eq!(
            s.as_ref().unwrap().state().result().is_some(),
            holder as u16 == RECIPIENT
        );
    }
    let result = stores[RECIPIENT as usize]
        .as_ref()
        .unwrap()
        .state()
        .result()
        .unwrap()
        .bits()
        .to_vec();
    World {
        frames: tap.frames,
        result,
        inputs,
    }
}
fn accepted(s: &AcssId) -> Vec<Field> {
    match s.local_sharing() {
        Some(acss_id::LocalSharing::Accepted(v)) => v.shares().to_vec(),
        _ => panic!("input sharing not accepted"),
    }
}
/// Auditor (not the harness path): reconstruct a dealt value from two honest
/// holders' accepted shares.
fn reconstruct(states: &[AcssId], holders: [u16; 2]) -> u64 {
    let points = holders
        .iter()
        .map(|h| (*h, accepted(&states[*h as usize])))
        .collect::<Vec<_>>();
    let polys = acss_id::polynomial(&points, states[0].count).unwrap();
    polys.iter().enumerate().fold(0, |v, (i, p)| {
        assert!(p[0] == Field(0) || p[0] == Field(1));
        v | ((p[0].0 as u64) << i)
    })
}
fn value(result: &[bool]) -> u64 {
    result.iter().enumerate().fold(0, |v, (i, b)| v | ((*b as u64) << i))
}
/// Frames that may differ: ROM-hidden PrivSend ciphertexts of other holders'
/// ACSS rows, and dZK column-proof frames. Everything else must be identical.
fn rom_hidden(frame: &Frame) -> Option<&'static str> {
    let Wire::Acss(m) = &frame.wire else {
        return None;
    };
    match &m.body {
        acss_id::Body::Row { holder, message } if *holder != CURIOUS => match message.body {
            crate::private_send::Body::Cipher(_) => Some("acss-row-cipher(other holder)"),
            _ => None,
        },
        acss_id::Body::Column { .. } => Some("acss-dzk-column"),
        _ => None,
    }
}
/// Compare two curious transcripts; returns per (phase, class) counts.
fn compare(a: &[Frame], b: &[Frame]) -> BTreeMap<(String, &'static str), usize> {
    assert_eq!(a.len(), b.len(), "curious transcript length");
    let mut counts = BTreeMap::new();
    for (i, (x, y)) in a.iter().zip(b).enumerate() {
        assert_eq!((&x.phase, x.sender), (&y.phase, y.sender), "frame {i} order");
        let class = if x.wire == y.wire {
            "identical"
        } else {
            let (cx, cy) = (rom_hidden(x), rom_hidden(y));
            assert!(
                cx.is_some() && cx == cy,
                "frame {i} ({}, from {}) differs outside the ROM-hidden classes:\n{:?}\n{:?}",
                x.phase,
                x.sender,
                x.wire,
                y.wire
            );
            cx.unwrap()
        };
        *counts.entry((x.phase.clone(), class)).or_insert(0) += 1;
    }
    counts
}

#[test]
fn curious_holder_view_is_consistent_with_three_input_pairs_and_recipient_gets_256() {
    let root = crate::entropy::test_root();
    let width = 8;
    let instance = 9100;
    let left = InputParty::new(0, 255, width, &mut root.fork(b"view/left"));
    let right = InputParty::new(2, 1, width, &mut root.fork(b"view/right"));
    let preparation = (0..3u16)
        .map(|d| PrepDealing::sample(d, COUNT, false, &mut root.fork(&[b'k', d as u8])))
        .collect::<Vec<_>>();
    let output_seed = root.fork(b"view/output-keys").bytes32();
    let a = run_world(&left, &right, &preparation, output_seed, instance);
    assert_eq!(value(&a.result), 256, "recipient decryption of 255+1");
    assert_eq!(reconstruct(&a.inputs[0], [0, 1]), 255);
    assert_eq!(reconstruct(&a.inputs[1], [1, 2]), 1);
    assert!(!a.frames.is_empty());

    let source = include_bytes!("../fixtures/addition-network-8-plan.bin");
    let network =
        crate::field_network::with_boolean_inputs(&Plan::decode(source).unwrap().network).unwrap();
    let qualified = |l: u64, r: u64| [bits(l, width), bits(r, width)].concat();
    let mut seen = vec![(255u64, 1u64)];
    for (l, r) in [(1u64, 255u64), (128, 128)] {
        let (dl, dr) = operand_deltas(&network, &qualified(255, 1), &qualified(l, r));
        assert_eq!(dl.len(), COUNT);
        assert!(dl.iter().chain(&dr).any(|d| *d != Field(0)));
        let prep_b = equivocate_preparation(&preparation, &dl, &dr);
        let left_b = left.equivocate(l, CURIOUS);
        let right_b = right.equivocate(r, CURIOUS);
        let b = run_world(&left_b, &right_b, &prep_b, output_seed, instance);
        // World B is genuinely a different execution: honest holders hold
        // sharings of (l, r), and the recipient still decrypts the sum.
        assert_eq!(reconstruct(&b.inputs[0], [0, 1]), l);
        assert_eq!(reconstruct(&b.inputs[1], [1, 2]), r);
        assert_ne!(accepted(&b.inputs[0][0]), accepted(&a.inputs[0][0]));
        assert_eq!(value(&b.result), 256);
        // Holder 3's own input shares are identical: one point below threshold
        // determines neither bit of either input.
        for k in 0..2 {
            assert_eq!(accepted(&b.inputs[k][CURIOUS as usize]), accepted(&a.inputs[k][CURIOUS as usize]));
        }
        let counts = compare(&a.frames, &b.frames);
        eprintln!("curious view A=(255,1) vs B=({l},{r}): {} frames", a.frames.len());
        for ((phase, class), n) in &counts {
            eprintln!("  {phase:24} {class:32} {n}");
        }
        for phase in ["king-preparation-sh2t", "king", "layer-mpc", "output"] {
            assert!(counts.contains_key(&(phase.to_string(), "identical")), "{phase} observed");
            assert!(
                counts.keys().all(|(p, c)| p != phase || *c == "identical"),
                "{phase} frames all byte-identical"
            );
        }
        seen.push((l, r));
    }
    assert_eq!(seen.len(), 3);
}

/// The instrument goes red on the wound it exists to see: under the retired
/// r31 dealing (public degree-1 coefficient 37+i) holder 3 decodes the input
/// from its shares alone; under party-local entropy the same decoder fails.
#[test]
fn retired_public_coefficient_dealing_is_decoded_by_the_curious_holder() {
    let g = test_generation(9200);
    let decode = |shares: &[Field]| -> Option<u64> {
        let mut v = 0;
        for (i, s) in shares.iter().enumerate() {
            let bit = s.add(Field(37 + i as u128).mul(alpha(CURIOUS)));
            if bit != Field(0) && bit != Field(1) {
                return None;
            }
            v |= (bit.0 as u64) << i;
        }
        Some(v)
    };
    let retired = InputParty::retired_public_coefficient_dealing(0, 255, 8);
    let states = share_inputs(&[&retired], &g, &mut Tap::none());
    assert_eq!(decode(&accepted(&states[0][CURIOUS as usize])), Some(255));
    let private = InputParty::new(0, 255, 8, &mut crate::entropy::test_root().fork(b"view/falsifier"));
    let states = share_inputs(&[&private], &g, &mut Tap::none());
    assert_eq!(decode(&accepted(&states[0][CURIOUS as usize])), None);
    assert_eq!(reconstruct(&states[0], [0, 1]), 255);
}
