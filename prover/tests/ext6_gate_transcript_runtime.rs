//! Focused teeth for the isolated atomic-Ext6 gate transcript path.

use minidregg_prover::{
    descriptor::{Descriptor, Fp, Gate, GateOp, Wire},
    field4::{badd, bmul, P},
    field6::Ext6,
    gate_sumcheck_ext6::{prove_clear_gate_ext6, verify_clear_gate_ext6},
    poseidon::demo_spec,
    transcript_ext6::{
        Ext6Transcript, Ext6TranscriptError, WideExt6Backend, EXT6_FIELD_SUITE,
        EXT6_MIN_CAPACITY_BITS,
    },
};

/// Sixteen-coordinate deterministic schedule oracle used only for conformance.
/// Its constants advertise the security *interface* expected by the protocol;
/// this test double is not a cryptographic instantiation of that interface.
#[derive(Debug, Clone)]
struct TestWideBackend {
    state: [Fp; 16],
    absorbed: Vec<Vec<Fp>>,
    draws: Vec<[Fp; 6]>,
    malformed_next_draw: bool,
}

impl Default for TestWideBackend {
    fn default() -> Self {
        Self {
            state: [0; 16],
            absorbed: Vec::new(),
            draws: Vec::new(),
            malformed_next_draw: false,
        }
    }
}

impl TestWideBackend {
    fn permute(&mut self) {
        for round in 0..5 {
            let previous = self.state;
            for i in 0..16 {
                let left = previous[(i + 15) % 16];
                let right = previous[(i + 1) % 16];
                let diagonal = bmul(previous[i], (i + 3) as Fp);
                self.state[i] = badd(
                    badd(diagonal, left),
                    badd(bmul(right, 17), (round * 19 + i + 1) as Fp),
                );
            }
        }
    }
}

impl WideExt6Backend for TestWideBackend {
    const JOINT_CHALLENGE_COORDINATES: usize = 6;
    const CAPACITY_BITS: usize = EXT6_MIN_CAPACITY_BITS;

    fn absorb(&mut self, fields: &[Fp]) -> Result<(), String> {
        self.absorbed.push(fields.to_vec());
        for (offset, &field) in fields.iter().enumerate() {
            self.state[offset % 16] = badd(self.state[offset % 16], field);
            self.state[(offset * 7 + 3) % 16] = badd(
                self.state[(offset * 7 + 3) % 16],
                bmul(field, (offset + 1) as Fp),
            );
            self.permute();
        }
        Ok(())
    }

    fn squeeze_joint_ext6(&mut self) -> Result<[Fp; 6], String> {
        self.permute();
        let mut output = [0; 6];
        output.copy_from_slice(&self.state[..6]);
        if self.malformed_next_draw {
            output[4] = P;
            self.malformed_next_draw = false;
        }
        self.draws.push(output);
        self.state.rotate_left(6);
        Ok(output)
    }
}

#[derive(Default)]
struct NarrowBackend(TestWideBackend);

impl WideExt6Backend for NarrowBackend {
    const JOINT_CHALLENGE_COORDINATES: usize = 2;
    const CAPACITY_BITS: usize = EXT6_MIN_CAPACITY_BITS;

    fn absorb(&mut self, fields: &[Fp]) -> Result<(), String> {
        self.0.absorb(fields)
    }

    fn squeeze_joint_ext6(&mut self) -> Result<[Fp; 6], String> {
        self.0.squeeze_joint_ext6()
    }
}

fn descriptor(add_constant: Fp) -> Descriptor {
    let descriptor = Descriptor {
        p: P,
        n_public: 1,
        n_vars: 1,
        n_wires: 3,
        gates: vec![
            Gate {
                op: GateOp::Add,
                a: Wire::Wire(0),
                b: Wire::Const(add_constant),
                out: 1,
            },
            Gate {
                op: GateOp::Mul,
                a: Wire::Wire(1),
                b: Wire::Wire(0),
                out: 2,
            },
        ],
        zeros: vec![Wire::Wire(2)],
    };
    descriptor.validate().unwrap();
    descriptor
}

#[test]
fn narrow_state_profile_cannot_enter_the_ext6_transcript() {
    let mut backend = NarrowBackend::default();
    let error = match Ext6Transcript::new(&mut backend) {
        Ok(_) => panic!("a two-coordinate backend must not construct an Ext6 transcript"),
        Err(error) => error,
    };
    assert_eq!(
        error,
        Ext6TranscriptError::InsufficientJointCoordinates {
            required: 6,
            actual: 2
        }
    );
    assert!(backend.0.absorbed.is_empty());
}

#[test]
fn field_suite_is_the_first_bound_record_and_bad_lanes_fail_closed() {
    let mut backend = TestWideBackend::default();
    {
        let _transcript = Ext6Transcript::new(&mut backend).unwrap();
    }
    assert_eq!(&backend.absorbed[0][3..], &EXT6_FIELD_SUITE);

    let mut malformed = TestWideBackend {
        malformed_next_draw: true,
        ..TestWideBackend::default()
    };
    let mut transcript = Ext6Transcript::new(&mut malformed).unwrap();
    assert_eq!(
        transcript.squeeze_ext6(7),
        Err(Ext6TranscriptError::NonCanonicalChallenge { lane: 4, value: P })
    );
}

#[test]
fn clear_gate_round_trip_replays_every_atomic_challenge() {
    let descriptor = descriptor(0);
    let public = [0];
    let trace = [0, 0, 0];
    let spec = demo_spec();

    let mut prover_backend = TestWideBackend::default();
    let proof =
        prove_clear_gate_ext6(&descriptor, &public, &trace, &spec, &mut prover_backend).unwrap();
    assert_eq!(proof.sumcheck.rounds.len(), 2);

    let mut verifier_backend = TestWideBackend::default();
    assert!(verify_clear_gate_ext6(
        &descriptor,
        &public,
        &trace,
        &proof,
        &spec,
        &mut verifier_backend,
    )
    .unwrap());
    assert_eq!(prover_backend.draws, verifier_backend.draws);
    assert_eq!(prover_backend.draws.len(), 3, "gamma plus two rounds");
}

#[test]
fn statement_and_each_absorbed_message_lane_have_teeth() {
    let honest_descriptor = descriptor(0);
    let changed_descriptor = descriptor(1);
    let public = [0];
    let trace = [0, 0, 0];
    let spec = demo_spec();

    let mut honest_backend = TestWideBackend::default();
    let proof = prove_clear_gate_ext6(
        &honest_descriptor,
        &public,
        &trace,
        &spec,
        &mut honest_backend,
    )
    .unwrap();
    let mut changed_backend = TestWideBackend::default();
    let _changed_proof = prove_clear_gate_ext6(
        &changed_descriptor,
        &public,
        &trace,
        &spec,
        &mut changed_backend,
    )
    .unwrap();
    assert_ne!(
        honest_backend.draws[0], changed_backend.draws[0],
        "descriptor is bound before gamma"
    );
    let mut replay_changed = TestWideBackend::default();
    assert!(!verify_clear_gate_ext6(
        &changed_descriptor,
        &public,
        &trace,
        &proof,
        &spec,
        &mut replay_changed,
    )
    .unwrap());

    for round in 0..proof.sumcheck.rounds.len() {
        for endpoint in 0..2 {
            for lane in 0..6 {
                let mut tampered = proof.clone();
                let mut limbs = *tampered.sumcheck.rounds[round][endpoint].limbs();
                limbs[lane] = badd(limbs[lane], 1);
                tampered.sumcheck.rounds[round][endpoint] = Ext6::try_from_limbs(limbs).unwrap();
                let mut backend = TestWideBackend::default();
                assert!(!verify_clear_gate_ext6(
                    &honest_descriptor,
                    &public,
                    &trace,
                    &tampered,
                    &spec,
                    &mut backend,
                )
                .unwrap());
                assert_ne!(
                    honest_backend.draws[round + 1],
                    backend.draws[round + 1],
                    "round {round}, endpoint {endpoint}, lane {lane}"
                );
            }
        }
    }
}

#[test]
fn malformed_root_and_round_shapes_reject_without_panicking() {
    let descriptor = descriptor(0);
    let public = [0];
    let trace = [0, 0, 0];
    let spec = demo_spec();
    let mut prover_backend = TestWideBackend::default();
    let proof =
        prove_clear_gate_ext6(&descriptor, &public, &trace, &spec, &mut prover_backend).unwrap();

    let mut short = proof.clone();
    short.sumcheck.rounds.pop();
    let mut backend = TestWideBackend::default();
    assert!(
        !verify_clear_gate_ext6(&descriptor, &public, &trace, &short, &spec, &mut backend,)
            .unwrap()
    );

    let mut long = proof.clone();
    long.sumcheck.rounds.push([Ext6::ZERO; 2]);
    let mut backend = TestWideBackend::default();
    assert!(
        !verify_clear_gate_ext6(&descriptor, &public, &trace, &long, &spec, &mut backend,).unwrap()
    );

    let mut malformed_root = proof;
    malformed_root.trace_root.limbs[3] = P;
    let mut backend = TestWideBackend::default();
    assert!(!verify_clear_gate_ext6(
        &descriptor,
        &public,
        &trace,
        &malformed_root,
        &spec,
        &mut backend,
    )
    .unwrap());
}
