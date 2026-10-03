//! Adversarial regression for the raw backend, never a production guard edit.
//! A one-row main trace gets only one independent masking row. Its degree-one
//! base-field polynomial can be recovered from one extension-field opening.
//! This test exercises the raw IR2 API directly; the CLI now refuses this shape.
#[path = "../src/config.rs"]
mod config;
use dregg_circuit::{BabyBear, descriptor_ir2::{parse_vm_descriptor2,
    prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
    MemBoundaryWitness, UMemBoundaryWitness}};
use p3_batch_stark::BatchTranscript;
use p3_field::{BasedVectorSpace, Field, PrimeField32};
use p3_uni_stark::StarkGenericConfig;
use std::{fs, path::PathBuf};

fn fields(path: PathBuf) -> Vec<BabyBear> {
    fs::read_to_string(path).unwrap().trim_end().split(',')
        .map(|value| BabyBear::new_canonical(value.parse().unwrap())).collect()
}

#[test]
fn raw_one_row_hiding_proof_reveals_trace_coefficients() {
    let fixture = PathBuf::from(std::env::var("BEND_IR2_FIXTURE")
        .expect("set BEND_IR2_FIXTURE to the actual Lean-emitted fixture directory"));
    let descriptor = parse_vm_descriptor2(&fs::read_to_string(fixture.join("descriptor.json")).unwrap()).unwrap();
    let row = fields(fixture.join("trace.csv"));
    let public = fields(fixture.join("public.csv"));
    let alternate = fields(fixture.join("alternate-trace.csv"));
    assert_ne!(row[5], alternate[5], "the private bit is not determined by public13");
    let config = config::fresh().unwrap();
    let proof = prove_vm_descriptor2_for_config(&descriptor, std::slice::from_ref(&row), &public,
        &MemBoundaryWitness::default(), &[], &UMemBoundaryWitness::default(), &config).unwrap();
    verify_vm_descriptor2_with_config(&descriptor, &proof, &public, &config).unwrap();
    let alternate_proof = prove_vm_descriptor2_for_config(&descriptor,
        std::slice::from_ref(&alternate), &public, &MemBoundaryWitness::default(),
        &[], &UMemBoundaryWitness::default(), &config).unwrap();
    verify_vm_descriptor2_with_config(&descriptor, &alternate_proof, &public, &config).unwrap();
    assert_eq!(proof.degree_bits, [1], "this regression specifically targets one real row");
    assert!(proof.commitments.permutation.is_none());
    let opened = &proof.opened_values.instances[0].base_opened_values;

    // Replay the public verifier transcript for this no-lookup/no-preprocess
    // local-row descriptor. No RNG state, secret seed or prover data is read.
    let mut transcript = BatchTranscript::<config::Config>::new(config.initialise_challenger());
    transcript.observe_instance_count(1);
    transcript.observe_instance_binding(1, 0, descriptor.trace_width, opened.quotient_chunks.len());
    let pi: Vec<_> = public.iter().map(|value| p3_baby_bear::BabyBear::new(value.as_u32())).collect();
    transcript.observe_main(&proof.commitments.main, &[pi]);
    transcript.observe_preprocessed(&[0], None);
    let _alpha = transcript.observe_perm_and_sample_alpha(None, &proof.global_lookup_data);
    transcript.observe_quotient_commitment(&proof.commitments.quotient_chunks);
    transcript.observe_random_commitment(proof.commitments.random.as_ref().unwrap());
    let zeta = transcript.sample_zeta();
    let z: &[p3_baby_bear::BabyBear] = zeta.as_basis_coefficients_slice();
    let pivot = (1..z.len()).find(|&i| !z[i].is_zero())
        .expect("exceptional base-field zeta; repeat the randomized regression");

    // y=a+b*zeta, with a,b in the base field. A nonbase coordinate gives b;
    // coordinate zero gives a. The original singleton trace domain is {1}.
    let recovered: Vec<u32> = opened.trace_local.iter().map(|value| {
        let y: &[p3_baby_bear::BabyBear] = value.as_basis_coefficients_slice();
        let b = y[pivot] / z[pivot];
        let a = y[0] - b * z[0];
        (a + b).as_canonical_u32()
    }).collect();
    assert_eq!(recovered, row.iter().map(|value| value.as_u32()).collect::<Vec<_>>());
}
