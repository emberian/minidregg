//! Exact artifact-byte binding is distinct from source authenticity and FS soundness.
#[path = "../src/config.rs"] mod config;
#[path = "../src/masking_budget.rs"] mod masking_budget;
#[path = "../src/full_degree_challenger.rs"] mod full_degree_challenger;
use dregg_circuit::{BabyBear, descriptor_ir2::{parse_vm_descriptor2,
    prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
    MemBoundaryWitness, UMemBoundaryWitness}};
use std::{fs, path::PathBuf};

#[test]
fn exact_artifact_profile_rejects_semantically_equal_changed_bytes() {
    let directory = PathBuf::from(std::env::var("BEND_IR2_FIXTURE").unwrap());
    let bytes = fs::read_to_string(directory.join("descriptor.json")).unwrap();
    let changed_bytes = format!("{bytes} "); // Parser ignores it; transcript must not.
    let descriptor = parse_vm_descriptor2(&bytes).unwrap();
    let changed = parse_vm_descriptor2(&changed_bytes).unwrap();
    let fields = |name| -> Vec<BabyBear> {
        fs::read_to_string(directory.join(name)).unwrap().trim_end().split(',')
            .map(|v| BabyBear::new_canonical(v.parse().unwrap())).collect()
    };
    let row = fields("trace.csv");
    let public = fields("public.csv");
    let capacity = masking_budget::TraceCapacity::checked(32).unwrap();
    let exact = config::for_artifact(capacity, bytes.as_bytes()).unwrap();
    let different = config::for_artifact(capacity, changed_bytes.as_bytes()).unwrap();
    let old = config::for_capacity(capacity).unwrap();
    let trace = vec![row; capacity.rows()];
    let proof = prove_vm_descriptor2_for_config(&descriptor, &trace, &public,
        &MemBoundaryWitness::default(), &[], &UMemBoundaryWitness::default(), &exact).unwrap();
    verify_vm_descriptor2_with_config(&descriptor, &proof, &public, &exact).unwrap();
    // Establish the two parsed AIRs are equivalent for this proof under SAME seed.
    verify_vm_descriptor2_with_config(&changed, &proof, &public, &exact).unwrap();
    assert!(verify_vm_descriptor2_with_config(&changed, &proof, &public, &different).is_err());
    assert!(verify_vm_descriptor2_with_config(&descriptor, &proof, &public, &old).is_err());
    assert_ne!(config::artifact_digest(bytes.as_bytes()), config::artifact_digest(changed_bytes.as_bytes()));
}
