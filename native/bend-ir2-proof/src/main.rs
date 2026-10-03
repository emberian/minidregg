//! Offline proof conformance harness. This is not a world admission endpoint.
//! It consumes Lean-authored descriptors and witnesses; it authors no AIR.
mod config;
mod masking_budget;
mod full_degree_challenger;
use dregg_circuit::{BabyBear, descriptor_ir2::{parse_vm_descriptor2,
    check_descriptor2_wellformed, prove_vm_descriptor2_for_config,
    EffectVmDescriptor2, TableSem, VmConstraint2, WindowExpr,
    verify_vm_descriptor2_with_config, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness}};
use std::{collections::BTreeSet, error::Error, fs, path::Path};
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};

const MODULUS: u32 = 2_013_265_921;
fn read_fields(path: &Path) -> Result<Vec<BabyBear>, Box<dyn Error>> {
    let bytes = fs::read_to_string(path)?;
    let body = bytes.strip_suffix('\n').ok_or("missing canonical trailing newline")?;
    if body.is_empty() { return Ok(vec![]); }
    body.split(',').map(|text| {
        let value: u32 = text.parse()?;
        if value >= MODULUS || text != value.to_string() {
            return Err("noncanonical BabyBear element".into());
        }
        Ok(BabyBear::new_canonical(value))
    }).collect()
}
// This prototype deliberately accepts only the emitted local-row relation.
// Secret-bearing lookup/auxiliary tables need their own masking-height ledger.
fn local_only(expression: &WindowExpr) -> bool {
    match expression {
        WindowExpr::Loc(_) | WindowExpr::Const(_) => true,
        WindowExpr::Add(a, b) | WindowExpr::Mul(a, b) => local_only(a) && local_only(b),
        WindowExpr::Nxt(_) => false,
    }
}
fn require_subset(descriptor: &EffectVmDescriptor2) -> Result<(), Box<dyn Error>> {
    if descriptor.challenges != 0 || !descriptor.hash_sites.is_empty() || !descriptor.ranges.is_empty()
        || descriptor.tables.len() != 1 || descriptor.tables[0].sem != TableSem::Main {
        return Err("descriptor outside supported local-row grammar".into());
    }
    let mut pinned = BTreeSet::new();
    for constraint in &descriptor.constraints {
        match constraint {
            VmConstraint2::WindowGate(gate) if !gate.on_transition && local_only(&gate.body) => {},
            VmConstraint2::Base(VmConstraint::PiBinding { row: VmRow::First, col, pi_index })
                if *col < descriptor.trace_width && *pi_index < descriptor.public_input_count => {
                if !pinned.insert(*pi_index) { return Err("duplicate public pin".into()); }
            },
            _ => return Err("descriptor outside emitted local-row grammar".into()),
        }
    }
    if pinned.len() != descriptor.public_input_count { return Err("missing public pin".into()); }
    Ok(())
}
// This profile's public capacity is derived from its exact opening budget.
// It addresses trace-opening leakage only; full transcript hiding remains open.
fn check_proof_shape(proof: &Ir2BatchProof<config::Config>,
    capacity: masking_budget::TraceCapacity) -> Result<(), Box<dyn Error>> {
    if proof.degree_bits != [capacity.extended_log_height()] {
        return Err("unexpected proof instances or masking capacity".into());
    }
    Ok(())
}

fn run() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = std::env::args().collect();
    if !(args.len() == 6 && args[1] == "prove" || args.len() == 5 && args[1] == "verify") {
        return Err("usage: bend-ir2-proof prove descriptor.json public.csv trace.csv proof.bin; or verify descriptor.json public.csv proof.bin".into());
    }
    let descriptor = parse_vm_descriptor2(&fs::read_to_string(&args[2])?)?;
    check_descriptor2_wellformed(&descriptor)?;
    require_subset(&descriptor)?;
    let public = read_fields(Path::new(&args[3]))?;
    if public.len() != descriptor.public_input_count { return Err("public length mismatch".into()); }
    let capacity = masking_budget::TraceCapacity::checked(masking_budget::MIN_TRACE_ROWS)?;
    let config = config::for_capacity(capacity).map_err(|error| format!("proof entropy unavailable: {error}"))?;
    if args[1] == "prove" {
        let row = read_fields(Path::new(&args[4]))?;
        if row.len() != descriptor.trace_width { return Err("trace width mismatch".into()); }
        let trace = vec![row; capacity.rows()];
        let proof = prove_vm_descriptor2_for_config(&descriptor, &trace, &public,
            &MemBoundaryWitness::default(), &[], &UMemBoundaryWitness::default(), &config)?;
        check_proof_shape(&proof, capacity)?;
        verify_vm_descriptor2_with_config(&descriptor, &proof, &public, &config)?;
        fs::write(&args[5], postcard::to_allocvec(&proof)?)?;
    } else {
        let bytes = fs::read(&args[4])?;
        let (proof, rest): (Ir2BatchProof<config::Config>, _) = postcard::take_from_bytes(&bytes)?;
        if !rest.is_empty() { return Err("trailing proof bytes".into()); }
        check_proof_shape(&proof, capacity)?;
        verify_vm_descriptor2_with_config(&descriptor, &proof, &public, &config)?;
    }
    println!("PASS profile={} mode={}; experimental backend conformance only", config::PROFILE, args[1]);
    Ok(())
}
fn main() -> Result<(), Box<dyn Error>> { run() }
