use minidregg_prover::svcs_smallval_engine::*;
use std::time::Instant;

fn fixtures() -> Vec<SvcsBundle> {
    let bytes = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/testdata/svcs_compiler_conformance.json"
    ))
    .unwrap();
    parse_conformance(&bytes).unwrap()
}

#[test]
fn lean_bundles_rounds_and_readback() {
    let bundles = fixtures();
    assert_eq!(
        bundles.iter().map(|b| b.name.as_str()).collect::<Vec<_>>(),
        [
            "evm_u8_add_carry",
            "einsum_i8_matmul_4x4x4",
            "byte_dfa_digits_logup"
        ]
    );
    for b in bundles {
        let z = &b.witness;
        assert!(b.lean_check && b.instance.satisfied(z));
        assert!(b.cost_after < b.cost_before);
        assert!(b.instance.rows.len() < b.rows_before as usize);
        assert_eq!(b.extract_witness(z).unwrap(), b.extracted);
        let (baseline, _) = b.prove(z, ProverMode::NaiveExt, b"conformance").unwrap();
        let (optimized, stats) = b
            .prove(z, ProverMode::SmallValueGruen, b"conformance")
            .unwrap();
        assert_eq!(stats.tags_valid, b.tags.len());
        assert_eq!(stats.tags_rejected, 0);
        assert_eq!(baseline, optimized);
        assert_eq!(
            b.verify_and_extract(z, &optimized, b"conformance").unwrap(),
            b.extracted
        );
        println!(
            "{}: cost {} -> {}, rows {} -> {}, wires {} -> {}, {} checked tags",
            b.name,
            b.cost_before,
            b.cost_after,
            b.rows_before,
            b.instance.rows.len(),
            b.n_z_before,
            b.instance.n_z,
            b.tags.len()
        );
    }
}

#[test]
fn oracle_statement_round_terminal_and_replay_falsifiers() {
    let b = fixtures().remove(1);
    let (i, z) = (&b.instance, &b.witness);
    let mode = ProverMode::SmallValueGruen;
    let (proof, _) = SvcsProver::prove_in_context(i, z, &b.tags, mode, b"job one").unwrap();
    let check = |i: &SvcsInstance, z: &[u32], p: &SvcsProof| {
        SvcsVerifier::verify_in_context(i, z, p, b"job one")
    };
    check(i, z, &proof).unwrap();
    assert!(SvcsVerifier::verify_in_context(i, z, &proof, b"job two").is_err());
    let mut forged = proof.clone();
    forged.repetitions[0].rounds[0][0] = forged.repetitions[0].rounds[0][0].add(Ext4::ONE);
    assert!(check(i, z, &forged).unwrap_err().contains("round 0"));
    // Swapping two terminal factors preserves their product. Only the oracle opening fails.
    let mut forged = proof.clone();
    forged.repetitions[0].terminal.swap(0, 1);
    assert!(check(i, z, &forged)
        .unwrap_err()
        .contains("batched terminal"));
    let mut forged = proof.clone();
    forged.repetitions[1] = proof.repetitions[0].clone();
    assert!(check(i, z, &forged).is_err());
    let mut changed = i.clone();
    let row = changed
        .rows
        .iter_mut()
        .find(|r| !r.prods.is_empty())
        .unwrap();
    row.prods[0].0[0].0 = row.prods[0].0[0].0.add(Fp::ONE);
    assert!(!changed.satisfied(z));
    assert!(check(&changed, z, &proof).is_err());
    for mode in [mode, ProverMode::NaiveExt] {
        let (bad, _) =
            SvcsProver::prove_in_context(&changed, z, &b.tags, mode, b"job one").unwrap();
        assert!(check(&changed, z, &bad).is_err());
    }
    let mut changed_z = z.clone();
    changed_z[1] = Fp(changed_z[1]).add(Fp::ONE).0;
    assert!(check(i, &changed_z, &proof).is_err());
    let mut forged = proof;
    forged.repetitions[1].rounds[0][0].0[0] = P;
    assert!(check(i, z, &forged).unwrap_err().contains("non-canonical"));
}

#[test]
fn compiler_readback_is_bound_to_the_proof() {
    let data = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/testdata/svcs_compiler_conformance.json"
    ))
    .unwrap();
    let json: serde_json::Value = serde_json::from_str(&data).unwrap();
    let mut bundle = json["bundles"][0].clone();
    let trusted = SvcsBundle::from_json(&bundle.to_string()).unwrap();
    let (proof, _) = trusted
        .prove(&trusted.witness, ProverMode::SmallValueGruen, b"extract")
        .unwrap();
    let form = bundle["extractor"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find_map(|step| step.get_mut("form"))
        .unwrap();
    form[0][0] = serde_json::json!(0);
    let changed = SvcsBundle::from_json(&bundle.to_string()).unwrap();
    assert_eq!(trusted.instance, changed.instance);
    assert_ne!(
        trusted.extracted,
        changed.extract_witness(&trusted.witness).unwrap()
    );
    assert!(changed
        .verify_and_extract(&trusted.witness, &proof, b"extract")
        .is_err());
}

#[test]
fn lookup_mass_and_fraction_falsifiers() {
    let b = fixtures().remove(2);
    let proof = SvcsProver::prove(&b.instance, &b.witness, ProverMode::SmallValueGruen).unwrap();
    let reject = |p: &SvcsProof| SvcsVerifier::verify(&b.instance, &b.witness, p).unwrap_err();
    let mut forged = proof.clone();
    forged.repetitions[0].lookups[0].mult[0] += 1;
    assert!(reject(&forged).contains("multiplicity count"));
    let mut forged = proof.clone();
    let m = &mut forged.repetitions[0].lookups[0].mult;
    let j = m.iter().position(|&n| n > 0).unwrap();
    let k = (j + 1) % m.len();
    m[j] -= 1;
    m[k] += 1;
    assert!(reject(&forged).contains("LogUp"));
    let mut forged = proof.clone();
    forged.repetitions[1].lookups[0].layers[1].rounds[0][0] = Ext4::ONE;
    assert!(reject(&forged).contains("LogUp layer"));
    let mut forged = proof;
    let lp = &mut forged.repetitions[1].lookups[0];
    lp.root[0] = Ext4::ONE;
    assert!(reject(&forged).contains("LogUp"));
}

fn product_rows(log_n: u32, wide: bool) -> (SvcsInstance, Vec<u32>) {
    let n = 1usize << log_n;
    let mut z = vec![1];
    let mut rows = Vec::with_capacity(n);
    for k in 0..n as i128 {
        let (a, b) = if wide {
            (
                (k * 1073741789 + 23) % P as i128,
                (k * 526373131 - 867) % P as i128,
            )
        } else {
            ((k * 173 + k / 17) % 256, (k * 311 + k / 53) % 65536 - 32768)
        };
        let i = z.len();
        z.extend([a, b, a * b].map(|x| Fp::from_i128(x).0));
        rows.push(Row {
            prods: vec![(vec![(Fp::ONE, i)], vec![(Fp::ONE, i + 1)])],
            c: vec![(Fp(P - 1), i + 2)],
        });
    }
    (
        SvcsInstance {
            n_z: z.len(),
            rows,
            lookups: vec![],
        },
        z,
    )
}

#[test]
fn extremes_fallback_and_malformed_public_inputs() {
    let (mut i, z) = product_rows(6, true);
    i.rows.truncate(47);
    let (opt, stats) =
        SvcsProver::prove_with_stats(&i, &z, &[(z.len(), Lane::I16)], ProverMode::SmallValueGruen)
            .unwrap();
    assert_eq!(stats.tags_rejected, 1);
    assert!(!stats.round0_i64 && !stats.round1_i64);
    assert_eq!(
        opt,
        SvcsProver::prove(&i, &z, ProverMode::NaiveExt).unwrap()
    );
    SvcsVerifier::verify(&i, &z, &opt).unwrap();
    i.rows[0].prods[0].0[0].1 = z.len();
    assert!(SvcsProver::prove(&i, &z, ProverMode::SmallValueGruen).is_err());
    assert!(SvcsVerifier::verify(&i, &z, &opt).is_err());
}

#[test]
#[ignore = "release benchmark; run explicitly via build_and_verify.sh"]
fn release_benchmark() {
    assert!(!cfg!(debug_assertions));
    for log in 14..=18 {
        let (i, z) = product_rows(log, false);
        let mut times = [Vec::new(), Vec::new()];
        for trial in 0..3 {
            let mut proofs = Vec::new();
            for k in [trial % 2, 1 - trial % 2] {
                let mode = [ProverMode::NaiveExt, ProverMode::SmallValueGruen][k];
                let t = Instant::now();
                let p = SvcsProver::prove(&i, &z, mode).unwrap();
                times[k].push(t.elapsed().as_secs_f64() * 1000.0);
                proofs.push(p);
            }
            assert_eq!(proofs[0], proofs[1]);
            if trial == 0 {
                SvcsVerifier::verify(&i, &z, &proofs[0]).unwrap();
            }
        }
        for samples in &mut times {
            samples.sort_by(f64::total_cmp);
        }
        println!(
            "BENCH rows={} naive_ms={:.3} optimized_ms={:.3} speedup={:.3}x",
            i.rows.len(),
            times[0][1],
            times[1][1],
            times[0][1] / times[1][1]
        );
    }
}
