//! Owner-only cryptographic conformance harness. Secret key remains resident in
//! this process; public executor and checker are independent child processes.
//! This harness cannot mint governance/release authority and exposes no generic
//! ciphertext decryption operation. Governed use must call the Mini join first.
mod governed;
use fhe::bfv::{Encoding, Plaintext, PublicKey, RelinearizationKey, SecretKey};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter, Serialize};
use minidregg_fhe_bend::{
    artifact_arity, artifact_profile, canonical, ciphertext, digest, ensure, hex, params, read,
    unhex, validate_artifact, Completion, Context, OwnerPublicMaterial, Request, Result,
    TRANSFORMER,
};
use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};
fn invoke(
    exe: &Path,
    command: &str,
    artifact: &Path,
    request: &Path,
    completion: &Path,
    pin: &str,
) -> Result<()> {
    ensure(
        Command::new(exe)
            .arg(command)
            .arg(artifact)
            .arg(request)
            .arg(completion)
            .arg(pin)
            .status()?
            .success(),
        "isolated public child refused",
    )
}
fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();
    ensure(args.len() == 5 || args.len() == 10, "usage: fhe-bend-owner COMPILER_ARTIFACT PIN FHE_BEND_BINARY NEW_PUBLIC_RUN_DIR [--governed SOURCE_ARTIFACT DRIVER DRIVER_SHA256 NATIVE_SESSION_CONFIG]")?;
    let mut release_driver = governed::Driver::parse(&args[5..])?;
    let artifact = Path::new(&args[1]);
    let pin = &args[2];
    let exe = Path::new(&args[3]);
    let dir = PathBuf::from(&args[4]);
    ensure(!dir.exists(), "run directory already exists")?;
    fs::create_dir_all(&dir)?;
    let raw = read(artifact)?;
    let plan = validate_artifact(&raw, pin)?;
    let p = params()?;
    let mut rng = rand::rng();
    let sk = SecretKey::random(&p, &mut rng);
    let pk = PublicKey::new(&sk, &mut rng);
    let arity = artifact_arity(&plan)?;
    let profile = artifact_profile(&plan)?;
    let is_natural = profile == minidregg_fhe_bend::natural::PROFILE;
    let is_mux = !is_natural && arity == 3;
    // Same public4096-slot capacity and same owner/audience. Three private
    // mux inputs enumerate all eight environments in the first eight slots.
    let mut slots = vec![vec![0u64; 4096]; arity];
    if is_natural {
        let caps = minidregg_fhe_bend::natural::caps(&plan)?;
        for (input, cap) in caps.iter().enumerate() {
            for slot in 0..4096 {
                slots[input][slot] = (slot as u64 + 17 * input as u64) % cap;
            }
        }
    } else if arity == 1 {
        slots[0][1] = 1;
    } else {
        for assignment in 0..8 {
            for input in 0..3 {
                slots[input][assignment] = ((assignment >> input) & 1) as u64;
            }
        }
    }
    let mut inputs = Vec::new();
    for values in &slots {
        let pt = Plaintext::try_encode(values, Encoding::simd(), &p)?;
        inputs.push(pk.try_encrypt(&pt, &mut rng)?);
    }
    let rk = if is_mux {
        Some(RelinearizationKey::new(&sk, &mut rng)?)
    } else {
        None
    };
    let rkbytes = rk.as_ref().map(|r| r.to_bytes()).unwrap_or_default();
    let key_epoch = digest(&[p.to_bytes(), pk.to_bytes(), rkbytes.clone()].concat());
    let mut request = Request {
        schema: "dregg.fhe-bend.request.v1".into(),
        compiler_artifact_sha256: pin.clone(),
        profile: profile.into(),
        parameters_sha256: digest(&p.to_bytes()),
        transformer_sha256: TRANSFORMER.ok_or("unqualified transformer build")?.into(),
        public_key: hex(&pk.to_bytes()),
        key_epoch,
        relinearization_key: rk.as_ref().map(|r| hex(&r.to_bytes())),
        inputs: inputs.iter().map(|c| hex(&c.to_bytes())).collect(),
        input_depths: vec![0; arity],
        input_admission: if is_natural {
            "honest-owner-fresh-bounded-natural-v1"
        } else { "owner-generated-canonical-bool-v1" }.into(),
        context: Context {
            semantic_id: format!("compiler-artifact:{pin}"),
            program_id: format!("compiler-artifact:{pin}"),
            method_id: "source-conformance-only".into(),
            invocation: digest(&inputs.iter().flat_map(|c| c.to_bytes()).collect::<Vec<_>>()),
            predecessor: "none-conformance".into(),
            authority_snapshot: "not-a-governed-invocation".into(),
            tariff_id: "no-platform-charge-conformance".into(),
            canonical_charge: vec![0; 10],
        },
    };
    let public_material = OwnerPublicMaterial {
        schema: "dregg.fhe-bend.owner-public-material.v1".into(),
        profile: request.profile.clone(),
        parameters_sha256: request.parameters_sha256.clone(),
        transformer_sha256: request.transformer_sha256.clone(),
        public_key: request.public_key.clone(),
        relinearization_key: request.relinearization_key.clone(),
        key_epoch: request.key_epoch.clone(),
    };
    let material_bytes = canonical(&public_material)?;
    fs::write(dir.join("owner-public-material.json"), &material_bytes)?;
    if let Some(driver) = &mut release_driver {
        driver.register(&material_bytes, &dir)?;
        request.context = driver.prepare(&raw, &dir, 0)?;
    }
    let request_path = dir.join("request.json");
    let completion_path = dir.join("completion.json");
    fs::write(&request_path, canonical(&request)?)?;
    invoke(
        exe,
        "evaluate",
        artifact,
        &request_path,
        &completion_path,
        pin,
    )?;
    invoke(exe, "check", artifact, &request_path, &completion_path, pin)?;
    let candidate_bytes = read(&completion_path)?;
    let candidate: Completion = serde_json::from_slice(&candidate_bytes)?;
    // Also check this exact retained in-memory snapshot: the offline harness
    // must not decode bytes swapped after the independent child check.
    minidregg_fhe_bend::check(&raw, pin, &request, &candidate)?;
    if let Some(driver) = &release_driver {
        driver.release(&raw, &canonical(&request)?, &candidate_bytes, &dir, 0)?;
    }
    let out = ciphertext(&unhex(&candidate.output)?, &p)?;
    let decoded = Vec::<u64>::try_decode(&sk.try_decrypt(&out)?, Encoding::simd())?;
    let mut expected = Vec::new();
    for i in 0..4096 {
        let value = if is_natural {
            minidregg_fhe_bend::natural::source_value(&plan,
                &slots.iter().map(|v| v[i]).collect::<Vec<_>>())?
        } else if arity == 1 {
            u64::from(if slots[0][i] == 0 {
                plan["onFalse"].as_bool().unwrap()
            } else {
                plan["onTrue"].as_bool().unwrap()
            })
        } else {
            if slots[0][i] == 1 {
                slots[1][i]
            } else {
                slots[2][i]
            }
        };
        ensure(decoded[i] == value, "owner-private source oracle mismatch")?;
        expected.push(value);
    }
    if is_mux {
        ensure(
            candidate.physical_cost.ct_ct_mul == 1
                && candidate.physical_cost.relinearizations == 1
                && candidate.physical_cost.depth == 1,
            "mux physical profile mismatch",
        )?;
        // Reuse this same checked program and key for an encrypted successor:
        // the false arm is the previous encrypted result, with a freshly
        // encrypted private selector. This remains physical conformance;
        // platform state/fee/release authority is not minted by this harness.
        let selector: Vec<u64> = slots[0].iter().map(|b| 1 - b).collect();
        let selector_pt = Plaintext::try_encode(&selector, Encoding::simd(), &p)?;
        let selector_ct = pk.try_encrypt(&selector_pt, &mut rng)?;
        let mut next = request.clone();
        next.inputs = vec![
            hex(&selector_ct.to_bytes()),
            request.inputs[1].clone(),
            candidate.output.clone(),
        ];
        next.input_depths[2] = candidate.physical_cost.depth;
        next.context.predecessor = candidate.output_sha256.clone();
        next.context.invocation = digest(&canonical(&next.inputs)?);
        if let Some(driver) = &release_driver {
            next.context = driver.prepare(&raw, &dir, 1)?;
        }
        let next_request = dir.join("next-request.json");
        let next_completion = dir.join("next-completion.json");
        fs::write(&next_request, canonical(&next)?)?;
        invoke(
            exe,
            "evaluate",
            artifact,
            &next_request,
            &next_completion,
            pin,
        )?;
        invoke(exe, "check", artifact, &next_request, &next_completion, pin)?;
        let next_candidate_bytes = read(&next_completion)?;
        let next_candidate: Completion = serde_json::from_slice(&next_candidate_bytes)?;
        minidregg_fhe_bend::check(&raw, pin, &next, &next_candidate)?;
        if let Some(driver) = &release_driver {
            driver.release(&raw, &canonical(&next)?, &next_candidate_bytes, &dir, 1)?;
        }
        let next_ct = ciphertext(&unhex(&next_candidate.output)?, &p)?;
        let actual = Vec::<u64>::try_decode(&sk.try_decrypt(&next_ct)?, Encoding::simd())?;
        for i in 0..4096 {
            ensure(
                actual[i]
                    == if selector[i] == 1 {
                        slots[1][i]
                    } else {
                        expected[i]
                    },
                "repeated encrypted successor mismatch",
            )?;
        }
        let retry = dir.join("retry-completion.json");
        invoke(exe, "evaluate", artifact, &next_request, &retry, pin)?;
        ensure(
            read(&retry)? == read(&next_completion)?,
            "deterministic encrypted retry mismatch",
        )?;
        ensure(
            next_candidate.physical_cost.depth == 2,
            "repeated ciphertext lifetime depth missing",
        )?;
        let mut third = next.clone();
        third.inputs[2] = next_candidate.output.clone();
        third.input_depths[2] = 2;
        third.context.predecessor = next_candidate.output_sha256.clone();
        third.context.invocation.push_str("-third-refusal");
        fs::write(dir.join("exhausted-depth-request.json"), canonical(&third)?)?;
        let refused = Command::new(exe)
            .arg("evaluate")
            .arg(artifact)
            .arg(dir.join("exhausted-depth-request.json"))
            .arg(dir.join("refused-depth-output.json"))
            .arg(pin)
            .output()?;
        ensure(
            !refused.status.success(),
            "unrefreshed third invocation exceeded lifetime profile",
        )?;
        println!("FHE-BEND-REPEATED-COMPUTATION: PASS; same checked plan/key; predecessor ciphertext consumed; lifetime depth2; third unrefreshed use refused; deterministic retry; platform custody/fees not claimed");
    }
    // Falsify exact transformed output and invocation binding without any
    // mutation of the common source or ciphertext library.
    let mut corrupt = candidate.clone();
    let one = Plaintext::try_encode(&vec![1u64; 4096], Encoding::simd(), &p)?;
    let changed = &out + &one;
    corrupt.output = hex(&changed.to_bytes());
    corrupt.output_sha256 = digest(&changed.to_bytes());
    fs::write(dir.join("wrong-completion.json"), canonical(&corrupt)?)?;
    let refused = Command::new(exe)
        .arg("check")
        .arg(artifact)
        .arg(&request_path)
        .arg(dir.join("wrong-completion.json"))
        .arg(pin)
        .output()?;
    ensure(!refused.status.success(), "changed candidate accepted")?;
    let mut wrong = request.clone();
    wrong.context.invocation.push_str("-other-generation");
    fs::write(dir.join("wrong-request.json"), canonical(&wrong)?)?;
    let refused = Command::new(exe)
        .arg("check")
        .arg(artifact)
        .arg(dir.join("wrong-request.json"))
        .arg(&completion_path)
        .arg(pin)
        .output()?;
    ensure(
        !refused.status.success(),
        "cross-invocation candidate accepted",
    )?;
    let mut wrong = request.clone();
    wrong.key_epoch = "00".repeat(32);
    fs::write(dir.join("wrong-key-request.json"), canonical(&wrong)?)?;
    let refused = Command::new(exe)
        .arg("evaluate")
        .arg(artifact)
        .arg(dir.join("wrong-key-request.json"))
        .arg(dir.join("refused-key-output.json"))
        .arg(pin)
        .output()?;
    ensure(
        !refused.status.success(),
        "changed key-epoch claim accepted",
    )?;
    let refused = Command::new(exe)
        .arg("evaluate")
        .arg(artifact)
        .arg(&request_path)
        .arg(dir.join("refused-program-output.json"))
        .arg("00".repeat(32))
        .output()?;
    ensure(
        !refused.status.success(),
        "unqualified compiler artifact accepted",
    )?;
    // A canonical protobuf pair in PowerBasis must not reach arithmetic that
    // assumes NTT. The library decoder alone does not enforce this invariant.
    let mut forbidden = out.clone();
    for polynomial in forbidden.iter_mut() {
        polynomial.change_representation(fhe_math::rq::Representation::PowerBasis);
    }
    let mut wrong = request.clone();
    wrong.inputs[0] = hex(&forbidden.to_bytes());
    fs::write(
        dir.join("wrong-representation-request.json"),
        canonical(&wrong)?,
    )?;
    let refused = Command::new(exe)
        .arg("evaluate")
        .arg(artifact)
        .arg(dir.join("wrong-representation-request.json"))
        .arg(dir.join("refused-representation-output.json"))
        .arg(pin)
        .output()?;
    ensure(
        !refused.status.success(),
        "canonical forbidden representation accepted",
    )?;
    println!("FHE-BEND-PHYSICAL-CONFORMANCE: PASS; real BFV; 4096 slots; isolated secretless evaluator/checker; owner-only decode; candidate/invocation/key-epoch/artifact/representation refusals; GOVERNED-RECEIVING-PENDING");
    Ok(())
}
