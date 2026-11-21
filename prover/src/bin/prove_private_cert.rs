//! `prove_private_cert` — Native CLI for private-witness `Tower256` + `cSHAKE256` content certificates.
//!
//! Subcommands:
//! - `prove --input <FILE> --policy <no-sk|count-todo|count-markers> --claim <accept-true|accept-false|count:N|bound:LO:HI> --out-cert <CERT.bin> --out-receipt <RECEIPT.bin> [--fri-queries Q] [--step-queries S] [--seed-hex HEX]`
//! - `verify --cert <CERT.bin> --receipt <RECEIPT.bin>`
//! - `audit --input <FILE> --cert <CERT.bin> --receipt <RECEIPT.bin> [--min-slice N]`
//! - `bench [--fri-queries Q] [--step-queries S]`

use std::env;
use std::fs;
use std::process;
use std::time::Instant;

use minidregg_prover::binary_tower_256::Tower256;
use minidregg_prover::tower256_private_cert::{
    decode_private_cert, encode_private_cert, encode_private_receipt, fast_mul256, keccak_f_count,
    prove_private_document, reset_keccak_counter, scan_receipt_for_document_slices,
    synthesize_realistic_hermes_document, verify_private_cert_bytes, ClaimData, Digest, DfaTable,
};

fn parse_claim(spec: &str) -> Result<ClaimData, String> {
    if spec == "accept-true" {
        Ok(ClaimData::Accept(true))
    } else if spec == "accept-false" {
        Ok(ClaimData::Accept(false))
    } else if let Some(rest) = spec.strip_prefix("count:") {
        let n: u64 = rest.parse().map_err(|_| format!("invalid count: {spec}"))?;
        Ok(ClaimData::Count(n))
    } else if let Some(rest) = spec.strip_prefix("bound:") {
        let parts: Vec<&str> = rest.split(':').collect();
        if parts.len() != 2 {
            return Err(format!("expected bound:LO:HI, got {spec}"));
        }
        let lo: u64 = parts[0].parse().map_err(|_| format!("bad lo in {spec}"))?;
        let hi: u64 = parts[1].parse().map_err(|_| format!("bad hi in {spec}"))?;
        Ok(ClaimData::Bound { lo, hi })
    } else {
        Err(format!("unknown --claim {spec}"))
    }
}

fn parse_policy(spec: &str) -> Result<DfaTable, String> {
    match spec {
        "no-sk" => Ok(DfaTable::no_sk_dash()),
        "count-todo" => Ok(DfaTable::count_todo()),
        "count-markers" => Ok(DfaTable::count_todo_or_rule()),
        _ => Err(format!(
            "unknown --policy {spec} (expected no-sk | count-todo | count-markers)"
        )),
    }
}

fn parse_hex32(s: &str) -> Result<Digest, String> {
    if s.len() != 64 {
        return Err("seed-hex must be 64 hex chars (32 bytes)".to_string());
    }
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(&s[2 * i..2 * i + 2], 16)
            .map_err(|_| "invalid hex byte in seed-hex".to_string())?;
    }
    Ok(out)
}

fn hex_of(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn default_seed_for(doc: &[u8]) -> Digest {
    // Derive blinding seed from high-resolution clock + OS PID + document digest when no explicit seed is supplied.
    let mut buf = Vec::with_capacity(doc.len() + 24);
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    buf.extend_from_slice(&nanos.to_le_bytes());
    buf.extend_from_slice(&process::id().to_le_bytes());
    buf.extend_from_slice(doc);
    minidregg_prover::hash_kernels::cshake256_xof(b"MDPCRT/CLI/SEED", &buf, 32)
        .try_into()
        .expect("32B")
}

fn usage() -> ! {
    eprintln!(
        "Usage:\n  \
         prove_private_cert prove --input <FILE> --policy <no-sk|count-todo|count-markers> --claim <accept-true|accept-false|count:N|bound:LO:HI> --out-cert <CERT.bin> --out-receipt <RECEIPT.bin> [--fri-queries Q] [--step-queries S] [--seed-hex HEX]\n  \
         prove_private_cert verify --cert <CERT.bin> --receipt <RECEIPT.bin>\n  \
         prove_private_cert audit --input <FILE> --cert <CERT.bin> --receipt <RECEIPT.bin> [--min-slice N]\n  \
         prove_private_cert bench [--fri-queries Q] [--step-queries S]"
    );
    process::exit(2);
}

fn run_bench(fri_queries: usize, step_queries: usize) -> Result<(), String> {
    let _ = fast_mul256(Tower256::ONE, Tower256::ONE);
    let no_sk = DfaTable::no_sk_dash();
    let markers = DfaTable::count_todo_or_rule();
    let seed: Digest = [0x42u8; 32];

    println!("| Document Size | Policy + Claim | Prove (ms) | Verify (ms) | Prover Keccak-f | Verifier Keccak-f | Receipt Bytes | Leaked >=8B Slices |");
    println!("|---:|---|---:|---:|---:|---:|---:|---:|");

    for &size in &[1024usize, 4096, 16384] {
        let doc = synthesize_realistic_hermes_document(size, false);
        let marker_cnt = markers.run_count(&doc);

        for (label, dfa, claim) in [
            ("Absent(\"sk-\") [.accept true]", &no_sk, ClaimData::Accept(true)),
            (
                "Markers(TODO|RULE) [.bound 1..200]",
                &markers,
                ClaimData::Bound {
                    lo: 1,
                    hi: marker_cnt + 10,
                },
            ),
        ] {
            reset_keccak_counter();
            let t0 = Instant::now();
            let (stmt, receipt) =
                prove_private_document(dfa, &doc, claim, &seed, fri_queries, step_queries)
                    .map_err(|e| e.to_string())?;
            let receipt_bytes = encode_private_receipt(&receipt);
            let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
            let prove_keccak = keccak_f_count();

            reset_keccak_counter();
            let t1 = Instant::now();
            verify_private_cert_bytes(&stmt, &receipt_bytes).map_err(|e| e.to_string())?;
            let verify_ms = t1.elapsed().as_secs_f64() * 1000.0;
            let verify_keccak = keccak_f_count();

            let leaked = scan_receipt_for_document_slices(&doc, &receipt_bytes, 8);
            if leaked != 0 {
                return Err(format!("LEAKAGE DETECTED on size={size}: {leaked} slices"));
            }

            println!(
                "| {} B | {} | {:.2} | {:.2} | {} | {} | {} | {} |",
                size,
                label,
                prove_ms,
                verify_ms,
                prove_keccak,
                verify_keccak,
                receipt_bytes.len(),
                leaked
            );
        }
    }
    Ok(())
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.is_empty() {
        usage();
    }
    let sub = args[0].as_str();
    let mut input_path: Option<String> = None;
    let mut policy_str: Option<String> = None;
    let mut claim_str: Option<String> = None;
    let mut cert_path: Option<String> = None;
    let mut receipt_path: Option<String> = None;
    let mut seed_hex: Option<String> = None;
    let mut fri_queries: usize = 6;
    let mut step_queries: usize = 8;
    let mut min_slice: usize = 8;

    let mut i = 1;
    while i < args.len() {
        let flag = args[i].as_str();
        let val = args.get(i + 1).unwrap_or_else(|| usage());
        match flag {
            "--input" => input_path = Some(val.clone()),
            "--policy" => policy_str = Some(val.clone()),
            "--claim" => claim_str = Some(val.clone()),
            "--out-cert" | "--cert" => cert_path = Some(val.clone()),
            "--out-receipt" | "--receipt" => receipt_path = Some(val.clone()),
            "--seed-hex" => seed_hex = Some(val.clone()),
            "--fri-queries" => fri_queries = val.parse().unwrap_or_else(|_| usage()),
            "--step-queries" => step_queries = val.parse().unwrap_or_else(|_| usage()),
            "--min-slice" => min_slice = val.parse().unwrap_or_else(|_| usage()),
            _ => usage(),
        }
        i += 2;
    }

    let res: Result<(), String> = (|| match sub {
        "prove" => {
            let inp = input_path.ok_or("missing --input")?;
            let pol = parse_policy(&policy_str.ok_or("missing --policy")?)?;
            let clm = parse_claim(&claim_str.ok_or("missing --claim")?)?;
            let out_c = cert_path.ok_or("missing --out-cert")?;
            let out_r = receipt_path.ok_or("missing --out-receipt")?;
            let doc = fs::read(&inp).map_err(|e| format!("read {inp}: {e}"))?;
            let seed = match seed_hex {
                Some(h) => parse_hex32(&h)?,
                None => default_seed_for(&doc),
            };
            reset_keccak_counter();
            let t0 = Instant::now();
            let (stmt, receipt) =
                prove_private_document(&pol, &doc, clm, &seed, fri_queries, step_queries)
                    .map_err(|e| e.to_string())?;
            let cert_bytes = encode_private_cert(&stmt);
            let rec_bytes = encode_private_receipt(&receipt);
            let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
            let k_calls = keccak_f_count();
            fs::write(&out_c, &cert_bytes).map_err(|e| format!("write {out_c}: {e}"))?;
            fs::write(&out_r, &rec_bytes).map_err(|e| format!("write {out_r}: {e}"))?;
            println!(
                "PROVED record_bytes={} content_root={} automaton_root={} receipt_bytes={} prove_ms={:.2} keccak_f={}",
                stmt.record_length,
                hex_of(&stmt.content_root),
                hex_of(&stmt.automaton_root),
                rec_bytes.len(),
                elapsed_ms,
                k_calls
            );
            Ok(())
        }
        "verify" => {
            let cp = cert_path.ok_or("missing --cert")?;
            let rp = receipt_path.ok_or("missing --receipt")?;
            let cert_bytes = fs::read(&cp).map_err(|e| format!("read {cp}: {e}"))?;
            let rec_bytes = fs::read(&rp).map_err(|e| format!("read {rp}: {e}"))?;
            let stmt = decode_private_cert(&cert_bytes).map_err(|e| e.to_string())?;
            reset_keccak_counter();
            let t0 = Instant::now();
            verify_private_cert_bytes(&stmt, &rec_bytes).map_err(|e| e.to_string())?;
            let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
            println!(
                "VERIFIED record_bytes={} claim={:?} receipt_bytes={} verify_ms={:.2} keccak_f={}",
                stmt.record_length,
                stmt.claim,
                rec_bytes.len(),
                elapsed_ms,
                keccak_f_count()
            );
            Ok(())
        }
        "audit" => {
            let inp = input_path.ok_or("missing --input")?;
            let cp = cert_path.ok_or("missing --cert")?;
            let rp = receipt_path.ok_or("missing --receipt")?;
            let doc = fs::read(&inp).map_err(|e| format!("read {inp}: {e}"))?;
            let cert_bytes = fs::read(&cp).map_err(|e| format!("read {cp}: {e}"))?;
            let rec_bytes = fs::read(&rp).map_err(|e| format!("read {rp}: {e}"))?;
            let stmt = decode_private_cert(&cert_bytes).map_err(|e| e.to_string())?;
            verify_private_cert_bytes(&stmt, &rec_bytes).map_err(|e| e.to_string())?;
            let leaked = scan_receipt_for_document_slices(&doc, &rec_bytes, min_slice);
            if leaked != 0 {
                return Err(format!(
                    "AUDIT FAILED: {leaked} document slices of length >= {min_slice} found in receipt"
                ));
            }
            println!(
                "AUDIT_OK record_bytes={} receipt_bytes={} min_slice={} leaked_slices=0",
                doc.len(),
                rec_bytes.len(),
                min_slice
            );
            Ok(())
        }
        "bench" => run_bench(fri_queries, step_queries),
        _ => usage(),
    })();

    if let Err(err) = res {
        eprintln!("ERROR: {err}");
        process::exit(1);
    }
}
