//! Work 9104 against the Lean reference prover: for every Lean-authored request in
//! `testdata/tower256_fri_vectors.json` (written by `lake exe tower256-prover-run --vectors`),
//! the native receipt bytes equal Lean's byte for byte.

use minidregg_prover::native_dispatch::tower256_additive_fri_prove_bytes;
use serde::Deserialize;

#[derive(Deserialize)]
struct Vector {
    name: String,
    request: String,
    response: String,
}

#[derive(Deserialize)]
struct Vectors {
    vectors: Vec<Vector>,
}

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("hex")).collect()
}

fn vectors() -> Vec<Vector> {
    let text = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/tower256_fri_vectors.json"))
        .expect("vectors file");
    let v: Vectors = serde_json::from_str(&text).expect("vectors json");
    assert!(v.vectors.len() >= 5, "expected the five Lean vectors");
    v.vectors
}

#[test]
fn tower256_fri_prove_matches_lean() {
    for v in vectors() {
        let got = tower256_additive_fri_prove_bytes(&unhex(&v.request)).unwrap_or_else(|e| panic!("{}: {e}", v.name));
        assert_eq!(got.len(), v.response.len() / 2, "{}: response length", v.name);
        assert!(got == unhex(&v.response), "{}: response bytes differ", v.name);
    }
}

#[test]
fn tower256_fri_prove_reads_its_request() {
    for v in vectors() {
        let req = unhex(&v.request);
        let honest = unhex(&v.response);
        // A trailing byte and a truncation are refused.
        let mut longer = req.clone();
        longer.push(0);
        assert!(tower256_additive_fri_prove_bytes(&longer).is_err(), "{}: trailing byte", v.name);
        assert!(tower256_additive_fri_prove_bytes(&req[..req.len() - 1]).is_err(), "{}: truncation", v.name);
        // The statement bytes are read: change one and the receipt changes. Not at m = 0 with
        // no queries, where the transcript draws nothing and the receipt is statement-free.
        if v.name.contains("_m0_q0") {
            continue;
        }
        let mut other = req.clone();
        let at = other.iter().position(|&b| b == 255).expect("length terminator") + 1;
        other[at] ^= 1;
        let changed = tower256_additive_fri_prove_bytes(&other).expect("still a request");
        assert!(changed != honest, "{}: statement bytes ignored", v.name);
    }
}
