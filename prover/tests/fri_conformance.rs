//! `[PROVER-fri-fold]` conformance vectors against the Lean-computed FRI fold
//! reference (`prover/testdata/fri_conformance.json`, written by the `#eval` in
//! `Compiler/FriConformance.lean` — the Lean writer is the only author of that
//! file; the folded words there are THEOREM-equal to `Loom/Proximity.lean`'s
//! verified `fold` (`friFolded1_eq`/`friFolded2_eq`, kernel-decided numeric
//! leaves), and the extension products are kernel-decided instances of the
//! formula `ext4Mul_correct` proves to be multiplication in
//! `BabyBear[X]/(X^4 - 11)`).
//!
//! Cross-checks, NOT verification: there is no formal semantics of Rust, so
//! vector agreement is the whole claim. The fold vector is base-field valued
//! (Loom has no computable BabyBear^4 instance — see the honest scope limits in
//! `Compiler/FriConformance.lean`); it exercises the full Rust fold code path on
//! base-embedded lanes, and the cross-lane multiplication is pinned by the
//! `extProd*` vectors.

use std::path::Path;

use serde::Deserialize;

use minidregg_prover::field4::{bmul, two_adic_generator, Ext4, EXT_W, P};
use minidregg_prover::fri::fold;

/// Mirror of the conformance file the Lean `#eval` writes.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ConformanceFile {
    p: u64,
    log_n: u32,
    gen: u64,
    codeword: Vec<u64>,
    beta: u64,
    folded1: Vec<u64>,
    beta_sq: u64,
    folded2: Vec<u64>,
    ext_w: u64,
    ext_a: [u64; 4],
    ext_b: [u64; 4],
    ext_prod: [u64; 4],
    ext_a2: [u64; 4],
    ext_b2: [u64; 4],
    ext_prod2: [u64; 4],
}

fn conformance() -> ConformanceFile {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/fri_conformance.json");
    let s = std::fs::read_to_string(Path::new(path))
        .expect("read the Lean-written FRI conformance file");
    let c: ConformanceFile =
        serde_json::from_str(&s).expect("parse the Lean-written FRI conformance file");
    assert_eq!(c.p, P, "the vector is over the prover's field");
    assert_eq!(c.codeword.len(), 1 << c.log_n);
    assert_eq!(c.folded1.len(), 1 << (c.log_n - 1));
    assert_eq!(c.folded2.len(), 1 << (c.log_n - 2));
    assert_eq!(c.ext_w, EXT_W, "same extension constant X^4 = W");
    c
}

fn lift(vals: &[u64]) -> Vec<Ext4> {
    vals.iter().map(|&v| Ext4::from_base(v)).collect()
}

/// The Lean domain generator IS our canonical two-adic generator — the Lean
/// embedding (pinned to its power sequence in the kernel) and the Rust twiddle
/// generation (descended from 31^15) name the same domain.
#[test]
fn lean_domain_generator_is_the_canonical_one() {
    let c = conformance();
    assert_eq!(
        c.gen,
        two_adic_generator(c.log_n),
        "Lean friGen16 must equal the Rust two_adic_generator(logN)"
    );
    assert_eq!(bmul(c.beta, c.beta), c.beta_sq, "the Lean betaSq is beta^2");
}

/// **The fold conformance vector**: the Rust twiddle-form fold reproduces
/// Loom's verified `fold` — one round at beta, and the arity-4 chain at
/// (beta, beta^2) — on the Lean-authored word. The Lean side proved the
/// reference values equal `Loom.fold` (`friFolded1_eq`, `friFolded2_eq`);
/// Rust reproduces them, so OUR fold agrees with the VERIFIED fold on the
/// vector (agreement, not refinement).
#[test]
fn fold_matches_the_verified_lean_reference() {
    let c = conformance();
    let cw = lift(&c.codeword);
    let beta = Ext4::from_base(c.beta);

    assert_eq!(
        fold(&cw, beta, 1),
        lift(&c.folded1),
        "one fold round must reproduce Loom.fold at beta"
    );
    assert_eq!(
        fold(&cw, beta, 2),
        lift(&c.folded2),
        "the arity-4 fold must reproduce the Lean beta-squaring chain"
    );
    // and the chain factors through the intermediate word
    assert_eq!(
        fold(&lift(&c.folded1), Ext4::from_base(c.beta_sq), 1),
        lift(&c.folded2),
        "folding the Lean folded1 at betaSq gives the Lean folded2"
    );
}

/// **The extension-multiplication vectors**: `Ext4::mul` reproduces the Lean
/// `ext4Mul` known answers — the formula `ext4Mul_correct` proved to BE
/// multiplication in `BabyBear[X]/(X^4 - 11)`. The second pair has every lane
/// at the modulus edge (wraparound teeth). This is where the cross-lane terms
/// (which the base-embedded fold vector cannot reach) are pinned.
#[test]
fn ext4_mul_matches_the_lean_known_answers() {
    let c = conformance();
    assert_eq!(Ext4 { c: c.ext_a }.mul(Ext4 { c: c.ext_b }), Ext4 { c: c.ext_prod });
    assert_eq!(Ext4 { c: c.ext_a2 }.mul(Ext4 { c: c.ext_b2 }), Ext4 { c: c.ext_prod2 });
}

/// Tampering teeth: any single perturbed codeword element, or a perturbed
/// challenge, breaks agreement with the Lean reference.
#[test]
fn tampering_breaks_the_vector() {
    let c = conformance();
    let beta = Ext4::from_base(c.beta);
    let reference = lift(&c.folded1);

    for j in 0..c.codeword.len() {
        let mut bad = c.codeword.clone();
        bad[j] = (bad[j] + 1) % P;
        assert_ne!(fold(&lift(&bad), beta, 1), reference, "tampered codeword[{j}] must show");
    }
    let bad_beta = Ext4::from_base((c.beta + 1) % P);
    assert_ne!(fold(&lift(&c.codeword), bad_beta, 1), reference, "tampered beta must show");
}
