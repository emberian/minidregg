//! Experimental hiding configuration for the existing descriptor IR2 relation.
//! It preserves IR2's current FRI parameters; no 128-bit or PQ security claim.
//! Salt width is eight BabyBear elements (under 248 raw bits), not the old four.
//! PCS masking, openings and complete soundness accounting remain obligations.
use bend_proof_entropy::ProofRng;
use dregg_circuit::descriptor_ir2::{IR2_EXT_DEGREE, IR2_FRI_COMMIT_POW_BITS,
    IR2_FRI_LOG_BLOWUP, IR2_FRI_LOG_FINAL_POLY_LEN, IR2_FRI_MAX_LOG_ARITY,
    IR2_FRI_NUM_QUERIES, IR2_FRI_QUERY_POW_BITS};
use p3_baby_bear::{BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_challenger::{CanObserve, DuplexChallenger};
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::{Field, extension::BinomialExtensionField};
use p3_fri::{FriParameters, HidingFriPcs};
use p3_merkle_tree::MerkleTreeHidingMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::StarkConfig;
use tiny_keccak::{CShake, Hasher};

type Perm = Poseidon2BabyBear<16>;
type Extension = BinomialExtensionField<BabyBear, IR2_EXT_DEGREE>;
type Hash = PaddingFreeSponge<Perm, 16, 8, 8>;
type Compress = TruncatedPermutation<Perm, 2, 8, 16>;
type Mmcs = MerkleTreeHidingMmcs<<BabyBear as Field>::Packing,
    <BabyBear as Field>::Packing, Hash, Compress, ProofRng, 2, 8, 8>;
type ChallengeMmcs = ExtensionMmcs<BabyBear, Extension, Mmcs>;
type InnerChallenger = DuplexChallenger<BabyBear, Perm, 16, 8>;
type Challenger = crate::full_degree_challenger::FullDegreeChallenger<InnerChallenger>;
type Pcs = HidingFriPcs<BabyBear, Radix2DitParallel<BabyBear>, Mmcs, ChallengeMmcs, ProofRng>;
pub type Config = StarkConfig<Pcs, Extension, Challenger>;
pub const PROFILE: &str = "mini-bend-ir2-hiding-experimental-p3-82cfad73-salt8-full-degree-trace-budget-v4";

pub const ARTIFACT_PROFILE: &str = "mini-bend-ir2-hiding-experimental-p3-82cfad73-artifact-cshake-v5";

/// Public artifact binding, independent of private salted payload commitments.
/// Every digest byte is absorbed separately; there is no field-modulus folding.
pub fn artifact_digest(descriptor: &[u8]) -> [u8; 32] {
    let mut hash = CShake::v256(b"DREGG", b"BEND.IR2.DESCRIPTOR-BYTES/v1");
    let length = u64::try_from(descriptor.len()).expect("descriptor length exceeds u64");
    hash.update(&length.to_le_bytes());
    hash.update(descriptor);
    let mut digest = [0; 32];
    hash.finalize(&mut digest);
    digest
}

fn fresh_checked(capacity: crate::masking_budget::TraceCapacity, artifact: Option<&[u8]>) -> Result<Config, getrandom::Error> {
    let permutation = default_babybear_poseidon2_16();
    let make_mmcs = || -> Result<Mmcs, getrandom::Error> {
        Ok(Mmcs::new(PaddingFreeSponge::new(permutation.clone()),
            TruncatedPermutation::new(permutation.clone()), 0, ProofRng::from_os()?))
    };
    // Distinct initial seeds for value salts, challenge salts, and codeword
    // masking. Any subsequent P3 clone shares its stream without duplicating it.
    let value_mmcs = make_mmcs()?;
    let challenge_mmcs = ChallengeMmcs::new(make_mmcs()?);
    let parameters = FriParameters {
        log_blowup: IR2_FRI_LOG_BLOWUP,
        log_final_poly_len: IR2_FRI_LOG_FINAL_POLY_LEN,
        max_log_arity: IR2_FRI_MAX_LOG_ARITY,
        num_queries: IR2_FRI_NUM_QUERIES,
        commit_proof_of_work_bits: IR2_FRI_COMMIT_POW_BITS,
        query_proof_of_work_bits: IR2_FRI_QUERY_POW_BITS,
        mmcs: challenge_mmcs,
    };
    let pcs = Pcs::new(Radix2DitParallel::default(), value_mmcs, parameters,
        4, ProofRng::from_os()?);
    let mut transcript = InnerChallenger::new(permutation);
    // Bind this changed sampling protocol before any proof message. The old
    // profile never absorbed this frame, so it is not silently reinterpreted.
    let profile = if artifact.is_some() { ARTIFACT_PROFILE } else { PROFILE };
    transcript.observe(BabyBear::new(profile.len() as u32));
    for byte in profile.bytes() { transcript.observe(BabyBear::new(byte as u32)); }
    // Exact versioned parameters, including the authorized public capacity.
    for value in [IR2_EXT_DEGREE, IR2_FRI_LOG_BLOWUP, IR2_FRI_LOG_FINAL_POLY_LEN,
        IR2_FRI_MAX_LOG_ARITY, IR2_FRI_NUM_QUERIES, IR2_FRI_COMMIT_POW_BITS,
        IR2_FRI_QUERY_POW_BITS, 4, 8, crate::masking_budget::MAIN_EXTENSION_OPENINGS,
        crate::masking_budget::REQUIRED_TRACE_MASKS, capacity.rows()] {
        transcript.observe(BabyBear::new(value as u32));
    }
    if let Some(descriptor) = artifact {
        // Independently supplied verifier artifact, before any proof message.
        // The fixed profile/domain and eight explicit length bytes frame this.
        let length = u64::try_from(descriptor.len()).expect("descriptor length exceeds u64");
        for byte in length.to_le_bytes().into_iter().chain(artifact_digest(descriptor)) {
            transcript.observe(BabyBear::new(byte as u32));
        }
    }
    Ok(StarkConfig::new(pcs, Challenger::new(transcript)))
}

/// Enforces the derived trace-opening budget before constructing a deployment
/// candidate. Quotient/FRI decoupling remains a separate qualification.
pub fn for_capacity(capacity: crate::masking_budget::TraceCapacity) -> Result<Config, getrandom::Error> {
    fresh_checked(capacity, None)
}

/// V5 binds exact externally selected artifact bytes, not a proof-carried label.
/// This does not authenticate which source program produced the artifact.
pub fn for_artifact(capacity: crate::masking_budget::TraceCapacity,
    descriptor: &[u8]) -> Result<Config, getrandom::Error> {
    fresh_checked(capacity, Some(descriptor))
}

