//! Single-looker LogUp* over the fixed `GF(2^256)` Fan--Paar tower.
//!
//! This is the first coherent runtime instantiation of `Loom.LogupStar`.  It
//! binds the table, canonical address-bit commitments, and the row-by-table
//! incidence MLE `Y(i,v) = [I(i)=v]` before deriving `r`.  It then evaluates
//! that fixed `Y` at the transcript point, giving
//! `Y_r(v) = sum_i eq_r(i)Y(i,v)`, and samples `c`.  Two fractional-addition
//! GKR reductions establish equality of
//! the looker and table logarithmic derivatives without inversion, and a
//! separate quadratic sumcheck proves `<T,Y> = e`.  All algebraic challenges
//! are atomic [`Tower256`] transcript draws.
//!
//! The sampled additive MLE openings authenticate the committed `T`, `Y`, and
//! every address bit at the reduction terminals.  Before the lookup challenge,
//! every index root also receives a cubic zerocheck for
//! `eq_r(x) * b(x) * (b(x)+1)` and a sampled opening against that SAME root;
//! Booleanity is therefore no longer delegated to an unnamed upstream AIR.
//! Address reconstruction is exactly
//! `I(z) = sum_u basis[u] * bit_u(z)`; `gamma` never replaces the per-row
//! equality weight.  `[LOGUP256-INDEX-ROOT-LINK]` is now the sole semantic
//! seam: the receipt/trace adapter must bind this exact ordered root vector as
//! its lookup-address bundle.
//!
//! The additive opening's proximity/ROM/commitment assumptions and
//! `[BTOWER256-RUST-UNVERIFIED]` is inherited rather than restated as a
//! cryptographic theorem by this executable protocol.

use core::fmt;

use crate::{
    additive_mle_tower256::{
        verify_tower256_mle_opening, Tower256MleCommitment, Tower256MleError, Tower256MleOpening,
        TOWER256_MLE_MAX_LOG_DOMAIN,
    },
    binary_hash::{BinaryHashDomain, BinaryRoot, BinaryShake256V1, HashSuite},
    binary_tower_256::{Tower256, Tower256Error},
    binary_transcript::{BinaryShake256Transcript, TranscriptSuite},
};

pub const LOGUP_TOWER256_PROTOCOL_LABEL: &[u8] = b"minidregg/logup-star-tower256/v2";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Logup256Statement {
    pub row_count: usize,
    pub table_count: usize,
    pub table_root: BinaryRoot,
    /// LSB-first canonical address-bit columns.
    pub index_roots: Vec<BinaryRoot>,
    /// Canonical digest of the ordered address-root vector and its shape.  A
    /// semantic receipt binds this one fixed-size value as its lookup clause.
    pub index_bundle_root: BinaryRoot,
    /// Commitment to the flattened incidence table, row bits first and table
    /// bits second.  This root is fixed before the transcript derives `r`.
    pub y_root: BinaryRoot,
    pub log_blowup: u32,
    pub num_queries: usize,
}

/// Four evaluations of one individual-degree-three sumcheck round at
/// `0, 1, theta, 1+theta`, where `theta` is coordinate bit one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CubicRound256 {
    pub evaluations: [Tower256; 4],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FractionLayer256 {
    pub rounds: Vec<CubicRound256>,
    /// `[p(x,0), p(x,1), q(x,0), q(x,1)]` after the layer sumcheck.
    pub terminal: [Tower256; 4],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FractionTreeProof256 {
    /// Root numerator and denominator.  Challenges are transcript-derived.
    pub root: [Tower256; 2],
    /// Top/root layer first, leaf layer last.
    pub layers: Vec<FractionLayer256>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuadraticRound256 {
    pub evaluations: [Tower256; 3],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProductSumcheck256 {
    pub rounds: Vec<QuadraticRound256>,
    /// `[T(z), Y(z)]`.
    pub terminal: [Tower256; 2],
}

/// One roots-before-challenge Booleanity proof for an index column.  The
/// terminal is the same committed bit polynomial opened at the derived
/// sumcheck point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexBooleanityProof256 {
    pub rounds: Vec<CubicRound256>,
    pub terminal: Tower256,
    pub opening: Tower256MleOpening,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Logup256Proof {
    /// Pullback evaluation at the transcript-derived point `r`.
    pub evaluation_value: Tower256,
    pub looker_fraction: FractionTreeProof256,
    pub table_fraction: FractionTreeProof256,
    /// Values of the committed address-bit MLEs at the looker GKR point.
    pub index_terminals: Vec<Tower256>,
    pub product: ProductSumcheck256,
    pub index_booleanity: Vec<IndexBooleanityProof256>,
    pub index_openings: Vec<Tower256MleOpening>,
    pub y_fraction_opening: Tower256MleOpening,
    pub table_product_opening: Tower256MleOpening,
    pub y_product_opening: Tower256MleOpening,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Logup256Error {
    InvalidShape,
    InvalidProofShape,
    AddressOutOfRange { row: usize, address: usize },
    ScatterIdentityMismatch,
    DenominatorPole,
    FractionReductionMismatch,
    ProductSumcheckMismatch,
    IndexBooleanityMismatch,
    IndexBundleMismatch,
    TerminalMismatch,
    Mle(Tower256MleError),
    Tower(Tower256Error),
}

impl From<Tower256MleError> for Logup256Error {
    fn from(value: Tower256MleError) -> Self {
        Self::Mle(value)
    }
}

impl From<Tower256Error> for Logup256Error {
    fn from(value: Tower256Error) -> Self {
        Self::Tower(value)
    }
}

impl fmt::Display for Logup256Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidShape => write!(f, "invalid Tower256 LogUp* witness shape"),
            Self::InvalidProofShape => write!(f, "invalid Tower256 LogUp* proof shape"),
            Self::AddressOutOfRange { row, address } => write!(
                f,
                "lookup row {row} has address {address} outside the shared table"
            ),
            Self::ScatterIdentityMismatch => {
                write!(f, "scattered table does not reproduce the batched claim")
            }
            Self::DenominatorPole => write!(f, "LogUp* challenge hits a table denominator pole"),
            Self::FractionReductionMismatch => {
                write!(f, "fractional-addition GKR reduction failed")
            }
            Self::ProductSumcheckMismatch => write!(f, "lookup product sumcheck failed"),
            Self::IndexBooleanityMismatch => {
                write!(f, "lookup index-column Booleanity proof failed")
            }
            Self::IndexBundleMismatch => {
                write!(
                    f,
                    "lookup index roots do not match the semantic bundle root"
                )
            }
            Self::TerminalMismatch => write!(f, "lookup terminal opening mismatch"),
            Self::Mle(error) => error.fmt(f),
            Self::Tower(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for Logup256Error {}

/// Clear algebra helper for `sum_i eq_r(i) * table[address[i]]`.
///
/// The proof API deliberately does not accept this `point`; its security point
/// is sampled internally only after every witness root is transcript-bound.
pub fn lookup_evaluation_value(
    table: &[Tower256],
    addresses: &[usize],
    point: &[Tower256],
) -> Result<Tower256, Logup256Error> {
    validate_witness_shape(table, addresses, 1, 1)?;
    if point.len() != addresses.len().trailing_zeros() as usize {
        return Err(Logup256Error::InvalidShape);
    }
    let weights = equality_table(point)?;
    let mut value = Tower256::ZERO;
    for (row, (&address, &weight)) in addresses.iter().zip(&weights).enumerate() {
        let table_value = table
            .get(address)
            .copied()
            .ok_or(Logup256Error::AddressOutOfRange { row, address })?;
        value = value.add(weight.mul(table_value));
    }
    Ok(value)
}

/// Prove one evaluation claim against one shared small table.
///
/// The single looker uses `gamma^0`; the sampled `gamma` is nevertheless bound
/// at the exact multi-looker extension point, so adding lookers later cannot
/// reinterpret `eq_r` as a batching challenge.
pub fn prove_logup256_single(
    table: &[Tower256],
    addresses: &[usize],
    log_blowup: u32,
    num_queries: usize,
) -> Result<(Logup256Statement, Logup256Proof), Logup256Error> {
    validate_witness_shape(table, addresses, log_blowup, num_queries)?;
    for (row, &address) in addresses.iter().enumerate() {
        if address >= table.len() {
            return Err(Logup256Error::AddressOutOfRange { row, address });
        }
    }
    let table_commitment = Tower256MleCommitment::new(table, log_blowup)?;
    let address_bits = canonical_address_columns(addresses, table.len())?;
    let index_commitments = address_bits
        .iter()
        .map(|column| Tower256MleCommitment::new(column, log_blowup))
        .collect::<Result<Vec<_>, _>>()?;
    let incidence = canonical_incidence_table(addresses, table.len())?;
    let y_commitment = Tower256MleCommitment::new(&incidence, log_blowup)?;
    let index_roots = index_commitments
        .iter()
        .map(|commitment| commitment.root())
        .collect::<Vec<_>>();
    let index_bundle_root =
        compute_index_bundle_root(addresses.len(), table.len(), log_blowup, &index_roots)?;
    let statement = Logup256Statement {
        row_count: addresses.len(),
        table_count: table.len(),
        table_root: table_commitment.root(),
        index_roots,
        index_bundle_root,
        y_root: y_commitment.root(),
        log_blowup,
        num_queries,
    };

    let mut transcript = BinaryShake256Transcript::new(LOGUP_TOWER256_PROTOCOL_LABEL);
    absorb_initial_statement(&statement, &mut transcript)?;
    let _gamma = transcript.sample_gf2_256(b"logup256/gamma");
    let mut index_booleanity = Vec::with_capacity(address_bits.len());
    for (bit, (column, commitment)) in address_bits.iter().zip(&index_commitments).enumerate() {
        let check_point = sample_index_booleanity_point(
            bit,
            statement.row_count.trailing_zeros() as usize,
            &mut transcript,
        );
        index_booleanity.push(prove_index_booleanity(
            bit,
            column,
            commitment,
            &check_point,
            num_queries,
            &mut transcript,
        )?);
    }
    let evaluation_point = sample_evaluation_point(
        statement.row_count.trailing_zeros() as usize,
        &mut transcript,
    );

    // A single looker has gamma^0 = 1.  Equality weights remain the per-row
    // unit; gamma is reserved solely for batching independent lookers.
    let x = equality_table(&evaluation_point)?;
    let y = scatter_weights(addresses, &x, table.len())?;
    let evaluation_value = dot_product(table, &y)?;
    observe_field(
        &mut transcript,
        b"logup256/evaluation-value",
        evaluation_value,
    );
    let c = transcript.sample_gf2_256(b"logup256/log-derivative-challenge");

    let looker_denominators = addresses
        .iter()
        .map(|&address| c.add(embed_table_index(address)))
        .collect::<Vec<_>>();
    let table_denominators = (0..table.len())
        .map(|address| c.add(embed_table_index(address)))
        .collect::<Vec<_>>();
    let looker_tree = FractionTree::new(&x, &looker_denominators)?;
    let table_tree = FractionTree::new(&y, &table_denominators)?;
    if looker_tree.root()[1].is_zero() || table_tree.root()[1].is_zero() {
        return Err(Logup256Error::DenominatorPole);
    }

    absorb_fraction_roots(looker_tree.root(), table_tree.root(), &mut transcript);
    if !looker_tree.root()[0]
        .mul(table_tree.root()[1])
        .add(table_tree.root()[0].mul(looker_tree.root()[1]))
        .is_zero()
    {
        return Err(Logup256Error::FractionReductionMismatch);
    }

    let (looker_fraction, looker_terminal) =
        prove_fraction_tree(&looker_tree, b"looker", &mut transcript)?;
    let index_terminals = address_bits
        .iter()
        .map(|column| evaluate_mle(column, &looker_terminal.point))
        .collect::<Result<Vec<_>, _>>()?;
    absorb_index_terminals(&index_terminals, &mut transcript);
    let reconstructed_index = recompose_index(&index_terminals)?;
    if looker_terminal.p != equality_eval(&evaluation_point, &looker_terminal.point)?
        || looker_terminal.q != c.add(reconstructed_index)
    {
        return Err(Logup256Error::TerminalMismatch);
    }

    let (table_fraction, table_terminal) =
        prove_fraction_tree(&table_tree, b"table", &mut transcript)?;
    if table_terminal.q != c.add(recompose_index(&table_terminal.point)?) {
        return Err(Logup256Error::TerminalMismatch);
    }

    let (product, product_point) =
        prove_product_sumcheck(table, &y, evaluation_value, &mut transcript)?;

    // PCS retirement happens only after all algebraic reduction messages and
    // challenges are fixed.  Both Y openings use the same pre-r incidence root.
    let index_openings = index_commitments
        .iter()
        .enumerate()
        .map(|(bit, commitment)| {
            commitment.prove_opening(
                &looker_terminal.point,
                num_queries,
                &index_opening_context(bit),
                &mut transcript,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let y_fraction_point = combined_y_point(&evaluation_point, &table_terminal.point);
    let y_fraction_opening = y_commitment.prove_opening(
        &y_fraction_point,
        num_queries,
        b"logup256/y-fraction-terminal",
        &mut transcript,
    )?;
    let table_product_opening = table_commitment.prove_opening(
        &product_point,
        num_queries,
        b"logup256/table-product-terminal",
        &mut transcript,
    )?;
    let y_product_point = combined_y_point(&evaluation_point, &product_point);
    let y_product_opening = y_commitment.prove_opening(
        &y_product_point,
        num_queries,
        b"logup256/y-product-terminal",
        &mut transcript,
    )?;

    Ok((
        statement,
        Logup256Proof {
            evaluation_value,
            looker_fraction,
            table_fraction,
            index_terminals,
            product,
            index_booleanity,
            index_openings,
            y_fraction_opening,
            table_product_opening,
            y_product_opening,
        },
    ))
}

pub fn verify_logup256_single(
    statement: &Logup256Statement,
    proof: &Logup256Proof,
) -> Result<bool, Logup256Error> {
    validate_statement(statement)?;
    let log_rows = statement.row_count.trailing_zeros() as usize;
    let log_table = statement.table_count.trailing_zeros() as usize;
    if proof.index_terminals.len() != log_table
        || proof.index_booleanity.len() != log_table
        || proof.index_openings.len() != log_table
        || proof.looker_fraction.layers.len() != log_rows
        || proof.table_fraction.layers.len() != log_table
        || proof.product.rounds.len() != log_table
    {
        return Ok(false);
    }

    let mut transcript = BinaryShake256Transcript::new(LOGUP_TOWER256_PROTOCOL_LABEL);
    absorb_initial_statement(statement, &mut transcript)?;
    let _gamma = transcript.sample_gf2_256(b"logup256/gamma");
    for (bit, booleanity) in proof.index_booleanity.iter().enumerate() {
        let check_point = sample_index_booleanity_point(bit, log_rows, &mut transcript);
        if !verify_index_booleanity(
            bit,
            &statement.index_roots[bit],
            statement.row_count,
            statement.log_blowup,
            &check_point,
            statement.num_queries,
            booleanity,
            &mut transcript,
        )? {
            return Ok(false);
        }
    }
    let evaluation_point = sample_evaluation_point(
        statement.row_count.trailing_zeros() as usize,
        &mut transcript,
    );
    observe_field(
        &mut transcript,
        b"logup256/evaluation-value",
        proof.evaluation_value,
    );
    let c = transcript.sample_gf2_256(b"logup256/log-derivative-challenge");

    let looker_root = proof.looker_fraction.root;
    let table_root = proof.table_fraction.root;
    if looker_root[1].is_zero() || table_root[1].is_zero() {
        return Ok(false);
    }
    absorb_fraction_roots(looker_root, table_root, &mut transcript);
    if !looker_root[0]
        .mul(table_root[1])
        .add(table_root[0].mul(looker_root[1]))
        .is_zero()
    {
        return Ok(false);
    }

    let Some(looker_terminal) = verify_fraction_tree(
        statement.row_count,
        &proof.looker_fraction,
        b"looker",
        &mut transcript,
    )?
    else {
        return Ok(false);
    };
    absorb_index_terminals(&proof.index_terminals, &mut transcript);
    if looker_terminal.p != equality_eval(&evaluation_point, &looker_terminal.point)?
        || looker_terminal.q != c.add(recompose_index(&proof.index_terminals)?)
    {
        return Ok(false);
    }

    let Some(table_terminal) = verify_fraction_tree(
        statement.table_count,
        &proof.table_fraction,
        b"table",
        &mut transcript,
    )?
    else {
        return Ok(false);
    };
    if table_terminal.q != c.add(recompose_index(&table_terminal.point)?) {
        return Ok(false);
    }

    let Some(product_point) = verify_product_sumcheck(
        statement.table_count,
        proof.evaluation_value,
        &proof.product,
        &mut transcript,
    )?
    else {
        return Ok(false);
    };

    for bit in 0..log_table {
        if !verify_tower256_mle_opening(
            &statement.index_roots[bit],
            statement.row_count,
            statement.log_blowup,
            &looker_terminal.point,
            proof.index_terminals[bit],
            statement.num_queries,
            &index_opening_context(bit),
            &proof.index_openings[bit],
            &mut transcript,
        )? {
            return Ok(false);
        }
    }
    let incidence_len = statement
        .row_count
        .checked_mul(statement.table_count)
        .ok_or(Logup256Error::InvalidShape)?;
    let y_fraction_point = combined_y_point(&evaluation_point, &table_terminal.point);
    let y_product_point = combined_y_point(&evaluation_point, &product_point);
    if !verify_tower256_mle_opening(
        &statement.y_root,
        incidence_len,
        statement.log_blowup,
        &y_fraction_point,
        table_terminal.p,
        statement.num_queries,
        b"logup256/y-fraction-terminal",
        &proof.y_fraction_opening,
        &mut transcript,
    )? || !verify_tower256_mle_opening(
        &statement.table_root,
        statement.table_count,
        statement.log_blowup,
        &product_point,
        proof.product.terminal[0],
        statement.num_queries,
        b"logup256/table-product-terminal",
        &proof.table_product_opening,
        &mut transcript,
    )? || !verify_tower256_mle_opening(
        &statement.y_root,
        incidence_len,
        statement.log_blowup,
        &y_product_point,
        proof.product.terminal[1],
        statement.num_queries,
        b"logup256/y-product-terminal",
        &proof.y_product_opening,
        &mut transcript,
    )? {
        return Ok(false);
    }
    Ok(true)
}

/// Verify the lookup only if its canonical ordered address-root bundle is the
/// one already named by the semantic trace/receipt.  This is the executable
/// `[LOGUP256-INDEX-ROOT-LINK]` boundary: callers compare one fixed-size root,
/// while Booleanity and lookup soundness stay inside this proof.
pub fn verify_logup256_single_bound(
    expected_index_bundle_root: &BinaryRoot,
    statement: &Logup256Statement,
    proof: &Logup256Proof,
) -> Result<bool, Logup256Error> {
    if &statement.index_bundle_root != expected_index_bundle_root {
        return Ok(false);
    }
    verify_logup256_single(statement, proof)
}

/// Recompute the exact bundle root exposed to a semantic receipt.
pub fn semantic_index_bundle_root(
    statement: &Logup256Statement,
) -> Result<BinaryRoot, Logup256Error> {
    compute_index_bundle_root(
        statement.row_count,
        statement.table_count,
        statement.log_blowup,
        &statement.index_roots,
    )
}

fn compute_index_bundle_root(
    row_count: usize,
    table_count: usize,
    log_blowup: u32,
    index_roots: &[BinaryRoot],
) -> Result<BinaryRoot, Logup256Error> {
    let row_count = u64::try_from(row_count).map_err(|_| Logup256Error::InvalidShape)?;
    let table_count = u64::try_from(table_count).map_err(|_| Logup256Error::InvalidShape)?;
    let root_count = u64::try_from(index_roots.len()).map_err(|_| Logup256Error::InvalidShape)?;
    let mut payload = b"MDRG-LOOKUP-INDEX-BUNDLE-V1".to_vec();
    payload.extend_from_slice(&row_count.to_le_bytes());
    payload.extend_from_slice(&table_count.to_le_bytes());
    payload.extend_from_slice(&log_blowup.to_le_bytes());
    payload.extend_from_slice(&root_count.to_le_bytes());
    for (bit, root) in index_roots.iter().enumerate() {
        payload.extend_from_slice(&(bit as u64).to_le_bytes());
        payload.extend_from_slice(root.as_bytes());
    }
    Ok(BinaryShake256V1.hash_leaf(BinaryHashDomain::Trace, 0, &payload))
}

fn validate_witness_shape(
    table: &[Tower256],
    addresses: &[usize],
    log_blowup: u32,
    num_queries: usize,
) -> Result<(), Logup256Error> {
    if table.len() < 2
        || !table.len().is_power_of_two()
        || addresses.len() < 2
        || !addresses.len().is_power_of_two()
        || log_blowup == 0
        || num_queries == 0
        || table.len().trailing_zeros() as usize + log_blowup as usize > TOWER256_MLE_MAX_LOG_DOMAIN
        || addresses.len().trailing_zeros() as usize + log_blowup as usize
            > TOWER256_MLE_MAX_LOG_DOMAIN
    {
        return Err(Logup256Error::InvalidShape);
    }
    Ok(())
}

fn validate_statement(statement: &Logup256Statement) -> Result<(), Logup256Error> {
    let combined_log = statement.row_count.trailing_zeros() as usize
        + statement.table_count.trailing_zeros() as usize
        + statement.log_blowup as usize;
    if statement.table_count < 2
        || !statement.table_count.is_power_of_two()
        || statement.row_count < 2
        || !statement.row_count.is_power_of_two()
        || statement.log_blowup == 0
        || statement.num_queries == 0
        || statement.table_count.trailing_zeros() as usize + statement.log_blowup as usize
            > TOWER256_MLE_MAX_LOG_DOMAIN
        || statement.row_count.trailing_zeros() as usize + statement.log_blowup as usize
            > TOWER256_MLE_MAX_LOG_DOMAIN
        || combined_log > TOWER256_MLE_MAX_LOG_DOMAIN
        || statement
            .row_count
            .checked_mul(statement.table_count)
            .is_none()
        || statement.index_roots.len() != statement.table_count.trailing_zeros() as usize
    {
        return Err(Logup256Error::InvalidShape);
    }
    if compute_index_bundle_root(
        statement.row_count,
        statement.table_count,
        statement.log_blowup,
        &statement.index_roots,
    )? != statement.index_bundle_root
    {
        return Err(Logup256Error::IndexBundleMismatch);
    }
    Ok(())
}

fn absorb_initial_statement(
    statement: &Logup256Statement,
    transcript: &mut BinaryShake256Transcript,
) -> Result<(), Logup256Error> {
    validate_statement(statement)?;
    transcript.observe_bytes(b"logup256/protocol", LOGUP_TOWER256_PROTOCOL_LABEL);
    transcript.observe_u64(b"logup256/row-count", statement.row_count as u64);
    transcript.observe_u64(b"logup256/table-count", statement.table_count as u64);
    transcript.observe_u64(b"logup256/log-blowup", statement.log_blowup as u64);
    transcript.observe_u64(b"logup256/num-queries", statement.num_queries as u64);
    transcript.observe_root(b"logup256/table-root", &statement.table_root);
    transcript.observe_root(b"logup256/index-bundle-root", &statement.index_bundle_root);
    for (bit, root) in statement.index_roots.iter().enumerate() {
        transcript.observe_u64(b"logup256/index-bit", bit as u64);
        transcript.observe_root(b"logup256/index-root", root);
    }
    transcript.observe_root(b"logup256/y-incidence-root", &statement.y_root);
    Ok(())
}

fn sample_evaluation_point(
    dimension: usize,
    transcript: &mut BinaryShake256Transcript,
) -> Vec<Tower256> {
    transcript.observe_u64(b"logup256/evaluation-dimension", dimension as u64);
    (0..dimension)
        .map(|coordinate| {
            transcript.observe_u64(b"logup256/evaluation-coordinate-index", coordinate as u64);
            transcript.sample_gf2_256(b"logup256/evaluation-coordinate")
        })
        .collect()
}

fn sample_index_booleanity_point(
    bit: usize,
    dimension: usize,
    transcript: &mut BinaryShake256Transcript,
) -> Vec<Tower256> {
    transcript.observe_u64(b"logup256/index-booleanity-bit", bit as u64);
    transcript.observe_u64(b"logup256/index-booleanity-dimension", dimension as u64);
    (0..dimension)
        .map(|coordinate| {
            transcript.observe_u64(
                b"logup256/index-booleanity-coordinate-index",
                coordinate as u64,
            );
            transcript.sample_gf2_256(b"logup256/index-booleanity-point")
        })
        .collect()
}

fn prove_index_booleanity(
    bit: usize,
    column: &[Tower256],
    commitment: &Tower256MleCommitment,
    check_point: &[Tower256],
    num_queries: usize,
    transcript: &mut BinaryShake256Transcript,
) -> Result<IndexBooleanityProof256, Logup256Error> {
    if column.len() < 2
        || !column.len().is_power_of_two()
        || check_point.len() != column.len().trailing_zeros() as usize
        || commitment.table_len() != column.len()
    {
        return Err(Logup256Error::InvalidShape);
    }
    let mut eq = equality_table(check_point)?;
    let mut values = column.to_vec();
    let initial = eq
        .iter()
        .zip(&values)
        .fold(Tower256::ZERO, |sum, (&weight, &value)| {
            sum.add(weight.mul(value).mul(value.add(Tower256::ONE)))
        });
    if !initial.is_zero() {
        return Err(Logup256Error::IndexBooleanityMismatch);
    }

    transcript.observe_bytes(
        b"logup256/index-booleanity-protocol",
        b"cubic-equality-weighted-zerocheck",
    );
    transcript.observe_u64(b"logup256/index-booleanity-proof-bit", bit as u64);
    transcript.observe_u64(b"logup256/index-booleanity-length", column.len() as u64);
    let mut running = Tower256::ZERO;
    let mut rounds = Vec::with_capacity(check_point.len());
    let mut opening_point = Vec::with_capacity(check_point.len());
    for round in 0..check_point.len() {
        let evaluations = index_booleanity_message(&eq, &values)?;
        absorb_index_booleanity_round(bit, round, &evaluations, transcript);
        if evaluations[0].add(evaluations[1]) != running {
            return Err(Logup256Error::IndexBooleanityMismatch);
        }
        let challenge = transcript.sample_gf2_256(b"logup256/index-booleanity-challenge");
        running = interpolate(&evaluations, challenge)?;
        eq = bind_affine_layer(&eq, challenge)?;
        values = bind_affine_layer(&values, challenge)?;
        opening_point.push(challenge);
        rounds.push(CubicRound256 { evaluations });
    }
    let terminal = *values.first().ok_or(Logup256Error::InvalidShape)?;
    observe_field(transcript, b"logup256/index-booleanity-terminal", terminal);
    if eq.len() != 1 || running != eq[0].mul(terminal).mul(terminal.add(Tower256::ONE)) {
        return Err(Logup256Error::IndexBooleanityMismatch);
    }
    let opening = commitment.prove_opening(
        &opening_point,
        num_queries,
        &index_booleanity_opening_context(bit),
        transcript,
    )?;
    Ok(IndexBooleanityProof256 {
        rounds,
        terminal,
        opening,
    })
}

#[allow(clippy::too_many_arguments)]
fn verify_index_booleanity(
    bit: usize,
    root: &BinaryRoot,
    row_count: usize,
    log_blowup: u32,
    check_point: &[Tower256],
    num_queries: usize,
    proof: &IndexBooleanityProof256,
    transcript: &mut BinaryShake256Transcript,
) -> Result<bool, Logup256Error> {
    let rounds_len = row_count.trailing_zeros() as usize;
    if proof.rounds.len() != rounds_len || check_point.len() != rounds_len {
        return Ok(false);
    }
    transcript.observe_bytes(
        b"logup256/index-booleanity-protocol",
        b"cubic-equality-weighted-zerocheck",
    );
    transcript.observe_u64(b"logup256/index-booleanity-proof-bit", bit as u64);
    transcript.observe_u64(b"logup256/index-booleanity-length", row_count as u64);
    let mut running = Tower256::ZERO;
    let mut opening_point = Vec::with_capacity(rounds_len);
    for (round, message) in proof.rounds.iter().enumerate() {
        absorb_index_booleanity_round(bit, round, &message.evaluations, transcript);
        if message.evaluations[0].add(message.evaluations[1]) != running {
            return Ok(false);
        }
        let challenge = transcript.sample_gf2_256(b"logup256/index-booleanity-challenge");
        running = interpolate(&message.evaluations, challenge)?;
        opening_point.push(challenge);
    }
    observe_field(
        transcript,
        b"logup256/index-booleanity-terminal",
        proof.terminal,
    );
    let eq_terminal = equality_eval(check_point, &opening_point)?;
    if running
        != eq_terminal
            .mul(proof.terminal)
            .mul(proof.terminal.add(Tower256::ONE))
    {
        return Ok(false);
    }
    Ok(verify_tower256_mle_opening(
        root,
        row_count,
        log_blowup,
        &opening_point,
        proof.terminal,
        num_queries,
        &index_booleanity_opening_context(bit),
        &proof.opening,
        transcript,
    )?)
}

fn index_booleanity_message(
    eq: &[Tower256],
    values: &[Tower256],
) -> Result<[Tower256; 4], Logup256Error> {
    if eq.len() < 2 || eq.len() != values.len() || !eq.len().is_power_of_two() {
        return Err(Logup256Error::InvalidShape);
    }
    let probes = cubic_probes();
    let mut message = [Tower256::ZERO; 4];
    for index in 0..(eq.len() / 2) {
        for (slot, &probe) in message.iter_mut().zip(&probes) {
            let eq_value = affine(eq[2 * index], eq[2 * index + 1], probe);
            let value = affine(values[2 * index], values[2 * index + 1], probe);
            *slot = slot.add(eq_value.mul(value).mul(value.add(Tower256::ONE)));
        }
    }
    Ok(message)
}

fn absorb_index_booleanity_round(
    bit: usize,
    round: usize,
    evaluations: &[Tower256; 4],
    transcript: &mut BinaryShake256Transcript,
) {
    transcript.observe_u64(b"logup256/index-booleanity-round-bit", bit as u64);
    transcript.observe_u64(b"logup256/index-booleanity-round", round as u64);
    for &value in evaluations {
        observe_field(transcript, b"logup256/index-booleanity-round-value", value);
    }
}

fn index_booleanity_opening_context(bit: usize) -> Vec<u8> {
    let mut context = b"logup256/index-booleanity/".to_vec();
    context.extend_from_slice(&(bit as u64).to_le_bytes());
    context
}

fn absorb_fraction_roots(
    looker: [Tower256; 2],
    table: [Tower256; 2],
    transcript: &mut BinaryShake256Transcript,
) {
    for (label, value) in [
        (b"logup256/fraction-root-p-looker".as_slice(), looker[0]),
        (b"logup256/fraction-root-q-looker".as_slice(), looker[1]),
        (b"logup256/fraction-root-p-table".as_slice(), table[0]),
        (b"logup256/fraction-root-q-table".as_slice(), table[1]),
    ] {
        observe_field(transcript, label, value);
    }
}

fn absorb_index_terminals(values: &[Tower256], transcript: &mut BinaryShake256Transcript) {
    transcript.observe_u64(b"logup256/index-terminal-count", values.len() as u64);
    for (bit, &value) in values.iter().enumerate() {
        transcript.observe_u64(b"logup256/index-terminal-bit", bit as u64);
        observe_field(transcript, b"logup256/index-terminal", value);
    }
}

fn observe_field(transcript: &mut BinaryShake256Transcript, label: &[u8], value: Tower256) {
    transcript.observe_bytes(label, &value.to_le_bytes());
}

fn index_opening_context(bit: usize) -> Vec<u8> {
    let mut context = b"logup256/index-terminal/".to_vec();
    context.extend_from_slice(&(bit as u64).to_le_bytes());
    context
}

fn canonical_address_columns(
    addresses: &[usize],
    table_count: usize,
) -> Result<Vec<Vec<Tower256>>, Logup256Error> {
    let bits = table_count.trailing_zeros() as usize;
    let mut columns = vec![vec![Tower256::ZERO; addresses.len()]; bits];
    for (row, &address) in addresses.iter().enumerate() {
        if address >= table_count {
            return Err(Logup256Error::AddressOutOfRange { row, address });
        }
        for (bit, column) in columns.iter_mut().enumerate() {
            if address & (1usize << bit) != 0 {
                column[row] = Tower256::ONE;
            }
        }
    }
    Ok(columns)
}

/// Flatten `Y(i,v) = [I(i)=v]` with row bits as the low coordinates.
/// Committing this incidence MLE before `r` removes the adaptive-`Y(r)` cycle.
fn canonical_incidence_table(
    addresses: &[usize],
    table_count: usize,
) -> Result<Vec<Tower256>, Logup256Error> {
    let len = addresses
        .len()
        .checked_mul(table_count)
        .ok_or(Logup256Error::InvalidShape)?;
    let mut incidence = vec![Tower256::ZERO; len];
    for (row, &address) in addresses.iter().enumerate() {
        if address >= table_count {
            return Err(Logup256Error::AddressOutOfRange { row, address });
        }
        incidence[address * addresses.len() + row] = Tower256::ONE;
    }
    Ok(incidence)
}

fn combined_y_point(row_point: &[Tower256], table_point: &[Tower256]) -> Vec<Tower256> {
    row_point.iter().chain(table_point).copied().collect()
}

fn embed_table_index(index: usize) -> Tower256 {
    Tower256::from_limbs([index as u64, 0, 0, 0])
}

fn recompose_index(coordinates: &[Tower256]) -> Result<Tower256, Logup256Error> {
    if coordinates.len() > 64 {
        return Err(Logup256Error::InvalidShape);
    }
    let mut value = Tower256::ZERO;
    for (bit, &coordinate) in coordinates.iter().enumerate() {
        let basis = Tower256::from_limbs([1u64 << bit, 0, 0, 0]);
        value = value.add(basis.mul(coordinate));
    }
    Ok(value)
}

fn scatter_weights(
    addresses: &[usize],
    weights: &[Tower256],
    table_count: usize,
) -> Result<Vec<Tower256>, Logup256Error> {
    if addresses.len() != weights.len() {
        return Err(Logup256Error::InvalidShape);
    }
    let mut output = vec![Tower256::ZERO; table_count];
    for (row, (&address, &weight)) in addresses.iter().zip(weights).enumerate() {
        let slot = output
            .get_mut(address)
            .ok_or(Logup256Error::AddressOutOfRange { row, address })?;
        *slot = slot.add(weight);
    }
    Ok(output)
}

fn dot_product(left: &[Tower256], right: &[Tower256]) -> Result<Tower256, Logup256Error> {
    if left.len() != right.len() {
        return Err(Logup256Error::InvalidShape);
    }
    Ok(left
        .iter()
        .zip(right)
        .fold(Tower256::ZERO, |sum, (&a, &b)| sum.add(a.mul(b))))
}

fn equality_table(point: &[Tower256]) -> Result<Vec<Tower256>, Logup256Error> {
    let len = 1usize
        .checked_shl(point.len() as u32)
        .ok_or(Logup256Error::InvalidShape)?;
    (0..len)
        .map(|index| {
            let mut value = Tower256::ONE;
            for (bit, &coordinate) in point.iter().enumerate() {
                value = value.mul(if index & (1usize << bit) == 0 {
                    Tower256::ONE.add(coordinate)
                } else {
                    coordinate
                });
            }
            Ok(value)
        })
        .collect()
}

/// `eq(r,z) = product_i (1 + r_i + z_i)` in characteristic two.
fn equality_eval(left: &[Tower256], right: &[Tower256]) -> Result<Tower256, Logup256Error> {
    if left.len() != right.len() {
        return Err(Logup256Error::InvalidShape);
    }
    Ok(left
        .iter()
        .zip(right)
        .fold(Tower256::ONE, |product, (&a, &b)| {
            product.mul(Tower256::ONE.add(a).add(b))
        }))
}

fn evaluate_mle(table: &[Tower256], point: &[Tower256]) -> Result<Tower256, Logup256Error> {
    if table.len() < 2
        || !table.len().is_power_of_two()
        || point.len() != table.len().trailing_zeros() as usize
    {
        return Err(Logup256Error::InvalidShape);
    }
    let mut layer = table.to_vec();
    for &challenge in point {
        layer = bind_affine_layer(&layer, challenge)?;
    }
    layer.first().copied().ok_or(Logup256Error::InvalidShape)
}

fn affine(left: Tower256, right: Tower256, point: Tower256) -> Tower256 {
    left.add(left.add(right).mul(point))
}

fn bind_affine_layer(layer: &[Tower256], point: Tower256) -> Result<Vec<Tower256>, Logup256Error> {
    if layer.len() < 2 || !layer.len().is_power_of_two() {
        return Err(Logup256Error::InvalidShape);
    }
    Ok(layer
        .chunks_exact(2)
        .map(|pair| affine(pair[0], pair[1], point))
        .collect())
}

#[derive(Clone)]
struct FractionTree {
    p: Vec<Vec<Tower256>>,
    q: Vec<Vec<Tower256>>,
}

impl FractionTree {
    fn new(numerators: &[Tower256], denominators: &[Tower256]) -> Result<Self, Logup256Error> {
        if numerators.len() < 2
            || !numerators.len().is_power_of_two()
            || numerators.len() != denominators.len()
        {
            return Err(Logup256Error::InvalidShape);
        }
        let mut p = vec![numerators.to_vec()];
        let mut q = vec![denominators.to_vec()];
        while p.last().expect("leaf layer exists").len() > 1 {
            let current_p = p.last().expect("current p layer exists");
            let current_q = q.last().expect("current q layer exists");
            let half = current_p.len() / 2;
            let mut next_p = Vec::with_capacity(half);
            let mut next_q = Vec::with_capacity(half);
            for index in 0..half {
                next_p.push(
                    current_p[index]
                        .mul(current_q[half + index])
                        .add(current_p[half + index].mul(current_q[index])),
                );
                next_q.push(current_q[index].mul(current_q[half + index]));
            }
            p.push(next_p);
            q.push(next_q);
        }
        Ok(Self { p, q })
    }

    fn root(&self) -> [Tower256; 2] {
        [
            self.p.last().expect("root layer exists")[0],
            self.q.last().expect("root layer exists")[0],
        ]
    }
}

#[derive(Clone, Debug)]
struct FractionTerminal {
    point: Vec<Tower256>,
    p: Tower256,
    q: Tower256,
}

fn prove_fraction_tree(
    tree: &FractionTree,
    role: &[u8],
    transcript: &mut BinaryShake256Transcript,
) -> Result<(FractionTreeProof256, FractionTerminal), Logup256Error> {
    transcript.observe_bytes(b"logup256/fraction-role", role);
    let root = tree.root();
    let layer_count = tree.p.len() - 1;
    transcript.observe_u64(b"logup256/fraction-layer-count", layer_count as u64);
    let mut point = Vec::with_capacity(layer_count);
    let mut p_claim = root[0];
    let mut q_claim = root[1];
    let mut proof_layers = Vec::with_capacity(layer_count);

    for depth in 0..layer_count {
        absorb_fraction_layer_claim(depth, p_claim, q_claim, transcript);
        let beta = transcript.sample_gf2_256(b"logup256/fraction-batch");
        let child_level = layer_count - 1 - depth;
        let child_p = &tree.p[child_level];
        let child_q = &tree.q[child_level];
        let half = child_p.len() / 2;
        let mut state = FractionSumcheckState::new(
            &point,
            &child_p[..half],
            &child_p[half..],
            &child_q[..half],
            &child_q[half..],
        )?;
        let mut running = p_claim.add(beta.mul(q_claim));
        let mut rounds = Vec::with_capacity(depth);
        for round in 0..depth {
            let evaluations = state.message(beta)?;
            absorb_cubic_round(depth, round, &evaluations, transcript);
            if evaluations[0].add(evaluations[1]) != running {
                return Err(Logup256Error::FractionReductionMismatch);
            }
            let challenge = transcript.sample_gf2_256(b"logup256/fraction-sumcheck-challenge");
            running = interpolate(&evaluations, challenge)?;
            state.bind(challenge)?;
            rounds.push(CubicRound256 { evaluations });
        }
        let terminal = state.terminal()?;
        absorb_fraction_terminal(depth, &terminal, transcript);
        let eq_terminal = equality_eval(&point, &state.challenges)?;
        let numerator = terminal[0]
            .mul(terminal[3])
            .add(terminal[1].mul(terminal[2]));
        let denominator = terminal[2].mul(terminal[3]);
        if running != eq_terminal.mul(numerator.add(beta.mul(denominator))) {
            return Err(Logup256Error::FractionReductionMismatch);
        }
        let lambda = transcript.sample_gf2_256(b"logup256/fraction-line-challenge");
        p_claim = affine(terminal[0], terminal[1], lambda);
        q_claim = affine(terminal[2], terminal[3], lambda);
        // `state.challenges` has exactly the old point dimension, but those
        // are the new random coordinates replacing it; retain only them and
        // the line coordinate for the child claim.
        point = state
            .challenges
            .iter()
            .copied()
            .chain(core::iter::once(lambda))
            .collect();
        proof_layers.push(FractionLayer256 { rounds, terminal });
    }
    Ok((
        FractionTreeProof256 {
            root,
            layers: proof_layers,
        },
        FractionTerminal {
            point,
            p: p_claim,
            q: q_claim,
        },
    ))
}

fn verify_fraction_tree(
    leaf_count: usize,
    proof: &FractionTreeProof256,
    role: &[u8],
    transcript: &mut BinaryShake256Transcript,
) -> Result<Option<FractionTerminal>, Logup256Error> {
    if leaf_count < 2 || !leaf_count.is_power_of_two() {
        return Err(Logup256Error::InvalidShape);
    }
    let layer_count = leaf_count.trailing_zeros() as usize;
    if proof.layers.len() != layer_count {
        return Ok(None);
    }
    transcript.observe_bytes(b"logup256/fraction-role", role);
    transcript.observe_u64(b"logup256/fraction-layer-count", layer_count as u64);
    let mut point = Vec::with_capacity(layer_count);
    let mut p_claim = proof.root[0];
    let mut q_claim = proof.root[1];
    for (depth, layer) in proof.layers.iter().enumerate() {
        if layer.rounds.len() != depth {
            return Ok(None);
        }
        absorb_fraction_layer_claim(depth, p_claim, q_claim, transcript);
        let beta = transcript.sample_gf2_256(b"logup256/fraction-batch");
        let mut running = p_claim.add(beta.mul(q_claim));
        let mut challenges = Vec::with_capacity(depth);
        for (round, message) in layer.rounds.iter().enumerate() {
            absorb_cubic_round(depth, round, &message.evaluations, transcript);
            if message.evaluations[0].add(message.evaluations[1]) != running {
                return Ok(None);
            }
            let challenge = transcript.sample_gf2_256(b"logup256/fraction-sumcheck-challenge");
            running = interpolate(&message.evaluations, challenge)?;
            challenges.push(challenge);
        }
        absorb_fraction_terminal(depth, &layer.terminal, transcript);
        let eq_terminal = equality_eval(&point, &challenges)?;
        let numerator = layer.terminal[0]
            .mul(layer.terminal[3])
            .add(layer.terminal[1].mul(layer.terminal[2]));
        let denominator = layer.terminal[2].mul(layer.terminal[3]);
        if running != eq_terminal.mul(numerator.add(beta.mul(denominator))) {
            return Ok(None);
        }
        let lambda = transcript.sample_gf2_256(b"logup256/fraction-line-challenge");
        p_claim = affine(layer.terminal[0], layer.terminal[1], lambda);
        q_claim = affine(layer.terminal[2], layer.terminal[3], lambda);
        point = challenges
            .into_iter()
            .chain(core::iter::once(lambda))
            .collect();
    }
    Ok(Some(FractionTerminal {
        point,
        p: p_claim,
        q: q_claim,
    }))
}

fn absorb_fraction_layer_claim(
    depth: usize,
    p: Tower256,
    q: Tower256,
    transcript: &mut BinaryShake256Transcript,
) {
    transcript.observe_u64(b"logup256/fraction-depth", depth as u64);
    observe_field(transcript, b"logup256/fraction-p-claim", p);
    observe_field(transcript, b"logup256/fraction-q-claim", q);
}

fn absorb_cubic_round(
    depth: usize,
    round: usize,
    evaluations: &[Tower256; 4],
    transcript: &mut BinaryShake256Transcript,
) {
    transcript.observe_u64(b"logup256/fraction-round-depth", depth as u64);
    transcript.observe_u64(b"logup256/fraction-round", round as u64);
    for &value in evaluations {
        observe_field(transcript, b"logup256/fraction-round-value", value);
    }
}

fn absorb_fraction_terminal(
    depth: usize,
    terminal: &[Tower256; 4],
    transcript: &mut BinaryShake256Transcript,
) {
    transcript.observe_u64(b"logup256/fraction-terminal-depth", depth as u64);
    for &value in terminal {
        observe_field(transcript, b"logup256/fraction-terminal-value", value);
    }
}

struct FractionSumcheckState {
    eq: Vec<Tower256>,
    p0: Vec<Tower256>,
    p1: Vec<Tower256>,
    q0: Vec<Tower256>,
    q1: Vec<Tower256>,
    challenges: Vec<Tower256>,
}

impl FractionSumcheckState {
    fn new(
        parent_point: &[Tower256],
        p0: &[Tower256],
        p1: &[Tower256],
        q0: &[Tower256],
        q1: &[Tower256],
    ) -> Result<Self, Logup256Error> {
        let len = p0.len();
        if len == 0
            || !len.is_power_of_two()
            || [p1.len(), q0.len(), q1.len()]
                .iter()
                .any(|&other| other != len)
            || parent_point.len() != len.trailing_zeros() as usize
        {
            return Err(Logup256Error::InvalidShape);
        }
        Ok(Self {
            eq: equality_table(parent_point)?,
            p0: p0.to_vec(),
            p1: p1.to_vec(),
            q0: q0.to_vec(),
            q1: q1.to_vec(),
            challenges: Vec::with_capacity(parent_point.len()),
        })
    }

    fn message(&self, beta: Tower256) -> Result<[Tower256; 4], Logup256Error> {
        if self.eq.len() < 2 {
            return Err(Logup256Error::InvalidShape);
        }
        let probes = cubic_probes();
        let mut message = [Tower256::ZERO; 4];
        for index in 0..(self.eq.len() / 2) {
            for (slot, &probe) in message.iter_mut().zip(&probes) {
                let eq = affine(self.eq[2 * index], self.eq[2 * index + 1], probe);
                let p0 = affine(self.p0[2 * index], self.p0[2 * index + 1], probe);
                let p1 = affine(self.p1[2 * index], self.p1[2 * index + 1], probe);
                let q0 = affine(self.q0[2 * index], self.q0[2 * index + 1], probe);
                let q1 = affine(self.q1[2 * index], self.q1[2 * index + 1], probe);
                let numerator = p0.mul(q1).add(p1.mul(q0));
                let denominator = q0.mul(q1);
                *slot = slot.add(eq.mul(numerator.add(beta.mul(denominator))));
            }
        }
        Ok(message)
    }

    fn bind(&mut self, challenge: Tower256) -> Result<(), Logup256Error> {
        self.eq = bind_affine_layer(&self.eq, challenge)?;
        self.p0 = bind_affine_layer(&self.p0, challenge)?;
        self.p1 = bind_affine_layer(&self.p1, challenge)?;
        self.q0 = bind_affine_layer(&self.q0, challenge)?;
        self.q1 = bind_affine_layer(&self.q1, challenge)?;
        self.challenges.push(challenge);
        Ok(())
    }

    fn terminal(&self) -> Result<[Tower256; 4], Logup256Error> {
        if [self.p0.len(), self.p1.len(), self.q0.len(), self.q1.len()]
            .iter()
            .any(|&len| len != 1)
        {
            return Err(Logup256Error::InvalidShape);
        }
        Ok([self.p0[0], self.p1[0], self.q0[0], self.q1[0]])
    }
}

fn prove_product_sumcheck(
    table: &[Tower256],
    y: &[Tower256],
    claimed: Tower256,
    transcript: &mut BinaryShake256Transcript,
) -> Result<(ProductSumcheck256, Vec<Tower256>), Logup256Error> {
    if dot_product(table, y)? != claimed {
        return Err(Logup256Error::ScatterIdentityMismatch);
    }
    transcript.observe_bytes(b"logup256/product-protocol", b"quadratic-dot-product");
    transcript.observe_u64(b"logup256/product-length", table.len() as u64);
    observe_field(transcript, b"logup256/product-claim", claimed);
    let mut left = table.to_vec();
    let mut right = y.to_vec();
    let rounds_len = table.len().trailing_zeros() as usize;
    let mut running = claimed;
    let mut rounds = Vec::with_capacity(rounds_len);
    let mut point = Vec::with_capacity(rounds_len);
    for round in 0..rounds_len {
        let evaluations = quadratic_message(&left, &right)?;
        absorb_quadratic_round(round, &evaluations, transcript);
        if evaluations[0].add(evaluations[1]) != running {
            return Err(Logup256Error::ProductSumcheckMismatch);
        }
        let challenge = transcript.sample_gf2_256(b"logup256/product-challenge");
        running = interpolate(&evaluations, challenge)?;
        left = bind_affine_layer(&left, challenge)?;
        right = bind_affine_layer(&right, challenge)?;
        point.push(challenge);
        rounds.push(QuadraticRound256 { evaluations });
    }
    let terminal = [left[0], right[0]];
    for &value in &terminal {
        observe_field(transcript, b"logup256/product-terminal", value);
    }
    if running != terminal[0].mul(terminal[1]) {
        return Err(Logup256Error::ProductSumcheckMismatch);
    }
    Ok((ProductSumcheck256 { rounds, terminal }, point))
}

fn verify_product_sumcheck(
    table_count: usize,
    claimed: Tower256,
    proof: &ProductSumcheck256,
    transcript: &mut BinaryShake256Transcript,
) -> Result<Option<Vec<Tower256>>, Logup256Error> {
    let rounds_len = table_count.trailing_zeros() as usize;
    if proof.rounds.len() != rounds_len {
        return Ok(None);
    }
    transcript.observe_bytes(b"logup256/product-protocol", b"quadratic-dot-product");
    transcript.observe_u64(b"logup256/product-length", table_count as u64);
    observe_field(transcript, b"logup256/product-claim", claimed);
    let mut running = claimed;
    let mut point = Vec::with_capacity(rounds_len);
    for (round, message) in proof.rounds.iter().enumerate() {
        absorb_quadratic_round(round, &message.evaluations, transcript);
        if message.evaluations[0].add(message.evaluations[1]) != running {
            return Ok(None);
        }
        let challenge = transcript.sample_gf2_256(b"logup256/product-challenge");
        running = interpolate(&message.evaluations, challenge)?;
        point.push(challenge);
    }
    for &value in &proof.terminal {
        observe_field(transcript, b"logup256/product-terminal", value);
    }
    if running != proof.terminal[0].mul(proof.terminal[1]) {
        return Ok(None);
    }
    Ok(Some(point))
}

fn quadratic_message(
    left: &[Tower256],
    right: &[Tower256],
) -> Result<[Tower256; 3], Logup256Error> {
    if left.len() < 2 || left.len() != right.len() || !left.len().is_power_of_two() {
        return Err(Logup256Error::InvalidShape);
    }
    let probes = quadratic_probes();
    let mut message = [Tower256::ZERO; 3];
    for index in 0..(left.len() / 2) {
        for (slot, &probe) in message.iter_mut().zip(&probes) {
            *slot = slot.add(
                affine(left[2 * index], left[2 * index + 1], probe).mul(affine(
                    right[2 * index],
                    right[2 * index + 1],
                    probe,
                )),
            );
        }
    }
    Ok(message)
}

fn absorb_quadratic_round(
    round: usize,
    evaluations: &[Tower256; 3],
    transcript: &mut BinaryShake256Transcript,
) {
    transcript.observe_u64(b"logup256/product-round", round as u64);
    for &value in evaluations {
        observe_field(transcript, b"logup256/product-round-value", value);
    }
}

fn quadratic_probes() -> [Tower256; 3] {
    [
        Tower256::ZERO,
        Tower256::ONE,
        Tower256::from_limbs([2, 0, 0, 0]),
    ]
}

fn cubic_probes() -> [Tower256; 4] {
    [
        Tower256::ZERO,
        Tower256::ONE,
        Tower256::from_limbs([2, 0, 0, 0]),
        Tower256::from_limbs([3, 0, 0, 0]),
    ]
}

/// Evaluate the degree-`samples.len()-1` interpolant at `point`.
fn interpolate(samples: &[Tower256], point: Tower256) -> Result<Tower256, Logup256Error> {
    let probes = match samples.len() {
        3 => quadratic_probes().to_vec(),
        4 => cubic_probes().to_vec(),
        _ => return Err(Logup256Error::InvalidProofShape),
    };
    let mut value = Tower256::ZERO;
    for i in 0..samples.len() {
        let mut numerator = Tower256::ONE;
        let mut denominator = Tower256::ONE;
        for j in 0..samples.len() {
            if i != j {
                numerator = numerator.mul(point.add(probes[j]));
                denominator = denominator.mul(probes[i].add(probes[j]));
            }
        }
        value = value.add(samples[i].mul(numerator.div(denominator)?));
    }
    Ok(value)
}
