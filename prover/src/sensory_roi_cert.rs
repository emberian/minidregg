//! Zero-pixel-leakage wearable CSI-2 camera/audio ROI redaction, algebraic `BabyBear`
//! blur/downscale & speech-envelope certificates, and anti-deepfake splice refusal
//! (*Rainbows End* Wearable SHE Organ #4: "Epiphany Lens").
//!
//! Mirrors `/Users/ember/dev/minidregg/Assurance/SensoryRoiZeroKnowledge.lean` bit-for-bit:
//! - Domain-separated SP 800-185 `cSHAKE256` per-tile dual commitments (`rawCommit` + `sumCommit`
//!   -> `tileLeaf`), padded binary Merkle tree, and hardware-enclave frame attestation header.
//! - Streaming `1280x720` (`80x45 = 3,600` `16x16` tiles, `60 fps` budget) multi-core tile-Merkle
//!   sealer (`< 4 ms` per `720p` frame) with pre-absorbed `CShake256Core` instances.
//! - Zero-bystander-leakage ROI reveal & algebraic `BabyBear` blur/ambient-dB verifier
//!   (`< 2 ms` verify) plus unconditional zero-sum `BabyBear` masking bijection (`TVD = 0`).

#![deny(warnings)]

use std::collections::HashSet;
use std::fmt;

use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    CShake256, CShake256Core,
};

use crate::babybear::{badd, bsub, P as BABYBEAR_P};

/// 32-byte SP 800-185 `cSHAKE256` digest.
pub type Digest = [u8; 32];

/// 256-bit (32-byte) per-tile hardware TRNG salt.
pub type Salt256 = [u8; 32];

/// Domain-separation customization strings (byte-identical to `SensoryRoiZeroKnowledge.lean`).
pub const CUST_RAW_TILE: &[u8] = b"MINIDREGG/SENSORY_ROI/RAW_TILE/V1";
pub const CUST_SUM_LEAF: &[u8] = b"MINIDREGG/SENSORY_ROI/SUM_LEAF/V1";
pub const CUST_TILE_LEAF: &[u8] = b"MINIDREGG/SENSORY_ROI/TILE_LEAF/V1";
pub const CUST_EMPTY_LEAF: &[u8] = b"MINIDREGG/SENSORY_ROI/EMPTY_LEAF/V1";
pub const CUST_MERKLE_NODE: &[u8] = b"MINIDREGG/SENSORY_ROI/MERKLE_NODE/V1";
pub const CUST_FRAME_SEAL: &[u8] = b"MINIDREGG/SENSORY_ROI/HW_FRAME_SEAL/V1";

/// Maximum samples per tile/window (matches Lean `WellFormed`: `≤ 65,536`).
pub const MAX_TILE_SAMPLES: usize = 65_536;

/// Error returned when a sensor frame, ROI reveal, or blur/envelope certificate is refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SensoryRoiError {
    InvalidGeometry(&'static str),
    EmptyTile(usize),
    OversizedTile { tile_idx: usize, len: usize },
    SaltReuseDetected { tile_idx: usize },
    HeaderAttestationMismatch,
    TileIndexOutOfBounds { tile_idx: usize, max_tiles: usize },
    DuplicateTileIndex(usize),
    MerklePathLengthMismatch { expected: usize, actual: usize },
    MerklePathMismatch { tile_idx: usize },
    InvalidBlurSum { tile_idx: usize, sum: u32, max_sum: u32 },
    InvalidBlurMean { tile_idx: usize, claimed: u32, expected: u32 },
    BabyBearWrapRisk { total_samples: u64 },
    EnvelopeSumMismatch { claimed: u64, computed: u64 },
    BabyBearSumcheckMismatch { claimed_mod_p: u64, masked_sum: u64 },
    MaskLengthMismatch { expected: usize, actual: usize },
    NonZeroSumMask { sum: u64 },
}

impl fmt::Display for SensoryRoiError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for SensoryRoiError {}

#[inline]
fn ct_eq_digest(a: &Digest, b: &Digest) -> bool {
    let mut diff = 0u8;
    for i in 0..32 {
        diff |= a[i] ^ b[i];
    }
    diff == 0
}

/// Pre-absorbed `CShake256Core` handles (avoids repeating the 136-byte SP 800-185 customization
/// prefix permutation on every tile and internal Merkle node).
#[derive(Clone)]
pub struct CachedCshakeCores {
    raw_tile: CShake256Core,
    sum_leaf: CShake256Core,
    tile_leaf: CShake256Core,
    merkle_node: CShake256Core,
    frame_seal: CShake256Core,
    empty_leaf: Digest,
}

impl CachedCshakeCores {
    pub fn new() -> Self {
        let empty_core = CShake256Core::new(CUST_EMPTY_LEAF);
        let h = CShake256::from_core(empty_core);
        let mut empty_leaf = [0u8; 32];
        h.finalize_xof().read(&mut empty_leaf);
        Self {
            raw_tile: CShake256Core::new(CUST_RAW_TILE),
            sum_leaf: CShake256Core::new(CUST_SUM_LEAF),
            tile_leaf: CShake256Core::new(CUST_TILE_LEAF),
            merkle_node: CShake256Core::new(CUST_MERKLE_NODE),
            frame_seal: CShake256Core::new(CUST_FRAME_SEAL),
            empty_leaf,
        }
    }

    #[inline]
    pub fn empty_leaf(&self) -> Digest {
        self.empty_leaf
    }

    #[inline]
    pub fn raw_tile_commit(
        &self,
        ctx_bytes: &[u8; 24],
        tile_idx: u32,
        raw_salt: &Salt256,
        pixels: &[u8],
    ) -> Digest {
        let mut h = CShake256::from_core(self.raw_tile.clone());
        h.update(ctx_bytes);
        h.update(&tile_idx.to_le_bytes());
        h.update(raw_salt);
        h.update(&(pixels.len() as u32).to_le_bytes());
        h.update(pixels);
        let mut out = [0u8; 32];
        h.finalize_xof().read(&mut out);
        out
    }

    #[inline]
    pub fn sum_tile_commit(
        &self,
        ctx_bytes: &[u8; 24],
        tile_idx: u32,
        sum_salt: &Salt256,
        tile_sum: u32,
        tile_len: u32,
    ) -> Digest {
        let mut h = CShake256::from_core(self.sum_leaf.clone());
        h.update(ctx_bytes);
        h.update(&tile_idx.to_le_bytes());
        h.update(sum_salt);
        h.update(&tile_sum.to_le_bytes());
        h.update(&tile_len.to_le_bytes());
        let mut out = [0u8; 32];
        h.finalize_xof().read(&mut out);
        out
    }

    #[inline]
    pub fn tile_leaf_commit(
        &self,
        ctx_bytes: &[u8; 24],
        tile_idx: u32,
        raw_commit: &Digest,
        sum_commit: &Digest,
    ) -> Digest {
        let mut h = CShake256::from_core(self.tile_leaf.clone());
        h.update(ctx_bytes);
        h.update(&tile_idx.to_le_bytes());
        h.update(raw_commit);
        h.update(sum_commit);
        let mut out = [0u8; 32];
        h.finalize_xof().read(&mut out);
        out
    }

    #[inline]
    pub fn merkle_parent(&self, lvl: u8, idx: u32, left: &Digest, right: &Digest) -> Digest {
        let mut h = CShake256::from_core(self.merkle_node.clone());
        h.update(&[lvl]);
        h.update(&idx.to_le_bytes());
        h.update(left);
        h.update(right);
        let mut out = [0u8; 32];
        h.finalize_xof().read(&mut out);
        out
    }

    #[inline]
    pub fn compute_header_tag(&self, hw_key: &[u8], header: &SensorFrameHeader) -> Digest {
        let mut h = CShake256::from_core(self.frame_seal.clone());
        h.update(hw_key);
        h.update(&header.ctx.encode());
        h.update(&header.grid_width.to_le_bytes());
        h.update(&header.grid_height.to_le_bytes());
        h.update(&header.merkle_depth.to_le_bytes());
        h.update(&[header.modality.tag()]);
        h.update(&header.merkle_root);
        let mut out = [0u8; 32];
        h.finalize_xof().read(&mut out);
        out
    }
}

impl Default for CachedCshakeCores {
    fn default() -> Self {
        Self::new()
    }
}

/// Sensor modality tag matching Lean `SensorModality`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SensorModality {
    Csi2Tile16x16,
    I2sAudioWindow,
}

impl SensorModality {
    #[inline]
    pub fn tag(self) -> u8 {
        match self {
            Self::Csi2Tile16x16 => 1,
            Self::I2sAudioWindow => 2,
        }
    }
}

/// Hardware-capture frame context bound into every tile leaf and header attestation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrameContext {
    pub sensor_id: u64,
    pub frame_seq: u64,
    pub timestamp_ns: u64,
}

impl FrameContext {
    #[inline]
    pub fn encode(&self) -> [u8; 24] {
        let mut out = [0u8; 24];
        out[0..8].copy_from_slice(&self.sensor_id.to_le_bytes());
        out[8..16].copy_from_slice(&self.frame_seq.to_le_bytes());
        out[16..24].copy_from_slice(&self.timestamp_ns.to_le_bytes());
        out
    }
}

/// Hardware-signed sensor frame header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SensorFrameHeader {
    pub ctx: FrameContext,
    pub grid_width: u32,
    pub grid_height: u32,
    pub merkle_depth: u32,
    pub modality: SensorModality,
    pub merkle_root: Digest,
    pub header_tag: Digest,
}

/// Raw hardware-captured sensor tile paired with two independent 256-bit TRNG salts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawSensorTile {
    pub pixels: Vec<u8>,
    pub raw_salt: Salt256,
    pub sum_salt: Salt256,
}

/// Compute exact integer byte sum (`0 ..= 255 * pixels.len()`).
#[inline]
pub fn sum_bytes(pixels: &[u8]) -> u32 {
    let mut acc = 0u32;
    for &b in pixels {
        acc += b as u32;
    }
    acc
}

/// Minimal Merkle depth `d` such that `2^d >= tile_count` (`d >= 0`).
pub fn merkle_depth_for(tile_count: usize) -> u32 {
    if tile_count <= 1 {
        return 0;
    }
    (usize::BITS - (tile_count - 1).leading_zeros()) as u32
}

/// Full hardware-sealed frame with cached Merkle tree layers for `O(log N)` proof extraction.
#[derive(Clone)]
pub struct SealedSensorFrame {
    pub header: SensorFrameHeader,
    pub tiles: Vec<RawSensorTile>,
    pub raw_commits: Vec<Digest>,
    pub sum_commits: Vec<Digest>,
    pub tile_sums: Vec<u32>,
    /// `layers[0]` has length `2^depth` (padded with `empty_leaf`), `layers[depth]` has length 1.
    pub merkle_layers: Vec<Vec<Digest>>,
}

/// Verify frame-wide 256-bit TRNG salt freshness (no duplicates across tiles or raw/sum subleaves).
pub fn verify_fresh_salts(tiles: &[RawSensorTile]) -> Result<(), SensoryRoiError> {
    let mut seen: HashSet<Salt256> = HashSet::with_capacity(tiles.len() * 2);
    for (idx, t) in tiles.iter().enumerate() {
        if !seen.insert(t.raw_salt) || !seen.insert(t.sum_salt) {
            return Err(SensoryRoiError::SaltReuseDetected { tile_idx: idx });
        }
    }
    Ok(())
}

/// Build the padded binary Merkle tree layers from `leaves` (parallelized across CPU cores for
/// large frames such as `1280x720` `80x45 = 3,600` tiles).
pub fn build_merkle_layers(
    cores: &CachedCshakeCores,
    depth: u32,
    leaves: &[Digest],
) -> Vec<Vec<Digest>> {
    let cap = 1usize << depth;
    let mut layer0 = vec![cores.empty_leaf(); cap];
    let copy_len = leaves.len().min(cap);
    layer0[..copy_len].copy_from_slice(&leaves[..copy_len]);

    let mut layers = Vec::with_capacity(depth as usize + 1);
    layers.push(layer0);

    let threads = std::thread::available_parallelism()
        .map(|n| n.get().min(8))
        .unwrap_or(1);

    for lvl in 0..(depth as usize) {
        let prev = &layers[lvl];
        let next_len = prev.len() / 2;
        let mut next = vec![[0u8; 32]; next_len];
        let lvl_u8 = (lvl & 0xFF) as u8;
        if next_len >= 256 && threads > 1 {
            let chunk = next_len.div_ceil(threads);
            std::thread::scope(|s| {
                for (t_idx, dst) in next.chunks_mut(chunk).enumerate() {
                    let start = t_idx * chunk;
                    let c = cores;
                    s.spawn(move || {
                        for (off, slot) in dst.iter_mut().enumerate() {
                            let idx = start + off;
                            *slot = c.merkle_parent(
                                lvl_u8,
                                idx as u32,
                                &prev[2 * idx],
                                &prev[2 * idx + 1],
                            );
                        }
                    });
                }
            });
        } else {
            for (idx, slot) in next.iter_mut().enumerate() {
                *slot = cores.merkle_parent(lvl_u8, idx as u32, &prev[2 * idx], &prev[2 * idx + 1]);
            }
        }
        layers.push(next);
    }
    layers
}

/// Seal a generic list of `RawSensorTile`s with salt-freshness checking and Merkle tree rooting.
pub fn seal_sensor_frame(
    cores: &CachedCshakeCores,
    hw_key: &[u8],
    ctx: FrameContext,
    grid_width: u32,
    grid_height: u32,
    merkle_depth: u32,
    modality: SensorModality,
    tiles: Vec<RawSensorTile>,
) -> Result<SealedSensorFrame, SensoryRoiError> {
    let expected = (grid_width as usize)
        .checked_mul(grid_height as usize)
        .ok_or(SensoryRoiError::InvalidGeometry("grid overflow"))?;
    if expected == 0 || tiles.len() != expected {
        return Err(SensoryRoiError::InvalidGeometry(
            "tile count != grid_width * grid_height",
        ));
    }
    if merkle_depth >= 31 || expected > (1usize << merkle_depth) {
        return Err(SensoryRoiError::InvalidGeometry(
            "tile count exceeds 2^merkle_depth",
        ));
    }
    for (idx, t) in tiles.iter().enumerate() {
        if t.pixels.is_empty() {
            return Err(SensoryRoiError::EmptyTile(idx));
        }
        if t.pixels.len() > MAX_TILE_SAMPLES {
            return Err(SensoryRoiError::OversizedTile {
                tile_idx: idx,
                len: t.pixels.len(),
            });
        }
    }
    verify_fresh_salts(&tiles)?;

    let ctx_bytes = ctx.encode();
    let n = tiles.len();
    let mut raw_commits = vec![[0u8; 32]; n];
    let mut sum_commits = vec![[0u8; 32]; n];
    let mut tile_sums = vec![0u32; n];
    let mut leaves = vec![[0u8; 32]; n];

    let threads = std::thread::available_parallelism()
        .map(|k| k.get().min(8))
        .unwrap_or(1);

    if n >= 128 && threads > 1 {
        let chunk = n.div_ceil(threads);
        std::thread::scope(|s| {
            let mut rc_rest = raw_commits.as_mut_slice();
            let mut sc_rest = sum_commits.as_mut_slice();
            let mut ts_rest = tile_sums.as_mut_slice();
            let mut lf_rest = leaves.as_mut_slice();
            let mut start = 0usize;
            while !rc_rest.is_empty() {
                let take = chunk.min(rc_rest.len());
                let (rc_c, rc_r) = rc_rest.split_at_mut(take);
                let (sc_c, sc_r) = sc_rest.split_at_mut(take);
                let (ts_c, ts_r) = ts_rest.split_at_mut(take);
                let (lf_c, lf_r) = lf_rest.split_at_mut(take);
                rc_rest = rc_r;
                sc_rest = sc_r;
                ts_rest = ts_r;
                lf_rest = lf_r;
                let tile_slice = &tiles[start..start + take];
                let base = start;
                let c = cores;
                s.spawn(move || {
                    for off in 0..take {
                        let idx = (base + off) as u32;
                        let t = &tile_slice[off];
                        let sm = sum_bytes(&t.pixels);
                        let rc = c.raw_tile_commit(&ctx_bytes, idx, &t.raw_salt, &t.pixels);
                        let sc = c.sum_tile_commit(
                            &ctx_bytes,
                            idx,
                            &t.sum_salt,
                            sm,
                            t.pixels.len() as u32,
                        );
                        let lf = c.tile_leaf_commit(&ctx_bytes, idx, &rc, &sc);
                        ts_c[off] = sm;
                        rc_c[off] = rc;
                        sc_c[off] = sc;
                        lf_c[off] = lf;
                    }
                });
                start += take;
            }
        });
    } else {
        for (i, t) in tiles.iter().enumerate() {
            let idx = i as u32;
            let sm = sum_bytes(&t.pixels);
            let rc = cores.raw_tile_commit(&ctx_bytes, idx, &t.raw_salt, &t.pixels);
            let sc =
                cores.sum_tile_commit(&ctx_bytes, idx, &t.sum_salt, sm, t.pixels.len() as u32);
            let lf = cores.tile_leaf_commit(&ctx_bytes, idx, &rc, &sc);
            tile_sums[i] = sm;
            raw_commits[i] = rc;
            sum_commits[i] = sc;
            leaves[i] = lf;
        }
    }

    let merkle_layers = build_merkle_layers(cores, merkle_depth, &leaves);
    let merkle_root = merkle_layers[merkle_depth as usize][0];
    let mut header = SensorFrameHeader {
        ctx,
        grid_width,
        grid_height,
        merkle_depth,
        modality,
        merkle_root,
        header_tag: [0u8; 32],
    };
    header.header_tag = cores.compute_header_tag(hw_key, &header);

    Ok(SealedSensorFrame {
        header,
        tiles,
        raw_commits,
        sum_commits,
        tile_sums,
        merkle_layers,
    })
}

/// High-throughput zero-copy streaming CSI-2 `16x16`-tile frame sealer directly from a raw
/// row-major luminance plane (`width % 16 == 0`, `height % 16 == 0`, e.g. `1280x720` -> `80x45 = 3,600` tiles).
///
/// Extracts each `16x16` tile on the stack (`[u8; 256]`) and hashes all tiles + Merkle layers
/// across CPU cores with zero per-tile heap allocations on the hot path.
pub fn seal_csi2_plane_streaming(
    cores: &CachedCshakeCores,
    hw_key: &[u8],
    ctx: FrameContext,
    width: usize,
    height: usize,
    y_plane: &[u8],
    raw_salts: &[Salt256],
    sum_salts: &[Salt256],
) -> Result<SealedPlaneHandle, SensoryRoiError> {
    if width == 0 || height == 0 || width % 16 != 0 || height % 16 != 0 {
        return Err(SensoryRoiError::InvalidGeometry(
            "CSI-2 plane dimensions must be positive multiples of 16",
        ));
    }
    if y_plane.len() != width * height {
        return Err(SensoryRoiError::InvalidGeometry(
            "y_plane.len() != width * height",
        ));
    }
    let grid_w = width / 16;
    let grid_h = height / 16;
    let n = grid_w * grid_h;
    if raw_salts.len() != n || sum_salts.len() != n {
        return Err(SensoryRoiError::InvalidGeometry(
            "salt slice length != tile count",
        ));
    }
    // Check salt uniqueness across the frame (fast HashSet of 32-byte TRNG salts).
    let mut seen: HashSet<Salt256> = HashSet::with_capacity(n * 2);
    for i in 0..n {
        if !seen.insert(raw_salts[i]) || !seen.insert(sum_salts[i]) {
            return Err(SensoryRoiError::SaltReuseDetected { tile_idx: i });
        }
    }

    let merkle_depth = merkle_depth_for(n);
    let ctx_bytes = ctx.encode();
    let mut raw_commits = vec![[0u8; 32]; n];
    let mut sum_commits = vec![[0u8; 32]; n];
    let mut tile_sums = vec![0u32; n];
    let mut leaves = vec![[0u8; 32]; n];

    let threads = std::thread::available_parallelism()
        .map(|k| k.get().min(8))
        .unwrap_or(1);
    let chunk = n.div_ceil(threads.max(1));

    std::thread::scope(|s| {
        let mut rc_rest = raw_commits.as_mut_slice();
        let mut sc_rest = sum_commits.as_mut_slice();
        let mut ts_rest = tile_sums.as_mut_slice();
        let mut lf_rest = leaves.as_mut_slice();
        let mut start = 0usize;
        while !rc_rest.is_empty() {
            let take = chunk.min(rc_rest.len());
            let (rc_c, rc_r) = rc_rest.split_at_mut(take);
            let (sc_c, sc_r) = sc_rest.split_at_mut(take);
            let (ts_c, ts_r) = ts_rest.split_at_mut(take);
            let (lf_c, lf_r) = lf_rest.split_at_mut(take);
            rc_rest = rc_r;
            sc_rest = sc_r;
            ts_rest = ts_r;
            lf_rest = lf_r;
            let base = start;
            let c = cores;
            s.spawn(move || {
                let mut tile_buf = [0u8; 256];
                for off in 0..take {
                    let idx = base + off;
                    let ty = idx / grid_w;
                    let tx = idx % grid_w;
                    let row_base = ty * 16 * width + tx * 16;
                    let mut sm = 0u32;
                    for r in 0..16 {
                        let src = &y_plane[row_base + r * width..row_base + r * width + 16];
                        tile_buf[r * 16..r * 16 + 16].copy_from_slice(src);
                        for &px in src {
                            sm += px as u32;
                        }
                    }
                    let idx_u32 = idx as u32;
                    let rc = c.raw_tile_commit(&ctx_bytes, idx_u32, &raw_salts[idx], &tile_buf);
                    let sc = c.sum_tile_commit(&ctx_bytes, idx_u32, &sum_salts[idx], sm, 256);
                    let lf = c.tile_leaf_commit(&ctx_bytes, idx_u32, &rc, &sc);
                    ts_c[off] = sm;
                    rc_c[off] = rc;
                    sc_c[off] = sc;
                    lf_c[off] = lf;
                }
            });
            start += take;
        }
    });

    let merkle_layers = build_merkle_layers(cores, merkle_depth, &leaves);
    let merkle_root = merkle_layers[merkle_depth as usize][0];
    let mut header = SensorFrameHeader {
        ctx,
        grid_width: grid_w as u32,
        grid_height: grid_h as u32,
        merkle_depth,
        modality: SensorModality::Csi2Tile16x16,
        merkle_root,
        header_tag: [0u8; 32],
    };
    header.header_tag = cores.compute_header_tag(hw_key, &header);

    Ok(SealedPlaneHandle {
        header,
        width,
        raw_commits,
        sum_commits,
        tile_sums,
        merkle_layers,
    })
}

/// Compact handle produced by `seal_csi2_plane_streaming` (holds commitments + Merkle layers
/// without copying the raw `720p` frame buffer).
#[derive(Clone)]
pub struct SealedPlaneHandle {
    pub header: SensorFrameHeader,
    pub width: usize,
    pub raw_commits: Vec<Digest>,
    pub sum_commits: Vec<Digest>,
    pub tile_sums: Vec<u32>,
    pub merkle_layers: Vec<Vec<Digest>>,
}

impl SealedPlaneHandle {
    pub fn open_merkle_path(&self, tile_idx: usize) -> Vec<Digest> {
        extract_merkle_path(&self.merkle_layers, tile_idx)
    }

    pub fn extract_tile_pixels(&self, y_plane: &[u8], tile_idx: usize) -> Vec<u8> {
        let grid_w = self.header.grid_width as usize;
        let ty = tile_idx / grid_w;
        let tx = tile_idx % grid_w;
        let row_base = ty * 16 * self.width + tx * 16;
        let mut out = Vec::with_capacity(256);
        for r in 0..16 {
            out.extend_from_slice(&y_plane[row_base + r * self.width..row_base + r * self.width + 16]);
        }
        out
    }

    pub fn open_roi_cert(
        &self,
        y_plane: &[u8],
        raw_salts: &[Salt256],
        sum_salts: &[Salt256],
        roi_indices: &[u32],
    ) -> RoiRevealCert {
        let openings = roi_indices
            .iter()
            .map(|&idx| {
                let i = idx as usize;
                RoiTileOpening {
                    tile_idx: idx,
                    pixels: self.extract_tile_pixels(y_plane, i),
                    raw_salt: raw_salts[i],
                    sum_salt: sum_salts[i],
                    merkle_path: self.open_merkle_path(i),
                }
            })
            .collect();
        RoiRevealCert { openings }
    }

    pub fn open_blur_cert(
        &self,
        sum_salts: &[Salt256],
        blur_indices: &[u32],
        zero_sum_mask: &[u64],
    ) -> Result<BlurEnvelopeCert, SensoryRoiError> {
        build_blur_cert_from_parts(
            &self.tile_sums,
            &self.raw_commits,
            &vec![256u32; self.tile_sums.len()],
            sum_salts,
            &self.merkle_layers,
            blur_indices,
            zero_sum_mask,
        )
    }
}

/// Extract a Merkle authentication path from cached layers.
pub fn extract_merkle_path(layers: &[Vec<Digest>], mut idx: usize) -> Vec<Digest> {
    let depth = layers.len().saturating_sub(1);
    let mut path = Vec::with_capacity(depth);
    for layer in &layers[..depth] {
        let sib = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
        path.push(layer[sib]);
        idx /= 2;
    }
    path
}

/// Verify a single Merkle path against `root` at `depth` and `tile_idx`.
pub fn verify_merkle_path(
    cores: &CachedCshakeCores,
    root: &Digest,
    depth: u32,
    tile_idx: u32,
    leaf: &Digest,
    siblings: &[Digest],
) -> Result<(), SensoryRoiError> {
    if siblings.len() != depth as usize {
        return Err(SensoryRoiError::MerklePathLengthMismatch {
            expected: depth as usize,
            actual: siblings.len(),
        });
    }
    if (tile_idx as u64) >= (1u64 << depth) {
        return Err(SensoryRoiError::TileIndexOutOfBounds {
            tile_idx: tile_idx as usize,
            max_tiles: 1usize << depth,
        });
    }
    let mut cur = *leaf;
    let mut pos = tile_idx;
    for (lvl, sib) in siblings.iter().enumerate() {
        let parent_idx = pos / 2;
        cur = if pos % 2 == 0 {
            cores.merkle_parent((lvl & 0xFF) as u8, parent_idx, &cur, sib)
        } else {
            cores.merkle_parent((lvl & 0xFF) as u8, parent_idx, sib, &cur)
        };
        pos = parent_idx;
    }
    if !ct_eq_digest(&cur, root) {
        return Err(SensoryRoiError::MerklePathMismatch {
            tile_idx: tile_idx as usize,
        });
    }
    Ok(())
}

/// Verify hardware-enclave frame header attestation.
pub fn verify_frame_header(
    cores: &CachedCshakeCores,
    hw_key: &[u8],
    header: &SensorFrameHeader,
) -> Result<(), SensoryRoiError> {
    let cap = 1u64
        .checked_shl(header.merkle_depth)
        .ok_or(SensoryRoiError::InvalidGeometry("merkle_depth overflow"))?;
    let total = (header.grid_width as u64) * (header.grid_height as u64);
    if total == 0 || total > cap {
        return Err(SensoryRoiError::InvalidGeometry(
            "grid exceeds 2^merkle_depth",
        ));
    }
    let expected = cores.compute_header_tag(hw_key, header);
    if !ct_eq_digest(&expected, &header.header_tag) {
        return Err(SensoryRoiError::HeaderAttestationMismatch);
    }
    Ok(())
}

// ============================================================================
// Zero-Bystander-Leakage ROI Reveal & Algebraic Blur / Ambient-dB Certificates
// ============================================================================

/// One item in a frustum-narrowed `RoiRevealView` (mirrors Lean `RoiTileItem`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RoiTileItem {
    Opened {
        pixels: Vec<u8>,
        raw_salt: Salt256,
        sum_salt: Salt256,
    },
    Sealed {
        leaf: Digest,
    },
}

/// Succinct `O(|U| log N)` ROI tile opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoiTileOpening {
    pub tile_idx: u32,
    pub pixels: Vec<u8>,
    pub raw_salt: Salt256,
    pub sum_salt: Salt256,
    pub merkle_path: Vec<Digest>,
}

/// Zero-bystander-leakage ROI reveal certificate opening ONLY `tile_idx ∈ U`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoiRevealCert {
    pub openings: Vec<RoiTileOpening>,
}

impl RoiRevealCert {
    /// Deterministic wire serialization (used for zero-bystander-leakage byte audits).
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&(self.openings.len() as u32).to_le_bytes());
        for o in &self.openings {
            out.extend_from_slice(&o.tile_idx.to_le_bytes());
            out.extend_from_slice(&(o.pixels.len() as u32).to_le_bytes());
            out.extend_from_slice(&o.pixels);
            out.extend_from_slice(&o.raw_salt);
            out.extend_from_slice(&o.sum_salt);
            out.extend_from_slice(&(o.merkle_path.len() as u32).to_le_bytes());
            for sib in &o.merkle_path {
                out.extend_from_slice(sib);
            }
        }
        out
    }
}

/// One blurred tile / speech-redacted audio window entry (ZERO raw pixels & ZERO `raw_salt`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlurTileEntry {
    pub tile_idx: u32,
    pub tile_sum: u32,
    pub tile_len: u32,
    pub mean_value: u32,
    pub sum_salt: Salt256,
    pub sealed_raw_commit: Digest,
    pub merkle_path: Vec<Digest>,
}

/// Algebraic `BabyBear` blur / downscale & ambient-dB envelope certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlurEnvelopeCert {
    pub entries: Vec<BlurTileEntry>,
    pub claimed_envelope_sum: u64,
    pub masked_terms: Vec<u64>,
}

impl BlurEnvelopeCert {
    /// Deterministic wire serialization (contains ZERO raw pixel bytes and ZERO `raw_salt`s).
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&self.claimed_envelope_sum.to_le_bytes());
        out.extend_from_slice(&(self.masked_terms.len() as u32).to_le_bytes());
        for &m in &self.masked_terms {
            out.extend_from_slice(&m.to_le_bytes());
        }
        out.extend_from_slice(&(self.entries.len() as u32).to_le_bytes());
        for e in &self.entries {
            out.extend_from_slice(&e.tile_idx.to_le_bytes());
            out.extend_from_slice(&e.tile_sum.to_le_bytes());
            out.extend_from_slice(&e.tile_len.to_le_bytes());
            out.extend_from_slice(&e.mean_value.to_le_bytes());
            out.extend_from_slice(&e.sum_salt);
            out.extend_from_slice(&e.sealed_raw_commit);
            out.extend_from_slice(&(e.merkle_path.len() as u32).to_le_bytes());
            for sib in &e.merkle_path {
                out.extend_from_slice(sib);
            }
        }
        out
    }
}

/// Verify an ROI reveal certificate (strictly refuses splices, replays, grafts, duplicates).
pub fn verify_roi_reveal_cert(
    cores: &CachedCshakeCores,
    hw_key: &[u8],
    header: &SensorFrameHeader,
    cert: &RoiRevealCert,
) -> Result<(), SensoryRoiError> {
    verify_frame_header(cores, hw_key, header)?;
    let max_tiles = (header.grid_width as usize) * (header.grid_height as usize);
    let ctx_bytes = header.ctx.encode();
    let mut seen = HashSet::with_capacity(cert.openings.len());
    for o in &cert.openings {
        let idx = o.tile_idx as usize;
        if idx >= max_tiles {
            return Err(SensoryRoiError::TileIndexOutOfBounds {
                tile_idx: idx,
                max_tiles,
            });
        }
        if !seen.insert(o.tile_idx) {
            return Err(SensoryRoiError::DuplicateTileIndex(idx));
        }
        if o.pixels.is_empty() {
            return Err(SensoryRoiError::EmptyTile(idx));
        }
        if o.pixels.len() > MAX_TILE_SAMPLES {
            return Err(SensoryRoiError::OversizedTile {
                tile_idx: idx,
                len: o.pixels.len(),
            });
        }
        let sm = sum_bytes(&o.pixels);
        let rc = cores.raw_tile_commit(&ctx_bytes, o.tile_idx, &o.raw_salt, &o.pixels);
        let sc = cores.sum_tile_commit(
            &ctx_bytes,
            o.tile_idx,
            &o.sum_salt,
            sm,
            o.pixels.len() as u32,
        );
        let lf = cores.tile_leaf_commit(&ctx_bytes, o.tile_idx, &rc, &sc);
        verify_merkle_path(
            cores,
            &header.merkle_root,
            header.merkle_depth,
            o.tile_idx,
            &lf,
            &o.merkle_path,
        )?;
    }
    Ok(())
}

/// Verify a zero-raw-pixel algebraic `BabyBear` blur / ambient-dB envelope certificate.
pub fn verify_blur_envelope_cert(
    cores: &CachedCshakeCores,
    hw_key: &[u8],
    header: &SensorFrameHeader,
    cert: &BlurEnvelopeCert,
) -> Result<(), SensoryRoiError> {
    verify_frame_header(cores, hw_key, header)?;
    let max_tiles = (header.grid_width as usize) * (header.grid_height as usize);
    let ctx_bytes = header.ctx.encode();
    if cert.masked_terms.len() != cert.entries.len() {
        return Err(SensoryRoiError::MaskLengthMismatch {
            expected: cert.entries.len(),
            actual: cert.masked_terms.len(),
        });
    }
    let mut seen = HashSet::with_capacity(cert.entries.len());
    let mut total_samples: u64 = 0;
    let mut total_sum: u64 = 0;

    for e in &cert.entries {
        let idx = e.tile_idx as usize;
        if idx >= max_tiles {
            return Err(SensoryRoiError::TileIndexOutOfBounds {
                tile_idx: idx,
                max_tiles,
            });
        }
        if !seen.insert(e.tile_idx) {
            return Err(SensoryRoiError::DuplicateTileIndex(idx));
        }
        if e.tile_len == 0 {
            return Err(SensoryRoiError::EmptyTile(idx));
        }
        if (e.tile_len as usize) > MAX_TILE_SAMPLES {
            return Err(SensoryRoiError::OversizedTile {
                tile_idx: idx,
                len: e.tile_len as usize,
            });
        }
        let max_sum = e.tile_len * 255;
        if e.tile_sum > max_sum {
            return Err(SensoryRoiError::InvalidBlurSum {
                tile_idx: idx,
                sum: e.tile_sum,
                max_sum,
            });
        }
        let expected_mean = e.tile_sum / e.tile_len;
        if e.mean_value != expected_mean {
            return Err(SensoryRoiError::InvalidBlurMean {
                tile_idx: idx,
                claimed: e.mean_value,
                expected: expected_mean,
            });
        }
        total_samples += e.tile_len as u64;
        total_sum += e.tile_sum as u64;

        let sc = cores.sum_tile_commit(&ctx_bytes, e.tile_idx, &e.sum_salt, e.tile_sum, e.tile_len);
        let lf = cores.tile_leaf_commit(&ctx_bytes, e.tile_idx, &e.sealed_raw_commit, &sc);
        verify_merkle_path(
            cores,
            &header.merkle_root,
            header.merkle_depth,
            e.tile_idx,
            &lf,
            &e.merkle_path,
        )?;
    }

    if total_samples.saturating_mul(255) >= BABYBEAR_P {
        return Err(SensoryRoiError::BabyBearWrapRisk { total_samples });
    }
    if cert.claimed_envelope_sum != total_sum {
        return Err(SensoryRoiError::EnvelopeSumMismatch {
            claimed: cert.claimed_envelope_sum,
            computed: total_sum,
        });
    }
    let mut masked_sum = 0u64;
    for &t in &cert.masked_terms {
        if t >= BABYBEAR_P {
            return Err(SensoryRoiError::BabyBearSumcheckMismatch {
                claimed_mod_p: cert.claimed_envelope_sum % BABYBEAR_P,
                masked_sum: t,
            });
        }
        masked_sum = badd(masked_sum, t);
    }
    let claimed_bb = cert.claimed_envelope_sum % BABYBEAR_P;
    if masked_sum != claimed_bb {
        return Err(SensoryRoiError::BabyBearSumcheckMismatch {
            claimed_mod_p: claimed_bb,
            masked_sum,
        });
    }
    Ok(())
}

// ============================================================================
// Zero-Sum `BabyBear` Masking Bijection (`TVD = 0` Sub-Tile / Formant Hiding)
// ============================================================================

/// Construct a deterministic zero-sum `BabyBear` blinding mask of length `n` from `n - 1`
/// arbitrary random scalars (`mask[n-1] = -sum(mask[0..n-1]) mod P`).
pub fn make_zero_sum_mask(n: usize, raw_scalars: &[u64]) -> Result<Vec<u64>, SensoryRoiError> {
    if n == 0 {
        return Ok(Vec::new());
    }
    if raw_scalars.len() + 1 < n {
        return Err(SensoryRoiError::MaskLengthMismatch {
            expected: n - 1,
            actual: raw_scalars.len(),
        });
    }
    let mut out = Vec::with_capacity(n);
    let mut acc = 0u64;
    for &r in &raw_scalars[..n - 1] {
        let v = r % BABYBEAR_P;
        out.push(v);
        acc = badd(acc, v);
    }
    out.push(bsub(0, acc));
    Ok(out)
}

/// Apply a zero-sum `BabyBear` blinding mask to sample bytes `pixels`.
pub fn apply_zero_sum_mask(pixels: &[u8], mask: &[u64]) -> Result<Vec<u64>, SensoryRoiError> {
    if pixels.len() != mask.len() {
        return Err(SensoryRoiError::MaskLengthMismatch {
            expected: pixels.len(),
            actual: mask.len(),
        });
    }
    let mut msum = 0u64;
    for &m in mask {
        msum = badd(msum, m % BABYBEAR_P);
    }
    if msum != 0 {
        return Err(SensoryRoiError::NonZeroSumMask { sum: msum });
    }
    Ok(pixels
        .iter()
        .zip(mask.iter())
        .map(|(&b, &m)| badd(b as u64, m % BABYBEAR_P))
        .collect())
}

/// Exact involutive mask bijection `shift_mask(p, p', m) = m + p - p' (mod P)` witnessing
/// `TVD = 0` indistinguishability for any two same-sum sample blocks `p, p'`.
pub fn shift_zero_sum_mask(
    p: &[u8],
    p_prime: &[u8],
    mask: &[u64],
) -> Result<Vec<u64>, SensoryRoiError> {
    if p.len() != p_prime.len() || p.len() != mask.len() {
        return Err(SensoryRoiError::MaskLengthMismatch {
            expected: p.len(),
            actual: mask.len(),
        });
    }
    Ok(p.iter()
        .zip(p_prime.iter())
        .zip(mask.iter())
        .map(|((&a, &b), &m)| bsub(badd(m % BABYBEAR_P, a as u64), b as u64))
        .collect())
}

fn build_blur_cert_from_parts(
    tile_sums: &[u32],
    raw_commits: &[Digest],
    tile_lens: &[u32],
    sum_salts: &[Salt256],
    merkle_layers: &[Vec<Digest>],
    blur_indices: &[u32],
    zero_sum_mask: &[u64],
) -> Result<BlurEnvelopeCert, SensoryRoiError> {
    if zero_sum_mask.len() != blur_indices.len() {
        return Err(SensoryRoiError::MaskLengthMismatch {
            expected: blur_indices.len(),
            actual: zero_sum_mask.len(),
        });
    }
    let mut msum = 0u64;
    for &m in zero_sum_mask {
        msum = badd(msum, m % BABYBEAR_P);
    }
    if msum != 0 {
        return Err(SensoryRoiError::NonZeroSumMask { sum: msum });
    }
    let mut entries = Vec::with_capacity(blur_indices.len());
    let mut masked_terms = Vec::with_capacity(blur_indices.len());
    let mut total_sum = 0u64;
    for (&idx, &m) in blur_indices.iter().zip(zero_sum_mask.iter()) {
        let i = idx as usize;
        let sm = tile_sums[i];
        let len = tile_lens[i];
        total_sum += sm as u64;
        entries.push(BlurTileEntry {
            tile_idx: idx,
            tile_sum: sm,
            tile_len: len,
            mean_value: sm / len,
            sum_salt: sum_salts[i],
            sealed_raw_commit: raw_commits[i],
            merkle_path: extract_merkle_path(merkle_layers, i),
        });
        masked_terms.push(badd((sm as u64) % BABYBEAR_P, m % BABYBEAR_P));
    }
    Ok(BlurEnvelopeCert {
        entries,
        claimed_envelope_sum: total_sum,
        masked_terms,
    })
}

impl SealedSensorFrame {
    pub fn open_merkle_path(&self, tile_idx: usize) -> Vec<Digest> {
        extract_merkle_path(&self.merkle_layers, tile_idx)
    }

    pub fn roi_view(&self, in_frustum: impl Fn(usize) -> bool) -> (Digest, Vec<RoiTileItem>) {
        let items = self
            .tiles
            .iter()
            .enumerate()
            .map(|(i, t)| {
                if in_frustum(i) {
                    RoiTileItem::Opened {
                        pixels: t.pixels.clone(),
                        raw_salt: t.raw_salt,
                        sum_salt: t.sum_salt,
                    }
                } else {
                    RoiTileItem::Sealed {
                        leaf: self.merkle_layers[0][i],
                    }
                }
            })
            .collect();
        (self.header.merkle_root, items)
    }

    pub fn open_roi_cert(&self, roi_indices: &[u32]) -> RoiRevealCert {
        let openings = roi_indices
            .iter()
            .map(|&idx| {
                let i = idx as usize;
                let t = &self.tiles[i];
                RoiTileOpening {
                    tile_idx: idx,
                    pixels: t.pixels.clone(),
                    raw_salt: t.raw_salt,
                    sum_salt: t.sum_salt,
                    merkle_path: self.open_merkle_path(i),
                }
            })
            .collect();
        RoiRevealCert { openings }
    }

    pub fn open_blur_cert(
        &self,
        blur_indices: &[u32],
        zero_sum_mask: &[u64],
    ) -> Result<BlurEnvelopeCert, SensoryRoiError> {
        let sum_salts: Vec<Salt256> = self.tiles.iter().map(|t| t.sum_salt).collect();
        let tile_lens: Vec<u32> = self.tiles.iter().map(|t| t.pixels.len() as u32).collect();
        build_blur_cert_from_parts(
            &self.tile_sums,
            &self.raw_commits,
            &tile_lens,
            &sum_salts,
            &self.merkle_layers,
            blur_indices,
            zero_sum_mask,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk_salt(tag: u8, idx: usize) -> Salt256 {
        let mut s = [0u8; 32];
        s[0] = tag;
        s[1..9].copy_from_slice(&(idx as u64).to_le_bytes());
        s
    }

    #[test]
    fn roundtrip_roi_and_blur_cert() {
        let cores = CachedCshakeCores::new();
        let hw_key = [0x42u8; 32];
        let ctx = FrameContext {
            sensor_id: 7,
            frame_seq: 1,
            timestamp_ns: 1_000_000,
        };
        let tiles: Vec<RawSensorTile> = (0..4)
            .map(|i| RawSensorTile {
                pixels: vec![(20 + i * 30) as u8; 256],
                raw_salt: mk_salt(1, i),
                sum_salt: mk_salt(2, i),
            })
            .collect();
        let frame = seal_sensor_frame(
            &cores,
            &hw_key,
            ctx,
            2,
            2,
            2,
            SensorModality::Csi2Tile16x16,
            tiles,
        )
        .expect("seal ok");
        let roi = frame.open_roi_cert(&[0, 3]);
        verify_roi_reveal_cert(&cores, &hw_key, &frame.header, &roi).expect("roi verify ok");
        let mask = make_zero_sum_mask(2, &[987654321]).unwrap();
        let blur = frame.open_blur_cert(&[1, 2], &mask).unwrap();
        verify_blur_envelope_cert(&cores, &hw_key, &frame.header, &blur).expect("blur verify ok");
    }
}
