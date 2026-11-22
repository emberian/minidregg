//! Wearable "Belief Circles" & Spatial Co-Presence (*Rainbows End* SHE Organ #3).
//!
//! Byte-exact native counterpart of `Assurance/WearableBeliefCircle.lean`:
//! - **Physical Co-Presence (`Hancke–Kuhn` / `dregg_distance_tdc`):** 128-round rapid-bit
//!   picosecond ToF challenge-response with `3,990 ps` hardware turnaround floor, `230 ps`
//!   32-tap Vernier TDC quantization, single-shot challenge lock (`u_lock`), and exact integer
//!   speed-of-light (`c = 299,792,458 pm/ps`) radius enforcement.
//! - **Traffic-Analysis-Free Transport (`Theory.Channel`):** Constant-rate fixed-size `256 B`
//!   (`P1`) / `1,024 B` (`P2`) `cSHAKE256` counter-mode encrypt-then-MAC regular & duty cells,
//!   relay fill cells, and replay-protected mux/demux.
//! - **Scoped Belief-Circle Spatial AR Overlay CRDT (`PqSelectiveBiscuit` + ToF + `IConfluent`):**
//!   Post-quantum membership & ancestor-cone revocation verification + ToF co-presence gating +
//!   `0`-round BFT join-semilattice (`BTreeMap` set union) merge over room spatial anchor cells.

#![deny(warnings)]

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::pq_biscuit::{
    constant_time_eq, cshake32, encode_field, encode_leb128, sub_mask, verify_token, Digest32,
    HolderToken, PqSigBackend, RevocationSet,
};

// ---------------------------------------------------------------------------
// Domain Separation Strings & Silicon Constants (exact match to Lean)
// ---------------------------------------------------------------------------

pub const CUST_TOF_R0: &[u8] = b"MINIDREGG.BELIEF_CIRCLE.TOF_R0/v1";
pub const CUST_TOF_R1: &[u8] = b"MINIDREGG.BELIEF_CIRCLE.TOF_R1/v1";
pub const CUST_TOF_CHAL: &[u8] = b"MINIDREGG.BELIEF_CIRCLE.TOF_CHAL/v1";
pub const CUST_CELL_STREAM: &[u8] = b"MINIDREGG.BELIEF_CIRCLE.CELL_STREAM/v1";
pub const CUST_CELL_MAC: &[u8] = b"MINIDREGG.BELIEF_CIRCLE.CELL_MAC/v1";
pub const CUST_CELL_FILL: &[u8] = b"MINIDREGG.BELIEF_CIRCLE.CELL_FILL/v1";
pub const CUST_OVERLAY_ITEM: &[u8] = b"MINIDREGG.BELIEF_CIRCLE.OVERLAY_ITEM/v1";
pub const CUST_OVERLAY_ROOT: &[u8] = b"MINIDREGG.BELIEF_CIRCLE.OVERLAY_ROOT/v1";

/// Exact SI speed of light in picometers per picosecond (`299,792,458 m/s`).
pub const C_PM_PER_PS: u128 = 299_792_458;
/// Picometers per millimeter (`1 mm = 10^9 pm`).
pub const PM_PER_MM: u128 = 1_000_000_000;
/// `dregg_distance_tdc` rapid-bit pad-to-pad turnaround floor (`3.99 ns` post-SPEF).
pub const DREGG_T_PROC_MIN_PS: u64 = 3_990;
/// `dregg_vernier_tdc32` Vernier step (`450 ps` slow tap - `220 ps` fast tap).
pub const DREGG_VERNIER_STEP_PS: u64 = 230;
/// Default chained 2x64-round `dregg_distance_tdc` rapid-bit session (`(3/4)^128 < 2^-53`).
pub const DEFAULT_TOF_ROUNDS: usize = 128;
/// Default room co-presence radius (`3,000 mm = 3.0 m`).
pub const DEFAULT_D_MAX_MM: u64 = 3_000;
/// Required `PqSelectiveBiscuit` right bit to author AR overlay annotations.
pub const CIRCLE_WRITE_RIGHT: u64 = 0x01;

pub const HEADER_LEN: usize = 8;
pub const TAG_LEN: usize = 16;
pub const DUTY_PUBLIC_LEN: usize = 160;
pub const MLKEM_SEAL_OVERHEAD: usize = 5;

// ---------------------------------------------------------------------------
// §1. Picosecond ToF Distance-Bounding (`Hancke–Kuhn` / `dregg_distance_tdc`)
// ---------------------------------------------------------------------------

/// Parameters of a picosecond ToF distance-bounding gate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TofParams {
    pub rounds: usize,
    pub t_proc_min_ps: u64,
    pub d_max_mm: u64,
    pub vernier_step_ps: u64,
}

impl TofParams {
    pub fn dregg_default() -> Self {
        Self {
            rounds: DEFAULT_TOF_ROUNDS,
            t_proc_min_ps: DREGG_T_PROC_MIN_PS,
            d_max_mm: DEFAULT_D_MAX_MM,
            vernier_step_ps: DREGG_VERNIER_STEP_PS,
        }
    }

    /// Exact per-round acceptance deadline (ps): `t_proc_min + floor(2 * d_max * 10^9 / c)`.
    pub fn max_round_time_ps(&self) -> u64 {
        t_max_of_radius_ps(self.t_proc_min_ps, self.d_max_mm)
    }
}

/// Exact integer deadline in picoseconds for radius `d_max_mm` (mm).
pub fn t_max_of_radius_ps(t_proc_min_ps: u64, d_max_mm: u64) -> u64 {
    let prop = (2u128 * (d_max_mm as u128) * PM_PER_MM) / C_PM_PER_PS;
    t_proc_min_ps.saturating_add(prop as u64)
}

/// Minimum physically realizable round-trip time (ps) at distance `d_mm` (mm):
/// `t_proc_min + ceil(2 * d_mm * 10^9 / c)`.
pub fn causal_rtt_ps(t_proc_min_ps: u64, d_mm: u64) -> u64 {
    let num = 2u128 * (d_mm as u128) * PM_PER_MM;
    let prop = (num + C_PM_PER_PS - 1) / C_PM_PER_PS;
    t_proc_min_ps.saturating_add(prop as u64)
}

/// Decode `dregg_distance_tdc.sv` `{coarse_cnt - 2, vernier_fine}` register into picoseconds.
pub fn tdc_cycles_to_ps(
    coarse_cycles: u64,
    vernier_fine: u64,
    clk_period_ps: u64,
    vernier_step_ps: u64,
) -> u64 {
    coarse_cycles
        .saturating_mul(clk_period_ps)
        .saturating_add(vernier_fine.saturating_mul(vernier_step_ps))
}

/// Expand bytes into LSB-first bits (matches Lean `bytesToBitsLSB`).
pub fn bytes_to_bits_lsb(bs: &[u8]) -> Vec<bool> {
    let mut out = Vec::with_capacity(bs.len() * 8);
    for &b in bs {
        for j in 0..8 {
            out.push(((b >> j) & 1) == 1);
        }
    }
    out
}

/// Pack LSB-first bits into bytes (matches Lean `bitsToBytesLSB`).
pub fn bits_to_bytes_lsb(bits: &[bool]) -> Vec<u8> {
    let mut out = Vec::with_capacity(bits.len() / 8);
    for chunk in bits.chunks_exact(8) {
        let mut b = 0u8;
        for (j, &bit) in chunk.iter().enumerate() {
            if bit {
                b |= 1u8 << j;
            }
        }
        out.push(b);
    }
    out
}

/// Derive 128 rapid-bit ToF register bits via domain-separated `cSHAKE256`.
pub fn derive_tof_bits(cust: &[u8], seed: &[u8], nonce: &[u8]) -> Vec<bool> {
    let mut buf = Vec::with_capacity(seed.len() + nonce.len());
    buf.extend_from_slice(seed);
    buf.extend_from_slice(nonce);
    let digest = cshake32(cust, &buf);
    bytes_to_bits_lsb(&digest[..16])
}

/// Compute honest rapid-bit response vector `resp[i] = if chal[i] { r1[i] } else { r0[i] }`.
pub fn compute_tof_response(r0: &[bool], r1: &[bool], chal: &[bool]) -> Vec<bool> {
    chal.iter()
        .zip(r0.iter().zip(r1.iter()))
        .map(|(&c, (&a, &b))| if c { b } else { a })
        .collect()
}

/// Complete `k`-round rapid-bit ToF exchange transcript.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TofTranscript {
    pub r0: Vec<bool>,
    pub r1: Vec<bool>,
    pub chal: Vec<bool>,
    pub resp: Vec<bool>,
    pub times_ps: Vec<u64>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TofRejectReason {
    LengthMismatch,
    BelowTurnaroundFloor(usize),
    TofTimeout(usize),
    ResponseBitMismatch(usize),
}

/// Verify a `k`-round rapid-bit ToF transcript (byte-exact with Lean `verifyTofSession`).
pub fn verify_tof_session(
    params: &TofParams,
    tr: &TofTranscript,
) -> Result<(), TofRejectReason> {
    let k = params.rounds;
    if k == 0
        || tr.r0.len() != k
        || tr.r1.len() != k
        || tr.chal.len() != k
        || tr.resp.len() != k
        || tr.times_ps.len() != k
    {
        return Err(TofRejectReason::LengthMismatch);
    }
    let t_min = params.t_proc_min_ps;
    let t_max = params.max_round_time_ps();
    for i in 0..k {
        let t = tr.times_ps[i];
        if t < t_min {
            return Err(TofRejectReason::BelowTurnaroundFloor(i));
        }
        if t > t_max {
            return Err(TofRejectReason::TofTimeout(i));
        }
        let expected = if tr.chal[i] { tr.r1[i] } else { tr.r0[i] };
        if tr.resp[i] != expected {
            return Err(TofRejectReason::ResponseBitMismatch(i));
        }
    }
    Ok(())
}

/// Hardware model of `dregg_distance_tdc`'s single-shot challenge lock (`u_lock`):
/// each round `i` locks permanently on its first query and NEVER reveals the complementary bit.
#[derive(Clone, Debug)]
pub struct SingleShotResponder {
    r0: Vec<bool>,
    r1: Vec<bool>,
    locked_chal: Vec<Option<bool>>,
}

impl SingleShotResponder {
    pub fn new(r0: Vec<bool>, r1: Vec<bool>) -> Self {
        let k = r0.len().min(r1.len());
        Self {
            r0: r0[..k].to_vec(),
            r1: r1[..k].to_vec(),
            locked_chal: vec![None; k],
        }
    }

    /// Query round `i` with challenge bit `c`. First query locks round `i` to `c`; any
    /// subsequent attempt to read `!c` is rejected (`None`), preventing dual-bit extraction.
    pub fn query_round(&mut self, i: usize, c: bool) -> Option<bool> {
        if i >= self.locked_chal.len() {
            return None;
        }
        match self.locked_chal[i] {
            None => {
                self.locked_chal[i] = Some(c);
                Some(if c { self.r1[i] } else { self.r0[i] })
            }
            Some(prev) if prev == c => Some(if c { self.r1[i] } else { self.r0[i] }),
            Some(_) => None,
        }
    }
}

// ---------------------------------------------------------------------------
// §2. Constant-Rate `Theory.Channel` (`256 B` P1 / `1,024 B` P2) Cells
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChannelProfile {
    /// `P1`: `256 B` cells (`1 Hz`, `E = 16`, regular sealed `232 B`, duty sealed `72 B`).
    P1,
    /// `P2`: `1,024 B` cells (`5 Hz`, `E = 64`, regular sealed `1,000 B`, duty sealed `840 B`).
    P2,
}

impl ChannelProfile {
    pub const fn cell_len(self) -> usize {
        match self {
            Self::P1 => 256,
            Self::P2 => 1024,
        }
    }

    pub const fn epoch_ticks(self) -> u16 {
        match self {
            Self::P1 => 16,
            Self::P2 => 64,
        }
    }

    pub const fn body_len(self) -> usize {
        self.cell_len() - HEADER_LEN
    }

    pub const fn sealed_len(self) -> usize {
        self.cell_len() - HEADER_LEN - TAG_LEN
    }

    pub const fn duty_sealed_len(self) -> usize {
        self.cell_len() - HEADER_LEN - DUTY_PUBLIC_LEN - TAG_LEN
    }
}

/// Big-endian 8-byte `Theory.Channel.Header` (`domain:2 | epoch:2 | tick:2 | slot:2`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CellHeader {
    pub domain: u16,
    pub epoch: u16,
    pub tick: u16,
    pub slot: u16,
}

impl CellHeader {
    pub fn encode(self) -> [u8; HEADER_LEN] {
        let mut out = [0u8; HEADER_LEN];
        out[0..2].copy_from_slice(&self.domain.to_be_bytes());
        out[2..4].copy_from_slice(&self.epoch.to_be_bytes());
        out[4..6].copy_from_slice(&self.tick.to_be_bytes());
        out[6..8].copy_from_slice(&self.slot.to_be_bytes());
        out
    }

    pub fn decode(bytes: &[u8]) -> Option<Self> {
        if bytes.len() < HEADER_LEN {
            return None;
        }
        Some(Self {
            domain: u16::from_be_bytes([bytes[0], bytes[1]]),
            epoch: u16::from_be_bytes([bytes[2], bytes[3]]),
            tick: u16::from_be_bytes([bytes[4], bytes[5]]),
            slot: u16::from_be_bytes([bytes[6], bytes[7]]),
        })
    }

    pub const fn is_duty_tick(self) -> bool {
        self.tick == 0
    }
}

/// Public 160-byte prefix of a `tick == 0` duty cell (`vrf 96 | verdictRoot 32 | accRoot 32`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DutyPublic {
    pub vrf: [u8; 96],
    pub verdict_root: [u8; 32],
    pub acc_root: [u8; 32],
}

impl DutyPublic {
    pub fn encode(&self) -> [u8; DUTY_PUBLIC_LEN] {
        let mut out = [0u8; DUTY_PUBLIC_LEN];
        out[0..96].copy_from_slice(&self.vrf);
        out[96..128].copy_from_slice(&self.verdict_root);
        out[128..160].copy_from_slice(&self.acc_root);
        out
    }

    pub fn decode(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != DUTY_PUBLIC_LEN {
            return None;
        }
        let mut vrf = [0u8; 96];
        let mut verdict_root = [0u8; 32];
        let mut acc_root = [0u8; 32];
        vrf.copy_from_slice(&bytes[0..96]);
        verdict_root.copy_from_slice(&bytes[96..128]);
        acc_root.copy_from_slice(&bytes[128..160]);
        Some(Self {
            vrf,
            verdict_root,
            acc_root,
        })
    }
}

/// Wearable activity classes multiplexed into constant-rate `Theory.Channel` cells.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WearableActivity {
    Idle,
    JittQuery(Vec<u8>),
    ArHazardReticle {
        anchor_id: u64,
        priority: u8,
        patch: Vec<u8>,
    },
    OverlayPatch {
        anchor_id: u64,
        patch: Vec<u8>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CellError {
    WrongLength,
    MissingDutyPublic,
    MacMismatch,
    MalformedPlaintext,
    UnknownViewTag(u8),
    ReplayedCell(CellHeader),
    WrongDomain,
}

/// Counter-mode `cSHAKE256` keystream (byte-exact with Lean `cshakeKeystream`).
pub fn cshake_keystream(cust: &[u8], key: &[u8], ctx: &[u8], len: usize) -> Vec<u8> {
    let blocks = (len + 31) / 32;
    let mut out = Vec::with_capacity(blocks * 32);
    let mut input = Vec::with_capacity(key.len() + ctx.len() + 4);
    input.extend_from_slice(key);
    input.extend_from_slice(ctx);
    input.extend_from_slice(&[0u8; 4]);
    let ctr_off = key.len() + ctx.len();
    for ctr in 0..blocks {
        input[ctr_off..ctr_off + 4].copy_from_slice(&(ctr as u32).to_be_bytes());
        out.extend_from_slice(&cshake32(cust, &input));
    }
    out.truncate(len);
    out
}

/// Pack `WearableActivity` into exact `L`-byte plaintext (`viewTag 1 | fragSeq 2 | fragLen 2 | payload`).
pub fn pack_activity_plaintext(sealed_len: usize, act: &WearableActivity) -> Vec<u8> {
    let cap = sealed_len.saturating_sub(MLKEM_SEAL_OVERHEAD);
    let mut out = vec![0u8; sealed_len];
    match act {
        WearableActivity::Idle => {
            // viewTag = 0x00, fragSeq = 0, fragLen = 0, zero padding.
        }
        WearableActivity::JittQuery(payload) => {
            let n = payload.len().min(cap);
            out[0] = 0x01;
            out[1..3].copy_from_slice(&0u16.to_be_bytes());
            out[3..5].copy_from_slice(&(n as u16).to_be_bytes());
            out[5..5 + n].copy_from_slice(&payload[..n]);
        }
        WearableActivity::ArHazardReticle {
            anchor_id,
            priority,
            patch,
        } => {
            let mut full = Vec::with_capacity(1 + patch.len());
            full.push(*priority);
            full.extend_from_slice(patch);
            let n = full.len().min(cap);
            out[0] = 0x02;
            out[1..3].copy_from_slice(&((*anchor_id % 65536) as u16).to_be_bytes());
            out[3..5].copy_from_slice(&(n as u16).to_be_bytes());
            out[5..5 + n].copy_from_slice(&full[..n]);
        }
        WearableActivity::OverlayPatch { anchor_id, patch } => {
            let n = patch.len().min(cap);
            out[0] = 0x03;
            out[1..3].copy_from_slice(&((*anchor_id % 65536) as u16).to_be_bytes());
            out[3..5].copy_from_slice(&(n as u16).to_be_bytes());
            out[5..5 + n].copy_from_slice(&patch[..n]);
        }
    }
    out
}

/// Unpack a decrypted `L`-byte plaintext back into `WearableActivity`.
pub fn unpack_activity_plaintext(pt: &[u8]) -> Result<WearableActivity, CellError> {
    if pt.len() < MLKEM_SEAL_OVERHEAD {
        return Err(CellError::MalformedPlaintext);
    }
    let view_tag = pt[0];
    let frag_seq = u16::from_be_bytes([pt[1], pt[2]]) as u64;
    let frag_len = u16::from_be_bytes([pt[3], pt[4]]) as usize;
    let cap = pt.len() - MLKEM_SEAL_OVERHEAD;
    if frag_len > cap {
        return Err(CellError::MalformedPlaintext);
    }
    let body = &pt[5..5 + frag_len];
    match view_tag {
        0x00 => Ok(WearableActivity::Idle),
        0x01 => Ok(WearableActivity::JittQuery(body.to_vec())),
        0x02 => {
            if body.is_empty() {
                return Err(CellError::MalformedPlaintext);
            }
            Ok(WearableActivity::ArHazardReticle {
                anchor_id: frag_seq,
                priority: body[0],
                patch: body[1..].to_vec(),
            })
        }
        0x03 => Ok(WearableActivity::OverlayPatch {
            anchor_id: frag_seq,
            patch: body.to_vec(),
        }),
        other => Err(CellError::UnknownViewTag(other)),
    }
}

/// Seal a `WearableActivity` into a fixed-size `256 B` (`P1`) or `1,024 B` (`P2`)
/// `cSHAKE256` encrypt-then-MAC `Theory.Channel` cell (byte-exact with Lean `sealBeliefCellCshake`).
pub fn seal_belief_cell(
    profile: ChannelProfile,
    circle_key: &[u8],
    header: CellHeader,
    duty_pub: Option<&DutyPublic>,
    act: &WearableActivity,
) -> Result<Vec<u8>, CellError> {
    let hdr_bytes = header.encode();
    let mut cell = Vec::with_capacity(profile.cell_len());
    cell.extend_from_slice(&hdr_bytes);
    if header.is_duty_tick() {
        let dp = duty_pub.ok_or(CellError::MissingDutyPublic)?;
        let dp_bytes = dp.encode();
        let l = profile.duty_sealed_len();
        let pt = pack_activity_plaintext(l, act);
        let ks = cshake_keystream(CUST_CELL_STREAM, circle_key, &hdr_bytes, l);
        let ct: Vec<u8> = pt.iter().zip(ks.iter()).map(|(a, b)| a ^ b).collect();
        let mut mac_in =
            Vec::with_capacity(circle_key.len() + HEADER_LEN + DUTY_PUBLIC_LEN + ct.len());
        mac_in.extend_from_slice(circle_key);
        mac_in.extend_from_slice(&hdr_bytes);
        mac_in.extend_from_slice(&dp_bytes);
        mac_in.extend_from_slice(&ct);
        let tag = cshake32(CUST_CELL_MAC, &mac_in);
        cell.extend_from_slice(&dp_bytes);
        cell.extend_from_slice(&ct);
        cell.extend_from_slice(&tag[..TAG_LEN]);
    } else {
        let l = profile.sealed_len();
        let pt = pack_activity_plaintext(l, act);
        let ks = cshake_keystream(CUST_CELL_STREAM, circle_key, &hdr_bytes, l);
        let ct: Vec<u8> = pt.iter().zip(ks.iter()).map(|(a, b)| a ^ b).collect();
        let mut mac_in = Vec::with_capacity(circle_key.len() + HEADER_LEN + ct.len());
        mac_in.extend_from_slice(circle_key);
        mac_in.extend_from_slice(&hdr_bytes);
        mac_in.extend_from_slice(&ct);
        let tag = cshake32(CUST_CELL_MAC, &mac_in);
        cell.extend_from_slice(&ct);
        cell.extend_from_slice(&tag[..TAG_LEN]);
    }
    debug_assert_eq!(cell.len(), profile.cell_len());
    Ok(cell)
}

/// Authenticate and open a fixed-size `Theory.Channel` cell. Verifies the 16-byte `cSHAKE256`
/// MAC in constant time BEFORE decrypting plaintext.
pub fn open_belief_cell(
    profile: ChannelProfile,
    circle_key: &[u8],
    raw: &[u8],
) -> Result<(CellHeader, Option<DutyPublic>, WearableActivity), CellError> {
    if raw.len() != profile.cell_len() {
        return Err(CellError::WrongLength);
    }
    let header = CellHeader::decode(&raw[..HEADER_LEN]).ok_or(CellError::WrongLength)?;
    let hdr_bytes = &raw[..HEADER_LEN];
    let tag_received = &raw[raw.len() - TAG_LEN..];
    if header.is_duty_tick() {
        let dp_bytes = &raw[HEADER_LEN..HEADER_LEN + DUTY_PUBLIC_LEN];
        let ct = &raw[HEADER_LEN + DUTY_PUBLIC_LEN..raw.len() - TAG_LEN];
        let mut mac_in =
            Vec::with_capacity(circle_key.len() + HEADER_LEN + DUTY_PUBLIC_LEN + ct.len());
        mac_in.extend_from_slice(circle_key);
        mac_in.extend_from_slice(hdr_bytes);
        mac_in.extend_from_slice(dp_bytes);
        mac_in.extend_from_slice(ct);
        let expected_tag = cshake32(CUST_CELL_MAC, &mac_in);
        if !constant_time_eq(&expected_tag[..TAG_LEN], tag_received) {
            return Err(CellError::MacMismatch);
        }
        let ks = cshake_keystream(CUST_CELL_STREAM, circle_key, hdr_bytes, ct.len());
        let pt: Vec<u8> = ct.iter().zip(ks.iter()).map(|(a, b)| a ^ b).collect();
        let act = unpack_activity_plaintext(&pt)?;
        let dp = DutyPublic::decode(dp_bytes).ok_or(CellError::MissingDutyPublic)?;
        Ok((header, Some(dp), act))
    } else {
        let ct = &raw[HEADER_LEN..raw.len() - TAG_LEN];
        let mut mac_in = Vec::with_capacity(circle_key.len() + HEADER_LEN + ct.len());
        mac_in.extend_from_slice(circle_key);
        mac_in.extend_from_slice(hdr_bytes);
        mac_in.extend_from_slice(ct);
        let expected_tag = cshake32(CUST_CELL_MAC, &mac_in);
        if !constant_time_eq(&expected_tag[..TAG_LEN], tag_received) {
            return Err(CellError::MacMismatch);
        }
        let ks = cshake_keystream(CUST_CELL_STREAM, circle_key, hdr_bytes, ct.len());
        let pt: Vec<u8> = ct.iter().zip(ks.iter()).map(|(a, b)| a ^ b).collect();
        let act = unpack_activity_plaintext(&pt)?;
        Ok((header, None, act))
    }
}

/// Generate a relay PRF fill cell of exact size `profile.cell_len()` for an absent slot.
pub fn fill_belief_cell(profile: ChannelProfile, fill_key: &[u8], header: CellHeader) -> Vec<u8> {
    let hdr_bytes = header.encode();
    let mut cell = Vec::with_capacity(profile.cell_len());
    cell.extend_from_slice(&hdr_bytes);
    cell.extend_from_slice(&cshake_keystream(
        CUST_CELL_FILL,
        fill_key,
        &hdr_bytes,
        profile.body_len(),
    ));
    cell
}

/// Constant-rate belief-circle cell multiplexer and replay-protected demultiplexer.
pub struct ConstantRateCellMux {
    pub profile: ChannelProfile,
    pub domain: u16,
    pub slot: u16,
    circle_key: Digest32,
    tx_queue: VecDeque<WearableActivity>,
    seen_headers: BTreeSet<CellHeader>,
}

impl ConstantRateCellMux {
    pub fn new(profile: ChannelProfile, domain: u16, slot: u16, circle_key: Digest32) -> Self {
        Self {
            profile,
            domain,
            slot,
            circle_key,
            tx_queue: VecDeque::new(),
            seen_headers: BTreeSet::new(),
        }
    }

    pub fn enqueue(&mut self, act: WearableActivity) {
        self.tx_queue.push_back(act);
    }

    /// Emit exactly one fixed-size `256/1024 B` cell for `(epoch, tick)`: dequeues one pending
    /// activity or emits indistinguishable `.Idle` cover padding if the queue is empty.
    pub fn emit_tick(
        &mut self,
        epoch: u16,
        tick: u16,
        duty_pub: Option<&DutyPublic>,
    ) -> Result<Vec<u8>, CellError> {
        let header = CellHeader {
            domain: self.domain,
            epoch,
            tick,
            slot: self.slot,
        };
        let act = self.tx_queue.pop_front().unwrap_or(WearableActivity::Idle);
        seal_belief_cell(self.profile, &self.circle_key, header, duty_pub, &act)
    }

    /// Verify, decrypt, and replay-protect an incoming cell for this circle domain.
    pub fn demux_cell(
        &mut self,
        raw: &[u8],
    ) -> Result<(CellHeader, Option<DutyPublic>, WearableActivity), CellError> {
        let (hdr, dp, act) = open_belief_cell(self.profile, &self.circle_key, raw)?;
        if hdr.domain != self.domain {
            return Err(CellError::WrongDomain);
        }
        if !self.seen_headers.insert(hdr) {
            return Err(CellError::ReplayedCell(hdr));
        }
        Ok((hdr, dp, act))
    }
}

// ---------------------------------------------------------------------------
// §3. Scoped Belief-Circle Spatial AR Overlay CRDT (`PqSelectiveBiscuit` + ToF + `IConfluent`)
// ---------------------------------------------------------------------------

/// Canonical authenticated spatial AR overlay annotation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpatialEntry {
    pub circle_id: u64,
    pub anchor_id: u64,
    pub lamport_clock: u64,
    pub author_slot: u16,
    pub priority: u8,
    pub label: Vec<u8>,
    pub entry_digest: Digest32,
}

/// Compute canonical 32-byte `SpatialEntry` digest (byte-exact with Lean `computeEntryDigest`).
pub fn compute_entry_digest(
    circle_id: u64,
    anchor_id: u64,
    lamport_clock: u64,
    author_slot: u16,
    priority: u8,
    label: &[u8],
) -> Digest32 {
    let mut buf = Vec::with_capacity(8 + 8 + 8 + 2 + 1 + 10 + label.len());
    buf.extend_from_slice(&circle_id.to_be_bytes());
    buf.extend_from_slice(&anchor_id.to_be_bytes());
    buf.extend_from_slice(&lamport_clock.to_be_bytes());
    buf.extend_from_slice(&author_slot.to_be_bytes());
    buf.push(priority);
    encode_field(label, &mut buf);
    cshake32(CUST_OVERLAY_ITEM, &buf)
}

impl SpatialEntry {
    pub fn new(
        circle_id: u64,
        anchor_id: u64,
        lamport_clock: u64,
        author_slot: u16,
        priority: u8,
        label: Vec<u8>,
    ) -> Self {
        let entry_digest = compute_entry_digest(
            circle_id,
            anchor_id,
            lamport_clock,
            author_slot,
            priority,
            &label,
        );
        Self {
            circle_id,
            anchor_id,
            lamport_clock,
            author_slot,
            priority,
            label,
            entry_digest,
        }
    }
}

/// Incoming unverified AR overlay update carrying PQ credential + ToF transcript.
#[derive(Clone, Debug)]
pub struct CircleOverlayUpdate {
    pub circle_id: u64,
    pub anchor_id: u64,
    pub lamport_clock: u64,
    pub author_slot: u16,
    pub priority: u8,
    pub label: Vec<u8>,
    pub token: HolderToken,
    pub tof: TofTranscript,
}

/// Verifier policy pinned by a belief-circle wearable.
#[derive(Clone, Debug)]
pub struct CirclePolicy {
    pub circle_id: u64,
    pub issuer_pk: Vec<u8>,
    pub revocations: RevocationSet,
    pub required_rights: u64,
    pub tof_params: TofParams,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdmitReject {
    WrongCircle,
    InvalidCredential,
    InsufficientRights,
    TofFailed(TofRejectReason),
}

/// Scoped admission gate: verifies circle ID, `PqSelectiveBiscuit` token + revocation cone,
/// required capability rights, and picosecond ToF co-presence before creating a `SpatialEntry`.
pub fn admit_circle_update<S: PqSigBackend>(
    scheme: &S,
    pol: &CirclePolicy,
    now: u64,
    upd: &CircleOverlayUpdate,
) -> Result<SpatialEntry, AdmitReject> {
    if upd.circle_id != pol.circle_id {
        return Err(AdmitReject::WrongCircle);
    }
    let va = verify_token(scheme, &pol.issuer_pk, &pol.revocations, now, &upd.token)
        .map_err(|_| AdmitReject::InvalidCredential)?;
    if !sub_mask(pol.required_rights, va.rights) {
        return Err(AdmitReject::InsufficientRights);
    }
    verify_tof_session(&pol.tof_params, &upd.tof).map_err(AdmitReject::TofFailed)?;
    Ok(SpatialEntry::new(
        upd.circle_id,
        upd.anchor_id,
        upd.lamport_clock,
        upd.author_slot,
        upd.priority,
        upd.label.clone(),
    ))
}

/// Projected AR reticle item rendered for an anchor cell (mirrors `LightClientAndViewLens.ViewNode`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReticleItem {
    pub label: String,
    pub tag: &'static str,
    pub lamport_clock: u64,
}

/// `IConfluent` join-semilattice state (`⊔ = ∪`) of admitted spatial AR annotations.
/// Keyed by `(anchor_id, entry_digest)` so canonical iteration order matches Lean `entryLe`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct OverlayState {
    entries: BTreeMap<(u64, Digest32), SpatialEntry>,
}

impl OverlayState {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn insert_admitted(&mut self, entry: SpatialEntry) {
        self.entries
            .insert((entry.anchor_id, entry.entry_digest), entry);
    }

    /// Admit an incoming update through `admit_circle_update` and insert into the semilattice;
    /// unauthenticated, revoked, or out-of-range relays are deterministically dropped.
    pub fn ingest<S: PqSigBackend>(
        &mut self,
        scheme: &S,
        pol: &CirclePolicy,
        now: u64,
        upd: &CircleOverlayUpdate,
    ) -> Result<Digest32, AdmitReject> {
        let entry = admit_circle_update(scheme, pol, now, upd)?;
        let d = entry.entry_digest;
        self.insert_admitted(entry);
        Ok(d)
    }

    /// Coordination-free `IConfluent` semilattice join (`self ⊔ other`, commutative, associative,
    /// idempotent — `0` BFT rounds).
    pub fn join(&self, other: &Self) -> Self {
        let mut merged = self.entries.clone();
        for (k, v) in &other.entries {
            merged.entry(*k).or_insert_with(|| v.clone());
        }
        Self { entries: merged }
    }

    /// Canonical 32-byte overlay state root (byte-exact with Lean `overlayStateRoot`).
    pub fn state_root(&self) -> Digest32 {
        let mut buf = Vec::with_capacity(10 + self.entries.len() * 32);
        encode_leb128(self.entries.len(), &mut buf);
        for entry in self.entries.values() {
            buf.extend_from_slice(&entry.entry_digest);
        }
        cshake32(CUST_OVERLAY_ROOT, &buf)
    }

    /// Render the canonical AR reticle items for a spatial anchor cell.
    pub fn render_anchor_reticle(&self, anchor_id: u64) -> Vec<ReticleItem> {
        self.entries
            .values()
            .filter(|e| e.anchor_id == anchor_id)
            .map(|e| ReticleItem {
                label: String::from_utf8_lossy(&e.label).into_owned(),
                tag: if e.priority >= 2 {
                    "hazard"
                } else if e.priority == 1 {
                    "caution"
                } else {
                    "info"
                },
                lamport_clock: e.lamport_clock,
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tof_deadline_and_tdc_decode_exact() {
        let p = TofParams::dregg_default();
        assert_eq!(p.max_round_time_ps(), 24_003);
        assert_eq!(causal_rtt_ps(3_990, 3_000), 24_004); // ceiling exceeds floor by 1 ps at exact boundary
        assert_eq!(causal_rtt_ps(3_990, 2_999), 23_998);
        assert_eq!(tdc_cycles_to_ps(1, 26, 20_000, 230), 25_980);
    }

    #[test]
    fn cell_roundtrip_p1_and_p2_regular_and_duty() {
        let key = cshake32(b"TEST.KEY", b"circle-7");
        let dp = DutyPublic {
            vrf: [0x11; 96],
            verdict_root: [0x22; 32],
            acc_root: [0x33; 32],
        };
        let act = WearableActivity::ArHazardReticle {
            anchor_id: 42,
            priority: 2,
            patch: b"LASER-CLASS-4".to_vec(),
        };
        for profile in [ChannelProfile::P1, ChannelProfile::P2] {
            let h_reg = CellHeader {
                domain: 7,
                epoch: 1,
                tick: 3,
                slot: 0,
            };
            let raw_reg = seal_belief_cell(profile, &key, h_reg, None, &act).unwrap();
            assert_eq!(raw_reg.len(), profile.cell_len());
            let (dh, ddp, dact) = open_belief_cell(profile, &key, &raw_reg).unwrap();
            assert_eq!(dh, h_reg);
            assert!(ddp.is_none());
            assert_eq!(dact, act);

            let h_duty = CellHeader {
                domain: 7,
                epoch: 1,
                tick: 0,
                slot: 0,
            };
            let raw_duty = seal_belief_cell(profile, &key, h_duty, Some(&dp), &act).unwrap();
            assert_eq!(raw_duty.len(), profile.cell_len());
            let (dh2, ddp2, dact2) = open_belief_cell(profile, &key, &raw_duty).unwrap();
            assert_eq!(dh2, h_duty);
            assert_eq!(ddp2.as_ref(), Some(&dp));
            assert_eq!(dact2, act);
        }
    }
}
