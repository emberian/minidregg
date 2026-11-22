//! Vinge "Mysterious Stranger" wetware-hijack defense (temporal flicker & covert LSB scrubber)
//! + plausibly deniable fixed-geometry dual-root duress vault.
//!
//! Byte-exact mirror of `Theory/WetwareSafetyAndDuress.lean` (Lean 4.35.0):
//!
//! * **Part A (`WetwareSafety`).** [`step`] is `Theory.WetwareSafetyAndDuress.step`
//!   (quantize → slew clamp → reversal hold-off) on one byte channel; [`FrameScrubber`] runs it
//!   independently on every byte of a planar frame. The photosafety theorem binds the channel
//!   the guard runs on, so the caller must hand it the **luma plane `Y'`** (plus `Cb`, `Cr`,
//!   alpha) of a `Y'CbCr` surface: guarding `R`, `G`, `B` separately does not bound luma
//!   (Lean `tooth_per_channel_rgb_misses_luma_flicker`, mirrored in the tests). The Lean theorems
//!   `scrubber_enforces_slew_and_reversal_bound`, `revSpaced_count_le`,
//!   `scrubber_kills_subthreshold_stego`, `scrubber_zero_covert_capacity` and
//!   `scrubber_idempotent_on_safe_canonical` are statements about exactly this transition;
//!   the conformance vectors in `testdata/wetware_duress_conformance.json` are the Lean
//!   `#guard_msgs`-pinned `#eval` outputs. [`quant_audio`] and [`snap_release`] mirror
//!   `quantAudio` / `snapRelease`.
//! * **Part B (`DuressChaffVolume`, v1 legacy single-snapshot).** [`DuressVault`] is a
//!   fixed-`N`-slot image of 64-byte blocks sealed under `(root, salt_i, i)`. Kept as a v1
//!   baseline and contrast target; its `derive_root` is a single non-memory-hard cSHAKE256 call
//!   and its in-place `rewrite_owned` leaks across 2 snapshots
//!   (`tooth_single_slot_update_leaks_across_two_snapshots`).
//! * **Part C (`Argon2id` RFC 9106 `v = 0x13` + `BLAKE2b` RFC 7693).** Pure-Rust, zero-unsafe
//!   memory-hard passphrase KDF (`derive_vault_root_argon2id`) verified against the official
//!   RFC 9106 §5.3 test vector and RFC 7693 `BLAKE2b` KATs.
//! * **Part D (`MultiSnapshotDuressVault`, v2 write-all oblivious vault).** Fixed-header
//!   `(epoch: u64, volume_salt: [u8; 32])` + `N` × 64-byte slots where every commit
//!   ([`MultiSnapshotDuressVault::commit_decoy_only`] or [`MultiSnapshotDuressVault::commit_dual`])
//!   strictly increments `epoch` and rewrites ALL `N` slots. Mirrors Lean
//!   `multi_snapshot_trace_indistinguishable` (`TVD = 0` in the ideal-XOF model across arbitrary
//!   `K`-snapshot forensic sequences).
//!
//! Honest security boundaries:
//! * The Lean deniability theorems are in the ideal-XOF model; here per-epoch pads are
//!   cSHAKE256 under Argon2id-derived roots, so deniability is computational (PRF assumption on
//!   cSHAKE256; not mechanised here).
//! * **Coercion vs. availability (`commit_decoy_only` vs. `commit_dual`):** In `commit_decoy_only`,
//!   `root_sov` is absent, so rewriting every non-decoy slot `[0..N) \ I_decoy` with fresh CSPRNG
//!   chaff **intentionally shreds/clobbers** any unmounted sovereign slots (preserving multi-snapshot
//!   deniability at the cost of hidden-volume availability under pure duress writes). To update
//!   decoy notes while preserving hidden sovereign slots across snapshots, the owner must use
//!   `commit_dual` (holding both roots) or restore sovereign state from external backup.
//! * **Rollback & branching boundary:** `MultiSnapshotDuressVault` enforces monotonic `epoch + 1`
//!   on a live instance and exposes [`MultiSnapshotDuressVault::from_bytes_min_epoch`] to reject
//!   stale images when the host tracks a trusted monotonic counter (e.g., hardware SE/TPM).
//!   Without trusted external monotonic state, a hostile adversary who rolls back or forks a raw
//!   flash image could force two commits at the same `(volume_salt, epoch + 1)` and reuse pads.
//! * **Chaff RNG precondition:** All constructors and commit methods accept a caller-supplied
//!   `rng: &mut dyn FnMut(&mut [u8])`; production callers must pass an OS CSPRNG that fills the
//!   entire buffer with independent uniform bytes.
//! * Intermediate Argon2id buffers are overwritten with zeros before drop (best-effort safe Rust
//!   wipe without `unsafe` or the `zeroize` crate; production deployments should use volatile
//!   zeroization + OS CSPRNG for chaff).

#![deny(warnings)]

use std::fmt;

use crate::hash_kernels::cshake256_xof;

// ============================================================================
// §A. Part A — the scrubber
// ============================================================================

/// `ScrubParams` in Lean: `q` sub-perceptual quantum, `dmax` per-frame slew, `hold` reversal
/// hold-off (frames).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScrubParams {
    pub q: u8,
    pub dmax: u8,
    pub hold: u8,
}

/// `wearable60`: drop 2 LSBs, slew 16/frame, hold-off 12 frames at 60 fps.
pub const WEARABLE60: ScrubParams = ScrubParams { q: 4, dmax: 16, hold: 12 };

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WetwareError {
    /// `ScrubParams.Valid` fails (`0 < q`, `q ∣ dmax`, `0 < hold`).
    InvalidParams(ScrubParams),
    /// The initial level must be a byte on the quantization lattice.
    InitialLevelOffLattice(u8),
    /// Frame length differs from the scrubber's channel count.
    FrameLength { expected: usize, got: usize },
    /// Audio quantum out of range (`k ≤ 15`).
    AudioShift(u32),
    /// Cadence period must be positive.
    ZeroPeriod,
}

impl fmt::Display for WetwareError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidParams(p) => write!(f, "invalid scrub params {p:?}"),
            Self::InitialLevelOffLattice(v) => write!(f, "initial level {v} off the lattice"),
            Self::FrameLength { expected, got } => {
                write!(f, "frame length {got}, scrubber has {expected} channels")
            }
            Self::AudioShift(k) => write!(f, "audio quantum shift {k} > 15"),
            Self::ZeroPeriod => write!(f, "cadence period is zero"),
        }
    }
}

impl std::error::Error for WetwareError {}

impl ScrubParams {
    /// `ScrubParams.Valid`.
    pub fn validate(&self) -> Result<(), WetwareError> {
        if self.q == 0 || self.dmax % self.q != 0 || self.hold == 0 {
            return Err(WetwareError::InvalidParams(*self));
        }
        Ok(())
    }
}

/// `Dir` codes.
pub const DIR_FLAT: u8 = 0;
pub const DIR_UP: u8 = 1;
pub const DIR_DOWN: u8 = 2;

/// `PixState`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PixState {
    pub prev: u8,
    pub dir: u8,
    pub since: u8,
}

impl PixState {
    /// `initState p p0`.
    pub fn init(p: ScrubParams, p0: u8) -> Self {
        PixState { prev: p0, dir: DIR_FLAT, since: p.hold }
    }
}

/// `quant Q x = min x 255 / Q * Q` (a byte is already `≤ 255`).
#[inline(always)]
pub fn quant(q: u8, x: u8) -> u8 {
    ((x as u16 / q as u16) * q as u16) as u8
}

/// `slewClamp`.
#[inline(always)]
pub fn slew_clamp(d: u8, prev: u8, target: u8) -> u8 {
    let (d, p, t) = (d as u16, prev as u16, target as u16);
    if p + d < t {
        (p + d) as u8
    } else if t + d < p {
        (p - d) as u8
    } else {
        target
    }
}

/// `dirOf`.
#[inline(always)]
pub fn dir_of(a: u8, b: u8) -> u8 {
    if a < b {
        DIR_UP
    } else if b < a {
        DIR_DOWN
    } else {
        DIR_FLAT
    }
}

/// `isRev`.
#[inline(always)]
pub fn is_rev(d: u8, s: u8) -> bool {
    s != DIR_FLAT && d != DIR_FLAT && s != d
}

/// `stepCore`: the decision after the slew clamp proposed `y`.
#[inline(always)]
fn step_core(p: ScrubParams, st: PixState, y: u8) -> PixState {
    let s = dir_of(st.prev, y);
    let tick = core::cmp::min(st.since as u16 + 1, p.hold as u16) as u8;
    if is_rev(st.dir, s) {
        if (st.since as u16) + 1 < p.hold as u16 {
            PixState { since: tick, ..st }
        } else {
            PixState { prev: y, dir: s, since: 0 }
        }
    } else if s == DIR_FLAT {
        PixState { since: tick, ..st }
    } else {
        PixState { prev: y, dir: s, since: tick }
    }
}

/// `step p st x`.
#[inline(always)]
pub fn step(p: ScrubParams, st: PixState, x: u8) -> PixState {
    step_core(p, st, slew_clamp(p.dmax, st.prev, quant(p.q, x)))
}

/// `emitted p p0 x n`: the per-frame output for input frames `0..n`.
pub fn scrub_stream(p: ScrubParams, p0: u8, xs: &[u8]) -> Result<Vec<u8>, WetwareError> {
    p.validate()?;
    let mut st = PixState::init(p, p0);
    Ok(xs
        .iter()
        .map(|&x| {
            st = step(p, st, x);
            st.prev
        })
        .collect())
}

/// Per-byte-channel scrubber for whole frames (struct-of-arrays state).
#[derive(Clone, Debug)]
pub struct FrameScrubber {
    p: ScrubParams,
    lut: [u8; 256],
    prev: Vec<u8>,
    dir: Vec<u8>,
    since: Vec<u8>,
}

impl FrameScrubber {
    /// `channels` = bytes per frame of a planar `Y'CbCr(A)` surface (luma first; see module docs —
    /// never interleaved `R`, `G`, `B`). `p0` must be a lattice byte
    /// (`scrubber_output_is_lattice_byte` premise).
    pub fn new(p: ScrubParams, channels: usize, p0: u8) -> Result<Self, WetwareError> {
        p.validate()?;
        if p0 % p.q != 0 {
            return Err(WetwareError::InitialLevelOffLattice(p0));
        }
        let mut lut = [0u8; 256];
        for (x, slot) in lut.iter_mut().enumerate() {
            *slot = quant(p.q, x as u8);
        }
        Ok(FrameScrubber {
            p,
            lut,
            prev: vec![p0; channels],
            dir: vec![DIR_FLAT; channels],
            since: vec![p.hold; channels],
        })
    }

    pub fn channels(&self) -> usize {
        self.prev.len()
    }

    /// Scrub one frame in place: on return `buf` holds what reaches the display.
    pub fn scrub_frame(&mut self, buf: &mut [u8]) -> Result<(), WetwareError> {
        if buf.len() != self.prev.len() {
            return Err(WetwareError::FrameLength { expected: self.prev.len(), got: buf.len() });
        }
        let p = self.p;
        let lut = &self.lut;
        for (((b, pv), dr), sn) in buf
            .iter_mut()
            .zip(self.prev.iter_mut())
            .zip(self.dir.iter_mut())
            .zip(self.since.iter_mut())
        {
            let st = step_core(
                p,
                PixState { prev: *pv, dir: *dr, since: *sn },
                slew_clamp(p.dmax, *pv, lut[*b as usize]),
            );
            *pv = st.prev;
            *dr = st.dir;
            *sn = st.since;
            *b = st.prev;
        }
        Ok(())
    }
}

/// `quantAudio k s` on offset-binary 16-bit samples.
pub fn quant_audio(k: u32, s: u16) -> Result<u16, WetwareError> {
    if k > 15 {
        return Err(WetwareError::AudioShift(k));
    }
    Ok((s >> k) << k)
}

/// Two's-complement PCM view of [`quant_audio`] (`offset = s + 32768`; the lattice commutes
/// with the offset because `2^k ∣ 32768`).
pub fn quant_audio_i16(k: u32, s: i16) -> Result<i16, WetwareError> {
    if k > 15 {
        return Err(WetwareError::AudioShift(k));
    }
    Ok((s >> k) << k)
}

/// `snapRelease P τ = (τ / P + 1) * P`: release at the next vsync boundary.
pub fn snap_release(period: u64, tau: u64) -> Result<u64, WetwareError> {
    if period == 0 {
        return Err(WetwareError::ZeroPeriod);
    }
    Ok((tau / period + 1) * period)
}

// ============================================================================
// §B. Part B — fixed-geometry dual-root duress vault
// ============================================================================

pub const ROOT_BYTES: usize = 32;
pub const NONCE_BYTES: usize = 32;
pub const BODY_BYTES: usize = 32;
pub const TAG_BYTES: usize = 32;
pub const SLOT_BYTES: usize = BODY_BYTES + TAG_BYTES;

const CS_KDF: &[u8] = b"SHE-WETWARE-DURESS/KDF/v1";
const CS_SALT: &[u8] = b"SHE-WETWARE-DURESS/SALT/v1";
const CS_PAD: &[u8] = b"SHE-WETWARE-DURESS/PAD/v1";
const CS_TAG: &[u8] = b"SHE-WETWARE-DURESS/TAG/v1";
const CS_DRBG: &[u8] = b"SHE-WETWARE-DURESS/DRBG/v1";

pub type Root = [u8; ROOT_BYTES];
pub type Body = [u8; BODY_BYTES];
pub type Block = [u8; SLOT_BYTES];

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DuressError {
    SlotOutOfRange { slot: usize, n: usize },
    DuplicateSlot(usize),
    ZeroSlots,
    /// A duress-side write named a slot the given root does not open (it would clobber a
    /// block that may be sovereign).
    NotOwned(usize),
    ImageLength { expected: usize, got: usize },
    /// `BLAKE2b` digest length must be in `1..=64`.
    InvalidBlake2bOutLen(usize),
    /// RFC 9106 `Argon2id` parameter validation failure.
    InvalidArgon2Params(&'static str),
    /// Decoy and sovereign slot maps intersect (`I_decoy ∩ I_sov != ∅`).
    SlotCollision(usize),
    /// Decoy and sovereign roots must be distinct.
    IdenticalRoots,
    /// Requested more slots than available in `[0..n)` or `[0..n) \ I_decoy`.
    InsufficientSlots { requested: usize, available: usize },
    /// Epoch counter reached `u64::MAX`; cannot advance without pad reuse.
    EpochOverflow,
    /// Deserialized image epoch is below the caller's trusted monotonic minimum.
    EpochRollback { got: u64, min_epoch: u64 },
    /// Root opened zero decoy slots during commit (refusing to silently wipe a vault on a
    /// mistyped passphrase).
    NoOwnedSlots,
    /// Sovereign root opened zero slots during `commit_dual` (refusing to silently overwrite an
    /// existing sovereign compartment on a mistyped sovereign passphrase).
    NoOwnedSovereignSlots,
    /// Compartment initialization requires at least one entry.
    EmptyCompartment,
    /// Slot count exceeds the `u32` slot-index or platform byte-length bound.
    TooManySlots(usize),
}

impl fmt::Display for DuressError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SlotOutOfRange { slot, n } => write!(f, "slot {slot} out of range 0..{n}"),
            Self::DuplicateSlot(s) => write!(f, "slot {s} assigned twice"),
            Self::ZeroSlots => write!(f, "vault must have at least one slot"),
            Self::NotOwned(s) => write!(f, "slot {s} does not open under this root"),
            Self::ImageLength { expected, got } => {
                write!(f, "vault image length {got}, expected {expected}")
            }
            Self::InvalidBlake2bOutLen(n) => write!(f, "invalid BLAKE2b output length {n} (must be 1..=64)"),
            Self::InvalidArgon2Params(msg) => write!(f, "invalid Argon2id params: {msg}"),
            Self::SlotCollision(s) => write!(f, "decoy/sovereign slot collision at slot {s}"),
            Self::IdenticalRoots => write!(f, "decoy and sovereign roots must be distinct"),
            Self::InsufficientSlots { requested, available } => {
                write!(f, "requested {requested} slots, only {available} available")
            }
            Self::EpochOverflow => write!(f, "vault epoch counter overflow (u64::MAX)"),
            Self::EpochRollback { got, min_epoch } => {
                write!(f, "vault epoch rollback: got {got}, expected >= {min_epoch}")
            }
            Self::NoOwnedSlots => write!(f, "root opened zero owned decoy slots"),
            Self::NoOwnedSovereignSlots => write!(f, "sovereign root opened zero owned slots"),
            Self::EmptyCompartment => write!(f, "compartment must contain at least one slot"),
            Self::TooManySlots(n) => write!(f, "vault slot count {n} exceeds maximum supported geometry"),
        }
    }
}

impl std::error::Error for DuressError {}

fn xof<const L: usize>(cs: &[u8], parts: &[&[u8]]) -> [u8; L] {
    let mut input = Vec::with_capacity(parts.iter().map(|p| p.len()).sum());
    for p in parts {
        input.extend_from_slice(p);
    }
    let v = cshake256_xof(cs, &input, L);
    let mut out = [0u8; L];
    out.copy_from_slice(&v);
    out
}

/// Passphrase → root. One cSHAKE256 call (NOT memory-hard; see module docs).
pub fn derive_root(passphrase: &[u8], nonce: &[u8; NONCE_BYTES]) -> Root {
    xof::<ROOT_BYTES>(CS_KDF, &[nonce, passphrase])
}

/// Public per-slot salt: distinct for every `(vault nonce, slot)`.
pub fn slot_salt(nonce: &[u8; NONCE_BYTES], i: u32) -> [u8; 32] {
    xof::<32>(CS_SALT, &[nonce, &i.to_le_bytes()])
}

/// `SlotScheme.xof`: the root's pad over the whole `body ‖ tag` block.
pub fn slot_pad(root: &Root, salt: &[u8; 32], i: u32) -> Block {
    xof::<SLOT_BYTES>(CS_PAD, &[root, salt, &i.to_le_bytes()])
}

/// `SlotScheme.mac`.
pub fn slot_tag(root: &Root, salt: &[u8; 32], i: u32, body: &Body) -> [u8; TAG_BYTES] {
    xof::<TAG_BYTES>(CS_TAG, &[root, salt, &i.to_le_bytes(), body])
}

/// `SlotScheme.seal`: `(body ‖ tag) XOR pad`.
pub fn seal_slot(root: &Root, nonce: &[u8; NONCE_BYTES], i: u32, body: &Body) -> Block {
    let salt = slot_salt(nonce, i);
    let pad = slot_pad(root, &salt, i);
    let tag = slot_tag(root, &salt, i, body);
    let mut out = [0u8; SLOT_BYTES];
    for k in 0..BODY_BYTES {
        out[k] = body[k] ^ pad[k];
        out[BODY_BYTES + k] = tag[k] ^ pad[BODY_BYTES + k];
    }
    out
}

/// `SlotScheme.open_`: strip the pad, recompute the tag, compare in constant time.
pub fn open_slot(root: &Root, nonce: &[u8; NONCE_BYTES], i: u32, block: &Block) -> Option<Body> {
    let salt = slot_salt(nonce, i);
    let pad = slot_pad(root, &salt, i);
    let mut body = [0u8; BODY_BYTES];
    for k in 0..BODY_BYTES {
        body[k] = block[k] ^ pad[k];
    }
    let tag = slot_tag(root, &salt, i, &body);
    let mut diff = 0u8;
    for k in 0..TAG_BYTES {
        diff |= (block[BODY_BYTES + k] ^ pad[BODY_BYTES + k]) ^ tag[k];
    }
    if diff == 0 {
        Some(body)
    } else {
        None
    }
}

/// Deterministic cSHAKE256 counter-mode byte source (tests and reproducible vectors only;
/// production chaff must come from the OS CSPRNG).
#[derive(Clone, Debug)]
pub struct XofDrbg {
    seed: [u8; 32],
    ctr: u64,
}

impl XofDrbg {
    pub fn new(seed: &[u8]) -> Self {
        XofDrbg { seed: xof::<32>(CS_DRBG, &[b"seed", seed]), ctr: 0 }
    }

    pub fn fill(&mut self, out: &mut [u8]) {
        let v = cshake256_xof(CS_DRBG, &[&self.seed[..], &self.ctr.to_le_bytes()].concat(), out.len());
        self.ctr += 1;
        out.copy_from_slice(&v);
    }
}

/// One occupant of a vault: which root seals which slot with which body.
#[derive(Clone, Copy, Debug)]
pub struct Occupant<'a> {
    pub root: &'a Root,
    pub slot: usize,
    pub body: Body,
}

/// Fixed-geometry vault image: `nonce ‖ N × 64-byte blocks`. `N` never depends on how many
/// slots are decoy, sovereign or chaff.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DuressVault {
    pub nonce: [u8; NONCE_BYTES],
    pub slots: Vec<Block>,
}

impl DuressVault {
    /// Fill all `n` slots with chaff, then seal each occupant into its slot.
    pub fn create(
        nonce: [u8; NONCE_BYTES],
        n: usize,
        occupants: &[Occupant<'_>],
        chaff: &mut dyn FnMut(&mut [u8]),
    ) -> Result<Self, DuressError> {
        if n == 0 {
            return Err(DuressError::ZeroSlots);
        }
        let mut used = vec![false; n];
        for o in occupants {
            if o.slot >= n {
                return Err(DuressError::SlotOutOfRange { slot: o.slot, n });
            }
            if used[o.slot] {
                return Err(DuressError::DuplicateSlot(o.slot));
            }
            used[o.slot] = true;
        }
        let mut slots = vec![[0u8; SLOT_BYTES]; n];
        for s in slots.iter_mut() {
            chaff(s);
        }
        for o in occupants {
            slots[o.slot] = seal_slot(o.root, &nonce, o.slot as u32, &o.body);
        }
        Ok(DuressVault { nonce, slots })
    }

    /// Try every slot under `root` (no early exit, no slot table): the slots it opens.
    pub fn unlock(&self, root: &Root) -> Vec<(usize, Body)> {
        let mut out = Vec::new();
        for (i, b) in self.slots.iter().enumerate() {
            if let Some(body) = open_slot(root, &self.nonce, i as u32, b) {
                out.push((i, body));
            }
        }
        out
    }

    /// Duress-side write: only a slot that already opens under `root` may be rewritten.
    pub fn rewrite_owned(&mut self, root: &Root, slot: usize, body: &Body) -> Result<(), DuressError> {
        let n = self.slots.len();
        if slot >= n {
            return Err(DuressError::SlotOutOfRange { slot, n });
        }
        if open_slot(root, &self.nonce, slot as u32, &self.slots[slot]).is_none() {
            return Err(DuressError::NotOwned(slot));
        }
        self.slots[slot] = seal_slot(root, &self.nonce, slot as u32, body);
        Ok(())
    }

    pub fn image_len(n: usize) -> usize {
        NONCE_BYTES + n * SLOT_BYTES
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(Self::image_len(self.slots.len()));
        v.extend_from_slice(&self.nonce);
        for s in &self.slots {
            v.extend_from_slice(s);
        }
        v
    }

    pub fn from_bytes(bytes: &[u8], n: usize) -> Result<Self, DuressError> {
        let expected = Self::image_len(n);
        if bytes.len() != expected {
            return Err(DuressError::ImageLength { expected, got: bytes.len() });
        }
        let mut nonce = [0u8; NONCE_BYTES];
        nonce.copy_from_slice(&bytes[..NONCE_BYTES]);
        let slots = bytes[NONCE_BYTES..]
            .chunks_exact(SLOT_BYTES)
            .map(|c| {
                let mut b = [0u8; SLOT_BYTES];
                b.copy_from_slice(c);
                b
            })
            .collect();
        Ok(DuressVault { nonce, slots })
    }
}

// ============================================================================
// §C. Part C — Pure-Rust RFC 7693 BLAKE2b & RFC 9106 Argon2id (v = 0x13)
// ============================================================================

pub const ARGON2_VERSION: u32 = 0x13;
pub const ARGON2_TYPE_ID: u32 = 2;
pub const ARGON2_BLOCK_BYTES: usize = 1024;
pub const ARGON2_QWORDS_IN_BLOCK: usize = 128;
pub const ARGON2_SYNC_POINTS: usize = 4;
pub const ARGON2_MIN_SALT_BYTES: usize = 8;
pub const ARGON2_MIN_TAG_BYTES: usize = 4;

const BLAKE2B_IV: [u64; 8] = [
    0x6a09_e667_f3bc_c908,
    0xbb67_ae85_84ca_a73b,
    0x3c6e_f372_fe94_f82b,
    0xa54f_f53a_5f1d_36f1,
    0x510e_527f_ade6_82d1,
    0x9b05_688c_2b3e_6c1f,
    0x1f83_d9ab_fb41_bd6b,
    0x5be0_cd19_137e_2179,
];

const BLAKE2B_SIGMA: [[usize; 16]; 10] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

#[inline(always)]
fn blake2b_g(v: &mut [u64; 16], a: usize, b: usize, c: usize, d: usize, x: u64, y: u64) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = (v[d] ^ v[a]).rotate_right(32);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(24);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(63);
}

fn blake2b_compress(h: &mut [u64; 8], block: &[u8; 128], t: u128, last: bool) {
    let mut m = [0u64; 16];
    for i in 0..16 {
        let off = i * 8;
        m[i] = u64::from_le_bytes([
            block[off],
            block[off + 1],
            block[off + 2],
            block[off + 3],
            block[off + 4],
            block[off + 5],
            block[off + 6],
            block[off + 7],
        ]);
    }
    let mut v = [0u64; 16];
    v[..8].copy_from_slice(h);
    v[8..].copy_from_slice(&BLAKE2B_IV);
    v[12] ^= t as u64;
    v[13] ^= (t >> 64) as u64;
    if last {
        v[14] = !v[14];
    }
    for r in 0..12 {
        let s = &BLAKE2B_SIGMA[r % 10];
        blake2b_g(&mut v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
        blake2b_g(&mut v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
        blake2b_g(&mut v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
        blake2b_g(&mut v, 3, 7, 11, 15, m[s[6]], m[s[7]]);
        blake2b_g(&mut v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
        blake2b_g(&mut v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
        blake2b_g(&mut v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
        blake2b_g(&mut v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
    }
    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
}

/// Unkeyed RFC 7693 `BLAKE2b` with `out_len` in `1..=64` bytes.
pub fn blake2b(out_len: usize, input: &[u8]) -> Result<Vec<u8>, DuressError> {
    if out_len == 0 || out_len > 64 {
        return Err(DuressError::InvalidBlake2bOutLen(out_len));
    }
    let mut h = BLAKE2B_IV;
    h[0] ^= 0x0101_0000u64 ^ (out_len as u64);

    let mut offset = 0usize;
    let mut t = 0u128;
    while input.len().saturating_sub(offset) > 128 {
        let mut block = [0u8; 128];
        block.copy_from_slice(&input[offset..offset + 128]);
        offset += 128;
        t += 128;
        blake2b_compress(&mut h, &block, t, false);
    }
    let rem = input.len() - offset;
    let mut last_block = [0u8; 128];
    last_block[..rem].copy_from_slice(&input[offset..]);
    t += rem as u128;
    blake2b_compress(&mut h, &last_block, t, true);

    let mut full = [0u8; 64];
    for (i, word) in h.iter().enumerate() {
        full[i * 8..(i + 1) * 8].copy_from_slice(&word.to_le_bytes());
    }
    Ok(full[..out_len].to_vec())
}

/// RFC 9106 §3.3 variable-length hash `H'(out_len, input)`.
pub fn blake2b_long(out_len: usize, input: &[u8]) -> Result<Vec<u8>, DuressError> {
    if out_len == 0 || out_len > u32::MAX as usize {
        return Err(DuressError::InvalidArgon2Params("H' output length must be in 1..=2^32-1"));
    }
    let mut msg = Vec::with_capacity(4 + input.len());
    msg.extend_from_slice(&(out_len as u32).to_le_bytes());
    msg.extend_from_slice(input);

    if out_len <= 64 {
        return blake2b(out_len, &msg);
    }
    let r = out_len.div_ceil(32) - 2;
    let mut out = Vec::with_capacity(out_len);
    let mut v = blake2b(64, &msg)?;
    out.extend_from_slice(&v[..32]);
    for _ in 2..=r {
        v = blake2b(64, &v)?;
        out.extend_from_slice(&v[..32]);
    }
    let rem = out_len - 32 * r;
    let v_last = blake2b(rem, &v)?;
    out.extend_from_slice(&v_last);
    Ok(out)
}

#[inline(always)]
fn f_blamka(x: u64, y: u64) -> u64 {
    let xl = x as u32 as u64;
    let yl = y as u32 as u64;
    x.wrapping_add(y).wrapping_add(2u64.wrapping_mul(xl.wrapping_mul(yl)))
}

#[inline(always)]
fn gb(a: &mut u64, b: &mut u64, c: &mut u64, d: &mut u64) {
    *a = f_blamka(*a, *b);
    *d = (*d ^ *a).rotate_right(32);
    *c = f_blamka(*c, *d);
    *b = (*b ^ *c).rotate_right(24);
    *a = f_blamka(*a, *b);
    *d = (*d ^ *a).rotate_right(16);
    *c = f_blamka(*c, *d);
    *b = (*b ^ *c).rotate_right(63);
}

#[inline(always)]
fn permute_p(v: &mut [u64; 16]) {
    let [mut v0, mut v1, mut v2, mut v3, mut v4, mut v5, mut v6, mut v7, mut v8, mut v9, mut v10, mut v11, mut v12, mut v13, mut v14, mut v15] =
        *v;
    gb(&mut v0, &mut v4, &mut v8, &mut v12);
    gb(&mut v1, &mut v5, &mut v9, &mut v13);
    gb(&mut v2, &mut v6, &mut v10, &mut v14);
    gb(&mut v3, &mut v7, &mut v11, &mut v15);
    gb(&mut v0, &mut v5, &mut v10, &mut v15);
    gb(&mut v1, &mut v6, &mut v11, &mut v12);
    gb(&mut v2, &mut v7, &mut v8, &mut v13);
    gb(&mut v3, &mut v4, &mut v9, &mut v14);
    *v = [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15];
}

/// RFC 9106 §3.5 `G(X, Y)` compression function over 1,024-byte (`128 × u64`) blocks.
fn argon2_compress_g(x: &[u64; ARGON2_QWORDS_IN_BLOCK], y: &[u64; ARGON2_QWORDS_IN_BLOCK]) -> [u64; ARGON2_QWORDS_IN_BLOCK] {
    let mut r = [0u64; ARGON2_QWORDS_IN_BLOCK];
    for i in 0..ARGON2_QWORDS_IN_BLOCK {
        r[i] = x[i] ^ y[i];
    }
    let mut z = r;
    // Row-wise P (8 rows of 16 u64 words).
    for row in 0..8 {
        let base = row * 16;
        let mut slice = [0u64; 16];
        slice.copy_from_slice(&z[base..base + 16]);
        permute_p(&mut slice);
        z[base..base + 16].copy_from_slice(&slice);
    }
    // Column-wise P (8 columns of 8 16-byte register pairs).
    for col in 0..8 {
        let mut slice = [0u64; 16];
        for row in 0..8 {
            let idx = row * 16 + col * 2;
            slice[row * 2] = z[idx];
            slice[row * 2 + 1] = z[idx + 1];
        }
        permute_p(&mut slice);
        for row in 0..8 {
            let idx = row * 16 + col * 2;
            z[idx] = slice[row * 2];
            z[idx + 1] = slice[row * 2 + 1];
        }
    }
    for i in 0..ARGON2_QWORDS_IN_BLOCK {
        z[i] ^= r[i];
    }
    z
}

fn next_argon2_addresses(
    address_block: &mut [u64; ARGON2_QWORDS_IN_BLOCK],
    input_block: &mut [u64; ARGON2_QWORDS_IN_BLOCK],
) {
    const ZERO: [u64; ARGON2_QWORDS_IN_BLOCK] = [0u64; ARGON2_QWORDS_IN_BLOCK];
    input_block[6] = input_block[6].wrapping_add(1);
    let tmp = argon2_compress_g(&ZERO, input_block);
    *address_block = argon2_compress_g(&ZERO, &tmp);
}

fn block_from_bytes(bytes: &[u8]) -> [u64; ARGON2_QWORDS_IN_BLOCK] {
    let mut blk = [0u64; ARGON2_QWORDS_IN_BLOCK];
    for i in 0..ARGON2_QWORDS_IN_BLOCK {
        let off = i * 8;
        blk[i] = u64::from_le_bytes([
            bytes[off],
            bytes[off + 1],
            bytes[off + 2],
            bytes[off + 3],
            bytes[off + 4],
            bytes[off + 5],
            bytes[off + 6],
            bytes[off + 7],
        ]);
    }
    blk
}

/// RFC 9106 `Argon2id` parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Argon2idParams {
    /// Memory cost in KiB (`>= 8 * p_lanes`).
    pub m_kib: u32,
    /// Number of passes / iterations (`>= 1`).
    pub t_passes: u32,
    /// Degree of parallelism / lanes (`1..2^24`).
    pub p_lanes: u32,
}

/// RFC 9106 §4 second recommended parameter set for memory-constrained / wearable environments
/// (`64 MiB`, `3` passes, `4` lanes).
pub const ARGON2ID_RFC9106_LOW_MEM: Argon2idParams =
    Argon2idParams { m_kib: 65_536, t_passes: 3, p_lanes: 4 };

/// Default wearable vault KDF profile (RFC 9106 §4 64 MiB `Argon2id`).
pub const ARGON2ID_WEARABLE_DEFAULT: Argon2idParams = ARGON2ID_RFC9106_LOW_MEM;

/// Fast profile for unit-test fuzz loops only (NOT for production passphrases).
pub const ARGON2ID_TEST_FAST: Argon2idParams =
    Argon2idParams { m_kib: 256, t_passes: 2, p_lanes: 1 };

impl Argon2idParams {
    pub fn validate(&self) -> Result<(), DuressError> {
        if self.p_lanes == 0 || self.p_lanes >= (1 << 24) {
            return Err(DuressError::InvalidArgon2Params("p_lanes must be in 1..2^24"));
        }
        if self.t_passes == 0 {
            return Err(DuressError::InvalidArgon2Params("t_passes must be >= 1"));
        }
        let min_m = (self.p_lanes as u64) * 8;
        if (self.m_kib as u64) < min_m {
            return Err(DuressError::InvalidArgon2Params("m_kib must be >= 8 * p_lanes"));
        }
        Ok(())
    }
}

/// Pure-Rust RFC 9106 `Argon2id` (`v = 0x13`, `y = 2`).
///
/// Exact RFC 9106 §3.4.1 hybrid indexing rule:
/// * pass `0`, slices `0` and `1`: `Argon2i` data-independent addressing;
/// * pass `0`, slices `2` and `3`, and all passes `>= 1`: `Argon2d` data-dependent addressing.
///
/// Salt policy: enforces `salt.len() >= 8` (matching the PHC reference implementation
/// `ARGON2_MIN_SALT_LENGTH = 8` and RFC 9106 §4 guidance; stricter than RFC 9106 §3.1's
/// 0-byte syntactic lower bound for password-hashing safety).
pub fn argon2id_raw(
    password: &[u8],
    salt: &[u8],
    secret: &[u8],
    ad: &[u8],
    params: Argon2idParams,
    tag_len: usize,
) -> Result<Vec<u8>, DuressError> {
    params.validate()?;
    if salt.len() < ARGON2_MIN_SALT_BYTES {
        return Err(DuressError::InvalidArgon2Params("salt must be >= 8 bytes"));
    }
    if tag_len < ARGON2_MIN_TAG_BYTES || tag_len > u32::MAX as usize {
        return Err(DuressError::InvalidArgon2Params("tag_len must be in 4..=2^32-1"));
    }
    if password.len() > u32::MAX as usize
        || salt.len() > u32::MAX as usize
        || secret.len() > u32::MAX as usize
        || ad.len() > u32::MAX as usize
    {
        return Err(DuressError::InvalidArgon2Params("input length exceeds 2^32-1"));
    }

    let p = params.p_lanes as usize;
    let m_kib = params.m_kib as usize;
    let t = params.t_passes as usize;
    let four_p = 4usize
        .checked_mul(p)
        .ok_or(DuressError::InvalidArgon2Params("4 * p_lanes overflow"))?;
    let m_prime = four_p * (m_kib / four_p);
    let q = m_prime / p;
    let seg_len = q / ARGON2_SYNC_POINTS;

    // Checked capacity for H_0 input and memory matrix before allocation.
    let h0_cap = 40usize
        .checked_add(password.len())
        .and_then(|v| v.checked_add(salt.len()))
        .and_then(|v| v.checked_add(secret.len()))
        .and_then(|v| v.checked_add(ad.len()))
        .ok_or(DuressError::InvalidArgon2Params("H_0 buffer length overflow"))?;
    if m_prime.checked_mul(ARGON2_BLOCK_BYTES).is_none() {
        return Err(DuressError::InvalidArgon2Params("memory matrix size exceeds usize"));
    }

    // Step 1: H_0 = BLAKE2b-512(...)
    let mut h0_in = Vec::new();
    h0_in
        .try_reserve_exact(h0_cap)
        .map_err(|_| DuressError::InvalidArgon2Params("H_0 allocation failed"))?;
    h0_in.extend_from_slice(&params.p_lanes.to_le_bytes());
    h0_in.extend_from_slice(&(tag_len as u32).to_le_bytes());
    h0_in.extend_from_slice(&params.m_kib.to_le_bytes());
    h0_in.extend_from_slice(&params.t_passes.to_le_bytes());
    h0_in.extend_from_slice(&ARGON2_VERSION.to_le_bytes());
    h0_in.extend_from_slice(&ARGON2_TYPE_ID.to_le_bytes());
    h0_in.extend_from_slice(&(password.len() as u32).to_le_bytes());
    h0_in.extend_from_slice(password);
    h0_in.extend_from_slice(&(salt.len() as u32).to_le_bytes());
    h0_in.extend_from_slice(salt);
    h0_in.extend_from_slice(&(secret.len() as u32).to_le_bytes());
    h0_in.extend_from_slice(secret);
    h0_in.extend_from_slice(&(ad.len() as u32).to_le_bytes());
    h0_in.extend_from_slice(ad);
    let mut h0 = blake2b(64, &h0_in)?;
    h0_in.fill(0);
    core::hint::black_box(&h0_in);

    // Step 2: Allocate memory matrix B[lane][col] (flattened as lane * q + col) and fill cols 0, 1.
    let mut mem: Vec<[u64; ARGON2_QWORDS_IN_BLOCK]> = Vec::new();
    mem.try_reserve_exact(m_prime)
        .map_err(|_| DuressError::InvalidArgon2Params("memory matrix allocation failed"))?;
    mem.resize(m_prime, [0u64; ARGON2_QWORDS_IN_BLOCK]);
    let mut seed_buf = [0u8; 72];
    seed_buf[..64].copy_from_slice(&h0);
    for lane in 0..p {
        seed_buf[68..72].copy_from_slice(&(lane as u32).to_le_bytes());
        seed_buf[64..68].copy_from_slice(&0u32.to_le_bytes());
        let b0 = blake2b_long(ARGON2_BLOCK_BYTES, &seed_buf)?;
        mem[lane * q] = block_from_bytes(&b0);

        seed_buf[64..68].copy_from_slice(&1u32.to_le_bytes());
        let b1 = blake2b_long(ARGON2_BLOCK_BYTES, &seed_buf)?;
        mem[lane * q + 1] = block_from_bytes(&b1);
    }
    seed_buf.fill(0);
    h0.fill(0);
    core::hint::black_box((&seed_buf, &h0));

    // Step 3: Fill segments across passes, sync slices, and lanes.
    for pass in 0..t {
        for slice in 0..ARGON2_SYNC_POINTS {
            let data_independent = pass == 0 && slice < 2;
            for lane in 0..p {
                let mut address_block = [0u64; ARGON2_QWORDS_IN_BLOCK];
                let mut input_block = [0u64; ARGON2_QWORDS_IN_BLOCK];
                if data_independent {
                    input_block[0] = pass as u64;
                    input_block[1] = lane as u64;
                    input_block[2] = slice as u64;
                    input_block[3] = m_prime as u64;
                    input_block[4] = t as u64;
                    input_block[5] = ARGON2_TYPE_ID as u64;
                }
                let starting_index = if pass == 0 && slice == 0 {
                    if data_independent {
                        next_argon2_addresses(&mut address_block, &mut input_block);
                    }
                    2
                } else {
                    0
                };
                for index in starting_index..seg_len {
                    let curr_col = slice * seg_len + index;
                    let prev_col = if curr_col == 0 { q - 1 } else { curr_col - 1 };
                    let curr_idx = lane * q + curr_col;
                    let prev_idx = lane * q + prev_col;

                    let pseudo_rand = if data_independent {
                        if index % ARGON2_QWORDS_IN_BLOCK == 0 {
                            next_argon2_addresses(&mut address_block, &mut input_block);
                        }
                        address_block[index % ARGON2_QWORDS_IN_BLOCK]
                    } else {
                        mem[prev_idx][0]
                    };

                    let j1 = (pseudo_rand & 0xFFFF_FFFF) as u64;
                    let j2 = (pseudo_rand >> 32) as usize;
                    let ref_lane = if pass == 0 && slice == 0 { lane } else { j2 % p };
                    let same_lane = ref_lane == lane;

                    let ref_area_size = if pass == 0 {
                        if slice == 0 {
                            index - 1
                        } else if same_lane {
                            slice * seg_len + index - 1
                        } else {
                            slice * seg_len - usize::from(index == 0)
                        }
                    } else if same_lane {
                        q - seg_len + index - 1
                    } else {
                        q - seg_len - usize::from(index == 0)
                    };

                    let x = (j1 * j1) >> 32;
                    let y = ((ref_area_size as u64) * x) >> 32;
                    let rel_pos = (ref_area_size as u64) - 1 - y;
                    let start_pos = if pass == 0 || slice == 3 { 0 } else { (slice + 1) * seg_len };
                    let ref_col = (start_pos + rel_pos as usize) % q;
                    let ref_idx = ref_lane * q + ref_col;

                    let next_blk = argon2_compress_g(&mem[prev_idx], &mem[ref_idx]);
                    if pass == 0 {
                        mem[curr_idx] = next_blk;
                    } else {
                        for w in 0..ARGON2_QWORDS_IN_BLOCK {
                            mem[curr_idx][w] ^= next_blk[w];
                        }
                    }
                }
            }
        }
    }

    // Step 4: Finalization — XOR last column of all lanes and hash with H'.
    let mut c_blk = mem[q - 1];
    for lane in 1..p {
        let last = &mem[lane * q + (q - 1)];
        for w in 0..ARGON2_QWORDS_IN_BLOCK {
            c_blk[w] ^= last[w];
        }
    }
    let mut c_bytes = [0u8; ARGON2_BLOCK_BYTES];
    for (i, word) in c_blk.iter().enumerate() {
        c_bytes[i * 8..(i + 1) * 8].copy_from_slice(&word.to_le_bytes());
    }
    let tag = blake2b_long(tag_len, &c_bytes)?;

    // Best-effort safe zeroization of sensitive state.
    for blk in mem.iter_mut() {
        blk.fill(0);
    }
    c_blk.fill(0);
    c_bytes.fill(0);
    core::hint::black_box((&mem, &c_blk, &c_bytes));

    Ok(tag)
}

// ============================================================================
// §D. Part D — Multi-Snapshot Write-All Oblivious Duress Vault
// ============================================================================

pub const VOLUME_SALT_BYTES: usize = 32;
pub const MS_HEADER_BYTES: usize = 8 + VOLUME_SALT_BYTES;

const CS_ARGON2ID_AD: &[u8] = b"SHE-WETWARE-DURESS/ARGON2ID-ROOT/v2";
const CS_MS_SALT: &[u8] = b"SHE-WETWARE-DURESS/MS-SALT/v2";
const CS_MS_PAD: &[u8] = b"SHE-WETWARE-DURESS/MS-PAD/v2";
const CS_MS_TAG: &[u8] = b"SHE-WETWARE-DURESS/MS-TAG/v2";
const CS_MS_DECOY_MAP: &[u8] = b"SHE-WETWARE-DURESS/MS-DECOY-MAP/v2";
const CS_MS_SOV_MAP: &[u8] = b"SHE-WETWARE-DURESS/MS-SOV-MAP/v2";

/// Derive a 32-byte vault root from `(passphrase, volume_salt)` using RFC 9106 `Argon2id`.
pub fn derive_vault_root_argon2id(
    passphrase: &[u8],
    volume_salt: &[u8; VOLUME_SALT_BYTES],
    params: Argon2idParams,
) -> Result<Root, DuressError> {
    let tag = argon2id_raw(passphrase, volume_salt, b"", CS_ARGON2ID_AD, params, ROOT_BYTES)?;
    let mut root = [0u8; ROOT_BYTES];
    root.copy_from_slice(&tag);
    Ok(root)
}

/// Derive a 32-byte vault root under [`ARGON2ID_WEARABLE_DEFAULT`] (`64 MiB`, `t=3`, `p=4`).
pub fn derive_vault_root_default(
    passphrase: &[u8],
    volume_salt: &[u8; VOLUME_SALT_BYTES],
) -> Result<Root, DuressError> {
    derive_vault_root_argon2id(passphrase, volume_salt, ARGON2ID_WEARABLE_DEFAULT)
}

/// Public per-(epoch, slot) salt for v2 multi-snapshot volumes.
pub fn epoch_slot_salt(volume_salt: &[u8; VOLUME_SALT_BYTES], epoch: u64, i: u32) -> [u8; 32] {
    xof::<32>(CS_MS_SALT, &[volume_salt, &epoch.to_le_bytes(), &i.to_le_bytes()])
}

/// Root- and epoch-bound 64-byte pad over `body ‖ tag`.
pub fn epoch_slot_pad(root: &Root, salt: &[u8; 32], epoch: u64, i: u32) -> Block {
    xof::<SLOT_BYTES>(CS_MS_PAD, &[root, salt, &epoch.to_le_bytes(), &i.to_le_bytes()])
}

/// Root- and epoch-bound 32-byte authentication tag.
pub fn epoch_slot_tag(root: &Root, salt: &[u8; 32], epoch: u64, i: u32, body: &Body) -> [u8; TAG_BYTES] {
    xof::<TAG_BYTES>(CS_MS_TAG, &[root, salt, &epoch.to_le_bytes(), &i.to_le_bytes(), body])
}

/// Epoch-bound `SlotScheme.seal`: `(body ‖ tag_e) XOR pad_e`.
pub fn seal_slot_epoch(
    root: &Root,
    volume_salt: &[u8; VOLUME_SALT_BYTES],
    epoch: u64,
    i: u32,
    body: &Body,
) -> Block {
    let salt = epoch_slot_salt(volume_salt, epoch, i);
    let pad = epoch_slot_pad(root, &salt, epoch, i);
    let tag = epoch_slot_tag(root, &salt, epoch, i, body);
    let mut out = [0u8; SLOT_BYTES];
    for k in 0..BODY_BYTES {
        out[k] = body[k] ^ pad[k];
        out[BODY_BYTES + k] = tag[k] ^ pad[BODY_BYTES + k];
    }
    out
}

/// Epoch-bound `SlotScheme.open_` with constant-time tag verification.
pub fn open_slot_epoch(
    root: &Root,
    volume_salt: &[u8; VOLUME_SALT_BYTES],
    epoch: u64,
    i: u32,
    block: &Block,
) -> Option<Body> {
    let salt = epoch_slot_salt(volume_salt, epoch, i);
    let pad = epoch_slot_pad(root, &salt, epoch, i);
    let mut body = [0u8; BODY_BYTES];
    for k in 0..BODY_BYTES {
        body[k] = block[k] ^ pad[k];
    }
    let tag = epoch_slot_tag(root, &salt, epoch, i, &body);
    let mut diff = 0u8;
    for k in 0..TAG_BYTES {
        diff |= (block[BODY_BYTES + k] ^ pad[BODY_BYTES + k]) ^ tag[k];
    }
    if diff == 0 {
        Some(body)
    } else {
        None
    }
}

/// Unbiased keyed Fisher–Yates sampling of `k` elements from `pool` via cSHAKE256 rejection sampling.
fn sample_slots_keyed(
    cs: &[u8],
    root: &Root,
    volume_salt: &[u8; VOLUME_SALT_BYTES],
    n: usize,
    mut pool: Vec<usize>,
    k: usize,
) -> Result<Vec<usize>, DuressError> {
    if k > pool.len() {
        return Err(DuressError::InsufficientSlots { requested: k, available: pool.len() });
    }
    let seed = xof::<32>(cs, &[root, volume_salt, &(n as u64).to_le_bytes()]);
    let mut ctr = 0u64;
    let mut buf = [0u8; 64];
    let mut pos = 64usize;
    let mut next_u64 = || -> u64 {
        if pos >= 64 {
            buf = xof::<64>(cs, &[&seed, &ctr.to_le_bytes()]);
            ctr += 1;
            pos = 0;
        }
        let w = u64::from_le_bytes([
            buf[pos],
            buf[pos + 1],
            buf[pos + 2],
            buf[pos + 3],
            buf[pos + 4],
            buf[pos + 5],
            buf[pos + 6],
            buf[pos + 7],
        ]);
        pos += 8;
        w
    };
    let len = pool.len();
    for step in 0..k {
        let rem = (len - step) as u64;
        // Exact unbiased rejection threshold: (2^64 - rem) % rem.
        let zone = (u64::MAX - rem + 1) % rem;
        let offset = loop {
            let r = next_u64();
            if r >= zone {
                break (r % rem) as usize;
            }
        };
        pool.swap(step, step + offset);
    }
    let mut chosen = pool[..k].to_vec();
    chosen.sort_unstable();
    Ok(chosen)
}

fn validate_slot_count(n: usize) -> Result<usize, DuressError> {
    if n == 0 {
        return Err(DuressError::ZeroSlots);
    }
    if n > u32::MAX as usize {
        return Err(DuressError::TooManySlots(n));
    }
    MultiSnapshotDuressVault::checked_image_len(n).ok_or(DuressError::TooManySlots(n))
}

/// Derive a deterministic decoy slot map `I_decoy ⊂ {0..n-1}` from `(root_decoy, volume_salt)`.
pub fn derive_decoy_slots(
    root_decoy: &Root,
    volume_salt: &[u8; VOLUME_SALT_BYTES],
    n: usize,
    k_decoy: usize,
) -> Result<Vec<usize>, DuressError> {
    validate_slot_count(n)?;
    sample_slots_keyed(CS_MS_DECOY_MAP, root_decoy, volume_salt, n, (0..n).collect(), k_decoy)
}

/// Derive a deterministic sovereign slot map `I_sov ⊂ {0..n-1} \ I_decoy`, guaranteed disjoint
/// from `decoy_slots` by construction.
pub fn derive_sovereign_slots_disjoint(
    root_sov: &Root,
    volume_salt: &[u8; VOLUME_SALT_BYTES],
    n: usize,
    decoy_slots: &[usize],
    k_sov: usize,
) -> Result<Vec<usize>, DuressError> {
    validate_slot_count(n)?;
    let mut is_decoy = vec![false; n];
    for &s in decoy_slots {
        if s >= n {
            return Err(DuressError::SlotOutOfRange { slot: s, n });
        }
        if is_decoy[s] {
            return Err(DuressError::DuplicateSlot(s));
        }
        is_decoy[s] = true;
    }
    let available: Vec<usize> = (0..n).filter(|&i| !is_decoy[i]).collect();
    sample_slots_keyed(CS_MS_SOV_MAP, root_sov, volume_salt, n, available, k_sov)
}

/// Multi-snapshot write-all oblivious duress vault:
/// fixed header `(epoch: u64, volume_salt: [u8; 32])` + `N × 64`-byte blocks.
///
/// Every commit (`commit_decoy_only`, `init_sovereign_compartment`, or `commit_dual`) increments
/// `epoch = epoch + 1` and rewrites ALL `N` blocks, eliminating the v1 2-snapshot diff side
/// channel. Callers MUST pass an OS CSPRNG for `rng` in production.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MultiSnapshotDuressVault {
    pub epoch: u64,
    pub volume_salt: [u8; VOLUME_SALT_BYTES],
    pub slots: Vec<Block>,
}

impl MultiSnapshotDuressVault {
    /// Create an epoch-0 decoy-only vault: requires at least one decoy entry, fills all `n` slots
    /// with CSPRNG chaff (`rng`), then seals `decoy_entries` under `(root_decoy, volume_salt, 0)`.
    pub fn create_decoy_only(
        volume_salt: [u8; VOLUME_SALT_BYTES],
        n: usize,
        root_decoy: &Root,
        decoy_entries: &[(usize, Body)],
        rng: &mut dyn FnMut(&mut [u8]),
    ) -> Result<Self, DuressError> {
        validate_slot_count(n)?;
        if decoy_entries.is_empty() {
            return Err(DuressError::EmptyCompartment);
        }
        let mut used = vec![false; n];
        for &(slot, _) in decoy_entries {
            if slot >= n {
                return Err(DuressError::SlotOutOfRange { slot, n });
            }
            if used[slot] {
                return Err(DuressError::DuplicateSlot(slot));
            }
            used[slot] = true;
        }
        let mut slots = vec![[0u8; SLOT_BYTES]; n];
        for blk in slots.iter_mut() {
            rng(blk);
        }
        for &(slot, body) in decoy_entries {
            slots[slot] = seal_slot_epoch(root_decoy, &volume_salt, 0, slot as u32, &body);
        }
        Ok(MultiSnapshotDuressVault { epoch: 0, volume_salt, slots })
    }

    /// Create an epoch-0 dual-compartment vault with explicitly disjoint non-empty `I_decoy` and
    /// `I_sov`. Rejects identical roots (`IdenticalRoots`), empty compartments
    /// (`EmptyCompartment`), and any slot overlap (`SlotCollision`).
    pub fn create_dual(
        volume_salt: [u8; VOLUME_SALT_BYTES],
        n: usize,
        root_decoy: &Root,
        decoy_entries: &[(usize, Body)],
        root_sov: &Root,
        sov_entries: &[(usize, Body)],
        rng: &mut dyn FnMut(&mut [u8]),
    ) -> Result<Self, DuressError> {
        validate_slot_count(n)?;
        if root_decoy == root_sov {
            return Err(DuressError::IdenticalRoots);
        }
        if decoy_entries.is_empty() || sov_entries.is_empty() {
            return Err(DuressError::EmptyCompartment);
        }
        let mut is_decoy = vec![false; n];
        for &(slot, _) in decoy_entries {
            if slot >= n {
                return Err(DuressError::SlotOutOfRange { slot, n });
            }
            if is_decoy[slot] {
                return Err(DuressError::DuplicateSlot(slot));
            }
            is_decoy[slot] = true;
        }
        let mut is_sov = vec![false; n];
        for &(slot, _) in sov_entries {
            if slot >= n {
                return Err(DuressError::SlotOutOfRange { slot, n });
            }
            if is_decoy[slot] {
                return Err(DuressError::SlotCollision(slot));
            }
            if is_sov[slot] {
                return Err(DuressError::DuplicateSlot(slot));
            }
            is_sov[slot] = true;
        }
        let mut slots = vec![[0u8; SLOT_BYTES]; n];
        for blk in slots.iter_mut() {
            rng(blk);
        }
        for &(slot, body) in decoy_entries {
            slots[slot] = seal_slot_epoch(root_decoy, &volume_salt, 0, slot as u32, &body);
        }
        for &(slot, body) in sov_entries {
            slots[slot] = seal_slot_epoch(root_sov, &volume_salt, 0, slot as u32, &body);
        }
        Ok(MultiSnapshotDuressVault { epoch: 0, volume_salt, slots })
    }

    /// Scan all `N` slots at the current `epoch` (no slot table, no early exit).
    pub fn unlock(&self, root: &Root) -> Vec<(usize, Body)> {
        let mut out = Vec::new();
        for (i, blk) in self.slots.iter().enumerate() {
            if let Some(body) = open_slot_epoch(root, &self.volume_salt, self.epoch, i as u32, blk) {
                out.push((i, body));
            }
        }
        out
    }

    /// Write-all decoy-only commit: increments `epoch`, updates owned decoy slots under
    /// `(root_decoy, epoch + 1)`, and overwrites EVERY non-decoy slot `i ∉ I_decoy` with fresh
    /// CSPRNG chaff.
    ///
    /// **Availability note:** Because `root_sov` is not provided, any unmounted sovereign slots
    /// in `[0..N) \ I_decoy` are intentionally overwritten (panic-shredded) in the new image so
    /// that the snapshot sequence remains multi-snapshot indistinguishable under coercion.
    pub fn commit_decoy_only(
        &mut self,
        root_decoy: &Root,
        decoy_writes: &[(usize, Body)],
        rng: &mut dyn FnMut(&mut [u8]),
    ) -> Result<(), DuressError> {
        let next_epoch = self.epoch.checked_add(1).ok_or(DuressError::EpochOverflow)?;
        let n = self.slots.len();
        let mut decoy_map: Vec<Option<Body>> = vec![None; n];
        let mut owned_count = 0usize;
        for (i, blk) in self.slots.iter().enumerate() {
            if let Some(body) = open_slot_epoch(root_decoy, &self.volume_salt, self.epoch, i as u32, blk) {
                decoy_map[i] = Some(body);
                owned_count += 1;
            }
        }
        if owned_count == 0 {
            return Err(DuressError::NoOwnedSlots);
        }
        let mut seen = vec![false; n];
        for &(slot, body) in decoy_writes {
            if slot >= n {
                return Err(DuressError::SlotOutOfRange { slot, n });
            }
            if seen[slot] {
                return Err(DuressError::DuplicateSlot(slot));
            }
            seen[slot] = true;
            if decoy_map[slot].is_none() {
                return Err(DuressError::NotOwned(slot));
            }
            decoy_map[slot] = Some(body);
        }
        let mut next_slots = vec![[0u8; SLOT_BYTES]; n];
        for blk in next_slots.iter_mut() {
            rng(blk);
        }
        for (i, maybe_body) in decoy_map.into_iter().enumerate() {
            if let Some(body) = maybe_body {
                next_slots[i] = seal_slot_epoch(root_decoy, &self.volume_salt, next_epoch, i as u32, &body);
            }
        }
        self.epoch = next_epoch;
        self.slots = next_slots;
        Ok(())
    }

    /// Deliberately initialize a new sovereign compartment onto a decoy-only vault (or after a
    /// duress panic-shred). Distinct from [`Self::commit_dual`] so that a mistyped sovereign
    /// passphrase in `commit_dual` can never silently wipe an existing sovereign compartment.
    pub fn init_sovereign_compartment(
        &mut self,
        root_decoy: &Root,
        root_sov: &Root,
        initial_sov_entries: &[(usize, Body)],
        rng: &mut dyn FnMut(&mut [u8]),
    ) -> Result<(), DuressError> {
        if root_decoy == root_sov {
            return Err(DuressError::IdenticalRoots);
        }
        if initial_sov_entries.is_empty() {
            return Err(DuressError::EmptyCompartment);
        }
        let next_epoch = self.epoch.checked_add(1).ok_or(DuressError::EpochOverflow)?;
        let n = self.slots.len();
        let mut decoy_map: Vec<Option<Body>> = vec![None; n];
        let mut decoy_count = 0usize;
        for (i, blk) in self.slots.iter().enumerate() {
            if let Some(d) = open_slot_epoch(root_decoy, &self.volume_salt, self.epoch, i as u32, blk) {
                decoy_map[i] = Some(d);
                decoy_count += 1;
            }
        }
        if decoy_count == 0 {
            return Err(DuressError::NoOwnedSlots);
        }
        let mut sov_map: Vec<Option<Body>> = vec![None; n];
        for &(slot, body) in initial_sov_entries {
            if slot >= n {
                return Err(DuressError::SlotOutOfRange { slot, n });
            }
            if decoy_map[slot].is_some() {
                return Err(DuressError::SlotCollision(slot));
            }
            if sov_map[slot].is_some() {
                return Err(DuressError::DuplicateSlot(slot));
            }
            sov_map[slot] = Some(body);
        }
        let mut next_slots = vec![[0u8; SLOT_BYTES]; n];
        for blk in next_slots.iter_mut() {
            rng(blk);
        }
        for i in 0..n {
            if let Some(body) = decoy_map[i] {
                next_slots[i] = seal_slot_epoch(root_decoy, &self.volume_salt, next_epoch, i as u32, &body);
            } else if let Some(body) = sov_map[i] {
                next_slots[i] = seal_slot_epoch(root_sov, &self.volume_salt, next_epoch, i as u32, &body);
            }
        }
        self.epoch = next_epoch;
        self.slots = next_slots;
        Ok(())
    }

    /// Write-all dual-compartment commit: increments `epoch`, verifies BOTH `root_decoy` and
    /// `root_sov` open at least one existing disjoint slot (refusing to silently wipe an existing
    /// sovereign compartment on a mistyped sovereign passphrase), re-seals all decoy slots under
    /// `(root_decoy, epoch + 1)`, re-seals all sovereign slots under `(root_sov, epoch + 1)`
    /// (preserving unchanged sovereign slots and applying `sov_writes` outside `I_decoy`), and
    /// overwrites all remaining slots `i ∉ I_decoy ∪ I_sov` with fresh CSPRNG chaff.
    pub fn commit_dual(
        &mut self,
        root_decoy: &Root,
        decoy_writes: &[(usize, Body)],
        root_sov: &Root,
        sov_writes: &[(usize, Body)],
        rng: &mut dyn FnMut(&mut [u8]),
    ) -> Result<(), DuressError> {
        if root_decoy == root_sov {
            return Err(DuressError::IdenticalRoots);
        }
        let next_epoch = self.epoch.checked_add(1).ok_or(DuressError::EpochOverflow)?;
        let n = self.slots.len();
        let mut decoy_map: Vec<Option<Body>> = vec![None; n];
        let mut sov_map: Vec<Option<Body>> = vec![None; n];
        let mut decoy_count = 0usize;
        let mut sov_count = 0usize;
        for (i, blk) in self.slots.iter().enumerate() {
            let d = open_slot_epoch(root_decoy, &self.volume_salt, self.epoch, i as u32, blk);
            let s = open_slot_epoch(root_sov, &self.volume_salt, self.epoch, i as u32, blk);
            if d.is_some() && s.is_some() {
                return Err(DuressError::SlotCollision(i));
            }
            if d.is_some() {
                decoy_count += 1;
            }
            if s.is_some() {
                sov_count += 1;
            }
            decoy_map[i] = d;
            sov_map[i] = s;
        }
        if decoy_count == 0 {
            return Err(DuressError::NoOwnedSlots);
        }
        if sov_count == 0 {
            return Err(DuressError::NoOwnedSovereignSlots);
        }
        let mut seen_d = vec![false; n];
        for &(slot, body) in decoy_writes {
            if slot >= n {
                return Err(DuressError::SlotOutOfRange { slot, n });
            }
            if seen_d[slot] {
                return Err(DuressError::DuplicateSlot(slot));
            }
            seen_d[slot] = true;
            if decoy_map[slot].is_none() {
                return Err(DuressError::NotOwned(slot));
            }
            decoy_map[slot] = Some(body);
        }
        let mut seen_s = vec![false; n];
        for &(slot, body) in sov_writes {
            if slot >= n {
                return Err(DuressError::SlotOutOfRange { slot, n });
            }
            if seen_s[slot] {
                return Err(DuressError::DuplicateSlot(slot));
            }
            seen_s[slot] = true;
            if decoy_map[slot].is_some() {
                return Err(DuressError::SlotCollision(slot));
            }
            sov_map[slot] = Some(body);
        }
        let mut next_slots = vec![[0u8; SLOT_BYTES]; n];
        for blk in next_slots.iter_mut() {
            rng(blk);
        }
        for i in 0..n {
            if let Some(body) = decoy_map[i] {
                next_slots[i] = seal_slot_epoch(root_decoy, &self.volume_salt, next_epoch, i as u32, &body);
            } else if let Some(body) = sov_map[i] {
                next_slots[i] = seal_slot_epoch(root_sov, &self.volume_salt, next_epoch, i as u32, &body);
            }
        }
        self.epoch = next_epoch;
        self.slots = next_slots;
        Ok(())
    }

    pub fn checked_image_len(n: usize) -> Option<usize> {
        n.checked_mul(SLOT_BYTES)?.checked_add(MS_HEADER_BYTES)
    }

    pub fn image_len(n: usize) -> usize {
        Self::checked_image_len(n).expect("vault image length overflow")
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(Self::image_len(self.slots.len()));
        v.extend_from_slice(&self.epoch.to_le_bytes());
        v.extend_from_slice(&self.volume_salt);
        for s in &self.slots {
            v.extend_from_slice(s);
        }
        v
    }

    /// Deserialize a fixed-geometry vault image. Note: accepts whatever `epoch` is encoded in
    /// `bytes`; callers with trusted monotonic state MUST use [`Self::from_bytes_min_epoch`] to
    /// reject rollback/replay.
    pub fn from_bytes(bytes: &[u8], n: usize) -> Result<Self, DuressError> {
        let expected = validate_slot_count(n)?;
        if bytes.len() != expected {
            return Err(DuressError::ImageLength { expected, got: bytes.len() });
        }
        let epoch = u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]);
        let mut volume_salt = [0u8; VOLUME_SALT_BYTES];
        volume_salt.copy_from_slice(&bytes[8..MS_HEADER_BYTES]);
        let slots = bytes[MS_HEADER_BYTES..]
            .chunks_exact(SLOT_BYTES)
            .map(|c| {
                let mut b = [0u8; SLOT_BYTES];
                b.copy_from_slice(c);
                b
            })
            .collect();
        Ok(MultiSnapshotDuressVault { epoch, volume_salt, slots })
    }

    /// Deserialize a fixed-geometry vault image and reject any epoch `< min_epoch` (host
    /// monotonic rollback/replay protection).
    pub fn from_bytes_min_epoch(bytes: &[u8], n: usize, min_epoch: u64) -> Result<Self, DuressError> {
        let vault = Self::from_bytes(bytes, n)?;
        if vault.epoch < min_epoch {
            return Err(DuressError::EpochRollback { got: vault.epoch, min_epoch });
        }
        Ok(vault)
    }
}
