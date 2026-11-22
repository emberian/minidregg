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
//! * **Part B (`DuressChaffVolume`).** [`DuressVault`] is a fixed-`N`-slot image of 64-byte
//!   blocks; each occupied slot is `(body ‖ tag) XOR pad` with
//!   `pad = cSHAKE256(root ‖ salt_i ‖ u32le(i))` and `tag = cSHAKE256(root ‖ salt_i ‖ u32le(i) ‖ body)`
//!   under distinct customization strings; every other slot is chaff. This is
//!   `SlotScheme.seal` / `SlotScheme.open_` in the Lean file with `B = [u8; 32]` under XOR.
//!   The Lean deniability theorem is in the ideal-XOF model; here the pads are cSHAKE256, so
//!   deniability is computational (PRF assumption on cSHAKE256 under the sovereign root) and
//!   is *not* proved for this code.
//!
//! What this module does not do: the passphrase KDF is one cSHAKE256 call, not a memory-hard
//! function; the chaff source is caller-supplied (production must pass an OS CSPRNG); the
//! vault model is a single snapshot (an adversary who images the device twice sees which
//! blocks changed — see the research note).

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
