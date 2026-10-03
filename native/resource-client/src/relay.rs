//! `mini relay`, `mini relay-emit`, `mini relay-witness` — one channel domain's relay on one node
//! (CHANNELS.md §2.4, §4, §9 row 9; lane CH-RELAY-1).
//!
//! The Lean definitions are the implementation. This file does custody and IO only: sockets, clocks,
//! keys, the fill PRF stream (outside Lean by design, CH-CELL §6), and the client subprocess that appends
//! each epoch record. Everything with a meaning in the kernel is a call into the Lean library
//! (`--lean-lib`, built by `channel-lib/build.sh` from `Kernel.DomainEpochExport` and its imports: `Init` and
//! eleven package modules, no Mathlib — 0.73 MB, ~10 ms and ~21 MB to initialise):
//!
//! | step | Lean export | definition |
//! |---|---|---|
//! | class sizes and timing | `minidregg_channel_profile` | `profileOfId` |
//! | a cell's header (emitter) | `minidregg_channel_header` | `Schedule.headerAt` |
//! | a cell (emitter) | `minidregg_channel_cell_encode` | `Cell.ofRaw` / `Cell.encode` |
//! | the tick vector and its absent mask | `minidregg_channel_assemble` | `Schedule.assembleTagged` |
//! | the send list | `minidregg_channel_fanout` | `fanout` |
//! | the tick root | `minidregg_channel_tick_root` | `vectorRoot` |
//! | the epoch record and its opening | `minidregg_channel_seal` | `sealEpoch`, `epochOpening` |
//! | the append topic | `minidregg_channel_topic` | `channelTopic` |
//! | the witness's check | `minidregg_channel_open` | `openRecord` |
//! | a fill's envelope (relay); a member's cell (`mini channel`) | `minidregg_channel_seal_cell` | `envelopeCell` |
//! | a cell's sealing fields (`mini channel`) | `minidregg_channel_open_cell` | the `Plaintext .x25519` cut |
//! | the payload capacity at a tick | `minidregg_channel_payload_cap` | `payloadCapAt` |
//! | a record's tick roots (a member's record check) | `minidregg_channel_record_roots` | `EpochRecord.decode` |
//!
//! The wire between a member and the relay (byte-exact; every integer big-endian):
//!
//! ```text
//! member -> relay  HELLO     "DCH1" | slot 4 | subject 8 | ed25519 public key 32                 (48 B)
//! relay  -> member CHALLENGE nonce 32                                                            (32 B)
//! member -> relay  AUTH      ed25519 signature 64 over
//!                            "DREGG.CHANNEL.HELLO/v1" | domain 2 | slot 4 | subject 8 | nonce 32 (64 B)
//! relay  -> member WELCOME   "DCH1" | status 1 | class 1 | domain 2 | n 4 | relay frame key 32  (44 B)
//!                            status 0 = admitted; 1 no such lease; 2 bad signature; 3 malformed
//! then, every tick k, relay -> every slot (the same bytes to every slot):
//!                  TICK      type 1 = 0x01 | domain 2 | epoch 8 | tick-in-epoch 4 | k 8 |
//!                            prevRoot 32 | signature 64 | vector n·C                       (119 + n·C B)
//!                            the signature is ed25519 over "DREGG.CHANNEL.FRAME/v1" | bytes[0..55];
//!                            `vector` is tick k−1's assembled vector and prevRoot its tick root
//!                            (tick 0 carries an all-zero vector and root: nothing precedes it)
//! and, every tick, member -> relay: one cell, exactly C bytes, for the tick the last TICK opened.
//! ```
//!
//! The relay -> witness message (a second unix socket; never the channel cell):
//! `"DCW1" | epoch 8 | record length 4 | record | opening length 4 | opening`.

use crate::{path, Args, Result};
use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{CShake256, CShake256Core};
use std::collections::VecDeque;
use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufWriter, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::{self, Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

// ------------------------------------------------------------------ the Lean library

#[link(name = "dl")]
extern "C" {
    fn dlopen(filename: *const c_char, flag: c_int) -> *mut c_void;
    fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
    fn dlerror() -> *const c_char;
}
const RTLD_NOW: c_int = 2;
const RTLD_GLOBAL: c_int = 0x100;

type Obj = *mut c_void;

/// The channel exports of `Kernel.DomainEpochExport` and `Theory.Channel`, resolved by `dlsym` from the
/// library `channel-lib/build.sh` links. A missing symbol refuses the run by name; there is no fallback.
pub(crate) struct Lean {
    bytes_new: unsafe extern "C" fn(*const u8, usize) -> Obj,
    bytes_len: unsafe extern "C" fn(Obj) -> usize,
    bytes_ptr: unsafe extern "C" fn(Obj) -> *const u8,
    dec: unsafe extern "C" fn(Obj),
    profile: unsafe extern "C" fn(u8) -> Obj,
    header: unsafe extern "C" fn(u16, u64, u32, u32) -> Obj,
    cell_encode: unsafe extern "C" fn(u8, Obj, Obj) -> Obj,
    assemble: unsafe extern "C" fn(u8, u16, u32, u64, u32, Obj, Obj, Obj) -> Obj,
    fanout: unsafe extern "C" fn(u8, u32, Obj) -> Obj,
    tick_root: unsafe extern "C" fn(u8, u32, Obj) -> Obj,
    seal: unsafe extern "C" fn(u8, u16, u32, u64, Obj, Obj) -> Obj,
    open: unsafe extern "C" fn(Obj, Obj) -> Obj,
    topic: unsafe extern "C" fn(u16, u64) -> Obj,
    payload_cap: unsafe extern "C" fn(u8, u32) -> Obj,
    seal_cell: unsafe extern "C" fn(u8, Obj, Obj, Obj, Obj, Obj, Obj, Obj) -> Obj,
    open_cell: unsafe extern "C" fn(u8, Obj) -> Obj,
    record_roots: unsafe extern "C" fn(Obj) -> Obj,
}

unsafe fn sym<T: Copy>(handle: *mut c_void, name: &str) -> Result<T> {
    let c = CString::new(name).map_err(|_| "symbol name".to_owned())?;
    let p = dlsym(handle, c.as_ptr());
    if p.is_null() {
        return Err(format!("the channel library has no symbol {name}"));
    }
    Ok(std::mem::transmute_copy::<*mut c_void, T>(&p))
}

impl Lean {
    /// Load and initialise the library on the calling thread; every later call must be on this thread.
    pub(crate) fn load(lib: &Path) -> Result<Lean> {
        let c = CString::new(lib.as_os_str().as_encoded_bytes()).map_err(|_| "library path".to_owned())?;
        unsafe {
            let handle = dlopen(c.as_ptr(), RTLD_NOW | RTLD_GLOBAL);
            if handle.is_null() {
                let e = dlerror();
                let why = if e.is_null() { "unknown".into() } else { CStr::from_ptr(e).to_string_lossy().into_owned() };
                return Err(format!("cannot load the channel library {}: {why}", lib.display()));
            }
            let init: unsafe extern "C" fn() -> c_int = sym(handle, "mdc_init")?;
            if init() != 0 {
                return Err("the channel library's Lean initialisation failed".into());
            }
            Ok(Lean {
                bytes_new: sym(handle, "mdc_bytes_new")?,
                bytes_len: sym(handle, "mdc_bytes_len")?,
                bytes_ptr: sym(handle, "mdc_bytes_ptr")?,
                dec: sym(handle, "mdc_dec")?,
                profile: sym(handle, "minidregg_channel_profile")?,
                header: sym(handle, "minidregg_channel_header")?,
                cell_encode: sym(handle, "minidregg_channel_cell_encode")?,
                assemble: sym(handle, "minidregg_channel_assemble")?,
                fanout: sym(handle, "minidregg_channel_fanout")?,
                tick_root: sym(handle, "minidregg_channel_tick_root")?,
                seal: sym(handle, "minidregg_channel_seal")?,
                open: sym(handle, "minidregg_channel_open")?,
                topic: sym(handle, "minidregg_channel_topic")?,
                payload_cap: sym(handle, "minidregg_channel_payload_cap")?,
                seal_cell: sym(handle, "minidregg_channel_seal_cell")?,
                open_cell: sym(handle, "minidregg_channel_open_cell")?,
                record_roots: sym(handle, "minidregg_channel_record_roots")?,
            })
        }
    }

    /// A fresh Lean `ByteArray`; the export it is passed to consumes it.
    fn arr(&self, b: &[u8]) -> Obj {
        unsafe { (self.bytes_new)(b.as_ptr(), b.len()) }
    }

    /// Copy out a returned `ByteArray` and release it.
    fn take(&self, o: Obj) -> Vec<u8> {
        unsafe {
            let n = (self.bytes_len)(o);
            let v = std::slice::from_raw_parts((self.bytes_ptr)(o), n).to_vec();
            (self.dec)(o);
            v
        }
    }

    pub(crate) fn profile(&self, pid: u8) -> Result<Profile> {
        let b = self.take(unsafe { (self.profile)(pid) });
        if b.len() != 24 {
            return Err(format!("class {pid} is not a published class (profileOfId refused)"));
        }
        let f = |i: usize| u32::from_be_bytes(b[4 * i..4 * i + 4].try_into().unwrap()) as u64;
        Ok(Profile { c: f(0) as usize, rate_mhz: f(1), e: f(2), delta_ms: f(3), delta_relay_ms: f(4), mu_ms: f(5) })
    }

    pub(crate) fn header(&self, domain: u16, epoch: u64, tick: u32, slot: u32) -> Vec<u8> {
        self.take(unsafe { (self.header)(domain, epoch, tick, slot) })
    }

    pub(crate) fn cell_encode(&self, pid: u8, header: &[u8], body: &[u8]) -> Vec<u8> {
        let (h, b) = (self.arr(header), self.arr(body));
        self.take(unsafe { (self.cell_encode)(pid, h, b) })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assemble(&self, pid: u8, domain: u16, n: u32, epoch: u64, tick: u32, leases: &[u8], rx: &[u8], pad: &[u8]) -> Vec<u8> {
        let (l, r, p) = (self.arr(leases), self.arr(rx), self.arr(pad));
        self.take(unsafe { (self.assemble)(pid, domain, n, epoch, tick, l, r, p) })
    }

    pub(crate) fn fanout(&self, pid: u8, n: u32, presence: &[u8]) -> Vec<u8> {
        let p = self.arr(presence);
        self.take(unsafe { (self.fanout)(pid, n, p) })
    }

    pub(crate) fn tick_root(&self, pid: u8, n: u32, cells: &[u8]) -> Vec<u8> {
        let c = self.arr(cells);
        self.take(unsafe { (self.tick_root)(pid, n, c) })
    }

    pub(crate) fn seal(&self, pid: u8, domain: u16, n: u32, epoch: u64, ticks: &[u8], salt: &[u8]) -> Vec<u8> {
        let (t, s) = (self.arr(ticks), self.arr(salt));
        self.take(unsafe { (self.seal)(pid, domain, n, epoch, t, s) })
    }

    pub(crate) fn open(&self, record: &[u8], opening: &[u8]) -> Vec<u8> {
        let (r, o) = (self.arr(record), self.arr(opening));
        self.take(unsafe { (self.open)(r, o) })
    }

    pub(crate) fn topic(&self, domain: u16, epoch: u64) -> Vec<u8> {
        self.take(unsafe { (self.topic)(domain, epoch) })
    }

    /// The X25519-mode payload capacity of a cell at `tick` (`payloadCapAt`; 195 / 35 at P1).
    pub(crate) fn payload_cap(&self, pid: u8, tick: u32) -> Result<usize> {
        let b = self.take(unsafe { (self.payload_cap)(pid, tick) });
        let b: [u8; 4] = b.try_into().map_err(|_| format!("class {pid}: payload_cap refused"))?;
        Ok(u32::from_be_bytes(b) as usize)
    }

    /// A cell from its sealing fields (`envelopeCell`); empty when a field has the wrong length.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn seal_cell(&self, pid: u8, header: &[u8], duty: &[u8], view_tag: u8, frag: &[u8], epk: &[u8], payload: &[u8], tag: &[u8]) -> Vec<u8> {
        let a = [self.arr(header), self.arr(duty), self.arr(&[view_tag]), self.arr(frag), self.arr(epk), self.arr(payload), self.arr(tag)];
        self.take(unsafe { (self.seal_cell)(pid, a[0], a[1], a[2], a[3], a[4], a[5], a[6]) })
    }

    /// A cell's seven fields `header, duty, viewTag, frag, epk, payload, tag`, as the Lean codec cuts
    /// them (`openCellBytesList`: each `length 2 | bytes`); `None` when the cell is not `C` bytes.
    pub(crate) fn open_cell(&self, pid: u8, cell: &[u8]) -> Option<CellFields> {
        let b = self.take(unsafe { (self.open_cell)(pid, self.arr(cell)) });
        let mut fields = Vec::with_capacity(7);
        let mut i = 0;
        while i < b.len() {
            let n = u16::from_be_bytes([b[i], *b.get(i + 1)?]) as usize;
            fields.push(b.get(i + 2..i + 2 + n)?.to_vec());
            i += 2 + n;
        }
        let [header, duty, view_tag, frag, epk, payload, tag]: [Vec<u8>; 7] = fields.try_into().ok()?;
        Some(CellFields { header, duty, view_tag: *view_tag.first()?, frag, epk, payload, tag })
    }

    /// `domain 2 | epoch 8 | E tick roots` of a canonical epoch record; empty when it is not one.
    pub(crate) fn record_roots(&self, record: &[u8]) -> Vec<u8> {
        self.take(unsafe { (self.record_roots)(self.arr(record)) })
    }
}

/// A cell cut into its sealing fields by `minidregg_channel_open_cell`.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct CellFields {
    pub header: Vec<u8>,
    pub duty: Vec<u8>,
    pub view_tag: u8,
    pub frag: Vec<u8>,
    pub epk: Vec<u8>,
    pub payload: Vec<u8>,
    pub tag: Vec<u8>,
}

/// A published class, as `minidregg_channel_profile` reports it.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Profile {
    pub c: usize,
    pub rate_mhz: u64,
    pub e: u64,
    pub delta_ms: u64,
    pub delta_relay_ms: u64,
    pub mu_ms: u64,
}

impl Profile {
    pub(crate) fn tick(&self) -> Duration {
        Duration::from_micros(1_000_000_000 / self.rate_mhz)
    }
}

// ------------------------------------------------------------------ wire

pub(crate) const MAGIC: &[u8; 4] = b"DCH1";
pub(crate) const WITNESS_MAGIC: &[u8; 4] = b"DCW1";
const HELLO_TAG: &[u8] = b"DREGG.CHANNEL.HELLO/v1";
const FRAME_TAG: &[u8] = b"DREGG.CHANNEL.FRAME/v1";
pub(crate) const HELLO_LEN: usize = 48;
pub(crate) const WELCOME_LEN: usize = 44;
pub(crate) const FRAME_HEAD: usize = 55;
pub(crate) const FRAME_LEN: usize = FRAME_HEAD + 64;

pub(crate) fn tick_message_len(n: usize, c: usize) -> usize {
    FRAME_LEN + n * c
}

pub(crate) fn hello_bytes(slot: u32, subject: u64, key: &[u8; 32]) -> Vec<u8> {
    let mut v = Vec::with_capacity(HELLO_LEN);
    v.extend_from_slice(MAGIC);
    v.extend_from_slice(&slot.to_be_bytes());
    v.extend_from_slice(&subject.to_be_bytes());
    v.extend_from_slice(key);
    v
}

pub(crate) fn hello_signing_bytes(domain: u16, slot: u32, subject: u64, nonce: &[u8; 32]) -> Vec<u8> {
    let mut v = HELLO_TAG.to_vec();
    v.extend_from_slice(&domain.to_be_bytes());
    v.extend_from_slice(&slot.to_be_bytes());
    v.extend_from_slice(&subject.to_be_bytes());
    v.extend_from_slice(nonce);
    v
}

pub(crate) fn welcome_bytes(status: u8, pid: u8, domain: u16, n: u32, frame_key: &[u8; 32]) -> Vec<u8> {
    let mut v = Vec::with_capacity(WELCOME_LEN);
    v.extend_from_slice(MAGIC);
    v.push(status);
    v.push(pid);
    v.extend_from_slice(&domain.to_be_bytes());
    v.extend_from_slice(&n.to_be_bytes());
    v.extend_from_slice(frame_key);
    v
}

/// The fixed head of a TICK message, before its signature.
pub(crate) fn frame_head(domain: u16, epoch: u64, tick: u32, k: u64, prev_root: &[u8; 32]) -> [u8; FRAME_HEAD] {
    let mut h = [0u8; FRAME_HEAD];
    h[0] = 1;
    h[1..3].copy_from_slice(&domain.to_be_bytes());
    h[3..11].copy_from_slice(&epoch.to_be_bytes());
    h[11..15].copy_from_slice(&tick.to_be_bytes());
    h[15..23].copy_from_slice(&k.to_be_bytes());
    h[23..55].copy_from_slice(prev_root);
    h
}

pub(crate) fn frame_signing_bytes(head: &[u8]) -> Vec<u8> {
    let mut v = FRAME_TAG.to_vec();
    v.extend_from_slice(head);
    v
}

/// A parsed TICK message head.
#[derive(Debug, PartialEq)]
pub(crate) struct FrameHead {
    pub domain: u16,
    pub epoch: u64,
    pub tick: u32,
    pub k: u64,
    pub prev_root: [u8; 32],
}

pub(crate) fn parse_frame_head(m: &[u8]) -> Option<FrameHead> {
    if m.len() < FRAME_LEN || m[0] != 1 {
        return None;
    }
    Some(FrameHead {
        domain: u16::from_be_bytes(m[1..3].try_into().ok()?),
        epoch: u64::from_be_bytes(m[3..11].try_into().ok()?),
        tick: u32::from_be_bytes(m[11..15].try_into().ok()?),
        k: u64::from_be_bytes(m[15..23].try_into().ok()?),
        prev_root: m[23..55].try_into().ok()?,
    })
}

pub(crate) fn witness_bytes(epoch: u64, record: &[u8], opening: &[u8]) -> Vec<u8> {
    let mut v = WITNESS_MAGIC.to_vec();
    v.extend_from_slice(&epoch.to_be_bytes());
    v.extend_from_slice(&(record.len() as u32).to_be_bytes());
    v.extend_from_slice(record);
    v.extend_from_slice(&(opening.len() as u32).to_be_bytes());
    v.extend_from_slice(opening);
    v
}

// ------------------------------------------------------------------ leases, keys, PRF

/// A row of the relay's lease file: `slot holder pubkey-hex from to` (epochs `[from, to)`).
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct LeaseRow {
    pub slot: u32,
    pub holder: u64,
    pub key: [u8; 32],
    pub from: u64,
    pub to: u64,
}

pub(crate) fn parse_leases(text: &str) -> Result<Vec<LeaseRow>> {
    let mut rows = Vec::new();
    for (i, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let f: Vec<&str> = line.split_whitespace().collect();
        if f.len() != 5 {
            return Err(format!("lease line {}: want `slot holder pubkey-hex from to`", i + 1));
        }
        let num = |s: &str| s.parse::<u64>().map_err(|_| format!("lease line {}: {s} is not a number", i + 1));
        let key = unhex(f[2]).filter(|k| k.len() == 32).ok_or(format!("lease line {}: key is not 32 hex bytes", i + 1))?;
        rows.push(LeaseRow {
            slot: u32::try_from(num(f[0])?).map_err(|_| "slot out of range".to_owned())?,
            holder: num(f[1])?,
            key: key.try_into().unwrap(),
            from: num(f[3])?,
            to: num(f[4])?,
        });
    }
    Ok(rows)
}

/// The lease records `minidregg_channel_assemble` reads: `holder 8 | slot 4 | from 8 | to 8` each.
pub(crate) fn lease_records(rows: &[LeaseRow]) -> Vec<u8> {
    let mut v = Vec::with_capacity(28 * rows.len());
    for r in rows {
        v.extend_from_slice(&r.holder.to_be_bytes());
        v.extend_from_slice(&r.slot.to_be_bytes());
        v.extend_from_slice(&r.from.to_be_bytes());
        v.extend_from_slice(&r.to.to_be_bytes());
    }
    v
}

pub(crate) fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

pub(crate) fn unhex(s: &str) -> Option<Vec<u8>> {
    crate::decode_hex(s).ok()
}

pub(crate) fn xof(customization: &[u8], parts: &[&[u8]], out: &mut [u8]) {
    let mut h = CShake256::from_core(CShake256Core::new(customization));
    for p in parts {
        h.update(p);
    }
    XofReader::read(&mut h.finalize_xof(), out);
}

/// The fill key of an epoch, then the fill PRF stream of a tick: `n × (C − 8)` bytes, position-major,
/// position `ρ`'s bytes `cSHAKE256_{FILL}(fillKey_e ‖ epoch 8 ‖ tick 4 ‖ ρ 4)`. Outside Lean by design
/// (CH-CELL §6): the relay supplies the stream, `assemble` places it (`fillCell`).
pub(crate) fn fill_pad(secret: &[u8; 32], domain: u16, epoch: u64, tick: u32, n: usize, body: usize) -> Vec<u8> {
    let mut key = [0u8; 32];
    xof(b"DREGG.CHANNEL.FILL-KEY/v1", &[secret, &domain.to_be_bytes(), &epoch.to_be_bytes()], &mut key);
    let mut pad = vec![0u8; n * body];
    for (rho, chunk) in pad.chunks_mut(body).enumerate() {
        xof(b"DREGG.CHANNEL.FILL/v1", &[&key, &epoch.to_be_bytes(), &tick.to_be_bytes(), &(rho as u32).to_be_bytes()], chunk);
    }
    pad
}

/// The 32-byte blinder of an epoch's absent commitment: `cSHAKE256_{ABSENT-SALT}(secret ‖ domain ‖ epoch)`.
pub(crate) fn absent_salt(secret: &[u8; 32], domain: u16, epoch: u64) -> [u8; 32] {
    let mut s = [0u8; 32];
    xof(b"DREGG.CHANNEL.ABSENT-SALT/v1", &[secret, &domain.to_be_bytes(), &epoch.to_be_bytes()], &mut s);
    s
}

/// The fill of one tick, position-major (`n × (C − 8)` bytes), as `assemble` takes it. Each position's
/// body is an envelope drawn from `fill_pad`'s stream — duty part, view tag, fragment, payload and tag —
/// with an X25519 public key (of a scalar drawn from the same stream) where a sealed cell carries its
/// ephemeral key, laid out by the Lean seal export. A sealed cell's `epk` is a curve point and a raw PRF
/// string is one only half the time, so without the point a non-recipient could tell a fill from a
/// sealed cell by a Legendre symbol; with it the two have the same shape (`FillHidden`, CHANNELS §2.4).
/// Still one value per position: deterministic in (relay secret, domain, epoch, tick, position).
#[allow(clippy::too_many_arguments)]
pub(crate) fn fill_bodies(lean: &Lean, pid: u8, secret: &[u8; 32], domain: u16, epoch: u64, tick: u32, n: usize, c: usize) -> Result<Vec<u8>> {
    let body = c - 8;
    let stream = fill_pad(secret, domain, epoch, tick, n, body + 32);
    let mut out = Vec::with_capacity(n * body);
    let mut shape: Option<(usize, usize)> = None;
    for (rho, s) in stream.chunks(body + 32).enumerate() {
        let header = lean.header(domain, epoch, tick, rho as u32);
        let (dl, cap) = match shape {
            Some(x) => x,
            None => {
                let mut probe = header.clone();
                probe.resize(c, 0);
                let f = lean.open_cell(pid, &probe).ok_or("open_cell refused a C-byte probe")?;
                *shape.insert((f.duty.len(), f.payload.len()))
            }
        };
        let scalar: [u8; 32] = s[body..body + 32].try_into().unwrap();
        let epk = x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(scalar));
        let cell = lean.seal_cell(pid, &header, &s[..dl], s[dl], &s[dl + 1..dl + 5], epk.as_bytes(), &s[dl + 5..dl + 5 + cap], &s[dl + 5 + cap..dl + 21 + cap]);
        if cell.len() != c {
            return Err(format!("seal_cell refused the fill at tick {tick} position {rho} ({} bytes)", cell.len()));
        }
        out.extend_from_slice(&cell[8..]);
    }
    Ok(out)
}

pub(crate) fn urandom(out: &mut [u8]) -> Result<()> {
    File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(out))
        .map_err(|e| format!("cannot read /dev/urandom: {e}"))
}

/// A 32-byte secret held in a private file, created on first use.
pub(crate) fn secret_file(path: &Path) -> Result<[u8; 32]> {
    match fs::read(path) {
        Ok(b) if b.len() == 32 => Ok(b.try_into().unwrap()),
        Ok(_) => Err(format!("{} is not 32 bytes", path.display())),
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            let mut s = [0u8; 32];
            urandom(&mut s)?;
            let mut f = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(path)
                .map_err(|e| format!("cannot create {}: {e}", path.display()))?;
            f.write_all(&s).map_err(|e| format!("cannot write {}: {e}", path.display()))?;
            Ok(s)
        }
        Err(e) => Err(format!("cannot read {}: {e}", path.display())),
    }
}

// ------------------------------------------------------------------ connections

pub(crate) enum Conn {
    Unix(UnixStream),
    Tcp(TcpStream),
}

impl Conn {
    fn try_clone(&self) -> io::Result<Conn> {
        Ok(match self {
            Conn::Unix(s) => Conn::Unix(s.try_clone()?),
            Conn::Tcp(s) => Conn::Tcp(s.try_clone()?),
        })
    }
    fn set_write_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        match self {
            Conn::Unix(s) => s.set_write_timeout(d),
            Conn::Tcp(s) => s.set_write_timeout(d),
        }
    }
    fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        match self {
            Conn::Unix(s) => s.set_read_timeout(d),
            Conn::Tcp(s) => s.set_read_timeout(d),
        }
    }
    fn shutdown(&self) {
        let _ = match self {
            Conn::Unix(s) => s.shutdown(std::net::Shutdown::Both),
            Conn::Tcp(s) => s.shutdown(std::net::Shutdown::Both),
        };
    }
}

impl Read for Conn {
    fn read(&mut self, b: &mut [u8]) -> io::Result<usize> {
        match self {
            Conn::Unix(s) => s.read(b),
            Conn::Tcp(s) => s.read(b),
        }
    }
}

impl Write for Conn {
    fn write(&mut self, b: &[u8]) -> io::Result<usize> {
        match self {
            Conn::Unix(s) => s.write(b),
            Conn::Tcp(s) => s.write(b),
        }
    }
    fn flush(&mut self) -> io::Result<()> {
        match self {
            Conn::Unix(s) => s.flush(),
            Conn::Tcp(s) => s.flush(),
        }
    }
}

pub(crate) fn connect(spec: &str) -> Result<Conn> {
    if let Some(p) = spec.strip_prefix("unix:") {
        UnixStream::connect(p).map(Conn::Unix).map_err(|e| format!("cannot connect to {spec}: {e}"))
    } else if let Some(a) = spec.strip_prefix("tcp:") {
        let s = TcpStream::connect(a).map_err(|e| format!("cannot connect to {spec}: {e}"))?;
        let _ = s.set_nodelay(true);
        Ok(Conn::Tcp(s))
    } else {
        Err(format!("--connect wants unix:PATH or tcp:HOST:PORT, not {spec}"))
    }
}

/// A cell that arrived on a slot's connection.
struct Arrival {
    holder: u64,
    cell: Vec<u8>,
}

/// One live member connection per slot; `gen` tells a stale reader from the current one.
struct Slots {
    writers: Vec<Option<(u64, Conn)>>,
}

struct Shared {
    slots: Mutex<Slots>,
    next_gen: AtomicU64,
    stop: AtomicBool,
    bytes_in: AtomicU64,
}

struct Domain {
    pid: u8,
    domain: u16,
    n: usize,
    c: usize,
    leases: Vec<LeaseRow>,
    frame_key: [u8; 32],
}

fn handshake(conn: &mut Conn, dom: &Domain) -> Result<(u32, u64)> {
    conn.set_read_timeout(Some(Duration::from_secs(5))).map_err(|e| e.to_string())?;
    let mut hello = [0u8; HELLO_LEN];
    conn.read_exact(&mut hello).map_err(|e| format!("hello: {e}"))?;
    let refuse = |conn: &mut Conn, status: u8, why: String| -> Result<(u32, u64)> {
        let _ = conn.write_all(&welcome_bytes(status, dom.pid, dom.domain, dom.n as u32, &dom.frame_key));
        Err(why)
    };
    if &hello[0..4] != MAGIC {
        return refuse(conn, 3, "hello: bad magic".into());
    }
    let slot = u32::from_be_bytes(hello[4..8].try_into().unwrap());
    let subject = u64::from_be_bytes(hello[8..16].try_into().unwrap());
    let key: [u8; 32] = hello[16..48].try_into().unwrap();
    let mut nonce = [0u8; 32];
    urandom(&mut nonce)?;
    conn.write_all(&nonce).map_err(|e| format!("challenge: {e}"))?;
    let mut sig = [0u8; 64];
    conn.read_exact(&mut sig).map_err(|e| format!("auth: {e}"))?;
    if !dom.leases.iter().any(|l| l.slot == slot && l.holder == subject && l.key == key) || slot as usize >= dom.n {
        return refuse(conn, 1, format!("no lease for slot {slot} held by subject {subject} under that key"));
    }
    let vk = VerifyingKey::from_bytes(&key).map_err(|_| "bad key".to_owned())?;
    if vk
        .verify(&hello_signing_bytes(dom.domain, slot, subject, &nonce), &Signature::from_bytes(&sig))
        .is_err()
    {
        return refuse(conn, 2, format!("slot {slot}: the hello signature does not verify"));
    }
    conn.write_all(&welcome_bytes(0, dom.pid, dom.domain, dom.n as u32, &dom.frame_key))
        .map_err(|e| format!("welcome: {e}"))?;
    conn.set_read_timeout(None).map_err(|e| e.to_string())?;
    Ok((slot, subject))
}

fn serve_member(mut conn: Conn, dom: Arc<Domain>, shared: Arc<Shared>, tx: Sender<Arrival>, log: Arc<Mutex<File>>) {
    let (slot, subject) = match handshake(&mut conn, &dom) {
        Ok(x) => x,
        Err(why) => {
            let _ = writeln!(log.lock().unwrap(), "refused connection: {why}");
            return;
        }
    };
    let writer = match conn.try_clone() {
        Ok(w) => w,
        Err(_) => return,
    };
    let _ = writer.set_write_timeout(Some(Duration::from_millis(50)));
    let gen = shared.next_gen.fetch_add(1, Ordering::SeqCst);
    {
        let mut s = shared.slots.lock().unwrap();
        if let Some((_, old)) = s.writers[slot as usize].take() {
            old.shutdown();
        }
        s.writers[slot as usize] = Some((gen, writer));
    }
    let _ = writeln!(log.lock().unwrap(), "slot {slot} connected (subject {subject}, gen {gen})");
    let mut cell = vec![0u8; dom.c];
    loop {
        if conn.read_exact(&mut cell).is_err() {
            break;
        }
        shared.bytes_in.fetch_add(dom.c as u64, Ordering::Relaxed);
        if tx.send(Arrival { holder: subject, cell: cell.clone() }).is_err() {
            break;
        }
    }
    let mut s = shared.slots.lock().unwrap();
    if matches!(&s.writers[slot as usize], Some((g, _)) if *g == gen) {
        s.writers[slot as usize] = None;
    }
    drop(s);
    let _ = writeln!(log.lock().unwrap(), "slot {slot} disconnected (gen {gen})");
}

// ------------------------------------------------------------------ clocks

#[repr(C)]
struct Timespec {
    tv_sec: i64,
    tv_nsec: i64,
}
extern "C" {
    fn clock_gettime(clk: c_int, tp: *mut Timespec) -> c_int;
}
const CLOCK_PROCESS_CPUTIME_ID: c_int = 2;

fn cpu_us() -> u64 {
    let mut t = Timespec { tv_sec: 0, tv_nsec: 0 };
    unsafe { clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &mut t) };
    t.tv_sec as u64 * 1_000_000 + t.tv_nsec as u64 / 1000
}

fn load1() -> String {
    fs::read_to_string("/proc/loadavg").ok().and_then(|s| s.split_whitespace().next().map(str::to_owned)).unwrap_or_default()
}

pub(crate) fn sleep_until(t: Instant) {
    let now = Instant::now();
    if t > now {
        thread::sleep(t - now);
    }
}

/// The relay's frame and deadline waits: sleep to `guard` before `t`, then yield until `t`, so a
/// timer wake-up's latency is spent before the instant rather than after it (`--spin-ms`).
fn wait_until(t: Instant, guard: Duration) {
    let now = Instant::now();
    if t > now + guard {
        thread::sleep(t - now - guard);
    }
    while Instant::now() < t {
        thread::yield_now();
    }
}

fn us(d: Duration) -> u128 {
    d.as_micros()
}

/// Signed microseconds `a − b`.
pub(crate) fn diff_us(a: Instant, b: Instant) -> i64 {
    if a >= b {
        (a - b).as_micros() as i64
    } else {
        -((b - a).as_micros() as i64)
    }
}

// ------------------------------------------------------------------ the relay

/// Write a sealed record to the members' record directory as `<epoch>.rec` (write, then rename: a
/// member never reads half a record).
fn publish_record(dir: &Path, epoch: u64, record: &[u8]) {
    let tmp = dir.join(format!(".{epoch}.rec.tmp"));
    if fs::write(&tmp, record).is_ok() {
        let _ = fs::rename(&tmp, dir.join(format!("{epoch}.rec")));
    }
}

/// What the append thread is given once per epoch.
struct Sealed {
    epoch: u64,
    topic: Vec<u8>,
    record: Vec<u8>,
}

fn append_loop(rx: Receiver<Sealed>, mini: PathBuf, ws: PathBuf, stream: String, dir: PathBuf, out: PathBuf) {
    let mut csv = match File::create(&out) {
        Ok(f) => BufWriter::new(f),
        Err(_) => return,
    };
    let _ = writeln!(csv, "epoch,result,propose_ms,submit_ms,detail");
    let _ = csv.flush();
    for s in rx {
        let id = format!("chr-{stream}-e{}", s.epoch);
        let req = dir.join(format!("{id}.json"));
        let body = serde_json::json!({
            "type": "minidregg-workspace-proposal-v1",
            "action": "invoke",
            "targets": [{"name": stream, "payload": {"type": "append", "topicHex": hex(&s.topic), "payloadHex": hex(&s.record)}}],
        });
        let _ = fs::write(&req, body.to_string());
        let t0 = Instant::now();
        let p = Command::new(&mini)
            .args(["workspace", "--action", "propose", "--dir"])
            .arg(&ws)
            .arg("--request")
            .arg(&req)
            .args(["--proposal-id", &id])
            .output();
        let propose_ms = t0.elapsed().as_millis();
        let (result, submit_ms, detail) = match p {
            Ok(o) if o.status.success() => {
                let t1 = Instant::now();
                let q = Command::new(&mini)
                    .args(["workspace", "--action", "submit", "--dir"])
                    .arg(&ws)
                    .arg("--intent")
                    .arg(ws.join("proposals").join(&id).join("intent.json"))
                    .arg("--attempt")
                    .arg(ws.join("attempts").join(&id))
                    .output();
                let ms = t1.elapsed().as_millis();
                match q {
                    Ok(o) if o.status.success() => ("admitted", ms, String::new()),
                    Ok(o) => ("refused", ms, last_line(&o.stderr)),
                    Err(e) => ("error", ms, e.to_string()),
                }
            }
            Ok(o) => ("refused-at-propose", 0, last_line(&o.stderr)),
            Err(e) => ("error", 0, e.to_string()),
        };
        let _ = writeln!(csv, "{},{result},{propose_ms},{submit_ms},\"{}\"", s.epoch, detail.replace('"', "'"));
        let _ = csv.flush();
    }
}

fn last_line(b: &[u8]) -> String {
    let s = String::from_utf8_lossy(b);
    let refusal = s.lines().filter(|l| l.contains("encoded refusal")).last().and_then(|l| l.split_whitespace().last()).and_then(unhex);
    let decoded = refusal.map(|r| String::from_utf8_lossy(&r).chars().filter(|c| !c.is_control()).collect::<String>());
    let tail = s.lines().filter(|l| !l.trim().is_empty()).last().unwrap_or("").to_owned();
    match decoded {
        Some(d) => format!("{} | {}", d.chars().take(300).collect::<String>(), tail),
        None => tail,
    }
}

/// `mini relay`.
pub(crate) fn run_relay(mut args: Args) -> Result<()> {
    let lib = path(args.required("lean-lib")?);
    let pid: u8 = num(&mut args, "class")?;
    let domain: u16 = num(&mut args, "domain")?;
    let n: usize = num(&mut args, "n")?;
    let leases_file = path(args.required("leases")?);
    let ticks: u64 = num(&mut args, "ticks")?;
    let e0: u64 = args.optional("first-epoch").map(|v| v.to_string_lossy().parse()).transpose().map_err(|_| "--first-epoch".to_owned())?.unwrap_or(0);
    let unix_path = path(args.required("unix")?);
    let tcp = args.optional("tcp").map(|v| v.to_string_lossy().into_owned());
    let witness = args.optional("witness").map(path);
    let state = path(args.required("state-dir")?);
    let out = path(args.required("out-dir")?);
    let append_ws = args.optional("append-ws").map(path);
    let stream = args.optional("stream").map(|v| v.to_string_lossy().into_owned());
    let fault_gap: Option<u64> = args.optional("fault-gap-at-epoch").map(|v| v.to_string_lossy().parse()).transpose().map_err(|_| "--fault-gap-at-epoch".to_owned())?;
    let start_delay_ms: u64 = args.optional("start-delay-ms").map(|v| v.to_string_lossy().parse()).transpose().map_err(|_| "--start-delay-ms".to_owned())?.unwrap_or(3000);
    let spin = Duration::from_millis(args.optional("spin-ms").map(|v| v.to_string_lossy().parse()).transpose().map_err(|_| "--spin-ms".to_owned())?.unwrap_or(2));
    let wait_members_ms: u64 = args.optional("wait-members-ms").map(|v| v.to_string_lossy().parse()).transpose().map_err(|_| "--wait-members-ms".to_owned())?.unwrap_or(0);
    // a planted fault for the member's own-slot check: drop slot S's cell at tick K once (`S:K`)
    let fault_drop: Option<(u32, u64)> = match args.optional("fault-drop") {
        None => None,
        Some(v) => {
            let v = v.to_string_lossy().into_owned();
            let (a, b) = v.split_once(':').ok_or("--fault-drop wants SLOT:TICK")?;
            Some((a.parse().map_err(|_| "--fault-drop slot")?, b.parse().map_err(|_| "--fault-drop tick")?))
        }
    };
    // each sealed record, published to members for their own-slot check against the record (§4 step 6)
    let records_dir = args.optional("records-dir").map(path);
    args.finish()?;
    if append_ws.is_some() != stream.is_some() {
        return Err("--append-ws and --stream go together".into());
    }

    let tl0 = Instant::now();
    let lean = Lean::load(&lib)?;
    let lean_init_ms = tl0.elapsed().as_millis();
    let prof = lean.profile(pid)?;
    fs::create_dir_all(&state).map_err(|e| format!("state dir: {e}"))?;
    fs::create_dir_all(&out).map_err(|e| format!("out dir: {e}"))?;
    if let Some(d) = &records_dir {
        fs::create_dir_all(d).map_err(|e| format!("records dir: {e}"))?;
    }
    let secret = secret_file(&state.join("relay-secret"))?;
    let frame_sk = SigningKey::from_bytes(&secret_file(&state.join("relay-frame-key"))?);
    let leases = parse_leases(&fs::read_to_string(&leases_file).map_err(|e| format!("leases: {e}"))?)?;
    let lease_bytes = lease_records(&leases);
    let dom = Arc::new(Domain { pid, domain, n, c: prof.c, leases, frame_key: frame_sk.verifying_key().to_bytes() });
    let shared = Arc::new(Shared {
        slots: Mutex::new(Slots { writers: (0..n).map(|_| None).collect() }),
        next_gen: AtomicU64::new(1),
        stop: AtomicBool::new(false),
        bytes_in: AtomicU64::new(0),
    });
    let log = Arc::new(Mutex::new(File::create(out.join("relay.log")).map_err(|e| format!("relay.log: {e}"))?));
    let (tx, arrivals) = mpsc::channel::<Arrival>();

    let _ = fs::remove_file(&unix_path);
    let ul = UnixListener::bind(&unix_path).map_err(|e| format!("cannot bind {}: {e}", unix_path.display()))?;
    {
        let (dom, shared, tx, log) = (dom.clone(), shared.clone(), tx.clone(), log.clone());
        thread::spawn(move || {
            for c in ul.incoming().flatten() {
                let (dom, shared, tx, log) = (dom.clone(), shared.clone(), tx.clone(), log.clone());
                thread::spawn(move || serve_member(Conn::Unix(c), dom, shared, tx, log));
            }
        });
    }
    if let Some(addr) = &tcp {
        let tl = TcpListener::bind(addr).map_err(|e| format!("cannot bind {addr}: {e}"))?;
        let bound = tl.local_addr().map_err(|e| e.to_string())?;
        fs::write(out.join("tcp-addr"), bound.to_string()).map_err(|e| format!("tcp-addr: {e}"))?;
        let (dom, shared, tx, log) = (dom.clone(), shared.clone(), tx.clone(), log.clone());
        thread::spawn(move || {
            for c in tl.incoming().flatten() {
                let _ = c.set_nodelay(true);
                let (dom, shared, tx, log) = (dom.clone(), shared.clone(), tx.clone(), log.clone());
                thread::spawn(move || serve_member(Conn::Tcp(c), dom, shared, tx, log));
            }
        });
    }
    drop(tx);

    let appender = match (&append_ws, &stream) {
        (Some(ws), Some(st)) => {
            let (atx, arx) = mpsc::channel::<Sealed>();
            let mini = std::env::current_exe().map_err(|e| format!("current exe: {e}"))?;
            let (ws, st, dir, csv) = (ws.clone(), st.clone(), out.join("append-requests"), out.join("appends.csv"));
            fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
            let h = thread::spawn(move || append_loop(arx, mini, ws, st, dir, csv));
            Some((atx, h))
        }
        _ => None,
    };
    let mut witness_conn = match &witness {
        Some(p) => Some(UnixStream::connect(p).map_err(|e| format!("cannot reach the witness at {}: {e}", p.display()))?),
        None => None,
    };
    let mut discard = OpenOptions::new().write(true).open("/dev/null").map_err(|e| format!("/dev/null: {e}"))?;

    let mut csv = BufWriter::new(File::create(out.join("relay.csv")).map_err(|e| e.to_string())?);
    writeln!(
        csv,
        "k,epoch,tick,send_late_us,sends,live,mailbox,fanout_lean_us,send_us,bytes_out,bytes_in,cells_in,absent,wake_late_us,pad_us,assemble_us,root_us,ready_slack_us,missed,seal_us,cpu_us,load1"
    )
    .map_err(|e| e.to_string())?;
    // the per-(tick, slot) byte log: what crossed the relay's sockets for each slot (the trace test's
    // relay-side capture; tcpdump needs a capability this box does not grant, and slots ride unix sockets)
    let mut wire = BufWriter::new(File::create(out.join("wire.csv")).map_err(|e| e.to_string())?);
    writeln!(wire, "k,slot,route,down_bytes,up_bytes").map_err(|e| e.to_string())?;
    let slot_of: std::collections::HashMap<u64, u32> = dom.leases.iter().map(|l| (l.holder, l.slot)).collect();
    let mut up_prev: Vec<u64> = vec![0; n];
    let mut records = BufWriter::new(File::create(out.join("records.csv")).map_err(|e| e.to_string())?);
    writeln!(records, "epoch,sealed_epoch,record_bytes,opening_bytes,record_sha_hex16,witness").map_err(|e| e.to_string())?;

    let tick = prof.tick();
    let deadline_lead = Duration::from_millis(prof.delta_relay_ms);
    let e_len = prof.e;
    let msg_len = tick_message_len(n, prof.c);
    let mut prev_vector = vec![0u8; n * prof.c];
    let mut prev_root = [0u8; 32];
    let mut epoch_buf: Vec<u8> = Vec::with_capacity(e_len as usize * n * (prof.c + 1));
    let mut pending: VecDeque<Arrival> = VecDeque::new();
    let mut pending_seal: Option<(u64, Vec<u8>)> = None;
    let mut missed = 0u64;
    let mut sealed_count = 0u64;
    // optionally hold the first frame until every slot is connected (or the wait runs out): the tick
    // schedule never depends on presence after t0
    let tw = Instant::now();
    while tw.elapsed() < Duration::from_millis(wait_members_ms) {
        if shared.slots.lock().unwrap().writers.iter().all(Option::is_some) {
            break;
        }
        thread::sleep(Duration::from_millis(50));
    }
    let connected_at_t0 = shared.slots.lock().unwrap().writers.iter().filter(|w| w.is_some()).count();
    let t0 = Instant::now() + Duration::from_millis(start_delay_ms);
    let _ = writeln!(
        log.lock().unwrap(),
        "class {pid} C {} E {e_len} tick {:?} n {n} domain {domain} ticks {ticks}; lean init {lean_init_ms} ms; {connected_at_t0}/{n} connected after {} ms; t0 = now + {start_delay_ms} ms",
        prof.c,
        tick,
        tw.elapsed().as_millis()
    );

    for k in 0..ticks {
        let epoch = e0 + k / e_len;
        let t = (k % e_len) as u32;
        let frame = t0 + tick * k as u32;
        let deadline = frame + tick - deadline_lead;
        let cpu0 = cpu_us();

        // (1) fan out tick k−1's vector at frame k, to every slot (`fanout`), live or mailbox.
        wait_until(frame, spin);
        let send_start = Instant::now();
        let send_late = diff_us(send_start, frame);
        let presence: Vec<u8> = {
            let s = shared.slots.lock().unwrap();
            s.writers.iter().map(|w| u8::from(w.is_some())).collect()
        };
        let tf = Instant::now();
        let routes = lean.fanout(pid, n as u32, &presence);
        let fanout_lean = us(tf.elapsed());
        if routes.len() != 5 * n {
            return Err(format!("fanout returned {} bytes for n = {n}", routes.len()));
        }
        let head = frame_head(domain, epoch, t, k, &prev_root);
        let sig = frame_sk.sign(&frame_signing_bytes(&head)).to_bytes();
        let mut msg = Vec::with_capacity(msg_len);
        msg.extend_from_slice(&head);
        msg.extend_from_slice(&sig);
        msg.extend_from_slice(&prev_vector);
        let (mut sends, mut live, mut mailbox, mut bytes_out) = (0u64, 0u64, 0u64, 0u64);
        let mut wire_rows: Vec<(usize, &str, u64)> = Vec::with_capacity(n);
        let ts = Instant::now();
        {
            let mut s = shared.slots.lock().unwrap();
            for r in routes.chunks(5) {
                let slot = u32::from_be_bytes(r[0..4].try_into().unwrap()) as usize;
                let (ok, route) = if r[4] == 0 {
                    live += 1;
                    match s.writers.get_mut(slot).and_then(|w| w.as_mut()) {
                        Some((_, w)) => (w.write_all(&msg).is_ok(), "live"),
                        None => (discard.write_all(&msg).is_ok(), "live-gone"),
                    }
                } else {
                    mailbox += 1;
                    (discard.write_all(&msg).is_ok(), "mailbox")
                };
                sends += 1;
                if ok {
                    bytes_out += msg.len() as u64;
                }
                wire_rows.push((slot, route, if ok { msg.len() as u64 } else { 0 }));
            }
        }
        let send_us = us(ts.elapsed());
        // tick k−1's uplink (collected at its deadline) beside tick k's downlink (the vector of k−1)
        for (slot, route, down) in wire_rows {
            let _ = writeln!(wire, "{k},{slot},{route},{down},{}", up_prev.get(slot).copied().unwrap_or(0));
        }
        let _ = wire.flush();

        // (2) the previous epoch's seal, after this tick's fan-out so it never delays a frame.
        let mut seal_us = 0u128;
        if let Some((sealed_for, buf)) = pending_seal.take() {
            let tz = Instant::now();
            let salt = absent_salt(&secret, domain, sealed_for);
            let labelled = match fault_gap {
                Some(g) if sealed_for >= g => sealed_for + 1,
                _ => sealed_for,
            };
            let sealed = lean.seal(pid, domain, n as u32, labelled, &buf, &salt);
            let rlen = 47 + 32 * e_len as usize;
            let olen = e_len as usize * n + 32;
            if sealed.len() != rlen + olen {
                return Err(format!("seal refused epoch {sealed_for} ({} bytes)", sealed.len()));
            }
            let (record, opening) = sealed.split_at(rlen);
            let topic = lean.topic(domain, labelled);
            seal_us = us(tz.elapsed());
            sealed_count += 1;
            let wit = match witness_conn.as_mut() {
                Some(w) => if w.write_all(&witness_bytes(labelled, record, opening)).is_ok() { "sent" } else { "failed" },
                None => "none",
            };
            let digest = <sha2::Sha256 as sha2::Digest>::digest(record);
            let _ = writeln!(records, "{sealed_for},{labelled},{},{},{},{wit}", record.len(), opening.len(), hex(&digest[..8]));
            let _ = records.flush();
            if let Some(d) = &records_dir {
                publish_record(d, labelled, record);
            }
            if let Some((atx, _)) = &appender {
                let _ = atx.send(Sealed { epoch: labelled, topic, record: record.to_vec() });
            }
        }

        // (3) collect tick k's cells until its deadline, then assemble, root, and keep for the seal.
        wait_until(deadline, spin);
        let woke = Instant::now();
        let wake_late = diff_us(woke, deadline);
        while let Ok(a) = arrivals.try_recv() {
            pending.push_back(a);
        }
        let mut up = vec![0u64; n];
        for a in &pending {
            if let Some(&sl) = slot_of.get(&a.holder) {
                if let Some(u) = up.get_mut(sl as usize) {
                    *u += a.cell.len() as u64;
                }
            }
        }
        if let Some((fs_, fk)) = fault_drop {
            if fk == k {
                if let Some(i) = pending.iter().position(|a| slot_of.get(&a.holder) == Some(&fs_)) {
                    pending.remove(i);
                    let _ = writeln!(log.lock().unwrap(), "fault: dropped slot {fs_}'s cell at tick {k} (--fault-drop)");
                }
            }
        }
        up_prev = up;
        let mut received = Vec::with_capacity(pending.len() * (8 + prof.c));
        let cells_in = pending.len();
        for a in pending.drain(..) {
            received.extend_from_slice(&a.holder.to_be_bytes());
            received.extend_from_slice(&a.cell);
        }
        let tp = Instant::now();
        let pad = fill_bodies(&lean, pid, &secret, domain, epoch, t, n, prof.c)?;
        let pad_us = us(tp.elapsed());
        let ta = Instant::now();
        let out_t = lean.assemble(pid, domain, n as u32, epoch, t, &lease_bytes, &received, &pad);
        let assemble_us = us(ta.elapsed());
        if out_t.len() != n * (prof.c + 1) {
            return Err(format!("assemble refused tick {k} ({} bytes)", out_t.len()));
        }
        let tr = Instant::now();
        let root = lean.tick_root(pid, n as u32, &out_t[..n * prof.c]);
        let root_us = us(tr.elapsed());
        if root.len() != 32 {
            return Err(format!("tick_root refused tick {k}"));
        }
        let absent = out_t[n * prof.c..].iter().filter(|&&b| b == 1).count();
        prev_vector.copy_from_slice(&out_t[..n * prof.c]);
        prev_root.copy_from_slice(&root);
        epoch_buf.extend_from_slice(&out_t);
        if t as u64 == e_len - 1 {
            pending_seal = Some((epoch, std::mem::take(&mut epoch_buf)));
        }
        let ready = Instant::now();
        let next_frame = frame + tick;
        let slack = diff_us(next_frame, ready);
        let miss = ready > next_frame;
        if miss {
            missed += 1;
        }
        let cpu = cpu_us() - cpu0;
        writeln!(
            csv,
            "{k},{epoch},{t},{send_late},{sends},{live},{mailbox},{fanout_lean},{send_us},{bytes_out},{},{cells_in},{absent},{wake_late},{pad_us},{assemble_us},{root_us},{slack},{},{seal_us},{cpu},{}",
            shared.bytes_in.swap(0, Ordering::Relaxed),
            u8::from(miss),
            load1()
        )
        .map_err(|e| e.to_string())?;
        csv.flush().map_err(|e| e.to_string())?;
    }

    // the last complete epoch's seal is still pending when the last tick ends: seal it now
    if let Some((sealed_for, buf)) = pending_seal.take() {
        let salt = absent_salt(&secret, domain, sealed_for);
        let labelled = match fault_gap {
            Some(g) if sealed_for >= g => sealed_for + 1,
            _ => sealed_for,
        };
        let sealed = lean.seal(pid, domain, n as u32, labelled, &buf, &salt);
        let rlen = 47 + 32 * e_len as usize;
        if sealed.len() == rlen + e_len as usize * n + 32 {
            let (record, opening) = sealed.split_at(rlen);
            sealed_count += 1;
            let wit = match witness_conn.as_mut() {
                Some(w) => if w.write_all(&witness_bytes(labelled, record, opening)).is_ok() { "sent" } else { "failed" },
                None => "none",
            };
            let digest = <sha2::Sha256 as sha2::Digest>::digest(record);
            let _ = writeln!(records, "{sealed_for},{labelled},{},{},{},{wit}", record.len(), opening.len(), hex(&digest[..8]));
            if let Some(d) = &records_dir {
                publish_record(d, labelled, record);
            }
            if let Some((atx, _)) = &appender {
                let _ = atx.send(Sealed { epoch: labelled, topic: lean.topic(domain, labelled), record: record.to_vec() });
            }
        }
    }
    let _ = records.flush();
    shared.stop.store(true, Ordering::SeqCst);
    {
        let mut s = shared.slots.lock().unwrap();
        for w in s.writers.iter_mut() {
            if let Some((_, c)) = w.take() {
                c.shutdown();
            }
        }
    }
    drop(witness_conn);
    if let Some((atx, h)) = appender {
        drop(atx);
        let _ = h.join();
    }
    let _ = fs::remove_file(&unix_path);
    let summary = serde_json::json!({
        "type": "minidregg-channel-relay-run-v1",
        "class": pid, "domain": domain, "n": n, "ticks": ticks, "firstEpoch": e0,
        "missed": missed, "sealed": sealed_count, "faultGapAtEpoch": fault_gap,
        "leanInitMs": lean_init_ms as u64, "connectedAtT0": connected_at_t0, "spinMs": spin.as_millis() as u64,
    });
    fs::write(out.join("summary.json"), summary.to_string()).map_err(|e| e.to_string())?;
    println!("{summary}");
    Ok(())
}

pub(crate) fn num<T: std::str::FromStr>(args: &mut Args, name: &str) -> Result<T> {
    args.required(name)?.to_string_lossy().parse::<T>().map_err(|_| format!("--{name} is not a number"))
}

// ------------------------------------------------------------------ the test emitter

/// `mini relay-emit`: one member slot. Emits exactly one `C`-byte cell per tick at `arrival + T − δ`
/// (padding: the body is random bytes, a stand-in for a seal to a forgotten key; CH-CLIENT-1 seals),
/// and logs every TICK it receives: size, inter-arrival, frame signature, root and own-slot checks.
pub(crate) fn run_emit(mut args: Args) -> Result<()> {
    let lib = path(args.required("lean-lib")?);
    let spec = args.required("connect")?.to_string_lossy().into_owned();
    let domain: u16 = num(&mut args, "domain")?;
    let slot: u32 = num(&mut args, "slot")?;
    let subject: u64 = num(&mut args, "subject")?;
    let key_file = path(args.required("key")?);
    let out = path(args.required("out")?);
    let max_ticks: Option<u64> =
        args.optional("ticks").map(|v| v.to_string_lossy().parse()).transpose().map_err(|_| "--ticks".to_owned())?;
    args.finish()?;
    let lean = Lean::load(&lib)?;
    let sk = SigningKey::from_bytes(&secret_file(&key_file)?);
    let Joined { mut conn, pid, n, frame_key: vk } = member_join(&spec, domain, slot, subject, &sk)?;
    let prof = lean.profile(pid)?;
    let c = prof.c;
    let tick = prof.tick();
    let lead = Duration::from_millis(prof.delta_ms);
    let mut csv = BufWriter::new(File::create(&out).map_err(|e| format!("{}: {e}", out.display()))?);
    writeln!(csv, "k,epoch,tick,bytes,arrival_us,interarrival_us,sig_ok,root_ok,own,emit_late_us,seal_slack_us").map_err(|e| e.to_string())?;
    let start = Instant::now();
    let mut last: Option<Instant> = None;
    let mut sent: Option<(u64, Vec<u8>)> = None;
    let mut buf = vec![0u8; tick_message_len(n, c)];
    let mut count = 0u64;
    loop {
        if conn.read_exact(&mut buf).is_err() {
            break;
        }
        let a = Instant::now();
        let TickCheck { head, sig_ok, root_ok } = check_tick(&lean, pid, n, &vk, &buf)?;
        let vector = &buf[FRAME_LEN..];
        // the vector is tick k − 1's: my position holds the cell I sent then, or something else (§4 step 6)
        let own = match &sent {
            Some((kk, cell)) if kk + 1 == head.k => {
                if vector[slot as usize * c..(slot as usize + 1) * c] == cell[..] { "kept" } else { "replaced" }
            }
            _ => "none",
        };
        let inter = last.map(|l| (a - l).as_micros() as i64).unwrap_or(-1);
        last = Some(a);
        count += 1;
        let done = max_ticks.is_some_and(|m| count >= m);
        let mut emit_late = 0i64;
        let mut seal_slack = 0i64;
        if !done {
            let header = lean.header(domain, head.epoch, head.tick, slot);
            let mut body = vec![0u8; c - 8];
            urandom(&mut body)?;
            let cell = lean.cell_encode(pid, &header, &body);
            if cell.len() != c {
                return Err(format!("cell_encode refused ({} bytes)", cell.len()));
            }
            let emit_at = a + tick - lead;
            // §4: a cell is eligible only if sealed by the cutoff `emission − μ`
            seal_slack = diff_us(emit_at - Duration::from_millis(prof.mu_ms), Instant::now());
            sleep_until(emit_at);
            emit_late = diff_us(Instant::now(), emit_at);
            if conn.write_all(&cell).is_err() {
                break;
            }
            sent = Some((head.k, cell));
        }
        writeln!(
            csv,
            "{},{},{},{},{},{inter},{},{},{own},{emit_late},{seal_slack}",
            head.k,
            head.epoch,
            head.tick,
            buf.len(),
            (a - start).as_micros(),
            u8::from(sig_ok),
            u8::from(root_ok)
        )
        .map_err(|e| e.to_string())?;
        csv.flush().map_err(|e| e.to_string())?;
        if done {
            break;
        }
    }
    Ok(())
}

/// A member's side of the handshake (HELLO, CHALLENGE, AUTH, WELCOME): the connection, the domain's
/// class id, its slot count and the relay's frame key. Shared by `relay-emit` and `channel join`.
pub(crate) struct Joined {
    pub conn: Conn,
    pub pid: u8,
    pub n: usize,
    pub frame_key: VerifyingKey,
}

pub(crate) fn member_join(spec: &str, domain: u16, slot: u32, subject: u64, sk: &SigningKey) -> Result<Joined> {
    let mut conn = connect(spec)?;
    conn.write_all(&hello_bytes(slot, subject, &sk.verifying_key().to_bytes())).map_err(|e| format!("hello: {e}"))?;
    let mut nonce = [0u8; 32];
    conn.read_exact(&mut nonce).map_err(|e| format!("challenge: {e}"))?;
    conn.write_all(&sk.sign(&hello_signing_bytes(domain, slot, subject, &nonce)).to_bytes()).map_err(|e| format!("auth: {e}"))?;
    let mut w = [0u8; WELCOME_LEN];
    conn.read_exact(&mut w).map_err(|e| format!("welcome: {e}"))?;
    if &w[0..4] != MAGIC {
        return Err("welcome: bad magic".into());
    }
    if w[4] != 0 {
        return Err(format!("the relay refused slot {slot}: status {}", w[4]));
    }
    if u16::from_be_bytes([w[6], w[7]]) != domain {
        return Err("welcome: another domain".into());
    }
    let n = u32::from_be_bytes(w[8..12].try_into().unwrap()) as usize;
    if slot as usize >= n {
        return Err("slot out of range".into());
    }
    let frame_key = VerifyingKey::from_bytes(&w[12..44].try_into().unwrap()).map_err(|_| "welcome: bad frame key".to_owned())?;
    Ok(Joined { conn, pid: w[5], n, frame_key })
}

/// What a member checks on every TICK before using it: the relay's frame signature, and that the
/// vector it carries opens the frame's root (Lean `tick_root`; tick 0 carries the all-zero root and vector).
pub(crate) struct TickCheck {
    pub head: FrameHead,
    pub sig_ok: bool,
    pub root_ok: bool,
}

pub(crate) fn check_tick(lean: &Lean, pid: u8, n: usize, vk: &VerifyingKey, buf: &[u8]) -> Result<TickCheck> {
    let head = parse_frame_head(buf).ok_or("malformed TICK")?;
    let sig: [u8; 64] = buf[FRAME_HEAD..FRAME_LEN].try_into().unwrap();
    let sig_ok = vk.verify(&frame_signing_bytes(&buf[..FRAME_HEAD]), &Signature::from_bytes(&sig)).is_ok();
    let vector = &buf[FRAME_LEN..];
    let root_ok = if head.k == 0 {
        head.prev_root == [0u8; 32] && vector.iter().all(|&b| b == 0)
    } else {
        lean.tick_root(pid, n as u32, vector) == head.prev_root
    };
    Ok(TickCheck { head, sig_ok, root_ok })
}

/// `mini relay-key --key FILE`: the public key of a member's (or the relay's) ed25519 seed file,
/// creating the seed if absent, for the relay's lease file.
pub(crate) fn run_key(mut args: Args) -> Result<()> {
    let key = path(args.required("key")?);
    args.finish()?;
    let sk = SigningKey::from_bytes(&secret_file(&key)?);
    println!("{}", hex(&sk.verifying_key().to_bytes()));
    Ok(())
}

// ------------------------------------------------------------------ the witness endpoint

/// `mini relay-witness`: the endpoint the relay hands each epoch's record and absent opening to
/// (§2.4: the opening goes to the operator and the witnesses, never into the channel cell). Each
/// opening is checked by the kernel's `openRecord` (`minidregg_channel_open`), and so is a copy with
/// one salt bit flipped, which must be refused `notOpening`: the check can fail.
pub(crate) fn run_witness(mut args: Args) -> Result<()> {
    let lib = path(args.required("lean-lib")?);
    let sock = path(args.required("unix")?);
    let out = path(args.required("out")?);
    args.finish()?;
    let lean = Lean::load(&lib)?;
    let _ = fs::remove_file(&sock);
    let l = UnixListener::bind(&sock).map_err(|e| format!("cannot bind {}: {e}", sock.display()))?;
    let mut csv = BufWriter::new(File::create(&out).map_err(|e| e.to_string())?);
    writeln!(csv, "epoch,verdict,tampered_verdict,record_bytes,opening_bytes,mask_ones,opening_hex").map_err(|e| e.to_string())?;
    csv.flush().map_err(|e| e.to_string())?;
    let (mut c, _) = l.accept().map_err(|e| e.to_string())?;
    let verdict = |v: &[u8]| match v {
        [0] => "opened".to_owned(),
        [1, 0] => "refused-maskLength".into(),
        [1, 1] => "refused-maskByte".into(),
        [1, 2] => "refused-unknownClass".into(),
        [1, 3] => "refused-notOpening".into(),
        [2] => "malformed-record".into(),
        other => format!("unexpected-{}", hex(other)),
    };
    loop {
        let mut head = [0u8; 16];
        if c.read_exact(&mut head).is_err() {
            break;
        }
        if &head[0..4] != WITNESS_MAGIC {
            return Err("witness: bad magic".into());
        }
        let epoch = u64::from_be_bytes(head[4..12].try_into().unwrap());
        let rlen = u32::from_be_bytes(head[12..16].try_into().unwrap()) as usize;
        let mut record = vec![0u8; rlen];
        c.read_exact(&mut record).map_err(|e| e.to_string())?;
        let mut ol = [0u8; 4];
        c.read_exact(&mut ol).map_err(|e| e.to_string())?;
        let mut opening = vec![0u8; u32::from_be_bytes(ol) as usize];
        c.read_exact(&mut opening).map_err(|e| e.to_string())?;
        let v = verdict(&lean.open(&record, &opening));
        let mut tampered = opening.clone();
        if let Some(last) = tampered.last_mut() {
            *last ^= 1;
        }
        let tv = verdict(&lean.open(&record, &tampered));
        let ones = opening[..opening.len().saturating_sub(32)].iter().filter(|&&b| b == 1).count();
        writeln!(csv, "{epoch},{v},{tv},{},{},{ones},{}", record.len(), opening.len(), hex(&opening)).map_err(|e| e.to_string())?;
        csv.flush().map_err(|e| e.to_string())?;
    }
    let _ = fs::remove_file(&sock);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tick_message_is_fixed_size() {
        assert_eq!(FRAME_LEN, 119);
        assert_eq!(tick_message_len(3, 256), 887);
        let root = [7u8; 32];
        let head = frame_head(7, 0x0102_0304_0506_0708, 15, 600, &root);
        assert_eq!(head.len(), FRAME_HEAD);
        let mut msg = head.to_vec();
        msg.extend_from_slice(&[0u8; 64]);
        assert_eq!(
            parse_frame_head(&msg),
            Some(FrameHead { domain: 7, epoch: 0x0102_0304_0506_0708, tick: 15, k: 600, prev_root: root })
        );
        msg[0] = 2;
        assert_eq!(parse_frame_head(&msg), None, "a message of another type is refused");
        assert_eq!(parse_frame_head(&msg[..FRAME_LEN - 1]), None, "a short message is refused");
    }

    #[test]
    fn handshake_bytes_are_exact() {
        let sk = SigningKey::from_bytes(&[3u8; 32]);
        let pk = sk.verifying_key().to_bytes();
        let h = hello_bytes(2, 12, &pk);
        assert_eq!(h.len(), HELLO_LEN);
        assert_eq!(&h[0..4], MAGIC);
        assert_eq!(&h[4..8], &[0, 0, 0, 2]);
        assert_eq!(&h[8..16], &12u64.to_be_bytes());
        let nonce = [9u8; 32];
        let msg = hello_signing_bytes(7, 2, 12, &nonce);
        let sig = sk.sign(&msg);
        let vk = VerifyingKey::from_bytes(&pk).unwrap();
        assert!(vk.verify(&msg, &sig).is_ok());
        assert!(vk.verify(&hello_signing_bytes(8, 2, 12, &nonce), &sig).is_err(), "another domain's hello fails");
        assert!(vk.verify(&hello_signing_bytes(7, 1, 12, &nonce), &sig).is_err(), "another slot's hello fails");
        let w = welcome_bytes(0, 1, 7, 3, &pk);
        assert_eq!(w.len(), WELCOME_LEN);
        assert_eq!(&w[4..12], &[0, 1, 0, 7, 0, 0, 0, 3]);
    }

    #[test]
    fn lease_records_are_28_bytes() {
        let k = hex(&[5u8; 32]);
        let rows = parse_leases(&format!("# slot holder key from to\n0 10 {k} 0 100\n2 12 {k} 3 4\n")).unwrap();
        assert_eq!(rows.len(), 2);
        let b = lease_records(&rows);
        assert_eq!(b.len(), 56);
        assert_eq!(&b[0..8], &10u64.to_be_bytes());
        assert_eq!(&b[8..12], &0u32.to_be_bytes());
        assert_eq!(&b[12..20], &0u64.to_be_bytes());
        assert_eq!(&b[20..28], &100u64.to_be_bytes());
        assert_eq!(&b[28..36], &12u64.to_be_bytes());
        assert!(parse_leases("0 10 abcd 0 1").is_err(), "a short key is refused");
        assert!(parse_leases("0 10").is_err(), "a short line is refused");
    }

    #[test]
    fn fill_pad_is_per_position_and_deterministic() {
        let s = [1u8; 32];
        let a = fill_pad(&s, 7, 3, 4, 3, 248);
        assert_eq!(a.len(), 3 * 248);
        assert_eq!(a, fill_pad(&s, 7, 3, 4, 3, 248), "one value per position");
        assert_ne!(a[0..248], a[248..496], "positions differ");
        assert_ne!(a, fill_pad(&s, 7, 3, 5, 3, 248), "ticks differ");
        assert_ne!(a, fill_pad(&s, 7, 4, 4, 3, 248), "epochs differ");
        assert_ne!(a, fill_pad(&[2u8; 32], 7, 3, 4, 3, 248), "relays differ");
        assert_ne!(absent_salt(&s, 7, 3), absent_salt(&s, 7, 4));
    }

    #[test]
    fn witness_message_layout() {
        let m = witness_bytes(5, &[1, 2, 3], &[4, 5]);
        assert_eq!(&m[0..4], WITNESS_MAGIC);
        assert_eq!(&m[4..12], &5u64.to_be_bytes());
        assert_eq!(&m[12..16], &3u32.to_be_bytes());
        assert_eq!(&m[16..19], &[1, 2, 3]);
        assert_eq!(&m[19..23], &2u32.to_be_bytes());
        assert_eq!(&m[23..], &[4, 5]);
    }
}

#[test]
fn unhex_rejects_malformed_unicode_without_panicking() {
    for invalid in ["0é0", "😀", "a", "zz"] {
        assert_eq!(unhex(invalid), None);
    }
    let bytes: Vec<u8> = (0..=255).collect();
    assert_eq!(unhex(&hex(&bytes)), Some(bytes));
    assert_eq!(unhex("aAFF"), Some(vec![170, 255]));
}
