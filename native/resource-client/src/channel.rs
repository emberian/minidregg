//! `mini channel key|join|say|tail|status` — the member client of a constant-rate channel domain
//! (CHANNELS.md §2.2, §2.4, §4; lane CH-CLIENT-1).
//!
//! `join` is the member loop. It connects to the relay (`relay::member_join`: HELLO, CHALLENGE, AUTH,
//! WELCOME), then on every TICK it receives:
//!
//! 1. checks the frame signature and that the vector opens the frame's root (`relay::check_tick`, Lean
//!    `tick_root`), refusing by name otherwise;
//! 2. compares the committed cell at its own slot with the one it sent for the previous tick
//!    (`own_omission_evident`) and re-queues the fragment when they differ;
//! 3. trial-decrypts every other cell by view tag and delivers each completed message to `inbox.jsonl`;
//! 4. at the seal cutoff `emission − μ` (revision 2's rule: a payload queued by then rides this tick),
//!    takes the SMALLEST queued payload (smallest remaining bytes first, §4 decided 10-01), or padding;
//! 5. seals it there and then — real payload and padding through one code path — and records the seal
//!    time against the window μ;
//! 6. emits exactly `C` bytes at `arrival + T − δ` (the member's class's δ: 300 ms at P1, 600 ms at P1
//!    phone), whatever it sealed.
//!
//! After each epoch it reads the relay's published record (`--records-dir`), decodes its tick roots with
//! the Lean codec (`minidregg_channel_record_roots`) and checks every root against the one it verified on
//! the frame, and its own committed cells against what it sent.
//!
//! **Sealing** (X25519 mode; ML-KEM pairwise keys are lane CH-KEM-EPOCH). Per cell: a fresh ephemeral
//! X25519 key `esk`; `ss = X25519(esk, pk_recipient)`; `key ‖ viewTag = cSHAKE256_{DREGG.CHANNEL.SEAL/v1}(ss
//! ‖ epk ‖ pk_recipient ‖ header)` (33 bytes); ChaCha20-Poly1305 under `key`, nonce `header ‖ 0⁴` (the key
//! is fresh per cell), associated data `header ‖ duty ‖ viewTag ‖ epk`, plaintext `frag 4 ‖ payload`. The
//! fields are placed by the Lean codec (`minidregg_channel_seal_cell` / `_open_cell`,
//! `Theory.Channel.Envelope`): `[duty] | viewTag | frag | epk | payload | tag`. Padding is the same
//! construction to a fresh recipient key nobody keeps. `frag` is `seq 2 | len 2` (the high bit of `len`
//! marks a message's last fragment); `seq` counts this sender's messages to that recipient.
//!
//! **Files** (`HOME/ROOM/`, owner-private): `xkey` (the X25519 secret), `roster` (`name slot x25519-hex`
//! per line, copied at join), `outbox/` (one file per `say`; the loop takes them at the next tick),
//! `inbox.jsonl` (what this member received and could open, in tick order — the channel's `tail` is
//! this file, never a kernel read), `sent.jsonl`, `events.log`, `member.csv`, `wire.csv`
//! (`k, rx_bytes, tx_bytes`: the member side of the trace test), `status.json`.

use crate::relay::{self, check_tick, member_join, Joined, Lean, TickCheck, FRAME_LEN};
use crate::{path, Args, Result};
use chacha20poly1305::aead::{Aead, KeyInit, Payload};
use chacha20poly1305::{ChaCha20Poly1305, Key, Nonce};
use ed25519_dalek::SigningKey;
use serde_json::{json, Value};
use std::collections::{BTreeMap, HashMap};
use std::fs::{self, File, OpenOptions};
use std::io::{BufRead, BufReader, BufWriter, Read, Seek, SeekFrom, Write};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use x25519_dalek::{PublicKey, StaticSecret};

const SEAL_TAG: &[u8] = b"DREGG.CHANNEL.SEAL/v1";
/// The high bit of a fragment's `len`: this is the message's last fragment.
const FINAL: u16 = 0x8000;

pub(crate) const USAGE: &str = "mini channel key ROOM [--home DIR]
mini channel join ROOM --lean-lib LIB.so --connect unix:SOCKET|tcp:HOST:PORT --domain D --leases LEASES.txt --key ED25519-SEED --roster ROSTER [--class P1|P1phone] [--ticks K] [--records-dir DIR] [--home DIR]
mini channel say ROOM @NAME TEXT... [--home DIR]
mini channel tail ROOM [--follow] [--home DIR]
mini channel status ROOM [--home DIR]";

fn unix_ms() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_millis() as u64).unwrap_or(0)
}

/// `HOME/ROOM`: `--home`, else `$MINI_CHANNEL_HOME`, else `$HOME/.mini/channels`.
fn room_dir(args: &mut Args) -> Result<(String, PathBuf)> {
    let room = args.required("room")?.to_string_lossy().into_owned();
    if room.is_empty() || !room.chars().all(|c| c.is_ascii_alphanumeric() || "._-".contains(c)) || room.starts_with('.') {
        return Err(format!("room name {room:?}: letters, digits, '.', '_' and '-' only"));
    }
    let home = match args.optional("home") {
        Some(h) => path(h),
        None => match std::env::var_os("MINI_CHANNEL_HOME") {
            Some(h) => PathBuf::from(h),
            None => PathBuf::from(std::env::var_os("HOME").ok_or("no --home and no $HOME")?).join(".mini/channels"),
        },
    };
    Ok((room.clone(), home.join(room)))
}

fn private_dir(p: &Path) -> Result<()> {
    fs::DirBuilder::new().recursive(true).mode(0o700).create(p).map_err(|e| format!("{}: {e}", p.display()))
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args.required("action").map_err(|_| USAGE.to_owned())?.to_string_lossy().into_owned();
    match action.as_str() {
        "key" => key(args),
        "join" => join(args),
        "say" => say(args),
        "tail" => tail(args),
        "status" => status(args),
        _ => Err(format!("unknown channel action {action}\n\n{USAGE}")),
    }
}

// ------------------------------------------------------------------ keys and roster

fn xkey(dir: &Path) -> Result<StaticSecret> {
    private_dir(dir)?;
    Ok(StaticSecret::from(relay::secret_file(&dir.join("xkey"))?))
}

/// `mini channel key ROOM`: this member's X25519 public key for the room's roster (created if absent).
fn key(mut args: Args) -> Result<()> {
    let (_, dir) = room_dir(&mut args)?;
    args.finish()?;
    let sk = xkey(&dir)?;
    println!("{}", relay::hex(PublicKey::from(&sk).as_bytes()));
    Ok(())
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Peer {
    pub name: String,
    pub slot: u32,
    pub pk: [u8; 32],
}

/// The roster: `name slot x25519-public-hex` per line. Who holds which slot and under which sealing key
/// is out-of-band here; the kernel's schedule cell carrying it is lane CH-LEASE.
pub(crate) fn parse_roster(text: &str) -> Result<Vec<Peer>> {
    let mut peers: Vec<Peer> = Vec::new();
    for (i, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let f: Vec<&str> = line.split_whitespace().collect();
        if f.len() != 3 {
            return Err(format!("roster line {}: want `name slot x25519-hex`", i + 1));
        }
        let pk = relay::unhex(f[2]).filter(|k| k.len() == 32).ok_or(format!("roster line {}: key is not 32 hex bytes", i + 1))?;
        let peer = Peer {
            name: f[0].trim_start_matches('@').to_owned(),
            slot: f[1].parse().map_err(|_| format!("roster line {}: slot", i + 1))?,
            pk: pk.try_into().unwrap(),
        };
        if peers.iter().any(|p| p.name == peer.name || p.slot == peer.slot) {
            return Err(format!("roster line {}: name or slot repeated", i + 1));
        }
        peers.push(peer);
    }
    Ok(peers)
}

// ------------------------------------------------------------------ sealing

/// `key 32 ‖ viewTag 1` of one cell.
fn derive(ss: &[u8; 32], epk: &[u8; 32], rpk: &[u8; 32], header: &[u8]) -> ([u8; 32], u8) {
    let mut okm = [0u8; 33];
    relay::xof(SEAL_TAG, &[ss, epk, rpk, header], &mut okm);
    (okm[..32].try_into().unwrap(), okm[32])
}

fn nonce(header: &[u8]) -> [u8; 12] {
    let mut n = [0u8; 12];
    n[..8].copy_from_slice(&header[..8]);
    n
}

fn aad(header: &[u8], duty: &[u8], view_tag: u8, epk: &[u8]) -> Vec<u8> {
    let mut a = Vec::with_capacity(header.len() + duty.len() + 33);
    a.extend_from_slice(header);
    a.extend_from_slice(duty);
    a.push(view_tag);
    a.extend_from_slice(epk);
    a
}

fn random_secret() -> Result<StaticSecret> {
    let mut b = [0u8; 32];
    relay::urandom(&mut b)?;
    Ok(StaticSecret::from(b))
}

/// The layout at one tick, as the Lean codec cuts a `C`-byte cell under that tick's header.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Shape {
    pub duty: usize,
    pub cap: usize,
}

pub(crate) fn shape_at(lean: &Lean, pid: u8, header: &[u8], c: usize) -> Result<Shape> {
    let mut probe = header.to_vec();
    probe.resize(c, 0);
    let f = lean.open_cell(pid, &probe).ok_or("open_cell refused a C-byte cell")?;
    let cap = lean.payload_cap(pid, u16::from_be_bytes([header[4], header[5]]) as u32)?;
    if cap != f.payload.len() {
        return Err(format!("payload_cap {cap} disagrees with open_cell's payload {}", f.payload.len()));
    }
    Ok(Shape { duty: f.duty.len(), cap })
}

/// Seal one cell. `to = None` is padding: the same construction to a fresh key nobody keeps.
#[allow(clippy::too_many_arguments)]
pub(crate) fn seal(lean: &Lean, pid: u8, c: usize, header: &[u8], shape: Shape, to: Option<&[u8; 32]>, frag: [u8; 4], data: &[u8]) -> Result<Vec<u8>> {
    if data.len() > shape.cap {
        return Err(format!("{} payload bytes exceed the cell's {}", data.len(), shape.cap));
    }
    // the duty part (VRF proof, verdict root, accumulator) is CH-DUTY's; until then, random bytes
    let mut duty = vec![0u8; shape.duty];
    relay::urandom(&mut duty)?;
    let esk = random_secret()?;
    let epk = PublicKey::from(&esk);
    let rpk = match to {
        Some(pk) => *pk,
        None => *PublicKey::from(&random_secret()?).as_bytes(),
    };
    let ss = esk.diffie_hellman(&PublicKey::from(rpk));
    let (k, view_tag) = derive(ss.as_bytes(), epk.as_bytes(), &rpk, header);
    let mut pt = Vec::with_capacity(4 + shape.cap);
    pt.extend_from_slice(&frag);
    pt.extend_from_slice(data);
    pt.resize(4 + shape.cap, 0);
    let ct = ChaCha20Poly1305::new(Key::from_slice(&k))
        .encrypt(Nonce::from_slice(&nonce(header)), Payload { msg: &pt, aad: &aad(header, &duty, view_tag, epk.as_bytes()) })
        .map_err(|_| "seal: AEAD refused".to_owned())?;
    let cell = lean.seal_cell(pid, header, &duty, view_tag, &ct[..4], epk.as_bytes(), &ct[4..4 + shape.cap], &ct[4 + shape.cap..]);
    if cell.len() != c {
        return Err(format!("seal_cell refused ({} bytes, want {c})", cell.len()));
    }
    Ok(cell)
}

#[derive(Default, Debug)]
pub(crate) struct OpenStats {
    pub tried: u64,
    pub view_tag_hits: u64,
    pub aead_fail: u64,
    pub opened: u64,
}

/// Trial-decrypt one cell: `Some((frag, payload))` only when it was sealed to `me`.
pub(crate) fn try_open(lean: &Lean, pid: u8, cell: &[u8], me: &StaticSecret, me_pk: &[u8; 32], stats: &mut OpenStats) -> Option<([u8; 4], Vec<u8>)> {
    stats.tried += 1;
    let f = lean.open_cell(pid, cell)?;
    let epk: [u8; 32] = f.epk.as_slice().try_into().ok()?;
    let ss = me.diffie_hellman(&PublicKey::from(epk));
    if !ss.was_contributory() {
        return None;
    }
    let (k, view_tag) = derive(ss.as_bytes(), &epk, me_pk, &f.header);
    if view_tag != f.view_tag {
        return None;
    }
    stats.view_tag_hits += 1;
    let mut ct = Vec::with_capacity(f.frag.len() + f.payload.len() + f.tag.len());
    ct.extend_from_slice(&f.frag);
    ct.extend_from_slice(&f.payload);
    ct.extend_from_slice(&f.tag);
    match ChaCha20Poly1305::new(Key::from_slice(&k))
        .decrypt(Nonce::from_slice(&nonce(&f.header)), Payload { msg: &ct, aad: &aad(&f.header, &f.duty, f.view_tag, &f.epk) })
    {
        Ok(pt) if pt.len() >= 4 => {
            stats.opened += 1;
            Some((pt[..4].try_into().unwrap(), pt[4..].to_vec()))
        }
        _ => {
            stats.aead_fail += 1;
            None
        }
    }
}

pub(crate) fn frag_bytes(seq: u16, len: usize, last: bool) -> [u8; 4] {
    let l = len as u16 | if last { FINAL } else { 0 };
    let mut f = [0u8; 4];
    f[..2].copy_from_slice(&seq.to_be_bytes());
    f[2..].copy_from_slice(&l.to_be_bytes());
    f
}

pub(crate) fn parse_frag(f: &[u8; 4]) -> (u16, usize, bool) {
    let l = u16::from_be_bytes([f[2], f[3]]);
    (u16::from_be_bytes([f[0], f[1]]), (l & !FINAL) as usize, l & FINAL != 0)
}

// ------------------------------------------------------------------ the member loop

/// A message this member is sending.
struct Outgoing {
    id: String,
    to: String,
    to_pk: [u8; 32],
    seq: u16,
    data: Vec<u8>,
    /// bytes sent and not (yet) known to be dropped
    offset: usize,
    queued_ms: u64,
    order: u64,
    first_k: Option<u64>,
    fragments: u32,
    resends: u32,
}

/// What this member put in the cell it sent at tick `k`.
struct Sent {
    k: u64,
    cell: Vec<u8>,
    /// (message id, start, end) when the cell carried a fragment
    frag: Option<(String, usize, usize)>,
}

#[derive(Default)]
struct Counters {
    ticks: u64,
    missed_ticks: u64,
    late_emits: u64,
    frames_refused: u64,
    own_kept: u64,
    own_replaced: u64,
    resends: u64,
    epochs_seen: u64,
    records_checked: u64,
    record_roots_agree: u64,
    record_roots_mismatch: u64,
    records_missing: u64,
    delivered: u64,
    gaps: u64,
    sent_messages: u64,
    sent_fragments: u64,
    pad_cells: u64,
    real_cells: u64,
    /// seals that did not finish inside μ (the emission would wait for them)
    seal_overruns: u64,
}

/// What this member verified for one (epoch, tick): the root the frame carried and whether its own cell
/// was the committed one.
struct Observed {
    root: [u8; 32],
    own: &'static str,
}

struct Log {
    events: File,
}

impl Log {
    fn line(&mut self, s: String) {
        let _ = writeln!(self.events, "{} {s}", unix_ms());
    }
}

fn append_json(p: &Path, v: &Value) -> Result<()> {
    let mut f = OpenOptions::new().create(true).append(true).mode(0o600).open(p).map_err(|e| format!("{}: {e}", p.display()))?;
    writeln!(f, "{v}").map_err(|e| e.to_string())
}

/// `mini channel join ROOM`: the member loop, until the relay closes or `--ticks` TICKs.
fn join(mut args: Args) -> Result<()> {
    let (room, dir) = room_dir(&mut args)?;
    let lib = path(args.required("lean-lib")?);
    let spec = args.required("connect")?.to_string_lossy().into_owned();
    let domain: u16 = relay::num(&mut args, "domain")?;
    let leases_file = path(args.required("leases")?);
    let key_file = path(args.required("key")?);
    let roster_file = path(args.required("roster")?);
    let class = args.optional("class").map(|v| v.to_string_lossy().into_owned()).unwrap_or_else(|| "P1".into());
    let max_ticks: Option<u64> = args.optional("ticks").map(|v| v.to_string_lossy().parse()).transpose().map_err(|_| "--ticks".to_owned())?;
    let records_dir = args.optional("records-dir").map(path);
    args.finish()?;
    let member_pid: u8 = match class.as_str() {
        "P1" => 1,
        "P1phone" => 2,
        other => return Err(format!("--class {other}: this client speaks P1 and P1phone")),
    };

    private_dir(&dir)?;
    private_dir(&dir.join("outbox"))?;
    private_dir(&dir.join("outbox/taken"))?;
    private_dir(&dir.join("outbox/refused"))?;
    let me_sk = xkey(&dir)?;
    let me_pk = *PublicKey::from(&me_sk).as_bytes();
    let sk = SigningKey::from_bytes(&relay::secret_file(&key_file)?);
    // the lease: the relay's lease file row holding this member's ed25519 key (leases via the kernel: CH-LEASE)
    let leases = relay::parse_leases(&fs::read_to_string(&leases_file).map_err(|e| format!("leases: {e}"))?)?;
    let lease = leases
        .iter()
        .find(|l| l.key == sk.verifying_key().to_bytes())
        .ok_or("no lease in the relay's lease file holds this key")?
        .clone();
    let roster_text = fs::read_to_string(&roster_file).map_err(|e| format!("roster: {e}"))?;
    let roster = parse_roster(&roster_text)?;
    fs::write(dir.join("roster"), &roster_text).map_err(|e| format!("roster copy: {e}"))?;
    let me = roster.iter().find(|p| p.slot == lease.slot).ok_or("the roster names no member at this lease's slot")?.clone();
    if me.pk != me_pk {
        return Err(format!("the roster's key for {} is not this room's xkey", me.name));
    }

    let tl = Instant::now();
    let lean = Lean::load(&lib)?;
    let lean_init_ms = tl.elapsed().as_millis() as u64;
    let Joined { mut conn, pid, n, frame_key } = member_join(&spec, domain, lease.slot, lease.holder, &sk)?;
    let dprof = lean.profile(pid)?;
    let mprof = lean.profile(member_pid)?;
    if (mprof.c, mprof.rate_mhz, mprof.e, mprof.delta_relay_ms) != (dprof.c, dprof.rate_mhz, dprof.e, dprof.delta_relay_ms) {
        return Err(format!("--class {class} is not a variant of the domain's class {pid}"));
    }
    let c = dprof.c;
    let e_len = dprof.e;
    let tick = dprof.tick();
    let lead = Duration::from_millis(mprof.delta_ms);
    let mu = Duration::from_millis(mprof.mu_ms);
    let by_slot: HashMap<u32, Peer> = roster.iter().map(|p| (p.slot, p.clone())).collect();

    let mut log = Log { events: OpenOptions::new().create(true).append(true).mode(0o600).open(dir.join("events.log")).map_err(|e| e.to_string())? };
    log.line(format!(
        "joined room {room} as {} (slot {}, subject {}) class {class} (id {member_pid}, delta {} ms, mu {} ms) on domain {domain} class {pid} n {n}; lean init {lean_init_ms} ms",
        me.name, lease.slot, lease.holder, mprof.delta_ms, mprof.mu_ms
    ));
    let mut csv = BufWriter::new(File::create(dir.join("member.csv")).map_err(|e| e.to_string())?);
    writeln!(csv, "k,epoch,tick,rx_bytes,arrival_us,sig_ok,root_ok,own,cell,seal_us,seal_left_us,emit_late_us,tx_bytes,opened,view_tag_hits,aead_fail").map_err(|e| e.to_string())?;
    let mut wire = BufWriter::new(File::create(dir.join("wire.csv")).map_err(|e| e.to_string())?);
    writeln!(wire, "k,rx_bytes,tx_bytes").map_err(|e| e.to_string())?;

    let mut buf = vec![0u8; relay::tick_message_len(n, c)];
    let mut queue: Vec<Outgoing> = Vec::new();
    let mut seqs: HashMap<String, u16> = HashMap::new();
    let mut order = 0u64;
    let mut sent: Option<Sent> = None;
    let mut partial: HashMap<(u32, u16), Vec<u8>> = HashMap::new();
    let mut next_seq: HashMap<u32, u16> = HashMap::new();
    let mut observed: BTreeMap<(u64, u32), Observed> = BTreeMap::new();
    let mut last_epoch: Option<u64> = None;
    let mut last_k: Option<u64> = None;
    let mut cn = Counters::default();
    let mut stats = OpenStats::default();
    let start = Instant::now();
    let mut count = 0u64;

    loop {
        if conn.read_exact(&mut buf).is_err() {
            log.line("the relay closed the connection".into());
            break;
        }
        let a = Instant::now();
        let arrival_ms = unix_ms();
        let TickCheck { head, sig_ok, root_ok } = check_tick(&lean, pid, n, &frame_key, &buf)?;
        cn.ticks += 1;
        count += 1;
        if let Some(l) = last_k {
            if head.k > l + 1 {
                cn.missed_ticks += head.k - l - 1;
                log.line(format!("missed {} TICKs between {l} and {}", head.k - l - 1, head.k));
            }
        }
        last_k = Some(head.k);
        if last_epoch != Some(head.epoch) {
            cn.epochs_seen += 1;
            last_epoch = Some(head.epoch);
        }
        let vector = buf[FRAME_LEN..].to_vec();
        let frame_ok = sig_ok && root_ok && head.domain == domain;
        if !frame_ok {
            cn.frames_refused += 1;
            log.line(format!(
                "refused TICK {}: {}",
                head.k,
                if !sig_ok { "frameSignature" } else if !root_ok { "tickRoot" } else { "foreignDomain" }
            ));
        }

        // (2) the own-slot check on tick k−1's committed cell
        let mut own = "none";
        if let Some(s) = sent.take() {
            if s.k + 1 == head.k && frame_ok {
                let mine = &vector[lease.slot as usize * c..(lease.slot as usize + 1) * c];
                if mine == &s.cell[..] {
                    own = "kept";
                    cn.own_kept += 1;
                    if let Some((id, _, end)) = &s.frag {
                        if let Some(i) = queue.iter().position(|m| &m.id == id) {
                            if queue[i].offset == queue[i].data.len() && *end == queue[i].data.len() {
                                let m = queue.remove(i);
                                cn.sent_messages += 1;
                                append_json(&dir.join("sent.jsonl"), &json!({
                                    "id": m.id, "to": m.to, "seq": m.seq, "bytes": m.data.len(), "queued_unix_ms": m.queued_ms,
                                    "first_k": m.first_k, "final_k": s.k, "fragments": m.fragments, "resends": m.resends,
                                }))?;
                            }
                        }
                    }
                } else {
                    own = "replaced";
                    cn.own_replaced += 1;
                    match &s.frag {
                        Some((id, st, end)) => {
                            if let Some(m) = queue.iter_mut().find(|m| &m.id == id) {
                                if m.offset == *end {
                                    m.offset = *st;
                                    m.resends += 1;
                                    cn.resends += 1;
                                }
                            }
                            log.line(format!(
                                "own slot: the committed cell at tick {} is not the one I sent (own_omission_evident): re-queued {id} bytes {st}..{end}",
                                s.k
                            ));
                        }
                        None => log.line(format!("own slot: the committed cell at tick {} is not my padding (nothing to re-send)", s.k)),
                    }
                }
            } else if s.k + 1 != head.k {
                own = "unknown";
                log.line(format!("own slot: no TICK carried tick {}'s vector", s.k));
            }
        }
        // the root of tick k−1, verified on this frame, for the record check
        if head.k > 0 && frame_ok {
            let (pe, pt) = if head.tick > 0 { (head.epoch, head.tick - 1) } else { (head.epoch - 1, e_len as u32 - 1) };
            observed.insert((pe, pt), Observed { root: head.prev_root, own });
        }

        // (3) trial-decrypt the vector of tick k−1
        let mut opened_now = 0;
        if head.k > 0 && frame_ok {
            for slot in 0..n as u32 {
                if slot == lease.slot {
                    continue;
                }
                let cell = &vector[slot as usize * c..(slot as usize + 1) * c];
                if let Some((frag, data)) = try_open(&lean, pid, cell, &me_sk, &me_pk, &mut stats) {
                    opened_now += 1;
                    let (seq, len, last) = parse_frag(&frag);
                    let len = len.min(data.len());
                    let exp = next_seq.get(&slot).copied().unwrap_or(0);
                    let part = partial.entry((slot, seq)).or_default();
                    part.extend_from_slice(&data[..len]);
                    if last {
                        let body = partial.remove(&(slot, seq)).unwrap_or_default();
                        if seq != exp {
                            cn.gaps += 1;
                            log.line(format!("gap: from slot {slot} expected message #{exp}, got #{seq}"));
                        }
                        next_seq.insert(slot, seq.wrapping_add(1));
                        cn.delivered += 1;
                        let (pe, pt) = if head.tick > 0 { (head.epoch, head.tick - 1) } else { (head.epoch - 1, e_len as u32 - 1) };
                        let from = by_slot.get(&slot).map(|p| p.name.clone()).unwrap_or_else(|| format!("slot{slot}"));
                        append_json(&dir.join("inbox.jsonl"), &json!({
                            "k": head.k - 1, "epoch": pe, "tick": pt, "from": from, "from_slot": slot, "seq": seq,
                            "bytes": body.len(), "text": String::from_utf8_lossy(&body), "delivered_unix_ms": arrival_ms,
                        }))?;
                    }
                }
            }
        }

        // the record check: each epoch this member saw end, against the relay's published record
        if let Some(rd) = &records_dir {
            check_records(&lean, rd, domain, e_len, head.epoch, &mut observed, &mut cn, &mut log);
        }

        let done = max_ticks.is_some_and(|m| count >= m);
        let (mut seal_us, mut seal_slack, mut emit_late, mut tx, mut kind) = (0u128, 0i64, 0i64, 0usize, "-");
        if !done {
            let header = lean.header(domain, head.epoch, head.tick, lease.slot);
            let shape = shape_at(&lean, pid, &header, c)?;
            let emit_at = a + tick - lead;
            // (4) the seal cutoff: what is queued by `emission − μ` rides this tick; smallest first
            relay::sleep_until(emit_at - mu);
            take_outbox(&dir, &roster, &me, &mut queue, &mut seqs, &mut order, &mut log)?;
            let ts = Instant::now();
            let pick = queue
                .iter_mut()
                .filter(|m| m.offset < m.data.len())
                .min_by_key(|m| (m.data.len() - m.offset, m.order));
            let (cell, frag) = match pick {
                Some(m) => {
                    let st = m.offset;
                    let end = (st + shape.cap).min(m.data.len());
                    let last = end == m.data.len();
                    let cell = seal(&lean, pid, c, &header, shape, Some(&m.to_pk), frag_bytes(m.seq, end - st, last), &m.data[st..end])?;
                    m.offset = end;
                    m.fragments += 1;
                    m.first_k.get_or_insert(head.k);
                    cn.sent_fragments += 1;
                    cn.real_cells += 1;
                    kind = "real";
                    (cell, Some((m.id.clone(), st, end)))
                }
                None => {
                    let mut fill = vec![0u8; shape.cap];
                    relay::urandom(&mut fill)?;
                    let mut f = [0u8; 4];
                    relay::urandom(&mut f)?;
                    cn.pad_cells += 1;
                    kind = "pad";
                    (seal(&lean, pid, c, &header, shape, None, f, &fill)?, None)
                }
            };
            seal_us = ts.elapsed().as_micros();
            // (5)–(6): sealed inside the window μ, emitted at `arrival + T − δ` whatever it holds
            seal_slack = relay::diff_us(emit_at, Instant::now());
            if seal_slack < 0 {
                cn.seal_overruns += 1;
            }
            relay::sleep_until(emit_at);
            emit_late = relay::diff_us(Instant::now(), emit_at);
            if emit_late > (mprof.delta_ms as i64 - dprof.delta_relay_ms as i64) * 1000 {
                cn.late_emits += 1;
            }
            if conn.write_all(&cell).is_err() {
                log.line("the relay closed the connection before an emission".into());
                break;
            }
            tx = cell.len();
            sent = Some(Sent { k: head.k, cell, frag });
        }
        writeln!(
            csv,
            "{},{},{},{},{},{},{},{own},{kind},{seal_us},{seal_slack},{emit_late},{tx},{opened_now},{},{}",
            head.k,
            head.epoch,
            head.tick,
            buf.len(),
            (a - start).as_micros(),
            u8::from(sig_ok),
            u8::from(root_ok),
            stats.view_tag_hits,
            stats.aead_fail
        )
        .map_err(|e| e.to_string())?;
        csv.flush().map_err(|e| e.to_string())?;
        writeln!(wire, "{},{},{tx}", head.k, buf.len()).map_err(|e| e.to_string())?;
        wire.flush().map_err(|e| e.to_string())?;
        write_status(&dir, &room, &me, &lease, &class, mprof.delta_ms, lean_init_ms, head.k, &cn, &stats, queue.len())?;
        if done {
            break;
        }
    }
    write_status(&dir, &room, &me, &lease, &class, mprof.delta_ms, lean_init_ms, last_k.unwrap_or(0), &cn, &stats, queue.len())?;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn write_status(dir: &Path, room: &str, me: &Peer, lease: &relay::LeaseRow, class: &str, delta_ms: u64, lean_init_ms: u64, k: u64, cn: &Counters, st: &OpenStats, queued: usize) -> Result<()> {
    let v = json!({
        "type": "minidregg-channel-member-status-v1",
        "room": room, "name": me.name, "slot": lease.slot, "subject": lease.holder, "class": class, "deltaMs": delta_ms,
        "leanInitMs": lean_init_ms, "lastK": k, "ticks": cn.ticks, "missedTicks": cn.missed_ticks, "lateEmits": cn.late_emits,
        "framesRefused": cn.frames_refused, "ownKept": cn.own_kept, "ownReplaced": cn.own_replaced, "resends": cn.resends,
        "epochsSeen": cn.epochs_seen, "recordsChecked": cn.records_checked, "recordRootsAgree": cn.record_roots_agree,
        "recordRootsMismatch": cn.record_roots_mismatch, "recordsMissing": cn.records_missing,
        "delivered": cn.delivered, "gaps": cn.gaps, "sentMessages": cn.sent_messages, "sentFragments": cn.sent_fragments,
        "realCells": cn.real_cells, "padCells": cn.pad_cells, "sealOverruns": cn.seal_overruns, "queued": queued,
        "trialDecrypt": {"cells": st.tried, "viewTagHits": st.view_tag_hits, "aeadFail": st.aead_fail, "opened": st.opened},
    });
    let tmp = dir.join(".status.json.tmp");
    fs::write(&tmp, format!("{v}\n")).map_err(|e| e.to_string())?;
    fs::rename(&tmp, dir.join("status.json")).map_err(|e| e.to_string())
}

/// Check every epoch whose last tick this member has passed against the relay's published record:
/// each tick root must be the one verified on the frame, and this member's own cell the one it sent.
#[allow(clippy::too_many_arguments)]
fn check_records(lean: &Lean, rd: &Path, domain: u16, e_len: u64, current: u64, observed: &mut BTreeMap<(u64, u32), Observed>, cn: &mut Counters, log: &mut Log) {
    let epochs: Vec<u64> = observed.keys().map(|(e, _)| *e).filter(|e| *e < current).collect::<std::collections::BTreeSet<_>>().into_iter().collect();
    for e in epochs {
        let p = rd.join(format!("{e}.rec"));
        let Ok(record) = fs::read(&p) else {
            if current > e + 2 {
                cn.records_missing += 1;
                log.line(format!("record: epoch {e} was never published"));
                observed.retain(|(oe, _), _| *oe != e);
            }
            continue;
        };
        let roots = lean.record_roots(&record);
        let ticks: Vec<((u64, u32), Observed)> = {
            let keys: Vec<(u64, u32)> = observed.keys().filter(|(oe, _)| *oe == e).copied().collect();
            keys.into_iter().map(|key| (key, observed.remove(&key).unwrap())).collect()
        };
        cn.records_checked += 1;
        if roots.len() != 10 + 32 * e_len as usize
            || u16::from_be_bytes([roots[0], roots[1]]) != domain
            || u64::from_be_bytes(roots[2..10].try_into().unwrap()) != e
        {
            cn.record_roots_mismatch += 1;
            log.line(format!("record: epoch {e}: not a canonical record of this domain and epoch (refused)"));
            continue;
        }
        let (mut agree, mut differ, mut kept, mut replaced) = (0, Vec::new(), 0, Vec::new());
        for ((_, t), o) in &ticks {
            let r = &roots[10 + 32 * *t as usize..10 + 32 * (*t as usize + 1)];
            if r == o.root {
                agree += 1;
            } else {
                differ.push(*t);
            }
            match o.own {
                "kept" => kept += 1,
                "replaced" => replaced.push(*t),
                _ => {}
            }
        }
        cn.record_roots_agree += u64::from(differ.is_empty());
        cn.record_roots_mismatch += u64::from(!differ.is_empty());
        log.line(format!(
            "record: epoch {e}: {agree}/{} tick roots equal the roots on the signed frames{}; own cell committed at {kept} ticks{}",
            ticks.len(),
            if differ.is_empty() { String::new() } else { format!(", DIFFER at ticks {differ:?} (the relay signed one root and recorded another)") },
            if replaced.is_empty() { String::new() } else { format!(", replaced at ticks {replaced:?} (own_omission_evident against this record; re-sent)") }
        ));
    }
}

/// Move new `say` files from the outbox into the send queue (in name order: `say` names them by time).
fn take_outbox(dir: &Path, roster: &[Peer], me: &Peer, queue: &mut Vec<Outgoing>, seqs: &mut HashMap<String, u16>, order: &mut u64, log: &mut Log) -> Result<()> {
    let ob = dir.join("outbox");
    let mut names: Vec<String> = match fs::read_dir(&ob) {
        Ok(rd) => rd.flatten().map(|e| e.file_name().to_string_lossy().into_owned()).filter(|n| n.ends_with(".json")).collect(),
        Err(_) => return Ok(()),
    };
    names.sort();
    for name in names {
        let p = ob.join(&name);
        let v: Value = match fs::read_to_string(&p).ok().and_then(|t| serde_json::from_str(&t).ok()) {
            Some(v) => v,
            None => continue,
        };
        let to = v["to"].as_str().unwrap_or("").to_owned();
        let text = v["text"].as_str().unwrap_or("").to_owned();
        match roster.iter().find(|p| p.name == to) {
            Some(peer) if peer.name != me.name && !text.is_empty() => {
                let seq = seqs.entry(to.clone()).or_insert(0);
                queue.push(Outgoing {
                    id: name.trim_end_matches(".json").to_owned(),
                    to: to.clone(),
                    to_pk: peer.pk,
                    seq: *seq,
                    data: text.into_bytes(),
                    offset: 0,
                    queued_ms: v["queued_unix_ms"].as_u64().unwrap_or(0),
                    order: *order,
                    first_k: None,
                    fragments: 0,
                    resends: 0,
                });
                *seq = seq.wrapping_add(1);
                *order += 1;
                let _ = fs::rename(&p, ob.join("taken").join(&name));
            }
            _ => {
                log.line(format!("outbox: {name} refused: no other member named {to:?}, or empty text"));
                let _ = fs::rename(&p, ob.join("refused").join(&name));
            }
        }
    }
    Ok(())
}

/// `mini channel say ROOM @NAME TEXT`: queue a message for the member loop (it is sealed at the next tick).
fn say(mut args: Args) -> Result<()> {
    let (_, dir) = room_dir(&mut args)?;
    let to = args.required("to")?.to_string_lossy().trim_start_matches('@').to_owned();
    let text = args.required("text")?.to_string_lossy().into_owned();
    args.finish()?;
    let roster = parse_roster(&fs::read_to_string(dir.join("roster")).map_err(|_| "this room has no roster: run `mini channel join` first")?)?;
    if !roster.iter().any(|p| p.name == to) {
        return Err(format!("no member named @{to} in this room's roster"));
    }
    if text.len() > 65535 * 195 / 2 {
        return Err("message too long".into());
    }
    let now = unix_ms();
    let mut r = [0u8; 4];
    relay::urandom(&mut r)?;
    let id = format!("{now:013}-{}-{}", std::process::id(), relay::hex(&r));
    let ob = dir.join("outbox");
    let tmp = ob.join(format!(".{id}.tmp"));
    let mut f = OpenOptions::new().create_new(true).write(true).mode(0o600).open(&tmp).map_err(|e| format!("outbox: {e}"))?;
    writeln!(f, "{}", json!({"to": to, "text": text, "queued_unix_ms": now})).map_err(|e| e.to_string())?;
    drop(f);
    fs::rename(&tmp, ob.join(format!("{id}.json"))).map_err(|e| e.to_string())?;
    println!("{}", json!({"queued": id, "to": to, "bytes": text.len(), "queued_unix_ms": now}));
    Ok(())
}

fn render(v: &Value) -> String {
    format!(
        "[{}.{}] @{} #{}: {}",
        v["epoch"],
        v["tick"],
        v["from"].as_str().unwrap_or("?"),
        v["seq"],
        v["text"].as_str().unwrap_or("")
    )
}

/// `mini channel tail ROOM [--follow]`: what this member received and could open, in tick order.
fn tail(mut args: Args) -> Result<()> {
    let (_, dir) = room_dir(&mut args)?;
    let follow = match args.optional("follow").map(|v| v.to_string_lossy().into_owned()) {
        None => false,
        Some(v) if v == "true" || v == "1" => true,
        Some(v) if v == "false" || v == "0" => false,
        Some(v) => return Err(format!("--follow {v}: true or false")),
    };
    args.finish()?;
    let p = dir.join("inbox.jsonl");
    let mut pos = 0u64;
    loop {
        if let Ok(mut f) = File::open(&p) {
            f.seek(SeekFrom::Start(pos)).map_err(|e| e.to_string())?;
            let mut r = BufReader::new(f);
            let mut line = String::new();
            while r.read_line(&mut line).map_err(|e| e.to_string())? > 0 {
                if !line.ends_with('\n') {
                    break;
                }
                pos += line.len() as u64;
                if let Ok(v) = serde_json::from_str::<Value>(&line) {
                    println!("{}", render(&v));
                }
                line.clear();
            }
        }
        if !follow {
            return Ok(());
        }
        let _ = std::io::stdout().flush();
        std::thread::sleep(Duration::from_millis(200));
    }
}

/// `mini channel status ROOM`: the member loop's counters (missed ticks, re-sends, epochs, records).
fn status(mut args: Args) -> Result<()> {
    let (_, dir) = room_dir(&mut args)?;
    args.finish()?;
    let s = fs::read_to_string(dir.join("status.json")).map_err(|_| "no status yet: is `mini channel join` running?".to_owned())?;
    print!("{s}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frag_header_round_trips() {
        for (seq, len, last) in [(0u16, 195usize, false), (7, 3, true), (65535, 0, true)] {
            assert_eq!(parse_frag(&frag_bytes(seq, len, last)), (seq, len, last));
        }
        assert_eq!(frag_bytes(1, 195, true), [0, 1, 0x80, 195]);
    }

    #[test]
    fn roster_parses_and_refuses() {
        let k = relay::hex(&[5u8; 32]);
        let r = parse_roster(&format!("# name slot key\n@alice 0 {k}\nbob 1 {k}\n")).unwrap();
        assert_eq!(r[0].name, "alice");
        assert_eq!(r[1].slot, 1);
        assert!(parse_roster(&format!("a 0 {k}\na 1 {k}\n")).is_err(), "a repeated name is refused");
        assert!(parse_roster(&format!("a 0 {k}\nb 0 {k}\n")).is_err(), "a repeated slot is refused");
        assert!(parse_roster("a 0 abcd\n").is_err(), "a short key is refused");
    }

    #[test]
    fn key_derivation_separates_recipients_and_headers() {
        let ss = [1u8; 32];
        let epk = [2u8; 32];
        let (k1, v1) = derive(&ss, &epk, &[3u8; 32], &[0, 7, 0, 1, 0, 2, 0, 0]);
        let (k2, _) = derive(&ss, &epk, &[4u8; 32], &[0, 7, 0, 1, 0, 2, 0, 0]);
        let (k3, _) = derive(&ss, &epk, &[3u8; 32], &[0, 7, 0, 1, 0, 3, 0, 0]);
        assert_ne!(k1, k2);
        assert_ne!(k1, k3);
        assert_eq!(derive(&ss, &epk, &[3u8; 32], &[0, 7, 0, 1, 0, 2, 0, 0]), (k1, v1));
    }

    /// The construction without the Lean placement: a recipient opens, a non-recipient's view tag or
    /// AEAD refuses, and a flipped ciphertext byte is refused.
    #[test]
    fn x25519_aead_recipient_opens_non_recipient_cannot() {
        let bob = StaticSecret::from([9u8; 32]);
        let bob_pk = *PublicKey::from(&bob).as_bytes();
        let carol = StaticSecret::from([10u8; 32]);
        let carol_pk = *PublicKey::from(&carol).as_bytes();
        let header = [0u8, 7, 0, 1, 0, 2, 0, 0];
        let duty: [u8; 0] = [];
        let esk = StaticSecret::from([11u8; 32]);
        let epk = *PublicKey::from(&esk).as_bytes();
        let (k, vt) = derive(esk.diffie_hellman(&PublicKey::from(bob_pk)).as_bytes(), &epk, &bob_pk, &header);
        let mut pt = frag_bytes(0, 5, true).to_vec();
        pt.extend_from_slice(b"hello");
        let ct = ChaCha20Poly1305::new(Key::from_slice(&k))
            .encrypt(Nonce::from_slice(&nonce(&header)), Payload { msg: &pt, aad: &aad(&header, &duty, vt, &epk) })
            .unwrap();
        let (kb, vb) = derive(bob.diffie_hellman(&PublicKey::from(epk)).as_bytes(), &epk, &bob_pk, &header);
        assert_eq!(vb, vt);
        let opened = ChaCha20Poly1305::new(Key::from_slice(&kb))
            .decrypt(Nonce::from_slice(&nonce(&header)), Payload { msg: &ct, aad: &aad(&header, &duty, vt, &epk) })
            .unwrap();
        assert_eq!(opened, pt);
        let (kc, _) = derive(carol.diffie_hellman(&PublicKey::from(epk)).as_bytes(), &epk, &carol_pk, &header);
        assert!(ChaCha20Poly1305::new(Key::from_slice(&kc))
            .decrypt(Nonce::from_slice(&nonce(&header)), Payload { msg: &ct, aad: &aad(&header, &duty, vt, &epk) })
            .is_err());
        let mut bad = ct.clone();
        bad[0] ^= 1;
        assert!(ChaCha20Poly1305::new(Key::from_slice(&kb))
            .decrypt(Nonce::from_slice(&nonce(&header)), Payload { msg: &bad, aad: &aad(&header, &duty, vt, &epk) })
            .is_err());
    }
}
