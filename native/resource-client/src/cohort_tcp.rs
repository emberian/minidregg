//! Fixed enrolled-link TCP records for the guarded PQ cohort. Every link is
//! admitted by the public cohort roster through a signed, challenge-bound
//! ML-KEM enrollment (MCE2); this layer does not manufacture Mini outcomes.
use crate::scheduled_transport::{directory, persist, random, read_private};
use crate::{transport, Args, Result};
use aws_lc_rs::kem::{Ciphertext, DecapsulationKey, EncapsulationKey, ML_KEM_768};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use chacha20poly1305::{
    aead::{Aead, Payload},
    KeyInit, XChaCha20Poly1305, XNonce,
};
use sha2::{Digest, Sha256};
use std::{
    fs::{File, OpenOptions},
    io::{Read, Write},
    net::{TcpListener, TcpStream},
    os::unix::fs::OpenOptionsExt,
    path::{Path, PathBuf},
    thread,
    time::{Duration, SystemTime, UNIX_EPOCH},
};

const DOMAIN: &[u8] = b"Mini/PQ-cohort/fixed-link/v2";
const HEADER: usize = 4 + 32 + 8;
const OVERHEAD: usize = HEADER + 24 + 16;

#[derive(Clone, Debug)]
struct Profile {
    generation: [u8; 16],
    slot: u16,
    purpose: u8, // contribution, batch0..3, broadcast
    width: usize,
    payload: usize,
    origin: u64,
    tick: u64,
    processing: u64,
    first: u64,
    epochs: u64,
}
impl Profile {
    fn capacity(&self) -> usize {
        let manifest = 18 + 160 * self.width + 128;
        match self.purpose {
            0 => self.payload + 4640 + 160,
            1..=4 => {
                manifest + 19 + self.width * (self.payload + (5 - self.purpose as usize) * 1160)
            }
            5 => 19 + self.width * self.payload,
            _ => 0,
        }
    }
    fn check(&self) -> Result<()> {
        if !(2..=64).contains(&self.width)
            || !(1024..=262144).contains(&self.payload)
            || !(100..=60000).contains(&self.tick)
            || self.purpose > 5
            || !(1..=32).contains(&self.processing)
            || !(1..=4096).contains(&self.epochs)
            || self.slot as usize >= self.width
        {
            return Err("fixed cohort public profile bounds refused".into());
        }
        self.when(
            self.first
                .checked_add(self.epochs)
                .ok_or("cohort lifetime exhausted")?,
        )?;
        Ok(())
    }
    fn when(&self, epoch: u64) -> Result<u64> {
        epoch
            .checked_add(self.purpose as u64 * self.processing + 1)
            .and_then(|v| v.checked_mul(self.tick))
            .and_then(|v| v.checked_add(self.origin))
            .ok_or_else(|| "fixed cohort schedule lifetime exhausted".into())
    }
    fn identity(&self) -> Vec<u8> {
        let mut v = DOMAIN.to_vec();
        v.extend_from_slice(&self.generation);
        v.extend_from_slice(&self.slot.to_le_bytes());
        v.push(self.purpose);
        for n in [
            self.width as u64,
            self.payload as u64,
            self.origin,
            self.tick,
            self.processing,
            self.first,
            self.epochs,
        ] {
            v.extend_from_slice(&n.to_le_bytes());
        }
        v
    }
    fn digest(&self) -> [u8; 32] {
        Sha256::digest(self.identity()).into()
    }
}

fn now_ms() -> Result<u64> {
    let n = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|_| "clock before epoch")?
        .as_millis();
    n.try_into()
        .map_err(|_| "public clock lifetime exhausted".into())
}
fn wait(when: u64) -> Result<()> {
    let n = now_ms()?;
    // Public OS scheduling tolerance is a bound, not workload-dependent grace.
    // Sleeping may wake a millisecond late; zero tolerance spuriously killed
    // every simultaneous all-cover link in the sustained receiving experiment.
    if n > when.saturating_add(25) {
        return Err("missed public link slot; no catch-up burst".into());
    }
    if n < when {
        thread::sleep(Duration::from_millis(when - n));
    }
    if now_ms()? > when.saturating_add(25) {
        return Err("public clock scheduling bound exceeded".into());
    }
    Ok(())
}
fn exact(root: &Path, name: &str, body: &[u8]) -> Result<()> {
    let path = root.join(name);
    if path.exists() {
        if read_private(&path, body.len())? != body {
            return Err("changed retained link identity; preserve existing obligation".into());
        }
        Ok(())
    } else {
        persist(&path, body)
    }
}
// Empty/late output becomes physical-unavailable, not a native Pending or a
// synthetic source receipt. A contribution producer supplies a valid cover
// packet before its deadline through the live client API.
fn read_record(records: &Path, epoch: u64, capacity: usize) -> Result<Option<Vec<u8>>> {
    let record = records.join(format!("epoch-{epoch}.record"));
    if record.exists() {
        // The immutable file can become visible between hard-link publication
        // and its directory fsync. Only the post-fsync availability token permits
        // consumption. Losing that token on crash loses availability, not the
        // original source journal or authority, and never creates another effect.
        let ready = records.join(format!("epoch-{epoch}.adopted"));
        if !ready.exists() {
            return Ok(None);
        }
        read_private(&ready, 0)?;
        let v = read_private(&record, capacity + 5)?;
        if v.len() != capacity + 5 {
            return Err("retained authenticated record shape".into());
        }
        if v[0] == 0 && v[1..].iter().all(|b| *b == 0) {
            return Ok(None);
        }
        if v[0] != 1 || u32::from_le_bytes(v[1..5].try_into().unwrap()) as usize != capacity {
            return Err("retained authenticated record marker".into());
        }
        return Ok(Some(v[5..].to_vec()));
    }
    let body = records.join(format!("epoch-{epoch}.payload"));
    if body.exists() {
        return Ok(Some(read_private(&body, capacity)?));
    }
    Ok(None)
}
fn prepare_live_wire(
    source: &Path,
    p: &Profile,
    key: &[u8; 32],
    epoch: u64,
) -> Result<Option<Vec<u8>>> {
    let Some(body) = read_record(source, epoch, p.capacity())? else {
        return Ok(None);
    };
    if body.len() != p.capacity() {
        return Err("guarded cohort segment exact shape".into());
    }
    let mut plain = vec![0; p.capacity() + 5];
    plain[0] = 1;
    plain[1..5].copy_from_slice(&(body.len() as u32).to_le_bytes());
    plain[5..].copy_from_slice(&body);
    // The original producer journals remain authoritative and durable. This
    // fresh outer wire is physical preparation, never a source receipt.
    // Future-only resume cannot retransmit an already released epoch; a crash
    // before release may reseal the same exact inner body with a fresh nonce.
    seal(p, key, epoch, &plain).map(Some)
}
fn seal(p: &Profile, key: &[u8; 32], epoch: u64, plain: &[u8]) -> Result<Vec<u8>> {
    if plain.len() != p.capacity() + 5 {
        return Err("fixed cohort record shape".into());
    }
    let mut header = b"MCL1".to_vec();
    header.extend_from_slice(&p.digest());
    header.extend_from_slice(&epoch.to_le_bytes());
    let nonce = random::<24>()?;
    let mut context = p.identity();
    context.extend_from_slice(&header);
    let derived: [u8; 32] = ring::hmac::sign(
        &ring::hmac::Key::new(ring::hmac::HMAC_SHA256, key),
        &context,
    )
    .as_ref()
    .try_into()
    .unwrap();
    let cipher = XChaCha20Poly1305::new((&derived).into())
        .encrypt(
            XNonce::from_slice(&nonce),
            Payload {
                msg: plain,
                aad: &header,
            },
        )
        .map_err(|_| "cohort link seal")?;
    header.extend_from_slice(&nonce);
    header.extend_from_slice(&cipher);
    Ok(header)
}
fn open(p: &Profile, key: &[u8; 32], epoch: u64, wire: &[u8]) -> Result<Vec<u8>> {
    if wire.len() != p.capacity() + 5 + OVERHEAD
        || &wire[..4] != b"MCL1"
        || wire[4..36] != p.digest()
        || wire[36..44] != epoch.to_le_bytes()
    {
        return Err("fixed cohort link profile/epoch/shape mismatch".into());
    }
    let mut context = p.identity();
    context.extend_from_slice(&wire[..HEADER]);
    let derived: [u8; 32] = ring::hmac::sign(
        &ring::hmac::Key::new(ring::hmac::HMAC_SHA256, key),
        &context,
    )
    .as_ref()
    .try_into()
    .unwrap();
    let plain = XChaCha20Poly1305::new((&derived).into())
        .decrypt(
            XNonce::from_slice(&wire[HEADER..HEADER + 24]),
            Payload {
                msg: &wire[HEADER + 24..],
                aad: &wire[..HEADER],
            },
        )
        .map_err(|_| "cohort link authentication refused")?;
    let n = u32::from_le_bytes(plain[1..5].try_into().unwrap()) as usize;
    if !((plain[0] == 0 && n == 0 && plain[5..].iter().all(|b| *b == 0))
        || (plain[0] == 1 && n == p.capacity()))
    {
        return Err("fixed cohort private record shape refused".into());
    }
    Ok(plain)
}
fn adopt(_root: &Path, output: &Path, _p: &Profile, epoch: u64, plain: &[u8]) -> Result<()> {
    let record = output.join(format!("epoch-{epoch}.record"));
    if record.exists() {
        if read_private(&record, plain.len())? != plain {
            return Err("changed retained link identity; preserve existing obligation".into());
        }
        // Exact readback alone does not attest a prior uncertain directory fsync.
        File::open(&record)
            .and_then(|f| f.sync_all())
            .map_err(|e| e.to_string())?;
        File::open(output)
            .and_then(|f| f.sync_all())
            .map_err(|e| e.to_string())?;
    } else {
        persist(&record, plain)?;
    }
    // Published AFTER durable adoption. This token is deliberately not another
    // synced journal/receipt; a lost token is fail-closed until exact re-adoption.
    let ready = output.join(format!("epoch-{epoch}.adopted"));
    if ready.exists() {
        read_private(&ready, 0)?;
    } else {
        OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(ready)
            .map_err(|e| e.to_string())?;
    }
    Ok(())
}
fn send(
    mut stream: TcpStream,
    source: &Path,
    p: &Profile,
    key: &[u8; 32],
    start: u64,
) -> Result<()> {
    stream.set_nodelay(true).map_err(|e| e.to_string())?;
    stream
        .set_write_timeout(Some(Duration::from_millis(p.tick / 2)))
        .map_err(|e| e.to_string())?;
    let count = (p.first + p.epochs - start) as usize;
    if count
        .checked_mul(p.capacity() + 5 + OVERHEAD)
        .ok_or("cover inventory overflow")?
        > 64 * 1024 * 1024
    {
        return Err(
            "public in-memory wire lifetime exceeds64MiB; choose shorter enrolled lifetime".into(),
        );
    }
    // Seal the durable valid client/broadcast cover inventory, or a physical-
    // unavailable record, once before the public lifetime. The link key is this
    // connection's enrolled key, so outer wires are never persisted: the inner
    // cover stays the durable inventory and a resumed link reseals it fresh.
    // Neither disk nor producer runs in the clock loop.
    let mut fallback = Vec::with_capacity(count);
    for epoch in start..p.first + p.epochs {
        let wire = {
            let mut plain = vec![0; p.capacity() + 5];
            if p.purpose == 0 || p.purpose == 5 {
                let cover_path = source.join(format!("epoch-{epoch}.cover"));
                // Final dummy inventory is a fixed public-capacity producer,
                // independent of real custody/native work. Admit it completely
                // before this link's original first send, never move the clock.
                if p.purpose == 5 {
                    let cutoff = p
                        .when(start)?
                        .checked_sub(p.tick)
                        .ok_or("broadcast inventory cutoff")?;
                    while !cover_path.exists() && now_ms()? < cutoff {
                        thread::sleep(Duration::from_millis(5));
                    }
                }
                let cover = read_private(&cover_path, p.capacity())?;
                if cover.len() != p.capacity() {
                    return Err("complete enrolled cover inventory required".into());
                }
                if p.purpose == 5 {
                    crate::pq_mailbox::live_validate_broadcast(epoch, p.width, p.payload, &cover)?;
                }
                plain[0] = 1;
                plain[1..5].copy_from_slice(&(cover.len() as u32).to_le_bytes());
                plain[5..].copy_from_slice(&cover);
            }
            seal(p, key, epoch, &plain)?
        };
        open(p, key, epoch, &wire)?;
        fallback.push(wire);
    }
    let (tx, rx) = std::sync::mpsc::channel();
    let source = source.to_path_buf();
    let profile = p.clone();
    let key = *key;
    thread::spawn(move || {
        for epoch in start..profile.first + profile.epochs {
            let prepared: Result<Vec<u8>> = (|| {
                let release = profile.when(epoch)?;
                let begin = release
                    .checked_sub(profile.tick)
                    .ok_or("preparation clock exhausted")?;
                let cutoff = release
                    .checked_sub(25)
                    .ok_or("preparation cutoff exhausted")?;
                wait(begin)?;
                // Readiness may arrive after a half-tick sample. A fixed public
                // cutoff bounds preparation while the independent clock always
                // chooses one prepared wire or its retained durable fallback.
                while now_ms()? < cutoff {
                    if let Some(wire) = prepare_live_wire(&source, &profile, &key, epoch)? {
                        open(&profile, &key, epoch, &wire)?;
                        return Ok(wire);
                    }
                    thread::sleep(Duration::from_millis(5));
                }
                Err("no physical output before public cutoff".into())
            })();
            if let Ok(wire) = prepared {
                if tx.send((epoch, wire)).is_err() {
                    break;
                }
            }
        }
    });
    let mut ready = std::collections::BTreeMap::new();
    // Fixed epoch range, no disk/crypto/log persistence in emission loop.
    for epoch in start..p.first + p.epochs {
        wait(p.when(epoch)?)?;
        while let Ok((n, wire)) = rx.try_recv() {
            if n >= epoch {
                ready.insert(n, wire);
            }
        }
        let wire = ready
            .remove(&epoch)
            .unwrap_or_else(|| std::mem::take(&mut fallback[(epoch - start) as usize]));
        stream
            .write_all(&wire)
            .map_err(|e| format!("declared link fault; preserve source obligation: {e}"))?;
    }
    Ok(())
}
// LINK ENROLLMENT (MCE2). Every fixed link is admitted only by the public
// cohort roster: the sender proves the roster's native Ed25519 key for this
// exact (generation, slot, phase, profile, roster, start) under a FRESH
// receiver challenge, and the link key comes from two ML-KEM-768
// encapsulations -- one to the receiver's roster-pinned static key (only the
// enrolled receiver can answer, which authenticates it to the sender) and one
// to a per-connection ephemeral key (a later static-key compromise does not
// open recorded link traffic). No operator-provisioned shared secret exists.
// Native signatures stay classical Ed25519: this is NOT a PQ authentication.
const KEM_PUBLIC: usize = 1184;
const KEM_SECRET: usize = 2400;
const KEM_CIPHER: usize = 1088;
const CHALLENGE: usize = 4 + 32 + KEM_PUBLIC;
const RESPONSE: usize = 2 * KEM_CIPHER + 64;
const ACK: usize = 32;
const ROSTER_LIMIT: usize = 1 << 20;
// Public handshake bound per read/write. A LAN round trip must fit; a peer that
// withholds is an availability fault and the receiver re-accepts.
const HANDSHAKE_MS: u64 = 3000;

struct RosterEntry {
    native: VerifyingKey,
    link_kem: Vec<u8>,
}
/// The public fixed cohort: `width` members (phase-0 senders, phase-5
/// receivers) and five operators (registrar, relay0, relay1, relay2, mailbox).
/// Its exact-byte digest enters every link transcript and pin, so every link
/// endpoint must hold the SAME roster or no link opens.
struct Roster {
    generation: [u8; 16],
    members: Vec<RosterEntry>,
    operators: Vec<RosterEntry>,
    digest: [u8; 32],
}
fn roster_entry(v: &serde_json::Value) -> Result<RosterEntry> {
    let field = |name: &str| -> Result<Vec<u8>> {
        crate::decode_hex(v[name].as_str().ok_or("roster entry field must be hex text")?)
    };
    let native: [u8; 32] = field("native")?
        .try_into()
        .map_err(|_| "roster native key must be 32 bytes")?;
    let native =
        VerifyingKey::from_bytes(&native).map_err(|_| "roster native key is not an Ed25519 point")?;
    if native.is_weak() {
        return Err("roster native key is a weak Ed25519 point".into());
    }
    let link_kem = field("linkKem")?;
    if link_kem.len() != KEM_PUBLIC {
        return Err("roster link key must be an ML-KEM-768 encapsulation key".into());
    }
    EncapsulationKey::new(&ML_KEM_768, &link_kem).map_err(|_| "roster link key refused")?;
    if v.as_object().map(|o| o.len()) != Some(2) {
        return Err("roster entry has exactly native and linkKem".into());
    }
    Ok(RosterEntry { native, link_kem })
}
fn parse_roster(bytes: &[u8]) -> Result<Roster> {
    let v: serde_json::Value =
        serde_json::from_slice(bytes).map_err(|e| format!("cohort roster JSON: {e}"))?;
    if v["type"] != "minidregg-cohort-roster-v1" || v.as_object().map(|o| o.len()) != Some(5) {
        return Err("cohort roster type/shape refused".into());
    }
    let generation: [u8; 16] =
        crate::decode_hex(v["generation"].as_str().ok_or("roster generation must be hex")?)?
            .try_into()
            .map_err(|_| "roster generation must be 16 bytes")?;
    let list = |name: &str| -> Result<Vec<RosterEntry>> {
        v[name]
            .as_array()
            .ok_or("roster list missing")?
            .iter()
            .map(roster_entry)
            .collect()
    };
    let members = list("members")?;
    let operators = list("operators")?;
    if v["width"].as_u64() != Some(members.len() as u64)
        || !(2..=64).contains(&members.len())
        || operators.len() != 5
    {
        return Err("roster needs width members and exactly five operators".into());
    }
    let all = members.iter().chain(operators.iter());
    let natives: std::collections::BTreeSet<_> = all.clone().map(|e| e.native.to_bytes()).collect();
    let kems: std::collections::BTreeSet<_> = all.map(|e| e.link_kem.clone()).collect();
    if natives.len() != members.len() + 5 || kems.len() != members.len() + 5 {
        return Err("roster native and link keys must be pairwise distinct".into());
    }
    Ok(Roster {
        generation,
        members,
        operators,
        digest: Sha256::digest(bytes).into(),
    })
}
fn read_roster(path: &Path) -> Result<Roster> {
    parse_roster(&read_private(path, ROSTER_LIMIT)?)
}
impl Roster {
    /// The roster must describe exactly this public profile's cohort.
    fn admits(&self, p: &Profile) -> Result<()> {
        if self.generation != p.generation
            || self.members.len() != p.width
            || ((1..=4).contains(&p.purpose) && p.slot != 0)
        {
            return Err("cohort roster does not describe this link profile".into());
        }
        Ok(())
    }
    /// Phase 0 is member `slot`; phase k>0 is sent by operator k-1.
    fn sender(&self, p: &Profile) -> &VerifyingKey {
        match p.purpose {
            0 => &self.members[p.slot as usize].native,
            k => &self.operators[k as usize - 1].native,
        }
    }
    /// Phase k<5 is received by operator k; phase 5 by member `slot`.
    fn receiver(&self, p: &Profile) -> &[u8] {
        match p.purpose {
            5 => &self.members[p.slot as usize].link_kem,
            k => &self.operators[k as usize].link_kem,
        }
    }
}
fn link_pin(root: &Path, p: &Profile, roster: &Roster, role: &[u8]) -> Result<()> {
    // A retained link of an earlier codec, roster or role refuses to resume.
    let mut b = b"Mini/cohort-startup:MCE2/v1".to_vec();
    b.extend_from_slice(&p.identity());
    b.extend_from_slice(&roster.digest);
    b.extend_from_slice(&Sha256::digest(role));
    exact(root, "profile", &b)
}
fn worker_pin(root: &Path, p: &Profile) -> Result<()> {
    let mut b = b"Mini/cohort-startup:worker/v2".to_vec();
    b.extend_from_slice(&p.identity());
    exact(root, "profile", &b)
}
/// Written by the receiving end of an enrolled link into its record directory
/// before the first adoption. A worker consumes records only from a directory
/// whose marker binds the exact upstream link to the roster's sender.
fn enrolled_marker(p: &Profile, roster: &Roster) -> Vec<u8> {
    let mut b = b"Mini/cohort-enrolled-link/v1".to_vec();
    b.extend_from_slice(&p.identity());
    b.extend_from_slice(&roster.digest);
    b.extend_from_slice(roster.sender(p).as_bytes());
    b
}
fn check_enrolled_input(dir: &Path, link: &Profile, roster: &Roster) -> Result<()> {
    let want = enrolled_marker(link, roster);
    if read_private(&dir.join("enrolled-link"), want.len())? != want {
        return Err("input directory is not the roster-enrolled upstream link".into());
    }
    Ok(())
}
fn enrollment_transcript(
    p: &Profile,
    roster: &Roster,
    start: u64,
    challenge: &[u8],
    response_kems: &[u8],
) -> Vec<u8> {
    let mut t = b"Mini/cohort-link-enrollment/v2".to_vec();
    t.extend_from_slice(&p.identity());
    t.extend_from_slice(&roster.digest);
    t.extend_from_slice(&start.to_le_bytes());
    t.extend_from_slice(challenge);
    t.extend_from_slice(response_kems);
    t
}
fn link_keys(transcript: &[u8], signature: &[u8], fixed: &[u8], fresh: &[u8]) -> ([u8; 32], [u8; 32]) {
    let mut secret = b"Mini/cohort-link-secret/v2".to_vec();
    secret.extend_from_slice(fixed);
    secret.extend_from_slice(fresh);
    let secret = Sha256::digest(&secret);
    let mut bound = Sha256::new();
    bound.update(transcript);
    bound.update(signature);
    let bound = bound.finalize();
    let tag = |label: &[u8], key: &[u8]| -> [u8; 32] {
        let mut m = label.to_vec();
        m.extend_from_slice(&bound);
        ring::hmac::sign(&ring::hmac::Key::new(ring::hmac::HMAC_SHA256, key), &m)
            .as_ref()
            .try_into()
            .unwrap()
    };
    let key = tag(b"Mini/cohort-link-key/v2", &secret);
    let ack = tag(b"Mini/cohort-link-ack/v2", &key);
    (key, ack)
}
fn handshake_timeouts(stream: &TcpStream, ms: u64) -> Result<()> {
    let t = Some(Duration::from_millis(ms.max(1)));
    stream.set_read_timeout(t).map_err(|e| e.to_string())?;
    stream.set_write_timeout(t).map_err(|e| e.to_string())
}
fn enroll_sender(
    stream: &mut TcpStream,
    p: &Profile,
    roster: &Roster,
    signing: &SigningKey,
    start: u64,
) -> Result<[u8; 32]> {
    if signing.verifying_key() != *roster.sender(p) {
        return Err("this native key is not the roster sender of this link".into());
    }
    handshake_timeouts(stream, HANDSHAKE_MS)?;
    let mut challenge = [0; CHALLENGE];
    stream
        .read_exact(&mut challenge)
        .map_err(|e| e.to_string())?;
    if &challenge[..4] != b"MCE2" {
        return Err("enrollment challenge framing refused".into());
    }
    let fresh = EncapsulationKey::new(&ML_KEM_768, &challenge[36..])
        .map_err(|_| "enrollment ephemeral key refused")?;
    let fixed = EncapsulationKey::new(&ML_KEM_768, roster.receiver(p))
        .map_err(|_| "roster receiver key refused")?;
    let (fixed_ct, fixed_ss) = fixed.encapsulate().map_err(|_| "ML-KEM encapsulation")?;
    let (fresh_ct, fresh_ss) = fresh.encapsulate().map_err(|_| "ML-KEM encapsulation")?;
    let mut kems = fixed_ct.as_ref().to_vec();
    kems.extend_from_slice(fresh_ct.as_ref());
    let transcript = enrollment_transcript(p, roster, start, &challenge, &kems);
    let signature = signing.sign(&transcript).to_bytes();
    let mut response = kems;
    response.extend_from_slice(&signature);
    stream.write_all(&response).map_err(|e| e.to_string())?;
    let (key, ack) = link_keys(&transcript, &signature, fixed_ss.as_ref(), fresh_ss.as_ref());
    let mut got = [0; ACK];
    stream.read_exact(&mut got).map_err(|e| e.to_string())?;
    if !constant_eq(&got, &ack) {
        return Err("enrollment receiver authentication refused".into());
    }
    Ok(key)
}
fn constant_eq(a: &[u8], b: &[u8]) -> bool {
    a.len() == b.len() && a.iter().zip(b).fold(0u8, |acc, (x, y)| acc | (x ^ y)) == 0
}
/// One verified enrollment: the authenticated stream, its link key, and the
/// sender's signed transcript (retained as the registrar's admission evidence).
struct Enrolled {
    stream: TcpStream,
    key: [u8; 32],
    signed: Vec<u8>,
}
fn answer_enrollment(
    stream: &mut TcpStream,
    p: &Profile,
    roster: &Roster,
    fixed: &DecapsulationKey,
    start: u64,
) -> Option<([u8; 32], Vec<u8>)> {
    let fresh = DecapsulationKey::generate(&ML_KEM_768).ok()?;
    let fresh_public = fresh.encapsulation_key().ok()?.key_bytes().ok()?;
    let mut challenge = b"MCE2".to_vec();
    challenge.extend_from_slice(&random::<32>().ok()?);
    challenge.extend_from_slice(fresh_public.as_ref());
    stream.write_all(&challenge).ok()?;
    let mut response = [0; RESPONSE];
    stream.read_exact(&mut response).ok()?;
    let (kems, signature) = response.split_at(2 * KEM_CIPHER);
    let transcript = enrollment_transcript(p, roster, start, &challenge, kems);
    let signature_bytes: [u8; 64] = signature.try_into().ok()?;
    roster
        .sender(p)
        .verify_strict(&transcript, &Signature::from_bytes(&signature_bytes))
        .ok()?;
    let fixed_ss = fixed
        .decapsulate(Ciphertext::from(&kems[..KEM_CIPHER]))
        .ok()?;
    let fresh_ss = fresh
        .decapsulate(Ciphertext::from(&kems[KEM_CIPHER..]))
        .ok()?;
    let (key, ack) = link_keys(&transcript, signature, fixed_ss.as_ref(), fresh_ss.as_ref());
    stream.write_all(&ack).ok()?;
    let mut signed = transcript;
    signed.extend_from_slice(signature);
    Some((key, signed))
}
/// Accept exactly one roster-enrolled sender. Garbage, a wrong key, a replayed
/// response to an old challenge or a stalled peer is dropped and the listener
/// re-accepts until the public start deadline; none consumes the link.
fn accept_enrolled(
    listener: &TcpListener,
    p: &Profile,
    roster: &Roster,
    fixed: &DecapsulationKey,
    start: u64,
) -> Result<Enrolled> {
    listener.set_nonblocking(true).map_err(|e| e.to_string())?;
    let until = p.when(start)?;
    loop {
        if now_ms()? >= until {
            return Err("public enrolled connection deadline exhausted".into());
        }
        match listener.accept() {
            Ok((mut stream, _)) => {
                // BSD sockets inherit O_NONBLOCK from the listener; Linux does not.
                stream.set_nonblocking(false).map_err(|e| e.to_string())?;
                let remaining = until.saturating_sub(now_ms()?);
                if remaining == 0 {
                    continue;
                }
                handshake_timeouts(&stream, remaining.min(HANDSHAKE_MS))?;
                if let Some((key, signed)) = answer_enrollment(&mut stream, p, roster, fixed, start) {
                    return Ok(Enrolled {
                        stream,
                        key,
                        signed,
                    });
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                thread::sleep(Duration::from_millis(1))
            }
            Err(e) => return Err(format!("public listener fault: {e}")),
        }
    }
}
fn receive(
    mut stream: TcpStream,
    root: &Path,
    output: &Path,
    p: &Profile,
    key: &[u8; 32],
    start: u64,
) -> Result<()> {
    let count = (p.first + p.epochs - start) as usize;
    if count
        .checked_mul(p.capacity() + 5)
        .ok_or("receive inventory overflow")?
        > 64 * 1024 * 1024
    {
        return Err("public retained receive queue exceeds64MiB".into());
    }
    stream
        .set_read_timeout(Some(Duration::from_millis(p.tick / 2)))
        .map_err(|e| e.to_string())?;
    // Durable adoption owns its independent bounded queue; no consumer sees a
    // record before fsync. Disk work cannot stall the fixed receive clock.
    let (tx, rx) = std::sync::mpsc::sync_channel::<(u64, Vec<u8>)>(count);
    thread::scope(|scope| {
        let writer = scope.spawn(move || -> Result<()> {
            let mut fault = None;
            for (epoch, plain) in rx {
                if let Err(e) = adopt(root, output, p, epoch, &plain) {
                    if fault.is_none() {
                        fault = Some(e);
                    }
                }
            }
            // Even uncertain local persistence drains the fixed public lifetime;
            // it never becomes a traffic-triggered connection termination.
            match fault {
                Some(e) => Err(e),
                None => Ok(()),
            }
        });
        let received = (|| {
            for epoch in start..p.first + p.epochs {
                wait(p.when(epoch)?)?;
                let mut wire = vec![0; p.capacity() + 5 + OVERHEAD];
                stream
                    .read_exact(&mut wire)
                    .map_err(|e| format!("declared enrolled link fault: {e}"))?;
                let plain = open(p, key, epoch, &wire)?;
                tx.try_send((epoch, plain)).map_err(|_| {
                    "durable adoption queue failed; no receipt or consumer dispatch"
                })?;
            }
            Ok(())
        })();
        drop(tx);
        let adopted = writer
            .join()
            .map_err(|_| "durable adoption worker failed")?;
        received.and(adopted)
    })
}
fn number(args: &mut Args, name: &str, default: u64) -> Result<u64> {
    args.optional(name)
        .map(|v| {
            v.to_string_lossy()
                .parse()
                .map_err(|_| format!("invalid {name}"))
        })
        .transpose()
        .map(|v| v.unwrap_or(default))
}
fn paths(value: std::ffi::OsString) -> Result<Vec<PathBuf>> {
    let v = value
        .into_string()
        .map_err(|_| "invalid private actor paths")?;
    if v.is_empty() {
        return Err("empty actor path inventory".into());
    }
    Ok(v.split(',').map(PathBuf::from).collect())
}
fn prepare_client_intent(
    root: &Path,
    caps: &Path,
    output: &Path,
    input: &Path,
    p: &Profile,
    keys: &[Vec<u8>],
    epoch: u64,
) -> Result<()> {
    use crate::pq_mailbox as pq;
    let ready = output.join(format!("epoch-{epoch}.payload"));
    let intent = input.join(format!("epoch-{epoch}.intent"));
    let v = read_private(&intent, p.payload)?;
    if v.len() < 49 {
        return Err("private source transport intent shape".into());
    }
    exact(root, &format!("epoch-{epoch}.intent"), &v)?;
    if ready.exists() {
        return Ok(());
    }
    let id = v[1..17].try_into().unwrap();
    let (cap, packet) = match v[0] {
        1 => {
            let cap = v[17..49].try_into().unwrap();
            (
                cap,
                pq::live_offer(epoch, p.width, p.payload, &keys, id, cap, &v[49..])?,
            )
        }
        2 if v.len() == 114 => {
            let cap = v[82..114].try_into().unwrap();
            (
                cap,
                pq::live_fetch(
                    epoch,
                    p.width,
                    p.payload,
                    &keys,
                    id,
                    v[17] as usize,
                    v[18..50].try_into().unwrap(),
                    v[50..82].try_into().unwrap(),
                    cap,
                )?,
            )
        }
        _ => return Err("unknown source transport intent; cover retained".into()),
    };
    pq::live_save_cap(&caps, epoch, p.width, p.payload, id, cap)?;
    persist(&ready, &packet)
}
fn prepare_available_intents(
    root: &Path,
    caps: &Path,
    output: &Path,
    input: &Path,
    p: &Profile,
    keys: &[Vec<u8>],
    start: u64,
) -> Result<()> {
    for epoch in start..p.first + p.epochs {
        if input.join(format!("epoch-{epoch}.intent")).exists() {
            if let Err(e) = prepare_client_intent(root, caps, output, input, p, keys, epoch) {
                private_fault(root, epoch, &e)?;
            }
        }
    }
    Ok(())
}
fn private_fault(root: &Path, epoch: u64, error: &str) -> Result<()> {
    let path = root.join(format!("epoch-{epoch}.private-fault"));
    if path.exists() {
        return Ok(());
    }
    persist(&path, error.as_bytes())
}
// The source helper has already fsynced its immutable canonical output before
// returning these exact bytes. This alias is readiness only: no second journal,
// receipt or durability claim. Crash loss is repaired from the source cache only
// for future epochs; released epochs remain fenced by the public profile.
fn publish_cached_output(cache: &Path, ready: &Path, exact: &[u8]) -> Result<()> {
    if read_private(cache, exact.len())? != exact {
        return Err("source output cache exact readback refused".into());
    }
    match std::fs::hard_link(cache, ready) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
            if read_private(ready, exact.len())? == exact {
                Ok(())
            } else {
                Err("changed non-authoritative readiness alias refused".into())
            }
        }
        Err(e) => Err(format!("source cache readiness alias unavailable: {e}")),
    }
}
fn await_inputs(inputs: &[PathBuf], epoch: u64, until: u64) -> Result<Option<Vec<PathBuf>>> {
    let names = inputs
        .iter()
        .map(|v| v.join(format!("epoch-{epoch}.payload")))
        .collect::<Vec<_>>();
    loop {
        if names.iter().all(|v| {
            let record = v.with_extension("record");
            if record.exists() {
                v.with_extension("adopted").exists()
            } else {
                v.exists()
            }
        }) {
            return Ok(Some(names));
        }
        if now_ms()? >= until {
            return Ok(None);
        }
        thread::sleep(Duration::from_millis(1));
    }
}
fn worker(
    action: &str,
    mut args: Args,
    root: &Path,
    output: &Path,
    p: &Profile,
    start: u64,
) -> Result<()> {
    use crate::pq_mailbox as pq;
    let inputs = paths(args.required("source")?)?;
    let keypaths = if action == "cover" {
        paths(args.required("keys")?)?
    } else {
        Vec::new()
    };
    let keys = keypaths
        .iter()
        .map(|v| read_private(v, 1184))
        .collect::<Result<Vec<_>>>()?;
    let authpaths = if action == "registrar" {
        paths(args.required("auth-keys")?)?
    } else {
        Vec::new()
    };
    let auth = authpaths
        .iter()
        .map(|v| read_private(v, 32))
        .collect::<Result<Vec<_>>>()?;
    let hop = if action == "relay" {
        number(&mut args, "hop", 0)? as usize
    } else {
        0
    };
    if action == "relay" && hop >= 3 {
        return Err("relay cannot impersonate receiver".into());
    }
    let secret = if action == "relay" || action == "mailbox" {
        Some(PathBuf::from(args.required("secret")?))
    } else {
        None
    };
    let opauth = if secret.is_some() {
        Some(read_private(
            &PathBuf::from(args.required("auth-key")?),
            32,
        )?)
    } else {
        None
    };
    let gateway = if action == "mailbox" {
        let target = PathBuf::from(args.required("target")?);
        let config = transport::read_config(&PathBuf::from(args.required("config")?))?;
        Some(crate::scheduled_transport::AsyncDispatch::open(
            &root.join("gateway"),
            &target,
            &config,
            3,
            1024,
            p.payload - 74,
        )?)
    } else {
        None
    };
    let custody_hold = if action == "mailbox" {
        number(&mut args, "custody-hold-ms", 600000)?
    } else {
        0
    };
    if custody_hold > 6000000 {
        return Err("public custody residence bound".into());
    }
    let caps = if action == "scan" {
        PathBuf::from(args.required("caps")?)
    } else {
        root.join("caps")
    };
    // Every network-fed worker consumes only directories written by the
    // receiving end of a roster-enrolled link for the exact upstream slot.
    let roster = if action == "cover" {
        None
    } else {
        Some(read_roster(&PathBuf::from(args.required("roster")?))?)
    };
    args.finish()?;
    let expected = match action {
        "cover" => 0,
        "registrar" => 1,
        "relay" => hop + 2,
        "mailbox" | "scan" => 5,
        _ => 99,
    };
    if expected != p.purpose as usize
        || (action == "registrar" && inputs.len() != p.width)
        || (action != "registrar" && inputs.len() != 1)
    {
        return Err("actor does not match fixed cohort stage/slot inventory".into());
    }
    let upstream: Vec<(PathBuf, Profile)> = match &roster {
        None => Vec::new(),
        Some(roster) => {
            roster.admits(p)?;
            inputs
                .iter()
                .enumerate()
                .map(|(i, dir)| {
                    let mut link = p.clone();
                    (link.purpose, link.slot) = match action {
                        "registrar" => (0, i as u16),
                        "relay" => (hop as u8 + 1, 0),
                        "mailbox" => (4, 0),
                        _ => (5, p.slot),
                    };
                    roster.admits(&link).map(|()| (dir.clone(), link))
                })
                .collect::<Result<_>>()?
        }
    };
    let mut enrolled = vec![false; upstream.len()];
    let mut identity = action.as_bytes().to_vec();
    identity.extend_from_slice(&custody_hold.to_le_bytes());
    if let Some(roster) = &roster {
        identity.extend_from_slice(&roster.digest);
    }
    for k in keys.iter().chain(auth.iter()).chain(opauth.iter()) {
        identity.extend_from_slice(&Sha256::digest(k));
    }
    if let Some(k) = &secret {
        identity.extend_from_slice(&Sha256::digest(read_private(k, 2400)?));
    }
    exact(root, "actor-profile", &identity)?;
    if action == "cover" {
        // Provision the complete bounded public lifetime before the link starts.
        // No private real request or capacity check participates in cover supply.
        for epoch in start..p.first + p.epochs {
            let path = output.join(format!("epoch-{epoch}.cover"));
            if !path.exists() {
                persist(&path, &pq::live_cover(epoch, p.width, p.payload, &keys)?)?;
            }
        }
        // Existing immutable source outbox entries can be prepared ahead of
        // their public opportunity. Do not block all future work on an empty
        // earlier slot; late new entries still use the ordinary loop below.
        prepare_available_intents(root, &caps, output, &inputs[0], p, &keys, start)?;
    }
    if action == "mailbox" {
        // Shared final audience cover is provisioned before ANY private offer or
        // fetch. It has no client-openable receipt and never claims admission.
        // All four links use these SAME exact immutable batch bytes.
        for epoch in start..p.first + p.epochs {
            let path = output.join(format!("epoch-{epoch}.cover"));
            if path.exists() {
                pq::live_validate_broadcast(
                    epoch,
                    p.width,
                    p.payload,
                    &read_private(&path, p.capacity())?,
                )?;
            } else {
                persist(&path, &pq::live_broadcast_cover(epoch, p.width, p.payload)?)?;
            }
        }
    }
    for epoch in start..p.first + p.epochs {
        let ready = output.join(format!("epoch-{epoch}.payload"));
        if ready.exists() {
            continue;
        }
        if action == "cover" {
            // Source-authored local outbox. Mode1=id16,initial cap32,native body;
            // mode2=id16,original class1,digest32,recovery32,fresh reply cap32.
            let intent = inputs[0].join(format!("epoch-{epoch}.intent"));
            let cutoff = p
                .when(epoch)?
                .checked_sub(p.tick * 3 / 4)
                .ok_or("invalid client preparation window")?;
            while !intent.exists() && now_ms()? < cutoff {
                thread::sleep(Duration::from_millis(1));
            }
            if !intent.exists() {
                continue;
            }
            if let Err(e) = prepare_client_intent(root, &caps, output, &inputs[0], p, &keys, epoch)
            {
                private_fault(root, epoch, &e)?;
            }
            continue;
        }
        let until = if action == "scan" {
            p.when(epoch)?
                .checked_add(p.tick / 2)
                .ok_or("scan clock exhausted")?
        } else {
            p.when(epoch)?
                .checked_sub(p.tick / 2)
                .ok_or("invalid actor preparation window")?
        };
        let incoming = await_inputs(&inputs, epoch, until)?;
        let Some(incoming) = incoming else {
            continue;
        };
        let result = (|| {
            for (i, (dir, link)) in upstream.iter().enumerate() {
                if !enrolled[i] {
                    check_enrolled_input(dir, link, roster.as_ref().unwrap())?;
                    enrolled[i] = true;
                }
            }
            let offset = (p.purpose as u64 * (p.processing - 1) + 1)
                .checked_mul(p.tick)
                .ok_or("actor clock exhausted")?;
            let origin = p
                .origin
                .checked_add(offset)
                .ok_or("actor clock exhausted")?;
            match action {
                "registrar" => {
                    let n = p.payload + 4640 + 160;
                    let contributions = incoming
                        .iter()
                        .map(|v| {
                            read_record(v.parent().unwrap(), epoch, n)?.ok_or_else(|| {
                                "physical input unavailable; no source verdict".to_string()
                            })
                        })
                        .collect::<Result<Vec<_>>>()?;
                    pq::live_register(
                        root,
                        epoch,
                        p.width,
                        p.payload,
                        &contributions,
                        &auth,
                        origin,
                        p.tick,
                    )
                }
                "relay" => {
                    let n =
                        18 + 160 * p.width + 128 + 19 + p.width * (p.payload + (4 - hop) * 1160);
                    let segment = read_record(incoming[0].parent().unwrap(), epoch, n)?
                        .ok_or("physical input unavailable")?;
                    pq::live_relay(
                        root,
                        epoch,
                        p.width,
                        p.payload,
                        hop,
                        secret.as_ref().unwrap(),
                        opauth.as_ref().unwrap(),
                        &segment,
                        origin,
                        p.tick,
                    )
                }
                "mailbox" => {
                    let n = 18 + 160 * p.width + 128 + 19 + p.width * (p.payload + 1160);
                    let segment = read_record(incoming[0].parent().unwrap(), epoch, n)?
                        .ok_or("physical input unavailable")?;
                    pq::live_mailbox(
                        gateway.as_ref().unwrap(),
                        root,
                        epoch,
                        p.width,
                        p.payload,
                        secret.as_ref().unwrap(),
                        opauth.as_ref().unwrap(),
                        &segment,
                        origin,
                        p.tick,
                    )
                }
                "scan" => {
                    let broadcast = read_record(
                        incoming[0].parent().unwrap(),
                        epoch,
                        19 + p.width * p.payload,
                    )?
                    .ok_or("physical broadcast unavailable")?;
                    let opened = pq::live_scan(&caps, epoch, p.width, p.payload, &broadcast)?;
                    let mut v = Vec::new();
                    for b in opened {
                        v.extend_from_slice(&(b.len() as u32).to_le_bytes());
                        v.extend(b);
                    }
                    Ok(v)
                }
                _ => Err("invalid actor".into()),
            }
        })();
        match result {
            Ok(v) => {
                let cached = match action {
                    "relay" => Some(root.join(format!("live-epoch-{epoch}-stage-{hop}.output"))),
                    "mailbox" => Some(root.join(format!("epoch-{epoch}-stage-3.output"))),
                    _ => None,
                };
                if let Some(cache) = cached {
                    publish_cached_output(&cache, &ready, &v)?;
                } else {
                    persist(&ready, &v)?;
                }
            }
            Err(e) => private_fault(root, epoch, &e)?,
        }
    }
    if action == "mailbox" {
        // Public, workload-independent residence prevents the CLI ending as soon
        // as it emits a continuation. Responsibility and unknown-effect fences
        // remain durable if this process later dies; no redispatch follows.
        let until = p
            .when(p.first + p.epochs - 1)?
            .checked_add(custody_hold)
            .ok_or("custody residence clock exhausted")?;
        if now_ms()? < until {
            wait(until)?;
        }
    }
    Ok(())
}
pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args
        .required("action")?
        .into_string()
        .map_err(|_| "invalid live action")?;
    let state = PathBuf::from(args.required("state")?);
    directory(&state)?;
    let _lock = transport::service_lock(&state.join("service.lock"))?;
    let generation = crate::decode_hex(&args.required("generation")?.to_string_lossy())?
        .try_into()
        .map_err(|_| "public generation must be16bytes")?;
    let p = Profile {
        generation,
        slot: number(&mut args, "slot", 0)?
            .try_into()
            .map_err(|_| "slot overflow")?,
        purpose: number(&mut args, "phase", 0)?
            .try_into()
            .map_err(|_| "phase overflow")?,
        width: number(&mut args, "width", 4)? as usize,
        payload: number(&mut args, "payload-bytes", 65536)? as usize,
        origin: args
            .required("origin-ms")?
            .to_string_lossy()
            .parse()
            .map_err(|_| "invalid origin")?,
        tick: number(&mut args, "tick-ms", 1000)?,
        processing: number(&mut args, "processing-slots", 2)?,
        first: number(&mut args, "first-epoch", 0)?,
        epochs: number(&mut args, "epochs", 16)?,
    };
    p.check()?;
    let start = number(&mut args, "resume-epoch", p.first)?;
    if start < p.first || start >= p.first + p.epochs {
        return Err("resume must remain inside retained public lifetime".into());
    }
    let files = PathBuf::from(args.required("records")?);
    directory(&files)?;
    if ["cover", "registrar", "relay", "mailbox", "scan"].contains(&action.as_str()) {
        worker_pin(&state, &p)?;
        return worker(&action, args, &state, &files, &p, start);
    }
    let roster = read_roster(&PathBuf::from(args.required("roster")?))?;
    roster.admits(&p)?;
    let endpoint = args
        .required("endpoint")?
        .into_string()
        .map_err(|_| "invalid endpoint")?;
    match action.as_str() {
        "send" => {
            // The sender's own native Mini key: the roster names it for this link.
            let signing = crate::read_secret(&PathBuf::from(args.required("native-key")?))?;
            args.finish()?;
            link_pin(&state, &p, &roster, signing.verifying_key().as_bytes())?;
            if now_ms()? >= p.when(start)? {
                return Err("live link must start before first public slot".into());
            }
            let mut stream = TcpStream::connect(&endpoint).map_err(|e| e.to_string())?;
            let key = enroll_sender(&mut stream, &p, &roster, &signing, start)?;
            send(stream, &files, &p, &key, start)
        }
        "receive" => {
            let secret = read_private(&PathBuf::from(args.required("link-secret")?), KEM_SECRET)?;
            let public = read_private(&PathBuf::from(args.required("link-public")?), KEM_PUBLIC)?;
            args.finish()?;
            // aws-lc cannot derive the public half of a restored ML-KEM secret,
            // so the retained pair is checked by a real encapsulation and the
            // public half must be the roster's key for this exact link.
            crate::crypto_transit::validate_keypair(&secret, &public)?;
            if public != roster.receiver(&p) {
                return Err("this link key is not the roster receiver of this link".into());
            }
            let fixed = DecapsulationKey::new(&ML_KEM_768, &secret)
                .map_err(|_| "ML-KEM link secret refused")?;
            link_pin(&state, &p, &roster, &public)?;
            if now_ms()? >= p.when(start)? {
                return Err("live link must start before first public slot".into());
            }
            let listener = TcpListener::bind(&endpoint).map_err(|e| e.to_string())?;
            let enrolled = accept_enrolled(&listener, &p, &roster, &fixed, start)?;
            drop(listener);
            // The sender's signed, challenge-bound enrollment is retained as
            // this receiver's admission evidence before any record is adopted.
            let evidence = Sha256::digest(&enrolled.signed);
            persist(
                &state.join(format!("enrollment-{}.signed", crate::hex(&evidence[..16]))),
                &enrolled.signed,
            )?;
            exact(&files, "enrolled-link", &enrolled_marker(&p, &roster))?;
            receive(enrolled.stream, &state, &files, &p, &enrolled.key, start)
        }
        _ => Err("mix-live action send|receive|cover|registrar|relay|mailbox|scan".into()),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn cached_readiness_alias_preserves_exact_source_inode_and_refuses_conflicts() {
        use std::os::unix::fs::MetadataExt;
        let root = std::env::temp_dir().join(format!(
            "mini-cache-alias-{}",
            crate::hex(&random::<16>().unwrap())
        ));
        directory(&root).unwrap();
        let cache = root.join("source.output");
        let ready = root.join("ready.payload");
        persist(&cache, b"exact durable output").unwrap();
        publish_cached_output(&cache, &ready, b"exact durable output").unwrap();
        assert_eq!(
            std::fs::metadata(&cache).unwrap().ino(),
            std::fs::metadata(&ready).unwrap().ino()
        );
        publish_cached_output(&cache, &ready, b"exact durable output").unwrap();
        assert!(publish_cached_output(&cache, &ready, b"changed output").is_err());
        let conflict = root.join("conflict.payload");
        persist(&conflict, b"changed output").unwrap();
        assert!(publish_cached_output(&cache, &conflict, b"exact durable output").is_err());
        let absent = root.join("absent.payload");
        assert!(publish_cached_output(
            &root.join("missing.output"),
            &absent,
            b"exact durable output"
        )
        .is_err());
        assert!(!absent.exists());
        // Removing the disposable alias does not erase source responsibility.
        std::fs::remove_file(&ready).unwrap();
        assert_eq!(read_private(&cache, 64).unwrap(), b"exact durable output");
        publish_cached_output(&cache, &ready, b"exact durable output").unwrap();
    }
    use super::*;
    use std::fs;
    fn profile() -> Profile {
        Profile {
            generation: [8; 16],
            slot: 0,
            purpose: 0,
            width: 4,
            payload: 1024,
            origin: 0,
            tick: 100,
            processing: 1,
            first: 0,
            epochs: 2,
        }
    }
    fn temp() -> PathBuf {
        let p = std::env::temp_dir().join(format!(
            "mini-cohort-{}",
            crate::hex(&random::<16>().unwrap())
        ));
        directory(&p).unwrap();
        p
    }
    struct Cohort {
        bytes: Vec<u8>,
        members: Vec<SigningKey>,
        operators: Vec<SigningKey>,
        member_kems: Vec<crate::crypto_transit::KeyPair>,
        operator_kems: Vec<crate::crypto_transit::KeyPair>,
    }
    fn cohort(generation: [u8; 16], width: usize) -> Cohort {
        let signer = || SigningKey::from_bytes(&random::<32>().unwrap());
        let members: Vec<_> = (0..width).map(|_| signer()).collect();
        let operators: Vec<_> = (0..5).map(|_| signer()).collect();
        let member_kems: Vec<_> = (0..width)
            .map(|_| crate::crypto_transit::generate_keypair().unwrap())
            .collect();
        let operator_kems: Vec<_> = (0..5)
            .map(|_| crate::crypto_transit::generate_keypair().unwrap())
            .collect();
        let entry = |s: &SigningKey, k: &crate::crypto_transit::KeyPair| {
            serde_json::json!({"native": crate::hex(s.verifying_key().as_bytes()),
                "linkKem": crate::hex(&k.public)})
        };
        let bytes = serde_json::to_vec(&serde_json::json!({
            "type": "minidregg-cohort-roster-v1",
            "generation": crate::hex(&generation),
            "width": width,
            "members": members.iter().zip(&member_kems).map(|(s, k)| entry(s, k)).collect::<Vec<_>>(),
            "operators": operators.iter().zip(&operator_kems).map(|(s, k)| entry(s, k)).collect::<Vec<_>>(),
        }))
        .unwrap();
        Cohort {
            bytes,
            members,
            operators,
            member_kems,
            operator_kems,
        }
    }
    fn decap(k: &crate::crypto_transit::KeyPair) -> DecapsulationKey {
        DecapsulationKey::new(&ML_KEM_768, &k.secret).unwrap()
    }
    /// Answer one connection as an honest sender would, but hand back the raw
    /// response so a test can replay it against a later challenge.
    fn captured_response(
        stream: &mut TcpStream,
        p: &Profile,
        roster: &Roster,
        signing: &SigningKey,
        start: u64,
    ) -> Vec<u8> {
        let mut challenge = [0; CHALLENGE];
        stream.read_exact(&mut challenge).unwrap();
        let fresh = EncapsulationKey::new(&ML_KEM_768, &challenge[36..]).unwrap();
        let fixed = EncapsulationKey::new(&ML_KEM_768, roster.receiver(p)).unwrap();
        let mut kems = fixed.encapsulate().unwrap().0.as_ref().to_vec();
        kems.extend_from_slice(fresh.encapsulate().unwrap().0.as_ref());
        let t = enrollment_transcript(p, roster, start, &challenge, &kems);
        kems.extend_from_slice(&signing.sign(&t).to_bytes());
        kems
    }
    #[test]
    fn registrar_enrollment_admits_only_roster_member_signature_under_fresh_challenge() {
        let generation = [8; 16];
        let c = cohort(generation, 4);
        let roster = parse_roster(&c.bytes).unwrap();
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let address = listener.local_addr().unwrap();
        let mut p = profile();
        p.slot = 2;
        p.origin = now_ms().unwrap() + 20000;
        let registrar = decap(&c.operator_kems[0]);
        let server_p = p.clone();
        let server_roster = parse_roster(&c.bytes).unwrap();
        let server = thread::spawn(move || {
            let mut e = accept_enrolled(&listener, &server_p, &server_roster, &registrar, 0).unwrap();
            let mut marker = [0];
            e.stream.read_exact(&mut marker).unwrap();
            assert_eq!(marker, [91]);
            (e.key, e.signed)
        });
        // 1. Unauthenticated garbage is dropped, not admitted.
        let mut garbage = TcpStream::connect(address).unwrap();
        let mut challenge = [0; CHALLENGE];
        garbage.read_exact(&mut challenge).unwrap();
        assert_eq!(&challenge[..4], b"MCE2");
        garbage.write_all(&[0; RESPONSE]).unwrap();
        drop(garbage);
        // 2. A valid response captured under one challenge cannot be replayed.
        let mut first = TcpStream::connect(address).unwrap();
        let captured = captured_response(&mut first, &p, &roster, &c.members[2], 0);
        drop(first);
        let mut replay = TcpStream::connect(address).unwrap();
        let mut fresh = [0; CHALLENGE];
        replay.read_exact(&mut fresh).unwrap();
        replay.write_all(&captured).unwrap();
        let mut ack = [0; ACK];
        assert!(replay.read_exact(&mut ack).is_err(), "replay must be dropped");
        // 3. Another enrolled member cannot take slot 2; neither can an outsider.
        for wrong in [&c.members[1], &SigningKey::from_bytes(&[5; 32]), &c.operators[0]] {
            let mut s = TcpStream::connect(address).unwrap();
            let response = captured_response(&mut s, &p, &roster, wrong, 0);
            s.write_all(&response).unwrap();
            assert!(s.read_exact(&mut ack).is_err(), "wrong sender must be dropped");
            assert!(enroll_sender(&mut TcpStream::connect(address).unwrap(), &p, &roster, wrong, 0)
                .unwrap_err()
                .contains("not the roster sender"));
        }
        // 4. The roster's member for slot 2 enrolls and holds the one link.
        let mut valid = TcpStream::connect(address).unwrap();
        let key = enroll_sender(&mut valid, &p, &roster, &c.members[2], 0).unwrap();
        valid.write_all(&[91]).unwrap();
        let (server_key, signed) = server.join().unwrap();
        assert_eq!(key, server_key);
        // The retained admission evidence verifies under the member's key.
        let (t, sig) = signed.split_at(signed.len() - 64);
        c.members[2]
            .verifying_key()
            .verify_strict(t, &Signature::from_bytes(sig.try_into().unwrap()))
            .unwrap();
        assert!(t.windows(32).any(|w| w == roster.digest));
    }
    #[test]
    fn cohort_sender_refuses_receiver_without_roster_link_secret() {
        let c = cohort([8; 16], 4);
        let roster = parse_roster(&c.bytes).unwrap();
        let mut p = profile();
        p.origin = now_ms().unwrap() + 20000;
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let address = listener.local_addr().unwrap();
        // An impostor holds a valid ML-KEM key, just not the registrar's.
        let impostor = decap(&crate::crypto_transit::generate_keypair().unwrap());
        let server_p = p.clone();
        let server_roster = parse_roster(&c.bytes).unwrap();
        let server = thread::spawn(move || {
            let (mut s, _) = listener.accept().unwrap();
            let _ = answer_enrollment(&mut s, &server_p, &server_roster, &impostor, 0);
        });
        let error = enroll_sender(
            &mut TcpStream::connect(address).unwrap(),
            &p,
            &roster,
            &c.members[0],
            0,
        )
        .unwrap_err();
        assert!(error.contains("receiver authentication refused"), "{error}");
        server.join().unwrap();
    }
    #[test]
    fn cohort_roster_digest_profile_and_shape_bind_every_link() {
        let c = cohort([8; 16], 4);
        let roster = parse_roster(&c.bytes).unwrap();
        let mut p = profile();
        p.origin = now_ms().unwrap() + 20000;
        // Same keys, different bytes: a different roster, so no link opens.
        let mut respaced = c.bytes.clone();
        respaced.push(b'\n');
        let other = parse_roster(&respaced).unwrap();
        assert_ne!(other.digest, roster.digest);
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let address = listener.local_addr().unwrap();
        let registrar = decap(&c.operator_kems[0]);
        let server_p = p.clone();
        let server = thread::spawn(move || {
            let (mut s, _) = listener.accept().unwrap();
            answer_enrollment(&mut s, &server_p, &other, &registrar, 0).is_none()
        });
        assert!(enroll_sender(&mut TcpStream::connect(address).unwrap(), &p, &roster, &c.members[0], 0).is_err());
        assert!(server.join().unwrap(), "a different roster digest must not enroll");
        // Shape refusals.
        let mut v: serde_json::Value = serde_json::from_slice(&c.bytes).unwrap();
        v["operators"][3] = v["operators"][1].clone();
        assert!(parse_roster(&serde_json::to_vec(&v).unwrap()).is_err(), "duplicate operator");
        let mut v: serde_json::Value = serde_json::from_slice(&c.bytes).unwrap();
        v["width"] = 5.into();
        assert!(parse_roster(&serde_json::to_vec(&v).unwrap()).is_err(), "width mismatch");
        let mut v: serde_json::Value = serde_json::from_slice(&c.bytes).unwrap();
        v["members"][0]["linkKem"] = crate::hex(&[1; 32]).into();
        assert!(parse_roster(&serde_json::to_vec(&v).unwrap()).is_err(), "short link key");
        let mut wrong = p.clone();
        wrong.generation[0] ^= 1;
        assert!(roster.admits(&wrong).is_err());
        let mut relay = p.clone();
        relay.purpose = 2;
        relay.slot = 1;
        assert!(roster.admits(&relay).is_err(), "operator links have one slot");
        // Phase roles: member k sends phase 0 slot k; operator j sends phase j+1.
        assert_eq!(roster.sender(&p), &c.members[0].verifying_key());
        relay.slot = 0;
        assert_eq!(roster.sender(&relay), &c.operators[1].verifying_key());
        assert_eq!(roster.receiver(&relay), c.operator_kems[2].public.as_slice());
        let mut broadcast = p.clone();
        broadcast.purpose = 5;
        broadcast.slot = 3;
        assert_eq!(roster.sender(&broadcast), &c.operators[4].verifying_key());
        assert_eq!(roster.receiver(&broadcast), c.member_kems[3].public.as_slice());
    }
    #[test]
    fn registrar_worker_refuses_input_directory_of_another_enrolled_slot() {
        let c = cohort([8; 16], 4);
        let roster = parse_roster(&c.bytes).unwrap();
        let p = profile();
        let dirs: Vec<_> = (0..4).map(|_| temp()).collect();
        let link = |slot: u16| {
            let mut l = p.clone();
            l.slot = slot;
            l
        };
        for (i, d) in dirs.iter().enumerate() {
            exact(d, "enrolled-link", &enrolled_marker(&link(i as u16), &roster)).unwrap();
        }
        for (i, d) in dirs.iter().enumerate() {
            check_enrolled_input(d, &link(i as u16), &roster).unwrap();
        }
        // An operator CSV that swaps two slots, or names an unenrolled directory.
        assert!(check_enrolled_input(&dirs[1], &link(0), &roster).is_err());
        assert!(check_enrolled_input(&temp(), &link(0), &roster).is_err());
        // A marker cannot be silently rewritten to another slot.
        assert!(exact(&dirs[0], "enrolled-link", &enrolled_marker(&link(1), &roster)).is_err());
        for d in dirs {
            fs::remove_dir_all(d).unwrap();
        }
    }
    #[test]
    fn preexisting_future_intent_prepares_before_idle_gap_without_changed_body_replacement() {
        let root = temp();
        let output = temp();
        let input = temp();
        let caps = root.join("caps");
        let mut p = profile();
        p.epochs = 8;
        p.origin = now_ms().unwrap() + 600000;
        let keys = (0..4)
            .map(|_| crate::crypto_transit::generate_keypair().unwrap().public)
            .collect::<Vec<_>>();
        let intent = [
            vec![1],
            vec![9; 16],
            vec![8; 32],
            b"exact native envelope".to_vec(),
        ]
        .concat();
        persist(&input.join("epoch-4.intent"), &intent).unwrap();
        prepare_available_intents(&root, &caps, &output, &input, &p, &keys, 0).unwrap();
        assert!(!output.join("epoch-0.payload").exists());
        let ready = output.join("epoch-4.payload");
        let exact = read_private(&ready, p.capacity()).unwrap();
        prepare_available_intents(&root, &caps, &output, &input, &p, &keys, 0).unwrap();
        assert_eq!(read_private(&ready, p.capacity()).unwrap(), exact);
        fs::write(
            input.join("epoch-4.intent"),
            [
                vec![1],
                vec![9; 16],
                vec![8; 32],
                b"changed native envelope".to_vec(),
            ]
            .concat(),
        )
        .unwrap();
        prepare_available_intents(&root, &caps, &output, &input, &p, &keys, 0).unwrap();
        assert!(root.join("epoch-4.private-fault").exists());
        assert_eq!(read_private(&ready, p.capacity()).unwrap(), exact);
    }
    #[test]
    fn authenticated_cohort_record_binds_generation_slot_stage_epoch_and_padding() {
        let p = profile();
        let key = [7; 32];
        let b = vec![0; p.capacity() + 5];
        let wire = seal(&p, &key, 0, &b).unwrap();
        assert_eq!(wire.len(), b.len() + OVERHEAD);
        assert_eq!(open(&p, &key, 0, &wire).unwrap(), b);
        for field in 0..5 {
            let mut q = p.clone();
            match field {
                0 => q.generation[0] ^= 1,
                1 => q.slot = 1,
                2 => q.purpose = 1,
                3 => q.tick = 101,
                _ => q.first = 1,
            }
            assert!(open(&q, &key, 0, &wire).is_err());
        }
        assert!(open(&p, &key, 1, &wire).is_err());
        assert!(open(&p, &[6; 32], 0, &wire).is_err());
        let mut altered = wire;
        *altered.last_mut().unwrap() ^= 1;
        assert!(open(&p, &key, 0, &altered).is_err());
    }
    #[test]
    fn durable_epoch_adoption_refuses_changed_record_and_preserves_exact_readback() {
        let root = temp();
        let source = temp();
        let mut p = profile();
        p.purpose = 5;
        assert!(prepare_live_wire(&source, &p, &[7; 32], 0)
            .unwrap()
            .is_none());
        persist(&source.join("epoch-0.payload"), &vec![9; p.capacity()]).unwrap();
        let original = prepare_live_wire(&source, &p, &[7; 32], 0)
            .unwrap()
            .unwrap();
        assert!(prepare_live_wire(&source, &p, &[7; 32], 1)
            .unwrap()
            .is_none());
        let output = temp();
        let plain = open(&p, &[7; 32], 0, &original).unwrap();
        adopt(&root, &output, &p, 0, &plain).unwrap();
        adopt(&root, &output, &p, 0, &plain).unwrap();
        let mut changed = plain;
        *changed.last_mut().unwrap() ^= 1;
        assert!(adopt(&root, &output, &p, 0, &changed).is_err());
        fs::remove_dir_all(root).unwrap();
        fs::remove_dir_all(source).unwrap();
        fs::remove_dir_all(output).unwrap();
    }
    #[test]
    fn visible_unqualified_record_waits_for_exact_durable_adoption() {
        let root = temp();
        let p = profile();
        let mut plain = vec![0; p.capacity() + 5];
        plain[0] = 1;
        plain[1..5].copy_from_slice(&(p.capacity() as u32).to_le_bytes());
        plain[5..].fill(3);
        persist(&root.join("epoch-0.record"), &plain).unwrap();
        assert!(read_record(&root, 0, p.capacity()).unwrap().is_none());
        assert!(await_inputs(&[root.clone()], 0, now_ms().unwrap())
            .unwrap()
            .is_none());
        let (sent, received) = std::sync::mpsc::channel();
        let observing_root = root.clone();
        let waiter = thread::spawn(move || {
            sent.send(await_inputs(&[observing_root], 0, now_ms().unwrap() + 2000).unwrap())
                .unwrap();
        });
        thread::sleep(Duration::from_millis(50));
        assert!(received.try_recv().is_err());
        adopt(&root, &root, &p, 0, &plain).unwrap();
        let names = received
            .recv_timeout(Duration::from_secs(1))
            .unwrap()
            .unwrap();
        assert_eq!(names, vec![root.join("epoch-0.payload")]);
        waiter.join().unwrap();
        assert_eq!(
            read_record(&root, 0, p.capacity()).unwrap().unwrap(),
            vec![3; p.capacity()]
        );
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn scheduled_broadcast_uses_shared_cover_when_actual_source_output_is_not_ready() {
        let source = temp();
        let mut p = profile();
        p.purpose = 5;
        p.origin = now_ms().unwrap() + 100;
        p.epochs = 1;
        let cover = crate::pq_mailbox::live_broadcast_cover(0, p.width, p.payload).unwrap();
        persist(&source.join("epoch-0.cover"), &cover).unwrap();
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let address = listener.local_addr().unwrap();
        let q = p.clone();
        let observed = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut b = vec![0; q.capacity() + 5 + OVERHEAD];
            stream.read_exact(&mut b).unwrap();
            b
        });
        send(
            TcpStream::connect(address).unwrap(),
            &source,
            &p,
            &[7; 32],
            0,
        )
        .unwrap();
        let wire = observed.join().unwrap();
        let plain = open(&p, &[7; 32], 0, &wire).unwrap();
        assert_eq!(plain[0], 1);
        assert_eq!(&plain[5..], &cover);
        assert!(!source.join("epoch-0.payload").exists());
        assert!(
            crate::pq_mailbox::live_scan(&temp(), 0, p.width, p.payload, &cover)
                .unwrap()
                .is_empty()
        );
        std::fs::remove_dir_all(source).unwrap();
    }
    #[test]
    fn enrolled_contribution_selects_cover_even_without_ready_real_work() {
        let source = temp();
        let p = profile();
        let cover = vec![4; p.capacity()];
        persist(&source.join("epoch-0.cover"), &cover).unwrap();
        persist(&source.join("epoch-1.cover"), &cover).unwrap();
        assert!(prepare_live_wire(&source, &p, &[7; 32], 0)
            .unwrap()
            .is_none());
        let mut p = p;
        p.origin = now_ms().unwrap() + 100;
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let address = listener.local_addr().unwrap();
        let observed_p = p.clone();
        let observed = thread::spawn(move || {
            let (mut s, _) = listener.accept().unwrap();
            let mut bytes = vec![0; 2 * (observed_p.capacity() + 5 + OVERHEAD)];
            s.read_exact(&mut bytes).unwrap();
            bytes
        });
        send(
            TcpStream::connect(address).unwrap(),
            &source,
            &p,
            &[7; 32],
            0,
        )
        .unwrap();
        let wire = observed.join().unwrap();
        let plain = open(&p, &[7; 32], 0, &wire[..p.capacity() + 5 + OVERHEAD]).unwrap();
        assert_eq!(plain[0], 1);
        assert_eq!(&plain[5..], &cover);
        fs::remove_dir_all(source).unwrap();
    }
    #[test]
    fn loopback_fixed_tcp_emits_both_ready_and_unavailable_at_same_public_size() {
        let source = temp();
        let receiver = temp();
        let output = temp();
        let mut p = profile();
        // A processing stage: its fallback is the physical-unavailable record
        // (a broadcast link's fallback is the shared cover, tested above).
        p.purpose = 4;
        p.origin = now_ms().unwrap() + 100;
        p.tick = 100;
        persist(&source.join("epoch-0.payload"), &vec![3; p.capacity()]).unwrap();
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let address = listener.local_addr().unwrap();
        let rp = p.clone();
        let rr = receiver.clone();
        let ro = output.clone();
        let worker = thread::spawn(move || {
            let (s, _) = listener.accept().unwrap();
            receive(s, &rr, &ro, &rp, &[7; 32], rp.first).unwrap();
        });
        let stream = TcpStream::connect(address).unwrap();
        send(stream, &source, &p, &[7; 32], p.first).unwrap();
        worker.join().unwrap();
        assert_eq!(
            read_record(&output, 0, p.capacity()).unwrap().unwrap(),
            vec![3; p.capacity()]
        );
        assert!(read_record(&output, 1, p.capacity()).unwrap().is_none());
        assert_eq!(
            fs::metadata(output.join("epoch-0.record")).unwrap().len(),
            fs::metadata(output.join("epoch-1.record")).unwrap().len()
        );
        for d in [source, receiver, output] {
            fs::remove_dir_all(d).unwrap();
        }
    }
    #[test]
    fn late_durable_producer_is_selected_without_outer_cache_write() {
        let source = temp();
        let mut p = profile();
        p.purpose = 1;
        p.origin = now_ms().unwrap() + 100;
        p.tick = 1000;
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let address = listener.local_addr().unwrap();
        let observed_p = p.clone();
        let observed = thread::spawn(move || {
            let (mut s, _) = listener.accept().unwrap();
            let mut bytes = vec![0; 2 * (observed_p.capacity() + 5 + OVERHEAD)];
            s.read_exact(&mut bytes).unwrap();
            bytes
        });
        let prepared_p = p.clone();
        let prepared_source = source.clone();
        let producer = thread::spawn(move || {
            // After the old half-tick sample, before the fixed public cutoff.
            wait(prepared_p.when(0).unwrap() - 250).unwrap();
            persist(
                &prepared_source.join("epoch-0.payload"),
                &vec![3; prepared_p.capacity()],
            )
            .unwrap();
        });
        send(
            TcpStream::connect(address).unwrap(),
            &source,
            &p,
            &[7; 32],
            0,
        )
        .unwrap();
        producer.join().unwrap();
        let bytes = observed.join().unwrap();
        let size = p.capacity() + 5 + OVERHEAD;
        let first = open(&p, &[7; 32], 0, &bytes[..size]).unwrap();
        assert_eq!(first[0], 1);
        assert_eq!(&first[5..], vec![3; p.capacity()]);
        assert_eq!(open(&p, &[7; 32], 1, &bytes[size..]).unwrap()[0], 0);
        for d in [source] {
            fs::remove_dir_all(d).unwrap();
        }
    }
    #[test]
    fn public_cohort_lifetime_and_profile_changes_fail_closed() {
        let root = temp();
        let mut p = profile();
        p.check().unwrap();
        worker_pin(&root, &p).unwrap();
        worker_pin(&root, &p).unwrap();
        p.tick += 1;
        assert!(worker_pin(&root, &p).is_err());
        p.origin = u64::MAX;
        assert!(p.check().is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn local_adoption_conflict_drains_public_lifetime_without_releasing_changed_record() {
        let source = temp();
        let receiver = temp();
        let output = temp();
        let mut p = profile();
        p.purpose = 5;
        p.origin = now_ms().unwrap() + 100;
        for epoch in 0..2 {
            persist(
                &source.join(format!("epoch-{epoch}.payload")),
                &vec![3; p.capacity()],
            )
            .unwrap();
            let cover = crate::pq_mailbox::live_broadcast_cover(epoch, p.width, p.payload).unwrap();
            persist(&source.join(format!("epoch-{epoch}.cover")), &cover).unwrap();
        }
        let original = vec![0; p.capacity() + 5];
        persist(&output.join("epoch-0.record"), &original).unwrap();
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let address = listener.local_addr().unwrap();
        let rp = p.clone();
        let rr = receiver.clone();
        let ro = output.clone();
        let worker = thread::spawn(move || {
            let (s, _) = listener.accept().unwrap();
            receive(s, &rr, &ro, &rp, &[7; 32], 0)
        });
        send(
            TcpStream::connect(address).unwrap(),
            &source,
            &p,
            &[7; 32],
            0,
        )
        .unwrap();
        assert!(worker.join().unwrap().is_err());
        assert_eq!(
            read_private(&output.join("epoch-0.record"), original.len()).unwrap(),
            original
        );
        assert_eq!(
            read_record(&output, 1, p.capacity()).unwrap().unwrap(),
            vec![3; p.capacity()]
        );
        for d in [source, receiver, output] {
            fs::remove_dir_all(d).unwrap();
        }
    }
}
