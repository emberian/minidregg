//! Fixed enrolled-link TCP records for the guarded PQ cohort. Link PSKs are
//! independently provisioned; this layer does not manufacture Mini outcomes.
use crate::scheduled_transport::{directory, persist, random, read_private};
use crate::{transport, Args, Result};
use chacha20poly1305::{
    aead::{Aead, Payload},
    KeyInit, XChaCha20Poly1305, XNonce,
};
use sha2::{Digest, Sha256};
use std::{
    fs,
    io::{Read, Write},
    net::{TcpListener, TcpStream},
    path::{Path, PathBuf},
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

const DOMAIN: &[u8] = b"Mini/PQ-cohort/fixed-link/v1";
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
            || !(10..=60000).contains(&self.tick)
            || self.purpose > 5
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
            .checked_add(self.purpose as u64 + 1)
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
fn pin(root: &Path, p: &Profile, key: &[u8; 32]) -> Result<()> {
    let mut b = p.identity();
    b.extend_from_slice(&Sha256::digest(key));
    exact(root, "profile", &b)
}
// Empty/late output becomes physical-unavailable, not a native Pending or a
// synthetic source receipt. A contribution producer supplies a valid cover
// packet before its deadline through the live client API.
fn select(root: &Path, source: &Path, p: &Profile, epoch: u64) -> Result<Vec<u8>> {
    let retained = root.join(format!("epoch-{epoch}.selected"));
    if retained.exists() {
        return read_private(&retained, p.capacity() + 5);
    }
    let ready = source.join(format!("epoch-{epoch}.payload"));
    let cover = source.join(format!("epoch-{epoch}.cover"));
    let path = if ready.exists() {
        ready
    } else if p.purpose == 0 {
        cover
    } else {
        ready
    };
    let mut v = vec![0; p.capacity() + 5];
    if path.exists() {
        let b = read_private(&path, p.capacity())?;
        if b.len() != p.capacity() {
            return Err("guarded cohort segment is not exact public shape".into());
        }
        v[0] = 1;
        v[1..5].copy_from_slice(&(b.len() as u32).to_le_bytes());
        v[5..].copy_from_slice(&b);
    }
    persist(&retained, &v)?; // durable immutable selection BEFORE network emission
    Ok(v)
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
fn adopt(root: &Path, output: &Path, p: &Profile, epoch: u64, plain: &[u8]) -> Result<()> {
    // Whole exact authenticated record is durable before any consumer sees it.
    exact(root, &format!("epoch-{epoch}.received"), plain)?;
    if plain[0] == 1 {
        exact(output, &format!("epoch-{epoch}.payload"), &plain[5..])
    } else {
        exact(
            output,
            &format!("epoch-{epoch}.unavailable"),
            b"physical transport unavailable; no source decision",
        )
    }
}
fn send(
    mut stream: TcpStream,
    root: &Path,
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
    // Prepare durable valid client cover or physical-unavailable records once,
    // before the public lifetime. Neither disk nor producer runs in clock loop.
    let mut fallback = Vec::with_capacity(count);
    for epoch in start..p.first + p.epochs {
        let path = root.join(format!("epoch-{epoch}.fallback-wire"));
        let wire = if path.exists() {
            read_private(&path, p.capacity() + 5 + OVERHEAD)?
        } else {
            let mut plain = vec![0; p.capacity() + 5];
            if p.purpose == 0 {
                let cover =
                    read_private(&source.join(format!("epoch-{epoch}.cover")), p.capacity())?;
                if cover.len() != p.capacity() {
                    return Err("complete enrolled cover inventory required".into());
                }
                plain[0] = 1;
                plain[1..5].copy_from_slice(&(cover.len() as u32).to_le_bytes());
                plain[5..].copy_from_slice(&cover);
            }
            let wire = seal(p, key, epoch, &plain)?;
            persist(&path, &wire)?;
            wire
        };
        open(p, key, epoch, &wire)?;
        fallback.push(wire);
    }
    let (tx, rx) = std::sync::mpsc::channel();
    let root = root.to_path_buf();
    let source = source.to_path_buf();
    let profile = p.clone();
    let key = *key;
    thread::spawn(move || {
        for epoch in start..profile.first + profile.epochs {
            let prepared = (|| {
                let when = profile
                    .when(epoch)?
                    .checked_sub(profile.tick / 2)
                    .ok_or("preparation clock exhausted")?;
                wait(when)?;
                let path = root.join(format!("epoch-{epoch}.ready-wire"));
                let wire = if path.exists() {
                    read_private(&path, profile.capacity() + 5 + OVERHEAD)?
                } else {
                    let plain = select(&root, &source, &profile, epoch)?;
                    let wire = seal(&profile, &key, epoch, &plain)?;
                    persist(&path, &wire)?;
                    wire
                };
                open(&profile, &key, epoch, &wire)?;
                Ok(wire)
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
fn receive(
    mut stream: TcpStream,
    root: &Path,
    output: &Path,
    p: &Profile,
    key: &[u8; 32],
    start: u64,
) -> Result<()> {
    stream
        .set_read_timeout(Some(Duration::from_millis(p.tick / 2)))
        .map_err(|e| e.to_string())?;
    for epoch in start..p.first + p.epochs {
        wait(p.when(epoch)?)?;
        let mut wire = vec![0; p.capacity() + 5 + OVERHEAD];
        stream
            .read_exact(&mut wire)
            .map_err(|e| format!("declared enrolled link fault: {e}"))?;
        let plain = open(p, key, epoch, &wire)?;
        adopt(root, output, p, epoch, &plain)?;
    }
    Ok(())
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
fn private_fault(root: &Path, epoch: u64, error: &str) -> Result<()> {
    let path = root.join(format!("epoch-{epoch}.private-fault"));
    if path.exists() {
        return Ok(());
    }
    persist(&path, error.as_bytes())
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
    let mut identity = action.as_bytes().to_vec();
    identity.extend_from_slice(&custody_hold.to_le_bytes());
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
            let result = (|| {
                let v = read_private(&intent, p.payload)?;
                if v.len() < 49 {
                    return Err("private source transport intent shape".into());
                }
                exact(root, &format!("epoch-{epoch}.intent"), &v)?;
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
            })();
            if let Err(e) = result {
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
        let incoming = loop {
            let names = inputs
                .iter()
                .map(|v| v.join(format!("epoch-{epoch}.payload")))
                .collect::<Vec<_>>();
            if names.iter().all(|v| v.exists()) {
                break Some(names);
            }
            if now_ms()? >= until {
                break None;
            }
            thread::sleep(Duration::from_millis(1));
        };
        let Some(incoming) = incoming else {
            continue;
        };
        let result = (|| {
            let origin = p
                .origin
                .checked_add(p.tick)
                .ok_or("actor clock exhausted")?;
            match action {
                "registrar" => {
                    let n = p.payload + 4640 + 160;
                    let contributions = incoming
                        .iter()
                        .map(|v| read_private(v, n))
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
                    let segment = read_private(&incoming[0], n)?;
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
                    let segment = read_private(&incoming[0], n)?;
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
                    let broadcast = read_private(&incoming[0], 19 + p.width * p.payload)?;
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
            Ok(v) => persist(&ready, &v)?,
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
    let keyfile = PathBuf::from(args.required("key")?);
    if action == "key" {
        args.finish()?;
        return persist(&keyfile, &random::<32>()?);
    }
    let key: [u8; 32] = read_private(&keyfile, 32)?
        .try_into()
        .map_err(|_| "cohort PSK must be32bytes")?;
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
        first: number(&mut args, "first-epoch", 0)?,
        epochs: number(&mut args, "epochs", 16)?,
    };
    p.check()?;
    let start = number(&mut args, "resume-epoch", p.first)?;
    if start < p.first || start >= p.first + p.epochs {
        return Err("resume must remain inside retained public lifetime".into());
    }
    pin(&state, &p, &key)?;
    let files = PathBuf::from(args.required("records")?);
    directory(&files)?;
    if ["cover", "registrar", "relay", "mailbox", "scan"].contains(&action.as_str()) {
        return worker(&action, args, &state, &files, &p, start);
    }
    let endpoint = args
        .required("endpoint")?
        .into_string()
        .map_err(|_| "invalid endpoint")?;
    args.finish()?;
    if now_ms()? >= p.when(start)? {
        return Err("live link must start before first public slot".into());
    }
    match action.as_str() {
        "send" => {
            let stream = TcpStream::connect(&endpoint).map_err(|e| e.to_string())?;
            send(stream, &state, &files, &p, &key, start)
        }
        "receive" => {
            let listener = TcpListener::bind(&endpoint).map_err(|e| e.to_string())?;
            listener.set_nonblocking(true).map_err(|e| e.to_string())?;
            let remaining = p
                .when(start)?
                .checked_sub(now_ms()?)
                .ok_or("missed enrolled connection deadline")?;
            let until = Instant::now()
                .checked_add(Duration::from_millis(remaining))
                .ok_or("cohort monotonic lifetime exhausted")?;
            loop {
                match listener.accept() {
                    Ok((stream, _)) => break receive(stream, &state, &files, &p, &key, start),
                    Err(e)
                        if e.kind() == std::io::ErrorKind::WouldBlock && Instant::now() < until =>
                    {
                        thread::sleep(Duration::from_millis(1))
                    }
                    Err(e) => break Err(format!("public enrolled connection fault: {e}")),
                }
            }
        }
        _ => Err("mix-live action key|send|receive|cover|registrar|relay|mailbox|scan".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn profile() -> Profile {
        Profile {
            generation: [8; 16],
            slot: 0,
            purpose: 0,
            width: 4,
            payload: 1024,
            origin: 0,
            tick: 100,
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
    fn immutable_slot_selection_refuses_late_change_and_preserves_exact_readback() {
        let root = temp();
        let source = temp();
        let mut p = profile();
        p.purpose = 5;
        let original = select(&root, &source, &p, 0).unwrap();
        assert_eq!(original[0], 0);
        persist(&source.join("epoch-0.payload"), &vec![9; p.capacity()]).unwrap();
        assert_eq!(select(&root, &source, &p, 0).unwrap(), original);
        let good = select(&root, &source, &p, 1).unwrap();
        assert_eq!(good[0], 0);
        let output = temp();
        adopt(&root, &output, &p, 0, &original).unwrap();
        let mut changed = original;
        changed[0] = 1;
        assert!(adopt(&root, &output, &p, 0, &changed).is_err());
        fs::remove_dir_all(root).unwrap();
        fs::remove_dir_all(source).unwrap();
        fs::remove_dir_all(output).unwrap();
    }
    #[test]
    fn enrolled_contribution_selects_cover_even_without_ready_real_work() {
        let root = temp();
        let source = temp();
        let p = profile();
        let cover = vec![4; p.capacity()];
        persist(&source.join("epoch-0.cover"), &cover).unwrap();
        let selected = select(&root, &source, &p, 0).unwrap();
        assert_eq!(selected[0], 1);
        assert_eq!(&selected[5..], &cover);
        persist(&source.join("epoch-0.payload"), &vec![9; p.capacity()]).unwrap();
        assert_eq!(select(&root, &source, &p, 0).unwrap(), selected);
        fs::remove_dir_all(root).unwrap();
        fs::remove_dir_all(source).unwrap();
    }
    #[test]
    fn loopback_fixed_tcp_emits_both_ready_and_unavailable_at_same_public_size() {
        let root = temp();
        let source = temp();
        let receiver = temp();
        let output = temp();
        let mut p = profile();
        p.purpose = 5;
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
        send(stream, &root, &source, &p, &[7; 32], p.first).unwrap();
        worker.join().unwrap();
        assert_eq!(
            read_private(&output.join("epoch-0.payload"), p.capacity()).unwrap(),
            vec![3; p.capacity()]
        );
        assert!(output.join("epoch-1.unavailable").exists());
        assert_eq!(
            fs::metadata(receiver.join("epoch-0.received"))
                .unwrap()
                .len(),
            fs::metadata(receiver.join("epoch-1.received"))
                .unwrap()
                .len()
        );
        for d in [root, source, receiver, output] {
            fs::remove_dir_all(d).unwrap();
        }
    }
    #[test]
    fn public_cohort_lifetime_and_profile_changes_fail_closed() {
        let root = temp();
        let mut p = profile();
        p.check().unwrap();
        pin(&root, &p, &[7; 32]).unwrap();
        p.tick += 1;
        assert!(pin(&root, &p, &[7; 32]).is_err());
        p.origin = u64::MAX;
        assert!(p.check().is_err());
        fs::remove_dir_all(root).unwrap();
    }
}
