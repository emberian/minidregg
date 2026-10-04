//! Restricted PQ batch cascade + full-broadcast replies. NOT Outfox protocol
//! equivalence or a completed active/longitudinal anonymity theorem.
use crate::crypto_transit::{self, SealedRef};
use crate::scheduled_transport::{self as native, directory, persist, random, read_private};
use crate::{transport, Args, Result};
use crate::hybrid_kem::{self, HybridSecret};
use chacha20poly1305::{
    aead::{Aead, Payload},
    KeyInit, XChaCha20Poly1305, XNonce,
};
use ring::hmac;
use sha2::{Digest, Sha256};
use std::{
    fs,
    path::{Path, PathBuf},
    time::{Duration, SystemTime, UNIX_EPOCH},
};
const LAYERS: usize = 4; // three independently administered relays + mailbox receiver
const OVERHEAD: usize = crypto_transit::OVERHEAD_BYTES;
/// The v1 (pure ML-KEM-768) layer overhead: 1088 KEM + 24 + 32 + 16. Kept only to
/// recognise and refuse a v1 packet by name.
const V1_OVERHEAD: usize = 1088 + 24 + 32 + 16;
const CORE: usize = 4 + 8 + 1 + 1 + 16 + 32 + 4;
const REPLY: usize = 4 + 8 + 1 + 16 + 4;
const DOMAIN: &[u8] = b"Mini/PQ-batch-mailbox/v2";
/// Batch and manifest frames: v2 carries hybrid X25519 + ML-KEM-768 layers.
const BATCH_MAGIC: &[u8; 4] = b"MPB2";
const MANIFEST_MAGIC: &[u8; 4] = b"MPM2";
const V1_REFUSAL: &str = "this is a v1 pure ML-KEM-768 mix frame (no X25519 component): refused; the mix is hybrid X25519 + ML-KEM-768 (v2). Re-key the operators (`mix --action key`) and re-seal";
#[derive(Clone)]
struct Profile {
    epoch: u64,
    width: usize,
    payload: usize,
}
impl Profile {
    fn check(&self) -> Result<()> {
        if !(2..=64).contains(&self.width) || !(1024..=262144).contains(&self.payload) {
            Err("PQ batch profile bound refused".into())
        } else {
            Ok(())
        }
    }
    fn class(&self) -> usize {
        [0, 0, 1, 2][self.epoch as usize % 4]
    }
    fn aad(&self, hop: usize) -> Vec<u8> {
        let mut v = DOMAIN.to_vec();
        for n in [
            self.epoch,
            self.width as u64,
            self.payload as u64,
            hop as u64,
        ] {
            v.extend_from_slice(&n.to_le_bytes());
        }
        v
    }
    fn size(&self, hop: usize) -> usize {
        self.payload + (LAYERS - hop) * OVERHEAD
    }
    fn v1_size(&self, hop: usize) -> usize {
        self.payload + (LAYERS - hop) * V1_OVERHEAD
    }
}
fn wrap(p: &Profile, hop: usize, key: &[u8], body: &[u8]) -> Result<Vec<u8>> {
    if body.len() != p.size(hop + 1) {
        return Err("PQ layer body shape mismatch".into());
    }
    let sealed = crypto_transit::seal_raw_context(key, &p.aad(hop), body)?;
    let mut out = sealed.hybrid_ciphertext.to_vec();
    out.extend_from_slice(&sealed.nonce);
    out.extend_from_slice(&sealed.commitment);
    out.extend_from_slice(&sealed.ciphertext);
    Ok(out)
}
fn peel(p: &Profile, hop: usize, key: &HybridSecret, packet: &[u8]) -> Result<Vec<u8>> {
    const H: usize = crypto_transit::HYBRID_CIPHERTEXT_BYTES;
    const N: usize = crypto_transit::NONCE_BYTES;
    const C: usize = crypto_transit::COMMITMENT_BYTES;
    if hop < LAYERS && packet.len() == p.v1_size(hop) {
        return Err(format!("PQ layer packet: {V1_REFUSAL}"));
    }
    if hop >= LAYERS || packet.len() != p.size(hop) {
        return Err("PQ layer packet shape mismatch".into());
    }
    crypto_transit::open_raw_context(
        key,
        &p.aad(hop),
        SealedRef {
            hybrid_ciphertext: &packet[..H],
            nonce: &packet[H..H + N],
            commitment: &packet[H + N..H + N + C],
            ciphertext: &packet[H + N + C..],
        },
    )
}
fn shuffle<T>(values: &mut [T]) -> Result<()> {
    for i in (1..values.len()).rev() {
        // rejection sampling; no modulo-biased secret permutation
        let bound = (i + 1) as u64;
        let limit = u64::MAX - u64::MAX % bound;
        let x = loop {
            let n = u64::from_le_bytes(random()?);
            if n < limit {
                break n;
            }
        };
        values.swap(i, (x % bound) as usize);
    }
    Ok(())
}
fn batch(p: &Profile, hop: usize, packets: &[Vec<u8>]) -> Result<Vec<u8>> {
    if hop > LAYERS || packets.len() != p.width || packets.iter().any(|v| v.len() != p.size(hop)) {
        return Err("PQ batch fixed shape mismatch".into());
    }
    let mut out = BATCH_MAGIC.to_vec();
    out.extend_from_slice(&p.epoch.to_le_bytes());
    out.push(hop as u8);
    out.extend_from_slice(&(p.width as u16).to_le_bytes());
    out.extend_from_slice(&(p.payload as u32).to_le_bytes());
    for v in packets {
        out.extend_from_slice(v);
    }
    Ok(out)
}
fn unbatch(p: &Profile, hop: usize, bytes: &[u8]) -> Result<Vec<Vec<u8>>> {
    if bytes.get(..4) == Some(b"MPB1") {
        return Err(format!("PQ batch (MPB1): {V1_REFUSAL}"));
    }
    if hop > LAYERS
        || bytes.len() != 19 + p.width * p.size(hop)
        || bytes.get(..4) != Some(BATCH_MAGIC)
        || u64::from_le_bytes(bytes[4..12].try_into().unwrap()) != p.epoch
        || bytes[12] as usize != hop
        || u16::from_le_bytes(bytes[13..15].try_into().unwrap()) as usize != p.width
        || u32::from_le_bytes(bytes[15..19].try_into().unwrap()) as usize != p.payload
    {
        return Err("PQ batch epoch/stage/shape refused before allocation".into());
    }
    let packets: Vec<_> = bytes[19..]
        .chunks_exact(p.size(hop))
        .map(|v| v.to_vec())
        .collect();
    let mut digests = std::collections::BTreeSet::new();
    if packets
        .iter()
        .any(|v| !digests.insert(Sha256::digest(v).to_vec()))
    {
        return Err("duplicate packet within fixed cohort batch".into());
    }
    Ok(packets)
}
// Entire batch accepted before any output or native dispatch. A pending claim
// never authorizes regenerated shuffle state or another native semantic effect.
fn claim(root: &Path, p: &Profile, hop: usize, input: &[u8]) -> Result<Option<Vec<u8>>> {
    let stem = format!("epoch-{}-stage-{hop}", p.epoch);
    let hash = Sha256::digest(input);
    let bind = root.join(format!("{stem}.input"));
    if bind.exists() {
        if read_private(&bind, 32)? != hash.as_slice() {
            return Err("changed replay batch refused".into());
        }
    } else {
        persist(&bind, &hash)?;
    }
    let output = root.join(format!("{stem}.output"));
    if output.exists() {
        return Ok(Some(read_private(&output, 19 + p.width * p.size(hop))?));
    }
    let consumed = root.join(format!("{stem}.claimed"));
    if consumed.exists() {
        return Err("batch crash outcome uncertain; no automatic reprocessing".into());
    }
    persist(&consumed, b"claimed")?;
    Ok(None)
}
fn save_batch(root: &Path, p: &Profile, hop: usize, v: &[u8]) -> Result<()> {
    persist(
        &root.join(format!("epoch-{}-stage-{hop}.output", p.epoch)),
        v,
    )
}
fn process_relay(
    root: &Path,
    p: &Profile,
    hop: usize,
    key: &HybridSecret,
    input: &[u8],
) -> Result<Vec<u8>> {
    if hop >= 3 {
        return Err("relay stage must be 0,1,2; receiver is independent layer3".into());
    }
    let packets = unbatch(p, hop, input)?;
    // Validate every packet before creating the batch claim or releasing any prefix.
    let mut next: Vec<_> = packets
        .iter()
        .map(|v| peel(p, hop, key, v))
        .collect::<Result<_>>()?;
    if let Some(v) = claim(root, p, hop, input)? {
        return Ok(v);
    }
    shuffle(&mut next)?;
    let out = batch(p, hop + 1, &next)?;
    save_batch(root, p, hop, &out)?;
    Ok(out)
}
fn core(p: &Profile, id: [u8; 16], reply: [u8; 32], body: Option<&[u8]>) -> Result<Vec<u8>> {
    let body = body.unwrap_or(&[]);
    if body.len() > p.payload - CORE {
        return Err("native envelope exceeds public PQ mailbox class BEFORE dispatch".into());
    }
    let mut out = vec![0; p.payload];
    out[..4].copy_from_slice(b"MPC1");
    out[4..12].copy_from_slice(&p.epoch.to_le_bytes());
    out[12] = p.class() as u8;
    out[13] = u8::from(!body.is_empty());
    out[14..30].copy_from_slice(&id);
    out[30..62].copy_from_slice(&reply);
    out[62..66].copy_from_slice(&(body.len() as u32).to_le_bytes());
    out[66..66 + body.len()].copy_from_slice(body);
    Ok(out)
}
fn parse_core(p: &Profile, v: &[u8]) -> Result<([u8; 16], [u8; 32], Vec<u8>)> {
    if v.len() != p.payload
        || v.get(..4) != Some(b"MPC1")
        || u64::from_le_bytes(v[4..12].try_into().unwrap()) != p.epoch
        || v[12] as usize != p.class()
        || v[13] > 1
    {
        return Err("mailbox native core epoch/class/shape refused".into());
    }
    let n = u32::from_le_bytes(v[62..66].try_into().unwrap()) as usize;
    if n > p.payload - CORE || (v[13] == 0) != (n == 0) || v[66 + n..].iter().any(|b| *b != 0) {
        return Err("mailbox core body/padding refused".into());
    }
    Ok((
        v[14..30].try_into().unwrap(),
        v[30..62].try_into().unwrap(),
        v[66..66 + n].to_vec(),
    ))
}
fn reply(p: &Profile, id: [u8; 16], key: [u8; 32], body: &[u8]) -> Result<Vec<u8>> {
    if body.len() > p.payload - 40 - REPLY {
        return Err("native reply exceeds broadcast class".into());
    }
    let mut plain = vec![0; p.payload - 40];
    plain[..4].copy_from_slice(b"MPR1");
    plain[4..12].copy_from_slice(&p.epoch.to_le_bytes());
    plain[12] = p.class() as u8;
    plain[13..29].copy_from_slice(&id);
    plain[29..33].copy_from_slice(&(body.len() as u32).to_le_bytes());
    plain[33..33 + body.len()].copy_from_slice(body);
    let nonce = random::<24>()?;
    let cipher = XChaCha20Poly1305::new_from_slice(&key)
        .map_err(|_| "reply key")?
        .encrypt(
            XNonce::from_slice(&nonce),
            Payload {
                msg: &plain,
                aad: &p.aad(LAYERS),
            },
        )
        .map_err(|_| "reply seal")?;
    let mut out = nonce.to_vec();
    out.extend_from_slice(&cipher);
    Ok(out)
}
fn open_reply(p: &Profile, id: [u8; 16], key: [u8; 32], v: &[u8]) -> Result<Vec<u8>> {
    if v.len() != p.payload {
        return Err("broadcast reply shape".into());
    }
    let plain = XChaCha20Poly1305::new_from_slice(&key)
        .map_err(|_| "reply key")?
        .decrypt(
            XNonce::from_slice(&v[..24]),
            Payload {
                msg: &v[24..],
                aad: &p.aad(LAYERS),
            },
        )
        .map_err(|_| "not this capability or invalid reply")?;
    if plain.get(..4) != Some(b"MPR1")
        || u64::from_le_bytes(plain[4..12].try_into().unwrap()) != p.epoch
        || plain[12] as usize != p.class()
        || plain[13..29] != id
    {
        return Err("reply capability epoch/class/operation mismatch".into());
    }
    let n = u32::from_le_bytes(plain[29..33].try_into().unwrap()) as usize;
    if n > plain.len() - REPLY || plain[33 + n..].iter().any(|b| *b != 0) {
        return Err("reply bounds/padding".into());
    }
    Ok(plain[33..33 + n].to_vec())
}
fn process_mailbox(
    root: &Path,
    p: &Profile,
    key: &HybridSecret,
    input: &[u8],
    target: &Path,
    config: &[u8],
) -> Result<Vec<u8>> {
    let cores = unbatch(p, 3, input)?
        .iter()
        .map(|v| peel(p, 3, key, v).and_then(|v| parse_core(p, &v)))
        .collect::<Result<Vec<_>>>()?;
    if let Some(v) = claim(root, p, 3, input)? {
        return Ok(v);
    }
    let journal = root.join("native");
    directory(&journal)?;
    let mut replies = Vec::new();
    for (id, cap, body) in cores {
        let result = if body.is_empty() {
            vec![0]
        } else {
            native::dispatch_once(
                &journal,
                target,
                config,
                p.class(),
                id,
                &body,
                p.payload - 40 - REPLY - 1,
            )
            .unwrap_or_else(|_| {
                let mut v = vec![1];
                v.extend_from_slice(b"native dispatch uncertain; source exact recovery required");
                v
            })
        };
        replies.push(reply(p, id, cap, &result)?);
    }
    shuffle(&mut replies)?;
    let out = batch(p, LAYERS, &replies)?;
    save_batch(root, p, 3, &out)?;
    Ok(out)
}
fn seal_with_route(
    p: &Profile,
    keys: &[Vec<u8>],
    id: [u8; 16],
    cap: [u8; 32],
    body: Option<&[u8]>,
) -> Result<(Vec<u8>, Vec<u8>)> {
    seal_core_with_route(p, keys, core(p, id, cap, body)?)
}
fn seal_core_with_route(
    p: &Profile,
    keys: &[Vec<u8>],
    mut v: Vec<u8>,
) -> Result<(Vec<u8>, Vec<u8>)> {
    if keys.len() != LAYERS
        || keys.iter().collect::<std::collections::BTreeSet<_>>().len() != LAYERS
    {
        return Err("pin three relay keys and separate receiver key".into());
    }
    let mut hashes = vec![vec![]; LAYERS + 1];
    hashes[LAYERS] = Sha256::digest(&v).to_vec();
    for hop in (0..LAYERS).rev() {
        v = wrap(p, hop, &keys[hop], &v)?;
        hashes[hop] = Sha256::digest(&v).to_vec();
    }
    Ok((v, hashes.concat()))
}
#[cfg(test)]
fn seal_packet(
    p: &Profile,
    keys: &[Vec<u8>],
    id: [u8; 16],
    cap: [u8; 32],
    body: Option<&[u8]>,
) -> Result<Vec<u8>> {
    seal_with_route(p, keys, id, cap, body).map(|v| v.0)
}
// Registrar is an explicit additional trusted, noncolluding role. It receives
// secret PAIRED per-client commitments; publishes only independent sorted sets.
// Operator i receives only its independently provisioned registrar MAC key.
fn manifest(
    p: &Profile,
    packets: &[Vec<u8>],
    routes: &[Vec<u8>],
    auth: &[Vec<u8>],
) -> Result<Vec<u8>> {
    if packets.len() != p.width
        || routes.len() != p.width
        || auth.len() != LAYERS
        || auth.iter().any(|v| v.len() != 32)
        || auth.iter().collect::<std::collections::BTreeSet<_>>().len() != LAYERS
        || routes.iter().any(|v| v.len() != 32 * (LAYERS + 1))
    {
        return Err("registered fixed cohort commitments/authentication shape".into());
    }
    if packets
        .iter()
        .zip(routes)
        .any(|(v, r)| Sha256::digest(v).as_slice() != &r[..32])
    {
        return Err("cohort input differs from private registered commitment".into());
    }
    let mut out = MANIFEST_MAGIC.to_vec();
    out.extend_from_slice(&p.epoch.to_le_bytes());
    out.extend_from_slice(&(p.width as u16).to_le_bytes());
    out.extend_from_slice(&(p.payload as u32).to_le_bytes());
    for hop in 0..=LAYERS {
        let mut set: Vec<_> = routes
            .iter()
            .map(|r| r[hop * 32..(hop + 1) * 32].to_vec())
            .collect();
        set.sort();
        if set.windows(2).any(|w| w[0] == w[1]) {
            return Err("cohort duplicate admitted stage commitment".into());
        }
        for h in set {
            out.extend_from_slice(&h);
        }
    }
    let body = out.clone();
    for (hop, key) in auth.iter().enumerate() {
        let mut bound = p.aad(hop);
        bound.extend_from_slice(&body);
        out.extend_from_slice(hmac::sign(&hmac::Key::new(hmac::HMAC_SHA256, key), &bound).as_ref());
    }
    Ok(out)
}
fn stage_set(p: &Profile, hop: usize, m: &[u8]) -> Vec<Vec<u8>> {
    m[18 + hop * p.width * 32..18 + (hop + 1) * p.width * 32]
        .chunks_exact(32)
        .map(|v| v.to_vec())
        .collect()
}
fn verify_manifest(p: &Profile, hop: usize, m: &[u8], auth: &[u8]) -> Result<()> {
    if m.get(..4) == Some(b"MPM1") {
        return Err(format!("authenticated cohort manifest (MPM1): {V1_REFUSAL}"));
    }
    let n = 18 + (LAYERS + 1) * p.width * 32;
    if hop >= LAYERS
        || auth.len() != 32
        || m.len() != n + LAYERS * 32
        || m.get(..4) != Some(MANIFEST_MAGIC)
        || u64::from_le_bytes(m[4..12].try_into().unwrap()) != p.epoch
        || u16::from_le_bytes(m[12..14].try_into().unwrap()) as usize != p.width
        || u32::from_le_bytes(m[14..18].try_into().unwrap()) as usize != p.payload
    {
        return Err("authenticated cohort manifest epoch/shape".into());
    }
    let mut bound = p.aad(hop);
    bound.extend_from_slice(&m[..n]);
    hmac::verify(
        &hmac::Key::new(hmac::HMAC_SHA256, auth),
        &bound,
        &m[n + hop * 32..n + (hop + 1) * 32],
    )
    .map_err(|_| "registrar/operator manifest authentication refused")?;
    for stage in 0..=LAYERS {
        let set = stage_set(p, stage, m);
        if set.windows(2).any(|w| w[0] >= w[1]) {
            return Err("manifest admitted set not strict/sorted".into());
        }
    }
    Ok(())
}
fn verify_transition(
    p: &Profile,
    hop: usize,
    key: &HybridSecret,
    input: &[u8],
    m: &[u8],
    auth: &[u8],
) -> Result<()> {
    prepare_transition(p, hop, key, input, m, auth).map(|_| ())
}
fn prepare_transition(
    p: &Profile,
    hop: usize,
    key: &HybridSecret,
    input: &[u8],
    m: &[u8],
    auth: &[u8],
) -> Result<Vec<Vec<u8>>> {
    verify_manifest(p, hop, m, auth)?;
    let packets = unbatch(p, hop, input)?;
    let mut before: Vec<_> = packets.iter().map(|v| Sha256::digest(v).to_vec()).collect();
    before.sort();
    if before != stage_set(p, hop, m) {
        return Err("active omission/replacement/input-set substitution refused".into());
    }
    let next = packets
        .iter()
        .map(|v| peel(p, hop, key, v))
        .collect::<Result<Vec<_>>>()?;
    let mut after: Vec<_> = next.iter().map(|v| Sha256::digest(v).to_vec()).collect();
    after.sort();
    if after != stage_set(p, hop + 1, m) {
        return Err("active peeled-output-set substitution refused".into());
    }
    Ok(next)
}

struct ReleasePlan {
    when: u64,
    origin: u64,
    tick: u64,
}
fn release_at(args: &mut Args, p: &Profile, hop: usize) -> Result<ReleasePlan> {
    let tick = args
        .optional("tick-ms")
        .map(|v| {
            v.to_string_lossy()
                .parse::<u64>()
                .map_err(|_| "invalid mix tick")
        })
        .transpose()?
        .unwrap_or(1000);
    let origin = args
        .optional("origin-ms")
        .map(|v| {
            v.to_string_lossy()
                .parse::<u64>()
                .map_err(|_| "invalid mix origin")
        })
        .transpose()?;
    if tick < 10 || tick > 60_000 {
        return Err("mix public tick bound".into());
    }
    if let Some(origin) = origin {
        let when = p
            .epoch
            .checked_add(hop as u64 + 1)
            .and_then(|n| n.checked_mul(tick))
            .and_then(|n| n.checked_add(origin))
            .ok_or("mix schedule lifetime exhausted")?;
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|_| "clock before origin")?
            .as_millis();
        if now > when as u128 {
            return Err("missed public mix release epoch; no catch-up burst/reprocessing".into());
        }
        return Ok(ReleasePlan { when, origin, tick });
    } else {
        return Err(
            "mix output needs explicit public --origin-ms; offline tests use internal functions"
                .into(),
        );
    }
}
fn bind_epoch_profile(
    root: &Path,
    p: &Profile,
    stage: usize,
    m: &[u8],
    plan: &ReleasePlan,
) -> Result<()> {
    let mut v = p.aad(stage);
    v.extend_from_slice(&plan.origin.to_le_bytes());
    v.extend_from_slice(&plan.tick.to_le_bytes());
    v.extend_from_slice(&Sha256::digest(m));
    let path = root.join(format!("epoch-{}-profile", p.epoch));
    if path.exists() {
        if read_private(&path, 1024)? != v {
            return Err(
                "changed registered cohort/clock profile in same epoch; preserve obligations"
                    .into(),
            );
        }
    } else {
        persist(&path, &v)?;
    }
    Ok(())
}
fn wait_release(when: u64) -> Result<()> {
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|_| "clock before origin")?
        .as_millis();
    if now > when as u128 {
        return Err("processing missed public release; preserve claim and no catch-up".into());
    }
    std::thread::sleep(Duration::from_millis(when - now as u64));
    Ok(())
}
fn num(args: &mut Args, name: &str, default: usize) -> Result<usize> {
    args.optional(name)
        .map(|v| {
            v.to_string_lossy()
                .parse()
                .map_err(|_| format!("invalid {name}"))
        })
        .unwrap_or(Ok(default))
}
/// The bound is the v1 secret size, so a v1 (2400-byte pure ML-KEM) key file is
/// read and refused by name instead of by a size bound.
fn read_key(path: &Path) -> Result<HybridSecret> {
    HybridSecret::from_bytes(&read_private(path, 2400)?)
}
fn consume_broadcast(state: &Path, p: &Profile, input: &[u8]) -> Result<Vec<Vec<u8>>> {
    let cells = unbatch(p, LAYERS, input)?;
    let mut opened = Vec::new();
    for e in fs::read_dir(state).map_err(|e| e.to_string())? {
        let e = e.map_err(|e| e.to_string())?;
        let name = e.file_name().to_string_lossy().into_owned();
        if !name.ends_with(".cap") {
            continue;
        }
        let v = read_private(&e.path(), 57)?;
        if v.len() != 57 || u64::from_le_bytes(v[..8].try_into().unwrap()) != p.epoch {
            continue;
        }
        let id = v[9..25].try_into().unwrap();
        let cap = v[25..57].try_into().unwrap();
        let stem = name.trim_end_matches(".cap");
        let spent = state.join(format!("{stem}.spent"));
        let cached = state.join(format!("{stem}.opened"));
        if cached.exists() {
            opened.push(read_private(&cached, p.payload)?);
            continue;
        }
        if spent.exists() {
            return Err(
                "consumed reply capability crash requires native exact recovery; never reuse"
                    .into(),
            );
        }
        let found: Vec<_> = cells
            .iter()
            .filter_map(|c| open_reply(p, id, cap, c).ok())
            .collect();
        if found.len() > 1 {
            return Err("malicious duplicate reply-capability drain attempt".into());
        }
        if let Some(v) = found.first() {
            persist(&spent, b"spent-before-delivery")?;
            persist(&cached, v)?;
            opened.push(v.clone());
        }
    }
    Ok(opened)
}
// Resident transport helpers reuse the frozen manifest, exact stage-set,
// envelope and claim checks. The fixed emission loop runs independently of
// these workers and never treats a physical continuation as Mini Pending.
pub(crate) fn live_cover(
    epoch: u64,
    width: usize,
    payload: usize,
    keys: &[Vec<u8>],
) -> Result<Vec<u8>> {
    let p = Profile {
        epoch,
        width,
        payload,
    };
    p.check()?;
    let (mut packet, route) = seal_with_route(&p, keys, random()?, random()?, None)?;
    packet.extend_from_slice(&route);
    Ok(packet)
}
/// Non-authoritative final broadcast cover. Every slot uses a freshly generated
/// discarded capability; no enrolled client can open a result or receipt.
/// One immutable batch is shared by ALL audience links for this epoch.
pub(crate) fn live_broadcast_cover(epoch: u64, width: usize, payload: usize) -> Result<Vec<u8>> {
    let p = Profile {
        epoch,
        width,
        payload,
    };
    p.check()?;
    let mut slots = Vec::with_capacity(width);
    for _ in 0..width {
        slots.push(reply(&p, random()?, random()?, &[])?);
    }
    batch(&p, LAYERS, &slots)
}
pub(crate) fn live_validate_broadcast(
    epoch: u64,
    width: usize,
    payload: usize,
    bytes: &[u8],
) -> Result<()> {
    let p = Profile {
        epoch,
        width,
        payload,
    };
    p.check()?;
    unbatch(&p, LAYERS, bytes).map(|_| ())
}
pub(crate) fn live_offer(
    epoch: u64,
    width: usize,
    payload: usize,
    keys: &[Vec<u8>],
    id: [u8; 16],
    reply_cap: [u8; 32],
    body: &[u8],
) -> Result<Vec<u8>> {
    let p = Profile {
        epoch,
        width,
        payload,
    };
    p.check()?;
    if body.is_empty() {
        return Err("live offer needs exact original native envelope".into());
    }
    let (mut packet, route) = seal_with_route(&p, keys, id, reply_cap, Some(body))?;
    packet.extend_from_slice(&route);
    Ok(packet)
}
/// A recovery epoch carries a physical fetch, not a replayed native operation.
/// Original access is private and immutable; the outer reply key is fresh.
pub(crate) fn live_fetch(
    epoch: u64,
    width: usize,
    payload: usize,
    keys: &[Vec<u8>],
    id: [u8; 16],
    original_class: usize,
    original_digest: [u8; 32],
    recovery_access: [u8; 32],
    reply_cap: [u8; 32],
) -> Result<Vec<u8>> {
    let p = Profile {
        epoch,
        width,
        payload,
    };
    p.check()?;
    if p.class() != 2 || original_class >= 3 || reply_cap == recovery_access {
        return Err("fetch requires reserved recovery epoch and distinct reply capability".into());
    }
    let mut body = vec![original_class as u8];
    body.extend_from_slice(&original_digest);
    body.extend_from_slice(&recovery_access);
    let mut v = core(&p, id, reply_cap, Some(&body))?;
    v[13] = 2;
    let (mut packet, route) = seal_core_with_route(&p, keys, v)?;
    packet.extend_from_slice(&route);
    Ok(packet)
}
// Only private preparation/drain workers use this bounded wait. Clocked
// emission never acquires this lock and always retains its fixed cover.
fn live_cap_lock(root: &Path) -> Result<transport::ServiceLock> {
    transport::service_lock_waiting(
        &root.join("service.lock"),
        mini_sdk::lock::Wait::Poll { tries: 2000, interval: Duration::from_millis(1) },
    )
}
pub(crate) fn live_save_cap(
    root: &Path,
    epoch: u64,
    width: usize,
    payload: usize,
    id: [u8; 16],
    cap: [u8; 32],
) -> Result<()> {
    let p = Profile {
        epoch,
        width,
        payload,
    };
    p.check()?;
    directory(root)?;
    let _lock = live_cap_lock(root)?;
    let mut record = epoch.to_le_bytes().to_vec();
    record.push(p.class() as u8);
    record.extend_from_slice(&id);
    record.extend_from_slice(&cap);
    let path = root.join(format!("{}-{}.cap", epoch, crate::hex(&id)));
    if path.exists() {
        if read_private(&path, 57)? != record {
            return Err("changed immutable reply capability".into());
        }
        Ok(())
    } else {
        let mut class_count = 0;
        for entry in fs::read_dir(root).map_err(|e| e.to_string())? {
            let entry = entry.map_err(|e| e.to_string())?;
            if entry.file_name().to_string_lossy().ends_with(".cap") {
                let retained = read_private(&entry.path(), 57)?;
                if retained.len() != 57 || retained[8] >= 3 {
                    return Err("malformed retained reply capability; preserve obligations".into());
                }
                if retained[8] as usize == p.class() {
                    class_count += 1;
                }
            }
        }
        if class_count >= [128, 64, 64][p.class()] {
            return Err(
                "reply capability class reservation full; accepted obligations retained".into(),
            );
        }
        persist(&path, &record)
    }
}
pub(crate) fn live_scan(
    root: &Path,
    epoch: u64,
    width: usize,
    payload: usize,
    broadcast: &[u8],
) -> Result<Vec<Vec<u8>>> {
    let p = Profile {
        epoch,
        width,
        payload,
    };
    p.check()?;
    directory(root)?;
    let _lock = live_cap_lock(root)?;
    consume_broadcast(root, &p, broadcast)
}
fn live_plan(p: &Profile, stage: usize, origin: u64, tick: u64) -> Result<ReleasePlan> {
    if !(10..=60000).contains(&tick) || stage > LAYERS {
        return Err("live mix tick/stage bound".into());
    }
    let when = p
        .epoch
        .checked_add(stage as u64 + 1)
        .and_then(|v| v.checked_mul(tick))
        .and_then(|v| v.checked_add(origin))
        .ok_or("live mix schedule lifetime exhausted")?;
    Ok(ReleasePlan { when, origin, tick })
}
pub(crate) fn live_register(
    root: &Path,
    epoch: u64,
    width: usize,
    payload: usize,
    contributions: &[Vec<u8>],
    auth: &[Vec<u8>],
    origin: u64,
    tick: u64,
) -> Result<Vec<u8>> {
    let p = Profile {
        epoch,
        width,
        payload,
    };
    p.check()?;
    directory(root)?;
    if contributions.len() != width || contributions.iter().any(|v| v.len() != p.size(0) + 160) {
        return Err("fixed enrolled contribution cohort incomplete".into());
    }
    let packets = contributions
        .iter()
        .map(|v| v[..p.size(0)].to_vec())
        .collect::<Vec<_>>();
    let routes = contributions
        .iter()
        .map(|v| v[p.size(0)..].to_vec())
        .collect::<Vec<_>>();
    let mut admitted = manifest(&p, &packets, &routes, auth)?;
    bind_epoch_profile(root, &p, 0, &admitted, &live_plan(&p, 0, origin, tick)?)?;
    admitted.extend_from_slice(&batch(&p, 0, &packets)?);
    Ok(admitted)
}
pub(crate) fn live_relay(
    root: &Path,
    epoch: u64,
    width: usize,
    payload: usize,
    hop: usize,
    keypath: &Path,
    auth: &[u8],
    segment: &[u8],
    origin: u64,
    tick: u64,
) -> Result<Vec<u8>> {
    let p = Profile {
        epoch,
        width,
        payload,
    };
    p.check()?;
    directory(root)?;
    if hop >= 3 {
        return Err("live relay cannot impersonate receiver".into());
    }
    let n = 18 + 160 * width + 128;
    if segment.len() != n + 19 + width * p.size(hop) {
        return Err("live stage exact shape".into());
    }
    let (admitted, input) = segment.split_at(n);
    let key = read_key(keypath)?;
    let mut next = prepare_transition(&p, hop, &key, input, admitted, auth)?;
    let admission = live_relay_admission(&p, hop, admitted, input, origin, tick)?;
    let stem = format!("live-epoch-{}-stage-{hop}", p.epoch);
    let claim = root.join(format!("{stem}.admitted"));
    let output = root.join(format!("{stem}.output"));
    // A live admission is a single immutable group of the profile, registered
    // sets, exact input and consumed-shuffle fence. Ordinary CLI journals keep
    // their existing codec; an old claim cannot silently become a new shuffle.
    if root.join(format!("epoch-{}-profile", p.epoch)).exists()
        || ["input", "claimed", "output"].iter().any(|suffix| {
            root.join(format!("epoch-{}-stage-{hop}.{suffix}", p.epoch))
                .exists()
        })
    {
        return Err("live relay refuses legacy epoch journal migration".into());
    }
    if claim.exists() {
        if read_private(&claim, 1024)? != admission {
            return Err("changed live relay admission/profile replay refused".into());
        }
        if !output.exists() {
            return Err(
                "live relay claimed without output; outcome uncertain, no new shuffle".into(),
            );
        }
        let cached = read_private(&output, n + 19 + p.width * p.size(hop + 1))?;
        if cached.get(..n) != Some(admitted) {
            return Err("live relay cached manifest mismatch".into());
        }
        let next = unbatch(&p, hop + 1, &cached[n..])?;
        let mut set: Vec<_> = next.iter().map(|v| Sha256::digest(v).to_vec()).collect();
        set.sort();
        if set != stage_set(&p, hop + 1, admitted) {
            return Err("live relay cached output set mismatch".into());
        }
        return Ok(cached);
    }
    if output.exists() {
        return Err("live relay orphan output without durable admission".into());
    }
    // Every incoming layer was authenticated above, before the one durable
    // claim. Failure/crash after this point preserves uncertainty permanently.
    persist(&claim, &admission)?;
    shuffle(&mut next)?;
    let mut out = admitted.to_vec();
    out.extend_from_slice(&batch(&p, hop + 1, &next)?);
    // Full canonical manifest+batch readback is durable before TCP preparation
    // can publish it. Its exact replay never regenerates a secret permutation.
    persist(&output, &out)?;
    Ok(out)
}
fn live_relay_admission(
    p: &Profile,
    hop: usize,
    manifest: &[u8],
    input: &[u8],
    origin: u64,
    tick: u64,
) -> Result<Vec<u8>> {
    let plan = live_plan(p, hop + 1, origin, tick)?;
    let mut v = b"Mini/live-relay-admission/v1".to_vec();
    v.extend_from_slice(&p.aad(hop + 1));
    v.extend_from_slice(&plan.origin.to_le_bytes());
    v.extend_from_slice(&plan.tick.to_le_bytes());
    v.extend_from_slice(&plan.when.to_le_bytes());
    v.extend_from_slice(&Sha256::digest(manifest));
    v.extend_from_slice(&Sha256::digest(input));
    Ok(v)
}
enum LiveCore {
    Ordinary([u8; 16], [u8; 32], Vec<u8>),
    Fetch([u8; 16], [u8; 32], usize, [u8; 32], [u8; 32]),
}
fn parse_live_core(p: &Profile, v: &[u8]) -> Result<LiveCore> {
    if v.get(13) != Some(&2) {
        let (id, cap, body) = parse_core(p, v)?;
        return Ok(LiveCore::Ordinary(id, cap, body));
    }
    // Reuse every original exact epoch/class/body/padding check for the new
    // fetch mode, then restrict its private payload to the fixed access proof.
    let mut normal = v.to_vec();
    normal[13] = 1;
    let (id, cap, body) = parse_core(p, &normal)?;
    if p.class() != 2 || body.len() != 65 || body[0] >= 3 || body[33..] == cap {
        return Err("physical fetch class/access/reply shape refused".into());
    }
    Ok(LiveCore::Fetch(
        id,
        cap,
        body[0] as usize,
        body[1..33].try_into().unwrap(),
        body[33..65].try_into().unwrap(),
    ))
}
pub(crate) fn live_mailbox(
    gateway: &native::AsyncDispatch,
    root: &Path,
    epoch: u64,
    width: usize,
    payload: usize,
    keypath: &Path,
    auth: &[u8],
    segment: &[u8],
    origin: u64,
    tick: u64,
) -> Result<Vec<u8>> {
    let p = Profile {
        epoch,
        width,
        payload,
    };
    p.check()?;
    directory(root)?;
    let n = 18 + 160 * width + 128;
    if segment.len() != n + 19 + width * p.size(3) {
        return Err("live receiver exact shape".into());
    }
    let (admitted, input) = segment.split_at(n);
    let key = read_key(keypath)?;
    let peeled = prepare_transition(&p, 3, &key, input, admitted, auth)?;
    let cores = peeled
        .iter()
        .map(|v| parse_live_core(&p, v))
        .collect::<Result<Vec<_>>>()?;
    let plan = live_plan(&p, 4, origin, tick)?;
    let mut admission = b"Mini/live-mailbox-admission/v1".to_vec();
    admission.extend_from_slice(&p.aad(4));
    for n in [plan.origin, plan.tick, plan.when, segment.len() as u64] {
        admission.extend_from_slice(&n.to_le_bytes());
    }
    // Full opaque input retained, not only its digest: source responsibility
    // survives even if no gateway request reached qualified durable admission.
    admission.extend_from_slice(segment);
    let claimed = root.join(format!("live-mailbox-epoch-{epoch}.admitted"));
    let output = root.join(format!("epoch-{epoch}-stage-3.output"));
    if root.join(format!("epoch-{epoch}-profile")).exists()
        || ["input", "claimed"].iter().any(|suffix| {
            root.join(format!("epoch-{epoch}-stage-3.{suffix}"))
                .exists()
        })
    {
        return Err("live mailbox refuses legacy journal migration".into());
    }
    if claimed.exists() {
        if read_private(&claimed, admission.len())? != admission {
            return Err("changed live mailbox exact admission/profile refused".into());
        }
        if !output.exists() {
            return Err("live mailbox claimed without output; uncertainty, no native redispatch or reshuffle".into());
        }
        let cached = read_private(&output, 19 + p.width * p.payload)?;
        unbatch(&p, LAYERS, &cached)?;
        return Ok(cached);
    }
    if output.exists() {
        return Err("live mailbox orphan output without admitted input".into());
    }
    // One fsynced immutable record binds profile, exact authenticated input and
    // consumed receiver fence before any physical gateway offer/fetch.
    persist(&claimed, &admission)?;
    let mut replies = Vec::with_capacity(width);
    for core in cores {
        let (id, cap, result) = match core {
            LiveCore::Ordinary(id, cap, body) if body.is_empty() => (id, cap, vec![0]),
            LiveCore::Ordinary(id, cap, body) => (
                id,
                cap,
                gateway
                    .offer(p.class(), id, &body, &cap)
                    .map(|s| s.transport_reply())
                    .unwrap_or_else(|_| vec![1]),
            ),
            LiveCore::Fetch(id, cap, class, digest, access) => (
                id,
                cap,
                gateway
                    .fetch(class, id, &digest, &access)
                    .map(|s| s.transport_reply())
                    .unwrap_or_else(|_| vec![2]),
            ),
        };
        replies.push(reply(&p, id, cap, &result)?);
    }
    shuffle(&mut replies)?;
    let out = batch(&p, LAYERS, &replies)?;
    save_batch(root, &p, 3, &out)?;
    Ok(out)
}
pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args
        .required("action")?
        .into_string()
        .map_err(|_| "invalid mix action")?;
    let state = PathBuf::from(args.required("state")?);
    directory(&state)?;
    let _lock = transport::service_lock(&state.join("service.lock"))?;
    if action == "registrar-key" {
        let secret = PathBuf::from(args.required("secret")?);
        args.finish()?;
        return persist(&secret, &random::<32>()?);
    }
    if action == "key" {
        let secret = PathBuf::from(args.required("secret")?);
        let public = PathBuf::from(args.required("public")?);
        args.finish()?;
        let k = HybridSecret::generate()?;
        persist(&secret, &k.to_bytes())?;
        return persist(&public, &k.public().to_bytes());
    }
    let p = Profile {
        epoch: num(&mut args, "epoch", 0)? as u64,
        width: num(&mut args, "width", 4)?,
        payload: num(&mut args, "payload-bytes", 65536)?,
    };
    p.check()?;
    match action.as_str() {
        "seal" => {
            let files = args
                .required("keys")?
                .into_string()
                .map_err(|_| "invalid pinned keys")?;
            let keys = files
                .split(',')
                .map(|v| read_private(Path::new(v), hybrid_kem::PUBLIC_LEN))
                .collect::<Result<Vec<_>>>()?;
            let input = args.optional("request").map(PathBuf::from);
            let mut body = input
                .as_ref()
                .map(|v| {
                    read_private(
                        v,
                        transport::CARRIED_LOOKUP_MAX_FRAME + transport::MAX_CONFIG + 38,
                    )
                })
                .transpose()?;
            let id = args
                .optional("operation-id")
                .map(|v| {
                    crate::decode_hex(&v.to_string_lossy())
                        .and_then(|v| v.try_into().map_err(|_| "operation-id16bytes".into()))
                })
                .transpose()?
                .unwrap_or(random()?);
            let output = PathBuf::from(args.required("output")?);
            args.finish()?;
            let cap = random()?;
            let mut refusal = None;
            if let Some(b) = &body {
                if b.len() > p.payload - CORE {
                    refusal = Some("native request exceeds public mailbox carrier class");
                }
                let mut class_count = 0;
                for e in fs::read_dir(&state).map_err(|e| e.to_string())? {
                    let e = e.map_err(|e| e.to_string())?;
                    if e.file_name().to_string_lossy().ends_with(".cap") {
                        let v = read_private(&e.path(), 57)?;
                        if v.len() == 57 && v[8] as usize == p.class() {
                            class_count += 1;
                        }
                    }
                }
                if class_count >= [128, 64, 64][p.class()] {
                    refusal = Some(
                        "reply capability class reservation full; accepted obligations retained",
                    );
                }
                let intent = state.join(format!("{}.intent", crate::hex(&id)));
                if intent.exists() {
                    if read_private(
                        &intent,
                        transport::CARRIED_LOOKUP_MAX_FRAME + transport::MAX_CONFIG + 38,
                    )? != *b
                    {
                        refusal = Some(
                            "changed native operation identity; previous exact obligation retained",
                        );
                    }
                } else if refusal.is_none() {
                    persist(&intent, b)?;
                }
            }
            if let Some(reason) = refusal {
                let mut v = vec![2];
                v.extend_from_slice(reason.as_bytes());
                persist(
                    &PathBuf::from(format!("{}.private-refusal", output.display())),
                    &v,
                )?;
                body = None; // ALWAYS a valid cover packet; no occupancy-triggered missing cohort slot.
            } else if body.is_some() {
                let mut record = p.epoch.to_le_bytes().to_vec();
                record.push(p.class() as u8);
                record.extend_from_slice(&id);
                record.extend_from_slice(&cap);
                persist(
                    &state.join(format!("{}-{}.cap", p.epoch, crate::hex(&id))),
                    &record,
                )?;
            }
            let (packet, route) = seal_with_route(&p, &keys, id, cap, body.as_deref())?;
            persist(&output, &packet)?;
            persist(
                &PathBuf::from(format!("{}.route", output.display())),
                &route,
            )
        }
        "batch" => {
            let input = args
                .required("inputs")?
                .into_string()
                .map_err(|_| "invalid packet paths")?;
            let packets = input
                .split(',')
                .map(|v| read_private(Path::new(v), p.size(0)))
                .collect::<Result<Vec<_>>>()?;
            let output = PathBuf::from(args.required("output")?);
            let commitment_paths = args
                .required("commitments")?
                .into_string()
                .map_err(|_| "invalid private commitment paths")?;
            let routes = commitment_paths
                .split(',')
                .map(|v| read_private(Path::new(v), 32 * (LAYERS + 1)))
                .collect::<Result<Vec<_>>>()?;
            let auth_paths = args
                .required("auth-keys")?
                .into_string()
                .map_err(|_| "invalid registrar authentication pins")?;
            let auth = auth_paths
                .split(',')
                .map(|v| read_private(Path::new(v), 32))
                .collect::<Result<Vec<_>>>()?;
            let manifest_path = PathBuf::from(args.required("manifest")?);
            let admitted = manifest(&p, &packets, &routes, &auth)?;
            let when = release_at(&mut args, &p, 0)?;
            args.finish()?;
            let out = batch(&p, 0, &packets)?;
            bind_epoch_profile(&state, &p, 0, &admitted, &when)?;
            wait_release(when.when)?;
            persist(&manifest_path, &admitted)?;
            persist(&output, &out)
        }
        "relay" | "mailbox" => {
            let hop = if action == "mailbox" {
                3
            } else {
                num(&mut args, "hop", 0)?
            };
            if hop > 3 {
                return Err("invalid hop".into());
            }
            let key = read_key(&PathBuf::from(args.required("secret")?))?;
            let input = read_private(
                &PathBuf::from(args.required("input")?),
                19 + p.width * p.size(hop),
            )?;
            let output = PathBuf::from(args.required("output")?);
            if action == "relay" && hop == 3 {
                return Err("relay cannot impersonate receiver stage".into());
            }
            let receiver = if hop == 3 {
                Some((
                    PathBuf::from(args.required("target")?),
                    transport::read_config(&PathBuf::from(args.required("config")?))?,
                ))
            } else {
                None
            };
            let admitted = read_private(
                &PathBuf::from(args.required("manifest")?),
                18 + (LAYERS + 1) * p.width * 32 + LAYERS * 32,
            )?;
            let auth = read_private(&PathBuf::from(args.required("auth-key")?), 32)?;
            verify_transition(&p, hop, &key, &input, &admitted, &auth)?;
            let when = release_at(&mut args, &p, hop + 1)?;
            args.finish()?;
            bind_epoch_profile(&state, &p, hop + 1, &admitted, &when)?;
            let out = if let Some((target, config)) = receiver {
                process_mailbox(&state, &p, &key, &input, &target, &config)?
            } else {
                process_relay(&state, &p, hop, &key, &input)?
            };
            wait_release(when.when)?;
            persist(&output, &out)
        }
        "scan" => {
            let input = read_private(
                &PathBuf::from(args.required("input")?),
                19 + p.width * p.payload,
            )?;
            let output = PathBuf::from(args.required("output")?);
            args.finish()?;
            let opened = consume_broadcast(&state, &p, &input)?;
            let mut out = Vec::new();
            for v in opened {
                out.extend_from_slice(&(v.len() as u32).to_le_bytes());
                out.extend_from_slice(&v);
            }
            persist(&output, &out)
        }
        _ => Err("mix action: key|registrar-key|seal|batch|relay|mailbox|scan".into()),
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::net::UnixListener;
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };
    fn scratch() -> PathBuf {
        let p =
            std::env::temp_dir().join(format!("mini-pq-{}", crate::hex(&random::<16>().unwrap())));
        directory(&p).unwrap();
        p
    }
    fn keys() -> (Vec<HybridSecret>, Vec<Vec<u8>>) {
        let secrets: Vec<_> = (0..LAYERS)
            .map(|_| HybridSecret::generate().unwrap())
            .collect();
        let publics = secrets.iter().map(|k| k.public().to_bytes()).collect();
        (secrets, publics)
    }
    #[test]
    fn live_cap_contention_waits_without_skipping_retained_cap_or_weakening_identity() {
        let root = std::env::temp_dir().join(format!(
            "mini-cap-wait-{}",
            crate::hex(&random::<16>().unwrap())
        ));
        directory(&root).unwrap();
        let lock = transport::service_lock(&root.join("service.lock")).unwrap();
        let worker_root = root.clone();
        let worker =
            std::thread::spawn(move || live_save_cap(&worker_root, 3, 2, 1024, [1; 16], [2; 32]));
        std::thread::sleep(Duration::from_millis(40));
        assert!(!root
            .join(format!("3-{}.cap", crate::hex(&[1; 16])))
            .exists());
        drop(lock);
        worker.join().unwrap().unwrap();
        live_save_cap(&root, 3, 2, 1024, [1; 16], [2; 32]).unwrap();
        assert!(live_save_cap(&root, 3, 2, 1024, [1; 16], [3; 32]).is_err());
    }
    #[test]
    fn scheduled_broadcast_cover_is_exact_batch_without_client_receipt_or_native_job() {
        let p = Profile {
            epoch: 3,
            width: 4,
            payload: 4096,
        };
        let cover = live_broadcast_cover(p.epoch, p.width, p.payload).unwrap();
        live_validate_broadcast(p.epoch, p.width, p.payload, &cover).unwrap();
        let packets = unbatch(&p, LAYERS, &cover).unwrap();
        assert_eq!(packets.len(), 4);
        for packet in packets {
            assert!(open_reply(&p, [7; 16], [8; 32], &packet).is_err());
        }
        assert!(live_validate_broadcast(4, p.width, p.payload, &cover).is_err());
        assert!(live_validate_broadcast(3, 2, p.payload, &cover).is_err());
        assert_ne!(
            cover,
            live_broadcast_cover(p.epoch, p.width, p.payload).unwrap()
        );
    }
    #[test]
    fn shared_crypto_preserves_maximum_profile_through_all_layers() {
        let p = Profile {
            epoch: 1,
            width: 2,
            payload: 262144,
        };
        p.check().unwrap();
        let (secret, public) = keys();
        let original = vec![19; p.payload];
        let mut packet = original.clone();
        for hop in (0..LAYERS).rev() {
            packet = wrap(&p, hop, &public[hop], &packet).unwrap();
            assert_eq!(packet.len(), p.size(hop));
        }
        for hop in 0..LAYERS {
            packet = peel(&p, hop, &secret[hop], &packet).unwrap();
            assert_eq!(packet.len(), p.size(hop + 1));
        }
        assert_eq!(packet, original);
    }
    #[test]
    fn hybrid_layers_open_only_for_their_recipient_and_refuse_tampering_of_either_component() {
        let p = Profile { epoch: 3, width: 2, payload: 1024 };
        p.check().unwrap();
        let (secret, public) = keys();
        let body = vec![5; p.size(1)];
        let packet = wrap(&p, 0, &public[0], &body).unwrap();
        assert_eq!(packet.len(), p.size(0));
        assert_eq!(OVERHEAD, 1120 + 24 + 32 + 16, "a layer is hybrid ciphertext + nonce + commitment + tag");
        assert_eq!(peel(&p, 0, &secret[0], &packet).unwrap(), body);
        // Wrong recipient; and a split identity: one right half with the other's other half.
        assert!(peel(&p, 0, &secret[1], &packet).is_err());
        assert!(peel(&p, 0, &secret[0].with_kem_of(&secret[1]).unwrap(), &packet).is_err());
        assert!(peel(&p, 0, &secret[0].with_x25519_of(&secret[1]).unwrap(), &packet).is_err());
        // Wrong hop (the AAD binds it), epoch and shape.
        assert!(peel(&p, 1, &secret[0], &packet).is_err());
        assert!(peel(&Profile { epoch: 4, ..p.clone() }, 0, &secret[0], &packet).is_err());
        // Either ciphertext component, the nonce, the commitment, the box: each refuses.
        for (what, at) in [
            ("X25519 ephemeral, first", 0),
            ("X25519 ephemeral, last", 31),
            ("ML-KEM ciphertext, first", 32),
            ("ML-KEM ciphertext, middle", 32 + 544),
            ("ML-KEM ciphertext, last", 1119),
            ("nonce", 1120),
            ("commitment", 1120 + 24),
            ("box", packet.len() - 1),
        ] {
            let mut bad = packet.clone();
            bad[at] ^= 1;
            assert!(peel(&p, 0, &secret[0], &bad).is_err(), "{what} flipped must refuse");
        }
    }
    #[test]
    fn v1_pure_ml_kem_mix_frames_and_keys_refuse_by_name() {
        let p = Profile { epoch: 3, width: 2, payload: 1024 };
        let (secret, public) = keys();
        // A bare 1184-byte ML-KEM key is not an operator key.
        let refusal = wrap(&p, 0, &public[0][32..], &vec![0; p.size(1)]).unwrap_err();
        assert!(refusal.contains("pre-hybrid"), "{refusal}");
        // A v1-shaped packet (1088-byte KEM ciphertext, 1160-byte layers).
        let refusal = peel(&p, 0, &secret[0], &vec![0; p.v1_size(0)]).unwrap_err();
        assert!(refusal.contains("v1 pure ML-KEM-768"), "{refusal}");
        // A v1 batch and a v1 manifest.
        let mut v1_batch = b"MPB1".to_vec();
        v1_batch.extend_from_slice(&vec![0; 15 + p.width * p.v1_size(0)]);
        let refusal = unbatch(&p, 0, &v1_batch).unwrap_err();
        assert!(refusal.contains("MPB1") && refusal.contains("v1 pure ML-KEM-768"), "{refusal}");
        let mut v1_manifest = b"MPM1".to_vec();
        v1_manifest.extend_from_slice(&[0; 200]);
        let refusal = verify_manifest(&p, 0, &v1_manifest, &[0; 32]).unwrap_err();
        assert!(refusal.contains("MPM1") && refusal.contains("v1 pure ML-KEM-768"), "{refusal}");
        // A v1 operator key file (2400-byte ML-KEM secret) is read and refused by name.
        let root = scratch();
        let path = root.join("v1.secret");
        persist(&path, &vec![7; 2400]).unwrap();
        let refusal = read_key(&path).err().unwrap();
        assert!(refusal.contains("pre-hybrid"), "{refusal}");
        // The v2 key file round-trips: the secret is a seed and regenerates the same public key.
        let path = root.join("v2.secret");
        persist(&path, &secret[0].to_bytes()).unwrap();
        assert_eq!(read_key(&path).unwrap().public().to_bytes(), public[0]);
    }
    #[test]
    fn live_mailbox_grouped_exact_input_replay_crash_and_orphan_fences() {
        let root = scratch();
        let (secrets, publics) = keys();
        let paths: Vec<_> = secrets
            .iter()
            .enumerate()
            .map(|(i, key)| {
                let path = root.join(format!("key-{i}"));
                persist(&path, &key.to_bytes()).unwrap();
                path
            })
            .collect();
        let auth: Vec<_> = (0..4).map(|i| vec![i + 1; 32]).collect();
        let mut segment = live_register(
            &root.join("registrar"),
            0,
            2,
            1024,
            &[
                live_cover(0, 2, 1024, &publics).unwrap(),
                live_cover(0, 2, 1024, &publics).unwrap(),
            ],
            &auth,
            1000,
            1000,
        )
        .unwrap();
        for hop in 0..3 {
            segment = live_relay(
                &root.join(format!("relay-{hop}")),
                0,
                2,
                1024,
                hop,
                &paths[hop],
                &auth[hop],
                &segment,
                1000,
                1000,
            )
            .unwrap();
        }
        let gateway = native::AsyncDispatch::open(
            &root.join("gateway"),
            &root.join("no-native.sock"),
            b"{}",
            4,
            32,
            950,
        )
        .unwrap();
        let receiver = root.join("receiver");
        let call = |state: &Path, origin| {
            live_mailbox(
                &gateway, state, 0, 2, 1024, &paths[3], &auth[3], &segment, origin, 1000,
            )
        };
        let out = call(&receiver, 1000).unwrap();
        assert_eq!(call(&receiver, 1000).unwrap(), out);
        assert!(call(&receiver, 2000).is_err());
        let admitted =
            read_private(&receiver.join("live-mailbox-epoch-0.admitted"), 65536).unwrap();
        assert!(admitted.ends_with(&segment));
        assert!(!receiver.join("epoch-0-profile").exists());
        assert!(!receiver.join("epoch-0-stage-3.input").exists());
        assert!(!receiver.join("epoch-0-stage-3.claimed").exists());
        let interrupted = root.join("interrupted");
        directory(&interrupted).unwrap();
        persist(
            &interrupted.join("live-mailbox-epoch-0.admitted"),
            &admitted,
        )
        .unwrap();
        assert!(call(&interrupted, 1000)
            .unwrap_err()
            .contains("uncertainty"));
        assert!(!interrupted.join("epoch-0-stage-3.output").exists());
        let orphan = root.join("orphan");
        directory(&orphan).unwrap();
        persist(&orphan.join("epoch-0-stage-3.output"), &out).unwrap();
        assert!(call(&orphan, 1000).unwrap_err().contains("orphan"));
        let legacy = root.join("legacy");
        directory(&legacy).unwrap();
        persist(&legacy.join("epoch-0-profile"), b"legacy").unwrap();
        assert!(call(&legacy, 1000).unwrap_err().contains("legacy"));
        let corrupt = root.join("corrupt");
        directory(&corrupt).unwrap();
        persist(&corrupt.join("live-mailbox-epoch-0.admitted"), &admitted).unwrap();
        persist(&corrupt.join("epoch-0-stage-3.output"), b"bad").unwrap();
        assert!(call(&corrupt, 1000).is_err());
        assert_eq!(
            std::fs::read_dir(root.join("gateway"))
                .unwrap()
                .filter_map(|e| e.ok())
                .filter(|e| e.path().extension().is_some_and(|x| x == "class"))
                .count(),
            0
        );
    }
    #[test]
    fn live_relay_grouped_admission_exact_replay_crash_and_conflict_fences() {
        let root = scratch();
        let (secret, public) = keys();
        let keypath = root.join("key");
        persist(&keypath, &secret[0].to_bytes()).unwrap();
        let p = Profile {
            epoch: 3,
            width: 2,
            payload: 1024,
        };
        let auth: Vec<_> = (0..4).map(|i| vec![i + 1; 32]).collect();
        let segment = live_register(
            &root.join("registrar"),
            p.epoch,
            p.width,
            p.payload,
            &[
                live_cover(p.epoch, p.width, p.payload, &public).unwrap(),
                live_cover(p.epoch, p.width, p.payload, &public).unwrap(),
            ],
            &auth,
            1000,
            1000,
        )
        .unwrap();
        let relay = |state: &Path, clock, mac: &[u8]| {
            live_relay(
                state, p.epoch, p.width, p.payload, 0, &keypath, mac, &segment, clock, 1000,
            )
        };
        let good = root.join("good");
        let out = relay(&good, 1000, &auth[0]).unwrap();
        assert_eq!(relay(&good, 1000, &auth[0]).unwrap(), out);
        assert_eq!(fs::read_dir(&good).unwrap().count(), 2);
        assert!(relay(&good, 1001, &auth[0]).is_err());
        assert!(relay(&good, 1000, &[99; 32]).is_err());
        let n = 18 + 160 * p.width + 128;
        let frame = live_relay_admission(&p, 0, &segment[..n], &segment[n..], 1000, 1000).unwrap();
        let crash = root.join("crash");
        directory(&crash).unwrap();
        persist(&crash.join("live-epoch-3-stage-0.admitted"), &frame).unwrap();
        assert!(relay(&crash, 1000, &auth[0])
            .unwrap_err()
            .contains("uncertain"));
        assert!(!crash.join("live-epoch-3-stage-0.output").exists());
        let changed = root.join("changed");
        directory(&changed).unwrap();
        let mut wrong = frame.clone();
        *wrong.last_mut().unwrap() ^= 1;
        persist(&changed.join("live-epoch-3-stage-0.admitted"), &wrong).unwrap();
        assert!(relay(&changed, 1000, &auth[0]).is_err());
        let orphan = root.join("orphan");
        directory(&orphan).unwrap();
        persist(&orphan.join("live-epoch-3-stage-0.output"), &out).unwrap();
        assert!(relay(&orphan, 1000, &auth[0]).is_err());
        let legacy = root.join("legacy");
        directory(&legacy).unwrap();
        persist(&legacy.join("epoch-3-stage-0.claimed"), b"claimed").unwrap();
        assert!(relay(&legacy, 1000, &auth[0]).is_err());
        assert!(!legacy.join("live-epoch-3-stage-0.admitted").exists());
        let unauth = root.join("unauth");
        assert!(relay(&unauth, 1000, &[99; 32]).is_err());
        assert_eq!(fs::read_dir(&unauth).unwrap().count(), 0);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn epoch_profile_binding_cannot_equivocate_clock_or_registered_sets() {
        let root = scratch();
        let p = Profile {
            epoch: 2,
            width: 2,
            payload: 1024,
        };
        let plan = ReleasePlan {
            when: 100,
            origin: 10,
            tick: 30,
        };
        bind_epoch_profile(&root, &p, 0, b"manifest", &plan).unwrap();
        bind_epoch_profile(&root, &p, 0, b"manifest", &plan).unwrap();
        assert!(bind_epoch_profile(&root, &p, 0, b"changedmanifest", &plan).is_err());
        assert!(bind_epoch_profile(
            &root,
            &p,
            0,
            b"manifest",
            &ReleasePlan {
                when: 101,
                origin: 11,
                tick: 30
            }
        )
        .is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn private_capacity_or_oversize_refusal_still_emits_registered_cover() {
        let root = scratch();
        let (secret, public) = keys();
        let mut paths = Vec::new();
        for (i, k) in public.iter().enumerate() {
            let path = root.join(format!("k{i}.pub"));
            persist(&path, k).unwrap();
            paths.push(path.to_string_lossy().into_owned());
        }
        let p = Profile {
            epoch: 3,
            width: 2,
            payload: 1024,
        };
        for exhausted in [false, true] {
            let state = root.join(if exhausted { "full" } else { "oversize" });
            directory(&state).unwrap();
            if exhausted {
                for i in 0..64 {
                    let mut v = p.epoch.to_le_bytes().to_vec();
                    v.push(2);
                    v.extend_from_slice(&[i; 16]);
                    v.extend_from_slice(&[i; 32]);
                    persist(&state.join(format!("old{i}.cap")), &v).unwrap();
                }
            }
            let request = state.join("request");
            persist(&request, &vec![9; if exhausted { 100 } else { 1024 }]).unwrap();
            let output = state.join("packet");
            let values = vec![
                ("action", "seal".to_owned()),
                ("state", state.to_string_lossy().into_owned()),
                ("keys", paths.join(",")),
                ("epoch", "3".to_owned()),
                ("width", "2".to_owned()),
                ("payload-bytes", "1024".to_owned()),
                ("request", request.to_string_lossy().into_owned()),
                ("output", output.to_string_lossy().into_owned()),
            ];
            run(Args {
                command: "mix".into(),
                values: values
                    .into_iter()
                    .map(|(k, v)| (format!("--{k}").into(), v.into()))
                    .collect(),
            })
            .unwrap();
            let mut packet = read_private(&output, p.size(0)).unwrap();
            assert_eq!(packet.len(), p.size(0));
            for hop in 0..LAYERS {
                packet = peel(&p, hop, &secret[hop], &packet).unwrap();
            }
            assert!(parse_core(&p, &packet).unwrap().2.is_empty());
            assert_eq!(
                read_private(
                    &PathBuf::from(format!("{}.private-refusal", output.display())),
                    1024
                )
                .unwrap()[0],
                2
            );
            assert_eq!(
                fs::read_dir(&state)
                    .unwrap()
                    .filter_map(|e| e.ok())
                    .filter(|e| e.file_name().to_string_lossy().ends_with(".cap"))
                    .count(),
                if exhausted { 64 } else { 0 }
            );
        }
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn authenticated_stage_sets_refuse_valid_replacement_and_corrupt_operator_forgery() {
        let p = Profile {
            epoch: 2,
            width: 2,
            payload: 1024,
        };
        let (keys, public) = keys();
        let auth: Vec<_> = (0..LAYERS).map(|i| vec![i as u8 + 1; 32]).collect();
        let mut packets = Vec::new();
        let mut routes = Vec::new();
        for i in 0..2 {
            let (packet, route) =
                seal_with_route(&p, &public, [i; 16], [i + 1; 32], Some(b"authorized inner"))
                    .unwrap();
            packets.push(packet);
            routes.push(route);
        }
        let m = manifest(&p, &packets, &routes, &auth).unwrap();
        let b = batch(&p, 0, &packets).unwrap();
        verify_transition(&p, 0, &keys[0], &b, &m, &auth[0]).unwrap();
        let replacement = seal_packet(
            &p,
            &public,
            [7; 16],
            [8; 32],
            Some(b"valid injected request"),
        )
        .unwrap();
        let substituted = batch(&p, 0, &[replacement, packets[1].clone()]).unwrap();
        assert!(verify_transition(&p, 0, &keys[0], &substituted, &m, &auth[0]).is_err());
        assert!(verify_manifest(&p, 1, &m, &auth[0]).is_err()); // compromised operator0 cannot authenticate to operator1
        let mut tampered = m.clone();
        tampered[50] ^= 1;
        assert!(verify_manifest(&p, 1, &tampered, &auth[1]).is_err());
        let root = scratch();
        for hop in 0..3 {
            let state = root.join(format!("r{hop}"));
            directory(&state).unwrap();
            let input = if hop == 0 {
                b.clone()
            } else {
                read_private(
                    &root.join(format!("r{}/epoch-2-stage-{}.output", hop - 1, hop - 1)),
                    100000,
                )
                .unwrap()
            };
            verify_transition(&p, hop, &keys[hop], &input, &m, &auth[hop]).unwrap();
            process_relay(&state, &p, hop, &keys[hop], &input).unwrap();
        }
        let last = read_private(&root.join("r2/epoch-2-stage-2.output"), 100000).unwrap();
        verify_transition(&p, 3, &keys[3], &last, &m, &auth[3]).unwrap();
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn reply_capability_duplicate_drain_and_consumed_crash_are_fenced() {
        let root = scratch();
        let p = Profile {
            epoch: 1,
            width: 2,
            payload: 1024,
        };
        let id = [8; 16];
        let cap = [4; 32];
        let mut record = p.epoch.to_le_bytes().to_vec();
        record.push(p.class() as u8);
        record.extend_from_slice(&id);
        record.extend_from_slice(&cap);
        let stem = format!("{}-{}", p.epoch, crate::hex(&id));
        persist(&root.join(format!("{stem}.cap")), &record).unwrap();
        let a = reply(&p, id, cap, b"first").unwrap();
        let b = reply(&p, id, cap, b"second").unwrap();
        assert!(consume_broadcast(&root, &p, &batch(&p, 4, &[a.clone(), b]).unwrap()).is_err());
        assert!(!root.join(format!("{stem}.spent")).exists());
        let other = reply(&p, [2; 16], [9; 32], b"other").unwrap();
        let input = batch(&p, 4, &[a, other]).unwrap();
        assert_eq!(
            consume_broadcast(&root, &p, &input).unwrap(),
            vec![b"first".to_vec()]
        );
        assert_eq!(
            consume_broadcast(&root, &p, &input).unwrap(),
            vec![b"first".to_vec()]
        );
        let crash = root.join("crash");
        directory(&crash).unwrap();
        persist(&crash.join(format!("{stem}.cap")), &record).unwrap();
        persist(&crash.join(format!("{stem}.spent")), b"burned").unwrap();
        assert!(consume_broadcast(&crash, &p, &input).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn async_custody_reply_cap_reservation_preserves_exact_retry_at_capacity() {
        let root = scratch();
        for n in 0..64 {
            live_save_cap(&root, 3 + 4 * n, 2, 1024, [1; 16], [2; 32]).unwrap();
        }
        // An exact retained capability is reusable for fetching its opened
        // result, but a new epoch cannot allocate an unbounded obligation.
        live_save_cap(&root, 3, 2, 1024, [1; 16], [2; 32]).unwrap();
        assert!(live_save_cap(&root, 259, 2, 1024, [1; 16], [2; 32]).is_err());
        assert!(!root
            .join(format!("259-{}.cap", crate::hex(&[1; 16])))
            .exists());
        assert!(live_save_cap(&root, 3, 2, 1024, [1; 16], [3; 32]).is_err());
    }
    #[test]
    fn async_custody_live_mailbox_continuation_then_bound_fetch_without_second_dispatch() {
        use std::sync::mpsc;
        use std::time::Instant;
        let root = scratch();
        let (secret, public) = keys();
        let paths: Vec<_> = secret
            .iter()
            .enumerate()
            .map(|(i, k)| {
                let path = root.join(format!("key-{i}"));
                persist(&path, &k.to_bytes()).unwrap();
                path
            })
            .collect();
        let auth: Vec<_> = (0..4).map(|i| vec![i + 1; 32]).collect();
        let target = root.join("native.sock");
        let listener = UnixListener::bind(&target).unwrap();
        let body = [vec![1, 2, 0, 0, 0], b"{}".to_vec(), vec![12]].concat();
        let expected = body.clone();
        let (started, observed) = mpsc::channel();
        let (release, hold) = mpsc::channel();
        let host = std::thread::spawn(move || {
            let (mut s, _) = listener.accept().unwrap();
            assert_eq!(transport::read_frame(&mut s).unwrap().unwrap(), expected);
            started.send(()).unwrap();
            hold.recv().unwrap();
            transport::write_frame(&mut s, b"\x0cexact-native-live-reply").unwrap();
        });
        let gateway =
            native::AsyncDispatch::open(&root.join("gateway"), &target, b"{}", 4, 32, 4096 - 74)
                .unwrap();
        let id = [13; 16];
        let access = [23; 32];
        let fresh_cap = [24; 32];
        let digest: [u8; 32] = Sha256::digest(&body).into();
        let traverse = |epoch, real: Vec<u8>| {
            let mut segment = live_register(
                &root.join("registrar"),
                epoch,
                2,
                4096,
                &[real, live_cover(epoch, 2, 4096, &public).unwrap()],
                &auth,
                1000,
                1000,
            )
            .unwrap();
            for hop in 0..3 {
                segment = live_relay(
                    &root.join(format!("relay-{hop}")),
                    epoch,
                    2,
                    4096,
                    hop,
                    &paths[hop],
                    &auth[hop],
                    &segment,
                    1000,
                    1000,
                )
                .unwrap();
            }
            live_mailbox(
                &gateway,
                &root.join("receiver"),
                epoch,
                2,
                4096,
                &paths[3],
                &auth[3],
                &segment,
                1000,
                1000,
            )
            .unwrap()
        };
        let client = root.join("client");
        live_save_cap(&client, 0, 2, 4096, id, access).unwrap();
        let original = live_offer(0, 2, 4096, &public, id, access, &body).unwrap();
        let first = traverse(0, original);
        observed.recv_timeout(Duration::from_secs(3)).unwrap();
        let opened = live_scan(&client, 0, 2, 4096, &first).unwrap();
        assert_eq!(opened.len(), 1);
        assert_eq!(opened[0][0], 3); // physical custody only
        release.send(()).unwrap();
        host.join().unwrap();
        let until = Instant::now() + Duration::from_secs(3);
        while !matches!(
            gateway.fetch(0, id, &digest, &access).unwrap(),
            native::DispatchState::Ready(_)
        ) {
            assert!(Instant::now() < until);
            std::thread::yield_now();
        }
        // Same exact original class/body/access may be offered in another
        // scheduled application epoch. Native custody returns its cached reply;
        // the first native listener is already closed, so redispatch would fail.
        live_save_cap(&client, 4, 2, 4096, id, access).unwrap();
        let resent = traverse(
            4,
            live_offer(4, 2, 4096, &public, id, access, &body).unwrap(),
        );
        assert_eq!(
            live_scan(&client, 4, 2, 4096, &resent).unwrap(),
            vec![b"\0\x0cexact-native-live-reply".to_vec()]
        );
        live_save_cap(&client, 3, 2, 4096, id, fresh_cap).unwrap();
        let recovered = traverse(
            3,
            live_fetch(3, 2, 4096, &public, id, 0, digest, access, fresh_cap).unwrap(),
        );
        assert_eq!(
            live_scan(&client, 3, 2, 4096, &recovered).unwrap(),
            vec![b"\0\x0cexact-native-live-reply".to_vec()]
        );
        assert_eq!(
            live_scan(&client, 3, 2, 4096, &recovered).unwrap(),
            vec![b"\0\x0cexact-native-live-reply".to_vec()]
        );
        assert!(live_fetch(1, 2, 4096, &public, id, 0, digest, access, fresh_cap).is_err());
        assert!(live_fetch(3, 2, 4096, &public, id, 0, digest, access, access).is_err());
        assert!(live_save_cap(&client, 3, 2, 4096, id, [99; 32]).is_err());
        let wrong = traverse(
            7,
            live_fetch(7, 2, 4096, &public, id, 0, digest, [99; 32], [98; 32]).unwrap(),
        );
        let p = Profile {
            epoch: 7,
            width: 2,
            payload: 4096,
        };
        assert_eq!(
            unbatch(&p, 4, &wrong)
                .unwrap()
                .iter()
                .filter_map(|v| open_reply(&p, id, [98; 32], v).ok())
                .collect::<Vec<_>>(),
            vec![vec![2]]
        );
    }
    #[test]
    fn pq_multihop_native_delivery_broadcast_and_replay_fence() {
        let p = Profile {
            epoch: 3,
            width: 4,
            payload: 4096,
        };
        let root = scratch();
        let (secret, public) = keys();
        let target = root.join("host.sock");
        let listener = UnixListener::bind(&target).unwrap();
        let body = [vec![1, 2, 0, 0, 0], b"{}".to_vec(), vec![12]].concat();
        let calls = Arc::new(AtomicUsize::new(0));
        let counted = calls.clone();
        let expected = body.clone();
        let host = std::thread::spawn(move || {
            let (mut s, _) = listener.accept().unwrap();
            assert_eq!(transport::read_frame(&mut s).unwrap().unwrap(), expected);
            counted.fetch_add(1, Ordering::SeqCst);
            transport::write_frame(&mut s, b"\x0cactual-native-reply").unwrap();
        });
        let id = [3; 16];
        let cap = [6; 32];
        let mut packets = vec![seal_packet(&p, &public, id, cap, Some(&body)).unwrap()];
        for _ in 1..p.width {
            packets.push(
                seal_packet(&p, &public, random().unwrap(), random().unwrap(), None).unwrap(),
            );
        }
        let mut b = batch(&p, 0, &packets).unwrap();
        for hop in 0..3 {
            let state = root.join(format!("relay{hop}"));
            directory(&state).unwrap();
            let next = process_relay(&state, &p, hop, &secret[hop], &b).unwrap();
            assert_eq!(
                process_relay(&state, &p, hop, &secret[hop], &b).unwrap(),
                next
            );
            b = next;
        }
        let state = root.join("mailbox");
        directory(&state).unwrap();
        let out = process_mailbox(&state, &p, &secret[3], &b, &target, b"{}").unwrap();
        assert_eq!(
            process_mailbox(&state, &p, &secret[3], &b, &target, b"{}").unwrap(),
            out
        );
        let cells = unbatch(&p, 4, &out).unwrap();
        let own: Vec<_> = cells
            .iter()
            .filter_map(|v| open_reply(&p, id, cap, v).ok())
            .collect();
        assert_eq!(own, vec![b"\0\x0cactual-native-reply".to_vec()]);
        host.join().unwrap();
        assert_eq!(calls.load(Ordering::SeqCst), 1);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn malicious_tag_epoch_replay_and_reply_drain_refuse() {
        let p = Profile {
            epoch: 0,
            width: 2,
            payload: 1024,
        };
        let (secret, public) = keys();
        let original = seal_packet(&p, &public, [1; 16], [2; 32], Some(b"body")).unwrap();
        let dummy = seal_packet(&p, &public, [3; 16], [4; 32], None).unwrap();
        for pos in [0, 1090, 1130, 1200] {
            let mut tagged = original.clone();
            tagged[pos] ^= 1;
            assert!(peel(&p, 0, &secret[0], &tagged).is_err());
        }
        let mut other = p.clone();
        other.epoch = 1;
        assert!(peel(&other, 0, &secret[0], &original).is_err());
        assert!(unbatch(
            &p,
            0,
            &batch(&p, 0, &[original.clone(), original.clone()]).unwrap()
        )
        .is_err());
        let root = scratch();
        let state = root.join("relay");
        directory(&state).unwrap();
        let b = batch(&p, 0, &[original, dummy]).unwrap();
        process_relay(&state, &p, 0, &secret[0], &b).unwrap();
        let mut changed = b.clone();
        changed[30] ^= 1;
        assert!(process_relay(&state, &p, 0, &secret[0], &changed).is_err());
        let reply = reply(&p, [1; 16], [2; 32], b"native").unwrap();
        assert_eq!(open_reply(&p, [1; 16], [2; 32], &reply).unwrap(), b"native");
        assert!(open_reply(&p, [9; 16], [2; 32], &reply).is_err());
        assert!(open_reply(&other, [1; 16], [2; 32], &reply).is_err());
        let mut tag = reply;
        tag[70] ^= 1;
        assert!(open_reply(&p, [1; 16], [2; 32], &tag).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn crash_after_batch_claim_does_not_repeat_native_dispatch_or_shuffle() {
        let root = scratch();
        let p = Profile {
            epoch: 7,
            width: 2,
            payload: 1024,
        };
        assert!(claim(&root, &p, 0, b"exact epoch").unwrap().is_none());
        assert!(claim(&root, &p, 0, b"exact epoch").is_err());
        assert!(claim(&root, &p, 0, b"changed epoch").is_err());
        fs::remove_dir_all(root).unwrap();
    }
}
