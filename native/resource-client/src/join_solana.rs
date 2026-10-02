//! `mini join --solana | --wait | --renew`: enrol yourself by paying (PAY.md §11.6).
//!
//!   mini join --solana --host HOST --config PINNED-CONFIG.json (--socket SOCKET | --view PAY-VIEW.bin)
//!                      --enrol ENROL.json --dir NEW-JOIN-DIR [--key MINI.key] [--ssh-key KEY] [--name N]
//!   mini join --wait   --host HOST --config PINNED-CONFIG.json --socket SOCKET --dir JOIN-DIR
//!                      [--signature TX-BASE58] [--timeout SECONDS] [--interval SECONDS]
//!   mini join --renew  --host HOST --config PINNED-CONFIG.json (--socket SOCKET | --view PAY-VIEW.bin)
//!                      --enrol ENROL.json --dir JOIN-DIR
//!
//! `--solana` makes (or takes) the Mini key HERE — it never leaves this machine — signs the two
//! possessions (the Mini key over `"DREGG/PAY/ENROL/POSSESSION/v1" ‖ mint ‖ address ‖ sshBlob`;
//! the ssh key through `ssh-keygen -Y sign -n dregg-enrol@v1` over `mint ‖ address ‖ miniKey`),
//! and prints the enrollment address, the exact 400-byte memo (`Kernel/PayEnrolMemo.lean`
//! `encode`), the amount and a Solana Pay link. It submits nothing: the friend pays from their
//! own wallet. The memo is checked three ways before it is printed: both signatures verify
//! here, the Host's own codec (`inspect pay-enrol-memo`) reads back the same four fields, and
//! the enrollment address in ENROL.json (published by the operator) equals the pay view's book
//! row at the tariff's enrollment index.
//!
//! `--wait` polls the public enrollment view (op 112) for this Mini key; `--renew` prints the
//! same memo again with one node week's amount (the kernel decides renewal; a lapsed friend
//! cannot log in, so the memo is their renewal path).
//!
//! `--remote` may replace the socket. The local Host supplies codecs/derived enrollment
//! identities. `--wait` creates a Mini workspace; --birth-context supplies the deployment
//! genesis/template needed to create apps from the member's own account. The v1 payment
//! memo carries no next-key commitment; this enrollment has no prerotation promise.

use super::*;
use ed25519_dalek::{Signature, Verifier, VerifyingKey};
use sha2::{Sha256, Sha512};

const POSSESSION_TAG: &[u8] = b"DREGG/PAY/ENROL/POSSESSION/v1";
const SSHSIG_NAMESPACE: &str = "dregg-enrol@v1";
/// `string "ssh-ed25519" ‖ uint32 32`: the 19 bytes before an ssh-ed25519 key in its blob.
const SSH_BLOB_PREFIX: [u8; 19] = [
    0, 0, 0, 11, b's', b's', b'h', b'-', b'e', b'd', b'2', b'5', b'5', b'1', b'9', 0, 0, 0, 32,
];
const MEMO_LENGTH: usize = 400;
/// The template's value: the operator has not published the enrollment address yet.
const ADDRESS_PLACEHOLDER: &str = "EMBER_ENROL_ADDRESS";
const QUOTE_OP: u8 = 121;
const ENROLMENT_VIEW_OP: u8 = 112;
const B64: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

// ---------------------------------------------------------------- the memo (PayEnrolMemo)

/// The four memo fields, exactly `Kernel.PayEnrolMemo.Memo`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Memo {
    pub mini_key: [u8; 32],
    pub ssh_key: [u8; 32],
    pub mini_sig: [u8; 64],
    pub ssh_sig: [u8; 64],
}

pub(crate) fn ssh_blob(key: &[u8; 32]) -> Vec<u8> {
    [SSH_BLOB_PREFIX.as_slice(), key].concat()
}

pub(crate) fn b64_encode(bytes: &[u8]) -> String {
    let mut out = String::new();
    for chunk in bytes.chunks(3) {
        let n = chunk
            .iter()
            .enumerate()
            .fold(0u32, |n, (i, b)| n | (u32::from(*b) << (16 - 8 * i)));
        for i in 0..=chunk.len() {
            out.push(B64[((n >> (18 - 6 * i)) & 63) as usize] as char);
        }
        for _ in chunk.len()..3 {
            out.push('=');
        }
    }
    out
}

pub(crate) fn b64_decode(text: &str) -> Result<Vec<u8>> {
    let text = text.trim_end_matches('=');
    let mut bits = 0u32;
    let mut count = 0;
    let mut out = Vec::new();
    for c in text.bytes() {
        let value = B64
            .iter()
            .position(|b| *b == c)
            .ok_or("invalid base64")? as u32;
        bits = (bits << 6) | value;
        count += 6;
        if count >= 8 {
            count -= 8;
            out.push((bits >> count) as u8);
            bits &= (1 << count) - 1;
        }
    }
    Ok(out)
}

/// `Kernel.PayEnrolMemo.encode` (Kernel/PayEnrolMemo.lean:318):
/// `enrol:v1:<hex miniKey>:<unpadded base64 sshBlob>:<hex miniSig>:<hex sshSig>`. The 51-byte
/// blob is a multiple of three, so its base64 has no padding to strip.
pub(crate) fn encode_memo(memo: &Memo) -> String {
    format!(
        "enrol:v1:{}:{}:{}:{}",
        hex(&memo.mini_key),
        b64_encode(&ssh_blob(&memo.ssh_key)).trim_end_matches('='),
        hex(&memo.mini_sig),
        hex(&memo.ssh_sig)
    )
}

/// `miniFrame`: what the Mini key signs.
pub(crate) fn possession_frame(mint: &[u8; 32], address: &[u8; 32], ssh_key: &[u8; 32]) -> Vec<u8> {
    [POSSESSION_TAG, mint.as_slice(), address.as_slice(), &ssh_blob(ssh_key)].concat()
}

/// `sshsigMessage`: what the ssh key signs through SSHSIG.
pub(crate) fn sshsig_message(mint: &[u8; 32], address: &[u8; 32], mini_key: &[u8; 32]) -> Vec<u8> {
    [mint.as_slice(), address.as_slice(), mini_key.as_slice()].concat()
}

fn ssh_string(bytes: &[u8]) -> Vec<u8> {
    [(bytes.len() as u32).to_be_bytes().as_slice(), bytes].concat()
}

/// `sshsigSignedData`: PROTOCOL.sshsig's signed bytes over SHA-512 of the message.
fn sshsig_signed_data(message: &[u8]) -> Vec<u8> {
    sshsig_signed_data_for(SSHSIG_NAMESPACE, message)
}

pub(crate) fn sshsig_signed_data_for(namespace: &str, message: &[u8]) -> Vec<u8> {
    let digest = Sha512::digest(message);
    [
        b"SSHSIG".as_slice(),
        &ssh_string(namespace.as_bytes()),
        &ssh_string(&[]),
        &ssh_string(b"sha512"),
        &ssh_string(&digest),
    ]
    .concat()
}

fn take_string<'a>(bytes: &'a [u8], at: &mut usize) -> Result<&'a [u8]> {
    let length = bytes
        .get(*at..*at + 4)
        .ok_or("SSHSIG truncated")?;
    let length = u32::from_be_bytes(length.try_into().unwrap()) as usize;
    let value = bytes
        .get(*at + 4..*at + 4 + length)
        .ok_or("SSHSIG truncated")?;
    *at += 4 + length;
    Ok(value)
}

/// The raw Ed25519 signature inside `ssh-keygen -Y sign`'s armoured SSHSIG, after checking
/// every other field: the signer's blob, the namespace, the empty reserved field, `sha512`,
/// and an `ssh-ed25519` signature of 64 bytes.
pub(crate) fn sshsig_raw_signature(armoured: &str, expected_blob: &[u8]) -> Result<[u8; 64]> {
    sshsig_raw_signature_for(armoured, expected_blob, SSHSIG_NAMESPACE)
}

pub(crate) fn sshsig_raw_signature_for(armoured: &str, expected_blob: &[u8], expected_namespace: &str) -> Result<[u8; 64]> {
    let mut lines = armoured.lines().map(str::trim).filter(|line| !line.is_empty());
    if lines.next() != Some("-----BEGIN SSH SIGNATURE-----") {
        return Err("not an armoured SSH signature".into());
    }
    let mut body = String::new();
    let mut ended = false;
    for line in lines {
        if line == "-----END SSH SIGNATURE-----" {
            ended = true;
            break;
        }
        body.push_str(line);
    }
    if !ended {
        return Err("unterminated SSH signature armour".into());
    }
    let body = b64_decode(&body)?;
    if body.get(..6) != Some(b"SSHSIG".as_slice())
        || body.get(6..10) != Some(1u32.to_be_bytes().as_slice())
    {
        return Err("not an SSHSIG v1 blob".into());
    }
    let mut at = 10;
    let public = take_string(&body, &mut at)?;
    let namespace = take_string(&body, &mut at)?;
    let reserved = take_string(&body, &mut at)?;
    let hash = take_string(&body, &mut at)?;
    let signature = take_string(&body, &mut at)?;
    if at != body.len() {
        return Err("SSHSIG has trailing bytes".into());
    }
    if public != expected_blob {
        return Err("SSHSIG was made by another key than the one being enrolled".into());
    }
    if namespace != expected_namespace.as_bytes() || !reserved.is_empty() || hash != b"sha512" {
        return Err(format!("SSHSIG is not over namespace {expected_namespace} with sha512"));
    }
    let mut inner = 0;
    if take_string(signature, &mut inner)? != b"ssh-ed25519" {
        return Err("SSHSIG signature is not ssh-ed25519".into());
    }
    let raw = take_string(signature, &mut inner)?;
    if inner != signature.len() {
        return Err("SSHSIG signature has trailing bytes".into());
    }
    raw.try_into()
        .map_err(|_| "SSHSIG Ed25519 signature is not 64 bytes".to_owned())
}

/// The ssh public key line of KEY.pub: exactly one `ssh-ed25519` key. A FIDO key
/// (`sk-ssh-ed25519@openssh.com`) is refused by name: its SSHSIG signs a different structure
/// (flags and a counter) and its blob is not `ssh-ed25519`, so the kernel would journal the
/// payment `memoMalformed` (P3b-1, `memoBadSshKey`).
pub(crate) fn ssh_public_key(line: &str) -> Result<[u8; 32]> {
    let mut words = line.split_whitespace();
    let kind = words.next().ok_or("the ssh public key file is empty")?;
    if kind.starts_with("sk-") {
        return Err(format!(
            "fidoKeyRefused: {kind} is a FIDO/security-key ssh key; self-enrollment accepts only \
             a plain ssh-ed25519 key (make one with `ssh-keygen -t ed25519`)"
        ));
    }
    if kind != "ssh-ed25519" {
        return Err(format!(
            "notEd25519: {kind} keys are refused; self-enrollment accepts only ssh-ed25519"
        ));
    }
    let blob = b64_decode(words.next().ok_or("the ssh public key line has no key")?)?;
    if blob.len() != 51 || blob[..19] != SSH_BLOB_PREFIX {
        return Err("notEd25519: the key blob is not one ssh-ed25519 key".into());
    }
    Ok(blob[19..].try_into().unwrap())
}

// ---------------------------------------------------------------- inputs

/// The operator's published enrollment address (ENROL.json), base58, and the box's ssh target.
struct Pin {
    address: [u8; 32],
    login: String,
}

fn load_pin(path: &Path) -> Result<Pin> {
    let value = workspace::bounded_json(path)?;
    if value.get("type").and_then(Value::as_str) != Some("minidregg-enrol-pin-v1") {
        return Err(format!("{} is not a minidregg-enrol-pin-v1", path.display()));
    }
    let address = value
        .get("enrolAddress")
        .and_then(Value::as_str)
        .ok_or("ENROL.json lacks enrolAddress")?;
    if address.is_empty() || address == ADDRESS_PLACEHOLDER {
        return Err(format!(
            "{ADDRESS_PLACEHOLDER} is unset in {}: the operator has not published the enrollment \
             address; refusing to print a memo for an unknown address",
            path.display()
        ));
    }
    let address: [u8; 32] = bs58::decode(address)
        .into_vec()
        .ok()
        .and_then(|bytes| bytes.try_into().ok())
        .ok_or("enrolAddress is not a base58 32-byte Solana address")?;
    let login = value
        .get("login")
        .and_then(Value::as_str)
        .ok_or("ENROL.json lacks login (the box's ssh target, e.g. mini@HOST)")?
        .to_owned();
    Ok(Pin { address, login })
}

fn fixed<const N: usize>(text: &str, field: &str) -> Result<[u8; N]> {
    decode_hex(text)?
        .try_into()
        .map_err(|_| format!("{field} must be {N} bytes"))
}

fn field<'a>(value: &'a Value, name: &str) -> Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("Host JSON lacks {name}"))
}

/// A decimal the Host renders as a string (or a JSON number in the pinned config).
fn natural(value: &Value, name: &str) -> Result<u128> {
    match value.get(name) {
        Some(Value::String(text)) if !text.is_empty() && text.bytes().all(|b| b.is_ascii_digit()) => {
            text.parse().map_err(|_| format!("{name} out of range"))
        }
        Some(Value::Number(number)) => number
            .as_u64()
            .map(u128::from)
            .ok_or_else(|| format!("{name} must be a natural number")),
        _ => Err(format!("{name} must be a natural number")),
    }
}

fn frame_body(frame: &[u8], operation: u8) -> Result<&[u8]> {
    match frame {
        [actual, body @ ..] if *actual == operation => Ok(body),
        [255, body @ ..] => Err(format!(
            "Host refused op{operation}: {}",
            String::from_utf8_lossy(body)
        )),
        _ => Err(format!("op{operation} returned an invalid frame")),
    }
}

/// Payment amounts are source-owned quote fields, never a client price formula.
struct Terms {
    address: [u8; 32],
    mint: [u8; 32],
    token_program: [u8; 32],
    decimals: u32,
    quote: Value,
    bootstrap_metadata: Option<Value>,
}

impl Terms {
    fn display(&self, atomic: u128) -> String {
        let scale = 10u128.pow(self.decimals);
        let fraction = format!("{:0width$}", atomic % scale, width = self.decimals as usize);
        let fraction = fraction.trim_end_matches('0');
        if fraction.is_empty() { (atomic / scale).to_string() }
        else { format!("{}.{fraction}", atomic / scale) }
    }
}

fn terms(quote: Value, config: &Path, pin: &Pin, mini_key: &[u8;32], mode: &str,
         weeks: &str, starter: Option<&str>) -> Result<Terms> {
    if field(&quote,"type")? != "minidregg-pay-enrollment-quote-v1"
        || field(&quote,"miniKey")? != hex(mini_key) || field(&quote,"mode")? != mode
        || field(&quote,"requestedWeeks")? != weeks || field(&quote,"grantedWeeks")? != weeks
        || quote.get("priceReserved") != Some(&json!(false))
    { return Err("Host quote differs from requested key, mode, duration, or protocol".into()); }
    if let Some(starter) = starter {
        if field(&quote,"requestedStarterCredit")? != starter {
            return Err("Host quote differs from requested starter credit".into());
        }
    }
    let deployment = workspace::bounded_json(config)?;
    if natural(&quote,"domain")? != natural(&deployment,"domain")? {
        return Err("Host quote belongs to another deployment".into());
    }
    let address = fixed(field(&quote,"enrolAddress")?,"enrolAddress")?;
    if address != pin.address {
        return Err(format!("the box's enrollment row {} differs from the published enrolAddress {}; refusing",
            bs58::encode(address).into_string(),bs58::encode(pin.address).into_string()));
    }
    // Bounded native display, not a recomputation of any fee or split. The
    // exact source-owned amount remains verbatim in the retained quote.
    for name in ["atomicAmount","totalCredit","birthFee","membershipCredit","spendableRemainder",
                 "requestedStarterCredit","minimumEntryCredit","weekCredit","roundingCredit"] {
        natural(&quote,name)?;
    }
    let decimals = u32::try_from(natural(&quote,"decimals")?).map_err(|_| "decimals out of range")?;
    if decimals > 38 { return Err("token decimals exceed exact native amount display".into()); }
    Ok(Terms {address,mint:fixed(field(&quote,"mint")?,"mint")?,
        token_program:fixed(field(&quote,"tokenProgram")?,"tokenProgram")?,decimals,quote,bootstrap_metadata:None})
}

fn quoted_terms(common: &Common, pin: &Pin, mini_key: &[u8;32], mode: &str) -> Result<Terms> {
    let request = json!({"miniKey":hex(mini_key),"mode":mode,"weeks":common.weeks,
        "starterCredit":common.starter});
    let mut metadata = None;
    let quote = if let Some(url) = &common.bootstrap_url {
        metadata = Some(bootstrap_metadata(common,url,Some(&pin.login))?);
        bootstrap_request(common,url,"/quote",Some(&request))?
    } else if let Some(path) = &common.quote {
        workspace::bounded_json(path)?
    } else {
        let socket = SOCKET.get().ok_or("a per-key Host quote needs --socket/--remote, or --quote QUOTE.json with --key for offline preparation")?;
        let frame = session_invoke(&common.host,socket,&common.config,QUOTE_OP,
            &serde_json::to_vec(&request).map_err(|e|e.to_string())?)?;
        serde_json::from_slice(frame_body(&frame,QUOTE_OP)?).map_err(|e|format!("invalid Host quote JSON: {e}"))?
    };
    let mut terms = terms(quote,&common.config,pin,mini_key,mode,&common.weeks,common.starter.as_deref())?;
    terms.bootstrap_metadata = metadata;
    Ok(terms)
}

fn print_quote(terms: &Terms) -> Result<()> {
    let q = &terms.quote;
    println!("price    {} credit = birth fee {} + membership {} + spendable {}",
        field(q,"totalCredit")?,field(q,"birthFee")?,field(q,"membershipCredit")?,field(q,"spendableRemainder")?);
    println!("membership {} week(s); starter {} credit (requested {})",
        field(q,"grantedWeeks")?,field(q,"spendableRemainder")?,field(q,"requestedStarterCredit")?);
    println!("quote    tariff {} at height {}; this quote does not reserve the price",
        field(q,"tariffVersion")?,field(q,"height")?);
    Ok(())
}

// ---------------------------------------------------------------- printing

fn percent_encode(text: &str) -> String {
    text.bytes()
        .map(|b| match b {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'.' | b'_' | b'~' => (b as char).to_string(),
            _ => format!("%{b:02X}"),
        })
        .collect()
}

fn print_payment(terms: &Terms, atomic: u128, memo: &str, what: &str) {
    let address = bs58::encode(terms.address).into_string();
    let mint = bs58::encode(terms.mint).into_string();
    let program = bs58::encode(terms.token_program).into_string();
    let amount = terms.display(atomic);
    println!("{what}");
    println!("address  {address}");
    println!("mint     {mint}  (token program {program})");
    println!("amount   {amount} DREGG  ({atomic} atomic units)");
    println!("memo     {memo}");
    println!("memo-bytes {}", memo.len());
    println!(
        "solana-pay solana:{address}?amount={amount}&spl-token={mint}&memo={}",
        percent_encode(memo)
    );
    println!(
        "spl-token spl-token transfer --program-id {program} {mint} {amount} {address} --with-memo \"{memo}\""
    );
    println!(
        "note     send from a wallet you control, never an exchange: exchanges drop memos, and the \
         a transfer without one can fail enrollment. Some wallets also drop the memo from a Solana Pay \
         link; check the memo is in the transaction before you sign, or use the spl-token line."
    );
    println!(
        "note     your wallet, your ssh key and your Mini key are linked publicly and permanently \
         on Solana."
    );
}

// ---------------------------------------------------------------- the three modes

pub(crate) fn run_ssh_keygen(arguments: &[&OsStr]) -> Result<()> {
    let output = Command::new("ssh-keygen")
        .args(arguments)
        .stdin(std::process::Stdio::inherit())
        .output()
        .map_err(|e| format!("cannot run ssh-keygen: {e}"))?;
    if !output.status.success() {
        return Err(format!(
            "ssh-keygen failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(())
}

#[derive(Clone)]
struct Common {
    host: PathBuf,
    config: PathBuf,
    view: Option<PathBuf>,
    quote: Option<PathBuf>,
    bootstrap_url: Option<String>,
    weeks: String,
    starter: Option<String>,
    directory: PathBuf,
}

fn scratch(directory: &Path) -> Result<PathBuf> {
    let scratch = directory.join(format!("read-{}", workspace::random_nonce()?));
    workspace::make_private_dir(&scratch)?;
    Ok(scratch)
}

// Cold entry has only three fixed HTTP routes. Reuse the watcher transport's
// TLS, deadline, output bound and private spool; no redirect/proxy/curlrc ambient policy.
fn validate_bootstrap_url(url: &str) -> Result<()> {
    minidregg_pay_watcher::transport::validate_endpoint(url)?;
    if !url.ends_with("/mini/v1") || url.contains('?') || url.contains('#') {
        return Err("bootstrap URL must end in /mini/v1 with no query or fragment".into());
    }
    Ok(())
}
fn bootstrap_request(common: &Common, base: &str, route: &str, body: Option<&Value>) -> Result<Value> {
    validate_bootstrap_url(base)?;
    let spool = scratch(&common.directory)?;
    let result = (|| {
        let transport = minidregg_pay_watcher::CurlTransport::new("cold-entry",format!("{base}{route}"),&spool)?
            .with_bounds(std::time::Duration::from_secs(5),256*1024);
        let bytes = body.map(serde_json::to_vec).transpose().map_err(|e|e.to_string())?;
        let response = transport.request(if body.is_some() {"POST"} else {"GET"},bytes.as_deref())
            .map_err(|e|format!("bootstrap request failed: {e}"))?;
        serde_json::from_slice(&response).map_err(|e|format!("invalid bootstrap JSON: {e}"))
    })();
    let _ = fs::remove_dir(&spool);
    result
}
fn bootstrap_metadata(common: &Common, base: &str, login: Option<&str>) -> Result<Value> {
    let metadata = bootstrap_request(common,base,"/metadata",None)?;
    let config = workspace::bounded_json(&common.config)?;
    if field(&metadata,"type")? != "minidregg-enrollment-bootstrap-v1"
        || field(&metadata,"hostSha256")? != host_image_sha256(&common.host)?
        || natural(&metadata,"domain")? != natural(&config,"domain")?
        || login.is_some_and(|login| metadata.get("sshLogin").and_then(Value::as_str) != Some(login))
        || !metadata.get("memoVersions").and_then(Value::as_array)
            .is_some_and(|versions| versions.iter().any(|v| v.as_str()==Some("enrol:v1")))
    { return Err("bootstrap metadata differs from pinned deployment, Host, login, or memo version".into()); }
    transport::remote_address(field(&metadata,"sshLogin")?)?;
    Ok(metadata)
}
fn retained_bootstrap<'a>(common: &'a Common, record: &'a Value) -> Result<Option<&'a str>> {
    let retained = record.get("bootstrapUrl").and_then(Value::as_str);
    if let (Some(selected),Some(retained)) = (common.bootstrap_url.as_deref(),retained) {
        if selected != retained { return Err("bootstrap URL differs from retained join".into()); }
    }
    Ok(common.bootstrap_url.as_deref().or(retained))
}

/// Check a memo against the Host's own codec: accepted, the same four fields, 400 bytes.
fn host_reads_back(common: &Common, memo: &Memo, text: &str, scratch: &Path) -> Result<()> {
    if text.len() != MEMO_LENGTH {
        return Err(format!("the memo is {} bytes, not {MEMO_LENGTH}", text.len()));
    }
    let bin = scratch.join("memo.bin");
    create_private(&bin, text.as_bytes())?;
    let parsed_path = scratch.join("memo.json");
    let output = Command::new(&common.host).arg(&common.config)
        .args([OsStr::new("inspect"),OsStr::new("pay-enrol-memo"),bin.as_os_str(),parsed_path.as_os_str()])
        .output().map_err(|e|format!("cannot run pinned local memo codec: {e}"))?;
    if !output.status.success() { return Err(format!("local memo codec failed: {}",String::from_utf8_lossy(&output.stderr))); }
    let parsed = workspace::bounded_json(&parsed_path)?;
    let same = parsed.get("accepted").and_then(Value::as_bool) == Some(true)
        && field(&parsed, "miniKey")? == hex(&memo.mini_key)
        && field(&parsed, "sshBlob")? == hex(&ssh_blob(&memo.ssh_key))
        && field(&parsed, "miniSig")? == hex(&memo.mini_sig)
        && field(&parsed, "sshSig")? == hex(&memo.ssh_sig);
    if !same {
        return Err(format!(
            "the Host's memo codec does not read back this memo: {parsed}"
        ));
    }
    Ok(())
}

fn solana(common: &Common, pin: &Pin, key: Option<PathBuf>, ssh_key: Option<PathBuf>, name: &str) -> Result<()> {
    let directory = &common.directory;
    if directory.exists() {
        return Err(format!(
            "refusing to reuse {}: one join directory per enrollment (`--renew` reads it)",
            directory.display()
        ));
    }
    workspace::make_private_dir(directory)?;
    let scratch = scratch(directory)?;

    // The Mini key: made here (32 raw seed bytes, 0600, as `mini keygen` makes every key) or
    // the friend's own. It never leaves this machine.
    let key = match key {
        Some(key) => absolute(&key)?,
        None => {
            let secret = directory.join("mini.key");
            keygen(&secret, &directory.join("mini.pub"), None, NextKey::Without, false)?;
            secret
        }
    };
    let signing = read_secret(&key)?;
    let mini_key = signing.verifying_key().to_bytes();
    let terms = quoted_terms(common, pin, &mini_key, "enrol")?;

    // The ssh key: the friend's (a plain ssh-ed25519; FIDO refused) or a fresh one here.
    let ssh_private = match ssh_key {
        Some(path) => absolute(&path)?,
        None => {
            let ssh_dir = directory.join("ssh");
            workspace::make_private_dir(&ssh_dir)?;
            let private = ssh_dir.join("id_ed25519");
            let comment = format!("mini-join-{name}");
            run_ssh_keygen(&[
                OsStr::new("-q"),
                OsStr::new("-t"),
                OsStr::new("ed25519"),
                OsStr::new("-N"),
                OsStr::new(""),
                OsStr::new("-C"),
                OsStr::new(&comment),
                OsStr::new("-f"),
                private.as_os_str(),
            ])?;
            private
        }
    };
    let ssh_public_path = if ssh_private.extension() == Some(OsStr::new("pub")) {
        ssh_private.clone()
    } else {
        PathBuf::from(format!("{}.pub", ssh_private.display()))
    };
    let ssh_line = fs::read_to_string(&ssh_public_path)
        .map_err(|e| format!("cannot read {}: {e}", ssh_public_path.display()))?;
    let ssh_key = ssh_public_key(&ssh_line)?;

    let message = scratch.join("sshsig-message.bin");
    create_private(&message, &sshsig_message(&terms.mint, &terms.address, &mini_key))?;
    run_ssh_keygen(&[
        OsStr::new("-Y"),
        OsStr::new("sign"),
        OsStr::new("-n"),
        OsStr::new(SSHSIG_NAMESPACE),
        OsStr::new("-f"),
        ssh_private.as_os_str(),
        message.as_os_str(),
    ])?;
    let armoured = fs::read_to_string(scratch.join("sshsig-message.bin.sig"))
        .map_err(|e| format!("ssh-keygen wrote no signature: {e}"))?;
    let ssh_sig = sshsig_raw_signature(&armoured, &ssh_blob(&ssh_key))?;
    let mini_sig = signing
        .sign(&possession_frame(&terms.mint, &terms.address, &ssh_key))
        .to_bytes();
    let memo = Memo { mini_key, ssh_key, mini_sig, ssh_sig };

    // Both possessions verify here before anything is printed: a broken memo would cost the
    // friend a payment that lands in the journal.
    VerifyingKey::from_bytes(&ssh_key)
        .and_then(|ssh| {
            ssh.verify(
                &sshsig_signed_data(&sshsig_message(&terms.mint, &terms.address, &mini_key)),
                &Signature::from_bytes(&ssh_sig),
            )
        })
        .map_err(|_| "sshSigInvalid: the ssh signature does not verify over the enrollment statement")?;
    signing
        .verifying_key()
        .verify(
            &possession_frame(&terms.mint, &terms.address, &ssh_key),
            &Signature::from_bytes(&mini_sig),
        )
        .map_err(|_| "miniSigInvalid: the Mini signature does not verify")?;
    let text = encode_memo(&memo);
    host_reads_back(common, &memo, &text, &scratch)?;

    let atomic = natural(&terms.quote,"atomicAmount")?;
    let record = json!({"type":"minidregg-join-solana-v1","name":name,
        "miniKey":hex(&mini_key),"miniKeyFile":utf8_path(&key)?,
        "sshKey":hex(&ssh_key),"sshKeyFile":utf8_path(&ssh_private)?,
        "memo":text,"enrolAddress":hex(&terms.address),"mint":hex(&terms.mint),
        "tokenProgram":hex(&terms.token_program),"login":pin.login,
        "birthFee":terms.quote["birthFee"],
        "weekCredit":terms.quote["weekCredit"],"priceCredit":terms.quote["totalCredit"],
        "quote":terms.quote,"bootstrapUrl":common.bootstrap_url,"bootstrapMetadata":terms.bootstrap_metadata,
        "amountAtomic":atomic.to_string()});
    let mut bytes = serde_json::to_vec_pretty(&record).map_err(|e| e.to_string())?;
    bytes.push(b'\n');
    create_private(&directory.join("join.json"), &bytes)?;
    println!("mini-key {}  (kept at {}; it never leaves this machine)", hex(&mini_key), key.display());
    println!("ssh-key  {}  ({})", ssh_line.trim(), ssh_public_path.display());
    print_quote(&terms)?;
    print_payment(&terms, atomic, &text, "pay this to enrol yourself:");
    println!("then     mini join --wait --dir {} (with this box's --host/--config/--socket)", directory.display());
    Ok(())
}

fn retained(directory: &Path) -> Result<Value> {
    let record = workspace::bounded_json(&directory.join("join.json"))?;
    if record.get("type").and_then(Value::as_str) != Some("minidregg-join-solana-v1") {
        return Err(format!("{} holds no `join --solana` record", directory.display()));
    }
    Ok(record)
}

fn renew(common: &Common, pin: &Pin) -> Result<()> {
    let record = retained(&common.directory)?;
    let mut selected = common.clone();
    let retained_origin = retained_bootstrap(common,&record)?.map(str::to_owned);
    if selected.quote.is_none() { selected.bootstrap_url = retained_origin; }
    let common = &selected;
    let scratch = scratch(&common.directory)?;
    let terms = quoted_terms(common, pin, &fixed(field(&record,"miniKey")?,"miniKey")?, "renew")?;
    // The memo binds the mint and the address; renewing under other ones would be journaled.
    if field(&record, "enrolAddress")? != hex(&terms.address) || field(&record, "mint")? != hex(&terms.mint) {
        return Err("the box's enrollment address or mint changed since this memo was signed; run `join --solana` again".into());
    }
    let text = field(&record, "memo")?.to_owned();
    let memo = Memo {
        mini_key: fixed(field(&record, "miniKey")?, "miniKey")?,
        ssh_key: fixed(field(&record, "sshKey")?, "sshKey")?,
        mini_sig: fixed(&text[9 + 64 + 1 + 68 + 1..9 + 64 + 1 + 68 + 1 + 128], "miniSig")?,
        ssh_sig: fixed(&text[MEMO_LENGTH - 128..], "sshSig")?,
    };
    if encode_memo(&memo) != text {
        return Err("the retained memo is not canonical".into());
    }
    host_reads_back(common, &memo, &text, &scratch)?;
    workspace::private_file(&scratch.join("renewal-quote.json"),
        &serde_json::to_vec_pretty(&json!({"type":"minidregg-renewal-payment-v1",
            "miniKey":record["miniKey"],"memo":text,"quote":terms.quote,
            "bootstrapUrl":common.bootstrap_url,"bootstrapMetadata":terms.bootstrap_metadata}))
            .map_err(|e|e.to_string())?)?;
    print_quote(&terms)?;
    print_payment(
        &terms,
        natural(&terms.quote,"atomicAmount")?,
        &text,
        "pay this to renew (the same memo; the box decides renewal, and every whole node week \
         you pay extends your lease from its end, never shortening it):",
    );
    Ok(())
}

// Local construction only: enrollment is established by the exact key in the
// live view. Imported references remain hints; every read/write is checked by Host.
fn admitted_workspace(common: &Common, record: &Value, entry: &Value, ids: &Value,
                      published_context: Option<&Path>) -> Result<PathBuf> {
    let _lock = transport::service_lock(&common.directory.join("workspace-setup.lock"))?;
    let mini_key = field(record, "miniKey")?;
    let key_path = PathBuf::from(field(record, "miniKeyFile")?);
    let current_key = record.get("authorizingKey").and_then(Value::as_str).unwrap_or(mini_key);
    if hex(&read_secret(&key_path)?.verifying_key().to_bytes()) != current_key
        || field(ids, "miniKey")? != mini_key || field(entry, "miniKey")? != mini_key
        || field(entry, "subject")? != field(ids, "subject")?
        || field(entry, "sshBlob")? != hex(&ssh_blob(&fixed(field(record, "sshKey")?, "sshKey")?))
    {
        return Err("enrollment view, derived identities, and retained join keys disagree".into());
    }
    let config_bytes = fs::read(&common.config).map_err(|e| e.to_string())?;
    let config: Value = serde_json::from_slice(&config_bytes).map_err(|e| e.to_string())?;
    let factory = config.get("factoryId").and_then(|v| v.as_str().map(str::to_owned)
        .or_else(|| v.as_u64().map(|n| n.to_string()))).ok_or("config lacks factoryId")?;
    let context = published_context.map(|path| -> Result<Value> {
        let mut value = workspace::bounded_json(path)?;
        if field(&value, "type")? != "minidregg-participant-birth-context-v1"
            || !value["genesis"].is_object() || !value["template"].is_object()
            || field(&value["genesis"], "factoryId")? != factory
        { return Err("published birth context differs from the deployment factory".into()); }
        // Retain the exact deployment genesis/template, replacing all sponsor
        // funding/authority with only this member's actual enrollment grants.
        value["feePayer"] = ids["account"].clone();
        value["sourceCapabilities"] = json!([field(ids, "ownerCapability")?]);
        value["funding"] = json!([]);
        value["grants"] = json!([
            {"kind":"object","target":factory,"capability":field(ids,"observeCapability")?},
            {"kind":"account","target":field(ids,"account")?,"capability":field(ids,"ownerCapability")?}]);
        Ok(value)
    }).transpose()?;
    if SOCKET.get().is_none() && retained_bootstrap(common,record)?.is_some() {
        SOCKET.set(transport::remote_address(field(record,"login")?)?).map_err(|_|"cannot pin member remote")?;
    }
    if SOCKET.get().is_some_and(|socket| transport::is_remote(socket)) {
        pin_ssh_identity(Path::new(field(record,"sshKeyFile")?))?;
    }
    let socket = SOCKET.get().map(|socket| transport::pinned_address(socket)).transpose()?;
    let mut setup = json!({"type":"minidregg-paid-workspace-setup-v1", "miniKey":mini_key,
        "subject":field(ids,"subject")?, "account":field(ids,"account")?,
        "ownerCapability":field(ids,"ownerCapability")?, "controlCapability":field(ids,"controlCapability")?,
        "observeCapability":field(ids,"observeCapability")?, "factory":factory,
        "config":absolute(&common.config)?, "configSha256":format!("{:x}", Sha256::digest(&config_bytes)),
        "host":absolute(&common.host)?, "hostSha256":host_image_sha256(&common.host)?,
        "key":absolute(&key_path)?, "socket":socket, "sshIdentity":ssh_identity(), "birthContext":context});
    if ssh_identity().is_none() { setup.as_object_mut().unwrap().remove("sshIdentity"); }
    let pin = common.directory.join("workspace-setup.json");
    let first_ref = json!({"name":"account","kind":"account","target":field(ids,"account")?,
        "observeCapability":field(ids,"ownerCapability")?});
    // Existing legacy setups remain explicitly legacy. Every new setup pins
    // the shared fresh-onboarding contract before workspace publication.
    let fresh = !pin.exists() || workspace::bounded_json(&pin)?.get("freshContinuity").is_some();
    if fresh { setup["freshContinuity"] = first_ref.clone(); }
    if record.get("type").and_then(Value::as_str)==Some("minidregg-join-solana-v2") {
        setup["authorizingKey"] = json!(current_key);
        setup["authorityEpoch"] = record["authorityEpoch"].clone();
        setup["nextPublicFile"] = record["nextPublicFile"].clone();
        if !fresh { return Err("v2 paid entry requires retained fresh continuity setup".into()); }
    }
    if !pin.exists() && common.directory.join("workspace").exists() {
        return Err("workspace already exists without a retained paid setup; refusing to adopt it".into());
    }
    if record.get("type").and_then(Value::as_str)==Some("minidregg-join-solana-v2") {
        crate::paid_onboarding::reconcile(&common.directory,record,&setup,&first_ref,|staged| {
            paid_workspace_init(common,staged,&key_path,field(ids,"subject")?,
                &common.directory.join("namespace"),
                record.get("nextPublicFile").and_then(Value::as_str).map(Path::new),Some(&first_ref))
        })?;
    }
    if pin.exists() {
        if workspace::bounded_json(&pin)? != setup {
            return Err("paid workspace setup differs from retained deployment, identity, or birth context".into());
        }
    } else {
        workspace::replace_private_file(&pin, &serde_json::to_vec_pretty(&setup).map_err(|e|e.to_string())?)?;
    }
    let root = common.directory.join("workspace");
    let namespace = common.directory.join("namespace");
    let home = common.directory.join("home");
    if home.exists() { workspace::private_dir(&home)?; }
    else { workspace::make_private_dir(&home)?; }
    if namespace.exists() { workspace::private_dir(&namespace)?; }
    else { workspace::make_private_dir(&namespace)?; }
    // Publish a complete base workspace atomically. A crash before the rename
    // leaves only an unreferenced local staging directory, never a half-workspace.
    if !root.exists() {
        let staged = common.directory.join(format!("workspace-build-{}", workspace::random_nonce()?));
        paid_workspace_init(common, &staged, &key_path, field(ids,"subject")?, &namespace,
            record.get("nextPublicFile").and_then(Value::as_str).map(Path::new),
            if fresh {Some(&first_ref)} else {None})?;
        fs::rename(&staged, &root).map_err(|e| e.to_string())?;
        fs::File::open(&common.directory).and_then(|f| f.sync_all()).map_err(|e| e.to_string())?;
    }
    let workspace_pin = workspace::load(&root)?;
    if let Some(identity) = setup.get("sshIdentity") {
        if workspace_pin.get("sshIdentity") != Some(identity) { return Err("paid workspace SSH identity differs from retained setup".into()); }
    }
    for (field_name, expected) in [("subject", setup["subject"].clone()), ("key", setup["key"].clone()),
        ("config", setup["config"].clone()), ("host", setup["host"].clone()), ("socket", setup["socket"].clone())] {
        if workspace_pin.get(field_name) != Some(&expected) {
            return Err(format!("existing paid workspace {field_name} differs from retained setup"));
        }
    }
    if let Some(value) = &context {
        let context_path = root.join("birth-context.json");
        if context_path.exists() {
            if workspace::bounded_json(&context_path)? != *value {
                return Err("retained member birth context differs".into());
            }
        } else {
            workspace::private_file(&context_path, &serde_json::to_vec_pretty(value).map_err(|e|e.to_string())?)?;
        }
        let context_path_json = json!(context_path);
        if workspace_pin.get("birthContext") != Some(&context_path_json) {
            if !workspace_pin["birthContext"].is_null() {
                return Err("existing workspace names another birth context".into());
            }
            let mut complete = workspace_pin.clone();
            complete["birthContext"] = context_path_json;
            let staged = root.join("paid-workspace-complete.json");
            if staged.exists() {
                if workspace::bounded_json(&staged)? != complete {
                    return Err("staged workspace context attachment differs".into());
                }
            } else {
                workspace::private_file(&staged, &serde_json::to_vec_pretty(&complete).map_err(|e|e.to_string())?)?;
            }
            fs::rename(&staged, root.join("workspace.json")).map_err(|e|e.to_string())?;
            fs::File::open(&root).and_then(|f| f.sync_all()).map_err(|e|e.to_string())?;
        }
    }
    for (name, kind, target, observe, control) in [
        ("account", "account", field(ids,"account")?, field(ids,"ownerCapability")?, Some(field(ids,"controlCapability")?)),
        ("factory", "object", factory.as_str(), field(ids,"observeCapability")?, None)] {
        let reference_path = root.join("refs").join(format!("{name}.json"));
        if reference_path.exists() {
            let reference = workspace::reference(&root, name)?;
            if field(&reference,"kind")? != kind || field(&reference,"target")? != target
                || field(&reference,"observeCapability")? != observe
                || field(&reference,"operationCapability")? != observe
                || reference.get("controlCapability").and_then(Value::as_str) != control
            { return Err(format!("existing paid workspace {name} reference differs")); }
        } else {
            workspace::import(&root, workspace::ImportInput {name,kind,target,observe,
                operation:Some(observe),control,provenance:None,room:None})?;
        }
    }
    if fresh {
        let receipt=workspace::complete_fresh_onboarding(&root)?;
        println!("continuity {}",receipt);
    }
    Ok(root)
}

// Use the shared source-backed onboarding contract before publication and
// completion. Legacy retained setups are not silently upgraded.
fn paid_workspace_init(common:&Common,root:&Path,key:&Path,subject:&str,namespace:&Path,
                       next:Option<&Path>,first_ref:Option<&Value>)->Result<()> {
    let identity=workspace::InitIdentity {key:Some(key),subject:Some(subject),enrollment:None,
        next_public:next,without_prerotation:next.is_none()};
    match first_ref {
        Some(reference)=>workspace::init_fresh(root,Some(&common.host),&common.config,identity,
            None,Some(namespace),reference,Some(&common.host)),
        None=>workspace::init(root,Some(&common.host),&common.config,identity,None,Some(namespace)),
    }
}

pub(crate) fn admitted_workspace_v2(host:&Path,config:&Path,directory:&Path,bootstrap_url:Option<&str>,
    record:&Value,entry:&Value,ids:&Value,birth_context:Option<&Path>)->Result<PathBuf> {
    if field(record,"type")? != "minidregg-join-solana-v2" { return Err("v2 join record expected".into()); }
    if field(entry,"account")? != field(ids,"account")? {return Err("paid status account differs from source identity derivation".into());}
    let mut projected=entry.clone();
    projected["miniKey"]=record["miniKey"].clone();
    let common=Common {host:host.to_owned(),config:config.to_owned(),directory:directory.to_owned(),
        view:None,quote:None,bootstrap_url:bootstrap_url.map(str::to_owned),weeks:"1".into(),starter:None};
    admitted_workspace(&common,record,&projected,ids,birth_context)
}

// Enrollment identity persists after membership expires. Only a live lease
// means the SSH Mini transport can be used to finish a fresh workspace.
fn inactive_membership(entry: &Value, hour: Option<u64>) -> Result<Option<String>> {
    let hour = hour.ok_or("enrollment view lacks an authenticated clock hour")?;
    let lease = entry.get("lease").filter(|v| !v.is_null());
    let Some(lease) = lease else {
        return Ok(Some("enrolled identity has no membership lease; renew with `mini join --renew`".into()));
    };
    let expires = lease.get("expiresAt").and_then(Value::as_u64)
        .ok_or("enrollment lease lacks an exact expiry hour")?;
    Ok((hour >= expires).then(|| format!(
        "membership expired at box hour {expires} (current hour {hour}); renew with `mini join --renew`")))
}

fn wait(common: &Common, signature: Option<String>, timeout: u64, interval: u64, birth_context: Option<&Path>) -> Result<()> {
    let record = retained(&common.directory)?;
    let key = field(&record, "miniKey")?.to_owned();
    let bootstrap = retained_bootstrap(common,&record)?;
    if let Some(base) = bootstrap { bootstrap_metadata(common,base,Some(field(&record,"login")?))?; }
    let socket = SOCKET.get().cloned();
    if bootstrap.is_none() && socket.is_none() { return Err("join --wait needs --socket/--remote or retained --bootstrap-url".into()); }
    let signature = signature
        .map(|text| {
            bs58::decode(&text)
                .into_vec()
                .ok()
                .filter(|bytes| bytes.len() == 64)
                .map(|bytes| hex(&bytes))
                .ok_or("--signature must be a base58 Solana transaction signature")
        })
        .transpose()?;
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(timeout);
    loop {
        let scratch = scratch(&common.directory)?;
        let view = if let Some(base) = bootstrap {
            let mut route = format!("/enrollment/{key}");
            if let Some(signature) = &signature { route.push_str(&format!("?signature={signature}")); }
            let status = bootstrap_request(common,base,&route,None)?;
            if field(&status,"type")? != "minidregg-enrollment-status-v1" || field(&status,"miniKey")? != key {
                return Err("bootstrap status differs from exact enrollment key".into());
            }
            json!({"clock":status["clock"],
                "entries":status.get("entry").filter(|v|!v.is_null()).cloned().into_iter().collect::<Vec<_>>(),
                "journal":status.get("paymentDecision").filter(|v|!v.is_null()).cloned().into_iter().collect::<Vec<_>>()})
        } else {
            let frame = session_invoke(&common.host, socket.as_ref().unwrap(), &common.config, ENROLMENT_VIEW_OP, &[])?;
            let bin = scratch.join("enrolment-view.bin");
            create_private(&bin, frame_body(&frame, ENROLMENT_VIEW_OP)?)?;
            inspect(&common.host, &common.config, "pay-enrolment-view", &bin, &scratch.join("enrolment-view.json"))?
        };
        let hour = view
            .get("clock")
            .and_then(|clock| clock.get("hour"))
            .and_then(Value::as_u64);
        let entry = view
            .get("entries")
            .and_then(Value::as_array)
            .and_then(|entries| {
                entries
                    .iter()
                    .find(|entry| entry.get("miniKey").and_then(Value::as_str) == Some(key.as_str()))
            });
        let inactive = entry.map(|entry| inactive_membership(entry, hour)).transpose()?.flatten();
        if let Some(entry) = entry.filter(|_| inactive.is_none()) {
            let expires = entry
                .get("lease")
                .and_then(|lease| lease.get("expiresAt"))
                .and_then(Value::as_u64);
            let ids_path = scratch.join("ids.json");
            let output = Command::new(&common.host)
                .arg(&common.config)
                .arg("pay-enrol-ids")
                .arg(&key)
                .arg(&ids_path)
                .output()
                .map_err(|e| format!("cannot run the Host: {e}"))?;
            if !output.status.success() {
                return Err(format!(
                    "pay-enrol-ids failed: {}",
                    String::from_utf8_lossy(&output.stderr).trim()
                ));
            }
            let ids = workspace::bounded_json(&ids_path)?;
            let workspace = admitted_workspace(common, &record, entry, &ids, birth_context)?;
            println!("enrolled subject {}", field(entry, "subject")?);
            println!("workspace {}", workspace.display());
            println!("enter    mini shell --workspace {} --home {}", workspace.display(), common.directory.join("home").display());
            println!(
                "account  {}  (owner capability {}, control {}, factory observation {})",
                field(&ids, "account")?,
                field(&ids, "ownerCapability")?,
                field(&ids, "controlCapability")?,
                field(&ids, "observeCapability")?
            );
            match (expires, hour) {
                (Some(expires), Some(hour)) => println!(
                    "lease    until box hour {expires} ({} hours from now, box hour {hour})",
                    expires.saturating_sub(hour)
                ),
                _ => println!("lease    none (renew with `mini join --renew`)"),
            }
            if let Some(index) = entry.get("index").and_then(Value::as_u64) {
                println!("deposit  your own book index {index} (`mini pay address`)");
            }
            println!(
                "ssh      ssh -i {} {}   (a proxy key: the box adds it within 60 s; it carries \
                 Mini frames to the socket, no shell)",
                field(&record, "sshKeyFile")?,
                field(&record, "login")?
            );
            return Ok(());
        }
        if let Some(signature) = &signature {
            if let Some(row) = view.get("journal").and_then(Value::as_array).and_then(|rows| {
                rows.iter()
                    .find(|row| row.get("signature").and_then(Value::as_str) == Some(signature.as_str()))
            }) {
                set_exit(3);
                return Err(format!(
                    "the box journaled this payment, not an enrollment: {} (amount {}); ask the \
                     operator to comp it",
                    row.get("reason").and_then(Value::as_str).unwrap_or("?"),
                    row.get("amount").map(Value::to_string).unwrap_or_default()
                ));
            }
        }
        let _ = fs::remove_dir_all(&scratch);
        if std::time::Instant::now() >= deadline {
            set_exit(4);
            return Err(inactive.unwrap_or_else(|| format!(
                "not enrolled yet (Mini key {key} is not in the enrollment view); run --wait again after the next finalized-payment observation"
            )));
        }
        std::thread::sleep(std::time::Duration::from_secs(interval));
    }
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let mode = args
        .required("mode")?
        .into_string()
        .map_err(|_| "join mode must be UTF-8")?;
    let common = Common {
        host: path(args.required("host")?),
        config: path(args.required("config")?),
        view: args.optional("view").map(path),
        quote: args.optional("quote").map(path),
        bootstrap_url: args.optional("bootstrap-url").map(|v|v.into_string().map_err(|_|"bootstrap URL must be UTF-8")).transpose()?,
        weeks: args.optional("weeks").map(|v| v.into_string().map_err(|_| "weeks must be UTF-8")).transpose()?.unwrap_or_else(|| "1".into()),
        starter: args.optional("starter-credit").map(|v| v.into_string().map_err(|_| "starter-credit must be UTF-8")).transpose()?,
        directory: absolute(&path(args.required("dir")?))?,
    };
    if let Some(url) = &common.bootstrap_url { validate_bootstrap_url(url)?; }
    if common.bootstrap_url.is_some() && common.quote.is_some() { return Err("choose --bootstrap-url or --quote".into()); }
    if common.view.is_some() { return Err("paid join now uses a source-owned per-key --quote or --bootstrap-url; --view cannot quote receiver fees".into()); }
    workspace::decimal(&common.weeks, "weeks")?;
    if let Some(starter) = &common.starter { workspace::decimal(starter,"starter-credit")?; }
    let text = |value: OsString, name: &str| {
        value
            .into_string()
            .map_err(|_| format!("--{name} must be UTF-8"))
    };
    match mode.as_str() {
        "solana" => {
            let pin = load_pin(&path(args.required("enrol")?))?;
            let key = args.optional("key").map(path);
            let ssh_key = args.optional("ssh-key").map(path);
            let name = args
                .optional("name")
                .map(|value| text(value, "name"))
                .transpose()?
                .unwrap_or_else(|| "friend".into());
            if name.is_empty() || !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_') {
                return Err("--name is letters, digits, - and _".into());
            }
            args.finish()?;
            solana(&common, &pin, key, ssh_key, &name)
        }
        "renew" => {
            let pin = load_pin(&path(args.required("enrol")?))?;
            args.finish()?;
            renew(&common, &pin)
        }
        "wait" => {
            let birth_context = args.optional("birth-context").map(path);
            let signature = args.optional("signature").map(|v| text(v, "signature")).transpose()?;
            let seconds = |value: Option<OsString>, name: &str, default: u64| -> Result<u64> {
                value
                    .map(|v| text(v, name)?.parse::<u64>().map_err(|_| format!("--{name} must be seconds")))
                    .transpose()
                    .map(|v| v.unwrap_or(default))
            };
            let timeout = seconds(args.optional("timeout"), "timeout", 600)?;
            let interval = seconds(args.optional("interval"), "interval", 10)?.max(1);
            if common.view.is_some() {
                return Err("join --wait reads the live enrollment view; it takes no --view".into());
            }
            args.finish()?;
            wait(&common, signature, timeout, interval, birth_context.as_deref())
        }
        other => Err(format!("unknown join mode {other}: --solana | --wait | --renew")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enrollment_identity_is_not_ready_after_lease_expiry() {
        let entry = json!({"lease":{"expiresAt":100}});
        assert_eq!(inactive_membership(&entry, Some(99)).unwrap(), None);
        assert!(inactive_membership(&entry, Some(100)).unwrap().unwrap().contains("expired"));
        assert!(inactive_membership(&entry, Some(101)).unwrap().is_some());
        assert!(inactive_membership(&json!({"lease":null}), Some(99)).unwrap().unwrap().contains("no membership lease"));
        assert!(inactive_membership(&entry, None).is_err());
        assert!(inactive_membership(&json!({"lease":{}}), Some(99)).is_err());
    }

    fn workspace_fixture() -> (Common, Value, Value, Value, PathBuf) {
        let root = std::env::temp_dir().join(format!("paid-join-workspace-{}", workspace::random_nonce().unwrap()));
        workspace::make_private_dir(&root).unwrap();
        let common = Common {host:root.join("Host"),config:root.join("config.json"),view:None,quote:None,bootstrap_url:None,weeks:"1".into(),starter:None,directory:root.clone()};
        workspace::private_file(&common.host, b"fixture host image").unwrap();
        workspace::private_file(&common.config, br#"{"factoryId":10,"domain":8501}"#).unwrap();
        let key_path = root.join("mini.key");
        workspace::private_file(&key_path, &[42u8;32]).unwrap();
        let public = hex(&SigningKey::from_bytes(&[42u8;32]).verifying_key().to_bytes());
        let ssh = [43u8;32];
        let record = json!({"miniKey":public,"miniKeyFile":key_path,"sshKey":hex(&ssh)});
        let entry = json!({"miniKey":public,"subject":"101","sshBlob":hex(&ssh_blob(&ssh))});
        let ids = json!({"miniKey":public,"subject":"101","account":"201",
            "ownerCapability":"301","controlCapability":"401","observeCapability":"501"});
        let context_path = root.join("published-context.json");
        let context = json!({"type":"minidregg-participant-birth-context-v1",
            "genesis":{"factoryId":"10","domain":"8501","untouchedOriginalSeedData":[1,2]},
            "template":{"issuer":"5","ownerBudget":"1000","lifetime":"100"},
            "feePayer":"999","sourceCapabilities":["998"],"funding":[{"sponsor":"999"}],"grants":[]});
        workspace::private_file(&context_path, &serde_json::to_vec(&context).unwrap()).unwrap();
        (common,record,entry,ids,context_path)
    }

    #[test]
    fn paid_workspace_retains_setup_but_refuses_unverified_baseline() {
        let (common,record,entry,ids,context_path)=workspace_fixture();
        // A text file pretending to be a Host cannot establish key custody or
        // authenticated continuity. The retained setup remains recoverable,
        // but no successful workspace is published from this unverified input.
        assert!(admitted_workspace(&common,&record,&entry,&ids,Some(&context_path)).is_err());
        assert!(!common.directory.join("workspace").exists());
        let setup=workspace::bounded_json(&common.directory.join("workspace-setup.json")).unwrap();
        assert_eq!(setup["freshContinuity"],json!({"name":"account","kind":"account",
            "target":"201","observeCapability":"301"}));
        assert_eq!(setup["birthContext"]["feePayer"],"201");
        assert_eq!(setup["birthContext"]["sourceCapabilities"],json!(["301"]));
        assert_eq!(setup["birthContext"]["funding"],json!([]));
        assert_eq!(setup["birthContext"]["genesis"]["untouchedOriginalSeedData"],json!([1,2]));
        let original=fs::read(common.directory.join("workspace-setup.json")).unwrap();
        assert!(admitted_workspace(&common,&record,&entry,&ids,Some(&context_path)).is_err());
        assert_eq!(fs::read(common.directory.join("workspace-setup.json")).unwrap(),original);
        let mut changed=entry.clone();changed["subject"]=json!("102");
        assert!(admitted_workspace(&common,&record,&changed,&ids,Some(&context_path)).unwrap_err().contains("disagree"));
        fs::write(&common.config,br#"{"factoryId":10,"domain":8502}"#).unwrap();
        assert!(admitted_workspace(&common,&record,&entry,&ids,Some(&context_path)).unwrap_err().contains("differs"));
        fs::remove_dir_all(common.directory).unwrap();
    }

    #[test]
    fn paid_workspace_refuses_wrong_keys_and_existing_unowned_workspace() {
        let (common,record,entry,ids,context_path) = workspace_fixture();
        let mut wrong = record.clone(); wrong["sshKey"] = json!(hex(&[44u8;32]));
        assert!(admitted_workspace(&common,&wrong,&entry,&ids,None).unwrap_err().contains("disagree"));
        assert!(!common.directory.join("workspace-setup.json").exists());
        workspace::make_private_dir(&common.directory.join("workspace")).unwrap();
        assert!(admitted_workspace(&common,&record,&entry,&ids,Some(&context_path)).unwrap_err().contains("refusing to adopt"));
        fs::remove_dir_all(common.directory).unwrap();
    }

    // Kernel/PayEnrolMemo.lean's fixture (`fixtureBytes`, `fixtureMemo`, `fixtureMint`,
    // `fixtureAddress`): a real ssh-keygen run (P3b-1) and the Mini key of seed [42; 32].
    const FIXTURE_MEMO: &str = "enrol:v1:197f6b23e16c8532c6abc838facd5ea789be0c76b2920334039bfa8b3d368d61:AAAAC3NzaC1lZDI1NTE5AAAAIG07ssw/nVQyEp4fbo6x0DefttH5CdsmuUI28/nc/UkK:1a89a4544250df3be16bd701357d114ccb00dabd79da77f35c8a394875cf78d8ef66b47d8a3cde4c21efd6c9aefd2fe7430adc047d67746498280c274adae202:e3024a122f7f20335c168b22d428617cbcfb4dc6d0b68f26dae8e2c2038641fd40d672e739b8a1d1a681f6d8488f46046985570f0ee30db01ae361309ff21f09";
    const MINT: &str = "8525966c00f39ff54ef5e537a4736af436494d1f1681c659bd98e37ac28beff1";
    const ADDRESS: &str = "16946aa663362d557dd21ee08e8da60c2ea8a73467713c7c5205991e36634af5";
    const SSH_LINE: &str = "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIG07ssw/nVQyEp4fbo6x0DefttH5CdsmuUI28/nc/UkK p3b1-vector";
    /// `native/credential-signature-verifier/tests/sshsig.rs` SSHSIG_ARMOURED_BODY.
    const SSHSIG_BODY: &str = "53534853494700000001000000330000000b7373682d65643235353139000000206d3bb2cc3f9d5432129e1f6e8eb1d0379fb6d1f909db26b94236f3f9dcfd490a0000000e64726567672d656e726f6c4076310000000000000006736861353132000000530000000b7373682d6564323535313900000040e3024a122f7f20335c168b22d428617cbcfb4dc6d0b68f26dae8e2c2038641fd40d672e739b8a1d1a681f6d8488f46046985570f0ee30db01ae361309ff21f09";

    fn armour(body: &[u8]) -> String {
        let text = b64_encode(body);
        let lines: Vec<&str> = text.as_bytes().chunks(70).map(|c| std::str::from_utf8(c).unwrap()).collect();
        format!("-----BEGIN SSH SIGNATURE-----\n{}\n-----END SSH SIGNATURE-----\n", lines.join("\n"))
    }

    #[test]
    fn the_rust_memo_is_byte_identical_to_the_lean_fixture() {
        let mint: [u8; 32] = fixed(MINT, "mint").unwrap();
        let address: [u8; 32] = fixed(ADDRESS, "address").unwrap();
        let signing = SigningKey::from_bytes(&[42u8; 32]);
        let ssh_key = ssh_public_key(SSH_LINE).unwrap();
        let body = decode_hex(SSHSIG_BODY).unwrap();
        let ssh_sig = sshsig_raw_signature(&armour(&body), &ssh_blob(&ssh_key)).unwrap();
        // Ed25519 is deterministic: the Rust possession signature equals PyNaCl's in the fixture.
        let mini_sig = signing.sign(&possession_frame(&mint, &address, &ssh_key)).to_bytes();
        let memo = Memo { mini_key: signing.verifying_key().to_bytes(), ssh_key, mini_sig, ssh_sig };
        let text = encode_memo(&memo);
        assert_eq!(text, FIXTURE_MEMO);
        assert_eq!(text.len(), MEMO_LENGTH);
        // And the ssh signature verifies over the kernel's reconstruction of the signed data.
        VerifyingKey::from_bytes(&ssh_key)
            .unwrap()
            .verify(
                &sshsig_signed_data(&sshsig_message(&mint, &address, &memo.mini_key)),
                &Signature::from_bytes(&ssh_sig),
            )
            .unwrap();
    }

    #[test]
    fn the_sshsig_armour_is_checked_field_by_field() {
        let ssh_key = ssh_public_key(SSH_LINE).unwrap();
        let body = decode_hex(SSHSIG_BODY).unwrap();
        // another signer
        assert!(sshsig_raw_signature(&armour(&body), &ssh_blob(&[9u8; 32])).is_err());
        // another namespace (same length)
        let other = hex(b"dregg-enrol@v1");
        let mutated = SSHSIG_BODY.replace(&other, &hex(b"dregg-enrol@v2"));
        assert!(sshsig_raw_signature(&armour(&decode_hex(&mutated).unwrap()), &ssh_blob(&ssh_key)).is_err());
        // trailing bytes
        let mut long = body.clone();
        long.push(0);
        assert!(sshsig_raw_signature(&armour(&long), &ssh_blob(&ssh_key)).is_err());
        assert!(sshsig_raw_signature("not armour", &ssh_blob(&ssh_key)).is_err());
    }

    #[test]
    fn fido_and_other_ssh_keys_are_refused_by_name() {
        let fido = ssh_public_key("sk-ssh-ed25519@openssh.com AAAAGnNrLXNzaC1lZDI1NTE5QG9wZW5zc2guY29t x").unwrap_err();
        assert!(fido.starts_with("fidoKeyRefused"), "{fido}");
        let rsa = ssh_public_key("ssh-rsa AAAAB3NzaC1yc2E x").unwrap_err();
        assert!(rsa.starts_with("notEd25519"), "{rsa}");
        assert!(ssh_public_key(SSH_LINE).is_ok());
    }

    #[test]
    fn base64_round_trips_and_amounts_render_exactly() {
        for length in 0..60usize {
            let bytes: Vec<u8> = (0..length as u8).map(|b| b.wrapping_mul(37)).collect();
            assert_eq!(b64_decode(&b64_encode(&bytes)).unwrap(), bytes);
        }
        let terms = Terms {
            address: [0; 32], mint: [0; 32], token_program: [0; 32], decimals: 6,
            quote:json!({}),bootstrap_metadata:None,
        };
        assert_eq!(terms.display(999_999_847), "999.999847");
        assert_eq!(terms.display(1_000_000), "1");
        assert_eq!(percent_encode("enrol:v1:a+b/c="), "enrol%3Av1%3Aa%2Bb%2Fc%3D");
    }
    #[test]
    fn source_quote_is_bound_to_key_duration_starter_and_published_recipient() {
        let root = std::env::temp_dir().join(format!("mini-quote-{}-{}",std::process::id(),workspace::random_nonce().unwrap()));
        workspace::make_private_dir(&root).unwrap();
        let config = root.join("config.json");
        workspace::private_file(&config,br#"{"domain":"7"}"#).unwrap();
        let pin = Pin {address:[2;32],login:"mini@example.test".into()};
        let quote = json!({"type":"minidregg-pay-enrollment-quote-v1","miniKey":hex(&[1;32]),
            "mode":"enrol","requestedWeeks":"1","grantedWeeks":"1","priceReserved":false,
            "domain":"7","enrolAddress":hex(&[2;32]),"mint":hex(&[3;32]),"tokenProgram":hex(&[4;32]),
            "decimals":"6","atomicAmount":"1007","totalCredit":"1007","birthFee":"7",
            "membershipCredit":"900","spendableRemainder":"100","requestedStarterCredit":"100",
            "minimumEntryCredit":"907","weekCredit":"900","roundingCredit":"0"});
        assert!(terms(quote.clone(),&config,&pin,&[1;32],"enrol","1",Some("100")).is_ok());
        for (field_name,value) in [("miniKey",json!(hex(&[9;32]))),("grantedWeeks",json!("2")),
            ("requestedStarterCredit",json!("0")),("enrolAddress",json!(hex(&[8;32]))),
            ("domain",json!("8")),("priceReserved",json!(true))] {
            let mut bad=quote.clone(); bad[field_name]=value;
            assert!(terms(bad,&config,&pin,&[1;32],"enrol","1",Some("100")).is_err(),"{field_name}");
        }
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn bootstrap_origin_cannot_change_during_wait_or_use_unprotected_remote_http() {
        assert!(validate_bootstrap_url("https://node.dregg.net/mini/v1").is_ok());
        assert!(validate_bootstrap_url("http://127.0.0.1:8787/mini/v1").is_ok());
        for bad in ["http://node.dregg.net/mini/v1","https://user@node.dregg.net/mini/v1",
            "https://node.dregg.net/mini/v1?route=x","https://node.dregg.net/mini/v1#fragment"] {
            assert!(validate_bootstrap_url(bad).is_err());
        }
        let common = Common {host:PathBuf::new(),config:PathBuf::new(),view:None,quote:None,
            bootstrap_url:Some("https://other.test/mini/v1".into()),weeks:"1".into(),starter:None,directory:PathBuf::new()};
        assert!(retained_bootstrap(&common,&json!({"bootstrapUrl":"https://node.dregg.net/mini/v1"})).is_err());
    }

}
