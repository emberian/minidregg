//! V2 paid entry: source quote/status, two local possessions, exact retained
//! payment material, and shared admitted-workspace setup. Never submits funds.
use crate::participant_enrollment::{reply, retain_exact};
use crate::pay_memo_v2::{self, Context, ExpectedPurchase, PurchaseMode, ValidatedQuote};
use crate::pay_status::{self, Freshness, LeaseState, Payment};
use crate::*;
use serde_json::{json, Value};
use sha2::Sha256;
use std::time::{Duration, Instant};

const STATUS_OP: u8 = 181;
const QUOTE_OP: u8 = 182;

fn field<'a>(value: &'a Value, name: &str) -> Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("missing string {name}"))
}
fn number(text: &str, name: &str) -> Result<u64> {
    let n = text
        .parse::<u64>()
        .map_err(|_| format!("{name} must be u64 decimal"))?;
    if n.to_string() != text {
        return Err(format!("{name} must be canonical decimal"));
    }
    Ok(n)
}
fn scalar(value: &Value, name: &str) -> Result<u64> {
    number(field(value, name)?, name)
}
fn fixed<const N: usize>(text: &str, name: &str) -> Result<[u8; N]> {
    decode_hex(text)?
        .try_into()
        .map_err(|_| format!("{name} must be {N} bytes"))
}
fn same(actual: bool, message: &str) -> Result<()> {
    if actual {
        Ok(())
    } else {
        Err(message.into())
    }
}
fn pin_nat(value: &Value, name: &str) -> Result<u64> {
    match &value[name] {
        Value::String(s) => number(s, name),
        Value::Number(n) => n.as_u64().ok_or_else(|| format!("invalid {name}")),
        _ => Err(format!("missing {name}")),
    }
}
fn strict(value: &Value, names: &[&str]) -> Result<()> {
    let obj = value.as_object().ok_or("object expected")?;
    same(
        obj.len() == names.len() && names.iter().all(|k| obj.contains_key(*k)),
        "unexpected or missing pin fields",
    )
}
#[derive(Clone)]
struct Pin {
    context: Context,
    decimals: u32,
    login: String,
    value: Value,
}
impl Pin {
    fn parse(value: Value) -> Result<Self> {
        strict(
            &value,
            &[
                "type",
                "enrolAddress",
                "mint",
                "tokenProgram",
                "decimals",
                "login",
            ],
        )?;
        same(
            field(&value, "type")? == "minidregg-enrol-pin-v2",
            "explicit minidregg-enrol-pin-v2 required",
        )?;
        let key = |name| -> Result<[u8; 32]> {
            let text = field(&value, name)?;
            let bytes = bs58::decode(text)
                .into_vec()
                .map_err(|_| format!("invalid base58 {name}"))?;
            let bytes: [u8; 32] = bytes
                .try_into()
                .map_err(|_| format!("{name} must be 32 bytes"))?;
            same(
                bytes != [0; 32] && bs58::encode(bytes).into_string() == text,
                "zero or noncanonical published asset/address",
            )?;
            Ok(bytes)
        };
        let context = Context {
            mint: key("mint")?,
            token_program: key("tokenProgram")?,
            recipient: key("enrolAddress")?,
        };
        let decimals =
            u32::try_from(pin_nat(&value, "decimals")?).map_err(|_| "decimals overflow")?;
        same(decimals <= 38, "decimals exceed exact display bound")?;
        let login = field(&value, "login")?.to_owned();
        transport::remote_address(&login)?;
        Ok(Self {
            context,
            decimals,
            login,
            value,
        })
    }
    fn load(path: &Path) -> Result<Self> {
        Self::parse(workspace::bounded_json(path)?)
    }
    fn display(&self, atomic: u64) -> String {
        let scale = 10u128.pow(self.decimals);
        let atomic = u128::from(atomic);
        let fraction = format!("{:0width$}", atomic % scale, width = self.decimals as usize);
        let fraction = fraction.trim_end_matches('0');
        if fraction.is_empty() {
            (atomic / scale).to_string()
        } else {
            format!("{}.{}", atomic / scale, fraction)
        }
    }
}
#[derive(Clone)]
struct Common {
    host: PathBuf,
    config: PathBuf,
    directory: PathBuf,
    bootstrap: Option<String>,
    weeks: u32,
    starter: Option<u64>,
    expiry: Option<u64>,
    epoch: Option<u64>,
    host_sha256: String,
    config_bytes: Vec<u8>,
}
fn config_sha256(common: &Common) -> String {
    format!("{:x}", Sha256::digest(&common.config_bytes))
}
fn pinned_config(common: &Common) -> Result<Value> {
    serde_json::from_slice(&common.config_bytes).map_err(|e| format!("pinned config JSON: {e}"))
}
fn config_nat(config: &Value, name: &str) -> Result<String> {
    let text = config[name]
        .as_str()
        .map(str::to_owned)
        .unwrap_or_else(|| config[name].to_string());
    same(
        !text.is_empty()
            && text.bytes().all(|b| b.is_ascii_digit())
            && (text == "0" || !text.starts_with('0')),
        "pinned config requires canonical natural domain/expectedSeed",
    )?;
    Ok(text)
}
fn check_pins(common: &Common) -> Result<()> {
    same(
        host_image_sha256(&common.host)? == common.host_sha256
            && fs::read(&common.config).map_err(|e| e.to_string())? == common.config_bytes,
        "Host or config bytes changed during paid preparation",
    )
}
fn preparation_pins(common: &Common, pin: &Pin) -> Result<Value> {
    let config = pinned_config(common)?;
    Ok(
        json!({"hostSha256":common.host_sha256,"configSha256":config_sha256(common),
        "domain":config_nat(&config,"domain")?,"expectedSeed":config_nat(&config,"expectedSeed")?,
        "bootstrapUrl":common.bootstrap,"enrolPin":pin.value}),
    )
}
fn scratch(common: &Common) -> Result<PathBuf> {
    let dir = common
        .directory
        .join(format!("v2-{}", workspace::random_nonce()?));
    workspace::make_private_dir(&dir)?;
    Ok(dir)
}
fn validate_url(url: &str) -> Result<()> {
    minidregg_pay_watcher::transport::validate_endpoint(url)?;
    same(
        url.ends_with("/mini/v2") && !url.contains('?') && !url.contains('#'),
        "bootstrap URL must end in /mini/v2 without query or fragment",
    )
}
fn request(common: &Common, operation: u8, body: &Value) -> Result<Value> {
    let bytes = serde_json::to_vec(body).map_err(|e| e.to_string())?;
    same(bytes.len() <= 4096, "source request exceeds 4096 bytes")?;
    let response = if let Some(base) = &common.bootstrap {
        validate_url(base)?;
        let route = match operation {
            STATUS_OP => "/status",
            QUOTE_OP => "/quote",
            _ => return Err("closed v2 read operation required".into()),
        };
        let spool = scratch(common)?;
        let result =
            minidregg_pay_watcher::CurlTransport::new("paid-v2", format!("{base}{route}"), &spool)?
                .with_bounds(Duration::from_secs(5), 8192)
                .request("POST", Some(&bytes))
                .map_err(|e| format!("paid bootstrap: {e}"));
        let _ = fs::remove_dir(&spool);
        result?
    } else {
        let socket = SOCKET
            .get()
            .ok_or("v2 paid entry needs --socket/--remote or --bootstrap-url")?;
        let frame = session_invoke(&common.host, socket, &common.config, operation, &bytes)?;
        reply(&frame, operation)?.to_vec()
    };
    same(response.len() <= 8192, "source JSON exceeds 8192 bytes")?;
    serde_json::from_slice(&response).map_err(|e| format!("source JSON: {e}"))
}
fn metadata(common: &Common, pin: &Pin) -> Result<Option<Value>> {
    let Some(base) = &common.bootstrap else {
        return Ok(None);
    };
    validate_url(base)?;
    let spool = scratch(common)?;
    let result = minidregg_pay_watcher::CurlTransport::new(
        "paid-v2-metadata",
        format!("{base}/metadata"),
        &spool,
    )?
    .with_bounds(Duration::from_secs(5), 8192)
    .request("GET", None)
    .map_err(|e| format!("bootstrap metadata: {e}"));
    let _ = fs::remove_dir(&spool);
    let value: Value = serde_json::from_slice(&result?).map_err(|e| e.to_string())?;
    let config = pinned_config(common)?;
    same(
        field(&value, "type")? == "minidregg-enrollment-bootstrap-v2"
            && field(&value, "hostSha256")? == common.host_sha256
            && field(&value, "domain")?
                == config["domain"]
                    .as_str()
                    .map(str::to_owned)
                    .unwrap_or_else(|| config["domain"].to_string())
            && field(&value, "sshLogin")? == pin.login
            && value["memoVersions"]
                .as_array()
                .is_some_and(|a| a.iter().any(|v| v == "enrol:v2")),
        "bootstrap metadata differs from pinned Host, deployment, login or memo version",
    )?;
    Ok(Some(value))
}
fn local_json(common: &Common, verb: &str, input: &Value) -> Result<Value> {
    check_pins(common)?;
    let dir = scratch(common)?;
    let source = dir.join("input.json");
    let output = dir.join("output.json");
    create_private(
        &source,
        &serde_json::to_vec(input).map_err(|e| e.to_string())?,
    )?;
    let result = Command::new(&common.host)
        .arg(&common.config)
        .arg(verb)
        .arg(&source)
        .arg(&output)
        .output()
        .map_err(|e| format!("local Host: {e}"))?;
    same(
        result.status.success(),
        &format!("local {verb}: {}", String::from_utf8_lossy(&result.stderr)),
    )?;
    check_pins(common)?;
    workspace::bounded_json(&output)
}
fn source_context(common: &Common, pin: &Pin, next: Option<&Path>) -> Result<Value> {
    let mut input = json!({"mint":hex(&pin.context.mint),"tokenProgram":hex(&pin.context.token_program),"recipient":hex(&pin.context.recipient)});
    if let Some(path) = next {
        input["nextPublic"] = json!(hex(&key_rotation::public_file(path)?));
    }
    let value = local_json(common, "pay-enrol-v2-context", &input)?;
    let config = pinned_config(common)?;
    same(
        field(&value, "type")? == "payPurchaseContext"
            && field(&value, "mint")? == hex(&pin.context.mint)
            && field(&value, "tokenProgram")? == hex(&pin.context.token_program)
            && field(&value, "recipient")? == hex(&pin.context.recipient)
            && field(&value, "expectedSeed")? == config_nat(&config, "expectedSeed")?
            && field(&value, "domain")?
                == config["domain"]
                    .as_str()
                    .map(str::to_owned)
                    .unwrap_or_else(|| config["domain"].to_string()),
        "local source purchase context differs from pin",
    )?;
    let _: [u8; 32] = fixed(
        field(&value, "deploymentCommitment")?,
        "deploymentCommitment",
    )?;
    if next.is_some() {
        let _: [u8; 32] = fixed(field(&value, "nextKeyDigest")?, "nextKeyDigest")?;
    } else {
        same(value["nextKeyDigest"].is_null(), "unexpected source NEXT")?;
    }
    Ok(value)
}
fn status(
    common: &Common,
    identity: &[u8; 32],
    locator: Option<(&[u8; 64], &[u8; 32])>,
) -> Result<pay_status::Status> {
    let mut input = json!({"identityKey":hex(identity)});
    if let Some((signature, recipient)) = locator {
        input["signature"] = json!(hex(signature));
        input["originalRecipient"] = json!(hex(recipient));
    }
    pay_status::parse(&request(common, STATUS_OP, &input)?, &input)
}
fn expiry(common: &Common, status: &pay_status::Status) -> Result<u64> {
    if status.chain_freshness != Freshness::Fresh {
        return Err(format!("finalized chain evidence is {}; as-of {}. Wait for the verified payment watcher heartbeat before requesting a new quote",status.chain_freshness.as_str(),status.raw["asOf"]));
    }
    let hour = status
        .as_of
        .as_ref()
        .ok_or("fresh chain evidence missing")?
        .hour
        .to_u64()?;
    let expiry = common
        .expiry
        .unwrap_or(hour.checked_add(1).ok_or("chain hour overflow")?);
    same(
        expiry >= hour && expiry <= hour.saturating_add(1),
        "expiry is a processing-chain hour in currentHour..currentHour+1",
    )?;
    Ok(expiry)
}
fn retain_json(path: &Path, value: &Value) -> Result<()> {
    retain_exact(
        path,
        &serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?,
    )
}
fn retained(common: &mut Common, allow_legacy: bool) -> Result<Value> {
    workspace::private_dir(&common.directory)?;
    let latest = common.directory.join("latest-payment.json");
    let original = common.directory.join("join.json");
    let record = workspace::bounded_json(if latest.exists() { &latest } else { &original })?;
    let legacy = field(&record, "type")? == "minidregg-join-solana-v1";
    same(
        field(&record, "type")? == "minidregg-join-solana-v2" || (allow_legacy && legacy),
        "retained join is not supported for this v2 operation",
    )?;
    if !legacy {
        same(
            field(&record, "hostSha256")? == common.host_sha256
                && field(&record, "configSha256")? == config_sha256(common),
            "retained Host/config pin changed",
        )?;
    }
    if let Some(url) = record["bootstrapUrl"].as_str() {
        if let Some(selected) = &common.bootstrap {
            if !legacy {
                same(selected == url, "bootstrap URL changed")?;
            }
        } else if !legacy || SOCKET.get().is_none() {
            common.bootstrap = Some(url.into());
        }
    }
    Ok(record)
}
fn save_payment(common: &Common, record: &Value, initial: bool) -> Result<()> {
    let payments = common.directory.join("payments");
    if !payments.exists() {
        workspace::make_private_dir(&payments)?;
    }
    retain_json(
        &payments.join(format!("{}.json", workspace::random_nonce()?)),
        record,
    )?;
    if initial {
        retain_json(&common.directory.join("join.json"), record)?;
    }
    let staged = common
        .directory
        .join(format!("latest-{}.json", workspace::random_nonce()?));
    retain_json(&staged, record)?;
    fs::rename(staged, common.directory.join("latest-payment.json")).map_err(|e| e.to_string())?;
    fs::File::open(&common.directory)
        .and_then(|f| f.sync_all())
        .map_err(|e| e.to_string())
}
fn print_quote(pin: &Pin, quote: &ValidatedQuote) -> Result<()> {
    let split = quote.split();
    println!(
        "amount {} atomic ({} tokens), mint {}",
        split.amount_atomic,
        pin.display(split.amount_atomic),
        bs58::encode(pin.context.mint).into_string()
    );
    println!(
        "credit {} = birth {} + membership {} + spendable {}",
        split.minted_credit.decimal(),
        split.birth_fee.decimal(),
        split.membership_credit.decimal(),
        split.credited_remainder.decimal()
    );
    println!(
        "membership {} week(s); expires at processing-chain hour {}",
        quote.unsigned().weeks,
        quote.unsigned().expiry_hour
    );
    println!("price is not reserved; changed terms or processing after expiry retain a pending claim for explicit recovery. Wallet, Mini identity and SSH key are publicly linked by this payment.");
    std::io::stdout().flush().map_err(|e| e.to_string())
}
fn prepare_payment(
    common: &Common,
    pin: &Pin,
    identity: [u8; 32],
    key: &Path,
    ssh_private: &Path,
    next_public: Option<&Path>,
    epoch: u64,
    mode: PurchaseMode,
    name: &str,
    birth_context: Option<&Path>,
    initial: bool,
) -> Result<()> {
    check_pins(common)?;
    let signing = read_secret(key)?;
    let current = signing.verifying_key().to_bytes();
    let ssh_public = PathBuf::from(format!("{}.pub", ssh_private.display()));
    let ssh = join_solana::ssh_public_key(
        &fs::read_to_string(&ssh_public).map_err(|e| format!("SSH public key: {e}"))?,
    )?;
    let meta = metadata(common, pin)?;
    let before = status(common, &identity, None)?;
    let expiry = expiry(common, &before)?;
    same(
        (mode == PurchaseMode::Enrol && before.lease_state == LeaseState::NotEnrolled)
            || (mode == PurchaseMode::Renew && before.lease_state != LeaseState::NotEnrolled),
        "requested economic mode differs from source membership",
    )?;
    let context = source_context(common, pin, next_public)?;
    let committed = if context["nextKeyDigest"].is_null() {
        None
    } else {
        Some(fixed(field(&context, "nextKeyDigest")?, "nextKeyDigest")?)
    };
    let mut request_body = json!({"kind":"purchase","identityKey":hex(&identity),"sshKey":hex(&ssh),"mode":if mode==PurchaseMode::Enrol{"enrol"}else{"renew"},"weeks":common.weeks.to_string(),"starter":common.starter.map(|v|v.to_string()),"expiryHour":expiry.to_string()});
    if mode == PurchaseMode::Enrol {
        request_body["freshNext"] = json!(hex(
            &committed.ok_or("fresh enrollment requires --next-public or generated NEXT")?
        ));
    }
    let value = request(common, QUOTE_OP, &request_body)?;
    let source_next = if value["owner"]["nextKeyDigest"].is_null() {
        None
    } else {
        Some(fixed(
            field(&value["owner"], "nextKeyDigest")?,
            "current NEXT",
        )?)
    };
    if mode == PurchaseMode::Renew {
        if let Some(expected) = committed {
            same(
                source_next == Some(expected),
                "local next public key differs from current registry commitment",
            )?;
        }
    }
    // Only an omitted starter delegates selection to the source creation tariff.
    // The selected value is then bound through the complete quote and signatures.
    let starter = match common.starter {
        Some(value) => value,
        None => scalar(&value["split"], "minimumStarterCredit")?,
    };
    let expected = ExpectedPurchase {
        identity_key: identity,
        current_key: current,
        authority_epoch: epoch,
        ssh_key: ssh,
        next_digest: if mode == PurchaseMode::Enrol {
            committed
        } else {
            source_next
        },
        mode,
        weeks: common.weeks,
        starter,
        expiry_hour: expiry,
        context: pin.context.clone(),
        deployment_commitment: fixed(
            field(&context, "deploymentCommitment")?,
            "deploymentCommitment",
        )?,
    };
    let quote = pay_memo_v2::validate_purchase_quote(&value, &expected)?;
    check_pins(common)?;
    print_quote(pin, &quote)?;
    let dir = scratch(common)?;
    let message = dir.join("sshsig-message.bin");
    create_private(&message, &quote.signing_message()?)?;
    join_solana::run_ssh_keygen(&[
        OsStr::new("-Y"),
        OsStr::new("sign"),
        OsStr::new("-n"),
        OsStr::new(pay_memo_v2::SSH_NAMESPACE),
        OsStr::new("-f"),
        ssh_private.as_os_str(),
        message.as_os_str(),
    ])?;
    let armour =
        fs::read_to_string(dir.join("sshsig-message.bin.sig")).map_err(|e| e.to_string())?;
    check_pins(common)?;
    let memo = pay_memo_v2::sign_and_assemble(&quote, &signing, &armour)?.encode()?;
    pay_memo_v2::SignedMemo::parse_and_verify(&memo, &pin.context)?;
    let context_pin = if let Some(path) = birth_context {
        let bytes = fs::read(path).map_err(|e| e.to_string())?;
        Some(json!({"path":absolute(path)?,"sha256":format!("{:x}",Sha256::digest(bytes))}))
    } else {
        None
    };
    let record = json!({"type":"minidregg-join-solana-v2","name":name,"miniKey":hex(&identity),"authorizingKey":hex(&current),"authorityEpoch":epoch.to_string(),
        "miniKeyFile":absolute(key)?,"sshKey":hex(&ssh),"sshKeyFile":absolute(ssh_private)?,"nextPublicFile":next_public.map(absolute).transpose()?,
        "memo":memo,"enrolAddress":hex(&pin.context.recipient),"mint":hex(&pin.context.mint),"tokenProgram":hex(&pin.context.token_program),"login":pin.login,
        "enrolPin":pin.value,"quote":value,"sourceContext":context,"amountAtomic":quote.split().amount_atomic.to_string(),"bootstrapUrl":common.bootstrap,"bootstrapMetadata":meta,
        "hostSha256":common.host_sha256,"configSha256":config_sha256(common),"birthContextPin":context_pin});
    check_pins(common)?;
    save_payment(common, &record, initial)?;
    println!(
        "recipient {}",
        bs58::encode(pin.context.recipient).into_string()
    );
    println!("memo {memo}");
    println!("pay from your wallet; preflight the whole signed transaction, including wallet wrappers. No payment was submitted.");
    println!("then mini join --memo-version v2 --wait --dir {} --signature TX (with the same --host and --config)",common.directory.display());
    Ok(())
}
fn check_birth_context(record: &Value, selected: Option<&Path>) -> Result<Option<PathBuf>> {
    let retained = record.get("birthContextPin").filter(|v| !v.is_null());
    let path = selected
        .map(absolute)
        .transpose()?
        .or_else(|| retained.and_then(|v| v["path"].as_str()).map(PathBuf::from));
    if let (Some(pin), Some(path)) = (retained, path.as_ref()) {
        same(
            Path::new(field(pin, "path")?) == path
                && field(pin, "sha256")?
                    == format!(
                        "{:x}",
                        Sha256::digest(fs::read(path).map_err(|e| e.to_string())?)
                    ),
            "birth context differs from retained exact pin",
        )?;
    }
    Ok(path)
}
fn wait(
    common: &Common,
    record: &Value,
    signature: Option<String>,
    timeout: u64,
    interval: u64,
    birth: Option<&Path>,
) -> Result<()> {
    let identity = fixed(field(record, "miniKey")?, "identity")?;
    let recipient = fixed(field(record, "enrolAddress")?, "recipient")?;
    let pin = Pin::parse(record["enrolPin"].clone())?;
    metadata(common, &pin)?;
    let locator_file = common.directory.join(format!(
        "payment-{:x}.locator.json",
        Sha256::digest(field(record, "memo")?.as_bytes())
    ));
    let signature: [u8; 64] = if let Some(signature) = signature {
        bs58::decode(signature)
            .into_vec()
            .map_err(|_| "signature must be base58")?
            .try_into()
            .map_err(|_| "signature must be 64 bytes")?
    } else if locator_file.exists() {
        fixed(
            field(&workspace::bounded_json(&locator_file)?, "signature")?,
            "signature",
        )?
    } else {
        return Err("v2 --wait requires --signature TX for this exact retained payment; no enrollment-row inference".into());
    };
    retain_json(
        &locator_file,
        &json!({"signature":hex(&signature),"originalRecipient":hex(&recipient),"identityKey":hex(&identity)}),
    )?;
    let birth = check_birth_context(record, birth)?;
    let deadline = Instant::now()
        .checked_add(Duration::from_secs(timeout))
        .ok_or("wait timeout out of range")?;
    loop {
        let value = status(common, &identity, Some((&signature, &recipient)))?;
        match &value.payment {
            Payment::Pending(_) => {
                return Err(value
                    .pending_message()
                    .ok_or("pending payment lacks locator")?)
            }
            Payment::JournalNegative(negative) => {
                return Err(format!(
                    "payment has a negative journal decision: {}; no v2 consumption recorded",
                    negative.reason
                ))
            }
            Payment::Consumed(consumed) => {
                same(
                    consumed.coordinates.amount_atomic.as_str() == field(record, "amountAtomic")?,
                    "consumption amount differs from retained original payment",
                )?;
                if value.lease_state == LeaseState::Active {
                    let entry = value
                        .entry
                        .as_ref()
                        .ok_or("active source status lacks entry")?;
                    same(
                        entry.ssh_blob
                            == join_solana::ssh_blob(&fixed(field(record, "sshKey")?, "SSH key")?),
                        "admitted SSH key differs from retained payment",
                    )?;
                    let dir = scratch(common)?;
                    let output = dir.join("ids.json");
                    check_pins(common)?;
                    let run = Command::new(&common.host)
                        .arg(&common.config)
                        .arg("pay-enrol-ids")
                        .arg(hex(&identity))
                        .arg(&output)
                        .output()
                        .map_err(|e| e.to_string())?;
                    check_pins(common)?;
                    same(
                        run.status.success(),
                        "source stable identity derivation failed",
                    )?;
                    let ids = workspace::bounded_json(&output)?;
                    same(
                        entry.subject.as_str() == field(&ids, "subject")?
                            && entry.account.as_str() == field(&ids, "account")?,
                        "source status and stable identifiers differ",
                    )?;
                    let root = join_solana::admitted_workspace_v2(
                        &common.host,
                        &common.config,
                        &common.directory,
                        common.bootstrap.as_deref(),
                        record,
                        &value.raw["entry"],
                        &ids,
                        birth.as_deref(),
                    )?;
                    println!(
                        "payment consumed; active membership until chain hour {}",
                        entry.lease_until
                    );
                    println!("workspace {}", root.display());
                    println!(
                        "enter mini shell --workspace {} --home {}",
                        root.display(),
                        common.directory.join("home").display()
                    );
                    return Ok(());
                }
                return Err(format!(
                    "payment was consumed, but membership is {}; obtain a new renewal quote",
                    value.lease_state.as_str()
                ));
            }
            Payment::Unknown => {}
            Payment::NotRequested => {
                return Err("exact payment request returned no payment request".into())
            }
        }
        if Instant::now() >= deadline {
            return Err("exact payment is not yet observed; retained memo and locator are unchanged; retry --wait".into());
        }
        std::thread::sleep(
            Duration::from_secs(interval.max(1))
                .min(deadline.saturating_duration_since(Instant::now())),
        );
    }
}
fn initial(
    common: &Common,
    pin: &Pin,
    key: Option<PathBuf>,
    ssh: Option<PathBuf>,
    next: Option<PathBuf>,
    name: &str,
    birth: Option<&Path>,
) -> Result<()> {
    let preparation = common.directory.join("preparation.json");
    let (key, ssh, next) = if common.directory.exists() {
        workspace::private_dir(&common.directory)?;
        let saved = workspace::bounded_json(&preparation)?;
        same(saved["pins"] == preparation_pins(common,pin)?,
            "existing preparation differs from pinned Host/config/deployment/bootstrap or published pin")?;
        let stored =
            |field_name| -> Result<PathBuf> { Ok(PathBuf::from(field(&saved, field_name)?)) };
        let saved_key = stored("key")?;
        let saved_ssh = stored("ssh")?;
        let saved_next = stored("nextPublic")?;
        for (given, held) in [(key, &saved_key), (ssh, &saved_ssh), (next, &saved_next)] {
            if let Some(given) = given {
                same(
                    absolute(&given)? == *held,
                    "explicit key differs from retained preparation",
                )?;
            }
        }
        same(
            !common.directory.join("join.json").exists(),
            "a signed payment is already retained; use --wait or --renew",
        )?;
        (saved_key, saved_ssh, saved_next)
    } else {
        workspace::make_private_dir(&common.directory)?;
        let key = match key {
            Some(key) => absolute(&key)?,
            None => {
                let key = common.directory.join("mini.key");
                generate_key(
                    &key,
                    &common.directory.join("mini.pub"),
                    None,
                    NextKey::Beside,
                    false,
                )?;
                key
            }
        };
        let next = match next {
            Some(next) => absolute(&next)?,
            None => key_rotation::conventional_next_public(&key),
        };
        key_rotation::public_file(&next)?;
        let ssh = match ssh {
            Some(ssh) => absolute(&ssh)?,
            None => {
                let ssh = common.directory.join("id_ed25519");
                join_solana::run_ssh_keygen(&[
                    OsStr::new("-q"),
                    OsStr::new("-t"),
                    OsStr::new("ed25519"),
                    OsStr::new("-N"),
                    OsStr::new(""),
                    OsStr::new("-C"),
                    OsStr::new(name),
                    OsStr::new("-f"),
                    ssh.as_os_str(),
                ])?;
                ssh
            }
        };
        retain_json(
            &preparation,
            &json!({"key":key,"ssh":ssh,"nextPublic":next,"pins":preparation_pins(common,pin)?}),
        )?;
        (key, ssh, next)
    };
    let identity = read_secret(&key)?.verifying_key().to_bytes();
    prepare_payment(
        common,
        pin,
        identity,
        &key,
        &ssh,
        Some(&next),
        1,
        PurchaseMode::Enrol,
        name,
        birth,
        true,
    )
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let text = |value: OsString, name: &str| {
        value
            .into_string()
            .map_err(|_| format!("{name} must be UTF-8"))
    };
    if let Some(version) = args.optional("memo-version") {
        same(
            text(version, "memo-version")? == "v2",
            "v2 memo version expected",
        )?;
    }
    let mode = text(args.required("mode")?, "mode")?;
    let host = absolute(&path(args.required("host")?))?;
    let config = absolute(&path(args.required("config")?))?;
    let host_sha256 = host_image_sha256(&host)?;
    let config_bytes = fs::read(&config).map_err(|e| e.to_string())?;
    let mut common = Common {
        host,
        config,
        host_sha256,
        config_bytes,
        directory: absolute(&path(args.required("dir")?))?,
        bootstrap: args
            .optional("bootstrap-url")
            .map(|v| text(v, "bootstrap-url"))
            .transpose()?,
        weeks: u32::try_from(number(
            &args
                .optional("weeks")
                .map(|v| text(v, "weeks"))
                .transpose()?
                .unwrap_or_else(|| "1".into()),
            "weeks",
        )?)
        .map_err(|_| "weeks exceeds u32")?,
        starter: args
            .optional("starter-credit")
            .map(|v| number(&text(v, "starter-credit")?, "starter-credit"))
            .transpose()?,
        expiry: args
            .optional("expiry-hour")
            .map(|v| number(&text(v, "expiry-hour")?, "expiry-hour"))
            .transpose()?,
        epoch: args
            .optional("authority-epoch")
            .map(|v| number(&text(v, "authority-epoch")?, "authority-epoch"))
            .transpose()?,
    };
    same(common.weeks > 0, "weeks must be positive")?;
    if let Some(url) = &common.bootstrap {
        validate_url(url)?;
    }
    let birth = args.optional("birth-context").map(path);
    match mode.as_str() {
        "solana" => {
            let pin = Pin::load(&path(args.required("enrol")?))?;
            let key = args.optional("key").map(path);
            let ssh = args.optional("ssh-key").map(path);
            let next = args.optional("next-public").map(path);
            let name = args
                .optional("name")
                .map(|v| text(v, "name"))
                .transpose()?
                .unwrap_or_else(|| "friend".into());
            same(
                !name.is_empty()
                    && name
                        .bytes()
                        .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_'),
                "name must contain letters, digits, - or _",
            )?;
            same(
                common.epoch.is_none() || common.epoch == Some(1),
                "initial enrollment epoch is 1",
            )?;
            args.finish()?;
            initial(&common, &pin, key, ssh, next, &name, birth.as_deref())
        }
        "renew" => {
            let pin = Pin::load(&path(args.required("enrol")?))?;
            let selected_key = args.optional("key").map(path);
            let selected_next = args.optional("next-public").map(path);
            args.finish()?;
            let record = retained(&mut common, true)?;
            if field(&record, "type")? == "minidregg-join-solana-v1" {
                same(
                    field(&record, "enrolAddress")? == hex(&pin.context.recipient)
                        && field(&record, "mint")? == hex(&pin.context.mint)
                        && field(&record, "tokenProgram")? == hex(&pin.context.token_program)
                        && field(&record, "login")? == pin.login,
                    "explicit v2 pin differs from retained v1 payment asset/recipient/login",
                )?;
                // Explicit v2 renewal of an old member changes no registry key or NEXT.
                // A v1 bootstrap URL is not silently retargeted to a new protocol.
                if common
                    .bootstrap
                    .as_deref()
                    .is_some_and(|url| url.ends_with("/mini/v1"))
                {
                    return Err("v1 record requires explicit --bootstrap-url ending /mini/v2 or --socket for v2 renewal".into());
                }
            } else {
                same(
                    record["enrolPin"] == pin.value,
                    "published asset/recipient pin differs from retained join",
                )?;
            }
            let key = selected_key
                .map(|p| absolute(&p))
                .transpose()?
                .unwrap_or(PathBuf::from(field(&record, "miniKeyFile")?));
            let next = selected_next
                .map(|p| absolute(&p))
                .transpose()?
                .or_else(|| record["nextPublicFile"].as_str().map(PathBuf::from));
            let epoch = common
                .epoch
                .unwrap_or(if record.get("authorityEpoch").is_some() {
                    scalar(&record, "authorityEpoch")?
                } else {
                    1
                });
            same(epoch > 0, "epoch must be positive")?;
            let birth = check_birth_context(&record, birth.as_deref())?;
            prepare_payment(
                &common,
                &pin,
                fixed(field(&record, "miniKey")?, "identity")?,
                &key,
                Path::new(field(&record, "sshKeyFile")?),
                next.as_deref(),
                epoch,
                PurchaseMode::Renew,
                field(&record, "name")?,
                birth.as_deref(),
                false,
            )
        }
        "wait" => {
            let signature = args
                .optional("signature")
                .map(|v| text(v, "signature"))
                .transpose()?;
            let timeout = number(
                &args
                    .optional("timeout")
                    .map(|v| text(v, "timeout"))
                    .transpose()?
                    .unwrap_or_else(|| "600".into()),
                "timeout",
            )?;
            let interval = number(
                &args
                    .optional("interval")
                    .map(|v| text(v, "interval"))
                    .transpose()?
                    .unwrap_or_else(|| "10".into()),
                "interval",
            )?;
            args.finish()?;
            let record = retained(&mut common, false)?;
            wait(
                &common,
                &record,
                signature,
                timeout,
                interval,
                birth.as_deref(),
            )
        }
        _ => Err("v2 join expects --solana, --renew or --wait".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{BufRead, BufReader};
    use std::net::TcpListener;
    use std::os::unix::fs::PermissionsExt;

    fn pin_value() -> Value {
        json!({"type":"minidregg-enrol-pin-v2","enrolAddress":bs58::encode([10;32]).into_string(),"mint":bs58::encode([8;32]).into_string(),"tokenProgram":bs58::encode([9;32]).into_string(),"decimals":"6","login":"friend@localhost"})
    }
    fn temp() -> PathBuf {
        let p = std::env::temp_dir().join(format!(
            "mini-join-v2-test-{}",
            workspace::random_nonce().unwrap()
        ));
        workspace::make_private_dir(&p).unwrap();
        p
    }
    fn mock_server<F>(mut respond: F) -> (String, std::thread::JoinHandle<()>)
    where
        F: FnMut(&str, Value) -> Value + Send + 'static,
    {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let base = format!("http://{}/mini/v2", listener.local_addr().unwrap());
        let thread = std::thread::spawn(move || {
            listener.set_nonblocking(true).unwrap();
            let deadline = Instant::now() + Duration::from_secs(8);
            while Instant::now() < deadline {
                match listener.accept() {
                    Ok((mut stream, _)) => {
                        stream
                            .set_read_timeout(Some(Duration::from_secs(3)))
                            .unwrap();
                        let mut reader = BufReader::new(stream.try_clone().unwrap());
                        let mut line = String::new();
                        reader.read_line(&mut line).unwrap();
                        let route = line.split_whitespace().nth(1).unwrap().to_owned();
                        let mut length = 0;
                        loop {
                            line.clear();
                            reader.read_line(&mut line).unwrap();
                            if line == "\r\n" {
                                break;
                            }
                            if let Some((key, value)) = line.split_once(':') {
                                if key.eq_ignore_ascii_case("content-length") {
                                    length = value.trim().parse().unwrap();
                                }
                            }
                        }
                        let mut body = vec![0; length];
                        reader.read_exact(&mut body).unwrap();
                        let request = if body.is_empty() {
                            Value::Null
                        } else {
                            serde_json::from_slice(&body).unwrap()
                        };
                        let response = respond(&route, request);
                        let bytes = serde_json::to_vec(&response).unwrap();
                        write!(stream,"HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",bytes.len()).unwrap();
                        stream.write_all(&bytes).unwrap();
                        if response.get("stopMock") == Some(&json!(true)) {
                            break;
                        }
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                        std::thread::sleep(Duration::from_millis(5))
                    }
                    Err(e) => panic!("mock accept {e}"),
                }
            }
        });
        (base, thread)
    }
    fn quote_fixture(
        request: &Value,
        current: [u8; 32],
        epoch: u64,
        next: Option<[u8; 32]>,
    ) -> Value {
        let enrol = request["mode"] == "enrol";
        let mode = if enrol {
            1
        } else if next.is_some() {
            2
        } else {
            3
        };
        let unsigned = pay_memo_v2::Unsigned {
            mode,
            deployment_commitment: [11; 32],
            pricing_commitment: [12; 32],
            identity_key: fixed(field(request, "identityKey").unwrap(), "identity").unwrap(),
            authorizing_key: current,
            authority_epoch: epoch,
            ssh_key: fixed(field(request, "sshKey").unwrap(), "ssh").unwrap(),
            next_digest: next.unwrap_or([0; 32]),
            weeks: 1,
            starter: request["starter"]
                .as_str()
                .map(|v| number(v, "starter").unwrap())
                .unwrap_or(347),
            expiry_hour: 1001,
            amount_atomic: if enrol { 522 } else { 515 },
        };
        let frame = hex(&unsigned
            .frame(&Context {
                mint: [8; 32],
                token_program: [9; 32],
                recipient: [10; 32],
            })
            .unwrap());
        json!({"type":"payQuote","authorityRoot":hex(&[13;32]),"payRoot":hex(&[14;32]),"asOf":{"slot":"99","blockTime":"3600000","hour":"1000"},"priceReserved":false,"maxQuoteLifetimeHours":"1",
            "settlement":{"index":"0","mint":hex(&[8;32]),"tokenProgram":hex(&[9;32]),"recipient":hex(&[10;32])},
            "owner":{"identityKey":hex(&unsigned.identity_key),"authorizingKey":hex(&current),"authorityEpoch":epoch.to_string(),"nextKeyDigest":next.map(|v|hex(&v))},
            "split":{"amountAtomic":unsigned.amount_atomic.to_string(),"mintedCredit":unsigned.amount_atomic.to_string(),"birthFee":if enrol{"7"}else{"0"},"weeks":"1","membershipCredit":"168","creditedRemainder":"347","minimumStarterCredit":unsigned.starter.to_string()},
            "signing":{"kind":"purchase","unsigned":{"wireMode":mode.to_string(),"deploymentCommitment":hex(&[11;32]),"pricingCommitment":hex(&[12;32]),"identityKey":hex(&unsigned.identity_key),"authorizingKey":hex(&current),"authorityEpoch":epoch.to_string(),"sshKey":hex(&unsigned.ssh_key),"nextKeyDigest":hex(&unsigned.next_digest),"declaredNext":next.map(|v|hex(&v)),"weeks":"1","minimumStarterCredit":unsigned.starter.to_string(),"expiryHour":"1001","amountAtomic":unsigned.amount_atomic.to_string()},
                "unsignedCanonical":hex(&unsigned.encode().unwrap()),"miniMessage":frame,"sshMessage":frame,"sshNamespace":pay_memo_v2::SSH_NAMESPACE}})
    }
    #[test]
    fn pin_and_url_are_explicit_and_asset_complete() {
        let pin = Pin::parse(pin_value()).unwrap();
        assert_eq!(pin.display(1234567), "1.234567");
        for name in ["mint", "tokenProgram", "enrolAddress"] {
            let mut wrong = pin_value();
            wrong[name] = json!("EMBER_ENROL_ADDRESS");
            assert!(Pin::parse(wrong).is_err());
        }
        let mut legacy = pin_value();
        legacy["type"] = json!("minidregg-enrol-pin-v1");
        assert!(Pin::parse(legacy).is_err());
        let mut extra = pin_value();
        extra["creditPerAtomic"] = json!("1");
        assert!(Pin::parse(extra).is_err());
        assert!(validate_url("http://127.0.0.1:1234/mini/v2").is_ok());
        for bad in [
            "http://example.com/mini/v2",
            "https://box.example/mini/v1",
            "https://box.example/mini/v2?override=1",
        ] {
            assert!(validate_url(bad).is_err());
        }
    }
    fn status_fixture(freshness: &str) -> pay_status::Status {
        let request = json!({"identityKey":hex(&[1;32])});
        let mut v = pay_status::fixture(&request, json!({"state":"notRequested"}));
        v["chainFreshness"] = json!(freshness);
        pay_status::parse(&v, &request).unwrap()
    }
    #[test]
    fn fresh_quote_expiry_never_uses_local_wall_time() {
        let root = temp();
        let common = Common {
            host: root.join("host"),
            config: root.join("config"),
            directory: root,
            bootstrap: None,
            weeks: 1,
            starter: Some(0),
            expiry: None,
            epoch: None,
            host_sha256: String::new(),
            config_bytes: Vec::new(),
        };
        assert_eq!(expiry(&common, &status_fixture("fresh")).unwrap(), 1001);
        assert!(expiry(&common, &status_fixture("stale")).is_err());
        let mut wrong = common.clone();
        wrong.expiry = Some(1002);
        assert!(expiry(&wrong, &status_fixture("fresh")).is_err());
    }
    fn mock_payment(enrol: bool, starter: Option<u64>) {
        let root = temp();
        let pin = Pin::parse(pin_value()).unwrap();
        let key = root.join("mini.key");
        create_private(&key, &[42; 32]).unwrap();
        let current = read_secret(&key).unwrap().verifying_key().to_bytes();
        let identity = if enrol {
            current
        } else {
            SigningKey::from_bytes(&[41; 32]).verifying_key().to_bytes()
        };
        let next = root.join("next.pub");
        create_public(&next, &[99; 32]).unwrap();
        let ssh = root.join("ssh");
        join_solana::run_ssh_keygen(&[
            OsStr::new("-q"),
            OsStr::new("-t"),
            OsStr::new("ed25519"),
            OsStr::new("-N"),
            OsStr::new(""),
            OsStr::new("-f"),
            ssh.as_os_str(),
        ])
        .unwrap();
        let config = root.join("config.json");
        create_private(&config, b"{\"domain\":\"17\",\"expectedSeed\":\"18\"}").unwrap();
        let host = root.join("host");
        let context = root.join("context.json");
        retain_json(&context,&json!({"type":"payPurchaseContext","deploymentCommitment":hex(&[11;32]),"nextKeyDigest":if enrol{json!(hex(&[5;32]))}else{Value::Null},"domain":"17","expectedSeed":"18","mint":hex(&[8;32]),"tokenProgram":hex(&[9;32]),"recipient":hex(&[10;32])})).unwrap();
        create_private(
            &host,
            format!(
                "#!/bin/sh\ntest \"$2\" = pay-enrol-v2-context || exit 3\ncp '{}' \"$4\"\n",
                context.display()
            )
            .as_bytes(),
        )
        .unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        let sha = host_image_sha256(&host).unwrap();
        let calls = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let seen = calls.clone();
        let phase = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let observed_phase = phase.clone();
        let (base, server) = mock_server(move |route, body| {
            seen.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            match route {
                "/mini/v2/metadata" => {
                    json!({"type":"minidregg-enrollment-bootstrap-v2","hostSha256":sha,"domain":"17","sshLogin":"friend@localhost","memoVersions":["enrol:v2"]})
                }
                "/mini/v2/status" => {
                    if body.get("signature").is_some() {
                        let phase = observed_phase.load(std::sync::atomic::Ordering::SeqCst);
                        let payment = match phase {
                            1 => {
                                json!({"state":"pendingV2","amountAtomic":if enrol{"522"}else{"515"},"slot":"99","index":"0","reason":"termsStale"})
                            }
                            2 | 4 => json!({"state":"unobservedOrUnknownPositiveV1"}),
                            _ => {
                                json!({"state":"consumedV2","amountAtomic":if enrol{"522"}else{"515"},"slot":"99","index":"0","mode":if enrol{"enrol"}else{"renew"},"weeks":"1","mintedCredit":if enrol{"522"}else{"515"},"birthFee":if enrol{"7"}else{"0"},"membershipCredit":"168","creditedRemainder":"347","pricingCommitment":hex(&[12;32]),"authorization":"originalMemo","acceptedRequest":null})
                            }
                        };
                        let mut v = pay_status::fixture(&body, payment);
                        v["leaseState"] = json!(if phase == 5 { "active" } else { "expired" });
                        v["entry"] = json!({"subject":"12","account":"13","sshBlob":"00","index":"0","leaseUntil":if phase==5{"1100"}else{"999"},"enrolledSlot":"98"});
                        if phase == 4 {
                            v["paymentLocator"]["originalRecipient"] = json!(hex(&[77; 32]));
                        }
                        v
                    } else {
                        let mut v = pay_status::fixture(&body, json!({"state":"notRequested"}));
                        if !enrol {
                            v["leaseState"] = json!("expired");
                            v["entry"] = json!({"subject":"12","account":"13","sshBlob":"","index":"0","leaseUntil":"999","enrolledSlot":"98"});
                        }
                        v
                    }
                }
                "/mini/v2/quote" => {
                    assert_eq!(body["expiryHour"], "1001");
                    assert_eq!(body["weeks"], "1");
                    assert_eq!(body["starter"], json!(starter.map(|v| v.to_string())));
                    if enrol {
                        assert_eq!(body["freshNext"], hex(&[5; 32]));
                    } else {
                        assert!(body.get("freshNext").is_none());
                    }
                    quote_fixture(
                        &body,
                        current,
                        if enrol { 1 } else { 2 },
                        if enrol { Some([5; 32]) } else { None },
                    )
                }
                "/mini/v2/stop" => json!({"stopMock":true}),
                _ => panic!("unexpected route {route}"),
            }
        });
        let directory = root.join("join");
        let pin_file = root.join("enrol.json");
        retain_json(&pin_file, &pin.value).unwrap();
        if !enrol {
            workspace::make_private_dir(&directory).unwrap();
            // A v1 member can renew using mode3 without inventing a NEXT commitment.
            retain_json(
                &directory.join("join.json"),
                &json!({"type":"minidregg-join-solana-v1",
                "miniKey":hex(&identity),"miniKeyFile":key,"sshKeyFile":ssh,"name":"fixture",
                "enrolAddress":hex(&pin.context.recipient),"mint":hex(&pin.context.mint),
                "tokenProgram":hex(&pin.context.token_program),"login":pin.login,
                "bootstrapUrl":"https://old.example/mini/v1"}),
            )
            .unwrap();
        }
        let mut options = vec![
            ("memo-version", OsString::from("v2")),
            (
                "mode",
                OsString::from(if enrol { "solana" } else { "renew" }),
            ),
            ("host", host.as_os_str().to_owned()),
            ("config", config.as_os_str().to_owned()),
            ("dir", directory.as_os_str().to_owned()),
            ("bootstrap-url", OsString::from(&base)),
            ("enrol", pin_file.as_os_str().to_owned()),
            ("key", key.as_os_str().to_owned()),
            (
                "authority-epoch",
                OsString::from(if enrol { "1" } else { "2" }),
            ),
        ];
        if let Some(starter) = starter {
            options.push(("starter-credit", OsString::from(starter.to_string())));
        }
        if enrol {
            options.push(("ssh-key", ssh.as_os_str().to_owned()));
            options.push(("next-public", next.as_os_str().to_owned()));
        }
        run(Args {
            command: OsString::from("join"),
            values: options
                .into_iter()
                .map(|(k, v)| (OsString::from(format!("--{k}")), v))
                .collect(),
        })
        .unwrap();
        let common = Common {
            host_sha256: host_image_sha256(&host).unwrap(),
            config_bytes: fs::read(&config).unwrap(),
            host,
            config,
            directory: directory.clone(),
            bootstrap: Some(base.clone()),
            weeks: 1,
            starter: Some(347),
            expiry: None,
            epoch: None,
        };
        let record = workspace::bounded_json(&directory.join("latest-payment.json")).unwrap();
        assert_eq!(record["miniKey"], hex(&identity));
        assert_eq!(record["authorizingKey"], hex(&current));
        let memo = pay_memo_v2::SignedMemo::parse_and_verify(
            field(&record, "memo").unwrap(),
            &pin.context,
        )
        .unwrap();
        assert_eq!(memo.unsigned.mode, if enrol { 1 } else { 3 });
        assert_eq!(memo.unsigned.identity_key, identity);
        assert_eq!(memo.unsigned.authorizing_key, current);
        assert_eq!(calls.load(std::sync::atomic::Ordering::SeqCst), 3);
        assert_eq!(fs::read_dir(directory.join("payments")).unwrap().count(), 1);
        if !enrol {
            assert_eq!(
                workspace::bounded_json(&directory.join("join.json")).unwrap()["type"],
                "minidregg-join-solana-v1"
            );
        }
        for (value, expected_error) in [
            (1, "payment received; admission pending"),
            (2, "not yet observed"),
            (3, "payment was consumed, but membership is expired"),
            (4, "payment locator mismatch"),
            (5, "admitted SSH key differs"),
        ] {
            phase.store(value, std::sync::atomic::Ordering::SeqCst);
            let error = wait(
                &common,
                &record,
                Some(bs58::encode([71; 64]).into_string()),
                0,
                1,
                None,
            )
            .unwrap_err();
            assert!(error.contains(expected_error), "{error}");
        }
        // Retrying without --signature uses the exact immutable locator, never entry inference.
        phase.store(1, std::sync::atomic::Ordering::SeqCst);
        assert!(wait(&common, &record, None, 0, 1, None)
            .unwrap_err()
            .contains("payment received; admission pending"));
        assert_eq!(
            workspace::bounded_json(&directory.join("latest-payment.json")).unwrap(),
            record
        );
        let spool = root.join("stop-spool");
        workspace::make_private_dir(&spool).unwrap();
        minidregg_pay_watcher::CurlTransport::new("mock-stop", format!("{base}/stop"), &spool)
            .unwrap()
            .request("GET", None)
            .unwrap();
        server.join().unwrap();
    }
    #[test]
    fn synthetic_http_and_local_host_purchase_retains_two_valid_possessions() {
        mock_payment(true, Some(347))
    }
    #[test]
    fn synthetic_rotated_renewal_preserves_identity_and_none_commitment() {
        mock_payment(false, Some(347))
    }
    #[test]
    fn source_recommendation_is_used_only_when_starter_is_omitted() {
        mock_payment(true, None);
        mock_payment(true, Some(0));
    }
    #[test]
    fn preparation_and_local_source_require_unchanged_config_and_host() {
        let root = temp();
        let host = root.join("host");
        let config = root.join("config.json");
        create_private(&config, b"{\"domain\":\"17\",\"expectedSeed\":\"18\"}").unwrap();
        create_private(&host,b"#!/bin/sh\nprintf '{\"domain\":\"17\",\"expectedSeed\":\"19\"}' > \"$1\"\nprintf '{}' > \"$4\"\n").unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        let common = Common {
            host_sha256: host_image_sha256(&host).unwrap(),
            config_bytes: fs::read(&config).unwrap(),
            host,
            config,
            directory: root.clone(),
            bootstrap: None,
            weeks: 1,
            starter: None,
            expiry: None,
            epoch: None,
        };
        let pin = Pin::parse(pin_value()).unwrap();
        retain_json(&root.join("preparation.json"),&json!({"key":"unused","ssh":"unused","nextPublic":"unused","pins":preparation_pins(&common,&pin).unwrap()})).unwrap();
        let error = local_json(&common, "fixture", &json!({})).unwrap_err();
        assert!(error.contains("config bytes changed"), "{error}");
        assert!(check_pins(&common).is_err());
        let mut changed = common.clone();
        changed.config_bytes = fs::read(&changed.config).unwrap();
        assert!(initial(&changed, &pin, None, None, None, "fixture", None)
            .unwrap_err()
            .contains("existing preparation differs"));
        let mut changed = common.clone();
        changed.bootstrap = Some("https://other.example/mini/v2".into());
        assert!(initial(&changed, &pin, None, None, None, "fixture", None)
            .unwrap_err()
            .contains("existing preparation differs"));
        fs::write(&common.config, &common.config_bytes).unwrap();
        let wrong_context = json!({"type":"payPurchaseContext","deploymentCommitment":hex(&[11;32]),
            "nextKeyDigest":null,"domain":"17","expectedSeed":"19","mint":hex(&pin.context.mint),
            "tokenProgram":hex(&pin.context.token_program),"recipient":hex(&pin.context.recipient)});
        fs::write(
            &common.host,
            format!("#!/bin/sh\nprintf '%s' '{}' > \"$4\"\n", wrong_context),
        )
        .unwrap();
        let mut repinned = common.clone();
        repinned.host_sha256 = host_image_sha256(&repinned.host).unwrap();
        assert!(source_context(&repinned, &pin, None)
            .unwrap_err()
            .contains("source purchase context differs"));
        fs::write(&common.host, b"different Host bytes").unwrap();
        assert!(local_json(&common, "fixture", &json!({}))
            .unwrap_err()
            .contains("Host or config bytes changed"));
    }
}
