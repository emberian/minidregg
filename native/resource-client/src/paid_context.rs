//! Closed paid custody contexts. These are transport/origin snapshots, never
//! generic workspace authority or a bypass around normal workspace loading.
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Source {
    Workspace,
    Join,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SigningIntent {
    Current,
    Next,
}

#[derive(Default)]
pub(crate) struct Options {
    pub host: Option<PathBuf>,
    pub config: Option<PathBuf>,
    pub bootstrap: Option<String>,
    pub key: Option<PathBuf>,
    pub payment_record: Option<PathBuf>,
}

#[derive(Clone)]
pub(crate) struct Context {
    root: PathBuf,
    source: Source,
    subject: Option<String>,
    identity: Option<[u8; 32]>,
    origin: Option<Vec<u8>>,
    payment: Option<Origin>,
    seed: Option<String>,
    host: PathBuf,
    sha: String,
    config: Vec<u8>,
    bootstrap: Option<String>,
    socket: Option<PathBuf>,
    ssh: Option<PathBuf>,
    key: Option<PathBuf>,
    intent: Option<SigningIntent>,
}

#[derive(Clone)]
struct Origin {
    path: PathBuf,
    payment: Vec<u8>,
    locator: Vec<u8>,
}
fn string<'a>(value: &'a Value, name: &str) -> Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("paid snapshot lacks {name}"))
}
fn fixed<const N: usize>(value: &Value, name: &str) -> Result<[u8; N]> {
    let text = string(value, name)?;
    if text.len() != N * 2
        || !text
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(format!(
            "paid snapshot {name} is not {N} lowercase hexadecimal bytes"
        ));
    }
    decode_hex(text)?
        .try_into()
        .map_err(|_| format!("invalid {name}"))
}
fn absolute_member(value: &Value, name: &str) -> Result<PathBuf> {
    let path = PathBuf::from(string(value, name)?);
    if !path.is_absolute() {
        return Err(format!("paid snapshot {name} must be absolute"));
    }
    Ok(path)
}
fn selected_path(selected: &Option<PathBuf>, retained: &Path, name: &str) -> Result<PathBuf> {
    let chosen = selected.as_deref().unwrap_or(retained);
    if !chosen.is_absolute() {
        return Err(format!("paid {name} must be absolute"));
    }
    Ok(chosen.to_path_buf())
}
fn read(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let meta = fs::symlink_metadata(path).map_err(|e| format!("{}: {e}", path.display()))?;
    if !meta.is_file() || meta.len() > limit as u64 {
        return Err("paid snapshot must be a bounded regular file".into());
    }
    let mut bytes = Vec::new();
    File::open(path)
        .and_then(|f| f.take(limit as u64 + 1).read_to_end(&mut bytes))
        .map_err(|e| e.to_string())?;
    if bytes.len() > limit {
        return Err("paid snapshot exceeds bound".into());
    }
    Ok(bytes)
}
fn hash(bytes: &[u8]) -> String {
    hex(&sha2::Sha256::digest(bytes))
}
fn natural(value: &Value, name: &str) -> Result<String> {
    let text = match value.get(name) {
        Some(Value::String(s)) => s.clone(),
        Some(Value::Number(n)) => n
            .as_u64()
            .ok_or("paid snapshot integer is not exact")?
            .to_string(),
        _ => return Err(format!("paid snapshot lacks {name}")),
    };
    if text.is_empty()
        || text.len() > 78
        || !text.bytes().all(|b| b.is_ascii_digit())
        || (text.len() > 1 && text.starts_with('0'))
    {
        return Err(format!("paid snapshot {name} is not canonical decimal"));
    }
    Ok(text)
}
fn bootstrap(value: Option<&str>, selected: &Option<String>) -> Result<Option<String>> {
    if let (Some(old), Some(new)) = (value, selected.as_deref()) {
        if old != new {
            return Err("paid bootstrap URL differs from retained context".into());
        }
    }
    let url = selected.as_deref().or(value).map(str::to_owned);
    if let Some(url) = &url {
        minidregg_pay_watcher::transport::validate_endpoint(url)?;
        if !url.ends_with("/mini/v2") || url.contains('?') || url.contains('#') {
            return Err("paid bootstrap URL must name /mini/v2 without query or fragment".into());
        }
    }
    Ok(url)
}

impl Context {
    pub(crate) fn retain_origin(&self, record: &Path) -> Result<()> {
        if let Some(origin) = &self.payment {
            create_private(&record.join("origin-payment.json"), &origin.payment)?;
            create_private(&record.join("origin-locator.json"), &origin.locator)?;
            sync_directory_ancestors(record)?;
        }
        Ok(())
    }
    pub(crate) fn origin_claim_id(&self) -> Result<&[u8]> {
        self.origin
            .as_deref()
            .ok_or("quote requires an exact retained JOIN payment locator".into())
    }
    pub(crate) fn identity_key(&self) -> Result<&[u8; 32]> {
        self.identity
            .as_ref()
            .ok_or("quote requires a retained JOIN identity".into())
    }
    pub(crate) fn host(&self) -> &Path {
        &self.host
    }
    pub(crate) fn host_sha(&self) -> &str {
        &self.sha
    }
    pub(crate) fn config(&self) -> &[u8] {
        &self.config
    }
    pub(crate) fn bootstrap(&self) -> Option<&str> {
        self.bootstrap.as_deref()
    }
    pub(crate) fn socket(&self) -> Option<&Path> {
        self.socket.as_deref()
    }
    pub(crate) fn key(&self) -> Result<&Path> {
        self.key
            .as_deref()
            .ok_or("retained lookup context cannot supply signing custody".into())
    }

    /// Serialization of validated fields only; no caller-selected grants,
    /// current authority view, or raw workspace snapshot is exported.
    pub(crate) fn binding(&self) -> Result<Value> {
        let mut value = json!({"workspace":utf8_path(&self.root)?,"subject":self.subject,
            "hostSha256":self.sha,"bootstrapUrl":self.bootstrap,
            "socket":self.socket.as_ref().map(|p|transport::pinned_address(p)).transpose()?,
            "configSha256":hash(&self.config), "genesisExpectedSeed":self.seed});
        if self.source == Source::Join {
            value["contextType"] = json!("join");
            value["identityKey"] = json!(hex(self
                .identity
                .as_ref()
                .ok_or("join identity missing")?));
            value["originClaimId"] =
                json!(hex(self.origin.as_deref().ok_or("join origin missing")?));
            let origin = self.payment.as_ref().ok_or("join origin record missing")?;
            value["originRecordPath"] = json!(utf8_path(&origin.path)?);
            value["originRecordSha256"] = json!(hash(&origin.payment));
            value["originLocatorSha256"] = json!(hash(&origin.locator));
        }
        Ok(value)
    }

    /// Applies only physical pins. HTTPS requires no SSH credential, registry
    /// read, resource entitlement, or current signing key.
    pub(crate) fn pin_transport(&self) -> Result<()> {
        pin_remote_host(&self.sha)?;
        if let Some(socket) = &self.socket {
            match SOCKET.get() {
                Some(selected) if selected != socket => {
                    return Err("selected socket differs from paid context".into())
                }
                Some(_) => {}
                None => {
                    SOCKET
                        .set(socket.clone())
                        .map_err(|_| "cannot pin paid socket")?;
                }
            }
            if transport::is_remote(socket) {
                if let Some(identity) = &self.ssh {
                    pin_ssh_identity(identity)?;
                }
            }
        }
        Ok(())
    }

    /// The command has already been decoded by the pinned local source.
    /// Binding a retained origin is not admission; op185 still checks current
    /// custody, the exact original claim and the composed current law.
    pub(crate) fn validate_source_command(&self, command: &Value) -> Result<()> {
        let Some(identity) = self.identity else {
            return Ok(());
        };
        let action = command.get("action").ok_or("source claim action missing")?;
        if fixed::<32>(action, "identityKey")? != identity {
            return Err("source claim identity differs from retained join".into());
        }
        match string(action, "action")? {
            "acceptCurrentQuote" => {
                if self.intent == Some(SigningIntent::Next) {
                    return Err("NEXT intent cannot accept a quote".into());
                }
                let actual = fixed::<102>(action, "claimId")?;
                if self.origin.as_deref() != Some(actual.as_slice()) {
                    return Err("source claim differs from exact retained payment origin".into());
                }
            }
            "rotatePendingOwner" => {
                if self.intent == Some(SigningIntent::Current) {
                    return Err("current-key intent cannot rotate pending custody".into());
                }
            }
            _ => return Err("unknown closed paid action".into()),
        }
        Ok(())
    }
}

fn workspace_snapshot(root: &Path, options: &Options, lookup: bool) -> Result<Context> {
    workspace::private_dir(root)?;
    let value = if lookup {
        // Strict typed projection only: never invoke load/recheck_commitment
        // on historical lookup. The immutable operation record supplies the
        // exact original config/profile/transport binding checked below.
        for directory in ["refs", "attempts", "sources", "proposals"] {
            workspace::private_dir(&root.join(directory))?;
        }
        workspace::bounded_json(&root.join("workspace.json"))?
    } else {
        workspace::load(root)?
    };
    if string(&value, "type")? != "minidregg-participant-workspace-v1" {
        return Err("unknown paid workspace snapshot".into());
    }
    let subject = natural(&value, "subject")?;
    let config_path = selected_path(
        &options.config,
        &absolute_member(&value, "config")?,
        "config",
    )?;
    let config = read(&config_path, 1024 * 1024)?;
    let config_json: Value = serde_json::from_slice(&config).map_err(|e| e.to_string())?;
    let seed = natural(&config_json, "expectedSeed")?;
    let held_host = workspace::workspace_host(&value)?;
    let host = selected_path(&options.host, &held_host, "local Host")?;
    let sha = host_image_sha256(&host)?;
    if let Some(pin) = value.get("hostSha256") {
        if pin.as_str() != Some(sha.as_str()) {
            return Err("workspace Host image differs from pin".into());
        }
    }
    let bootstrap = bootstrap(None, &options.bootstrap)?;
    let socket = if bootstrap.is_some() {
        None
    } else {
        let socket = PathBuf::from(string(&value, "socket")?);
        if !socket.is_absolute() && !transport::is_remote(&socket) {
            return Err("paid workspace socket is not pinned".into());
        }
        Some(socket)
    };
    let ssh = value
        .get("sshIdentity")
        .filter(|v| !v.is_null())
        .map(|_| absolute_member(&value, "sshIdentity"))
        .transpose()?;
    let key = if lookup {
        None
    } else {
        Some(selected_path(
            &options.key,
            &absolute_member(&value, "key")?,
            "signing key",
        )?)
    };
    Ok(Context {
        root: root.to_path_buf(),
        source: Source::Workspace,
        subject: Some(subject),
        identity: None,
        origin: None,
        payment: None,
        seed: Some(seed),
        host,
        sha,
        config,
        bootstrap,
        socket,
        ssh,
        key,
        intent: None,
    })
}

fn join_snapshot(
    root: &Path,
    options: &Options,
    intent: Option<SigningIntent>,
    retained: Option<Origin>,
) -> Result<Context> {
    workspace::private_dir(root)?;
    let is_recovery = retained.is_some();
    let record_path = retained
        .as_ref()
        .map(|o| o.path.clone())
        .or_else(|| options.payment_record.clone())
        .unwrap_or_else(|| root.join("join.json"));
    if !record_path.is_absolute() {
        return Err("payment record must be absolute".into());
    }
    if is_recovery
        && options
            .payment_record
            .as_ref()
            .is_some_and(|p| p != &record_path)
    {
        return Err("payment record differs from retained operation origin".into());
    }
    let join_bytes = match &retained {
        Some(origin) => origin.payment.clone(),
        None => read(&record_path, 1024 * 1024)?,
    };
    let join: Value = serde_json::from_slice(&join_bytes).map_err(|e| e.to_string())?;
    if string(&join, "type")? != "minidregg-join-solana-v2" {
        return Err("pending claim needs immutable signed v2 join.json".into());
    }
    let identity = fixed::<32>(&join, "miniKey")?;
    let current = fixed::<32>(&join, "authorizingKey")?;
    let retained_key = absolute_member(&join, "miniKeyFile")?;
    let ssh = absolute_member(&join, "sshKeyFile")?;
    if !is_recovery {
        let initial = workspace::bounded_json(&root.join("join.json"))?;
        if fixed::<32>(&initial, "miniKey")? != identity {
            return Err("selected payment belongs to another JOIN identity".into());
        }
        // First v2 preparation has strong custody/deployment pins. Later
        // payments are independently signed immutable records; legacy v1 JOIN
        // directories legitimately have no v2 preparation.
        if record_path == root.join("join.json") {
            let preparation = workspace::bounded_json(&root.join("preparation.json"))?;
            let pins = preparation
                .get("pins")
                .ok_or("join preparation lacks immutable deployment pins")?;
            if absolute_member(&preparation, "key")? != retained_key
                || absolute_member(&preparation, "ssh")? != ssh
                || preparation.get("nextPublic") != join.get("nextPublicFile")
                || pins.get("enrolPin") != join.get("enrolPin")
                || pins.get("bootstrapUrl") != join.get("bootstrapUrl")
                || pins.get("hostSha256") != join.get("hostSha256")
                || pins.get("configSha256") != join.get("configSha256")
            {
                return Err("signed join differs from retained preparation".into());
            }
            let source = join
                .get("sourceContext")
                .ok_or("join source context missing")?;
            if natural(pins, "domain")? != natural(source, "domain")?
                || natural(pins, "expectedSeed")? != natural(source, "expectedSeed")?
            {
                return Err("preparation source domain/genesis differs".into());
            }
        }
    }
    let host = options
        .host
        .as_ref()
        .filter(|p| p.is_absolute())
        .ok_or("pending join context requires --host ABS")?
        .clone();
    let config_path = options
        .config
        .as_ref()
        .filter(|p| p.is_absolute())
        .ok_or("pending join context requires --config ABS")?
        .clone();
    let sha = host_image_sha256(&host)?;
    let config = read(&config_path, 1024 * 1024)?;
    if string(&join, "hostSha256")? != sha || string(&join, "configSha256")? != hash(&config) {
        return Err("join Host/config pin changed".into());
    }
    let config_json: Value = serde_json::from_slice(&config).map_err(|e| e.to_string())?;
    let source = join
        .get("sourceContext")
        .ok_or("join lacks pinned source context")?;
    let seed = natural(source, "expectedSeed")?;
    if natural(&config_json, "domain")? != natural(source, "domain")?
        || natural(&config_json, "expectedSeed")? != seed
    {
        return Err("join source domain/genesis differs from pinned config".into());
    }
    let payment = pay_memo_v2::Context {
        mint: fixed(&join, "mint")?,
        token_program: fixed(&join, "tokenProgram")?,
        recipient: fixed(&join, "enrolAddress")?,
    };
    let memo = pay_memo_v2::SignedMemo::parse_and_verify(string(&join, "memo")?, &payment)?;
    if memo.unsigned.identity_key != identity
        || memo.unsigned.authorizing_key != current
        || memo.unsigned.ssh_key != fixed::<32>(&join, "sshKey")?
        || memo.unsigned.authority_epoch.to_string() != natural(&join, "authorityEpoch")?
        || memo.unsigned.amount_atomic.to_string() != natural(&join, "amountAtomic")?
        || memo.unsigned.deployment_commitment != fixed::<32>(source, "deploymentCommitment")?
        || fixed::<32>(source, "mint")? != payment.mint
        || fixed::<32>(source, "tokenProgram")? != payment.token_program
        || fixed::<32>(source, "recipient")? != payment.recipient
    {
        return Err("retained join metadata differs from signed v2 memo/origin".into());
    }
    let locator_bytes = match &retained {
        Some(origin) => origin.locator.clone(),
        None => read(
            &root.join(format!(
                "payment-{}.locator.json",
                hash(string(&join, "memo")?.as_bytes())
            )),
            4096,
        )?,
    };
    let locator: Value = serde_json::from_slice(&locator_bytes).map_err(|e| e.to_string())?;
    if fixed::<32>(&locator, "identityKey")? != identity
        || fixed::<32>(&locator, "originalRecipient")? != payment.recipient
    {
        return Err("retained payment locator differs from signed join".into());
    }
    let mut origin = b"soltx:".to_vec();
    origin.extend_from_slice(&fixed::<64>(&locator, "signature")?);
    origin.extend_from_slice(&payment.recipient);
    let bootstrap = bootstrap(
        join.get("bootstrapUrl").and_then(Value::as_str),
        &options.bootstrap,
    )?;
    let socket = if bootstrap.is_some() {
        None
    } else {
        Some(
            SOCKET
                .get()
                .cloned()
                .ok_or("join claim needs retained bootstrap URL or explicit socket")?,
        )
    };
    let key = match intent {
        None => None,
        Some(SigningIntent::Current) => Some(selected_path(
            &options.key,
            &retained_key,
            "current signing key",
        )?),
        Some(SigningIntent::Next) => Some(
            options
                .key
                .as_ref()
                .filter(|p| p.is_absolute())
                .ok_or("pending rotation requires --key with explicit successor secret path")?
                .clone(),
        ),
    };
    Ok(Context {
        root: root.to_path_buf(),
        source: Source::Join,
        subject: None,
        identity: Some(identity),
        origin: Some(origin),
        payment: Some(Origin {
            path: record_path,
            payment: join_bytes,
            locator: locator_bytes,
        }),
        seed: Some(seed),
        host,
        sha,
        config,
        bootstrap,
        socket,
        ssh: Some(ssh),
        key,
        intent,
    })
}

pub(crate) fn fresh_workspace(root: &Path, options: &Options) -> Result<Context> {
    workspace_snapshot(root, options, false)
}
pub(crate) fn fresh_join(root: &Path, options: &Options, intent: SigningIntent) -> Result<Context> {
    join_snapshot(root, options, Some(intent), None)
}
pub(crate) fn retained_lookup(
    root: &Path,
    source: Source,
    record: &Path,
    options: &Options,
) -> Result<Context> {
    workspace::private_dir(record)?;
    let operation = workspace::bounded_json(&record.join("operation.json"))?;
    if string(&operation, "type")? != "minidregg-pay-claim-operation-v1" {
        return Err("unknown immutable claim operation".into());
    }
    let binding = operation
        .get("binding")
        .ok_or("claim operation binding missing")?;
    let mut options = Options {
        host: options.host.clone(),
        config: options.config.clone(),
        bootstrap: options.bootstrap.clone(),
        key: None,
        payment_record: options.payment_record.clone(),
    };
    options.bootstrap = bootstrap(
        binding.get("bootstrapUrl").and_then(Value::as_str),
        &options.bootstrap,
    )?;
    let context = match source {
        Source::Workspace => workspace_snapshot(root, &options, true)?,
        Source::Join => join_snapshot(
            root,
            &options,
            None,
            Some(Origin {
                path: absolute_member(binding, "originRecordPath")?,
                payment: read(&record.join("origin-payment.json"), 1024 * 1024)?,
                locator: read(&record.join("origin-locator.json"), 4096)?,
            }),
        )?,
    };
    if &context.binding()? != binding
        || context.config != read(&record.join("config.json"), 1024 * 1024)?
    {
        return Err(
            "retained claim transport/identity/config/profile/genesis binding changed".into(),
        );
    }
    // The original source plan/profile and receipt hashes are additionally
    // verified by pay_claim before exact op186. No current custody is read.
    Ok(context)
}

#[cfg(test)]
mod tests {
    use super::*;
    struct Fixture {
        root: PathBuf,
        options: Options,
    }
    impl Fixture {
        fn new() -> Self {
            let root = env::temp_dir().join(format!(
                "mini-paid-context-{}-{}",
                std::process::id(),
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            workspace::make_private_dir(&root).unwrap();
            create_private(&root.join("Host"), b"fixture local Host identity").unwrap();
            create_private(
                &root.join("public.config"),
                br#"{"domain":"4","expectedSeed":"77"}"#,
            )
            .unwrap();
            let options = Options {
                host: Some(root.join("Host")),
                config: Some(root.join("public.config")),
                bootstrap: Some("http://127.0.0.1:12345/mini/v2".into()),
                ..Options::default()
            };
            Self { root, options }
        }
        fn payment(&self, amount: u64, mode: u8) -> (Value, Value) {
            let mini = SigningKey::from_bytes(&[1; 32]);
            let ssh = SigningKey::from_bytes(&[2; 32]);
            let context = pay_memo_v2::Context {
                mint: [7; 32],
                token_program: [8; 32],
                recipient: [9; 32],
            };
            let unsigned = pay_memo_v2::Unsigned {
                mode,
                deployment_commitment: [3; 32],
                pricing_commitment: [4; 32],
                identity_key: mini.verifying_key().to_bytes(),
                authorizing_key: mini.verifying_key().to_bytes(),
                authority_epoch: 1,
                ssh_key: ssh.verifying_key().to_bytes(),
                next_digest: if mode == 3 { [0; 32] } else { [5; 32] },
                weeks: 2,
                starter: 347,
                expiry_hour: 100,
                amount_atomic: amount,
            };
            let frame = unsigned.frame(&context).unwrap();
            let memo = pay_memo_v2::SignedMemo {
                unsigned,
                mini_signature: mini.sign(&frame).to_bytes(),
                ssh_signature: ssh
                    .sign(&join_solana::sshsig_signed_data_for(
                        pay_memo_v2::SSH_NAMESPACE,
                        &frame,
                    ))
                    .to_bytes(),
            }
            .encode()
            .unwrap();
            let payment = json!({"type":"minidregg-join-solana-v2",
                "miniKey":hex(mini.verifying_key().as_bytes()),"authorizingKey":hex(mini.verifying_key().as_bytes()),
                "authorityEpoch":"1","miniKeyFile":self.root.join("missing-mini-secret"),
                "sshKey":hex(ssh.verifying_key().as_bytes()),"sshKeyFile":self.root.join("missing-ssh-secret"),
                "nextPublicFile":null,"memo":memo,"amountAtomic":amount.to_string(),
                "enrolAddress":hex(&context.recipient),"mint":hex(&context.mint),"tokenProgram":hex(&context.token_program),
                "enrolPin":{"fixture":"public pin"},"bootstrapUrl":self.options.bootstrap,
                "hostSha256":host_image_sha256(self.options.host.as_ref().unwrap()).unwrap(),
                "configSha256":hash(&fs::read(self.options.config.as_ref().unwrap()).unwrap()),
                "sourceContext":{"deploymentCommitment":hex(&[3;32]),"domain":"4","expectedSeed":"77",
                    "mint":hex(&context.mint),"tokenProgram":hex(&context.token_program),"recipient":hex(&context.recipient)}});
            let locator = json!({"signature":hex(&[amount as u8;64]),"originalRecipient":hex(&context.recipient),
                "identityKey":payment["miniKey"]});
            (payment, locator)
        }
        fn save(&self, path: &Path, payment: &Value, locator: &Value) {
            create_private(path, &serde_json::to_vec(payment).unwrap()).unwrap();
            create_private(
                &self.root.join(format!(
                    "payment-{}.locator.json",
                    hash(payment["memo"].as_str().unwrap().as_bytes())
                )),
                &serde_json::to_vec(locator).unwrap(),
            )
            .unwrap();
        }
        fn initial(&self, payment: &Value, locator: &Value) {
            self.save(&self.root.join("join.json"), payment, locator);
            let prep = json!({"key":payment["miniKeyFile"],"ssh":payment["sshKeyFile"],"nextPublic":payment["nextPublicFile"],
                "pins":{"hostSha256":payment["hostSha256"],"configSha256":payment["configSha256"],
                    "domain":"4","expectedSeed":"77","bootstrapUrl":payment["bootstrapUrl"],"enrolPin":payment["enrolPin"]}});
            create_private(
                &self.root.join("preparation.json"),
                &serde_json::to_vec(&prep).unwrap(),
            )
            .unwrap();
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.root);
        }
    }

    #[test]
    fn immutable_origin_recovery_ignores_later_payment_and_missing_keys() {
        let f = Fixture::new();
        let (first, first_locator) = f.payment(10, 1);
        f.initial(&first, &first_locator);
        let first_context = fresh_join(&f.root, &f.options, SigningIntent::Current).unwrap();
        assert!(!first_context.key().unwrap().exists());
        let record = f.root.join("operation");
        workspace::make_private_dir(&record).unwrap();
        first_context.retain_origin(&record).unwrap();
        create_private(&record.join("config.json"), first_context.config()).unwrap();
        create_private(
            &record.join("operation.json"),
            &serde_json::to_vec(&json!({
                "type":"minidregg-pay-claim-operation-v1","binding":first_context.binding().unwrap()
            }))
            .unwrap(),
        )
        .unwrap();

        let (second, second_locator) = f.payment(20, 3);
        let second_path = f.root.join("renewal.json");
        f.save(&second_path, &second, &second_locator);
        let renewal = Options {
            payment_record: Some(second_path.clone()),
            ..Options {
                host: f.options.host.clone(),
                config: f.options.config.clone(),
                bootstrap: f.options.bootstrap.clone(),
                ..Options::default()
            }
        };
        let second_context = fresh_join(&f.root, &renewal, SigningIntent::Current).unwrap();
        assert_ne!(
            first_context.origin_claim_id().unwrap(),
            second_context.origin_claim_id().unwrap()
        );
        create_private(
            &f.root.join("latest-payment.json"),
            &serde_json::to_vec(&second).unwrap(),
        )
        .unwrap();
        // Historical lookup must not depend on either mutable latest/preparation
        // or even the surviving initial JOIN presentation.
        fs::remove_file(f.root.join("preparation.json")).unwrap();
        fs::remove_file(f.root.join("join.json")).unwrap();
        let recovered = retained_lookup(&f.root, Source::Join, &record, &f.options).unwrap();
        assert_eq!(
            recovered.binding().unwrap(),
            first_context.binding().unwrap()
        );
        assert!(recovered.key().is_err());
        assert!(retained_lookup(&f.root, Source::Join, &record, &renewal).is_err());
        fs::write(
            record.join("origin-locator.json"),
            serde_json::to_vec(&second_locator).unwrap(),
        )
        .unwrap();
        assert!(retained_lookup(&f.root, Source::Join, &record, &f.options).is_err());
    }

    #[test]
    fn legacy_join_can_select_signed_v2_renewal_without_v2_preparation() {
        let f = Fixture::new();
        let (payment, locator) = f.payment(30, 3);
        create_private(
            &f.root.join("join.json"),
            &serde_json::to_vec(&json!({
            "type":"minidregg-join-solana-v1","miniKey":payment["miniKey"]}))
            .unwrap(),
        )
        .unwrap();
        let path = f.root.join("renewal.json");
        f.save(&path, &payment, &locator);
        let options = Options {
            host: f.options.host.clone(),
            config: f.options.config.clone(),
            bootstrap: f.options.bootstrap.clone(),
            payment_record: Some(path),
            ..Options::default()
        };
        let context = fresh_join(&f.root, &options, SigningIntent::Current).unwrap();
        assert_eq!(context.origin_claim_id().unwrap()[..6], *b"soltx:");
        let mut bad = payment.clone();
        bad["miniKey"] = json!(hex(&[99; 32]));
        fs::write(f.root.join("join.json"), serde_json::to_vec(&bad).unwrap()).unwrap();
        assert!(fresh_join(&f.root, &options, SigningIntent::Current).is_err());
    }

    #[test]
    fn fresh_join_refuses_pin_signature_locator_and_command_substitution() {
        let f = Fixture::new();
        let (payment, locator) = f.payment(40, 1);
        f.initial(&payment, &locator);
        let context = fresh_join(&f.root, &f.options, SigningIntent::Current).unwrap();
        let command = json!({"action":{"action":"acceptCurrentQuote","identityKey":payment["miniKey"],
            "claimId":hex(context.origin_claim_id().unwrap())}});
        context.validate_source_command(&command).unwrap();
        let mut changed = command.clone();
        changed["action"]["claimId"] = json!(hex(&[44; 102]));
        assert!(context.validate_source_command(&changed).is_err());
        let mut changed = command;
        changed["action"]["action"] = json!("rotatePendingOwner");
        assert!(context.validate_source_command(&changed).is_err());
        let mut changed = payment.clone();
        changed["amountAtomic"] = json!("41");
        fs::write(
            f.root.join("join.json"),
            serde_json::to_vec(&changed).unwrap(),
        )
        .unwrap();
        assert!(fresh_join(&f.root, &f.options, SigningIntent::Current).is_err());
        fs::write(
            f.root.join("join.json"),
            serde_json::to_vec(&payment).unwrap(),
        )
        .unwrap();
        fs::write(
            f.options.config.as_ref().unwrap(),
            br#"{"domain":"4","expectedSeed":"78"}"#,
        )
        .unwrap();
        assert!(fresh_join(&f.root, &f.options, SigningIntent::Current).is_err());
    }
}
