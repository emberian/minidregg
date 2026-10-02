//! Fresh native owner observations. These are read-only snapshots, not signed
//! mutation receipts. Proof values can only be obtained by querying the source;
//! archived evidence must never be deserialized back into current authority.
use super::*;
use std::os::unix::fs::DirBuilderExt;
use std::time::{SystemTime, UNIX_EPOCH};

pub(crate) struct CurrentOwnerProof {
    subject: String,
    public_key: String,
    epoch: String,
    evidence: Value,
}
impl CurrentOwnerProof {
    pub(crate) fn evidence(&self) -> Value {
        self.evidence.clone()
    }
    pub(crate) fn epoch(&self) -> &str {
        &self.epoch
    }
}
fn canonical_epoch(value: &str) -> bool {
    !value.is_empty()
        && value.bytes().all(|b| b.is_ascii_digit())
        && (value == "0" || !value.starts_with('0'))
}
pub(crate) fn observe(
    config: &Config,
    subject: &str,
    public_key: &str,
) -> Result<CurrentOwnerProof> {
    credentials::Owner::new(subject, public_key)?;
    let socket = config
        .host_socket
        .as_ref()
        .ok_or_else(|| credentials::refused("owner-status-needs-socket"))?;
    let pins = || -> Result<Value> {
        Ok(json!({
            "miniSha256":sha256_file(&config.mini)?, "hostSha256":sha256_file(&config.host)?,
            "configSha256":sha256_file(&config.host_config)?, "socket":socket,
        }))
    };
    let before = pins()?;
    let output = Command::new(&config.mini)
        .args(["key", "--action", "owner-status", "--host"])
        .arg(&config.host)
        .arg("--config")
        .arg(&config.host_config)
        .arg("--socket")
        .arg(socket)
        .args(["--subject", subject, "--public-key", public_key])
        .output()
        .map_err(|_| credentials::refused("owner-status-unavailable"))?;
    if !output.status.success() || output.stdout.len() > 16_384 {
        return Err(credentials::refused("owner-not-current"));
    }
    let view: Value = serde_json::from_slice(&output.stdout)
        .map_err(|_| credentials::refused("owner-status-unavailable"))?;
    let epoch = view["keyEpoch"]
        .as_str()
        .filter(|e| canonical_epoch(e))
        .ok_or_else(|| credentials::refused("owner-status-unavailable"))?;
    if view["type"] != "subject-key-status-v1"
        || view["subject"] != subject
        || view["publicKey"] != public_key
        || view["isCurrent"] != true
        || view["currentRevoked"] != false
        || before != pins()?
    {
        return Err(credentials::refused("owner-not-current"));
    }
    Ok(CurrentOwnerProof {
        subject: subject.into(),
        public_key: public_key.into(),
        epoch: epoch.into(),
        evidence: json!({"type":"native-owner-observation-v1", "subject":subject,
            "publicKey":public_key,"keyEpoch":epoch,"pins":before,
            "response":view,"responseSha256":sha256_bytes(&output.stdout)?,
            "meaning":"Current at this source read; re-observe before a later authority decision."}),
    })
}
/// Read-only migration preflight. Never creates a key/grant or consumes a call.
/// The height comes from a fresh signed query retained in the controller state.
/// The typed migration independently limits the config diff to this owner key.
pub(crate) fn grant_evidence(config: &Config, proof: &CurrentOwnerProof) -> Result<Value> {
    let task = config
        .provider_task
        .as_ref()
        .ok_or("provider task absent")?;
    let owner = task.on_behalf_of.as_ref().ok_or("provider owner absent")?;
    if owner.subject != proof.subject || owner.public_key != proof.public_key {
        return Err("current owner proof differs from target controller".into());
    }
    let (height, source) = source_height(config)?;
    let current = observe(config, &proof.subject, &proof.public_key)?;
    if current.epoch() != proof.epoch() {
        return Err("owner epoch changed during grant observation".into());
    }
    let table = credentials::ProviderTable::load(&task.providers, 0)?;
    let row = provider_task_row(task, &table)?;
    if row.credential != credentials::CredentialSource::User {
        return Err("owner key migration requires a member credential route".into());
    }
    let store = credentials::CredentialStore::open(&task.credentials_root, &task.credentials_key)?;
    let grant = store.verify_grant(
        &credentials::Owner::new(&proof.subject, &proof.public_key)?,
        &row.name,
        &task.subject,
        &task.model,
        &proof.epoch,
        height,
    )?;
    if grant.per_call < u64::from(task.max_output_tokens) {
        return Err(credentials::refused("per-call-cap"));
    }
    Ok(
        json!({"type":"member-provider-grant-observation-v1","subject":proof.subject,
        "publicKey":proof.public_key,"provider":row.name,"model":task.model,
        "tableSha256":table.sha256,"height":height.to_string(),"source":source,"grant":grant.to_json()}),
    )
}

fn source_height(config: &Config) -> Result<(u64, Value)> {
    let task = config
        .provider_task
        .as_ref()
        .ok_or("provider task absent")?;
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|_| "owner observation clock unavailable")?
        .as_nanos()
        .to_string();
    let dir = config.state_dir.join(format!("owner-observation-{nonce}"));
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&dir)
        .map_err(|_| "owner observation directory unavailable")?;
    let intent = dir.join("intent.json");
    let attempt = dir.join("attempt");
    let source = json!({"subject":task.subject,"nonce":nonce,
        "purpose":{"type":"query","kind":"object","target":task.task,"view":"resource"},
        "grants":[{"kind":"object","target":task.task,"capability":task.query_capability}]});
    write_new(&intent, &serde_json::to_vec(&source).unwrap())?;
    let output = Command::new(&config.mini)
        .arg("query")
        .arg("--host")
        .arg(&config.host)
        .arg("--config")
        .arg(&config.host_config)
        .arg("--socket")
        .arg(
            config
                .host_socket
                .as_ref()
                .ok_or("owner observation needs socket")?,
        )
        .arg("--intent")
        .arg(&intent)
        .arg("--key")
        .arg(&task.custody_key)
        .args(["--view", "resource"])
        .arg("--dir")
        .arg(&attempt)
        .output()
        .map_err(|_| "native owner resource observation unavailable")?;
    if !output.status.success() {
        return Err("native owner resource observation refused".into());
    }
    let read = |name: &str| -> Result<Value> {
        let bytes = fs::read(attempt.join(name))
            .map_err(|_| "native owner observation evidence missing")?;
        if bytes.len() > 1_048_576 {
            return Err("native owner observation evidence exceeds bound".into());
        }
        serde_json::from_slice(&bytes).map_err(|_| "invalid native owner observation".into())
    };
    let view = read("view.json")?;
    let challenge = read("challenge.json")?;
    if view.pointer("/cell/grain/task").and_then(Value::as_str) != Some(task.task.as_str()) {
        return Err("native owner resource observation names another task".into());
    }
    let height = challenge["height"]
        .as_str()
        .filter(|v| canonical_epoch(v))
        .ok_or("native owner resource observation has no canonical height")?
        .parse::<u64>()
        .map_err(|_| "native owner height exceeds u64")?;
    Ok((
        height,
        json!({"attempt":attempt,"challengeSha256":sha256_file(&attempt.join("challenge.json"))?,
        "viewSha256":sha256_file(&attempt.join("view.json"))?,"height":height.to_string(),
        "task":task.task,"worldRoot":challenge["worldRoot"]}),
    ))
}
