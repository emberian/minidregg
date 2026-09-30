//! Sponsor-backed admission of one new signing principal. The source Host
//! chooses both canonical signing bytes; Rust retains them, signs the sponsor
//! header and the distinct raw possession frame, and never resubmits an
//! uncertain ingress. An admitted key conveys no resource grant.
//!
//! A *home identity* enrollment admits a principal whose key and subject
//! number belong to another Store (a selected-release owner, for example).
//! The sponsor plans with only the public key and the explicit home subject;
//! the principal signs the Host-chosen possession header in its own process
//! (`--action possess`); the sponsor seals with that detached signature. No
//! process ever holds both secrets.
use crate::agent_reserve::{bounded, digest, field, private_bytes, private_socket};
use ed25519_dalek::{Verifier, VerifyingKey};
use crate::participant_namespace::{self, IdKind, Role};
use crate::*;
use serde_json::{json, Value};
use std::os::unix::fs::DirBuilderExt;

const FORMAT: &str = "minidregg-participant-enrollment-custody-v1";
const COMMAND_KIND: &str = "participant-key-enrollment";
const PLAN_KIND: &str = "participant-key-enrollment-plan";
const INGRESS_KIND: &str = "participant-key-enrollment-ingress";
const LIMIT: usize = transport::HOST_MAX_FRAME - 1;

fn json_private(path: &Path) -> Result<Value> {
    serde_json::from_slice(&private_bytes(path, 256 * 1024)?).map_err(|error| {
        format!(
            "invalid private enrollment JSON {}: {error}",
            path.display()
        )
    })
}

fn member_path(value: &Value, key: &str) -> Result<PathBuf> {
    let path = PathBuf::from(field(value, key)?);
    if !path.is_absolute() {
        return Err(format!("enrollment {key} must be absolute"));
    }
    Ok(path)
}

fn decimal(value: &str, label: &str) -> Result<()> {
    if value.is_empty()
        || value.len() > 80
        || value.starts_with('0') && value != "0"
        || !value.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err(format!("{label} must be canonical decimal"));
    }
    Ok(())
}

fn identity_name(value: &str) -> Result<()> {
    if value.is_empty()
        || value.len() > 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
    {
        return Err("enrollment name must contain 1..64 ASCII letters, digits or hyphens".into());
    }
    Ok(())
}

fn key(path: &Path) -> Result<SigningKey> {
    let mut bytes: [u8; 32] = private_bytes(path, 32)?
        .try_into()
        .map_err(|_| "enrollment key must contain exactly 32 raw bytes")?;
    let signing = SigningKey::from_bytes(&bytes);
    bytes.fill(0);
    Ok(signing)
}

fn nonce() -> Result<String> {
    let mut bytes = [0u8; 16];
    File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut bytes))
        .map_err(|error| format!("cannot obtain enrollment nonce: {error}"))?;
    Ok(u128::from_be_bytes(bytes).to_string())
}

fn pair(first: &[u8], second: &[u8]) -> Result<Vec<u8>> {
    let length: u32 = first
        .len()
        .try_into()
        .map_err(|_| "enrollment pair exceeds u32")?;
    let mut bytes = length.to_le_bytes().to_vec();
    bytes.extend_from_slice(first);
    bytes.extend_from_slice(second);
    if first.is_empty() || second.is_empty() || bytes.len() >= transport::HOST_MAX_FRAME {
        return Err("enrollment pair exceeds Host bound or has an empty component".into());
    }
    Ok(bytes)
}

fn reply(frame: &[u8], operation: u8) -> Result<&[u8]> {
    match frame {
        [255, ..] | [254, ..] => Err(format!(
            "enrollment Host refused op{operation}; exact frame retained"
        )),
        [actual, body @ ..] if *actual == operation && !body.is_empty() => Ok(body),
        _ => Err(format!(
            "enrollment op{operation} returned an invalid frame"
        )),
    }
}

fn save_json(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    create_private(path, &bytes)?;
    sync_directory_ancestors(path.parent().ok_or("enrollment file lacks parent")?)
}

fn retain_exact(path: &Path, bytes: &[u8]) -> Result<()> {
    if path.exists() {
        if bounded(path, LIMIT)? != bytes {
            return Err(format!(
                "retained enrollment source changed: {}",
                path.display()
            ));
        }
        return Ok(());
    }
    create_private(path, bytes)?;
    sync_directory_ancestors(path.parent().ok_or("enrollment file lacks parent")?)
}

fn save_json_staged(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    retain_exact(path, &bytes)
}

fn retained_request(directory: &Path, expected: &Value) -> Result<Value> {
    let path = directory.join("request.json");
    let request = if path.exists() {
        json_private(&path)?
    } else {
        if fs::read_dir(directory)
            .map_err(|error| error.to_string())?
            .filter_map(|entry| entry.ok())
            .any(|entry| entry.file_name() != "enrollment.lock")
        {
            return Err("enrollment attempt has artifacts but no durable request".into());
        }
        expected.clone()
    };
    for field_name in [
        "type",
        "name",
        "sponsor",
        "control",
        "factory",
        "observeCapability",
        "newPublicKey",
        "hostSha256",
        "configSha256",
    ] {
        pinned(&request, field_name, field(expected, field_name)?)?;
    }
    if request.get("homeSubject") != expected.get("homeSubject") {
        return Err("enrollment homeSubject pin changed".into());
    }
    decimal(field(&request, "nonce")?, "enrollment nonce")?;
    save_json_staged(&path, &request)?;
    Ok(request)
}

fn transform(
    host: &Path,
    socket: &Path,
    config: &Path,
    operation: u8,
    kind: Option<&str>,
    input: &Path,
    output: &Path,
) -> Result<()> {
    let input = bounded(input, LIMIT)?;
    let mut payload = Vec::new();
    if let Some(kind) = kind {
        let length: u16 = kind.len().try_into().map_err(|_| "Host kind too long")?;
        payload.extend_from_slice(&length.to_le_bytes());
        payload.extend_from_slice(kind.as_bytes());
    }
    payload.extend_from_slice(&input);
    let frame_path = output.with_file_name(format!(
        "{}.frame",
        output
            .file_name()
            .ok_or("enrollment output lacks file name")?
            .to_string_lossy()
    ));
    let frame = if frame_path.exists() {
        bounded(&frame_path, transport::HOST_MAX_FRAME)?
    } else {
        if output.exists() {
            return Err("enrollment output exists without its retained Host frame".into());
        }
        let frame = session_invoke(host, socket, config, operation, &payload)?;
        retain_exact(&frame_path, &frame)?;
        frame
    };
    let body = reply(&frame, operation)?;
    retain_exact(output, body)
}

fn inspect(
    host: &Path,
    socket: &Path,
    config: &Path,
    kind: &str,
    input: &Path,
    output: &Path,
) -> Result<Value> {
    transform(host, socket, config, 8, Some(kind), input, output)?;
    serde_json::from_slice(&bounded(output, 8 * transport::HOST_MAX_FRAME)?)
        .map_err(|error| format!("invalid enrollment Host inspection: {error}"))
}

fn retained_frame(directory: &Path, stem: &str, frame: &[u8], operation: u8) -> Result<Vec<u8>> {
    retain_exact(&directory.join(format!("{stem}.frame")), frame)?;
    let body = reply(frame, operation)?.to_vec();
    retain_exact(&directory.join(format!("{stem}.bin")), &body)?;
    Ok(body)
}

fn staged_invoke(
    host: &Path,
    socket: &Path,
    config: &Path,
    directory: &Path,
    stem: &str,
    operation: u8,
    payload: &[u8],
) -> Result<Vec<u8>> {
    let frame_path = directory.join(format!("{stem}.frame"));
    let frame = if frame_path.exists() {
        let retained = bounded(&frame_path, transport::HOST_MAX_FRAME)?;
        if operation == 86 {
            let current =
                session_invoke(host, socket, config, operation, payload).map_err(|error| {
                    format!("retained enrollment plan is stale; start a new request with a new --name label: {error}")
                })?;
            if current != retained {
                return Err("retained enrollment plan differs from current source image; start a new request with a new --name label".into());
            }
        }
        retained
    } else {
        if directory.join(format!("{stem}.bin")).exists() {
            return Err("enrollment body exists without its retained Host frame".into());
        }
        session_invoke(host, socket, config, operation, payload)?
    };
    retained_frame(directory, stem, &frame, operation)
}

fn pinned(value: &Value, key: &str, expected: &str) -> Result<()> {
    if field(value, key)? != expected {
        return Err(format!("enrollment {key} pin changed"));
    }
    Ok(())
}

struct Pin {
    host: PathBuf,
    config: PathBuf,
    public_socket: PathBuf,
    operation_socket: PathBuf,
    sponsor_key: PathBuf,
    /// `None` for a home-identity enrollment: the new secret never enters
    /// this process and possession arrives as a detached signature.
    new_key: Option<PathBuf>,
    subject: String,
    key_id: String,
    public_key: String,
    plan: Vec<u8>,
    command: Vec<u8>,
}

/// A home identity keeps its origin subject number, so only the Store-local
/// key id is reserved; the Host still refuses any subject already present.
fn enrollment_roles(home: bool) -> Vec<Role> {
    let mut roles = Vec::new();
    if !home {
        roles.push(Role {
            label: "subject".into(),
            kind: IdKind::Subject,
        });
    }
    roles.push(Role {
        label: "keyId".into(),
        kind: IdKind::Key,
    });
    roles
}

fn public_key_file(path: &Path) -> Result<VerifyingKey> {
    let bytes: [u8; 32] = bounded(path, 32)?
        .try_into()
        .map_err(|_| "enrollment public key must contain exactly 32 raw bytes")?;
    VerifyingKey::from_bytes(&bytes).map_err(|_| "enrollment public key is not a valid Ed25519 point".into())
}

fn load_pin(directory: &Path) -> Result<Pin> {
    drain::private_dir(directory)?;
    let pin = json_private(&directory.join("pin.json"))?;
    pinned(&pin, "format", FORMAT)?;
    let host = member_path(&pin, "host")?;
    let config = member_path(&pin, "config")?;
    let public_socket = member_path(&pin, "publicSocket")?;
    let operation_socket = member_path(&pin, "operationSocket")?;
    let sponsor_key = member_path(&pin, "sponsorKey")?;
    let home = pin.get("homeSubject").and_then(Value::as_bool) == Some(true);
    let new_key = if home {
        if !pin.get("newKey").is_some_and(Value::is_null) {
            return Err("home-identity enrollment pin must not name a new secret key".into());
        }
        None
    } else {
        Some(member_path(&pin, "newKey")?)
    };
    let namespace_root = member_path(&pin, "namespaceRoot")?;
    if pin.get("operatorOnly").and_then(Value::as_bool) == Some(true) {
        private_socket(&operation_socket)?;
    } else if operation_socket != public_socket {
        return Err("public enrollment operation socket differs from sponsor workspace".into());
    }
    pinned(&pin, "hostSha256", &host_image_sha256(&host)?)?;
    pinned(&pin, "configSha256", &digest(&bounded(&config, 65_536)?))?;
    let request_bytes = private_bytes(&directory.join("request.json"), 256 * 1024)?;
    pinned(&pin, "requestSha256", &digest(&request_bytes))?;
    let request: Value =
        serde_json::from_slice(&request_bytes).map_err(|error| error.to_string())?;
    pinned(&request, "hostSha256", field(&pin, "hostSha256")?)?;
    pinned(&request, "configSha256", field(&pin, "configSha256")?)?;
    let command = private_bytes(&directory.join("command.bin"), LIMIT)?;
    let plan = private_bytes(&directory.join("plan.bin"), LIMIT)?;
    pinned(&pin, "commandSha256", &digest(&command))?;
    pinned(&pin, "planSha256", &digest(&plan))?;
    let name = field(&pin, "name")?;
    let sponsor = field(&pin, "sponsor")?;
    let subject = field(&pin, "subject")?.to_owned();
    let key_id = field(&pin, "keyId")?.to_owned();
    let public_key = field(&pin, "publicKey")?.to_owned();
    if field(&request, "name")? != name
        || field(&request, "sponsor")? != sponsor
        || field(&request, "newPublicKey")? != public_key
    {
        return Err("enrollment request changed after namespace reservation".into());
    }
    let config_json: Value =
        serde_json::from_slice(&bounded(&config, 65_536)?).map_err(|error| error.to_string())?;
    let domain = config_json
        .get("domain")
        .and_then(|value| {
            value
                .as_str()
                .map(str::to_owned)
                .or_else(|| value.as_u64().map(|number| number.to_string()))
        })
        .ok_or("enrollment config lacks deployment domain")?;
    let roles = enrollment_roles(home);
    let reservation = participant_namespace::reserve(
        &namespace_root,
        &domain,
        sponsor,
        name,
        &request_bytes,
        &roles,
    )?;
    pinned(&pin, "reservationDigest", &reservation.request_digest)?;
    let reserved_subject = if home {
        field(&request, "homeSubject")?
    } else {
        reservation.ids["subject"].as_str()
    };
    if reserved_subject != subject
        || reservation.ids["keyId"] != key_id
        || member_path(&pin, "reservationRecord")? != reservation.record_path
    {
        return Err("enrollment namespace reservation changed".into());
    }
    participant_namespace::bind_attempt(&reservation, directory, &digest(&command))?;
    Ok(Pin {
        host,
        config,
        public_socket,
        operation_socket,
        sponsor_key,
        new_key,
        subject,
        key_id,
        public_key,
        plan,
        command,
    })
}

fn plan(mut args: Args) -> Result<()> {
    let workspace = absolute(&path(args.required("sponsor-workspace")?))?;
    let factory_name = args
        .required("factory-ref")?
        .into_string()
        .map_err(|_| "factory reference name must be UTF-8")?;
    let name = args
        .required("name")?
        .into_string()
        .map_err(|_| "enrollment name must be UTF-8")?;
    let new_key = args
        .optional("new-key")
        .map(|value| absolute(&path(value)))
        .transpose()?;
    let new_public = args
        .optional("new-public-key")
        .map(|value| absolute(&path(value)))
        .transpose()?;
    let home_subject = args
        .optional("home-subject")
        .map(|value| {
            value
                .into_string()
                .map_err(|_| "home subject must be UTF-8".to_owned())
        })
        .transpose()?;
    let home = match (&new_key, &new_public, &home_subject) {
        (Some(_), None, None) => false,
        (None, Some(_), Some(subject)) => {
            decimal(subject, "home subject")?;
            true
        }
        _ => {
            return Err(
                "enrollment takes either --new-key, or --new-public-key with --home-subject".into(),
            )
        }
    };
    let operator_override = args
        .optional("operator-socket")
        .map(path)
        .map(|value| absolute(&value))
        .transpose()?;
    let directory = absolute(&path(args.required("dir")?))?;
    args.finish()?;
    identity_name(&factory_name)?;
    identity_name(&name)?;
    let workspace_pin = json_private(&workspace.join("workspace.json"))?;
    pinned(&workspace_pin, "type", "minidregg-participant-workspace-v1")?;
    let factory = json_private(&workspace.join("refs").join(format!("{factory_name}.json")))?;
    pinned(&factory, "type", "minidregg-participant-reference-v1")?;
    pinned(&factory, "name", &factory_name)?;
    pinned(&factory, "kind", "object")?;
    let host = member_path(&workspace_pin, "host")?;
    let config = member_path(&workspace_pin, "config")?;
    let public_socket = member_path(&workspace_pin, "socket")?;
    let sponsor_key = member_path(&workspace_pin, "key")?;
    let namespace_root = member_path(&workspace_pin, "namespaceRoot")?;
    let operation_socket = operator_override
        .clone()
        .unwrap_or_else(|| public_socket.clone());
    if operator_override.is_some() {
        private_socket(&operation_socket)?;
    }
    let sponsor = field(&workspace_pin, "subject")?.to_owned();
    let control = field(&factory, "controlCapability")?.to_owned();
    let observe = field(&factory, "observeCapability")?.to_owned();
    let factory_target = field(&factory, "target")?.to_owned();
    for (value, label) in [
        (&sponsor, "sponsor"),
        (&control, "factory control capability"),
        (&observe, "factory observe capability"),
        (&factory_target, "factory target"),
    ] {
        decimal(value, label)?;
    }
    let config_bytes = bounded(&config, 65_536)?;
    let config_json: Value =
        serde_json::from_slice(&config_bytes).map_err(|error| error.to_string())?;
    let deployed_factory = config_json
        .get("factoryId")
        .and_then(|value| {
            value
                .as_str()
                .map(str::to_owned)
                .or_else(|| value.as_u64().map(|number| number.to_string()))
        })
        .ok_or("deployed config lacks factoryId")?;
    let deployment_domain = config_json
        .get("domain")
        .and_then(|value| {
            value
                .as_str()
                .map(str::to_owned)
                .or_else(|| value.as_u64().map(|number| number.to_string()))
        })
        .ok_or("deployed config lacks domain")?;
    if factory_target != deployed_factory {
        return Err("factory reference differs from deployed factory".into());
    }
    let sponsor_signing = key(&sponsor_key)?;
    let public_key = match (&new_key, &new_public) {
        (Some(secret), _) => hex(&key(secret)?.verifying_key().to_bytes()),
        (None, Some(public)) => hex(&public_key_file(public)?.to_bytes()),
        _ => unreachable!("enrollment key inputs validated above"),
    };
    if public_key == hex(&sponsor_signing.verifying_key().to_bytes()) {
        return Err("enrolled key must differ from the sponsor key".into());
    }
    match fs::DirBuilder::new().mode(0o700).create(&directory) {
        Ok(()) => (),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            drain::private_dir(&directory)?;
        }
        Err(error) => return Err(format!("cannot create enrollment attempt: {error}")),
    }
    sync_directory_ancestors(&directory)?;
    let _lock = transport::service_lock(&directory.join("enrollment.lock"))?;
    if directory.join("submit-marker.json").exists() {
        return Err(
            "enrollment may have been submitted; use --action lookup with this exact --dir".into(),
        );
    }
    if directory.join("seal.json").exists() || directory.join("ingress.bin").exists() {
        return Err(
            "enrollment already sealed; use --action submit or lookup with this exact --dir".into(),
        );
    }
    let request_nonce = if directory.join("request.json").exists() {
        field(&json_private(&directory.join("request.json"))?, "nonce")?.to_owned()
    } else {
        nonce()?
    };
    let mut expected_request = json!({"type":"minidregg-participant-enrollment-request-v1",
        "name":name,"sponsor":sponsor,"control":control,"factory":factory_target,
        "observeCapability":observe,"newPublicKey":public_key,
        "nonce":request_nonce,"hostSha256":host_image_sha256(&host)?,
        "configSha256":digest(&config_bytes)});
    if let Some(subject) = &home_subject {
        if *subject == sponsor {
            return Err("home subject equals the sponsor subject".into());
        }
        expected_request["homeSubject"] = json!(subject);
    }
    let request = retained_request(&directory, &expected_request)?;
    let roles = enrollment_roles(home);
    let request_bytes = private_bytes(&directory.join("request.json"), 256 * 1024)?;
    let reservation = participant_namespace::reserve(
        &namespace_root,
        &deployment_domain,
        &sponsor,
        &name,
        &request_bytes,
        &roles,
    )?;
    let subject = match &home_subject {
        Some(subject) => subject.clone(),
        None => reservation.ids["subject"].clone(),
    };
    retain_exact(&directory.join("config.json"), &config_bytes)?;
    let retained_config = directory.join("config.json");
    let query = json!({"subject":sponsor,"nonce":field(&request,"nonce")?,
        "purpose":{"type":"query","kind":"object","target":factory_target,"view":"resource"},
        "grants":[{"kind":"object","target":factory_target,"capability":observe}]});
    save_json_staged(&directory.join("query.json"), &query)?;
    transform(
        &host,
        &public_socket,
        &retained_config,
        7,
        Some("intent"),
        &directory.join("query.json"),
        &directory.join("query.bin"),
    )?;
    let query_bytes = private_bytes(&directory.join("query.bin"), LIMIT)?;
    let observation = directory.join("observation");
    match fs::DirBuilder::new().mode(0o700).create(&observation) {
        Ok(()) => (),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            drain::private_dir(&observation)?;
        }
        Err(error) => return Err(format!("cannot create enrollment observation: {error}")),
    }
    let challenge = staged_invoke(
        &host,
        &public_socket,
        &retained_config,
        &observation,
        "challenge",
        4,
        &query_bytes,
    )?;
    let challenge_json = inspect(
        &host,
        &public_socket,
        &retained_config,
        "challenge",
        &observation.join("challenge.bin"),
        &observation.join("challenge.json"),
    )?;
    let headers = challenge_headers(&challenge_json)?;
    if headers.is_empty() {
        return Err("factory observation has no signing header".into());
    }
    let signatures = sign_headers(&sponsor_signing, &headers);
    save_json_staged(&observation.join("signatures.json"), &signatures)?;
    transform(
        &host,
        &public_socket,
        &retained_config,
        9,
        None,
        &observation.join("signatures.json"),
        &observation.join("signatures.bin"),
    )?;
    let signature_bytes = private_bytes(&observation.join("signatures.bin"), 4096)?;
    let signed = staged_invoke(
        &host,
        &public_socket,
        &retained_config,
        &observation,
        "signed-observation",
        10,
        &pair(&challenge, &signature_bytes)?,
    )?;
    let _view = staged_invoke(
        &host,
        &public_socket,
        &retained_config,
        &observation,
        "view",
        5,
        &signed,
    )?;
    let view_json = inspect(
        &host,
        &public_socket,
        &retained_config,
        "view-resource",
        &observation.join("view.bin"),
        &observation.join("view.json"),
    )?;
    pinned(&view_json, "type", "resource")?;
    let factory_root = view_json
        .get("page")
        .and_then(|page| page.get("root"))
        .and_then(Value::as_str)
        .ok_or("signed factory view lacks root")?;
    decimal(factory_root, "factory root")?;
    let authority_root = challenge_json
        .get("signing")
        .and_then(Value::as_array)
        .and_then(|items| items.first())
        .and_then(|first| first.get("authorityRoot"))
        .and_then(Value::as_str)
        .ok_or("signed factory challenge lacks authority root")?;
    decimal(authority_root, "authority root")?;
    let command_source = json!({"sponsor":sponsor,"control":control,
        "nonce":field(&request,"nonce")?,"expectedFactoryRoot":factory_root,
        "expectedAuthorityRoot":authority_root,
        "key":{"keyId":reservation.ids["keyId"],"keyEpoch":"1","algorithm":"1",
            "subject":subject,"publicKey":public_key,
            "activeFrom":"0","activeUntil":u64::MAX.to_string(),"revoked":false}});
    save_json_staged(&directory.join("source.json"), &command_source)?;
    transform(
        &host,
        &public_socket,
        &retained_config,
        7,
        Some(COMMAND_KIND),
        &directory.join("source.json"),
        &directory.join("command.bin"),
    )?;
    let command = private_bytes(&directory.join("command.bin"), LIMIT)?;
    let command_view = inspect(
        &host,
        &public_socket,
        &retained_config,
        COMMAND_KIND,
        &directory.join("command.bin"),
        &directory.join("command.json"),
    )?;
    if field(&command_view, "type")? != "participant-key-enrollment-v1"
        || field(&command_view, "canonical")? != hex(&command)
        || command_view.get("key") != Some(&command_source["key"])
    {
        return Err("enrollment canonical command differs from reserved source".into());
    }
    let plan = staged_invoke(
        &host,
        &operation_socket,
        &retained_config,
        &directory,
        "plan",
        86,
        &pair(&signed, &command)?,
    )?;
    let plan_view = inspect(
        &host,
        &public_socket,
        &retained_config,
        PLAN_KIND,
        &directory.join("plan.bin"),
        &directory.join("plan.json"),
    )?;
    validate_plan(&plan_view, &command, &plan)?;
    pinned(&request, "hostSha256", &host_image_sha256(&host)?)?;
    pinned(
        &request,
        "configSha256",
        &digest(&bounded(&config, 65_536)?),
    )?;
    let command_sha = digest(&command);
    participant_namespace::bind_attempt(&reservation, &directory, &command_sha)?;
    save_json_staged(
        &directory.join("pin.json"),
        &json!({"format":FORMAT,
        "host":host,"hostSha256":host_image_sha256(&host)?,
        "config":retained_config,"configSha256":digest(&config_bytes),
        "publicSocket":public_socket,"operationSocket":operation_socket,
        "operatorOnly":operator_override.is_some(),
        "sponsorKey":sponsor_key,"newKey":new_key,"homeSubject":home,"namespaceRoot":namespace_root,
        "name":name,"sponsor":sponsor,"subject":subject,
        "keyId":reservation.ids["keyId"],"publicKey":public_key,
        "requestSha256":digest(&request_bytes),"commandSha256":command_sha,
        "planSha256":digest(&plan),"reservationDigest":reservation.request_digest,
        "reservationRecord":reservation.record_path}),
    )?;
    print_json(
        &json!({"type":"minidregg-participant-enrollment-plan-custody-v1",
        "subject":subject,"keyId":reservation.ids["keyId"],
        "publicKey":public_key,"plan":plan_view,"authority":"candidate-only"}),
    )
}

fn validate_plan(view: &Value, command: &[u8], plan: &[u8]) -> Result<()> {
    if field(view, "type")? != "participant-key-enrollment-plan-v1"
        || field(view, "canonical")? != hex(plan)
        || field(view, "commandBytes")? != hex(command)
        || view
            .get("sponsorHeader")
            .and_then(|header| header.get("decoded"))
            != Some(&Value::Bool(true))
        || view
            .get("sponsorHeader")
            .and_then(|header| header.get("canonical"))
            .and_then(Value::as_str)
            .is_none_or(str::is_empty)
        || view
            .get("possessionHeader")
            .and_then(Value::as_str)
            .is_none_or(str::is_empty)
    {
        return Err("enrollment Plan differs from canonical command or signing headers".into());
    }
    Ok(())
}

/// Run by the enrolled principal, in its own process, over the sponsor's
/// retained Plan and canonical command inspection. It signs only the Host's
/// possession header, and only when the command names this key at the
/// expected home subject. The sponsor's secret is never read.
fn possess(mut args: Args) -> Result<()> {
    let directory = absolute(&path(args.required("dir")?))?;
    let key_path = absolute(&path(args.required("key")?))?;
    let subject = args
        .required("subject")?
        .into_string()
        .map_err(|_| "home subject must be UTF-8")?;
    let output = absolute(&path(args.required("output")?))?;
    args.finish()?;
    print_json(&possess_at(&directory, &key_path, &subject, &output)?)
}

fn possess_at(directory: &Path, key_path: &Path, subject: &str, output: &Path) -> Result<Value> {
    let signing = key(key_path)?;
    decimal(subject, "home subject")?;
    if output.exists() {
        return Err("possession signature output already exists".into());
    }
    let plan_view: Value = serde_json::from_slice(&bounded(&directory.join("plan.json"), 8 * transport::HOST_MAX_FRAME)?)
        .map_err(|error| format!("invalid enrollment Plan inspection: {error}"))?;
    let command_view: Value = serde_json::from_slice(&bounded(&directory.join("command.json"), 8 * transport::HOST_MAX_FRAME)?)
        .map_err(|error| format!("invalid enrollment command inspection: {error}"))?;
    let public_key = hex(&signing.verifying_key().to_bytes());
    let key_record = command_view.get("key").ok_or("enrollment command names no key")?;
    if field(&command_view, "type")? != "participant-key-enrollment-v1"
        || field(&plan_view, "type")? != "participant-key-enrollment-plan-v1"
        || field(&plan_view, "commandBytes")? != field(&command_view, "canonical")?
        || field(key_record, "publicKey")? != public_key
        || field(key_record, "subject")? != subject
        || key_record.get("revoked") != Some(&Value::Bool(false))
    {
        return Err("enrollment Plan does not name this key at the expected home subject".into());
    }
    let header = decode_hex(field(&plan_view, "possessionHeader")?)?;
    let signature = signing.sign(&header).to_bytes();
    create_private(output, &signature)?;
    sync_directory_ancestors(output.parent().ok_or("possession output lacks parent")?)?;
    Ok(json!({"type":"minidregg-participant-possession-signature-v1",
        "subject":subject,"publicKey":public_key,
        "commandSha256":digest(&decode_hex(field(&command_view, "canonical")?)?),
        "possessionHeaderSha256":digest(&header),"signatureSha256":digest(&signature)}))
}

fn seal(directory: &Path, detached: Option<&Path>) -> Result<()> {
    let directory = absolute(directory)?;
    let _lock = transport::service_lock(&directory.join("enrollment.lock"))?;
    if directory.join("submit-marker.json").exists() {
        return Err(
            "enrollment may have been submitted; use --action lookup with this exact --dir".into(),
        );
    }
    let pin = load_pin(&directory)?;
    match (&pin.new_key, detached) {
        (Some(new_key), None) => {
            if hex(&key(new_key)?.verifying_key().to_bytes()) != pin.public_key {
                return Err("new enrollment key changed after plan".into());
            }
        }
        (None, Some(_)) => (),
        (Some(_), Some(_)) => {
            return Err("a local-key enrollment signs its own possession header".into())
        }
        (None, None) => {
            return Err("home-identity enrollment requires --possession-signature".into())
        }
    }
    let plan_view = json_private(&directory.join("plan.json"))?;
    validate_plan(&plan_view, &pin.command, &pin.plan)?;
    let fresh = inspect(
        &pin.host,
        &pin.public_socket,
        &pin.config,
        PLAN_KIND,
        &directory.join("plan.bin"),
        &directory.join("seal-plan.json"),
    )?;
    if fresh != plan_view {
        return Err("enrollment Plan inspection changed before signing".into());
    }
    let sponsor_header = decode_hex(field(&plan_view["sponsorHeader"], "canonical")?)?;
    let possession_header = decode_hex(field(&plan_view, "possessionHeader")?)?;
    let sponsor = key(&pin.sponsor_key)?;
    let sponsor_signature = sponsor.sign(&sponsor_header).to_bytes();
    let possession_signature: [u8; 64] = match (&pin.new_key, detached) {
        (Some(new_key), _) => key(new_key)?.sign(&possession_header).to_bytes(),
        (None, Some(file)) => {
            let bytes: [u8; 64] = bounded(&absolute(file)?, 64)?
                .try_into()
                .map_err(|_| "possession signature must contain exactly 64 bytes")?;
            let public: [u8; 32] = decode_hex(&pin.public_key)?
                .try_into()
                .map_err(|_| "pinned enrollment public key is not 32 bytes")?;
            VerifyingKey::from_bytes(&public)
                .map_err(|_| "pinned enrollment public key is invalid")?
                .verify(
                    &possession_header,
                    &ed25519_dalek::Signature::from_bytes(&bytes),
                )
                .map_err(|_| "detached possession signature does not verify for the pinned key")?;
            bytes
        }
        (None, None) => unreachable!("detached input checked above"),
    };
    retain_exact(&directory.join("sponsor-signature.bin"), &sponsor_signature)?;
    retain_exact(
        &directory.join("possession-signature.bin"),
        &possession_signature,
    )?;
    let signatures = pair(&sponsor_signature, &possession_signature)?;
    let assembly = pair(&pin.plan, &signatures)?;
    let ingress = staged_invoke(
        &pin.host,
        &pin.operation_socket,
        &pin.config,
        &directory,
        "ingress",
        87,
        &assembly,
    )?;
    let view = inspect(
        &pin.host,
        &pin.public_socket,
        &pin.config,
        INGRESS_KIND,
        &directory.join("ingress.bin"),
        &directory.join("ingress.json"),
    )?;
    if field(&view, "type")? != "participant-key-enrollment-ingress-v1"
        || field(&view, "canonical")? != hex(&ingress)
        || field(&view, "commandBytes")? != hex(&pin.command)
        || field(&view, "possessionSignature")? != hex(&possession_signature)
        || field(&view, "possessionSignatureLength")? != "64"
    {
        return Err("enrollment assembled ingress differs from signed exact Plan".into());
    }
    save_json_staged(
        &directory.join("seal.json"),
        &json!({"format":FORMAT,
        "planSha256":digest(&pin.plan),"commandSha256":digest(&pin.command),
        "ingressSha256":digest(&ingress),"sponsorSignatureSha256":digest(&sponsor_signature),
        "possessionSignatureSha256":digest(&possession_signature)}),
    )?;
    print_json(&json!({"type":"minidregg-participant-enrollment-sealed-v1",
        "subject":pin.subject,"keyId":pin.key_id,"ingressSha256":digest(&ingress),
        "authority":"awaiting-admission"}))
}

fn sealed(directory: &Path) -> Result<(Pin, Vec<u8>)> {
    let pin = load_pin(directory)?;
    let seal = json_private(&directory.join("seal.json"))?;
    pinned(&seal, "format", FORMAT)?;
    pinned(&seal, "planSha256", &digest(&pin.plan))?;
    pinned(&seal, "commandSha256", &digest(&pin.command))?;
    let ingress = private_bytes(&directory.join("ingress.bin"), LIMIT)?;
    pinned(&seal, "ingressSha256", &digest(&ingress))?;
    let assembly = private_bytes(&directory.join("ingress.frame"), transport::HOST_MAX_FRAME)?;
    if assembly != [vec![87], ingress.clone()].concat() {
        return Err("retained enrollment ingress differs from exact Host assembly".into());
    }
    let view = json_private(&directory.join("ingress.json"))?;
    if field(&view, "canonical")? != hex(&ingress)
        || field(&view, "commandBytes")? != hex(&pin.command)
    {
        return Err("retained enrollment ingress inspection changed".into());
    }
    Ok((pin, ingress))
}

fn outcome(directory: &Path, pin: &Pin, stem: &str, frame: &[u8], operation: u8) -> Result<Value> {
    let _body = retained_frame(directory, stem, frame, operation)?;
    let value = inspect(
        &pin.host,
        &pin.public_socket,
        &pin.config,
        "outcome",
        &directory.join(format!("{stem}.bin")),
        &directory.join(format!("{stem}.json")),
    )?;
    Ok(value)
}

fn confirmed(value: &Value) -> Result<()> {
    if field(value, "type")? != "confirmed"
        || !matches!(field(value, "confirmation")?, "installed" | "replayed")
    {
        return Err("enrollment outcome is not a confirmed admitted key".into());
    }
    for field_name in ["transactionId", "eventId", "acceptedCount", "imageBoundary"] {
        decimal(field(value, field_name)?, field_name)?;
    }
    Ok(())
}

fn result(directory: &Path, pin: &Pin, receipt: &Value) -> Result<()> {
    confirmed(receipt)?;
    let path = directory.join("enrollment.json");
    let stable_receipt = json!({
        "transactionId":field(receipt,"transactionId")?,
        "eventId":field(receipt,"eventId")?,
        "acceptedCount":field(receipt,"acceptedCount")?,
        "imageBoundary":field(receipt,"imageBoundary")?
    });
    let value = json!({"type":"minidregg-participant-enrollment-result-v1",
        "subject":pin.subject,"keyId":pin.key_id,"publicKey":pin.public_key,
        "keyPath":pin.new_key,"receipt":stable_receipt,"authority":"admitted-key-only"});
    if path.exists() {
        if json_private(&path)? != value {
            return Err("prior admitted enrollment result differs from exact receipt".into());
        }
    } else {
        save_json(&path, &value)?;
    }
    print_json(&value)
}

fn lookup_exact(directory: &Path, pin: &Pin, ingress: &[u8]) -> Result<()> {
    let stem = format!(
        "lookup-{:04}",
        fs::read_dir(directory)
            .map_err(|error| error.to_string())?
            .filter_map(|entry| entry.ok())
            .filter(
                |entry| entry.file_name().to_string_lossy().starts_with("lookup-")
                    && entry.file_name().to_string_lossy().ends_with(".frame")
            )
            .count()
    );
    let frame = session_invoke(&pin.host, &pin.operation_socket, &pin.config, 89, ingress)?;
    let value = outcome(directory, pin, &stem, &frame, 89)?;
    confirmed(&value)?;
    result(directory, pin, &value)
}

fn submit(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let _lock = transport::service_lock(&directory.join("enrollment.lock"))?;
    let (pin, ingress) = sealed(&directory)?;
    if pin.operation_socket != pin.public_socket {
        private_socket(&pin.operation_socket)?;
    }
    let marker = directory.join("submit-marker.json");
    if marker.exists() {
        let prior = json_private(&marker)?;
        pinned(&prior, "ingressSha256", &digest(&ingress))?;
        return lookup_exact(&directory, &pin, &ingress);
    }
    save_json(
        &marker,
        &json!({"format":FORMAT,"operation":88,
        "ingressSha256":digest(&ingress),"status":"may-have-submitted"}),
    )?;
    match session_invoke(&pin.host, &pin.operation_socket, &pin.config, 88, &ingress) {
        Ok(frame) => {
            let value = outcome(&directory, &pin, "submit", &frame, 88)?;
            if confirmed(&value).is_ok() {
                return result(&directory, &pin, &value);
            }
            lookup_exact(&directory, &pin, &ingress)
        }
        Err(_) => lookup_exact(&directory, &pin, &ingress),
    }
}

fn lookup(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let _lock = transport::service_lock(&directory.join("enrollment.lock"))?;
    let (pin, ingress) = sealed(&directory)?;
    if !directory.join("submit-marker.json").exists() {
        return Err("enrollment has no submitted or uncertain attempt".into());
    }
    lookup_exact(&directory, &pin, &ingress)
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args
        .required("action")?
        .into_string()
        .map_err(|_| "enrollment action must be UTF-8")?;
    match action.as_str() {
        "plan" => plan(args),
        "possess" => possess(args),
        "seal" => {
            let directory = path(args.required("dir")?);
            let detached = args.optional("possession-signature").map(path);
            args.finish()?;
            seal(&directory, detached.as_deref())
        }
        "submit" | "lookup" => {
            let directory = path(args.required("dir")?);
            args.finish()?;
            match action.as_str() {
                "submit" => submit(&directory),
                _ => lookup(&directory),
            }
        }
        _ => Err("enrollment action must be plan, possess, seal, submit or lookup".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scratch(label: &str) -> PathBuf {
        let root = std::env::temp_dir().join(format!(
            "mini-enrollment-{label}-{}-{}",
            std::process::id(),
            nonce().unwrap()
        ));
        fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
        root
    }

    #[test]
    fn possession_signs_only_its_own_key_at_the_named_home_subject() {
        let root = scratch("possess");
        let secret = [7u8; 32];
        create_private(&root.join("owner.key"), &secret).unwrap();
        let other = [9u8; 32];
        create_private(&root.join("other.key"), &other).unwrap();
        let public = hex(&SigningKey::from_bytes(&secret).verifying_key().to_bytes());
        save_json(
            &root.join("command.json"),
            &json!({"type":"participant-key-enrollment-v1","canonical":"abcd",
                "key":{"subject":"7","publicKey":public,"revoked":false}}),
        )
        .unwrap();
        save_json(
            &root.join("plan.json"),
            &json!({"type":"participant-key-enrollment-plan-v1","commandBytes":"abcd",
                "possessionHeader":"0102"}),
        )
        .unwrap();
        let wrong_subject = possess_at(&root, &root.join("owner.key"), "8", &root.join("a.sig"));
        assert!(wrong_subject.unwrap_err().contains("does not name this key"));
        let wrong_key = possess_at(&root, &root.join("other.key"), "7", &root.join("b.sig"));
        assert!(wrong_key.unwrap_err().contains("does not name this key"));
        assert!(!root.join("a.sig").exists() && !root.join("b.sig").exists());
        possess_at(&root, &root.join("owner.key"), "7", &root.join("c.sig")).unwrap();
        let signature: [u8; 64] = fs::read(root.join("c.sig")).unwrap().try_into().unwrap();
        SigningKey::from_bytes(&secret)
            .verifying_key()
            .verify(&[1, 2], &ed25519_dalek::Signature::from_bytes(&signature))
            .unwrap();
        assert!(possess_at(&root, &root.join("owner.key"), "7", &root.join("c.sig")).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn home_identity_reserves_only_a_key_id() {
        assert_eq!(enrollment_roles(true).len(), 1);
        assert_eq!(enrollment_roles(true)[0].label, "keyId");
        assert_eq!(enrollment_roles(false).len(), 2);
    }

    #[test]
    fn empty_attempt_then_retained_request_recovers_without_changing_nonce() {
        let root = scratch("request-retry");
        let first = json!({"type":"minidregg-participant-enrollment-request-v1",
            "name":"bob","sponsor":"1","control":"2","factory":"3",
            "observeCapability":"4","newPublicKey":"abc","hostSha256":"h",
            "configSha256":"c","nonce":"123"});
        assert_eq!(retained_request(&root, &first).unwrap(), first);
        let mut retry = first.clone();
        retry["nonce"] = json!("456");
        assert_eq!(retained_request(&root, &retry).unwrap()["nonce"], "123");
        retry["control"] = json!("5");
        assert!(retained_request(&root, &retry).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn orphaned_artifact_without_request_cannot_pick_new_nonce() {
        let root = scratch("orphan-retry");
        retain_exact(&root.join("source.json"), b"stale").unwrap();
        let request = json!({"type":"minidregg-participant-enrollment-request-v1",
            "name":"bob","sponsor":"1","control":"2","factory":"3",
            "observeCapability":"4","newPublicKey":"abc","hostSha256":"h",
            "configSha256":"c","nonce":"123"});
        assert!(retained_request(&root, &request).is_err());
        assert!(!root.join("request.json").exists());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn crash_after_host_frame_recovers_exact_body_without_socket_call() {
        let root = scratch("frame-retry");
        retain_exact(&root.join("challenge.frame"), &[4, 9, 8]).unwrap();
        let body = staged_invoke(
            Path::new("/missing-host"),
            Path::new("/missing-socket"),
            Path::new("/missing-config"),
            &root,
            "challenge",
            4,
            b"query",
        )
        .unwrap();
        assert_eq!(body, [9, 8]);
        assert_eq!(bounded(&root.join("challenge.bin"), LIMIT).unwrap(), [9, 8]);
        assert!(retain_exact(&root.join("challenge.bin"), &[9, 7]).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn retained_pin_replays_identically_and_refuses_rebinding() {
        let root = scratch("pin-retry");
        let pin = json!({"format":FORMAT,"subject":"9","planSha256":"a"});
        save_json_staged(&root.join("pin.json"), &pin).unwrap();
        save_json_staged(&root.join("pin.json"), &pin).unwrap();
        assert!(save_json_staged(
            &root.join("pin.json"),
            &json!({"format":FORMAT,"subject":"10","planSha256":"a"})
        )
        .is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn raw_possession_and_sponsor_headers_remain_distinct() {
        let sponsor = SigningKey::from_bytes(&[7; 32]);
        let new = SigningKey::from_bytes(&[8; 32]);
        let canonical = [1u8, 2, 3];
        let raw = [4u8, 5, 6];
        assert_ne!(
            sponsor.sign(&canonical).to_bytes(),
            new.sign(&raw).to_bytes()
        );
        let inner = pair(
            &sponsor.sign(&canonical).to_bytes(),
            &new.sign(&raw).to_bytes(),
        )
        .unwrap();
        assert_eq!(u32::from_le_bytes(inner[..4].try_into().unwrap()), 64);
        assert_eq!(inner.len(), 4 + 64 + 64);
    }

    #[test]
    fn candidate_or_rejected_result_never_claims_admitted_key() {
        assert!(confirmed(&json!({"type":"rejected","confirmation":"installed"})).is_err());
        assert!(confirmed(&json!({"type":"confirmed","confirmation":"absent"})).is_err());
        assert!(
            confirmed(&json!({"type":"confirmed","confirmation":"replayed",
            "transactionId":"1","eventId":"2","acceptedCount":"3","imageBoundary":"4"}))
            .is_ok()
        );
    }

    #[test]
    fn installed_and_replayed_receipts_have_one_stable_result() {
        let root = std::env::temp_dir().join(format!(
            "mini-enrollment-result-{}-{}",
            std::process::id(),
            nonce().unwrap()
        ));
        fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
        let pin = Pin {
            host: PathBuf::new(),
            config: PathBuf::new(),
            public_socket: PathBuf::new(),
            operation_socket: PathBuf::new(),
            sponsor_key: PathBuf::new(),
            new_key: Some(PathBuf::from("/private/new.key")),
            subject: "42".into(),
            key_id: "99".into(),
            public_key: "aa".repeat(32),
            plan: vec![],
            command: vec![],
        };
        let installed = json!({"type":"confirmed","confirmation":"installed",
            "transactionId":"1","eventId":"2","acceptedCount":"3","imageBoundary":"4"});
        let replayed = json!({"type":"confirmed","confirmation":"replayed",
            "transactionId":"1","eventId":"2","acceptedCount":"3","imageBoundary":"4"});
        result(&root, &pin, &installed).unwrap();
        result(&root, &pin, &replayed).unwrap();
        assert_eq!(
            json_private(&root.join("enrollment.json")).unwrap()["receipt"]["eventId"],
            "2"
        );
        fs::remove_dir_all(root).unwrap();
    }
}
