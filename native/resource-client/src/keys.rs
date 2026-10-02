//! `mini key`: put a provider key into hosted custody and say which Hermes
//! runners may use it.
//!
//!   mini key --action set    --dir WORKSPACE --provider NAME --secret FILE|-
//!   mini key --action grant  --dir WORKSPACE --provider NAME --runner SUBJECT
//!                            --per-call TOKENS --per-day CALLS --until HEIGHT
//!   mini key --action revoke --dir WORKSPACE --provider NAME [--runner SUBJECT]
//!   mini key --action ls     --dir WORKSPACE
//!   mini key --action set|revoke|ls --pool true --provider NAME [--secret FILE|-]
//!
//! The namespace is the workspace's subject AND the public key of its signing
//! key, so a workspace that only claims someone else's subject lands in its
//! own directory (`credentials.rs`). `--pool true` is the operator's pool key;
//! the hosted shell never offers it. Values are never printed.
//!
//! Shell verbs (`key set PROVIDER -|@FILE`, `key grant PROVIDER RUNNER
//! --per-call N --per-day N --until HEIGHT`, `key revoke PROVIDER [RUNNER]`,
//! `key ls`) map one-to-one onto the above through `shell_plan`.

use super::shell::Plan;
use super::{Args, Result};
use serde_json::{json, Value};
use std::ffi::OsString;
use std::io::Read;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

#[path = "../../grain-runtime/src/credentials.rs"]
#[allow(dead_code)] // shared with grain-runtime: its reserve-time lookups are used there
mod credentials;
#[path = "key_service.rs"]
mod service;

use credentials::{CredentialSource, CredentialStore, Grant, Namespace, Owner, ProviderTable};

/// Set by the shell: true only for the one-verb form (`--line`), where stdin
/// is not the shell's own input and `key set PROVIDER -` may read it.
pub(crate) static STDIN_FREE: OnceLock<bool> = OnceLock::new();

pub(crate) const SHELL_USAGE: &str = "key set PROVIDER -|@FILE | key grant PROVIDER RUNNER --per-call TOKENS --per-day CALLS --until HEIGHT [--model MODEL] | key revoke PROVIDER [RUNNER] | key ls | key providers | key choose PROVIDER MODEL RUNNER TASK";

fn text(value: OsString, label: &str) -> Result<String> {
    value
        .into_string()
        .map_err(|_| format!("--{label} must be UTF-8"))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// The workspace's subject and the public key of its own signing key.
fn owner(workspace: &Path) -> Result<Owner> {
    let pin = super::workspace::load(workspace)?;
    let subject = pin
        .get("subject")
        .and_then(Value::as_str)
        .ok_or("workspace has no subject")?;
    let key = pin
        .get("key")
        .and_then(Value::as_str)
        .ok_or("workspace has no key")?;
    let mut seed: [u8; 32] = crate::agent_reserve::private_bytes(Path::new(key), 32)?
        .try_into()
        .map_err(|_| "workspace key must be exactly 32 bytes")?;
    let public = ed25519_dalek::SigningKey::from_bytes(&seed)
        .verifying_key()
        .to_bytes();
    seed.fill(0);
    Owner::new(subject, &hex(&public))
}

fn read_secret(source: &str) -> Result<credentials::Secret> {
    let mut bytes = Vec::new();
    if source == "-" {
        std::io::stdin()
            .take(4100)
            .read_to_end(&mut bytes)
            .map_err(|e| format!("cannot read provider secret from stdin: {e}"))?;
    } else {
        let path = Path::new(source);
        let mut file = std::fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
            .open(path)
            .map_err(|_| "provider secret file is unavailable".to_owned())?;
        let meta = file
            .metadata()
            .map_err(|_| "provider secret file metadata unavailable".to_owned())?;
        if !meta.file_type().is_file()
            || meta.len() > 4100
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.permissions().mode() & 0o077 != 0
        {
            return Err(
                "provider secret file must be an owned private regular file under 4100 bytes"
                    .into(),
            );
        }
        file.by_ref()
            .take(4100)
            .read_to_end(&mut bytes)
            .map_err(|_| "cannot read provider secret file".to_owned())?;
    }
    let secret = credentials::secret_from_input(&bytes);
    bytes.fill(0);
    secret
}

fn row_of(
    table: &Path,
    provider: &str,
    wanted: CredentialSource,
    model: Option<&str>,
) -> Result<()> {
    let table = ProviderTable::load(table, 0)?;
    let row = table
        .rows
        .iter()
        .find(|row| row.name == provider)
        .ok_or_else(|| format!("provider table has no row named {provider}"))?;
    if row.credential != wanted {
        return Err(match wanted {
            CredentialSource::Pool => format!("{provider} is not a pool row"),
            _ => format!("{provider} does not take a friend's own key"),
        });
    }
    if model.is_some_and(|model| !row.models.iter().any(|m| m == model)) {
        return Err(
            "model is not allowed on the selected provider route; see key providers".into(),
        );
    }
    Ok(())
}

fn catalogue(table: &ProviderTable) -> Value {
    let providers: Vec<Value> = table.rows.iter().map(|row| json!({
        "provider":row.name, "models":row.models,
        "credential":match row.credential { CredentialSource::User => "user", CredentialSource::Pool => "pool", CredentialSource::Homelab => "homelab" },
        "memberKey":row.credential == CredentialSource::User,
    })).collect();
    json!({"type":"mini-provider-catalogue-v1", "providers":providers,"tableSha256":table.sha256,
        "custody":"Hosted keys are sealed on this service; its operator can use them. A local key command does not upload custody to a remote service.",
        "selection":"A credential grant authorizes a provider/model; the controller must also be provisioned for that route.",
        "budget":"Credential caps limit output tokens and calls; Mini purse authority and credit remain separate."})
}

fn owner_view(host: &Path, socket: &Path, config: &Path, owner: &Owner) -> Result<Value> {
    let payload =
        serde_json::to_vec(&json!({"subject":owner.subject,"publicKey":owner.public_key})).unwrap();
    let reply = crate::session_invoke(host, socket, config, 144, &payload)?;
    let mut view: Value = match reply.split_first() {
        Some((144, body)) => {
            serde_json::from_slice(body).map_err(|_| "invalid native owner status")?
        }
        _ => return Err("native owner status unavailable".into()),
    };
    service::verify_current(&view, owner)?;
    view["publicKey"] = json!(owner.public_key);
    Ok(view)
}
fn owner_status(mut args: Args) -> Result<()> {
    let host = PathBuf::from(args.required("host")?);
    let socket = crate::SOCKET
        .get()
        .ok_or("owner-status requires --socket")?
        .clone();
    let config = PathBuf::from(args.required("config")?);
    let subject = text(args.required("subject")?, "subject")?;
    let public = text(args.required("public-key")?, "public-key")?;
    args.finish()?;
    super::print_json(&owner_view(
        &host,
        &socket,
        &config,
        &Owner::new(&subject, &public)?,
    )?)
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = text(args.required("action")?, "action")?;
    if action == "owner-status" {
        return owner_status(args);
    }
    let root_override = args.optional("credentials").map(PathBuf::from);
    let key_override = args.optional("credentials-key").map(PathBuf::from);
    let table_override = args.optional("providers").map(PathBuf::from);
    let custom_custody =
        root_override.is_some() || key_override.is_some() || table_override.is_some();
    let root = root_override.unwrap_or_else(|| PathBuf::from(credentials::DEFAULT_ROOT));
    let key = key_override.unwrap_or_else(|| PathBuf::from(credentials::DEFAULT_KEY));
    let table = table_override.unwrap_or_else(|| PathBuf::from(credentials::DEFAULT_TABLE));
    let pool = match args
        .optional("pool")
        .map(|v| text(v, "pool"))
        .transpose()?
        .as_deref()
    {
        None | Some("false") => false,
        Some("true") => true,
        Some(_) => return Err("--pool must be true or false".into()),
    };
    let workspace = args.optional("dir").map(PathBuf::from);
    let provider = args
        .optional("provider")
        .map(|v| text(v, "provider"))
        .transpose()?;
    let secret = args
        .optional("secret")
        .map(|v| text(v, "secret"))
        .transpose()?;
    let runner = args
        .optional("runner")
        .map(|v| text(v, "runner"))
        .transpose()?;
    let per_call = args
        .optional("per-call")
        .map(|v| text(v, "per-call"))
        .transpose()?;
    let per_day = args
        .optional("per-day")
        .map(|v| text(v, "per-day"))
        .transpose()?;
    let until = args
        .optional("until")
        .map(|v| text(v, "until"))
        .transpose()?;
    let model = args
        .optional("model")
        .map(|v| text(v, "model"))
        .transpose()?;
    let task = args.optional("task").map(|v| text(v, "task")).transpose()?;
    args.finish()?;
    if !pool {
        let workspace = workspace
            .as_ref()
            .ok_or("member key commands need --dir WORKSPACE")?;
        let owner = owner(workspace)?;
        let mut request = json!({"action":action});
        for (name, value) in [
            ("provider", provider),
            ("runner", runner),
            ("perCall", per_call),
            ("perDay", per_day),
            ("notAfter", until),
            ("model", model),
            ("task", task),
        ] {
            if let Some(value) = value {
                request[name] = json!(value);
            }
        }
        if let Some(source) = secret {
            if action != "set" {
                return Err("only key set takes --secret".into());
            }
            request["secret"] = json!(read_secret(&source)?.expose());
        }
        let result = (|| {
            let ws = super::workspace::load(workspace)?;
            if let Some(destination) = ws
                .get("socket")
                .and_then(Value::as_str)
                .and_then(|s| s.strip_prefix("ssh:"))
            {
                if custom_custody {
                    return Err("remote credential custody is pinned by the service; local custody overrides are unavailable".into());
                }
                return service::client(workspace, &ws, &owner, destination, &mut request);
            }
            let table = ProviderTable::load(&table, 0)?;
            sign_choice(workspace, &owner, &table.sha256, &mut request)?;
            let view = owner_view(
                &super::workspace::workspace_host(&ws)?,
                &super::workspace::member_path(&ws, "socket")?,
                &super::workspace::member_path(&ws, "config")?,
                &owner,
            )?;
            member_action(
                &CredentialStore::open(&root, &key)?,
                &owner,
                &table,
                &request,
                required(&view, "keyEpoch")?,
            )
        })();
        scrub_request(&mut request);
        return super::print_json(&result?);
    }
    if workspace.is_some() {
        return Err("--pool true takes no workspace".into());
    }
    if task.is_some()
        || model.is_some()
        || per_call.is_some()
        || per_day.is_some()
        || until.is_some()
    {
        return Err("pool commands take no member choice or grant limits".into());
    }
    let namespace = Namespace::Pool;
    let who = json!("pool");
    let store = CredentialStore::open(&root, &key)?;
    let need = |value: Option<String>, label: &str| {
        value.ok_or_else(|| format!("key {action} needs --{label}"))
    };
    let reject = |present: bool, label: &str| -> Result<()> {
        if present {
            return Err(format!("key {action} does not take --{label}"));
        }
        Ok(())
    };
    let report = match action.as_str() {
        "set" => {
            reject(
                model.is_some()
                    || runner.is_some()
                    || per_call.is_some()
                    || per_day.is_some()
                    || until.is_some(),
                "runner/caps",
            )?;
            let provider = need(provider, "provider")?;
            credentials::provider_name(&provider)?;
            row_of(&table, &provider, CredentialSource::Pool, None)?;
            let secret = read_secret(&need(secret, "secret")?)?;
            store.set(namespace, &provider, &secret)?;
            json!({"type":"mini-key-set-v1","owner":who,"provider":provider,
                "stored":"sealed","existingGrants":"preserved","next":"none: the purse gates pool spend"})
        }
        "revoke" => {
            reject(
                model.is_some()
                    || secret.is_some()
                    || per_call.is_some()
                    || per_day.is_some()
                    || until.is_some(),
                "secret/caps",
            )?;
            let provider = need(provider, "provider")?;
            let removed = store.revoke(namespace, &provider, runner.as_deref())?;
            json!({"type":"mini-key-revoke-v1","owner":who,"provider":provider,
                "runner":runner,"removed":removed,"effect":"Future reservations refuse; an already authorized request may finish."})
        }
        "ls" => {
            reject(
                provider.is_some()
                    || secret.is_some()
                    || runner.is_some()
                    || per_call.is_some()
                    || per_day.is_some()
                    || until.is_some()
                    || model.is_some(),
                "provider/secret/runner/caps/model",
            )?;
            let mut listed = store.list(namespace)?;
            listed["owner"] = who;
            listed
        }
        _ => return Err("pool key --action must be set, revoke or ls".into()),
    };
    super::print_json(&report)
}

fn scrub_request(request: &mut Value) {
    if let Some(Value::String(mut secret)) =
        request.as_object_mut().and_then(|m| m.remove("secret"))
    {
        unsafe {
            secret.as_bytes_mut().fill(0);
        }
    }
}
fn sign_choice(
    workspace: &Path,
    owner: &Owner,
    table_sha256: &str,
    request: &mut Value,
) -> Result<()> {
    if request["action"] != "choose" {
        return Ok(());
    }
    action_fields(request, &["action", "provider", "model", "runner", "task"])?;
    let ws = super::workspace::load(workspace)?;
    let key = super::workspace::member_path(&ws, "key")?;
    let mut seed: [u8; 32] = crate::agent_reserve::private_bytes(&key, 32)?
        .try_into()
        .map_err(|_| "workspace key size")?;
    let choice = credentials::choice::Choice::signed_for_catalogue(
        owner.clone(),
        required(request, "runner")?,
        required(request, "task")?,
        required(request, "provider")?,
        required(request, "model")?,
        table_sha256,
        &seed,
    );
    seed.fill(0);
    *request = json!({"action":"choose","choice":choice?.to_json()});
    Ok(())
}
fn required<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("key action requires {key}"))
}
fn action_fields(value: &Value, fields: &[&str]) -> Result<()> {
    if value
        .as_object()
        .is_none_or(|m| m.keys().any(|k| !fields.contains(&k.as_str())))
    {
        return Err("unknown key action field".into());
    }
    Ok(())
}
/// One operation implementation for hosted shell and authenticated remote service.
fn member_action(
    store: &CredentialStore,
    owner: &Owner,
    table: &ProviderTable,
    request: &Value,
    owner_epoch: &str,
) -> Result<Value> {
    let who = json!({"subject":owner.subject,"publicKey":owner.public_key});
    let provider = || required(request, "provider");
    let user_row = |name: &str| -> Result<()> {
        if table
            .rows
            .iter()
            .any(|r| r.name == name && r.credential == CredentialSource::User)
        {
            Ok(())
        } else {
            Err("selected provider does not accept a member key".into())
        }
    };
    match required(request, "action")? {
        "providers" => {
            action_fields(request, &["action"])?;
            Ok(catalogue(table))
        }
        "ls" => {
            action_fields(request, &["action"])?;
            let mut v = store.list(Namespace::Owner(owner))?;
            v["owner"] = who;
            Ok(v)
        }
        "set" => {
            action_fields(request, &["action", "provider", "secret"])?;
            let provider = provider()?;
            user_row(provider)?;
            let secret = credentials::Secret::new(required(request, "secret")?.to_owned())?;
            store.set(Namespace::Owner(owner), provider, &secret)?;
            Ok(
                json!({"type":"mini-key-set-v1","owner":who,"provider":provider,"stored":"sealed","existingGrants":"preserved"}),
            )
        }
        "grant" => {
            action_fields(
                request,
                &[
                    "action", "provider", "runner", "perCall", "perDay", "notAfter", "model",
                ],
            )?;
            let provider = provider()?;
            user_row(provider)?;
            let mut raw = request.clone();
            raw.as_object_mut().unwrap().remove("action");
            raw.as_object_mut().unwrap().remove("provider");
            raw["ownerEpoch"] = json!(owner_epoch);
            let grant = Grant::from_json(&raw)?;
            if let Some(model) = &grant.model {
                table.select(model, Some(provider))?;
            }
            store.grant(owner, provider, grant.clone())?;
            Ok(
                json!({"type":"mini-key-grant-v1","owner":who,"provider":provider,"grant":grant.to_json(),"budget":"Mini purse authority and credit are separate"}),
            )
        }
        "revoke" => {
            action_fields(request, &["action", "provider", "runner"])?;
            let provider = provider()?;
            let runner = request
                .get("runner")
                .map(|_| required(request, "runner"))
                .transpose()?;
            let removed = store.revoke(Namespace::Owner(owner), provider, runner)?;
            Ok(
                json!({"type":"mini-key-revoke-v1","owner":who,"provider":provider,"runner":runner,"removed":removed,"effect":"Future reservations refuse; an already authorized request may finish."}),
            )
        }
        "choose" => {
            action_fields(request, &["action", "choice"])?;
            let choice = credentials::choice::Choice::from_json(
                request.get("choice").ok_or("choice absent")?,
            )?;
            if &choice.owner != owner {
                return Err("choice belongs to another member".into());
            }
            store.choose(&choice, table)?;
            Ok(
                json!({"type":"mini-provider-choice-stored-v1","choice":choice.to_json(),"choiceSha256":choice.digest(),"activation":"Fresh controller provisioning must consume this choice; existing controllers remain pinned."}),
            )
        }
        _ => Err("unknown member key action".into()),
    }
}

pub(crate) fn serve(mut args: Args) -> Result<()> {
    let config = PathBuf::from(args.required("config")?);
    args.finish()?;
    service::serve(&config)
}

fn flag(name: &str, value: impl Into<OsString>) -> (String, OsString) {
    (name.to_owned(), value.into())
}

fn plain_file(value: &str) -> Result<()> {
    if value.is_empty()
        || value.len() > 64
        || value.starts_with('.')
        || !value
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.'))
    {
        return Err("key file must be a plain file name in HOME/keys".into());
    }
    Ok(())
}

/// One shell line (`w[0] == "key"`) to one `mini key` call on this
/// session's workspace. `@FILE` is confined to HOME/keys.
pub(crate) fn shell_plan(workspace: &Path, home: &Path, w: &[String]) -> Result<Plan> {
    let usage = || SHELL_USAGE.to_owned();
    let sub = w.get(1).map(String::as_str).ok_or_else(usage)?;
    let mut flags = vec![flag("action", sub), flag("dir", workspace)];
    match sub {
        "choose" => {
            if w.len() != 6 {
                return Err(usage());
            }
            for (name, value) in ["provider", "model", "runner", "task"].iter().zip(&w[2..]) {
                flags.push(flag(name, value.clone()));
            }
        }
        "set" => {
            if w.len() != 4 {
                return Err(usage());
            }
            flags.push(flag("provider", w[2].clone()));
            let source = if w[3] == "-" {
                if STDIN_FREE.get() != Some(&true) {
                    return Err("key set PROVIDER - reads stdin; use the one-verb form: ssh mini@HOST 'key set PROVIDER -' < KEYFILE".into());
                }
                OsString::from("-")
            } else if let Some(file) = w[3].strip_prefix('@') {
                plain_file(file)?;
                home.join("keys").join(file).into_os_string()
            } else {
                return Err(
                    "key set takes the key from - (stdin) or @FILE, never on the line".into(),
                );
            };
            flags.push(flag("secret", source));
        }
        "grant" => {
            if !matches!(w.len(), 10 | 12) {
                return Err(usage());
            }
            flags.push(flag("provider", w[2].clone()));
            flags.push(flag("runner", w[3].clone()));
            let mut seen = Vec::new();
            for pair in w[4..].chunks(2) {
                let name = match pair[0].as_str() {
                    "--per-call" => "per-call",
                    "--per-day" => "per-day",
                    "--until" => "until",
                    "--model" => "model",
                    _ => return Err(usage()),
                };
                if seen.contains(&name) {
                    return Err(usage());
                }
                seen.push(name);
                flags.push(flag(name, pair[1].clone()));
            }
            if !["per-call", "per-day", "until"]
                .iter()
                .all(|name| seen.contains(name))
            {
                return Err(usage());
            }
        }
        "revoke" => {
            if !(3..=4).contains(&w.len()) {
                return Err(usage());
            }
            flags.push(flag("provider", w[2].clone()));
            if let Some(runner) = w.get(3) {
                flags.push(flag("runner", runner.clone()));
            }
        }
        "ls" | "providers" => {
            if w.len() != 2 {
                return Err(usage());
            }
        }
        _ => return Err(usage()),
    }
    Ok(Plan::Client {
        command: "key".into(),
        flags,
        writes: vec![],
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn words(line: &str) -> Vec<String> {
        line.split_whitespace().map(str::to_owned).collect()
    }

    fn flags_of(plan: Plan) -> Vec<(String, String)> {
        match plan {
            Plan::Client {
                command,
                flags,
                writes,
            } => {
                assert_eq!(command, "key");
                assert!(writes.is_empty());
                flags
                    .into_iter()
                    .map(|(k, v)| (k, v.into_string().unwrap()))
                    .collect()
            }
            _ => panic!("key must be one client call"),
        }
    }

    #[test]
    fn catalogue_is_shared_provider_data_without_endpoint_or_custody_details() {
        let table = ProviderTable::parse(br#"{"type":"mini-provider-table-v2","providers":[
          {"name":"openrouter","endpoint":"https://example.test/v1/chat/completions","kind":"openai-compatible","models":["qwen/model"],"credential":"user"},
          {"name":"chutes","endpoint":"https://chutes.example.test/v1/chat/completions","kind":"openai-compatible","models":["another/model"],"credential":"user"},
          {"name":"pug","endpoint":"http://127.0.0.1:10001/v1/chat/completions","kind":"openai-compatible","models":["local/model"],"credential":"homelab"}]}"#).unwrap();
        let report = catalogue(&table);
        assert_eq!(report["providers"][0]["models"][0], "qwen/model");
        assert_eq!(report["providers"][2]["memberKey"], false);
        assert!(!report.to_string().contains("127.0.0.1"));
        let flags = flags_of(
            shell_plan(
                Path::new("/ws"),
                Path::new("/home"),
                &words("key providers"),
            )
            .unwrap(),
        );
        assert_eq!(flags[0], ("action".into(), "providers".into()));
        let flags = flags_of(shell_plan(Path::new("/ws"), Path::new("/home"), &words("key grant chutes 9 --per-call 64 --per-day 2 --until 100 --model another/model")).unwrap());
        assert!(flags.contains(&("model".into(), "another/model".into())));
        assert!(shell_plan(
            Path::new("/ws"),
            Path::new("/home"),
            &words("key grant chutes 9 --per-call 64 --per-day 2 --model another/model")
        )
        .is_err());
    }

    #[test]
    fn shell_lines_map_to_one_key_call_on_the_session_workspace() {
        let ws = Path::new("/s/ws");
        let home = Path::new("/s/home");
        let grant = flags_of(
            shell_plan(
                ws,
                home,
                &words("key grant openrouter 9 --per-call 4096 --per-day 50 --until 900"),
            )
            .unwrap(),
        );
        assert_eq!(
            grant,
            [
                ("action", "grant"),
                ("dir", "/s/ws"),
                ("provider", "openrouter"),
                ("runner", "9"),
                ("per-call", "4096"),
                ("per-day", "50"),
                ("until", "900")
            ]
            .map(|(k, v)| (k.to_owned(), v.to_owned()))
        );
        let set = flags_of(shell_plan(ws, home, &words("key set openrouter @or.key")).unwrap());
        assert_eq!(
            set[3],
            ("secret".to_owned(), "/s/home/keys/or.key".to_owned())
        );
        let revoke = flags_of(shell_plan(ws, home, &words("key revoke openrouter 9")).unwrap());
        assert_eq!(revoke.len(), 4);
        assert_eq!(
            flags_of(shell_plan(ws, home, &words("key ls")).unwrap()).len(),
            2
        );
        for bad in [
            "key set openrouter sk-on-the-line",
            "key set openrouter @../escape",
            "key grant openrouter 9 --per-call 1 --per-call 2 --until 3",
            "key grant openrouter 9 --pool true --per-day 1 --until 3",
            "key ls extra",
            "key frobnicate",
        ] {
            assert!(shell_plan(ws, home, &words(bad)).is_err(), "{bad}");
        }
        // Interactive and script sessions own stdin; only --line may use `-`.
        assert!(shell_plan(ws, home, &words("key set openrouter -")).is_err());
    }
}
