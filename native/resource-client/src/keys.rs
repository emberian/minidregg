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
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

#[path = "../../grain-runtime/src/credentials.rs"]
#[allow(dead_code)] // shared with grain-runtime: its reserve-time lookups are used there
mod credentials;

use credentials::{CredentialStore, CredentialSource, Grant, Namespace, Owner, ProviderTable};

/// Set by the shell: true only for the one-verb form (`--line`), where stdin
/// is not the shell's own input and `key set PROVIDER -` may read it.
pub(crate) static STDIN_FREE: OnceLock<bool> = OnceLock::new();

pub(crate) const SHELL_USAGE: &str = "key set PROVIDER -|@FILE | key grant PROVIDER RUNNER --per-call TOKENS --per-day CALLS --until HEIGHT | key revoke PROVIDER [RUNNER] | key ls";

fn text(value: OsString, label: &str) -> Result<String> {
    value
        .into_string()
        .map_err(|_| format!("--{label} must be UTF-8"))
}

fn number(value: &str, label: &str) -> Result<u64> {
    if value.is_empty() || !value.bytes().all(|b| b.is_ascii_digit()) {
        return Err(format!("{label} must be a decimal number"));
    }
    value
        .parse()
        .map_err(|_| format!("{label} exceeds u64"))
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
    let seed: [u8; 32] = crate::agent_reserve::private_bytes(Path::new(key), 32)?
        .try_into()
        .map_err(|_| "workspace key must be exactly 32 bytes")?;
    let public = ed25519_dalek::SigningKey::from_bytes(&seed)
        .verifying_key()
        .to_bytes();
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
        let meta = std::fs::symlink_metadata(path)
            .map_err(|e| format!("provider secret file: {e}"))?;
        if !meta.file_type().is_file() || meta.len() > 4100 {
            return Err("provider secret file must be a regular file under 4100 bytes".into());
        }
        bytes = std::fs::read(path).map_err(|e| format!("provider secret file: {e}"))?;
    }
    let secret = credentials::secret_from_input(&bytes);
    bytes.fill(0);
    secret
}

fn row_of(table: &Path, provider: &str, wanted: CredentialSource) -> Result<()> {
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
    Ok(())
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = text(args.required("action")?, "action")?;
    let root = args
        .optional("credentials")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(credentials::DEFAULT_ROOT));
    let key = args
        .optional("credentials-key")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(credentials::DEFAULT_KEY));
    let table = args
        .optional("providers")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(credentials::DEFAULT_TABLE));
    let pool = match args.optional("pool").map(|v| text(v, "pool")).transpose()?.as_deref() {
        None | Some("false") => false,
        Some("true") => true,
        Some(_) => return Err("--pool must be true or false".into()),
    };
    let workspace = args.optional("dir").map(PathBuf::from);
    let provider = args.optional("provider").map(|v| text(v, "provider")).transpose()?;
    let secret = args.optional("secret").map(|v| text(v, "secret")).transpose()?;
    let runner = args.optional("runner").map(|v| text(v, "runner")).transpose()?;
    let per_call = args.optional("per-call").map(|v| text(v, "per-call")).transpose()?;
    let per_day = args.optional("per-day").map(|v| text(v, "per-day")).transpose()?;
    let until = args.optional("until").map(|v| text(v, "until")).transpose()?;
    args.finish()?;
    let owner = match (pool, &workspace) {
        (true, None) => None,
        (false, Some(dir)) => Some(owner(dir)?),
        (true, Some(_)) => return Err("--pool true takes no workspace".into()),
        (false, None) => return Err("mini key needs --dir WORKSPACE (or --pool true)".into()),
    };
    let namespace = match &owner {
        Some(owner) => Namespace::Owner(owner),
        None => Namespace::Pool,
    };
    let who = match &owner {
        Some(owner) => json!({"subject":owner.subject,"publicKey":owner.public_key}),
        None => json!("pool"),
    };
    let store = CredentialStore::open(&root, &key)?;
    let need = |value: Option<String>, label: &str| value.ok_or_else(|| format!("key {action} needs --{label}"));
    let reject = |present: bool, label: &str| -> Result<()> {
        if present {
            return Err(format!("key {action} does not take --{label}"));
        }
        Ok(())
    };
    let report = match action.as_str() {
        "set" => {
            reject(runner.is_some() || per_call.is_some() || per_day.is_some() || until.is_some(), "runner/caps")?;
            let provider = need(provider, "provider")?;
            credentials::provider_name(&provider)?;
            row_of(&table, &provider, if pool { CredentialSource::Pool } else { CredentialSource::User })?;
            let secret = read_secret(&need(secret, "secret")?)?;
            store.set(namespace, &provider, &secret)?;
            json!({"type":"mini-key-set-v1","owner":who,"provider":provider,
                "stored":"sealed","next":if pool { "none: the purse gates pool spend" } else { "grant a runner: key grant" }})
        }
        "grant" => {
            reject(secret.is_some(), "secret")?;
            let owner = owner.as_ref().ok_or("the pool is not granted; the purse gates it")?;
            let provider = need(provider, "provider")?;
            row_of(&table, &provider, CredentialSource::User)?;
            let grant = Grant {
                runner: need(runner, "runner")?,
                per_call: number(&need(per_call, "per-call")?, "per-call")?,
                per_day: number(&need(per_day, "per-day")?, "per-day")?,
                not_after: number(&need(until, "until")?, "until")?,
            };
            store.grant(owner, &provider, grant.clone())?;
            json!({"type":"mini-key-grant-v1","owner":who,"provider":provider,
                "runner":grant.runner,"perCall":grant.per_call.to_string(),
                "perDay":grant.per_day.to_string(),"notAfter":grant.not_after.to_string()})
        }
        "revoke" => {
            reject(secret.is_some() || per_call.is_some() || per_day.is_some() || until.is_some(), "secret/caps")?;
            let provider = need(provider, "provider")?;
            let removed = store.revoke(namespace, &provider, runner.as_deref())?;
            json!({"type":"mini-key-revoke-v1","owner":who,"provider":provider,
                "runner":runner,"removed":removed})
        }
        "ls" => {
            reject(provider.is_some() || secret.is_some() || runner.is_some(), "provider/secret/runner")?;
            let mut listed = store.list(namespace)?;
            listed["owner"] = who;
            listed
        }
        _ => return Err("mini key --action must be set, grant, revoke or ls".into()),
    };
    super::print_json(&report)
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
                return Err("key set takes the key from - (stdin) or @FILE, never on the line".into());
            };
            flags.push(flag("secret", source));
        }
        "grant" => {
            if w.len() != 10 {
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
                    _ => return Err(usage()),
                };
                if seen.contains(&name) {
                    return Err(usage());
                }
                seen.push(name);
                flags.push(flag(name, pair[1].clone()));
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
        "ls" => {
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
            Plan::Client { command, flags, writes } => {
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
    fn shell_lines_map_to_one_key_call_on_the_session_workspace() {
        let ws = Path::new("/s/ws");
        let home = Path::new("/s/home");
        let grant = flags_of(
            shell_plan(ws, home, &words("key grant openrouter 9 --per-call 4096 --per-day 50 --until 900")).unwrap(),
        );
        assert_eq!(
            grant,
            [("action", "grant"), ("dir", "/s/ws"), ("provider", "openrouter"), ("runner", "9"),
             ("per-call", "4096"), ("per-day", "50"), ("until", "900")]
                .map(|(k, v)| (k.to_owned(), v.to_owned()))
        );
        let set = flags_of(shell_plan(ws, home, &words("key set openrouter @or.key")).unwrap());
        assert_eq!(set[3], ("secret".to_owned(), "/s/home/keys/or.key".to_owned()));
        let revoke = flags_of(shell_plan(ws, home, &words("key revoke openrouter 9")).unwrap());
        assert_eq!(revoke.len(), 4);
        assert_eq!(flags_of(shell_plan(ws, home, &words("key ls")).unwrap()).len(), 2);
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
