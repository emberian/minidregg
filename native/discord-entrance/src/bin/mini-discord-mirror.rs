//! `mini-discord-mirror`: a RUNNER that mirrors one Mini reference into one Discord channel.
//!
//! It is not part of the interactions endpoint. It holds its OWN session (its own key, its
//! own workspace, the observe capability someone delegated to it); every poll is one
//! `read REF` through the same forced command as ssh and Discord, so every poll is a signed
//! Host observation by the runner's key, metered and refusable like anyone's. It posts what
//! changed to a channel webhook.
//!
//! Direction: stream -> channel only. Channel -> `say` is NOT implemented: `mini shell` has
//! no `say`/`tail` verbs until PLACE §4.4 K-STREAM lands, and a channel message has no Mini
//! author to sign it. Until then the "stream" is the cell's fields: a new or changed field is
//! an entry. When `tail ROOM --since H` exists, the poll line changes and nothing else.
//!
//! Configuration is the environment (`EnvironmentFile`, 0600; the webhook URL is a secret):
//! `MINI_MIRROR_REF`, `MINI_MIRROR_WEBHOOK_URL`, `MINI_MIRROR_HOME`, `MINI_MIRROR_WORKSPACE`,
//! `MINI_MIRROR_INTERVAL_S` (default 30), `MINI_DISCORD_SPOOL`, the deployment variables of
//! `mini-discord` (`MINI_SHELL_WRAPPER` `MINI_CLIENT` `MINI_HOST` `MINI_CONFIG` `MINI_SOCKET`).
//! One argument is accepted: `--once` (one poll, exit 0 when it posted or had nothing new).

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Duration;

use minidregg_discord_entrance::curl::Poster;
use minidregg_discord_entrance::interaction::followup;
use minidregg_discord_entrance::reply::code_block;
use minidregg_discord_entrance::session::{append_log, Deployment, Session};
use minidregg_discord_entrance::{env_path, env_required, env_u64, now_s};
use serde_json::{json, Value};

const LOG_FILE: &str = "discord-mirror.log";

fn fail(msg: impl std::fmt::Display) -> ! {
    eprintln!("mini-discord-mirror: {msg}");
    std::process::exit(78);
}

fn is_ref_name(s: &str) -> bool {
    !s.is_empty() && s.len() <= 64 && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
}

fn scalar(v: &Value) -> String {
    match v {
        Value::String(s) => s.clone(),
        other => other.to_string(),
    }
}

/// The fields of the last JSON document on stdout that carries `page.entries`.
pub fn fields_of(stdout: &str) -> Option<BTreeMap<String, String>> {
    let mut last = None;
    for doc in serde_json::Deserializer::from_str(stdout).into_iter::<Value>() {
        let Ok(doc) = doc else { break };
        if let Some(entries) = doc.get("page").and_then(|p| p.get("entries")).and_then(Value::as_array) {
            let mut m = BTreeMap::new();
            for e in entries {
                if let (Some(k), Some(v)) = (e.get("key").and_then(|k| k.get("field")), e.get("value")) {
                    m.insert(scalar(k), scalar(v));
                }
            }
            last = Some(m);
        }
    }
    last
}

/// What changed, one line per field, in field order.
pub fn diff(old: &BTreeMap<String, String>, new: &BTreeMap<String, String>) -> Vec<String> {
    let mut out = Vec::new();
    for (k, v) in new {
        match old.get(k) {
            None => out.push(format!("field {k} = {v}")),
            Some(w) if w != v => out.push(format!("field {k} = {v} (was {w})")),
            _ => {}
        }
    }
    for k in old.keys().filter(|k| !new.contains_key(*k)) {
        out.push(format!("field {k} removed"));
    }
    out
}

fn load_state(p: &Path) -> BTreeMap<String, String> {
    std::fs::read(p)
        .ok()
        .and_then(|b| serde_json::from_slice::<BTreeMap<String, String>>(&b).ok())
        .unwrap_or_default()
}

fn save_state(p: &Path, m: &BTreeMap<String, String>) -> std::io::Result<()> {
    let tmp = p.with_extension("tmp");
    std::fs::write(&tmp, serde_json::to_vec(m)?)?;
    std::fs::rename(tmp, p)
}

struct Mirror {
    deployment: Deployment,
    session: Session,
    reference: String,
    webhook: String,
    poster: Poster,
    state: PathBuf,
}

impl Mirror {
    /// One poll. `Ok(n)`: n changes posted (0: nothing new).
    fn poll(&self) -> Result<usize, String> {
        let outcome = self.deployment.run(&self.session, &format!("read {}", self.reference));
        if outcome.ending.word != "ok" {
            let _ = append_log(
                &self.session.home,
                LOG_FILE,
                &json!({ "at": now_s(), "ref": self.reference, "ending": outcome.ending.word, "ending_line": outcome.ending.line }),
            );
            return Err(outcome.ending.line);
        }
        let new = fields_of(&outcome.stdout).ok_or("read printed no page")?;
        let old = load_state(&self.state);
        let changes = diff(&old, &new);
        if changes.is_empty() {
            return Ok(0);
        }
        let content = format!("`{}`\n{}", self.reference, code_block(&changes.join("\n")));
        let content = if content.chars().count() > minidregg_discord_entrance::reply::DISCORD_LIMIT {
            code_block(&format!("{}\n{}", self.reference, changes.join("\n")))
        } else {
            content
        };
        let url = if self.webhook.contains('?') { format!("{}&wait=true", self.webhook) } else { format!("{}?wait=true", self.webhook) };
        let code = self.poster.send("POST", &url, followup(&content).to_string().as_bytes())?;
        if !(200..300).contains(&code) {
            return Err(format!("channel webhook answered HTTP {code}"));
        }
        save_state(&self.state, &new).map_err(|e| format!("state {}: {e}", self.state.display()))?;
        let _ = append_log(
            &self.session.home,
            LOG_FILE,
            &json!({ "at": now_s(), "ref": self.reference, "ending": "ok", "posted": changes }),
        );
        Ok(changes.len())
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let once = match args.as_slice() {
        [] => false,
        [a] if a == "--once" => true,
        _ => fail("usage: mini-discord-mirror [--once]; configuration is the environment"),
    };
    let reference = env_required("MINI_MIRROR_REF").unwrap_or_else(|e| fail(e));
    if !is_ref_name(&reference) {
        fail("MINI_MIRROR_REF must be a reference name (letters, digits, hyphens)");
    }
    let webhook = env_required("MINI_MIRROR_WEBHOOK_URL").unwrap_or_else(|e| fail(e));
    if !minidregg_discord_entrance::curl::is_plain_url(&webhook) {
        fail("MINI_MIRROR_WEBHOOK_URL is not a plain URL");
    }
    let home = env_path("MINI_MIRROR_HOME").unwrap_or_else(|e| fail(e));
    let workspace = env_path("MINI_MIRROR_WORKSPACE").unwrap_or_else(|e| fail(e));
    let interval = env_u64("MINI_MIRROR_INTERVAL_S", 30).unwrap_or_else(|e| fail(e)).max(5);
    let spool = match std::env::var("MINI_DISCORD_SPOOL") {
        Ok(v) if !v.is_empty() => env_path("MINI_DISCORD_SPOOL").unwrap_or_else(|e| fail(e)),
        _ => PathBuf::from("/run/mini-discord"),
    };
    let state_dir = home.join("mirror");
    if let Err(e) = std::fs::create_dir_all(&state_dir) {
        fail(format!("{}: {e}", state_dir.display()));
    }
    let mirror = Mirror {
        deployment: Deployment::from_env().unwrap_or_else(|e| fail(e)),
        session: Session { name: "mirror".into(), home, workspace },
        state: state_dir.join(format!("{reference}.json")),
        reference,
        webhook,
        poster: Poster { curl: PathBuf::from(minidregg_discord_entrance::curl::CURL), spool, max_time_s: 20 },
    };
    loop {
        match mirror.poll() {
            Ok(n) => eprintln!("mini-discord-mirror: {} posted {n} change(s)", mirror.reference),
            Err(e) => {
                eprintln!("mini-discord-mirror: {}: {e}", mirror.reference);
                if once {
                    std::process::exit(1);
                }
            }
        }
        if once {
            return;
        }
        std::thread::sleep(Duration::from_secs(interval));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fields_from_the_last_page_and_their_diff() {
        let out = r#"{"subject":"7"}
{"page":{"entries":[{"key":{"field":"2"},"value":"1"}]}}
{"page":{"entries":[{"key":{"field":"2"},"value":"7"},{"key":{"field":"3"},"value":9}]}}"#;
        let new = fields_of(out).unwrap();
        assert_eq!(new.get("2").map(String::as_str), Some("7"));
        assert_eq!(new.get("3").map(String::as_str), Some("9"));
        let mut old = BTreeMap::new();
        old.insert("2".to_string(), "1".to_string());
        old.insert("4".to_string(), "0".to_string());
        assert_eq!(diff(&old, &new), vec!["field 2 = 7 (was 1)", "field 3 = 9", "field 4 removed"]);
        assert!(diff(&new, &new).is_empty());
        assert!(fields_of("{\"subject\":1}").is_none());
    }

    #[test]
    fn reference_names() {
        assert!(is_ref_name("shared"));
        assert!(!is_ref_name("../x"));
        assert!(!is_ref_name(""));
    }
}
