//! `mini attempt-state --attempt DIR [--file NAME]`: an attempt's retained state as JSON, read
//! locally (no socket, no Host). It reads the answers through the SDK's one history (`store::AttemptDir::history`: `outcome.json`, then `retry-N.json` in numeric
//! order) and its one standing rule (`custody::standing`).
//!
//! Output (`--file` absent): `{"type":"minidregg-attempt-state-v1","class":"answered","attempt",
//! "call","outcome","retries":[{"file","outcome"}],"last","standing"}`;
//! `outcome` is `outcome.json`'s value or null, `last` the newest answer or null, `standing` one of
//! confirmed | charged | refused | pending. With `--file outcome.json` or `--file retry-NNNN.json`
//! the verb prints exactly that answer's JSON (what `jq ... DIR/outcome.json` read before), exit 1
//! when it is absent. An answer file that does not parse: exit 1 naming it, never a guess.
use std::path::Path;

use serde_json::{json, Value};

type Result<T> = std::result::Result<T, String>;

fn answer_name(name: &str) -> bool {
    name == "outcome.json"
        || name.strip_prefix("retry-").and_then(|s| s.strip_suffix(".json"))
            .is_some_and(mini_sdk::decimal::is_digits)
}

pub(crate) fn state(dir: &Path) -> Result<Value> {
    if !dir.is_dir() {
        return Err(format!("attempt-state: no attempt directory at {}", dir.display()));
    }
    let attempt = mini_sdk::store::AttemptDir(dir.to_path_buf());
    let outcome = mini_sdk::store::read_json(&dir.join("outcome.json"))
        .map_err(|e| format!("attempt-state: outcome.json: {e}"))?;
    let mut retries = Vec::new();
    for path in attempt.outcome_files().map_err(String::from)? {
        let name = path.file_name().and_then(|n| n.to_str()).unwrap_or_default().to_owned();
        let value = mini_sdk::store::read_json(&path).map_err(|e| format!("attempt-state: {name}: {e}"))?
            .ok_or_else(|| format!("attempt-state: {name} vanished while read"))?;
        retries.push(json!({"file": name, "outcome": value}));
    }
    let history = attempt.history().map_err(String::from)?;
    let standing = match mini_sdk::custody::standing(&history) {
        mini_sdk::custody::Standing::Confirmed(_) => "confirmed",
        mini_sdk::custody::Standing::Charged(_) => "charged",
        mini_sdk::custody::Standing::Refused => "refused",
        mini_sdk::custody::Standing::Pending => "pending",
    };
    Ok(json!({
        "type": "minidregg-attempt-state-v1",
        "class": "answered",
        "attempt": dir,
        "call": dir.join("call.bin").is_file(),
        "outcome": outcome,
        "retries": retries,
        "last": history.last().cloned(),
        "standing": standing,
    }))
}

pub(crate) fn run(dir: &Path, file: Option<&str>) -> Result<()> {
    let value = state(dir)?;
    let printed = match file {
        None => value,
        Some(name) if answer_name(name) => {
            let found = if name == "outcome.json" {
                value["outcome"].clone()
            } else {
                value["retries"].as_array().into_iter().flatten()
                    .find(|r| r["file"] == name).map(|r| r["outcome"].clone()).unwrap_or(Value::Null)
            };
            if found.is_null() {
                return Err(format!("attempt-state: {} holds no {name}", dir.display()));
            }
            found
        }
        Some(name) => return Err(format!("attempt-state: --file names an answer (outcome.json or retry-NNNN.json), not {name}")),
    };
    println!("{}", serde_json::to_string(&printed).map_err(|e| e.to_string())?);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn scratch(tag: &str) -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!("mini-attempt-state-{tag}-{}-{}", std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir_all(&p).unwrap();
        p
    }

    fn retained_attempt(tag: &str) -> std::path::PathBuf {
        let dir = scratch(tag);
        fs::write(dir.join("intent.json"), br#"{"action":"invoke","object":"7"}"#).unwrap();
        fs::write(dir.join("call.bin"), b"exact call bytes").unwrap();
        dir
    }

    #[test]
    fn attempt_state_reads_a_decided_attempt() {
        let dir = retained_attempt("decided");
        fs::write(dir.join("outcome.json"), br#"{"type":"refused","phase":"admit","detail":"stale","reason":"stale-root"}"#).unwrap();
        fs::write(dir.join("retry-0001.json"), br#"{"type":"confirmed","confirmation":"installed","transactionId":"9","acceptedCount":"12"}"#).unwrap();
        let state = state(&dir).unwrap();
        assert_eq!(state["class"], "answered");
        assert_eq!(state["call"], true);
        assert_eq!(state["outcome"]["phase"], "admit");
        assert_eq!(state["retries"][0]["file"], "retry-0001.json");
        assert_eq!(state["last"]["acceptedCount"], "12");
        assert_eq!(state["standing"], "confirmed");
        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn attempt_state_names_a_corrupt_answer() {
        let dir = retained_attempt("corrupt");
        fs::write(dir.join("outcome.json"), b"{\"type\":\"conf").unwrap();
        let error = state(&dir).unwrap_err();
        assert!(error.contains("outcome.json"), "{error}");
        fs::remove_dir_all(&dir).unwrap();
    }
}
