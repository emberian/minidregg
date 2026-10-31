//! Recorded whole-store lifecycle evidence, separate from local ingest verdicts.
//! Shipped in the candidate; an operator may select a newer sweep JSON explicitly.
use super::{valid_app_id, valid_package_id, Entry};
use crate::Result;
use serde_json::{json, Value};
use std::{collections::BTreeMap, path::Path};

const RECORDED: &str = include_str!("../../../deploy/market/store-qualification.json");
const SCOPE: &str = "install-share-start-enroll-get-root";

pub(super) struct Qualification(BTreeMap<(String, String), Value>);

impl Qualification {
    pub(super) fn load(path: Option<&Path>) -> Result<Self> {
        let bytes = match path {
            Some(path) => crate::fsio::read_bounded(path, 4 * 1024 * 1024)
                .map_err(|e| format!("store qualification {}: {e}", path.display()))?,
            None => RECORDED.as_bytes().to_vec(),
        };
        Self::parse(&bytes).map_err(|e| format!("store qualification: {e}"))
    }

    fn parse(bytes: &[u8]) -> Result<Self> {
        let value: Value = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
        let text = |v: &Value, key: &str| -> Result<String> {
            v[key]
                .as_str()
                .filter(|s| !s.is_empty() && s.len() <= 4096)
                .map(str::to_owned)
                .ok_or_else(|| format!("missing/invalid {key}"))
        };
        if value["protocol"] != "mini-store-qualification-v1" || value["scope"] != SCOPE {
            return Err("unknown protocol or lifecycle scope".into());
        }
        let candidate = text(&value, "candidate")?;
        if candidate.len() != 40
            || !candidate
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err("invalid candidate commit".into());
        }
        let apps = value["apps"].as_array().ok_or("missing apps")?;
        let mut entries = BTreeMap::new();
        for app in apps {
            let app_id = text(app, "appId")?;
            let package_id = text(app, "packageId")?;
            if !valid_app_id(&app_id)
                || !valid_package_id(&package_id)
                || app["candidate"] != candidate
            {
                return Err("invalid package identity or mismatched candidate".into());
            }
            let verdict = text(app, "verdict")?;
            let stage = text(app, "stage")?;
            let state = match verdict.as_str() {
                "PASS" if stage == "get" => "known-working",
                "FAIL" => "lifecycle-failed",
                _ => return Err("invalid verdict or incomplete PASS".into()),
            };
            let row = json!({"state":state,"verdict":verdict,"candidate":candidate,"scope":SCOPE,
                "stage":stage,"reason":text(app,"reason")?,"evidence":text(app,"evidence")?,
                "checkedAt":text(app,"checkedAt")?,"importProfile":text(app,"importProfile")?});
            if entries.insert((app_id, package_id), row).is_some() {
                return Err("duplicate package verdict".into());
            }
        }
        Ok(Self(entries))
    }

    pub(super) fn get(&self, entry: &Entry) -> Option<&Value> {
        self.0
            .get(&(entry.app_id.clone(), entry.package_id.clone()))
    }
}

pub(super) fn line(row: Option<&Value>) -> String {
    match row {
        None => "its lifecycle not yet tried on this box".into(),
        Some(v) => {
            let candidate = v["candidate"].as_str().unwrap_or_default();
            if v["state"] == "known-working" {
                format!("known working (lifecycle; candidate {})", &candidate[..9])
            } else {
                format!(
                    "lifecycle failed at {} (candidate {}): {}",
                    v["stage"].as_str().unwrap_or_default(),
                    &candidate[..9],
                    v["reason"]
                        .as_str()
                        .unwrap_or_default()
                        .replace(['\n', '\r', '\t'], " ")
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn apps_store_sweep_verdict_is_package_scoped_and_never_ingest_authority() {
        let mut entry = super::super::parse_index(include_bytes!(
            "../tests/fixtures/sandstorm-index-2026-10-27.json"
        ))
        .unwrap()
        .remove(0);
        let candidate = "a".repeat(40);
        let mut data = json!({"protocol":"mini-store-qualification-v1","scope":SCOPE,"candidate":candidate,
            "apps":[{"candidate":candidate,"appId":entry.app_id,"packageId":entry.package_id,
            "verdict":"PASS","stage":"get","reason":"HTTP 200","evidence":"hbox:/evidence/test",
            "checkedAt":"2026-10-28T12:00:00Z","importProfile":"standard-v1"}]});
        let q = Qualification::parse(&serde_json::to_vec(&data).unwrap()).unwrap();
        assert!(line(q.get(&entry)).starts_with("known working (lifecycle; candidate aaaaaaaaa)"));
        let local = super::super::verdict(
            Path::new("/nonexistent"),
            Path::new("/nonexistent"),
            &entry.package_id,
        );
        let shown = super::super::qualified_entry_json(&entry, &local, &q);
        assert_eq!(shown["qualification"]["state"], "known-working");
        assert_eq!(shown["verdict"]["state"], "unverified");
        entry.package_id = "f".repeat(32);
        assert!(
            q.get(&entry).is_none(),
            "new package never inherits an old PASS"
        );
        data["apps"][0]["stage"] = json!("install");
        assert!(Qualification::parse(&serde_json::to_vec(&data).unwrap()).is_err());
        data["apps"][0]["verdict"] = json!("FAIL");
        let failed = Qualification::parse(&serde_json::to_vec(&data).unwrap()).unwrap();
        entry.package_id = data["apps"][0]["packageId"].as_str().unwrap().into();
        assert!(line(failed.get(&entry)).starts_with("lifecycle failed at install"));
        data["apps"][0]["candidate"] = json!("b".repeat(40));
        assert!(Qualification::parse(&serde_json::to_vec(&data).unwrap()).is_err());
        assert!(Qualification::parse(b"{}").is_err());
        Qualification::load(None).unwrap();
    }
}
