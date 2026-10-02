//! Fresh signed reads tolerate bounded shared-Store contention. Only a retained
//! op-5 stale-root refusal retries; no prompt, native submit or financial call
//! is repeated here. Every read gets a fresh journal counter and directory.
use super::*;

const MAX_FRESH_READS: usize = 3;
enum ReadError {
    Stale(String),
    Other(String),
}
impl From<String> for ReadError {
    fn from(value: String) -> Self {
        Self::Other(value)
    }
}
impl From<&str> for ReadError {
    fn from(value: &str) -> Self {
        Self::Other(value.into())
    }
}

fn fresh_read<T>(mut read: impl FnMut() -> std::result::Result<T, ReadError>) -> Result<T> {
    for round in 0..MAX_FRESH_READS {
        match read() {
            Ok(value) => return Ok(value),
            Err(ReadError::Stale(error)) if round + 1 == MAX_FRESH_READS => {
                return Err(format!("signed query remained stale after {MAX_FRESH_READS} fresh observations: {error}"));
            }
            Err(ReadError::Stale(_)) => {}
            Err(ReadError::Other(error)) => return Err(error),
        }
    }
    unreachable!("bounded reads always return on the last attempt")
}

fn absent(path: &Path) -> Result<()> {
    match fs::symlink_metadata(path) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Ok(_) => Err(format!(
            "query refusal contains later-stage artifact {}",
            path.display()
        )),
        Err(error) => Err(format!("query refusal artifact stat: {error}")),
    }
}

/// Classification is from the pinned Host's decoding, never stderr. A missing
/// marker (including older Mini clients) leaves the original error untouched.
fn stale_query_with(
    config: &Config,
    attempt: &Path,
    source: &[u8],
    inspect: impl FnOnce(&[u8]) -> Result<Value>,
) -> Result<bool> {
    stale_query_via_with(config, config.host_socket.as_deref(), attempt, source, inspect)
}
fn stale_query_via_with(
    config: &Config,
    expected_socket: Option<&Path>,
    attempt: &Path,
    source: &[u8],
    inspect: impl FnOnce(&[u8]) -> Result<Value>,
) -> Result<bool> {
    let marker_path = attempt.join("query-refusal.json");
    match fs::symlink_metadata(&marker_path) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(false),
        Err(e) => return Err(format!("query refusal marker stat: {e}")),
        Ok(_) => {}
    }
    let marker: Value = serde_json::from_slice(&bounded_regular_file(&marker_path, 65_536)?)
        .map_err(|e| format!("query refusal marker JSON: {e}"))?;
    if marker["type"] != "minidregg-query-refusal-v1"
        || marker["stage"] != "query"
        || marker["operation"] != 5
    {
        return Err("query refusal marker is not an op-5 decision".into());
    }
    let manifest_path = attempt.join("attempt.json");
    let manifest: Value = serde_json::from_slice(&bounded_regular_file(&manifest_path, 65_536)?)
        .map_err(|e| format!("query refusal manifest JSON: {e}"))?;
    let copied_config = attempt.join("config.json");
    if expected_socket.is_none()
        || manifest["format"] != "minidregg-resource-client-attempt-v1"
        || manifest["operation"] != "query"
        || manifest["host"].as_str().map(Path::new) != Some(config.host.as_path())
        || manifest["config"].as_str().map(Path::new) != Some(copied_config.as_path())
        || manifest["socket"].as_str().map(Path::new) != expected_socket
        || bounded_regular_file(&copied_config, 65_536)?
            != bounded_regular_file(&config.host_config, 65_536)?
        || bounded_regular_file(&attempt.join("intent.json"), 65_536)? != source
    {
        return Err("query refusal does not bind this pinned read".into());
    }
    for name in [
        "view.bin",
        "view.json",
        "plan.bin",
        "call.bin",
        "outcome.bin",
        "outcome.json",
    ] {
        absent(&attempt.join(name))?;
    }
    for (name, field, limit) in [
        ("query-refusal.frame", "frameSha256", 12_102_761),
        ("signed-observation.bin", "requestSha256", 12_102_760),
        ("config.json", "hostConfigSha256", 65_536),
        ("attempt.json", "attemptManifestSha256", 65_536),
    ] {
        let path = attempt.join(name);
        let bytes = bounded_regular_file(&path, limit)?;
        if bytes.is_empty() || marker[field].as_str() != Some(sha256_file(&path)?.as_str()) {
            return Err(format!(
                "query refusal {field} differs from retained artifact"
            ));
        }
    }
    let frame = bounded_regular_file(&attempt.join("query-refusal.frame"), 12_102_761)?;
    if frame.len() < 2 || frame[0] != 255 {
        return Err("query refusal is not an op-255 frame".into());
    }
    let refusal = inspect(&frame[1..])?;
    Ok(refusal["type"] == "refused" && refusal["reason"] == "stale-root")
}

impl Runtime {
    pub(super) fn query_observation_as(&mut self, authority: &Authority) -> Result<Value> {
        self.query_observation_via(authority, None)
    }
    pub(super) fn query_observation_via(&mut self, authority: &Authority,
        transport: Option<&quiescence_transport::AuthorizedTransport>) -> Result<Value> {
        fresh_read(|| self.query_observation_once(authority, false, transport))
    }
    pub(super) fn query_policy_observation(&mut self) -> Result<Value> {
        let authority = self.parent();
        fresh_read(|| self.query_observation_once(&authority, true, None))
    }
    fn query_observation_once(
        &mut self,
        authority: &Authority,
        policy: bool,
        transport: Option<&quiescence_transport::AuthorizedTransport>,
    ) -> std::result::Result<Value, ReadError> {
        if let Some(via) = transport {
            via.assert_bound(&self.config, &self.config_path, &self.journal.binding)?;
        }
        let query_socket = transport.map(|via| via.socket().to_owned())
            .or_else(|| self.config.host_socket.clone());
        let id = self.next_id()?;
        let prefix = if policy { "policy-query" } else { "query" };
        let view_kind = if policy { "policy" } else { "resource" };
        let dir = self.config.state_dir.join(format!("{prefix}-{id:016}"));
        fs::create_dir(&dir).map_err(|e| format!("query directory: {e}"))?;
        let source=serde_json::to_vec_pretty(&json!({"subject":authority.subject,"nonce":id.to_string(),
            "purpose":{"type":"query","kind":"object","target":authority.task,"view":view_kind},
            "grants":[{"kind":"object","target":authority.task,"capability":authority.query_capability}]}))
            .map_err(|e| e.to_string())?;
        let source_path = dir.join("intent-source.json");
        write_new(&source_path, &source)?;
        let attempt = dir.join("attempt");
        let cfg = &self.config;
        let mut args = vec![
            "query",
            "--host",
            cfg.host.to_str().ok_or("host path UTF-8")?,
            "--config",
            cfg.host_config.to_str().ok_or("config path UTF-8")?,
            "--intent",
            source_path.to_str().ok_or("query source path UTF-8")?,
            "--key",
            authority.custody_key.to_str().ok_or("key path UTF-8")?,
            "--view",
            view_kind,
            "--dir",
            attempt.to_str().ok_or("query attempt path UTF-8")?,
        ];
        if let Some(socket) = &query_socket {
            args.extend(["--socket", socket.to_str().ok_or("socket path UTF-8")?]);
        }
        if let Err(error) = self.command_output(&cfg.mini, &args) {
            let stale = stale_query_via_with(cfg, query_socket.as_deref(), &attempt, &source, |body| {
                let binary = attempt.join("query-refusal-inspect.bin");
                let decoded = attempt.join("query-refusal-inspect.json");
                write_new(&binary, body)?;
                self.command_output(
                    &cfg.host,
                    &[
                        cfg.host_config.to_str().ok_or("config path UTF-8")?,
                        "inspect",
                        "outcome",
                        binary.to_str().ok_or("refusal path UTF-8")?,
                        decoded.to_str().ok_or("refusal decode path UTF-8")?,
                    ],
                )?;
                serde_json::from_slice(&bounded_regular_file(&decoded, 65_536)?)
                    .map_err(|e| format!("query refusal Host decoding: {e}"))
            })
            .map_err(|e| ReadError::Other(format!("{error}; query refusal evidence: {e}")))?;
            return Err(if stale {
                ReadError::Stale(error)
            } else {
                ReadError::Other(error)
            });
        }
        let view: Value = serde_json::from_slice(
            &fs::read(attempt.join("view.json")).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        let challenge: Value = serde_json::from_slice(
            &fs::read(attempt.join("challenge.json")).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        if policy {
            if view["policyId"].as_str() != Some(authority.task.as_str()) {
                return Err("signed policy view names another task".into());
            }
            Ok(json!({"view":view,"authorityRoot":challenge.get("authorityRoot")}))
        } else {
            let grain = view
                .pointer("/cell/grain")
                .ok_or("signed resource view has no grain")?;
            if grain["task"].as_str() != Some(authority.task.as_str()) {
                return Err("signed resource view names another task".into());
            }
            Ok(
                json!({"grain":grain,"targetRoot":view.pointer("/cell/root"),
                "authorityRoot":challenge.get("authorityRoot"),"worldRoot":challenge.get("worldRoot"),"height":challenge.get("height")}),
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture() -> (PathBuf, Config, PathBuf) {
        let root = std::env::temp_dir().join(format!(
            "grain-query-observation-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&root).unwrap();
        let config:Config=serde_json::from_value(json!({"mini":root.join("mini"),"host":root.join("host"),
            "hostConfig":root.join("host.json"),"hostSocket":root.join("host.sock"),
            "controlSocket":root.join("control.sock"),"custodyKey":root.join("unused.key"),
            "stateDir":root,"cwd":root,"task":"10","subject":"7","capability":"71", "queryCapability":"71","commands":[]})).unwrap();
        fs::write(&config.host_config, b"config").unwrap();
        let attempt = root.join("attempt");
        fs::create_dir(&attempt).unwrap();
        fs::write(attempt.join("config.json"), b"config").unwrap();
        fs::write(attempt.join("intent.json"), b"source").unwrap();
        fs::write(attempt.join("signed-observation.bin"), b"signed").unwrap();
        fs::write(attempt.join("query-refusal.frame"), b"\xffencoded").unwrap();
        fs::write(attempt.join("attempt.json"),serde_json::to_vec(&json!({"format":"minidregg-resource-client-attempt-v1",
            "operation":"query","host":config.host,"config":attempt.join("config.json"),"socket":config.host_socket})).unwrap()).unwrap();
        let mut marker = json!({"type":"minidregg-query-refusal-v1","stage":"query","operation":5});
        for (name, field) in [
            ("query-refusal.frame", "frameSha256"),
            ("signed-observation.bin", "requestSha256"),
            ("config.json", "hostConfigSha256"),
            ("attempt.json", "attemptManifestSha256"),
        ] {
            marker[field] = json!(sha256_file(&attempt.join(name)).unwrap());
        }
        fs::write(
            attempt.join("query-refusal.json"),
            serde_json::to_vec(&marker).unwrap(),
        )
        .unwrap();
        (root, config, attempt)
    }
    #[test]
    fn only_exact_host_decoded_stale_query_can_retry() {
        let (root, cfg, attempt) = fixture();
        for (reason, expected) in [
            ("stale-root", true),
            ("revoked", false),
            ("predicate", false),
            ("unknown", false),
        ] {
            assert_eq!(
                stale_query_with(&cfg, &attempt, b"source", |body| {
                    assert_eq!(body, b"encoded");
                    Ok(json!({"type":"refused","reason":reason}))
                })
                .unwrap(),
                expected
            );
        }
        assert!(!stale_query_with(&cfg, &attempt, b"source", |_| Ok(
            json!({"type":"uncertain","reason":"stale-root"})
        ))
        .unwrap());
        assert!(stale_query_with(&cfg, &attempt, b"other", |_| panic!(
            "changed source must not reach Host"
        ))
        .is_err());
        fs::write(attempt.join("signed-observation.bin"), b"changed").unwrap();
        assert!(stale_query_with(&cfg, &attempt, b"source", |_| panic!(
            "changed request must not reach Host"
        ))
        .is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn admitted_query_transport_keeps_refusal_bound_to_actual_socket() {
        let (root, cfg, attempt) = fixture();
        let management = root.join("management.sock");
        let manifest_path = attempt.join("attempt.json");
        let mut manifest: Value = serde_json::from_slice(&fs::read(&manifest_path).unwrap()).unwrap();
        manifest["socket"] = json!(management);
        fs::write(&manifest_path, serde_json::to_vec(&manifest).unwrap()).unwrap();
        let marker_path = attempt.join("query-refusal.json");
        let mut marker: Value = serde_json::from_slice(&fs::read(&marker_path).unwrap()).unwrap();
        marker["attemptManifestSha256"] = json!(sha256_file(&manifest_path).unwrap());
        fs::write(marker_path, serde_json::to_vec(&marker).unwrap()).unwrap();
        assert!(stale_query_with(&cfg,&attempt,b"source", |_| panic!("wrong socket must refuse before decoding")).is_err());
        assert!(stale_query_via_with(&cfg,Some(&management),&attempt,b"source", |_| Ok(json!({"type":"refused","reason":"stale-root"}))).unwrap());
        assert_eq!(cfg.host_socket,Some(root.join("host.sock")));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn missing_marker_and_later_stage_artifacts_never_retry() {
        let (root, cfg, attempt) = fixture();
        std::os::unix::fs::symlink(root.join("missing"), attempt.join("call.bin")).unwrap();
        assert!(stale_query_with(&cfg, &attempt, b"source", |_| panic!(
            "call must fail closed"
        ))
        .is_err());
        fs::remove_file(attempt.join("call.bin")).unwrap();
        fs::remove_file(attempt.join("query-refusal.json")).unwrap();
        assert!(!stale_query_with(&cfg, &attempt, b"source", |_| panic!(
            "missing evidence must not inspect"
        ))
        .unwrap());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn contention_is_bounded_and_client_errors_stop_immediately() {
        let mut calls = 0;
        let result: Result<()> = fresh_read(|| {
            calls += 1;
            Err(ReadError::Stale("retained op5".into()))
        });
        assert!(result.unwrap_err().contains("3 fresh observations"));
        assert_eq!(calls, 3);
        calls = 0;
        let result: Result<()> = fresh_read(|| {
            calls += 1;
            Err(ReadError::Other(
                "stale-root text without typed evidence".into(),
            ))
        });
        assert!(result.is_err());
        assert_eq!(calls, 1);
        calls = 0;
        assert_eq!(
            fresh_read(|| {
                calls += 1;
                if calls == 1 {
                    Err(ReadError::Stale("old root".into()))
                } else {
                    Ok(42)
                }
            })
            .unwrap(),
            42
        );
        assert_eq!(calls, 2);
    }

    #[test]
    fn runtime_retries_with_fresh_source_and_preserves_the_failed_attempt() {
        let (root, cfg, seed) = fixture();
        let first = root.join("query-0000000000000001/attempt");
        let source = serde_json::to_vec_pretty(&json!({"subject":"7","nonce":"1",
            "purpose":{"type":"query","kind":"object","target":"10","view":"resource"},
            "grants":[{"kind":"object","target":"10","capability":"71"}]}))
        .unwrap();
        fs::write(seed.join("intent.json"), &source).unwrap();
        let manifest_path = seed.join("attempt.json");
        let mut manifest: Value =
            serde_json::from_slice(&fs::read(&manifest_path).unwrap()).unwrap();
        manifest["config"] = json!(first.join("config.json"));
        fs::write(&manifest_path, serde_json::to_vec(&manifest).unwrap()).unwrap();
        let marker_path = seed.join("query-refusal.json");
        let mut marker: Value = serde_json::from_slice(&fs::read(&marker_path).unwrap()).unwrap();
        marker["attemptManifestSha256"] = json!(sha256_file(&manifest_path).unwrap());
        fs::write(&marker_path, serde_json::to_vec(&marker).unwrap()).unwrap();
        let mini = r#"#!/bin/sh
set -eu
[ "$1" = query ] || exit 90
shift
dir=
view=
while [ "$#" -gt 0 ]; do
  case "$1" in
    --dir) dir=$2; shift 2 ;;
    --view) view=$2; shift 2 ;;
    *) shift ;;
  esac
done
mkdir "$dir"
case "$dir" in
  */query-0000000000000001/attempt)
    cp '__SEED__/'* "$dir/"
    echo 'typed Host refusal is retained; this text is irrelevant' >&2
    exit 3 ;;
esac
if [ "$view" = policy ]; then
  printf '%s' '{"policyId":"10"}' > "$dir/view.json"
else
  printf '%s' '{"cell":{"root":"fresh-root","grain":{"task":"10","generation":"1","status":"1","remaining":"8","reserved":"0"}}}' > "$dir/view.json"
fi
printf '%s' '{"authorityRoot":"authority","worldRoot":"new-world","height":"10"}' > "$dir/challenge.json"
"#.replace("__SEED__",seed.to_str().unwrap());
        let host = r#"#!/bin/sh
set -eu
[ "$2" = inspect ] && [ "$3" = outcome ] || exit 91
printf '%s' '{"type":"refused","reason":"stale-root"}' > "$5"
"#;
        fs::write(&cfg.mini, mini).unwrap();
        fs::write(&cfg.host, host).unwrap();
        for program in [&cfg.mini, &cfg.host] {
            fs::set_permissions(program, fs::Permissions::from_mode(0o700)).unwrap();
        }
        let mut runtime = Runtime::open(cfg, root.join("controller-config.json")).unwrap();
        let observed = runtime.query_observation_as(&runtime.parent()).unwrap();
        assert_eq!(observed["targetRoot"], "fresh-root");
        assert_eq!(runtime.journal.next_operation_id, 3);
        for (number, nonce) in [(1, "1"), (2, "2")] {
            let source: Value = serde_json::from_slice(
                &fs::read(root.join(format!("query-{number:016}/intent-source.json"))).unwrap(),
            )
            .unwrap();
            assert_eq!(source["nonce"], nonce);
            assert_eq!(source.pointer("/purpose/type").unwrap(), "query");
        }
        assert_eq!(
            fs::read(first.join("query-refusal.frame")).unwrap(),
            b"\xffencoded"
        );
        assert_eq!(fs::read(first.join("intent.json")).unwrap(), source);
        assert!(!first.join("view.json").exists());
        assert_eq!(
            runtime.query_policy_observation().unwrap()["view"]["policyId"],
            "10"
        );
        assert!(root
            .join("policy-query-0000000000000003/attempt/view.json")
            .exists());
        assert!(runtime.journal.pending.is_none() && runtime.journal.provider_pending.is_none());
        drop(runtime);
        fs::remove_dir_all(root).unwrap();
    }
}
