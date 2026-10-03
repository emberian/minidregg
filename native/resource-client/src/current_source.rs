//! Pinned local source invocation under the existing receipt custody lock.
//! A readback is physical source evidence; its meaning is validated by the
//! source-specific consumer before the lock is released. No remote fallback.
use super::*;

#[derive(Clone, Copy)]
pub(crate) enum CurrentSourceOperation {
    CurrentRecipient,
}
impl CurrentSourceOperation {
    fn names(self) -> (&'static str, &'static str, &'static str) {
        match self {
            Self::CurrentRecipient => (
                "current-recipient-query",
                "current-recipient",
                "current-recipient-readback",
            ),
        }
    }
}
pub(crate) struct CurrentSourceReadback {
    view: Value,
    exact_query: Vec<u8>,
    exact_readback: Vec<u8>,
    custody_point: Value,
    source_identity: Value,
}
impl CurrentSourceReadback {
    pub(crate) fn view(&self) -> &Value {
        &self.view
    }
    pub(crate) fn exact_query(&self) -> &[u8] {
        &self.exact_query
    }
    pub(crate) fn exact_readback(&self) -> &[u8] {
        &self.exact_readback
    }
    pub(crate) fn custody_point(&self) -> &Value {
        &self.custody_point
    }
    pub(crate) fn source_identity(&self) -> &Value {
        &self.source_identity
    }
}
fn nat(value: &str) -> Result<Value> {
    decimal(value)?;
    serde_json::from_str(value).map_err(fail)
}
fn bounded_output(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let f = OpenOptions::new()
        .read(true)
        .custom_flags(NOFOLLOW)
        .open(path)
        .map_err(fail)?;
    private_metadata(&f, false)?;
    if f.metadata().map_err(fail)?.len() > limit as u64 {
        return Err(fail("local source output exceeds bound"));
    }
    let mut b = Vec::new();
    f.take((limit + 1) as u64)
        .read_to_end(&mut b)
        .map_err(fail)?;
    if b.is_empty() || b.len() > limit {
        return Err(fail("local source output empty or oversized"));
    }
    Ok(b)
}
fn bind_input(mut input: Value, point: &Point) -> Result<Vec<u8>> {
    let object = input
        .as_object_mut()
        .ok_or_else(|| fail("local source input must be an object"))?;
    // The consumer chooses scope only; it cannot choose the custody point.
    if object.contains_key("pointHeight") || object.contains_key("pointRoot") {
        return Err(fail(
            "local source custody point is selected by its locked runner",
        ));
    }
    object.insert("pointHeight".into(), nat(&point.height)?);
    object.insert("pointRoot".into(), json!(point.world_root));
    let bytes = serde_json::to_vec(&input).map_err(fail)?;
    if bytes.len() > 4096 {
        return Err(fail("local source input exceeds bound"));
    }
    Ok(bytes)
}
fn bind_readback(
    view: Value,
    query: Vec<u8>,
    raw: Vec<u8>,
    settings: &Settings,
    point: &Point,
) -> Result<CurrentSourceReadback> {
    if view["queryHex"] != json!(crate::hex(&query))
        || view["domain"] != settings.identity["domain"]
        || view["semantics"] != settings.identity["semantics"]
        || view["pointHeight"] != nat(&point.height)?
        || view["pointRoot"] != json!(point.world_root)
    {
        return Err(fail(
            "local source readback differs from exact selected request/deployment/point",
        ));
    }
    Ok(CurrentSourceReadback {
        view,
        exact_query: query,
        exact_readback: raw,
        custody_point: point.json(),
        source_identity: settings.identity.clone(),
    })
}
/// Only confirmed, source-owned verb triples can be selected. The validator runs
/// under the same custody lock and returns its own private typed token; this
/// runner does not interpret a JSON Boolean as permission or admit a Mini effect.
pub(crate) fn with_current_source<T>(
    root: &Path,
    workspace: &Value,
    operation: CurrentSourceOperation,
    input: Value,
    validate: impl FnOnce(&CurrentSourceReadback) -> Result<T>,
) -> Result<T> {
    let custody = root.join(DIRECTORY);
    let _lock = lock(&custody)?;
    if read_json(&root.join("workspace.json"))? != *workspace {
        return Err(fail("workspace changed before local source verification"));
    }
    let settings = Settings::load(&custody)?;
    let config = workspace::member_path(workspace, "config")?;
    settings.check(&config)?;
    let point = anchor(&custody, &settings)?;
    let config_bytes = crate::agent_reserve::bounded(&config, MAX_JSON as usize)?;
    let input = bind_input(input, &point)?;
    let attempts = root.join("attempts");
    directory(&attempts)?;
    let scratch = attempts.join(format!("source-read-{}", workspace::random_nonce()?));
    workspace::make_private_dir(&scratch)?;
    let input_path = scratch.join("input.json");
    let query_path = scratch.join("query.bin");
    let readback_path = scratch.join("readback.bin");
    let json_path = scratch.join("readback.json");
    create_file(&input_path, &input)?;
    for path in [&query_path, &readback_path, &json_path] {
        create_file(path, b"")?;
    }
    let (author, inspect, readback) = operation.names();
    for (verb, kind, source, dest) in [
        ("author", author, &input_path, &query_path),
        ("inspect", inspect, &query_path, &readback_path),
        ("inspect", readback, &readback_path, &json_path),
    ] {
        let status = Command::new(&settings.verifier)
            .arg(&config)
            .arg(verb)
            .arg(kind)
            .arg(source)
            .arg(dest)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .map_err(fail)?;
        if !status.success() {
            return Err(fail(format!("pinned local source refused {kind}")));
        }
    }
    let unchanged = || -> Result<()> {
        if crate::host_image_sha256(&settings.verifier)? != settings.verifier_sha256
            || crate::agent_reserve::bounded(&config, MAX_JSON as usize)? != config_bytes
            || read_json(&root.join("workspace.json"))? != *workspace
            || Settings::load(&custody)?.json() != settings.json()
            || anchor(&custody, &settings)? != point
        {
            return Err(fail(
                "custody inputs changed during local source verification",
            ));
        }
        Ok(())
    };
    unchanged()?;
    let query = bounded_output(&query_path, 4096)?;
    let raw = bounded_output(&readback_path, 8192)?;
    let view = serde_json::from_slice(&bounded_output(&json_path, 8192)?).map_err(fail)?;
    let readback = bind_readback(view, query, raw, &settings, &point)?;
    let token = validate(&readback)?;
    unchanged()?;
    Ok(token)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn current_source_runner_selects_point_and_binds_complete_readback() {
        let settings = Settings {
            identity: json!({"domain":"3","semantics":"4"}),
            verifier: "/source".into(),
            verifier_sha256: "pin".into(),
        };
        let point = Point {
            height: "18446744073709551619".into(),
            world_root: "340282366920938463463374607431768211457".into(),
            witness: None,
        };
        let input: Value =
            serde_json::from_slice(&bind_input(json!({"room":9}), &point).unwrap()).unwrap();
        assert_eq!(input["pointHeight"], nat(&point.height).unwrap());
        assert_eq!(input["pointRoot"], json!(point.world_root));
        assert!(bind_input(json!({"pointHeight":1}), &point).is_err());
        assert!(bind_input(json!({"pointRoot":"0"}), &point).is_err());
        assert!(bind_input(json!({"body":"x".repeat(4096)}), &point).is_err());
        let view = json!({"queryHex":"010203","domain":"3","semantics":"4","pointHeight":nat(&point.height).unwrap(),"pointRoot":point.world_root});
        assert!(bind_readback(view.clone(), vec![1, 2, 3], vec![4], &settings, &point).is_ok());
        for field in [
            "queryHex",
            "domain",
            "semantics",
            "pointHeight",
            "pointRoot",
        ] {
            let mut wrong = view.clone();
            wrong[field] = json!("changed");
            assert!(bind_readback(wrong, vec![1, 2, 3], vec![4], &settings, &point).is_err());
        }
    }
}
