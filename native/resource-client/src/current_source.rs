//! Pinned local source invocation under the existing receipt custody lock.
//! A readback is physical source evidence; its meaning is validated by the
//! source-specific consumer before the lock is released. No remote fallback.
use super::*;
use sha2::Digest;

#[derive(Clone, Copy)]
pub(crate) enum CurrentSourceOperation {
    CurrentRecipient,
}
impl CurrentSourceOperation {
    // Development approval binds reviewed source/closed contract to the exact
    // linked artifact. This is an explicit trusted release registry, not a
    // binary's self-attestation. Installation cannot supply or extend it.
    fn approval(self, image_sha256: &str) -> Result<(&'static str, &'static str)> {
        match (self, image_sha256) {
            (
                Self::CurrentRecipient,
                "95928d13109b553abfcfd6f51b5b4c29377402eecf54deffa02020245cca113c",
            ) => Ok((
                "minidregg-current-recipient-v1",
                "f72bcf74a8c10e40d3eeb4132f27b22d49a4e55ac82b1f8a015afefaca264970",
            )),
            _ => Err(fail(
                "source helper is not a developer-approved artifact for this closed contract",
            )),
        }
    }
    fn pin_name(self) -> &'static str {
        match self {
            Self::CurrentRecipient => "source-current-recipient.json",
        }
    }
    fn label(self) -> &'static str {
        match self {
            Self::CurrentRecipient => "current-recipient",
        }
    }
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
// A helper is trusted executable code selected explicitly by the local custody
// owner. This record selects code only: it neither creates an anchor nor grants
// publication authority. The full continuity verifier remains in Settings.
struct SourceHelper {
    image: PathBuf,
    sha256: String,
    record: Option<Value>,
}
fn image_pin(value: &str) -> Result<()> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(fail("source helper SHA-256 must be64lowercasehex bytes"));
    }
    Ok(())
}
fn helper_record(
    operation: CurrentSourceOperation,
    image: &Path,
    sha256: &str,
    settings: &Settings,
    config_bytes: &[u8],
) -> Result<Value> {
    image_pin(sha256)?;
    let (contract, cohort) = operation.approval(sha256)?;
    if !image.is_absolute() || image.as_os_str().len() > 4096 {
        return Err(fail("source helper must have a bounded absolute path"));
    }
    Ok(
        json!({"type":"minidregg-current-source-helper-v1", "operation":operation.label(),
        "identity":settings.identity, "image":image, "imageSha256":sha256,
        "approvedContract":contract, "approvedSourceCohort":cohort,
        "configSha256":crate::hex(&sha2::Sha256::digest(config_bytes))}),
    )
}
fn select_helper(
    custody: &Path,
    operation: CurrentSourceOperation,
    settings: &Settings,
    config_bytes: &[u8],
) -> Result<SourceHelper> {
    let path = custody.join(operation.pin_name());
    let record = match fs::symlink_metadata(&path) {
        Ok(_) => read_json(&path)?,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            // The full native verifier may itself implement the closed verbs.
            // There is no lookup of an unpinned latest or remote helper.
            return Ok(SourceHelper {
                image: settings.verifier.clone(),
                sha256: settings.verifier_sha256.clone(),
                record: None,
            });
        }
        Err(e) => return Err(fail(e)),
    };
    let image = PathBuf::from(text(&record, "image")?);
    let sha256 = text(&record, "imageSha256")?.to_owned();
    if record != helper_record(operation, &image, &sha256, settings, config_bytes)? {
        return Err(fail(
            "source helper pin differs from custody deployment/config/purpose",
        ));
    }
    if crate::host_image_sha256(&image)? != sha256 {
        return Err(fail("source helper image changed"));
    }
    Ok(SourceHelper {
        image,
        sha256,
        record: Some(record),
    })
}
fn persist_helper(custody: &Path, operation: CurrentSourceOperation, record: &Value) -> Result<()> {
    let path = custody.join(operation.pin_name());
    match fs::symlink_metadata(&path) {
        Ok(_) if read_json(&path)? == *record => {
            directory(custody)?.sync_all().map_err(fail)?;
        }
        Ok(_) => {
            return Err(fail(
                "source helper pin is immutable; changed input refused",
            ));
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            save(custody, operation.pin_name(), record)?
        }
        Err(e) => return Err(fail(e)),
    }
    Ok(())
}
/// Install once, or reconfirm an exact existing pin. A changed helper requires a
/// separately designed explicit upgrade; ordinary calls cannot replace this pin.
pub(crate) fn pin_helper(
    root: &Path,
    workspace: &Value,
    operation: CurrentSourceOperation,
    image: &Path,
    sha256: &str,
) -> Result<Value> {
    let custody = root.join(DIRECTORY);
    let _lock = lock(&custody)?;
    if read_json(&root.join("workspace.json"))? != *workspace {
        return Err(fail("workspace changed before source helper pin"));
    }
    let settings = Settings::load(&custody)?;
    let config = workspace::member_path(workspace, "config")?;
    settings.check(&config)?;
    let point = anchor(&custody, &settings)?;
    let config_bytes = crate::agent_reserve::bounded(&config, MAX_JSON as usize)?;
    let image = crate::absolute(image)?;
    let record = helper_record(operation, &image, sha256, &settings, &config_bytes)?;
    if crate::host_image_sha256(&image)? != sha256 {
        return Err(fail(
            "source helper does not match explicitly selected image pin",
        ));
    }
    persist_helper(&custody, operation, &record)?;
    if select_helper(&custody, operation, &settings, &config_bytes)?.record != Some(record.clone())
        || Settings::load(&custody)?.json() != settings.json()
        || read_json(&root.join("workspace.json"))? != *workspace
        || crate::agent_reserve::bounded(&config, MAX_JSON as usize)? != config_bytes
        || anchor(&custody, &settings)? != point
    {
        return Err(fail(
            "custody changed during source helper pin; retained pin is not a grant",
        ));
    }
    Ok(record)
}
pub(crate) fn run(mut args: crate::Args) -> Result<()> {
    let root = crate::absolute(&crate::path(args.required("dir")?))?;
    let operation = match args
        .required("kind")?
        .to_str()
        .ok_or_else(|| fail("source helper kind must beUTF8"))?
    {
        "current-recipient" => CurrentSourceOperation::CurrentRecipient,
        _ => {
            return Err(fail(
                "only current-recipient is a qualified source helper kind",
            ));
        }
    };
    let image = crate::path(args.required("verifier")?);
    let sha256 = args
        .required("sha256")?
        .into_string()
        .map_err(|_| fail("source helper SHA-256 must beUTF8"))?;
    args.finish()?;
    let workspace = workspace::load(&root)?;
    crate::print_json(&pin_helper(&root, &workspace, operation, &image, &sha256)?)
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
    let helper = select_helper(&custody, operation, &settings, &config_bytes)?;
    let image_digest: [u8; 32] = crate::decode_hex(&helper.sha256)?
        .try_into()
        .map_err(|_| fail("source helper image digest bound"))?;
    // The three commands execute one held image and Config snapshot. Reopening
    // paths between checks would permit a replace-and-restore execution attack.
    let invocation = crate::transport::PinnedLocalInvocation::new(
        &helper.image,
        &config,
        &image_digest,
        &config_bytes,
    )?;
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
        let status = invocation.status(&[
            std::ffi::OsStr::new(verb),
            std::ffi::OsStr::new(kind),
            source.as_os_str(),
            dest.as_os_str(),
        ])?;
        if !status.success() {
            return Err(fail(format!("pinned local source refused {kind}")));
        }
    }
    let unchanged = || -> Result<()> {
        if crate::host_image_sha256(&settings.verifier)? != settings.verifier_sha256
            || crate::host_image_sha256(&helper.image)? != helper.sha256
            || select_helper(&custody, operation, &settings, &config_bytes)?.record != helper.record
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
    fn current_source_helper_pin_binds_code_config_identity_and_purpose() {
        let root = std::env::temp_dir().join(format!(
            "mini-source-helper-{}",
            workspace::random_nonce().unwrap()
        ));
        workspace::make_private_dir(&root).unwrap();
        let image = root.join("helper");
        create_file(&image, b"not executed by this pinning test").unwrap();
        let sha = crate::host_image_sha256(&image).unwrap();
        let settings = Settings {
            identity: json!({"domain":"3","semantics":"4","expectedSeed":"5"}),
            verifier: PathBuf::from("/original-full-continuity-verifier"),
            verifier_sha256: "old".into(),
        };
        let op = CurrentSourceOperation::CurrentRecipient;
        let fallback = select_helper(&root, op, &settings, b"config").unwrap();
        assert_eq!(fallback.image, settings.verifier);
        // An arbitrary image cannot enroll itself by claiming a contract or
        // echoing a valid identity. The developer registry is independent.
        assert!(helper_record(op, &image, &sha, &settings, b"config").is_err());
        let approved = "95928d13109b553abfcfd6f51b5b4c29377402eecf54deffa02020245cca113c";
        let record = helper_record(op, &image, approved, &settings, b"config").unwrap();
        assert_eq!(record["approvedContract"], "minidregg-current-recipient-v1");
        assert_eq!(
            record["approvedSourceCohort"],
            "f72bcf74a8c10e40d3eeb4132f27b22d49a4e55ac82b1f8a015afefaca264970"
        );
        persist_helper(&root, op, &record).unwrap();
        persist_helper(&root, op, &record).unwrap();
        assert_eq!(read_json(&root.join(op.pin_name())).unwrap(), record);
        // A record naming approved code still refuses a different file image.
        assert!(select_helper(&root, op, &settings, b"config").is_err());
        assert!(select_helper(&root, op, &settings, b"changed config").is_err());
        let mut other = settings.clone();
        other.identity["expectedSeed"] = json!("6");
        assert!(select_helper(&root, op, &other, b"config").is_err());
        let mut changed = record.clone();
        changed["imageSha256"] = json!("0".repeat(64));
        assert!(persist_helper(&root, op, &changed).is_err());
        fs::write(&image, b"changed image").unwrap();
        assert!(select_helper(&root, op, &settings, b"config").is_err());
        assert!(helper_record(op, Path::new("relative"), &sha, &settings, b"config").is_err());
        assert!(helper_record(op, &image, "A".repeat(64).as_str(), &settings, b"config").is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn current_source_helper_incomplete_or_aliased_pin_never_falls_back() {
        use std::os::unix::fs::symlink;
        let root = std::env::temp_dir().join(format!(
            "mini-source-helper-{}",
            workspace::random_nonce().unwrap()
        ));
        workspace::make_private_dir(&root).unwrap();
        let settings = Settings {
            identity: json!({"domain":"3","semantics":"4","expectedSeed":"5"}),
            verifier: PathBuf::from("/original"),
            verifier_sha256: "old".into(),
        };
        let op = CurrentSourceOperation::CurrentRecipient;
        let path = root.join(op.pin_name());
        create_file(&path, b"{unfinished").unwrap();
        assert!(select_helper(&root, op, &settings, b"config").is_err());
        assert!(persist_helper(&root, op, &json!({})).is_err());
        fs::remove_file(&path).unwrap();
        symlink(root.join("missing"), &path).unwrap();
        assert!(select_helper(&root, op, &settings, b"config").is_err());
        assert!(persist_helper(&root, op, &json!({})).is_err());
        fs::remove_dir_all(root).unwrap();
    }
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
