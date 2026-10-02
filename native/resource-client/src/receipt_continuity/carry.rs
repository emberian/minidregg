//! Explicit operator-authorized identity transitions. The trusted local verifier
//! checks public signatures and commitments; private semantic audit remains with
//! the operator receiver. This module owns client custody and durable adoption.
mod verifier;
use super::*;
pub(crate) use verifier::install as install_verifier;

const EDGE: &str = "minidregg-carry-edge-v1";
const WAL: &str = "carry-pending.json";
const AUTHORITY: &str = "carry-authority.json";

fn hex64(value: &str) -> Result<()> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
    {
        return Err(fail(
            "carry key or image digest must be 64 lowercase hex characters",
        ));
    }
    Ok(())
}
fn full(point: &Point) -> Result<Value> {
    let (chain, siblings) = point
        .witness
        .as_ref()
        .ok_or_else(|| fail("carry point lacks witness"))?;
    if siblings.len() != 256 {
        return Err(fail("carry point requires exactly 256 system siblings"));
    }
    Ok(
        json!({"height":point.height,"worldRoot":point.world_root,"logChain":chain,"systemSiblings":siblings}),
    )
}
fn point(value: &Value) -> Result<Point> {
    let point = Point::parse(value)?
        .with_witness(&json!({"chain":value["logChain"],"siblings":value["systemSiblings"]}))?;
    full(&point)?;
    Ok(point)
}
fn next_height(height: &str) -> String {
    let mut digits = height.as_bytes().to_vec();
    for byte in digits.iter_mut().rev() {
        if *byte < b'9' {
            *byte += 1;
            return String::from_utf8(digits).unwrap();
        }
        *byte = b'0';
    }
    digits.insert(0, b'1');
    String::from_utf8(digits).unwrap()
}
fn same_manifest(root: &Path, workspace: &Value) -> Result<()> {
    if read_json(&root.join("workspace.json"))? != *workspace {
        return Err(fail(
            "workspace changed; reload before carrying or issuing requests",
        ));
    }
    Ok(())
}
fn anchor_json(settings: &Settings, point: &Point) -> Result<Value> {
    let (chain, siblings) = point
        .witness
        .as_ref()
        .ok_or_else(|| fail("carry endpoint lacks opening"))?;
    Ok(json!({"identity":settings.identity,"point":point.json(),"chain":chain,"siblings":siblings}))
}

/// Must run while holding the existing custody lock. Only a previously verified,
/// durably recorded transition can be completed; there is no bootstrap fallback.
pub(super) fn recover_locked(root: &Path) -> Result<()> {
    recover_with(root, |_| Ok(()))
}
fn recover_with(root: &Path, mut checkpoint: impl FnMut(&str) -> Result<()>) -> Result<()> {
    let custody = root.join(DIRECTORY);
    match fs::symlink_metadata(custody.join(WAL)) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(fail(error)),
        Ok(_) => (),
    }
    let mut wal = read_json(&custody.join(WAL))?;
    if text(&wal, "type")? != "minidregg-carry-transition-v1" {
        return Err(fail("unknown carry recovery record"));
    }
    if text(&wal, "phase")? == "complete" {
        return Ok(());
    }
    let id = text(&wal, "id")?;
    decimal(id)?;
    let lineage = custody.join("lineages").join(id);
    // The immutable lineage evidence was synced before the WAL became visible.
    if read_json(&lineage.join("transition.json"))? != wal["transition"] {
        return Err(fail(
            "carry recovery evidence differs from recorded transition",
        ));
    }
    let transition = wal["transition"].clone();
    validate_transition(&transition)?;
    // Refuse unrecorded concurrent changes before any recovery write. Every
    // component may independently be old or new after a process/power failure.
    for (base, filename, name) in [
        (custody.as_path(), "enabled.json", "settings"),
        (custody.as_path(), "anchor.json", "anchor"),
        (root, "workspace.json", "manifest"),
        (custody.as_path(), AUTHORITY, "authority"),
    ] {
        let current = read_json(&base.join(filename))?;
        if current != transition["old"][name] && current != transition["next"][name] {
            return Err(fail(format!(
                "carry recovery found an unrecorded {name}; restore exact custody"
            )));
        }
    }
    for (base, filename, name) in [
        (custody.as_path(), "enabled.json", "settings"),
        (custody.as_path(), "anchor.json", "anchor"),
        (root, "workspace.json", "manifest"),
        (custody.as_path(), AUTHORITY, "authority"),
    ] {
        save(base, filename, &transition["next"][name])?;
        checkpoint(name)?;
        wal["phase"] = json!(name);
        save(&custody, WAL, &wal)?;
    }
    wal["phase"] = json!("complete");
    save(&custody, WAL, &wal)?;
    checkpoint("complete")
}
fn validate_transition(value: &Value) -> Result<()> {
    let old = &value["old"];
    let next = &value["next"];
    let result = &value["verifiedEdge"];
    let cut = point(&result["oldCut"])?;
    let start = point(&result["newStart"])?;
    let old_anchor = Point::parse(&old["anchor"]["point"])?.with_witness(&old["anchor"])?;
    if text(result, "algorithm")? != EDGE
        || result["oldIdentity"] != old["settings"]["identity"]
        || result["newIdentity"] != next["settings"]["identity"]
        || result["newIdentity"]["domain"] != result["oldIdentity"]["domain"]
        || result["newIdentity"]["expectedSeed"] != result["oldIdentity"]["expectedSeed"]
        || old["anchor"]["identity"] != old["settings"]["identity"]
        || next["anchor"]["identity"] != next["settings"]["identity"]
        || Point::parse(&next["anchor"]["point"])? != start
        || next["anchor"]["chain"] != result["newStart"]["logChain"]
        || next["anchor"]["siblings"] != result["newStart"]["systemSiblings"]
        || compare(&cut.height, &old_anchor.height) == Ordering::Less
        || start.height != next_height(&cut.height)
        || result["operatorPublicKey"] != old["authority"]["operatorPublicKey"]
        || result["targetVerifierDigest"] != next["settings"]["verifierSha256"]
        || old["manifest"]["freshContinuity"] != next["manifest"]["freshContinuity"]
        || next["manifest"]["receiptContinuity"] != ALGORITHM
        || next["authority"] != Value::Null
    {
        return Err(fail("carry recovery transition bindings disagree"));
    }
    Ok(())
}
/// Explicit local authorization. A server response never gets to choose this key.
pub(crate) fn pin_authority(root: &Path, workspace: &Value, key: &str) -> Result<Value> {
    hex64(key)?;
    let custody = root.join(DIRECTORY);
    let _lock = lock(&custody)?;
    recover_locked(root)?;
    same_manifest(root, workspace)?;
    let settings = Settings::load(&custody)?;
    settings.check(&workspace::member_path(workspace, "config")?)?;
    let retained = anchor(&custody, &settings)?;
    let (capsule, pins) = register_capsule(
        &custody,
        &settings,
        &workspace::member_path(workspace, "config")?,
    )?;
    let pin = json!({"type":"minidregg-carry-authority-v1","identity":settings.identity,
        "anchor":full(&retained)?,"operatorPublicKey":key,"sourceCapsulePath":capsule,"sourceCapsulePins":pins});
    save(&custody, AUTHORITY, &pin)?;
    Ok(
        json!({"type":"minidregg-carry-authority-pinned-v1","identity":settings.identity,"point":retained.json(),"operatorPublicKey":key,"sourceCapsulePath":capsule}),
    )
}
fn check_result(
    result: &Value,
    old: &Settings,
    retained: &Point,
    pin: &Value,
    replacement: &Settings,
) -> Result<(Point, Point)> {
    let cut = point(&result["oldCut"])?;
    let start = point(&result["newStart"])?;
    for name in ["bodyDigest", "originIndexDigest"] {
        decimal(text(result, name)?)?;
    }
    hex64(text(result, "operatorPublicKey")?)?;
    hex64(text(result, "targetVerifierDigest")?)?;
    if text(result, "algorithm")? != EDGE
        || result["oldIdentity"] != old.identity
        || result["newIdentity"] != replacement.identity
        || replacement.identity["domain"] != old.identity["domain"]
        || replacement.identity["expectedSeed"] != old.identity["expectedSeed"]
        || result["operatorPublicKey"] != pin["operatorPublicKey"]
        || result["targetVerifierDigest"] != replacement.verifier_sha256
        || compare(&cut.height, &retained.height) == Ordering::Less
        || (cut.height == retained.height && cut != *retained)
        || start.height != next_height(&cut.height)
    {
        return Err(fail(
            "carry verifier result does not bind the locally selected transition",
        ));
    }
    Ok((cut, start))
}
fn copy_config(source: &Path, destination: &Path) -> Result<()> {
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(NOFOLLOW)
        .open(source)
        .map_err(fail)?;
    let metadata = file.metadata().map_err(fail)?;
    if !metadata.is_file() || metadata.len() > MAX_JSON {
        return Err(fail("configuration exceeds bound or is not a regular file"));
    }
    let mut bytes = Vec::new();
    (&mut file)
        .take(MAX_JSON + 1)
        .read_to_end(&mut bytes)
        .map_err(fail)?;
    if bytes.len() as u64 > MAX_JSON {
        return Err(fail("configuration exceeded bound while copying"));
    }
    create_file(destination, &bytes)
}

pub(crate) fn migrate(
    root: &Path,
    workspace: &Value,
    edge: &Path,
    capsule: &Path,
    new_config: &Path,
    new_verifier: &Path,
) -> Result<Value> {
    let custody = root.join(DIRECTORY);
    let _lock = lock(&custody)?;
    recover_locked(root)?;
    same_manifest(root, workspace)?;
    let old = Settings::load(&custody)?;
    let old_config = workspace::member_path(workspace, "config")?;
    old.check(&old_config)?;
    let retained = anchor(&custody, &old)?;
    let pin = read_json(&custody.join(AUTHORITY))?;
    if pin["type"] != "minidregg-carry-authority-v1" || pin["identity"] != old.identity {
        return Err(fail(
            "pin an operator key explicitly for this current lineage before carrying",
        ));
    }
    hex64(text(&pin, "operatorPublicKey")?)?;
    let (capsule, capsule_pins) = registered_capsule(&custody, &pin, capsule)?;
    let pinned_point = point(&pin["anchor"])?;
    if compare(&pinned_point.height, &retained.height) == Ordering::Greater
        || (pinned_point.height == retained.height && pinned_point != retained)
    {
        return Err(fail("operator pin is not an ancestor of current custody"));
    }
    let verifier = crate::absolute(new_verifier)?;
    let config = crate::absolute(new_config)?;
    // Hashing data does not grant an executable authority to justify itself.
    let verifier_sha256 = crate::host_image_sha256(&verifier)?;
    let lineages = custody.join("lineages");
    if !lineages.exists() {
        workspace::make_private_dir(&lineages)?;
        directory(&custody)?.sync_all().map_err(fail)?;
    }
    directory(&lineages)?;
    let id = workspace::random_nonce()?;
    let lineage = lineages.join(&id);
    workspace::make_private_dir(&lineage)?;
    directory(&lineages)?.sync_all().map_err(fail)?;
    copy_config(&old_config, &lineage.join("old-config.json"))?;
    copy_config(&config, &lineage.join("new-config.json"))?;
    copy_config(edge, &lineage.join("edge-manifest.json"))?;
    old.check(&lineage.join("old-config.json"))?;
    let carry_verifier = verifier::select(
        &custody,
        workspace,
        &old,
        &capsule,
        &capsule_pins,
        &lineage.join("old-config.json"),
    )?;
    let request = json!({"oldIdentity":old.identity,"oldAnchor":full(&retained)?,
        "operatorPublicKey":pin["operatorPublicKey"],"edgeManifestPath":lineage.join("edge-manifest.json"),
        "sourceCapsulePath":capsule,"sourceCapsulePins":capsule_pins,"newConfigPath":lineage.join("new-config.json"),
        "newVerifierPath":verifier});
    save(&lineage, "request.json", &request)?;
    let output = lineage.join("verified-edge.json");
    create_file(&output, b"")?;
    // An explicitly installed portable verifier, or the already trusted source
    // Host, authenticates the registered old profile and public signature.
    // No executable selected by the edge manifest runs.
    let status = Command::new(&carry_verifier.executable)
        .arg(&carry_verifier.config)
        .arg("carry-edge-verify")
        .arg(lineage.join("request.json"))
        .arg(&output)
        .output()
        .map_err(fail)?;
    if !status.status.success() {
        return Err(fail(
            "trusted source verifier refused carry edge; no custody changed",
        ));
    }
    let result = read_json(&output)?;
    if result["targetVerifierDigest"] != verifier_sha256 {
        return Err(fail(
            "signed target binary digest differs from explicit new verifier",
        ));
    }
    let replacement = Settings {
        identity: identity(&result["newIdentity"])?,
        verifier_sha256,
        verifier,
    };
    if result["newIdentity"] != replacement.identity || replacement.identity == old.identity {
        return Err(fail("carry requires a canonical new identity; use continuity-verifier for image-only upgrades"));
    }
    let (cut, start) = check_result(&result, &old, &retained, &pin, &replacement)?;
    // Only the old verifier's accepted, locally bound seal authorizes this target.
    replacement.check(&lineage.join("new-config.json"))?;
    // Retain the actual source-verifier request/responses under the workspace's
    // attempts directory. Never advance custody merely to prepare a transition.
    let mut old_workspace = workspace.clone();
    old_workspace["config"] = json!(lineage.join("old-config.json"));
    let mut source = CarryProof {
        local: HostProof::new(root, &old_workspace, &old)?,
        transport_config: lineage.join("new-config.json"),
        transport_host: replacement.verifier.clone(),
        authorized_target_digest: Some(replacement.verifier_sha256.clone()),
    };
    walk(&mut source, &pinned_point, &retained, |_| Ok(()))?;
    walk(&mut source, &retained, &cut, |_| Ok(()))?;
    // Re-check executable/config identities after external verifier invocations.
    old.check(&lineage.join("old-config.json"))?;
    let still_selected = verifier::select(
        &custody,
        workspace,
        &old,
        &capsule,
        &capsule_pins,
        &lineage.join("old-config.json"),
    )?;
    if still_selected.pin != carry_verifier.pin
        || still_selected.executable != carry_verifier.executable
    {
        return Err(fail("carry verifier selection changed during verification"));
    }
    replacement.check(&lineage.join("new-config.json"))?;
    let mut next_manifest = workspace.clone();
    next_manifest["config"] = json!(lineage.join("new-config.json"));
    next_manifest["hostSha256"] = json!(replacement.verifier_sha256);
    if !workspace["host"].is_null() {
        next_manifest["host"] = json!(replacement.verifier);
    }
    next_manifest["receiptContinuity"] = json!(ALGORITHM);
    next_manifest["receiptCarryLineage"] = json!(id);
    let transition = json!({"old":{"settings":old.json(),"anchor":anchor_json(&old, &retained)?,"manifest":workspace,"authority":pin},
        "next":{"settings":replacement.json(),"anchor":anchor_json(&replacement, &start)?,"manifest":next_manifest,"authority":null},
        "verifiedEdge":result,"request":request,"prefixProofAttempt":source.local.scratch,"carryVerifier":carry_verifier.pin,
        "historySettings":{"identity":old.identity,"verifier":capsule.join("verifier"),"verifierSha256":capsule_pins["verifierSha256"]},
        "historicalConfig":capsule.join("original-config.json"),
        "oldConfig":lineage.join("old-config.json"),"sourceCapsule":capsule});
    validate_transition(&transition)?;
    save(&lineage, "transition.json", &transition)?;
    let wal = json!({"type":"minidregg-carry-transition-v1","id":id,"phase":"prepared","transition":transition});
    save(&custody, WAL, &wal)?;
    recover_locked(root)?;
    Ok(
        json!({"type":"minidregg-continuity-carried-v1","identity":replacement.identity,"point":start.json(),"lineage":lineage}),
    )
}

fn copy_executable(source: &Path, target: &Path) -> Result<String> {
    use std::os::unix::fs::PermissionsExt;
    if !source.is_absolute() {
        return Err(fail(
            "capsule executables must have explicit absolute paths",
        ));
    }
    let expected = crate::host_image_sha256(source)?;
    let mut input = OpenOptions::new()
        .read(true)
        .custom_flags(NOFOLLOW)
        .open(source)
        .map_err(fail)?;
    if !input.metadata().map_err(fail)?.is_file() {
        return Err(fail("capsule executable is not regular"));
    }
    let mut output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o700)
        .custom_flags(NOFOLLOW)
        .open(target)
        .map_err(fail)?;
    std::io::copy(&mut input, &mut output).map_err(fail)?;
    output
        .set_permissions(fs::Permissions::from_mode(0o700))
        .map_err(fail)?;
    output.sync_all().map_err(fail)?;
    if crate::host_image_sha256(target)? != expected
        || crate::host_image_sha256(source)? != expected
    {
        return Err(fail("capsule executable changed during snapshot"));
    }
    Ok(expected)
}
fn register_capsule(root: &Path, settings: &Settings, config: &Path) -> Result<(PathBuf, Value)> {
    let registry = root.join("capsules");
    if !registry.exists() {
        workspace::make_private_dir(&registry)?;
        directory(root)?.sync_all().map_err(fail)?;
    }
    directory(&registry)?;
    let capsule = registry.join(workspace::random_nonce()?);
    workspace::make_private_dir(&capsule)?;
    directory(&registry)?.sync_all().map_err(fail)?;
    copy_config(config, &capsule.join("original-config.json"))?;
    let original = fs::read(capsule.join("original-config.json")).map_err(fail)?;
    let value: Value = serde_json::from_slice(&original).map_err(fail)?;
    let host = copy_executable(&settings.verifier, &capsule.join("verifier"))?;
    let signature = copy_executable(
        Path::new(text(&value, "signatureBinary")?),
        &capsule.join("signature-verifier"),
    )?;
    let profile = Command::new(&capsule.join("verifier"))
        .arg(capsule.join("original-config.json"))
        .arg("profile")
        .output()
        .map_err(fail)?;
    if !profile.status.success()
        || profile.stdout.len() as u64 > MAX_JSON
        || identity(&serde_json::from_slice(&profile.stdout).map_err(fail)?)? != settings.identity
    {
        return Err(fail(
            "retained capsule profile differs from current custody",
        ));
    }
    create_file(&capsule.join("profile.json"), &profile.stdout)?;
    let pins = json!({"verifierSha256":host,"identity":settings.identity,
        "signatureVerifierPath":capsule.join("signature-verifier"),"signatureVerifierSha256":signature,
        "configSha256":crate::host_image_sha256(&capsule.join("original-config.json"))?,
        "profileSha256":crate::host_image_sha256(&capsule.join("profile.json"))?});
    save(&capsule, "pins.json", &pins)?;
    settings.check(config)?;
    if host != settings.verifier_sha256 || crate::host_image_sha256(config)? != pins["configSha256"]
    {
        return Err(fail("source capsule changed during registration"));
    }
    directory(&capsule)?.sync_all().map_err(fail)?;
    Ok((capsule, pins))
}
fn registered_capsule(custody: &Path, pin: &Value, supplied: &Path) -> Result<(PathBuf, Value)> {
    let capsule = fs::canonicalize(supplied).map_err(fail)?;
    if Some(capsule.as_path()) != pin["sourceCapsulePath"].as_str().map(Path::new)
        || capsule.parent() != Some(custody.join("capsules").as_path())
    {
        return Err(fail(
            "source capsule is not the locally registered authority capsule",
        ));
    }
    directory(&capsule)?;
    let pins = read_json(&capsule.join("pins.json"))?;
    if pins != pin["sourceCapsulePins"] {
        return Err(fail("registered capsule pins changed"));
    }
    if pins["identity"] != pin["identity"]
        || pins["signatureVerifierPath"]
            != capsule
                .join("signature-verifier")
                .to_string_lossy()
                .as_ref()
    {
        return Err(fail(
            "registered capsule identity or signature helper path changed",
        ));
    }
    for (name, filename) in [
        ("verifierSha256", "verifier"),
        ("signatureVerifierSha256", "signature-verifier"),
        ("configSha256", "original-config.json"),
        ("profileSha256", "profile.json"),
    ] {
        hex64(text(&pins, name)?)?;
        let file = OpenOptions::new()
            .read(true)
            .custom_flags(NOFOLLOW)
            .open(capsule.join(filename))
            .map_err(fail)?;
        private_metadata(&file, false)?;
        if crate::host_image_sha256(&capsule.join(filename))? != pins[name] {
            return Err(fail(format!("registered capsule {name} changed")));
        }
    }
    Ok((capsule, pins))
}

// Follow only the committed chain named by the current workspace manifest.
// Stray prepared directories cannot become trusted historical lineages.
fn history(root: &Path, current: &Settings) -> Result<Vec<Value>> {
    let manifest = read_json(&root.join("workspace.json"))?;
    let mut id = manifest
        .get("receiptCarryLineage")
        .cloned()
        .unwrap_or(Value::Null);
    let mut expected = current.identity.clone();
    let mut result = Vec::new();
    let mut seen = std::collections::HashSet::new();
    while !id.is_null() {
        let name = id
            .as_str()
            .ok_or_else(|| fail("invalid historical lineage reference"))?;
        decimal(name)?;
        if !seen.insert(name.to_owned()) || result.len() >= MAX_HOPS {
            return Err(fail("historical lineage cycle or bound exceeded"));
        }
        let transition = read_json(
            &root
                .join(DIRECTORY)
                .join("lineages")
                .join(name)
                .join("transition.json"),
        )?;
        validate_transition(&transition)?;
        if transition["next"]["settings"]["identity"] != expected
            || transition["next"]["manifest"]["receiptCarryLineage"] != id
        {
            return Err(fail(
                "historical lineage does not connect to current custody",
            ));
        }
        expected = transition["old"]["settings"]["identity"].clone();
        id = transition["old"]["manifest"]
            .get("receiptCarryLineage")
            .cloned()
            .unwrap_or(Value::Null);
        result.push(transition);
    }
    result.reverse();
    Ok(result)
}
fn historical_source(
    _root: &Path,
    workspace: &Value,
    transition: &Value,
) -> Result<(Value, Settings)> {
    let archived = &transition["historySettings"];
    let settings = Settings {
        identity: identity(&archived["identity"])?,
        verifier: PathBuf::from(text(archived, "verifier")?),
        verifier_sha256: text(archived, "verifierSha256")?.into(),
    };
    if settings.identity != transition["old"]["settings"]["identity"]
        || !settings.verifier.is_absolute()
    {
        return Err(fail(
            "historical verifier is not bound to archived identity",
        ));
    }
    let mut selected = workspace.clone();
    selected["config"] = transition["historicalConfig"].clone();
    settings.check(&workspace::member_path(&selected, "config")?)?;
    // Host transport stays on the currently pinned host. Only local proof and
    // normalization use the archived profile; op151 explicitly names identity.
    Ok((selected, settings))
}
pub(super) fn historical_challenge(
    root: &Path,
    workspace: &Value,
    current: &Settings,
    challenge: &Value,
) -> Result<Option<Point>> {
    let mut lower = "0".to_owned();
    for transition in history(root, current)? {
        let old_identity = &transition["old"]["settings"]["identity"];
        let cut = point(&transition["verifiedEdge"]["oldCut"])?;
        if challenge["domain"] == old_identity["domain"]
            && challenge["semantics"] == old_identity["semantics"]
        {
            let (selected, settings) = historical_source(root, workspace, &transition)?;
            let source = HostProof::new(root, &selected, &settings)?;
            let candidate = source.challenge_point(challenge)?;
            if compare(&candidate.height, &lower) != Ordering::Less
                && compare(&candidate.height, &cut.height) != Ordering::Greater
            {
                return Ok(Some(candidate));
            }
        }
        lower = point(&transition["verifiedEdge"]["newStart"])?.height;
    }
    Ok(None)
}
pub(super) fn finish_historical_locked(
    root: &Path,
    workspace: &Value,
    current: &Settings,
    target: &Point,
    mode: Mode,
) -> Result<bool> {
    if mode != Mode::Historical && mode != Mode::ReceiptReplay {
        return Ok(false);
    }
    for transition in history(root, current)? {
        let cut = point(&transition["verifiedEdge"]["oldCut"])?;
        if compare(&target.height, &cut.height) != Ordering::Greater {
            let (selected, settings) = historical_source(root, workspace, &transition)?;
            let mut source = CarryProof {
                local: HostProof::new(root, &selected, &settings)?,
                transport_config: workspace::member_path(workspace, "config")?,
                transport_host: workspace::workspace_host(workspace)?,
                authorized_target_digest: None,
            };
            walk(&mut source, target, &cut, |_| Ok(()))?;
            return Ok(true);
        }
    }
    Ok(false)
}

/// A lineage proof has two profiles: current server transport and archived
/// local verification. The transport pin is never interpreted as the old root.
struct CarryProof<'a> {
    local: HostProof<'a>,
    transport_config: PathBuf,
    transport_host: PathBuf,
    authorized_target_digest: Option<String>,
}
impl ProofSource for CarryProof<'_> {
    fn verified_hop(&mut self, from: Option<&Point>, target: &Point) -> Result<(Point, bool)> {
        let mut query = json!({"identity":self.local.settings.identity,"from":from.map(Point::json),"target":target.json()});
        if let Some((chain, siblings)) = from.and_then(|p| p.witness.as_ref()) {
            query["fromChain"] = json!(chain);
            query["fromSiblings"] = json!(siblings);
        }
        let socket = SOCKET
            .get()
            .ok_or_else(|| fail("carry history requires pinned workspace socket"))?;
        let bytes = serde_json::to_vec(&query).map_err(fail)?;
        let frame = match &self.authorized_target_digest {
            // Only a locally accepted old-verifier EdgeSeal creates this value.
            // This proof-only call does not repin the process or acknowledge work.
            Some(digest) => crate::transport::invoke_pinned(
                socket,
                &self.transport_config,
                digest,
                151,
                &bytes,
            )?,
            None => crate::session_invoke(
                &self.transport_host,
                socket,
                &self.transport_config,
                151,
                &bytes,
            )?,
        };
        if frame.first() != Some(&151) || frame.len() as u64 > MAX_JSON {
            return Err(fail("server refused archived continuity proof"));
        }
        self.local.verify_response(&query, &frame[1..])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;
    struct Temp(PathBuf);
    impl Temp {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "mini-carry-test-{}-{}",
                std::process::id(),
                workspace::random_nonce().unwrap()
            ));
            workspace::make_private_dir(&path).unwrap();
            Self(path)
        }
    }
    impl Drop for Temp {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
    fn endpoint(height: u64) -> Point {
        Point {
            height: height.to_string(),
            world_root: (height * 17).to_string(),
            witness: Some(((height * 7).to_string(), vec!["3".into(); 256])),
        }
    }
    fn selected(semantics: &str) -> Settings {
        Settings {
            identity: json!({"algorithm":ALGORITHM,"domain":"1","semantics":semantics,"expectedSeed":"3"}),
            verifier: PathBuf::from("/unused-fixture"),
            verifier_sha256: "a".repeat(64),
        }
    }
    fn edge() -> Value {
        json!({"algorithm":EDGE,"oldIdentity":selected("2").identity,"newIdentity":selected("4").identity,
        "oldCut":full(&endpoint(5)).unwrap(),"newStart":full(&endpoint(6)).unwrap(),"bodyDigest":"7","originIndexDigest":"8", "operatorPublicKey":"b".repeat(64),"targetVerifierDigest":"a".repeat(64)})
    }
    fn completed_fresh_provenance(root: &Path) {
        // Match the actual onboarding module's immutable completed provenance,
        // rather than the placeholder object used before these lanes converged.
        save(root, "receipt-continuity.pending.json", &json!({
            "type":"minidregg-fresh-continuity-v1","enrollment":"11","state":"complete",
            "reference":{"name":"initial","kind":"object","target":"1","observeCapability":"2"}
        })).unwrap();
    }
    fn prepared() -> (Temp, Value, Ticket) {
        let root = Temp::new();
        let custody = root.0.join(DIRECTORY);
        workspace::make_private_dir(&custody).unwrap();
        workspace::make_private_dir(&custody.join("lineages")).unwrap();
        workspace::make_private_dir(&custody.join("lineages/1")).unwrap();
        let settings = selected("2");
        let replacement = selected("4");
        completed_fresh_provenance(&root.0);
        let manifest = json!({"receiptContinuity":ALGORITHM,"config":"/old/config","host":"/old/verifier","hostSha256":"a".repeat(64),"freshContinuity":"11"});
        let mut next = manifest.clone();
        next["config"] = json!("/new/config");
        next["host"] = json!("/new/verifier");
        next["receiptCarryLineage"] = json!("1");
        let authority = json!({"type":"minidregg-carry-authority-v1","identity":settings.identity,"anchor":full(&endpoint(1)).unwrap(),"operatorPublicKey":"b".repeat(64)});
        let transition = json!({"old":{"settings":settings.json(),"anchor":anchor_json(&settings,&endpoint(1)).unwrap(),"manifest":manifest,"authority":authority},
            "next":{"settings":replacement.json(),"anchor":anchor_json(&replacement,&endpoint(6)).unwrap(),"manifest":next,"authority":null},"verifiedEdge":edge()});
        for (file, value) in [
            ("enabled.json", &transition["old"]["settings"]),
            ("anchor.json", &transition["old"]["anchor"]),
            (AUTHORITY, &transition["old"]["authority"]),
        ] {
            save(&custody, file, value).unwrap();
        }
        save(&root.0, "workspace.json", &manifest).unwrap();
        save(&custody.join("lineages/1"), "transition.json", &transition).unwrap();
        save(&custody,WAL,&json!({"type":"minidregg-carry-transition-v1","id":"1","phase":"prepared","transition":transition})).unwrap();
        (
            root,
            transition,
            Ticket {
                baseline: endpoint(1),
                settings,
            },
        )
    }
    #[test]
    fn carry_result_binds_key_identity_target_binary_height_and_full_openings() {
        let old = selected("2");
        let new = selected("4");
        let pin = json!({"operatorPublicKey":"b".repeat(64)});
        check_result(&edge(), &old, &endpoint(1), &pin, &new).unwrap();
        for (key, bad) in [
            ("algorithm", json!("wrong")),
            ("operatorPublicKey", json!("c".repeat(64))),
            ("targetVerifierDigest", json!("f".repeat(64))),
            ("oldIdentity", new.identity.clone()),
            ("newIdentity", old.identity.clone()),
            ("bodyDigest", json!("01")),
            ("originIndexDigest", json!(12)),
        ] {
            let mut result = edge();
            result[key] = bad;
            assert!(
                check_result(&result, &old, &endpoint(1), &pin, &new).is_err(),
                "{key}"
            );
        }
        for (name, key, value) in [
            ("oldCut", "height", json!("0")),
            ("newStart", "height", json!("8")),
            ("newStart", "systemSiblings", json!(vec!["3"; 255])),
            ("oldCut", "systemSiblings", json!(vec!["3"; 257])),
        ] {
            let mut result = edge();
            result[name][key] = value;
            assert!(check_result(&result, &old, &endpoint(1), &pin, &new).is_err());
        }
    }
    #[test]
    fn carry_refuses_unrelated_domain_or_origin_seed_even_with_matching_target_profile() {
        for field in ["domain", "expectedSeed"] {
            let old = selected("2");
            let mut replacement = selected("4");
            replacement.identity[field] = json!("999");
            let mut result = edge();
            result["newIdentity"] = replacement.identity.clone();
            assert!(check_result(
                &result,
                &old,
                &endpoint(1),
                &json!({"operatorPublicKey":"b".repeat(64)}),
                &replacement
            )
            .is_err());
            let (_, mut transition, _) = prepared();
            transition["verifiedEdge"] = result;
            transition["next"]["settings"]["identity"] = replacement.identity.clone();
            transition["next"]["anchor"]["identity"] = replacement.identity;
            assert!(validate_transition(&transition).is_err());
        }
    }

    #[test]
    fn carry_recovery_finishes_exact_transition_and_preserves_first_enrollment() {
        let (root, transition, _) = prepared();
        let _lock = lock(&root.0.join(DIRECTORY)).unwrap();
        recover_locked(&root.0).unwrap();
        assert_eq!(
            read_json(&root.0.join("workspace.json")).unwrap(),
            transition["next"]["manifest"]
        );
        assert_eq!(
            anchor(&root.0.join(DIRECTORY), &selected("4")).unwrap(),
            endpoint(6)
        );
        assert_eq!(
            read_json(&root.0.join(DIRECTORY).join(AUTHORITY)).unwrap(),
            Value::Null
        );
        // A completed record must never roll back later ordinary progress.
        persist(&root.0.join(DIRECTORY), &selected("4"), &endpoint(9)).unwrap();
        recover_locked(&root.0).unwrap();
        assert_eq!(
            anchor(&root.0.join(DIRECTORY), &selected("4")).unwrap(),
            endpoint(9)
        );
        assert_eq!(history(&root.0, &selected("4")).unwrap().len(), 1);
    }
    #[test]
    fn carry_recovery_refuses_unrecorded_changes_and_missing_custody() {
        let (root, _, _) = prepared();
        let custody = root.0.join(DIRECTORY);
        let before = fs::read(custody.join("enabled.json")).unwrap();
        save(&root.0, "workspace.json", &json!({"config":"unrecorded"})).unwrap();
        assert!(recover_locked(&root.0).is_err());
        assert_eq!(fs::read(custody.join("enabled.json")).unwrap(), before);
        let (root, _, _) = prepared();
        fs::remove_file(root.0.join(DIRECTORY).join("anchor.json")).unwrap();
        assert!(recover_locked(&root.0).is_err());
        assert!(!root.0.join(DIRECTORY).join("anchor.json").exists());
    }
    #[test]
    fn carry_recovery_rejects_evidence_substitution_and_invalid_start() {
        let (root, _, _) = prepared();
        let custody = root.0.join(DIRECTORY);
        let mut wal = read_json(&custody.join(WAL)).unwrap();
        wal["transition"]["verifiedEdge"]["newStart"]["height"] = json!("7");
        save(&custody, WAL, &wal).unwrap();
        assert!(recover_locked(&root.0).is_err());
        save(
            &custody.join("lineages/1"),
            "transition.json",
            &wal["transition"],
        )
        .unwrap();
        assert!(recover_locked(&root.0).is_err());
    }
    #[test]
    fn carry_refuses_old_inflight_ticket_and_stale_workspace_after_recovery() {
        let (root, transition, ticket) = prepared();
        let result = finish_resolved(
            &root.0,
            &transition["old"]["manifest"],
            Some(ticket),
            Mode::Ordinary,
            |_| panic!("stale request must not resolve"),
        );
        assert!(result.unwrap_err().contains("custody changed"));
        assert!(begin(&root.0, &transition["old"]["manifest"])
            .err()
            .unwrap()
            .contains("workspace migrated"));
        assert_eq!(
            anchor(&root.0.join(DIRECTORY), &selected("4")).unwrap(),
            endpoint(6)
        );
    }
    #[test]
    fn carry_crash_child() {
        let Ok(root) = std::env::var("MINI_CARRY_CRASH_ROOT") else {
            return;
        };
        let stage = std::env::var("MINI_CARRY_CRASH_STAGE").unwrap();
        let root = Path::new(&root);
        let _lock = lock(&root.join(DIRECTORY)).unwrap();
        recover_with(root, |current| {
            if current == stage {
                std::process::exit(73);
            }
            Ok(())
        })
        .unwrap();
        panic!("crash hook not reached");
    }
    #[test]
    fn carry_process_crashes_resume_each_exact_durable_phase() {
        for stage in ["settings", "anchor", "manifest", "authority", "complete"] {
            let (root, transition, _) = prepared();
            let output = Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "receipt_continuity::carry::tests::carry_crash_child",
                ])
                .env("MINI_CARRY_CRASH_ROOT", &root.0)
                .env("MINI_CARRY_CRASH_STAGE", stage)
                .output()
                .unwrap();
            assert_eq!(
                output.status.code(),
                Some(73),
                "{stage}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            let _lock = lock(&root.0.join(DIRECTORY)).unwrap();
            recover_locked(&root.0).unwrap();
            assert_eq!(
                read_json(&root.0.join("workspace.json")).unwrap(),
                transition["next"]["manifest"]
            );
            assert_eq!(
                anchor(&root.0.join(DIRECTORY), &selected("4")).unwrap(),
                endpoint(6)
            );
            assert_eq!(
                read_json(&root.0.join(DIRECTORY).join(WAL)).unwrap()["phase"],
                "complete"
            );
        }
    }
    fn executable(path: &Path, script: &str) {
        create_file(path, script.as_bytes()).unwrap();
        fs::set_permissions(path, fs::Permissions::from_mode(0o700)).unwrap();
    }
    #[test]
    fn capsule_registration_snapshots_local_custody_and_rejects_tampering() {
        let root = Temp::new();
        let config = root.0.join("config.json");
        let verifier = root.0.join("current-verifier");
        let helper = root.0.join("signature-helper");
        executable(&verifier, "#!/bin/sh\ncat \"$1\"\n");
        executable(&helper, "#!/bin/sh\nexit 0\n");
        let mut profile = selected("2").identity;
        profile["signatureBinary"] = json!(helper);
        profile["arbitraryWidth"] = json!("not interpreted by custody");
        save(&root.0, "config.json", &profile).unwrap();
        let settings = Settings {
            identity: identity(&profile).unwrap(),
            verifier: verifier.clone(),
            verifier_sha256: crate::host_image_sha256(&verifier).unwrap(),
        };
        let (capsule, pins) = register_capsule(&root.0, &settings, &config).unwrap();
        let pin = json!({"identity":settings.identity,"sourceCapsulePath":capsule,"sourceCapsulePins":pins});
        registered_capsule(&root.0, &pin, &capsule).unwrap();
        assert_eq!(
            fs::read(capsule.join("original-config.json")).unwrap(),
            fs::read(&config).unwrap()
        );
        assert!(!capsule.join("storage-helper").exists());
        fs::write(&verifier, b"upgraded current verifier").unwrap();
        registered_capsule(&root.0, &pin, &capsule).unwrap(); // explicit upgrade retains original capsule.
        fs::write(capsule.join("signature-verifier"), b"tampered").unwrap();
        assert!(registered_capsule(&root.0, &pin, &capsule).is_err());
        assert!(registered_capsule(&root.0, &pin, &root.0).is_err());
    }
    #[test]
    fn carry_decimal_successor_has_no_machine_word_truncation() {
        assert_eq!(next_height("0"), "1");
        assert_eq!(
            next_height("99999999999999999999999999999999"),
            "100000000000000000000000000000000"
        );
    }
    #[test]
    fn carry_receiving_fixture_child() {
        let Ok(mode) = std::env::var("MINI_CARRY_RECEIVING_FIXTURE") else {
            return;
        };
        let reject = mode.ends_with("refuse");
        let portable_mode = mode.starts_with("portable");
        let root = Temp::new();
        let custody = root.0.join(DIRECTORY);
        workspace::make_private_dir(&custody).unwrap();
        workspace::make_private_dir(&root.0.join("attempts")).unwrap();
        for name in ["refs", "sources", "proposals"] {
            workspace::make_private_dir(&root.0.join(name)).unwrap();
        }
        let host = root.0.join("old-host");
        let target = root.0.join("target-host");
        let helper = root.0.join("sig");
        let edgefile = root.0.join("edge-verdict.json");
        let marker = root.0.join("target-executed");
        executable(&helper, "#!/bin/sh\nexit 0\n");
        executable(&host,&format!("#!/bin/sh\ncase \"$2\" in\nprofile) cat \"$1\" ;;\ncontinuity-verify) cp \"$4\" \"$5\" ;;\ncontinuity-point) cp \"$3\" \"$4\" ;;\ncarry-edge-verify) {} ;;\n*) exit 9 ;;\nesac\n",if reject || portable_mode {"exit 71".into()}else{format!("cp '{}' \"$4\"",edgefile.display())}));
        executable(
            &target,
            &format!(
                "#!/bin/sh\nprintf touched > '{}'\ncat \"$1\"\n",
                marker.display()
            ),
        );
        let mut old_profile = selected("2").identity;
        old_profile["signatureBinary"] = json!(helper);
        let mut next_profile = selected("4").identity;
        next_profile["signatureBinary"] = json!(helper);
        save(&root.0, "old-config.json", &old_profile).unwrap();
        save(&root.0, "target-config.json", &next_profile).unwrap();
        let old = Settings {
            identity: identity(&old_profile).unwrap(),
            verifier: host.clone(),
            verifier_sha256: crate::host_image_sha256(&host).unwrap(),
        };
        persist(&custody, &old, &endpoint(1)).unwrap();
        save(&custody, "enabled.json", &old.json()).unwrap();
        let socket = root.0.join("s");
        SOCKET.set(socket.clone()).unwrap();
        let mut manifest = json!({"type":"minidregg-participant-workspace-v1","subject":"1","key":root.0.join("unused-key"),"receiptContinuity":ALGORITHM,"config":root.0.join("old-config.json"),"host":host,"hostSha256":old.verifier_sha256,"socket":socket,
            "freshContinuity":"11"});
        completed_fresh_provenance(&root.0);
        let fresh_before = fs::read(root.0.join("receipt-continuity.pending.json")).unwrap();
        save(&root.0, "workspace.json", &manifest).unwrap();
        let pinned = pin_authority(&root.0, &manifest, &"b".repeat(64)).unwrap();
        let capsule = PathBuf::from(text(&pinned, "sourceCapsulePath").unwrap());
        let portable_invoked = root.0.join("portable-carry-invoked");
        if portable_mode {
            let portable = root.0.join("portable-verifier");
            let description = root.0.join("portable-description.json");
            let pins = read_json(&capsule.join("pins.json")).unwrap();
            save(&root.0,"portable-description.json",&json!({"algorithm":"minidregg-carry-verifier-v1","identity":old.identity,"sourceCapsulePins":pins,"edgeAlgorithm":EDGE})).unwrap();
            executable(&portable,&format!("#!/bin/sh\ncase \"$2\" in\ncarry-verifier-profile) cp '{}' \"$4\" ;;\ncarry-edge-verify) printf invoked > '{}'; {} ;;\n*) exit 91 ;;\nesac\n",description.display(),portable_invoked.display(),if reject {"exit 71".into()}else{format!("cp '{}' \"$4\"",edgefile.display())}));
            let before = fs::read(custody.join("anchor.json")).unwrap();
            let settings_before = fs::read(custody.join("enabled.json")).unwrap();
            install_verifier(
                &root.0,
                &manifest,
                &portable,
                &crate::host_image_sha256(&portable).unwrap(),
            )
            .unwrap();
            assert_eq!(fs::read(custody.join("anchor.json")).unwrap(), before);
            assert_eq!(
                fs::read(custody.join("enabled.json")).unwrap(),
                settings_before
            );
            manifest = read_json(&root.0.join("workspace.json")).unwrap();
        }
        let mut verdict = edge();
        verdict["targetVerifierDigest"] = json!(crate::host_image_sha256(&target).unwrap());
        save(&root.0, "edge-verdict.json", &verdict).unwrap();
        let original = fs::read(custody.join("anchor.json")).unwrap();
        // This fixture injects verifier verdicts. It tests physical routing and
        // durable acknowledgment, not EdgeSeal cryptography or semantic audit.
        let service = if reject {
            None
        } else {
            let listener = std::os::unix::net::UnixListener::bind(&socket).unwrap();
            let config = fs::read(root.0.join("target-config.json")).unwrap();
            let digest = crate::host_image_sha256(&target).unwrap();
            Some(std::thread::spawn(move || {
                for request_index in 0..9 {
                    let (mut connection, _) = listener.accept().unwrap();
                    let frame = crate::transport::read_frame(&mut connection)
                        .unwrap()
                        .unwrap();
                    assert_eq!(frame[0], 2);
                    let length = u32::from_le_bytes(frame[1..5].try_into().unwrap()) as usize;
                    assert_eq!(
                        &frame[5..5 + length],
                        config.as_slice(),
                        "transport must use new exact config"
                    );
                    let expected = (0..64)
                        .step_by(2)
                        .map(|i| u8::from_str_radix(&digest[i..i + 2], 16).unwrap())
                        .collect::<Vec<_>>();
                    assert_eq!(
                        &frame[5 + length..37 + length],
                        expected.as_slice(),
                        "transport must use signed target image"
                    );
                    if [3, 5, 6, 7, 8].contains(&request_index) {
                        assert_eq!(
                            frame[37 + length],
                            153,
                            "old calls must only use carried lookup"
                        );
                        let payload = &frame[38 + length..];
                        let header_length =
                            u32::from_le_bytes(payload[..4].try_into().unwrap()) as usize;
                        let header: Value =
                            serde_json::from_slice(&payload[4..4 + header_length]).unwrap();
                        assert_eq!(header["algorithm"], LOOKUP);
                        assert_eq!(header["originIdentity"], selected("2").identity);
                        assert_eq!(
                            &payload[4 + header_length..],
                            b"exact-retained-call-fixture"
                        );
                        let mut response = json!({"algorithm":LOOKUP,"originIdentity":selected("2").identity,
                            "callDigest":call_digest(b"exact-retained-call-fixture"),
                            "outcome":{"type":"confirmed","confirmation":"replayed","transactionId":"41","eventId":"42","acceptedCount":"2","worldRoot":"34"}});
                        match request_index {
                            5 => response["callDigest"] = json!("0".repeat(64)),
                            6 => response["originIdentity"] = selected("4").identity,
                            7 => response["outcome"]["detail"] = json!("must not forward content"),
                            8 => response["outcome"] = json!({"type":"absent"}),
                            _ => (),
                        }
                        let mut reply = vec![153];
                        reply.extend(serde_json::to_vec(&response).unwrap());
                        crate::transport::write_frame(&mut connection, &reply).unwrap();
                        continue;
                    }
                    assert_eq!(frame[37 + length], 151);
                    let query: Value = serde_json::from_slice(&frame[38 + length..]).unwrap();
                    assert_eq!(
                        query["identity"],
                        selected("2").identity,
                        "proof still names old identity"
                    );
                    let height = text(&query["target"], "height").unwrap().parse().unwrap();
                    let endpoint = endpoint(height);
                    let (chain, siblings) = endpoint.witness.unwrap();
                    let response = json!({"identity":query["identity"],"from":query["from"],"to":query["target"],"startChain":"7","endChain":chain,
                        "fromSiblings":vec!["3";256],"toSiblings":siblings,"suffix":[],"complete":true,"chain":chain,"siblings":siblings});
                    let mut reply = vec![151];
                    reply.extend(serde_json::to_vec(&response).unwrap());
                    crate::transport::write_frame(&mut connection, &reply).unwrap();
                }
            }))
        };
        let result = migrate(
            &root.0,
            &manifest,
            &edgefile,
            &capsule,
            &root.0.join("target-config.json"),
            &target,
        );
        if portable_mode {
            assert!(
                portable_invoked.exists(),
                "carry must invoke explicitly pinned portable verifier"
            );
        }
        if reject {
            assert!(result
                .unwrap_err()
                .contains("trusted source verifier refused"));
            assert!(!marker.exists(), "unapproved target code must not execute");
            assert_eq!(fs::read(custody.join("anchor.json")).unwrap(), original);
            assert!(!custody.join(WAL).exists());
            return;
        }
        result.unwrap();
        let next = read_json(&root.0.join("workspace.json")).unwrap();
        assert_eq!(next["freshContinuity"], manifest["freshContinuity"]);
        assert_eq!(fs::read(root.0.join("receipt-continuity.pending.json")).unwrap(), fresh_before);
        assert!(marker.exists());
        let retained = fs::read(custody.join("anchor.json")).unwrap();
        let ticket = begin(&root.0, &next).unwrap();
        finish_resolved(&root.0, &next, ticket, Mode::ReceiptReplay, |_| {
            Ok(endpoint(2))
        })
        .unwrap();
        assert_eq!(
            fs::read(custody.join("anchor.json")).unwrap(),
            retained,
            "historical replay never downgrades new anchor"
        );
        assert_eq!(
            anchor(&custody, &Settings::load(&custody).unwrap()).unwrap(),
            endpoint(6)
        );
        let attempt = root.0.join("attempts/old-call");
        workspace::make_private_dir(&attempt).unwrap();
        create_file(&attempt.join("call.bin"), b"exact-retained-call-fixture").unwrap();
        save(
            &attempt,
            "challenge.json",
            &json!({"domain":"1","semantics":"2","height":"1","worldRoot":"17"}),
        )
        .unwrap();
        save(&attempt,"attempt.json",&json!({"format":"minidregg-resource-client-attempt-v1","operation":"submit", "host":"/obsolete-missing-host", "config":"/obsolete-config"})).unwrap();
        crate::retry(&attempt, "lookup", false).unwrap();
        assert_eq!(
            read_json(&attempt.join("retry-0001.json")).unwrap()["confirmation"],
            "replayed"
        );
        for _ in 0..3 {
            assert!(crate::retry(&attempt, "lookup", false).is_err());
        }
        assert!(crate::retry(&attempt, "lookup", false)
            .unwrap_err()
            .contains("absent"));
        assert_eq!(
            read_json(&attempt.join("retry-0005.json")).unwrap(),
            json!({"type":"absent"})
        );
        assert!(crate::retry(&attempt, "submit", false)
            .unwrap_err()
            .contains("never direct execution or resubmission"));
        assert!(crate::retry(&attempt, "lookup", true)
            .unwrap_err()
            .contains("never direct execution or resubmission"));
        assert_eq!(
            fs::read(attempt.join("call.bin")).unwrap(),
            b"exact-retained-call-fixture"
        );
        assert_eq!(fs::read(custody.join("anchor.json")).unwrap(), retained);
        for n in [2, 3, 4] {
            assert!(attempt.join(format!("retry-{n:04}.bin")).exists());
            assert!(!attempt.join(format!("retry-{n:04}.json")).exists());
        }
        service.unwrap().join().unwrap();
        // Metadata-only lookup skips current-key checks, never continuity custody.
        fs::rename(custody.join("anchor.json"), custody.join("held-anchor.json")).unwrap();
        assert!(crate::retry(&attempt, "lookup", false).is_err());
        assert!(!custody.join("anchor.json").exists());
        assert_eq!(fs::read(attempt.join("call.bin")).unwrap(), b"exact-retained-call-fixture");
    }
    #[test]
    fn carry_receiving_fixture_new_endpoint_old_proof_and_refused_target_execution() {
        for mode in ["accept", "refuse", "portable", "portable-refuse"] {
            let output = Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "receipt_continuity::carry::tests::carry_receiving_fixture_child",
                    "--nocapture",
                ])
                .env("MINI_CARRY_RECEIVING_FIXTURE", mode)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{mode}: {} {}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }
    #[test]
    fn carried_lookup_rejects_forged_metadata_and_preserves_full_raw_call_bound() {
        let origin = selected("2").identity;
        let digest = call_digest(b"original");
        let good = json!({"algorithm":LOOKUP,"originIdentity":origin,"callDigest":digest,
            "outcome":{"type":"confirmed","confirmation":"replayed","transactionId":"41","eventId":"42","acceptedCount":"2","worldRoot":"34"}});
        lookup_outcome(&good, &origin, &digest, "0", &endpoint(5)).unwrap();
        for (key, bad) in [
            ("confirmation", json!("installed")),
            ("acceptedCount", json!("6")),
            ("worldRoot", json!("01")),
            ("type", json!("content")),
        ] {
            let mut value = good.clone();
            value["outcome"][key] = bad;
            assert!(lookup_outcome(&value, &origin, &digest, "0", &endpoint(5)).is_err());
        }
        let mut extra = good.clone();
        extra["outcome"]["leaf"] = json!({"private":"data"});
        assert!(lookup_outcome(&extra, &origin, &digest, "0", &endpoint(5)).is_err());
        extra = good.clone();
        extra["capsule"] = json!("private");
        assert!(lookup_outcome(&extra, &origin, &digest, "0", &endpoint(5)).is_err());
        for reason in [
            "origin-mismatch",
            "malformed-call",
            "capsule-unavailable",
            "lookup-refused",
            "receipt-invalid",
        ] {
            let mut value = good.clone();
            value["outcome"] = json!({"type":"refused","reason":reason});
            lookup_outcome(&value, &origin, &digest, "0", &endpoint(5)).unwrap();
        }
        let mut call = vec![7; crate::transport::MAX_CARRIED_CALL];
        let payload = lookup_payload(&origin, &call, crate::transport::MAX_CONFIG).unwrap();
        let header = u32::from_le_bytes(payload[..4].try_into().unwrap()) as usize;
        assert_eq!(&payload[4 + header..], call.as_slice());
        call.push(7);
        assert!(lookup_payload(&origin, &call, 0).is_err());
        assert!(lookup_payload(&origin, b"valid", crate::transport::MAX_CONFIG + 1).is_err());
    }
}

const LOOKUP: &str = "minidregg-carried-call-lookup-v1";
fn retained_call(path: &Path) -> Result<Vec<u8>> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(NOFOLLOW)
        .open(path)
        .map_err(fail)?;
    private_metadata(&file, false)?;
    let maximum = crate::transport::MAX_CARRIED_CALL as u64;
    if file.metadata().map_err(fail)?.len() > maximum {
        return Err(fail(
            "retained call exceeds carried lookup transport bound; exact call retained",
        ));
    }
    let mut bytes = Vec::new();
    file.take(maximum + 1)
        .read_to_end(&mut bytes)
        .map_err(fail)?;
    if bytes.is_empty() || bytes.len() as u64 > maximum {
        return Err(fail(
            "retained call is empty or exceeds carried lookup bound",
        ));
    }
    Ok(bytes)
}
fn call_digest(call: &[u8]) -> String {
    use sha2::Digest;
    crate::hex(&sha2::Sha256::digest(call))
}
fn lookup_payload(origin: &Value, call: &[u8], config_length: usize) -> Result<Vec<u8>> {
    let header =
        serde_json::to_vec(&json!({"algorithm":LOOKUP,"originIdentity":origin})).map_err(fail)?;
    // v2 envelope: version + config length + config + image digest + opcode.
    let size = 38usize
        .checked_add(config_length)
        .and_then(|n| n.checked_add(4 + header.len()))
        .and_then(|n| n.checked_add(call.len()));
    let maximum =
        crate::transport::CARRIED_LOOKUP_MAX_FRAME + 5 + crate::transport::MAX_CONFIG + 32;
    if header.len() > 1024
        || call.is_empty()
        || call.len() > crate::transport::MAX_CARRIED_CALL
        || config_length > crate::transport::MAX_CONFIG
        || size.is_none_or(|n| n > maximum)
    {
        return Err(fail(
            "carried lookup exceeds transport frame; exact call retained without transmission",
        ));
    }
    let mut result = Vec::with_capacity(4 + header.len() + call.len());
    result.extend_from_slice(&(header.len() as u32).to_le_bytes());
    result.extend(header);
    result.extend_from_slice(call);
    Ok(result)
}
fn lookup_outcome(
    response: &Value,
    origin: &Value,
    digest: &str,
    lower: &str,
    cut: &Point,
) -> Result<Value> {
    let response_fields = response
        .as_object()
        .ok_or_else(|| fail("carried lookup response is not an object"))?;
    if response_fields.len() != 4
        || response_fields.keys().any(|key| {
            !["algorithm", "originIdentity", "callDigest", "outcome"].contains(&key.as_str())
        })
    {
        return Err(fail("carried lookup response has unexpected fields"));
    }
    if response["algorithm"] != LOOKUP
        || response["originIdentity"] != *origin
        || response["callDigest"] != digest
    {
        return Err(fail(
            "carried lookup response does not bind exact call and origin",
        ));
    }
    let outcome = &response["outcome"];
    let allowed: &[&str] = match text(outcome, "type")? {
        "confirmed" => &[
            "type",
            "confirmation",
            "transactionId",
            "eventId",
            "acceptedCount",
            "worldRoot",
        ],
        "absent" => &["type"],
        "refused" => &["type", "reason"],
        _ => return Err(fail("carried lookup returned non-metadata outcome")),
    };
    let fields = outcome
        .as_object()
        .ok_or_else(|| fail("carried lookup outcome is not an object"))?;
    if fields.len() != allowed.len() || fields.keys().any(|key| !allowed.contains(&key.as_str())) {
        return Err(fail(
            "carried lookup returned unexpected content-bearing outcome fields",
        ));
    }
    match text(outcome, "type")? {
        "confirmed" => {
            if outcome["confirmation"] != "replayed" {
                return Err(fail(
                    "read-only carried lookup returned a non-replay confirmation",
                ));
            }
            for name in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
                decimal(text(outcome, name)?)?;
            }
            let height = text(outcome, "acceptedCount")?;
            if compare(height, lower) == Ordering::Less
                || compare(height, &cut.height) == Ordering::Greater
            {
                return Err(fail(
                    "carried lookup receipt lies outside its origin segment",
                ));
            }
        }
        "absent" => (),
        "refused" => {
            let reason = text(outcome, "reason")?;
            if ![
                "origin-mismatch",
                "malformed-call",
                "capsule-unavailable",
                "lookup-refused",
                "receipt-invalid",
            ]
            .contains(&reason)
            {
                return Err(fail(
                    "carried lookup refusal contains non-identifier metadata",
                ));
            }
        }
        _ => {
            return Err(fail(
                "carried lookup returned an unknown old-profile outcome",
            ))
        }
    }
    Ok(outcome.clone())
}
/// Intercept only old ordinary workspace calls, before the legacy attempt
/// manifest can pin an obsolete remote Host image. Always lookup; never submit.
pub(crate) fn retry_lookup(attempt: &Path, mode: &str, direct: bool) -> Result<Option<Value>> {
    let attempt = fs::canonicalize(attempt).map_err(fail)?;
    let Some(attempts) = attempt.parent() else {
        return Ok(None);
    };
    if attempts.file_name().and_then(|name| name.to_str()) != Some("attempts") {
        return Ok(None);
    }
    let Some(root) = attempts.parent() else {
        return Ok(None);
    };
    let manifest = match fs::symlink_metadata(root.join("workspace.json")) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(fail(error)),
        Ok(_) => read_json(&root.join("workspace.json"))?,
    };
    if manifest.get("receiptCarryLineage").is_none() {
        return Ok(None);
    }
    // Receipt-only recovery needs current transport and authenticated custody,
    // but neither a signing key nor current key-commitment entitlement.
    let workspace = workspace::load_for_key_transition(root)?;
    let ticket = begin(root, &workspace)?
        .ok_or_else(|| fail("carried workspace has no current continuity custody"))?;
    let custody = root.join(DIRECTORY);
    let archived = {
        let _lock = lock(&custody)?;
        recover_locked(root)?;
        history(root, &ticket.settings)?
    };
    let challenge = read_json_mode(&attempt.join("challenge.json"), false)?;
    let mut lower = "0".to_owned();
    let mut selected = None;
    for transition in archived {
        let origin = &transition["old"]["settings"]["identity"];
        let cut = point(&transition["verifiedEdge"]["oldCut"])?;
        if challenge["domain"] == origin["domain"] && challenge["semantics"] == origin["semantics"]
        {
            let (old_workspace, settings) = historical_source(root, &workspace, &transition)?;
            let source = HostProof::new(root, &old_workspace, &settings)?;
            let at = source.challenge_point(&challenge)?;
            if compare(&at.height, &lower) != Ordering::Less
                && compare(&at.height, &cut.height) != Ordering::Greater
            {
                selected = Some((origin.clone(), cut, lower.clone()));
                break;
            }
        }
        lower = point(&transition["verifiedEdge"]["newStart"])?.height;
    }
    let Some((origin, cut, lower)) = selected else {
        if challenge["domain"] == ticket.settings.identity["domain"]
            && challenge["semantics"] == ticket.settings.identity["semantics"]
        {
            return Ok(None);
        }
        return Err(fail(
            "retained attempt has no authenticated origin lineage; exact call retained",
        ));
    };
    if mode != "lookup" || direct {
        return Err(fail("old carried calls allow only read-only workspace lookup, never direct execution or resubmission"));
    }
    let original = read_json_mode(&attempt.join("attempt.json"), false)?;
    if original["format"] != "minidregg-resource-client-attempt-v1"
        || original["operation"] != "submit"
    {
        return Err(fail(
            "specialized old-call lookup is not supported; exact attempt retained",
        ));
    }
    let call = retained_call(&attempt.join("call.bin"))?;
    let digest = call_digest(&call);
    let config = workspace::member_path(&workspace, "config")?;
    let payload = lookup_payload(
        &origin,
        &call,
        fs::metadata(&config)
            .map_err(fail)?
            .len()
            .try_into()
            .map_err(fail)?,
    )?;
    let socket = SOCKET
        .get()
        .ok_or_else(|| fail("carried lookup requires current pinned socket"))?;
    let host = workspace::workspace_host(&workspace)?;
    let (binary, json_path) = crate::next_retry(&attempt)?;
    let frame = crate::session_invoke(&host, socket, &config, 153, &payload)?;
    // Reserve this retry evidence even when the returned protocol is malformed.
    create_file(&binary, &frame)?;
    save(
        &attempt,
        binary
            .with_extension("transport.json")
            .file_name()
            .unwrap()
            .to_str()
            .unwrap(),
        &json!({"type":"minidregg-carried-call-lookup-transport-v1","originIdentity":origin,
        "callDigest":digest,"operation":153,"hostSha256":crate::host_image_sha256(&host)?,"config":config,"socket":socket,
        "responseEncoding":"op153-byte-then-json"}),
    )?;
    if frame.first() != Some(&153) || frame.len() as u64 > MAX_JSON + 1 {
        return Err(fail(
            "carried lookup response refused or exceeded bound; exact evidence retained",
        ));
    }
    if retained_call(&attempt.join("call.bin"))? != call {
        return Err(fail("retained exact call changed during lookup"));
    }
    let response: Value = serde_json::from_slice(&frame[1..]).map_err(fail)?;
    let outcome = lookup_outcome(&response, &origin, &digest, &lower, &cut)?;
    create_file(&json_path, &serde_json::to_vec(&outcome).map_err(fail)?)?;
    directory(&attempt)?.sync_all().map_err(fail)?;
    finish_attempt(
        Some(AttemptTicket {
            root: root.to_path_buf(),
            workspace,
            ticket: Some(ticket),
        }),
        &outcome,
        true,
    )?;
    Ok(Some(outcome))
}
