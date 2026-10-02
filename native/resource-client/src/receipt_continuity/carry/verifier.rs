//! Explicit bootstrap of the generic public carry verifier. This does not
//! replace the source Host that owns ordinary receipt interpretation.
use super::*;

const PIN_FILE: &str = "carry-verifier.json";
const PIN_TYPE: &str = "minidregg-carry-verifier-pin-v1";
const PROFILE: &str = "minidregg-carry-verifier-v1";

pub(super) struct Selection {
    pub executable: PathBuf,
    pub config: PathBuf,
    pub pin: Option<Value>,
}

fn marker(workspace: &Value) -> Result<bool> {
    match workspace.get("receiptCarryVerifier") {
        None => Ok(false),
        Some(Value::String(value)) if value == PIN_TYPE => Ok(true),
        _ => Err(fail("unknown portable carry verifier marker")),
    }
}
fn authority(custody: &Path, settings: &Settings, retained: &Point) -> Result<Value> {
    let pin = read_json(&custody.join(AUTHORITY))?;
    if pin["type"] != "minidregg-carry-authority-v1" || pin["identity"] != settings.identity {
        return Err(fail(
            "portable carry verifier requires the current locally pinned carry authority",
        ));
    }
    hex64(text(&pin, "operatorPublicKey")?)?;
    let at = point(&pin["anchor"])?;
    if compare(&at.height, &retained.height) == Ordering::Greater
        || (at.height == retained.height && at != *retained)
    {
        return Err(fail(
            "carry authority anchor is not retained current lineage",
        ));
    }
    Ok(pin)
}
fn description(value: &Value, identity: &Value, pins: &Value) -> Result<()> {
    let expected = json!({"algorithm":PROFILE,"identity":identity,"sourceCapsulePins":pins,"edgeAlgorithm":EDGE});
    if *value != expected {
        return Err(fail(
            "portable carry verifier description differs from trusted source identity or capsule",
        ));
    }
    Ok(())
}

pub(crate) fn install(
    root: &Path,
    workspace: &Value,
    executable: &Path,
    expected_sha256: &str,
) -> Result<Value> {
    hex64(expected_sha256)?;
    if !executable.is_absolute() {
        return Err(fail(
            "portable carry verifier must be an explicit absolute path",
        ));
    }
    let custody = root.join(DIRECTORY);
    let _lock = lock(&custody)?;
    recover_locked(root)?;
    same_manifest(root, workspace)?;
    marker(workspace)?;
    let old = Settings::load(&custody)?;
    old.check(&workspace::member_path(workspace, "config")?)?;
    let retained = anchor(&custody, &old)?;
    let authority = authority(&custody, &old, &retained)?;
    let (capsule, pins) = registered_capsule(
        &custody,
        &authority,
        Path::new(text(&authority, "sourceCapsulePath")?),
    )?;
    // Never execute an installer-selected artifact until its explicit hash agrees.
    if crate::host_image_sha256(executable)? != expected_sha256 {
        return Err(fail(
            "portable carry verifier differs from explicitly supplied SHA-256",
        ));
    }
    let scratch = custody.join(format!(
        "carry-verifier-install-{}",
        workspace::random_nonce()?
    ));
    workspace::make_private_dir(&scratch)?;
    directory(&custody)?.sync_all().map_err(fail)?;
    let request =
        json!({"oldIdentity":old.identity,"sourceCapsulePath":capsule,"sourceCapsulePins":pins});
    save(&scratch, "request.json", &request)?;
    create_file(&scratch.join("result.json"), b"")?;
    let status = Command::new(executable)
        .arg(capsule.join("original-config.json"))
        .arg("carry-verifier-profile")
        .arg(scratch.join("request.json"))
        .arg(scratch.join("result.json"))
        .output()
        .map_err(fail)?;
    if !status.status.success() {
        return Err(fail(
            "portable carry verifier refused registered source profile",
        ));
    }
    description(
        &read_json(&scratch.join("result.json"))?,
        &old.identity,
        &pins,
    )?;
    if crate::host_image_sha256(executable)? != expected_sha256 {
        return Err(fail("portable carry verifier changed during installation"));
    }
    registered_capsule(&custody, &authority, &capsule)?;
    let pin = json!({"type":PIN_TYPE,"verifier":executable,"verifierSha256":expected_sha256,
        "identity":old.identity,"sourceCapsulePath":capsule,"sourceCapsulePins":pins});
    // Marker first: a crash before pin fsync disables carry until explicit
    // reinstall, rather than allowing fallback to a different executable.
    let mut manifest = workspace.clone();
    manifest["receiptCarryVerifier"] = json!(PIN_TYPE);
    save(root, "workspace.json", &manifest)?;
    save(&custody, PIN_FILE, &pin)?;
    Ok(
        json!({"type":"minidregg-carry-verifier-installed-v1","identity":old.identity,
        "verifier":executable,"verifierSha256":expected_sha256,"sourceCapsulePath":capsule,"point":retained.json()}),
    )
}

/// Called only while current custody and authority are locked and validated.
pub(super) fn select(
    custody: &Path,
    workspace: &Value,
    old: &Settings,
    capsule: &Path,
    pins: &Value,
    ordinary_config: &Path,
) -> Result<Selection> {
    let installed = marker(workspace)?;
    match fs::symlink_metadata(custody.join(PIN_FILE)) {
        Err(error) if error.kind()==std::io::ErrorKind::NotFound && !installed => {
            return Ok(Selection {executable:old.verifier.clone(),config:ordinary_config.to_path_buf(),pin:None});
        }
        Err(error) if error.kind()==std::io::ErrorKind::NotFound => return Err(fail("installed portable carry verifier pin is missing; reinstall explicitly or restore custody")),
        Err(error)=>return Err(fail(error)), Ok(_)=>(),
    }
    // No unmarked executable can become an implicit bootstrap source.
    if !installed {
        return Err(fail(
            "portable carry verifier pin lacks durable install marker; reinstall explicitly",
        ));
    }
    let pin = read_json(&custody.join(PIN_FILE))?;
    if pin["type"] != PIN_TYPE
        || pin["identity"] != old.identity
        || pin["sourceCapsulePins"] != *pins
        || pin["sourceCapsulePath"] != capsule.to_string_lossy().as_ref()
    {
        return Err(fail(
            "portable carry verifier belongs to another identity or source capsule",
        ));
    }
    let executable = PathBuf::from(text(&pin, "verifier")?);
    let digest = text(&pin, "verifierSha256")?;
    hex64(digest)?;
    if !executable.is_absolute() || crate::host_image_sha256(&executable)? != digest {
        return Err(fail("pinned portable carry verifier image changed"));
    }
    Ok(Selection {
        executable,
        config: capsule.join("original-config.json"),
        pin: Some(pin),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;
    struct Fixture {
        root: PathBuf,
        workspace: Value,
        portable: PathBuf,
        reply: PathBuf,
        executed: PathBuf,
        capsule: PathBuf,
        pins: Value,
        settings: Settings,
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.root).unwrap();
        }
    }
    fn executable(path: &Path, source: &str) {
        create_file(path, source.as_bytes()).unwrap();
        fs::set_permissions(path, fs::Permissions::from_mode(0o700)).unwrap();
    }
    fn fixture() -> Fixture {
        let root = std::env::temp_dir().join(format!(
            "mini-carry-bootstrap-{}-{}",
            std::process::id(),
            workspace::random_nonce().unwrap()
        ));
        workspace::make_private_dir(&root).unwrap();
        let custody = root.join(DIRECTORY);
        workspace::make_private_dir(&custody).unwrap();
        let host = root.join("old-host");
        let helper = root.join("crypto");
        let portable = root.join("portable");
        let reply = root.join("description.json");
        let executed = root.join("executed");
        executable(&host, "#!/bin/sh\ncat \"$1\"\n");
        executable(&helper, "#!/bin/sh\nexit 0\n");
        executable(
            &portable,
            &format!(
                "#!/bin/sh\nprintf yes > '{}'\ncp '{}' \"$4\"\n",
                executed.display(),
                reply.display()
            ),
        );
        let identity =
            json!({"algorithm":ALGORITHM,"domain":"1","semantics":"2","expectedSeed":"3"});
        let mut config = identity.clone();
        config["signatureBinary"] = json!(helper);
        save(&root, "config.json", &config).unwrap();
        let settings = Settings {
            identity,
            verifier: host.clone(),
            verifier_sha256: crate::host_image_sha256(&host).unwrap(),
        };
        let point = Point {
            height: "1".into(),
            world_root: "17".into(),
            witness: Some(("7".into(), vec!["3".into(); 256])),
        };
        save(&custody, "enabled.json", &settings.json()).unwrap();
        persist(&custody, &settings, &point).unwrap();
        let workspace = json!({"receiptContinuity":ALGORITHM,"config":root.join("config.json"),"host":host,"hostSha256":settings.verifier_sha256,"freshContinuity":{"id":"untouched"}});
        save(&root, "workspace.json", &workspace).unwrap();
        let authority = pin_authority(&root, &workspace, &"b".repeat(64)).unwrap();
        let capsule = PathBuf::from(text(&authority, "sourceCapsulePath").unwrap());
        let pins = read_json(&capsule.join("pins.json")).unwrap();
        save(&root,"description.json",&json!({"algorithm":PROFILE,"identity":settings.identity,"sourceCapsulePins":pins,"edgeAlgorithm":EDGE})).unwrap();
        Fixture {
            root,
            workspace,
            portable,
            reply,
            executed,
            capsule,
            pins,
            settings,
        }
    }
    #[test]
    fn portable_install_preserves_ordinary_custody_and_missing_pin_never_falls_back() {
        let f = fixture();
        let custody = f.root.join(DIRECTORY);
        let anchor_before = fs::read(custody.join("anchor.json")).unwrap();
        let enabled_before = fs::read(custody.join("enabled.json")).unwrap();
        let profile_before = fs::read(f.capsule.join("profile.json")).unwrap();
        let authority_before = fs::read(custody.join(AUTHORITY)).unwrap();
        let hash = crate::host_image_sha256(&f.portable).unwrap();
        install(&f.root, &f.workspace, &f.portable, &hash).unwrap();
        assert!(f.executed.exists());
        for (file, before) in [
            ("anchor.json", anchor_before),
            ("enabled.json", enabled_before),
            (AUTHORITY, authority_before),
        ] {
            assert_eq!(fs::read(custody.join(file)).unwrap(), before);
        }
        assert_eq!(
            fs::read(f.capsule.join("profile.json")).unwrap(),
            profile_before
        );
        let manifest = read_json(&f.root.join("workspace.json")).unwrap();
        assert_eq!(manifest["freshContinuity"], f.workspace["freshContinuity"]);
        let selected = select(
            &custody,
            &manifest,
            &f.settings,
            &f.capsule,
            &f.pins,
            &f.root.join("config.json"),
        )
        .unwrap();
        assert_eq!(selected.executable, f.portable);
        assert_eq!(selected.config, f.capsule.join("original-config.json"));
        fs::remove_file(custody.join(PIN_FILE)).unwrap();
        assert!(select(
            &custody,
            &manifest,
            &f.settings,
            &f.capsule,
            &f.pins,
            &f.root.join("config.json")
        )
        .err()
        .unwrap()
        .contains("missing"));
        // The marker-before-pin crash window can only be repaired by explicit install.
        install(&f.root, &manifest, &f.portable, &hash).unwrap();
        assert!(anchor(&custody, &f.settings).is_ok());
        f.settings.check(&f.root.join("config.json")).unwrap();
    }
    #[test]
    fn portable_wrong_hash_never_executes_and_wrong_identity_cannot_install() {
        let f = fixture();
        let custody = f.root.join(DIRECTORY);
        assert!(install(&f.root, &f.workspace, &f.portable, &"0".repeat(64))
            .unwrap_err()
            .contains("SHA-256"));
        assert!(!f.executed.exists());
        assert!(!custody.join(PIN_FILE).exists());
        let mut reply = read_json(&f.reply).unwrap();
        reply["identity"]["semantics"] = json!("999");
        save(&f.root, "description.json", &reply).unwrap();
        assert!(install(
            &f.root,
            &f.workspace,
            &f.portable,
            &crate::host_image_sha256(&f.portable).unwrap()
        )
        .unwrap_err()
        .contains("description differs"));
        assert!(!custody.join(PIN_FILE).exists());
        assert_eq!(
            read_json(&f.root.join("workspace.json")).unwrap(),
            f.workspace
        );
    }
    #[test]
    fn portable_stale_capsule_and_missing_anchor_refuse_before_execution() {
        let f = fixture();
        fs::write(f.capsule.join("profile.json"), b"changed").unwrap();
        assert!(install(
            &f.root,
            &f.workspace,
            &f.portable,
            &crate::host_image_sha256(&f.portable).unwrap()
        )
        .is_err());
        assert!(!f.executed.exists());
        let f = fixture();
        fs::remove_file(f.root.join(DIRECTORY).join("anchor.json")).unwrap();
        assert!(install(
            &f.root,
            &f.workspace,
            &f.portable,
            &crate::host_image_sha256(&f.portable).unwrap()
        )
        .is_err());
        assert!(!f.executed.exists());
    }
    #[test]
    fn portable_pin_rejects_changed_artifact_or_unrelated_lineage() {
        let f = fixture();
        let custody = f.root.join(DIRECTORY);
        install(
            &f.root,
            &f.workspace,
            &f.portable,
            &crate::host_image_sha256(&f.portable).unwrap(),
        )
        .unwrap();
        let manifest = read_json(&f.root.join("workspace.json")).unwrap();
        let mut changed = f.pins.clone();
        changed["profileSha256"] = json!("f".repeat(64));
        assert!(select(
            &custody,
            &manifest,
            &f.settings,
            &f.capsule,
            &changed,
            &f.root.join("config.json")
        )
        .is_err());
        let mut settings = f.settings.clone();
        settings.identity["semantics"] = json!("new");
        assert!(select(
            &custody,
            &manifest,
            &settings,
            &f.capsule,
            &f.pins,
            &f.root.join("config.json")
        )
        .is_err());
        fs::write(&f.portable, b"tampered executable").unwrap();
        assert!(select(
            &custody,
            &manifest,
            &f.settings,
            &f.capsule,
            &f.pins,
            &f.root.join("config.json")
        )
        .err()
        .unwrap()
        .contains("image changed"));
    }
}
