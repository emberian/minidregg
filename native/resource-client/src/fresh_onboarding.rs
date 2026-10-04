//! Automatic first trust for a newly created workspace. The retained candidate is
//! enrollment evidence, never a second advancing anchor. All proof decisions and
//! physical custody operations reuse receipt_continuity.
use super::*;

pub(super) const RECORD: &str = "receipt-continuity.pending.json";
const TYPE: &str = "minidregg-fresh-continuity-v1";

/// Receipt provenance must come from the source-decoded exact enrollment lookup,
/// not directly from a sponsor welcome. Only the join admission path constructs it.
pub(crate) enum FreshBaseline<'a> {
    Reference(&'a Value),
    AdmittedReceipt(&'a Value),
}
fn receipt_point(value: &Value) -> Result<Point> {
    if value["type"] != "minidregg-authenticated-enrollment-receipt-v1" {
        return Err(fail("unknown admitted receipt provenance"));
    }
    for name in ["ingressSha256", "lookupFrameSha256"] {
        let digest = text(value, name)?;
        if digest.len() != 64
            || !mini_sdk::hex::is_lower(digest)
        {
            return Err(fail("invalid admission evidence digest"));
        }
    }
    for name in ["transactionId", "eventId"] {
        decimal(text(&value["receipt"], name)?)?;
    }
    Point::parse(
        &json!({"height":value["receipt"]["acceptedCount"],"worldRoot":value["receipt"]["worldRoot"]}),
    )
}
fn baseline_target(source: &HostProof<'_>, record: &Value, challenge: &Value) -> Result<Point> {
    match record.get("admittedReceipt") {
        Some(receipt) => receipt_point(receipt),
        None => source.challenge_point(challenge),
    }
}

pub(crate) fn verifier_pin(config: &Path, verifier: &Path) -> Result<Value> {
    let verifier = crate::absolute(verifier)?;
    let verifier_sha256 = crate::host_image_sha256(&verifier)?;
    let config_bytes = crate::agent_reserve::bounded(config, MAX_JSON as usize)?;
    Ok(Settings {
        identity: local_identity(&verifier, &verifier_sha256, config, &config_bytes)?,
        verifier_sha256,
        verifier,
    }
    .json())
}
/// Creation evidence lives outside the workspace it protects. Reuse custody's
/// nofollow/private atomic save and directory fsync, under the caller's join lock.
pub(crate) fn retain_workspace_creation(root: &Path, value: &Value) -> Result<()> {
    let path = root.join("workspace-created.json");
    match fs::symlink_metadata(&path) {
        Ok(_) => {
            if read_json(&path)? != *value {
                return Err(fail("join workspace creation evidence changed"));
            }
            directory(root)?.sync_all().map_err(fail)
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            save(root, "workspace-created.json", value)
        }
        Err(error) => Err(fail(error)),
    }
}
fn reference_pin(reference: &Value) -> Result<Value> {
    let name = text(reference, "name")?;
    workspace::validate_name(name)?;
    let kind = text(reference, "kind")?;
    if !matches!(kind, "account" | "object" | "program") {
        return Err(fail("unknown fresh reference kind"));
    }
    for field in ["target", "observeCapability"] {
        workspace::decimal(text(reference, field)?, field)?;
    }
    Ok(json!({"name":name,"kind":kind,"target":reference["target"],
        "observeCapability":reference["observeCapability"]}))
}
fn binding(workspace: &Value) -> Value {
    // Do not retain the staged workspace path: paid onboarding atomically moves it.
    json!({"subject":workspace["subject"],"key":workspace["key"],
        "config":workspace["config"],"host":workspace["host"],
        "hostSha256":workspace["hostSha256"],"socket":workspace["socket"],
        "sshIdentity":workspace["sshIdentity"]})
}
fn config_sha(workspace: &Value) -> Result<String> {
    crate::host_image_sha256(&workspace::member_path(workspace, "config")?)
}

/// Called only within workspace's successful create-new path, before its manifest
/// is published. No read, import, or generic recovery path can manufacture this pin.
pub(crate) fn prepare(
    root: &Path,
    workspace: &mut Value,
    baseline: FreshBaseline<'_>,
    verifier: Option<&Path>,
) -> Result<()> {
    let (reference, admitted) = match baseline {
        FreshBaseline::Reference(reference) => (Some(reference_pin(reference)?), None),
        FreshBaseline::AdmittedReceipt(receipt) => {
            receipt_point(receipt)?;
            (None, Some(receipt.clone()))
        }
    };
    if fs::symlink_metadata(root.join("workspace.json")).is_ok()
        || fs::symlink_metadata(root.join(RECORD)).is_ok()
        || fs::symlink_metadata(root.join(DIRECTORY)).is_ok()
    {
        return Err(fail(
            "fresh pin requires a newly created unpublished workspace",
        ));
    }
    let selected = match verifier {
        Some(path) => path.to_path_buf(),
        None => workspace::workspace_host(workspace)?,
    };
    if selected.as_os_str().is_empty() {
        return Err(fail(
            "fresh remote onboarding requires a pinned local --verifier",
        ));
    }
    let verifier = crate::absolute(&selected)?;
    let config = workspace::member_path(workspace, "config")?;
    let verifier_sha256 = crate::host_image_sha256(&verifier)?;
    let config_bytes = crate::agent_reserve::bounded(&config, MAX_JSON as usize)?;
    let settings = Settings {
        identity: local_identity(&verifier, &verifier_sha256, &config, &config_bytes)?,
        verifier_sha256,
        verifier,
    };
    let enrollment = workspace::random_nonce()?;
    let mut record = json!({"type":TYPE,"enrollment":enrollment,"state":"awaiting-first-read",
        "settings":settings.json(),"configSha256":crate::hex(&<sha2::Sha256 as sha2::Digest>::digest(&config_bytes)),
        "workspace":binding(workspace)});
    if let Some(reference) = reference {
        record["reference"] = reference;
    }
    if let Some(admitted) = admitted {
        record["admittedReceipt"] = admitted;
    }
    save(root, RECORD, &record)?;
    workspace["freshContinuity"] = json!(enrollment);
    Ok(())
}

fn retained(root: &Path, workspace: &Value) -> Result<Value> {
    let record = read_json(&root.join(RECORD))?;
    if record["type"] != TYPE
        || record["enrollment"].as_str().is_none()
        || record["enrollment"] != workspace["freshContinuity"]
    {
        return Err(fail("fresh enrollment pin or configuration changed"));
    }
    // After completion, verified carry transitions may change the deployment and
    // verifier. Current custody owns those pins; this record is initial provenance.
    if record["state"] != "complete"
        && (record["workspace"] != binding(workspace)
            || record["configSha256"].as_str() != Some(config_sha(workspace)?.as_str()))
    {
        return Err(fail("pending fresh enrollment configuration changed"));
    }
    match (record.get("reference"), record.get("admittedReceipt")) {
        (Some(reference), None) => {
            if reference_pin(reference)? != *reference {
                return Err(fail("fresh reference pin is not canonical"));
            }
            if record["state"] != "complete" {
                let current = workspace::reference(root, text(reference, "name")?)?;
                if reference_pin(&current)? != *reference {
                    return Err(fail("fresh onboarding reference differs from retained pin"));
                }
            }
        }
        (None, Some(receipt)) => {
            receipt_point(receipt)?;
        }
        _ => {
            return Err(fail(
                "fresh enrollment requires exactly one baseline source",
            ))
        }
    }
    Ok(record)
}

/// Ordinary requests cannot silently treat interrupted fresh onboarding as legacy.
pub(super) fn guard(root: &Path, workspace: &Value) -> Result<()> {
    let exists = fs::symlink_metadata(root.join(RECORD)).is_ok();
    if workspace.get("freshContinuity").is_none() && !exists {
        return Ok(());
    }
    let record = retained(root, workspace)?;
    if record["state"] != "complete" || workspace["receiptContinuity"] != ALGORITHM {
        return Err(fail(
            "fresh onboarding is incomplete; resume the onboarding operation",
        ));
    }
    // Current identity, config and verifier are exclusively governed by begin()
    // and its settings, including explicit verifier upgrades and verified carry.
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Stage {
    Candidate,
    Directory,
    Anchor,
    Enabled,
    Manifest,
    Complete,
}

pub(crate) fn complete(
    root: &Path,
    workspace: &Value,
    read: impl FnOnce(&Value) -> Result<Value>,
) -> Result<Value> {
    complete_with(root, workspace, read, |_| Ok(()))
}
fn complete_with(
    root: &Path,
    workspace: &Value,
    read: impl FnOnce(&Value) -> Result<Value>,
    mut stage: impl FnMut(Stage) -> Result<()>,
) -> Result<Value> {
    let _onboarding = lock_named(root, "continuity-onboarding.lock")?;
    let manifest = read_json(&root.join("workspace.json"))?;
    if manifest != *workspace {
        return Err(fail(
            "workspace changed during onboarding; reload and resume",
        ));
    }
    let mut record = retained(root, workspace)?;
    let custody = root.join(DIRECTORY);
    let settings = Settings::parse(&record["settings"])?;
    if record["state"] == "complete" {
        let ticket = begin(root, workspace)?
            .ok_or_else(|| fail("completed enrollment lost continuity custody"))?;
        return Ok(
            json!({"type":"minidregg-fresh-continuity-ready-v1", "status":"verified",
            "identity":ticket.settings.identity,"point":ticket.baseline.json()}),
        );
    }
    settings.check(&workspace::member_path(workspace, "config")?)?;
    let source = HostProof::new(root, workspace, &settings)?;
    let resumed = record["state"] == "verified-candidate";
    match record["state"].as_str() {
        Some("awaiting-first-read") => {
            if manifest.get("receiptContinuity").is_some() || fs::symlink_metadata(&custody).is_ok()
            {
                return Err(fail(
                    "awaiting enrollment has unexpected prior custody; cannot rebootstrap",
                ));
            }
            let challenge = if record.get("admittedReceipt").is_some() {
                Value::Null
            } else {
                read(&record["reference"])?
            };
            let target = baseline_target(&source, &record, &challenge)?;
            let request = json!({"identity":settings.identity,"from":null,"target":target.json()});
            let response = source.response(&request)?;
            let (verified, complete) = source.verify_response(&request, &response)?;
            if !complete || verified != target {
                return Err(fail(
                    "first proof does not establish the exact signed observation",
                ));
            }
            record["candidate"] = json!({"challenge":challenge,"request":request,
                "response":serde_json::from_slice::<Value>(&response).map_err(fail)?});
            record["state"] = json!("verified-candidate");
            // A crash after this save must finish this exact candidate, never read
            // a replacement head. The proof survives before any custody exists.
            save(root, RECORD, &record)?;
            stage(Stage::Candidate)?;
        }
        Some("verified-candidate") => (),
        _ => return Err(fail("unknown fresh enrollment state")),
    }
    let candidate = &record["candidate"];
    let target = baseline_target(&source, &record, &candidate["challenge"])?;
    let expected = json!({"identity":settings.identity,"from":null,"target":target.json()});
    if candidate["request"] != expected {
        return Err(fail("retained candidate request changed"));
    }
    let (verified, complete) = source.verify_response(
        &expected,
        &serde_json::to_vec(&candidate["response"]).map_err(fail)?,
    )?;
    if !complete || verified != target {
        return Err(fail(
            "retained candidate proof does not establish its exact target",
        ));
    }
    match fs::symlink_metadata(&custody) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            if manifest.get("receiptContinuity").is_some() {
                return Err(fail("enabled candidate custody disappeared"));
            }
            crate::fsio::create_private_dir(&custody)?;
            directory(root)?.sync_all().map_err(fail)?;
        }
        Err(e) => return Err(fail(e)),
        Ok(_) => (),
    }
    stage(Stage::Directory)?;
    let _custody = lock(&custody)?;
    if fs::symlink_metadata(custody.join("anchor.json")).is_ok() {
        let existing = anchor(&custody, &settings)?;
        if existing != verified || existing.witness != verified.witness {
            return Err(fail(
                "interrupted candidate custody differs; refusing replacement",
            ));
        }
    } else {
        if fs::symlink_metadata(custody.join("enabled.json")).is_ok()
            || manifest.get("receiptContinuity").is_some()
        {
            return Err(fail("enabled candidate anchor disappeared"));
        }
        persist(&custody, &settings, &verified)?;
    }
    stage(Stage::Anchor)?;
    if fs::symlink_metadata(custody.join("enabled.json")).is_ok() {
        if Settings::load(&custody)?.json() != settings.json() {
            return Err(fail("interrupted candidate verifier settings changed"));
        }
    } else {
        if manifest.get("receiptContinuity").is_some() {
            return Err(fail("enabled candidate settings disappeared"));
        }
        save(&custody, "enabled.json", &settings.json())?;
    }
    stage(Stage::Enabled)?;
    let mut manifest = manifest;
    if manifest.get("receiptContinuity").is_some() && manifest["receiptContinuity"] != ALGORITHM {
        return Err(fail("candidate workspace continuity mode changed"));
    }
    manifest["receiptContinuity"] = json!(ALGORITHM);
    save(root, "workspace.json", &manifest)?;
    stage(Stage::Manifest)?;
    record["state"] = json!("complete");
    save(root, RECORD, &record)?;
    stage(Stage::Complete)?;
    Ok(json!({"type":"minidregg-fresh-continuity-ready-v1",
        "status":if resumed { "resumed" } else { "established" },
        "identity":settings.identity,"point":verified.json()}))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;
    struct Fixture {
        base: PathBuf,
        root: PathBuf,
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.base).unwrap();
        }
    }
    // This unit fixture starts at the fresh-custody boundary. It does not
    // simulate initializer key admission; the common receiving journey covers it.
    fn custody_workspace(base: &Path, root: &Path, baseline: FreshBaseline<'_>) {
        workspace::make_private_dir(root).unwrap();
        for name in ["refs","sources","attempts","proposals"] {
            workspace::make_private_dir(&root.join(name)).unwrap();
        }
        let mut manifest=json!({"type":"minidregg-participant-workspace-v1",
            "host":base.join("verifier"),"config":base.join("config.json"),
            "key":base.join("key"),"subject":"20","socket":null,"prerotation":false});
        prepare(root,&mut manifest,baseline,Some(&base.join("verifier"))).unwrap();
        save(root,"workspace.json",&manifest).unwrap();
    }
    fn resume_custody(root: &Path) -> Result<Value> {
        complete(root,&read_json(&root.join("workspace.json"))?, |_| Err("unexpected fresh read in custody fixture".into()))
    }
    impl Fixture {
        fn new() -> Self {
            let base = std::env::temp_dir()
                .join(format!("mini-fresh-{}", workspace::random_nonce().unwrap()));
            workspace::make_private_dir(&base).unwrap();
            let host = base.join("verifier");
            // Protocol fixture only. Cryptographic decisions are exercised against
            // the real source Host by fresh-onboarding-journey.sh.
            create_file(&host, br#"#!/usr/bin/python3
import json,sys
profile={'domain':'1','semantics':'2','expectedSeed':'3'}
if sys.argv[2]=='profile': print(json.dumps(profile))
elif sys.argv[2]=='continuity-point':
 x=json.load(open(sys.argv[3])); json.dump(x,open(sys.argv[4],'w'))
elif sys.argv[2]=='continuity-verify':
 q=json.load(open(sys.argv[3])); r=json.load(open(sys.argv[4]))
 assert q['target']==r['to'] and q['identity']==r['identity']
 assert r['endChain']=='14' and r['toSiblings']==['3'] and r['suffix']==[]
 json.dump({'to':r['to'],'complete':True,'chain':r['endChain'],'siblings':r['toSiblings']},open(sys.argv[5],'w'))
else: sys.exit(2)
"#).unwrap();
            fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
            let config = base.join("config.json");
            create_file(&config, b"{}").unwrap();
            let key = base.join("key");
            create_file(&key, &[0; 32]).unwrap();
            let root = base.join("workspace");
            custody_workspace(&base,&root,FreshBaseline::Reference(
                &json!({"name":"account","kind":"account","target":"20","observeCapability":"30"})));
            workspace::import(
                &root,
                workspace::ImportInput {
                    name: "account",
                    kind: "account",
                    target: "20",
                    observe: "30",
                    operation: None,
                    control: None,
                    provenance: None,
                    room: None,
                },
            )
            .unwrap();
            Self { base, root }
        }
        fn manifest(&self) -> Value {
            read_json(&self.root.join("workspace.json")).unwrap()
        }
        fn candidate(&self) {
            let mut record = read_json(&self.root.join(RECORD)).unwrap();
            let identity = record["settings"]["identity"].clone();
            let point = json!({"height":"2","worldRoot":"34"});
            record["candidate"] = json!({"challenge":point,
                "request":{"identity":identity,"from":null,"target":point},
                "response":{"identity":identity,"from":point,"to":point,"startChain":"14","endChain":"14",
                    "fromSiblings":["3"],"toSiblings":["3"],"suffix":[],"complete":true}});
            record["state"] = json!("verified-candidate");
            save(&self.root, RECORD, &record).unwrap();
        }
    }
    #[test]
    fn admitted_receipt_candidate_needs_no_resource_reference_or_read() {
        let mut f = Fixture::new();
        let receipt = json!({"type":"minidregg-authenticated-enrollment-receipt-v1",
            "receipt":{"transactionId":"1","eventId":"2","acceptedCount":"2","worldRoot":"34"},
            "ingressSha256":"a".repeat(64),"lookupFrameSha256":"b".repeat(64)});
        let root = f.base.join("receipt-workspace");
        custody_workspace(&f.base,&root,FreshBaseline::AdmittedReceipt(&receipt));
        f.root = root;
        f.candidate();
        assert_eq!(fs::read_dir(f.root.join("refs")).unwrap().count(), 0);
        let result = complete_with(
            &f.root,
            &f.manifest(),
            |_| panic!("receipt baseline never reads a resource"),
            |_| Ok(()),
        )
        .unwrap();
        assert_eq!(result["point"], json!({"height":"2","worldRoot":"34"}));
        assert!(begin(&f.root, &f.manifest()).unwrap().is_some());
        fs::remove_file(f.root.join(DIRECTORY).join("anchor.json")).unwrap();
        assert!(resume_custody(&f.root).is_err());
    }

    #[test]
    fn fresh_init_pin_blocks_legacy_read_and_manual_rebootstrap() {
        let f = Fixture::new();
        assert!(begin(&f.root, &f.manifest())
            .err()
            .unwrap()
            .contains("incomplete"));
        assert!(initialize(&f.root, &f.manifest(), None, || panic!("no read")).is_err());
        let error = complete_with(
            &f.root,
            &f.manifest(),
            |_| Err("interrupted first read".into()),
            |_| Ok(()),
        )
        .unwrap_err();
        assert_eq!(error, "interrupted first read");
        assert_eq!(
            read_json(&f.root.join(RECORD)).unwrap()["state"],
            "awaiting-first-read"
        );
        assert!(!f.root.join(DIRECTORY).exists());
        fs::remove_file(f.root.join(RECORD)).unwrap();
        assert!(begin(&f.root, &f.manifest()).is_err());
        assert!(resume_custody(&f.root).is_err());
    }
    #[test]
    fn every_interrupted_install_resumes_exact_candidate_through_shared_helper() {
        for stop in [
            Stage::Candidate,
            Stage::Directory,
            Stage::Anchor,
            Stage::Enabled,
            Stage::Manifest,
        ] {
            let f = Fixture::new();
            f.candidate();
            // Candidate is already durably saved; this stage models interruption
            // immediately after that save, before any custody file exists.
            if stop != Stage::Candidate {
                assert!(complete_with(
                    &f.root,
                    &f.manifest(),
                    |_| panic!("candidate must not read new head"),
                    |stage| if stage == stop {
                        Err("interrupted".into())
                    } else {
                        Ok(())
                    }
                )
                .is_err());
            }
            assert!(begin(&f.root, &f.manifest()).is_err());
            let result = resume_custody(&f.root).unwrap();
            assert_eq!(result["status"], "resumed");
            assert_eq!(result["point"]["height"], "2");
            assert!(begin(&f.root, &f.manifest()).unwrap().is_some());
            assert_eq!(
                read_json(&f.root.join(RECORD)).unwrap()["state"],
                "complete"
            );
        }
    }
    #[test]
    fn candidate_tampering_pin_changes_and_conflicting_custody_fail() {
        for mutation in [
            "config",
            "verifier",
            "reference",
            "request",
            "proof",
            "anchor",
        ] {
            let f = Fixture::new();
            f.candidate();
            match mutation {
                "config" => fs::write(f.base.join("config.json"), b"{\"changed\":true}").unwrap(),
                "verifier" => fs::write(f.base.join("verifier"), b"#!/bin/sh\nexit 0\n").unwrap(),
                "reference" => {
                    let p = f.root.join("refs/account.json");
                    let mut r = read_json(&p).unwrap();
                    r["target"] = json!("21");
                    save(&f.root.join("refs"), "account.json", &r).unwrap();
                }
                "anchor" => {
                    fs::DirBuilder::new()
                        .mode(0o700)
                        .create(f.root.join(DIRECTORY))
                        .unwrap();
                    let settings =
                        Settings::parse(&read_json(&f.root.join(RECORD)).unwrap()["settings"])
                            .unwrap();
                    let p = Point::parse(&json!({"height":"3","worldRoot":"51"}))
                        .unwrap()
                        .with_witness(&json!({"chain":"14","siblings":["3"]}))
                        .unwrap();
                    persist(&f.root.join(DIRECTORY), &settings, &p).unwrap();
                }
                _ => {
                    let mut r = read_json(&f.root.join(RECORD)).unwrap();
                    if mutation == "proof" {
                        r["candidate"]["response"]["endChain"] = json!("99");
                    } else {
                        r["candidate"]["request"]["target"]["height"] = json!("3");
                    }
                    save(&f.root, RECORD, &r).unwrap();
                }
            }
            assert!(
                resume_custody(&f.root).is_err(),
                "{mutation}"
            );
            assert_ne!(
                read_json(&f.root.join(RECORD)).unwrap()["state"],
                "complete"
            );
        }
    }
    #[test]
    fn completed_custody_loss_is_never_first_use() {
        for missing in ["anchor.json", "enabled.json", "directory", "record"] {
            let f = Fixture::new();
            f.candidate();
            resume_custody(&f.root).unwrap();
            match missing {
                "directory" => fs::remove_dir_all(f.root.join(DIRECTORY)).unwrap(),
                "record" => fs::remove_file(f.root.join(RECORD)).unwrap(),
                name => fs::remove_file(f.root.join(DIRECTORY).join(name)).unwrap(),
            }
            assert!(
                resume_custody(&f.root).is_err(),
                "{missing}"
            );
            assert!(begin(&f.root, &f.manifest()).is_err());
        }
    }
    #[test]
    fn completed_provenance_allows_anchor_advance_and_explicit_verifier_upgrade() {
        let f = Fixture::new();
        f.candidate();
        resume_custody(&f.root).unwrap();
        let custody = f.root.join(DIRECTORY);
        let initial = read_json(&f.root.join(RECORD)).unwrap();
        let settings = Settings::load(&custody).unwrap();
        let advanced = Point::parse(&json!({"height":"5","worldRoot":"85"}))
            .unwrap()
            .with_witness(&json!({"chain":"14","siblings":["3"]}))
            .unwrap();
        persist(&custody, &settings, &advanced).unwrap();
        let replacement = f.base.join("upgraded-verifier");
        fs::copy(&settings.verifier, &replacement).unwrap();
        replace_verifier(&f.root, &f.manifest(), &replacement).unwrap();
        fs::remove_file(&settings.verifier).unwrap();
        fs::remove_file(f.root.join("refs/account.json")).unwrap();
        let result = complete_with(
            &f.root,
            &f.manifest(),
            |_| panic!("completed enrollment cannot require the original grant"),
            |_| Ok(()),
        )
        .unwrap();
        assert_eq!(result["point"], advanced.json());
        assert_eq!(read_json(&f.root.join(RECORD)).unwrap(), initial);
        assert_eq!(
            anchor(&custody, &Settings::load(&custody).unwrap()).unwrap(),
            advanced
        );
    }
    #[test]
    fn legacy_workspace_cannot_be_reclassified_as_fresh() {
        let f = Fixture::new();
        let mut manifest = f.manifest();
        manifest.as_object_mut().unwrap().remove("freshContinuity");
        save(&f.root, "workspace.json", &manifest).unwrap();
        fs::remove_file(f.root.join(RECORD)).unwrap();
        assert!(resume_custody(&f.root).is_err());
        let record =
            json!({"name":"account","kind":"account","target":"20","observeCapability":"30"});
        assert!(prepare(
            &f.root,
            &mut manifest,
            FreshBaseline::Reference(&record),
            None
        )
        .is_err());
        assert!(begin(&f.root, &manifest).unwrap().is_none());
    }
    #[test]
    fn fresh_process_crash_child() {
        let Ok(root) = std::env::var("MINI_FRESH_CRASH_ROOT") else {
            return;
        };
        let stop = std::env::var("MINI_FRESH_CRASH_STAGE").unwrap();
        let root = Path::new(&root);
        let manifest = read_json(&root.join("workspace.json")).unwrap();
        complete_with(
            root,
            &manifest,
            |_| panic!("candidate recovery cannot read"),
            |stage| {
                if format!("{stage:?}") == stop {
                    std::process::exit(73)
                }
                Ok(())
            },
        )
        .unwrap();
        panic!("failpoint did not execute");
    }
    #[test]
    fn fresh_process_crashes_resume_durable_phases() {
        for stop in [
            Stage::Directory,
            Stage::Anchor,
            Stage::Enabled,
            Stage::Manifest,
            Stage::Complete,
        ] {
            let f = Fixture::new();
            f.candidate();
            let status = Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "receipt_continuity::fresh::tests::fresh_process_crash_child",
                ])
                .env("MINI_FRESH_CRASH_ROOT", &f.root)
                .env("MINI_FRESH_CRASH_STAGE", format!("{stop:?}"))
                .output()
                .unwrap()
                .status;
            assert_eq!(status.code(), Some(73));
            if stop != Stage::Complete {
                resume_custody(&f.root).unwrap();
            }
            assert!(begin(&f.root, &f.manifest()).unwrap().is_some());
            assert_eq!(
                read_json(&f.root.join(DIRECTORY).join("anchor.json")).unwrap()["point"]["height"],
                "2"
            );
        }
    }
}
