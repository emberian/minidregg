//! Actual native audience phase authoring. The source controller validates
//! transition semantics and exact current snapshots; this client generates and
//! durably stages cryptographic material before signed submission.
use crate::{
    object_keys::{AdmittedAnchor, Store},
    object_messages::Context,
    object_epoch_packages::{self, Recipient},
    Result,
};
use serde_json::{json, Value};
use std::{ffi::OsStr, fs, path::Path};
fn text<'a>(v: &'a Value, n: &str) -> Result<&'a str> {
    v[n].as_str().ok_or_else(|| format!("missing {n}"))
}
fn natural(v: &Value, n: &str) -> Result<String> {
    let s = text(v, n)?;
    if !mini_sdk::decimal::is_canonical(s)
    {
        return Err(format!("noncanonical {n}"));
    }
    Ok(s.into())
}
fn next(s: &str) -> Result<String> {
    mini_sdk::decimal::successor(s).map_err(|_| "invalid decimal counter".to_owned())
}
fn fixed(v: &Value, n: &str) -> Result<[u8; 32]> {
    mini_sdk::decimal::to_be_bytes32(&natural(v, n)?).map_err(|_| format!("{n} exceeds 256 bits"))
}
fn hex32(v: &Value, n: &str) -> Result<[u8; 32]> {
    crate::decode_hex(text(v, n)?)?
        .try_into()
        .map_err(|_| format!("{n} must be 32 bytes"))
}
use mini_sdk::decimal::from_be_bytes as decimal;
fn inspect_policy(host: &Path, config: &Path, source: &Value, dir: &Path) -> Result<Value> {
    let input = dir.join("planned-policy.json");
    let binary = dir.join("planned-policy.bin");
    let output = dir.join("planned-policy-inspected.json");
    crate::write_json_new(&input, source)?;
    crate::author(host, config, OsStr::new("policy"), &input, &binary)?;
    crate::inspect(host, config, "view-policy", &binary, &output)
}
fn publish_same(path:&Path,bytes:&[u8])->Result<()> {
    crate::fsio::retain_exact(path,bytes,||format!("{} differs from staged phase",path.display())).map(|_|())
}
fn random_label()->Result<String> {
    use ring::rand::{SecureRandom,SystemRandom};
    let mut random=[0;16];SystemRandom::new().fill(&mut random).map_err(|_|"randomness unavailable")?;
    Ok(crate::hex(&random))
}
/// Files are projections of encrypted custody. No author call or outward
/// publication happens until the exact operation, package key and intent exist
/// in the journal. Repeated restoration never asks for fresh package material.
fn materialize_phase(store:&mut Store,operation:&[u8;32],dir:&Path,
    mut author:impl FnMut(&Path,&Path)->Result<()>)->Result<()> {
    let (manifest,mut command,intent)=store.phase_artifacts(operation)?;
    if let Some(intent)=intent {
        let source=dir.join("phase-intent.json");publish_same(&source,&intent)?;
        if command.is_empty() {
            let temporary=dir.join(format!(".authored-phase-{}",random_label()?));
            author(&source,&temporary)?;
            command=fs::read(&temporary).map_err(|e|e.to_string())?;
            store.bind_epoch_command(operation,&command)?;
            fs::remove_file(temporary).map_err(|e|e.to_string())?;
        }
    }
    if command.is_empty() {return Err("staged phase has neither command nor recoverable intent".into());}
    publish_same(&dir.join("phase-intent.bin"),&command)?;
    if !manifest.is_empty() {publish_same(&dir.join("epoch-manifest.bin"),&manifest)?;}
    Ok(())
}
fn phase_transport(dir:&Path)->Result<(std::path::PathBuf,std::path::PathBuf)> {
    let (host,config,socket)=crate::manifest_paths(dir)?;
    match (crate::SOCKET.get(),socket) {
        (Some(current),Some(retained)) if crate::transport::pinned_address(current)?==crate::transport::pinned_address(&retained)?=>{},
        (None,Some(retained))=>{crate::SOCKET.set(retained).map_err(|_|"phase socket was concurrently pinned")?;},
        (None,None)=>{},
        _=>return Err("phase recovery transport differs from retained socket pin".into()),
    }
    Ok((host,config))
}
/// Return false only when this journal has never retained the operation. Known
/// phases reconstruct their exact artifacts, including accepted historical ones.
pub(crate) fn restore_phase(dir:&Path,state:&Path,storage:&Path,operation:&str)->Result<bool> {
    let op:[u8;32]=crate::decode_hex(operation)?.try_into().map_err(|_|"operation must be 32 bytes")?;
    let mut store=Store::open(state,crate::read_secret(storage)?.to_bytes())?;
    if !store.operation_known(&op)? {return Ok(false);}
    let (host,config)=phase_transport(dir)?;
    materialize_phase(&mut store,&op,dir,|source,output|
        crate::author(&host,&config,OsStr::new("intent"),source,output))?;
    Ok(true)
}

/// Request fields: phase=enroll|freeze|resume, control (canonical Nat),
/// operation (32-byte hex, used losslessly as source phase nonce), grants (ordinary observation grants). Enroll/freeze
/// additionally require transition (Nat). Enroll/resume require audience/devices/
/// history (Nat), dealerGeneration (hex), canonical rosterBytes hex, catalogIntent path, and complete ordered recipients[{subject,capability,deviceSource,generation,keyCommitment,kemPublic,dhPublic}].
/// The current record/predicate/descriptors and current snapshot roots ALWAYS
/// come from the authenticated local native audience observation `view`.
pub(crate) fn run(
    view: &Value,
    request: &Path,
    host: &Path,
    config: &Path,
    writer: &Path,
    state: &Path,
    storage: &Path,
    dir: &Path,
) -> Result<()> {
    let r: Value = serde_json::from_slice(&fs::read(request).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let phase = text(&r, "phase")?;
    if !matches!(phase, "enroll" | "freeze" | "resume") {
        return Err("invalid audience phase".into());
    }
    let operation = hex32(&r, "operation")?;
    let phase_nonce = decimal(&operation);
    if r.get("nonce").is_some() && natural(&r, "nonce")? != phase_nonce {
        return Err("phase nonce must equal lossless operation label".into());
    }
    let phase_dir=dir;
    if phase_dir.exists() {crate::workspace::private_dir(phase_dir)?;} else {crate::workspace::make_private_dir(phase_dir)?;}
    let retained_config=phase_dir.join("config.json");
    publish_same(&retained_config,&fs::read(config).map_err(|e|e.to_string())?)?;
    publish_same(&phase_dir.join("phase-request.json"),&serde_json::to_vec_pretty(&r).map_err(|e|e.to_string())?)?;
    let preparation=phase_dir.join(format!("prepare-{}",random_label()?));
    crate::workspace::make_private_dir(&preparation)?;
    if !phase_dir.join("attempt.json").exists() {
        crate::write_manifest(&preparation,host,&retained_config,"object-epoch")?;
        publish_same(&phase_dir.join("attempt.json"),&fs::read(preparation.join("attempt.json")).map_err(|e|e.to_string())?)?;
    }
    let mut store=Store::open(state,crate::read_secret(storage)?.to_bytes())?;
    if store.operation_known(&operation)? {
        drop(store);
        return retry(phase_dir,state,storage,text(&r,"operation")?,Some(writer));
    }
    if phase_dir.join("phase-intent.json").exists() || phase_dir.join("phase-intent.bin").exists()
        || phase_dir.join("submission/call.bin").exists() {
        return Err("phase artifacts exist without their durable operation; restore custody, refusing replacement keys".into());
    }
    // Pre-key preparation can restart in a fresh scratch directory. It retains
    // the same request/operation; no final phase intent or key has existed yet.
    let dir=preparation.as_path();
    let config=retained_config.as_path();
    let mut source = view["sourceRecord"].clone();
    if !source.is_object() {
        return Err("native audience observation lacks canonical sourceRecord".into());
    }
    for field in ["localSelector", "parents", "descendants", "audience", "objectDescriptor"] {
        if source.get(field).is_none() {
            return Err(format!("combined v6 source readback lacks {field}; audience authoring needs the matching profile"));
        }
    }
    source["version"] = json!(next(&natural(view, "policyRevision")?)?);
    source["previous"] = view["policyAddress"].clone();
    // Upgrade only the authenticated extension representation; preserve descriptor.
    let descriptor = source["objectDescriptor"].clone();
    let old = source["audience"].clone();
    let mut audience = match phase {
        "enroll" => {
            if !old.is_null() {
                return Err("already enrolled; use freeze/resume".into());
            }
            json!({"object":natural(view,"object")?,"epoch":"0","parent":"0","transition":natural(&r,"transition")?,"audience":natural(&r,"audience")?,"devices":natural(&r,"devices")?,"history":natural(&r,"history")?,"manifest":"0","mode":"active","authoritySnapshot":natural(view,"currentAuthorityRoot")?,"deviceSnapshot":"0"})
        }
        "freeze" => {
            if old["mode"] != json!("active") {
                return Err("freeze requires current active audience".into());
            }
            let mut a = old.clone();
            a["parent"] = old["transition"].clone();
            a["transition"] = json!(natural(&r, "transition")?);
            a["mode"] = json!("frozen");
            a
        }
        _ => {
            if old["mode"] != json!("frozen") {
                return Err("resume requires current frozen audience".into());
            }
            let mut a = old.clone();
            a["epoch"] = json!(next(&natural(&old, "epoch")?)?);
            a["audience"] = json!(natural(&r, "audience")?);
            a["devices"] = json!(natural(&r, "devices")?);
            a["history"] = json!(natural(&r, "history")?);
            a["manifest"] = json!("0");
            a["mode"] = json!("active");
            a["authoritySnapshot"] = json!(natural(view, "currentAuthorityRoot")?);
            a["deviceSnapshot"] = json!("0");
            a
        }
    };
    // Native codecs and source-owned checker authenticate the complete ordered
    // roster against a separately authorized actual catalog observation.
    let mut checked_roster = None;
    let mut roster_bytes = Vec::new();
    if phase != "freeze" {
        roster_bytes = crate::decode_hex(text(&r, "rosterBytes")?)?;
        let roster_bin = dir.join("audience-roster.bin");
        crate::write_new(&roster_bin, &roster_bytes)?;
        let roster_view_path = dir.join("audience-roster.json");
        crate::host_files(
            host,
            config,
            &[
                Path::new("object-roster-inspect"),
                &roster_bin,
                &roster_view_path,
            ],
        )?;
        let rv: Value =
            serde_json::from_slice(&fs::read(&roster_view_path).map_err(|e| e.to_string())?)
                .map_err(|e| e.to_string())?;
        audience["audience"] = rv["audience"].clone();
        audience["devices"] = rv["devices"].clone();
        let catalog_dir = dir.join("catalog-observation");
        crate::create_dir(&catalog_dir)?;
        let catalog_intent = Path::new(text(&r, "catalogIntent")?);
        let catalog = crate::authorize_observation(
            host,
            config,
            catalog_intent,
            OsStr::new("intent"),
            &crate::read_secret(writer)?,
            &catalog_dir,
        )?;
        let planned_state = dir.join("planned-audience.json");
        crate::write_json_new(&planned_state, &audience)?;
        let checked_path = dir.join("checked-roster.json");
        let source_observation = phase_dir
            .parent()
            .ok_or("missing source observation directory")?
            .join("signed-observation.bin");
        crate::host_files(
            host,
            config,
            &[
                Path::new("object-audience-roster"),
                &source_observation,
                &catalog.signed,
                &planned_state,
                &roster_bin,
                &checked_path,
            ],
        )?;
        let checked: Value =
            serde_json::from_slice(&fs::read(&checked_path).map_err(|e| e.to_string())?)
                .map_err(|e| e.to_string())?;
        if checked["type"] != json!("minidregg-checked-object-roster-v1")
            || checked["rosterBytes"] != json!(crate::hex(&roster_bytes))
        {
            return Err("native roster checker returned inconsistent canonical preimage".into());
        }
        audience = checked["audienceState"].clone();
        if !audience.is_object() {
            return Err("native roster checker lacks planned audience state".into());
        }
        checked_roster = Some(checked["roster"].clone());
    }
    // Preserve every composed-law field from the fresh authenticated source.
    // Direct v6 JSON fields are not either independent v5 extension envelope.
    source["audience"] = audience.clone();
    source["objectDescriptor"] = descriptor;
    if !old.is_null() {
        store.reconcile_anchor(&AdmittedAnchor {
            object: fixed(&old, "object")?,
            epoch: text(&old, "epoch")?
                .parse()
                .map_err(|_| "client epoch exceeds u64")?,
            transition: fixed(&old, "transition")?,
            active: old["mode"] == json!("active"),
        })?;
    }
    let prepared = if phase != "freeze" {
        let policy = inspect_policy(host, config, &source, dir)?;
        let ctx = Context {
            object: fixed(&audience, "object")?,
            epoch: text(&audience, "epoch")?
                .parse()
                .map_err(|_| "client epoch exceeds u64")?,
            transition: fixed(&audience, "transition")?,
            operation,
            law: fixed(&policy, "semanticLawDigest")?,
        };
        let rows = r["recipients"]
            .as_array()
            .ok_or("missing recipient devices")?;
        let mut recipients = Vec::new();
        let entries = checked_roster
            .as_ref()
            .ok_or("missing authenticated roster")?["entries"]
            .as_array()
            .ok_or("missing authenticated roster entries")?;
        if entries.len() != rows.len() {
            return Err("package list must equal complete authenticated roster".into());
        }
        for (row, entry) in rows.iter().zip(entries) {
            for name in ["subject", "capability", "deviceSource", "keyCommitment"] {
                if natural(row, name)? != natural(entry, name)? {
                    return Err(format!("package {name} differs from complete roster"));
                }
            }
            if decimal(&hex32(row, "generation")?) != natural(entry, "deviceGeneration")? {
                return Err("package generation differs from complete roster".into());
            }
            recipients.push(Recipient {
                subject: natural(row, "subject")?,
                capability: natural(row, "capability")?,
                device_source: natural(row, "deviceSource")?,
                generation: hex32(row, "generation")?,
                key_commitment: fixed(row, "keyCommitment")?,
                public: crate::object_keys_hybrid::public_from_record(row)?,
            });
        }
        let dealer_generation = hex32(&r, "dealerGeneration")?;
        let (_dealer_secret, dealer_public) = store.load_device(&dealer_generation)?;
        let dealer_subject = natural(view, "subject")?;
        let dealer = recipients
            .iter()
            .find(|entry| entry.subject == dealer_subject && entry.generation == dealer_generation)
            .ok_or("retaining dealer must be included in the entitled device roster")?;
        if dealer.public != dealer_public {
            return Err("dealer recipient keys differ from retained local device".into());
        }
        let p = object_epoch_packages::prepare(
            &ctx,
            &fixed(&audience, "audience")?,
            &fixed(&audience, "devices")?,
            &fixed(&audience, "history")?,
            &fixed(&audience, "authoritySnapshot")?,
            &fixed(&audience, "deviceSnapshot")?,
            &recipients,
            &roster_bytes,
            &dealer_subject,
            &dealer_generation,
            &crate::read_secret(writer)?,
        )?;
        audience["manifest"] = json!(decimal(&p.commitment));
        source["audience"] = audience.clone();
        Some(p)
    } else {
        None
    };
    let mut intent = json!({"subject":natural(view,"subject")?,"nonce":phase_nonce,"purpose":{"type":"prepare","draft":{"type":"install-source","subject":natural(view,"subject")?,"control":natural(&r,"control")?,"declaration":{"expectedPreRoot":natural(view,"currentAuthorityRoot")?,"expected":{"version":natural(view,"policyRevision")?,"address":natural(view,"policyAddress")?},"nonce":phase_nonce,"source":source}}},"grants":r["grants"]});
    if let Some(roster) = &checked_roster {
        intent["purpose"]["draft"]["audienceRoster"] = roster.clone();
    }
    let next=AdmittedAnchor {
        object:fixed(&audience,"object")?,
        epoch:text(&audience,"epoch")?.parse().map_err(|_|"client epoch exceeds u64")?,
        transition:fixed(&audience,"transition")?,active:audience["mode"]==json!("active"),
    };
    let intent_bytes=serde_json::to_vec_pretty(&intent).map_err(|e|e.to_string())?;
    // This is the first durable commitment to generated material. Save the key,
    // whole package and exact source JSON together BEFORE Host authoring or any
    // phase-intent publication. A crash after this line always takes exact retry.
    if let Some(prepared)=&prepared {
        store.stage_epoch_intent(&next,&operation,prepared,&intent_bytes)?;
    } else {
        store.stage_control_intent(&next,&operation,&intent_bytes)?;
    }
    materialize_phase(&mut store,&operation,phase_dir,|source,output|
        crate::author(host,config,OsStr::new("intent"),source,output))?;
    drop(store);
    retry(phase_dir,state,storage,text(&r,"operation")?,Some(writer))
}
/// Reconcile an uncertain exact phase through the retained native call. This
/// never prepares replacement keys, rewrites nonce or refreshes stale snapshots.
pub(crate) fn retry(
    dir: &Path,
    state: &Path,
    storage: &Path,
    operation: &str,
    writer: Option<&Path>,
) -> Result<()> {
    let op: [u8; 32] = crate::decode_hex(operation)?
        .try_into()
        .map_err(|_| "operation must be 32 bytes")?;
    let mut store = Store::open(state, crate::read_secret(storage)?.to_bytes())?;
    let (host,config)=phase_transport(dir)?;
    materialize_phase(&mut store,&op,dir,|source,output|
        crate::author(&host,&config,OsStr::new("intent"),source,output))?;
    store.pending_epoch(&op)?;
    let attempt = store
        .pending_attempt(&op)?
        .unwrap_or_else(|| dir.join("submission"));
    if attempt.join("call.bin").is_file() {
        crate::retry(&attempt, "submit", true)?;
    } else {
        // No call.bin means the existing submit routine could not have emitted:
        // it persists call.bin before Host submission. Re-author observations
        // around the exact encrypted-journal command, never new epoch material.
        let writer=writer.ok_or("staged epoch has no emitted call; retry with --key to resume exact command construction")?;
        let (host,config)=phase_transport(dir)?;
        let next=if !attempt.exists() {attempt} else {
            let recovery=dir.join(format!("recover-{}",random_label()?));
            crate::workspace::make_private_dir(&recovery)?;
            recovery.join("submission")
        };
        let intent=dir.join("phase-intent.bin");
        store.bind_attempt(&op, &next)?;
        crate::submit(
            &host,
            &config,
            &intent,
            OsStr::new("binary"),
            writer,
            &next,
            false,
        )?;
    }
    store.settle(&op, true)
}

/// Provision a real hybrid recipient device. Private keys never leave encrypted
/// Store custody; the returned file contains only public publication material.
pub(crate) fn device(state: &Path, storage: &Path, output: &Path) -> Result<()> {
    let (secret, public) = crate::object_keys_hybrid::generate()?;
    let generation = crate::object_keys_hybrid::key_commitment(&public);
    let mut store = Store::open(state, crate::read_secret(storage)?.to_bytes())?;
    store.retain_device(&generation, &secret, &public)?;
    crate::write_json_new(
        output,
        &json!({"codec":"MINI/OBJECT-DEVICE/v2","generation":crate::hex(&generation),"deviceGeneration":decimal(&generation),"keyCommitment":decimal(&generation),"hybridPublic":crate::hex(&public.to_bytes())}),
    )
}

#[cfg(test)]
mod staging_tests {
    use super::*;
    fn directory()->std::path::PathBuf {
        let root=std::env::temp_dir().join(format!("mini-epoch-publication-{}",random_label().unwrap()));
        crate::workspace::make_private_dir(&root).unwrap();root
    }
    fn intent(operation:&[u8;32])->Vec<u8> {
        serde_json::to_vec_pretty(&json!({"subject":"7","nonce":decimal(operation),
            "purpose":{"type":"prepare","draft":{"type":"install-source","source":"exact source fixture"}}})).unwrap()
    }
    #[test]
    fn generated_material_is_durable_before_phase_publication_and_survives_author_crash() {
        let root=directory();let state=root.join("keys.json");let operation=[4;32];
        let anchor=AdmittedAnchor {object:[1;32],epoch:2,transition:[3;32],active:true};
        let prepared=object_epoch_packages::PreparedEpoch {key:zeroize::Zeroizing::new([8;32]),
            manifest:b"exact complete prepared package".to_vec(),commitment:[9;32]};
        let source=intent(&operation);
        let mut store=Store::open(&state,[7;32]).unwrap();
        store.stage_epoch_intent(&anchor,&operation,&prepared,&source).unwrap();
        drop(store);
        assert!(!root.join("phase-intent.json").exists());
        assert!(!root.join("epoch-manifest.bin").exists());
        // First recovery starts with only the atomic encrypted journal.
        let mut store=Store::open(&state,[7;32]).unwrap();
        assert!(store.operation_known(&operation).unwrap());
        let (manifest,command,json)=store.phase_artifacts(&operation).unwrap();
        assert_eq!(manifest,prepared.manifest);assert!(command.is_empty());assert_eq!(json,Some(source.clone()));
        assert!(store.stage_epoch_intent(&anchor,&operation,&prepared,&source).is_err());
        let failed=materialize_phase(&mut store,&operation,&root,|input,output| {
            assert_eq!(fs::read(input).unwrap(),source);
            fs::write(output,b"interrupted Host output").unwrap();
            Err("simulated author crash before canonical reply".into())
        });
        assert!(failed.is_err());
        assert!(!root.join("phase-intent.bin").exists());
        assert!(!root.join("epoch-manifest.bin").exists());
        drop(store);
        let mut store=Store::open(&state,[7;32]).unwrap();
        let exact=b"canonical Host-authored binary fixture";
        materialize_phase(&mut store,&operation,&root,|input,output| {
            assert_eq!(fs::read(input).unwrap(),source);
            fs::write(output,exact).map_err(|e|e.to_string())
        }).unwrap();
        assert_eq!(fs::read(root.join("phase-intent.bin")).unwrap(),exact);
        assert_eq!(fs::read(root.join("epoch-manifest.bin")).unwrap(),prepared.manifest);
        assert!(store.bind_epoch_command(&operation,b"replacement command").is_err());
        drop(store);
        let mut store=Store::open(&state,[7;32]).unwrap();
        materialize_phase(&mut store,&operation,&root,|_,_|panic!("retained binary must not be re-authored")).unwrap();
        store.settle(&operation,true).unwrap();drop(store);
        let mut store=Store::open(&state,[7;32]).unwrap();
        assert_eq!(*store.historical_key(&anchor).unwrap(),*prepared.key);
        materialize_phase(&mut store,&operation,&root,|_,_|panic!("accepted phase must not regenerate")).unwrap();
        assert!(store.stage_epoch_intent(&anchor,&operation,&prepared,&source).is_err());
        drop(store);fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn freeze_intent_reopens_exactly_and_terminal_rejection_allows_only_new_operation() {
        let root=directory();let state=root.join("keys.json");let operation=[4;32];
        let anchor=AdmittedAnchor {object:[1;32],epoch:2,transition:[3;32],active:false};
        let source=intent(&operation);
        let mut store=Store::open(&state,[7;32]).unwrap();
        store.stage_control_intent(&anchor,&operation,&source).unwrap();drop(store);
        let mut store=Store::open(&state,[7;32]).unwrap();
        materialize_phase(&mut store,&operation,&root,|input,output| {
            assert_eq!(fs::read(input).unwrap(),source);
            fs::write(output,b"exact freeze binary").map_err(|e|e.to_string())
        }).unwrap();
        assert!(!root.join("epoch-manifest.bin").exists());
        assert_eq!(fs::read(root.join("phase-intent.json")).unwrap(),source);
        // Only a caller holding a confirmed terminal source refusal may settle
        // false; custody preserves that operation while allowing its successor.
        store.settle(&operation,false).unwrap();
        assert!(store.stage_control_intent(&anchor,&operation,&source).is_err());
        let successor=[5;32];store.stage_control_intent(&anchor,&successor,&intent(&successor)).unwrap();
        assert_eq!(store.phase_artifacts(&operation).unwrap().1,b"exact freeze binary");
        assert!(store.pending_epoch(&operation).is_err());
        drop(store);fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn restoration_uses_bound_command_after_crash_before_outward_files() {
        let root=directory();let state=root.join("keys.json");let operation=[4;32];
        let anchor=AdmittedAnchor {object:[1;32],epoch:2,transition:[3;32],active:true};
        let prepared=object_epoch_packages::PreparedEpoch {key:zeroize::Zeroizing::new([8;32]),
            manifest:b"retained package".to_vec(),commitment:[9;32]};
        let source=intent(&operation);
        let mut store=Store::open(&state,[7;32]).unwrap();
        store.stage_epoch_intent(&anchor,&operation,&prepared,&source).unwrap();
        store.bind_epoch_command(&operation,b"bound binary").unwrap();drop(store);
        // No final phase artifacts survived, but command binding did.
        let mut store=Store::open(&state,[7;32]).unwrap();
        materialize_phase(&mut store,&operation,&root,|_,_|panic!("binary already durable")).unwrap();
        assert_eq!(fs::read(root.join("phase-intent.json")).unwrap(),source);
        assert_eq!(fs::read(root.join("phase-intent.bin")).unwrap(),b"bound binary");
        assert_eq!(fs::read(root.join("epoch-manifest.bin")).unwrap(),prepared.manifest);
        fs::write(root.join("phase-intent.json"),b"different meaning").unwrap();
        assert!(materialize_phase(&mut store,&operation,&root,|_,_|panic!("must refuse differing artifact")).is_err());
        assert_eq!(store.phase_artifacts(&operation).unwrap().2,Some(source));
        drop(store);fs::remove_dir_all(root).unwrap();
    }
}
