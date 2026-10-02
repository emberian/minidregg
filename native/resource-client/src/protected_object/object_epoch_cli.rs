//! Actual native audience phase authoring. The source controller validates
//! transition semantics and exact current snapshots; this client generates and
//! durably stages cryptographic material before signed submission.
use crate::{
    object_keys::{AdmittedAnchor, Store},
    object_keys_hybrid::DevicePublic,
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
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) || (s.len() > 1 && s.starts_with('0'))
    {
        return Err(format!("noncanonical {n}"));
    }
    Ok(s.into())
}
fn next(s: &str) -> Result<String> {
    let mut b = s.as_bytes().to_vec();
    if b.is_empty() || !b.iter().all(u8::is_ascii_digit) {
        return Err("invalid decimal counter".into());
    }
    for i in (0..b.len()).rev() {
        if b[i] != b'9' {
            b[i] += 1;
            return String::from_utf8(b).map_err(|e| e.to_string());
        }
        b[i] = b'0';
    }
    b.insert(0, b'1');
    String::from_utf8(b).map_err(|e| e.to_string())
}
fn fixed(v: &Value, n: &str) -> Result<[u8; 32]> {
    let s = natural(v, n)?;
    let mut b = [0u8; 32];
    for d in s.bytes() {
        let mut c = (d - b'0') as u16;
        for x in b.iter_mut().rev() {
            c += (*x as u16) * 10;
            *x = c as u8;
            c >>= 8;
        }
        if c != 0 {
            return Err(format!("{n} exceeds 256 bits"));
        }
    }
    Ok(b)
}
fn hex32(v: &Value, n: &str) -> Result<[u8; 32]> {
    crate::decode_hex(text(v, n)?)?
        .try_into()
        .map_err(|_| format!("{n} must be 32 bytes"))
}
fn decimal(bytes: &[u8; 32]) -> String {
    let mut d = vec![0u8];
    for b in bytes {
        let mut carry = *b as u16;
        for x in &mut d {
            carry += (*x as u16) * 256;
            *x = (carry % 10) as u8;
            carry /= 10;
        }
        while carry > 0 {
            d.push((carry % 10) as u8);
            carry /= 10;
        }
    }
    d.iter().rev().map(|x| (b'0' + x) as char).collect()
}
fn inspect_policy(host: &Path, config: &Path, source: &Value, dir: &Path) -> Result<Value> {
    let input = dir.join("planned-policy.json");
    let binary = dir.join("planned-policy.bin");
    let output = dir.join("planned-policy-inspected.json");
    crate::write_json_new(&input, source)?;
    crate::author(host, config, OsStr::new("policy"), &input, &binary)?;
    crate::inspect(host, config, "view-policy", &binary, &output)
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
    crate::create_dir(dir)?;
    let retained_config = dir.join("config.json");
    crate::copy_new(config, &retained_config)?;
    crate::write_manifest(dir, host, &retained_config, "object-epoch")?;
    let config = retained_config.as_path();
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
        let source_observation = dir
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
    let mut store = Store::open(state, crate::read_secret(storage)?.to_bytes())?;
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
                public: DevicePublic {
                    kem: crate::decode_hex(text(row, "kemPublic")?)?,
                    dh: hex32(row, "dhPublic")?,
                },
            });
        }
        let dealer_generation = hex32(&r, "dealerGeneration")?;
        let (_dealer_secret, dealer_public) = store.load_device(&dealer_generation)?;
        let dealer_subject = natural(view, "subject")?;
        let dealer = recipients
            .iter()
            .find(|entry| entry.subject == dealer_subject && entry.generation == dealer_generation)
            .ok_or("retaining dealer must be included in the entitled device roster")?;
        if dealer.public.kem != dealer_public.kem || dealer.public.dh != dealer_public.dh {
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
    let intent_json = dir.join("phase-intent.json");
    let intent_bin = dir.join("phase-intent.bin");
    crate::write_json_new(&intent_json, &intent)?;
    crate::author(
        host,
        config,
        OsStr::new("intent"),
        &intent_json,
        &intent_bin,
    )?;
    if let Some(p) = &prepared {
        let a = AdmittedAnchor {
            object: fixed(&audience, "object")?,
            epoch: text(&audience, "epoch")?
                .parse()
                .map_err(|_| "client epoch exceeds u64")?,
            transition: fixed(&audience, "transition")?,
            active: true,
        };
        store.stage_epoch(
            &a,
            &operation,
            p,
            &fs::read(&intent_bin).map_err(|e| e.to_string())?,
        )?;
        crate::write_new(&dir.join("epoch-manifest.bin"), &p.manifest)?;
    }
    if prepared.is_none() {
        store.stage_control(
            &AdmittedAnchor {
                object: fixed(&audience, "object")?,
                epoch: text(&audience, "epoch")?
                    .parse()
                    .map_err(|_| "client epoch exceeds u64")?,
                transition: fixed(&audience, "transition")?,
                active: false,
            },
            &operation,
            &fs::read(&intent_bin).map_err(|e| e.to_string())?,
        )?;
    }
    // Ordinary native path retains a signed exact call before submission. Lost
    // replies must use that call's retry, never regenerate an epoch proposal.
    let call_dir = dir.join("submission");
    store.bind_attempt(&operation, &call_dir)?;
    crate::submit(
        host,
        config,
        &intent_bin,
        OsStr::new("binary"),
        writer,
        &call_dir,
        false,
    )?;
    // submit only returns success for the source's confirmed native outcome.
    // The exact phase operation was fixed in the retained source declaration.
    store.reconcile_anchor(&AdmittedAnchor {
        object: fixed(&audience, "object")?,
        epoch: text(&audience, "epoch")?
            .parse()
            .map_err(|_| "client epoch exceeds u64")?,
        transition: fixed(&audience, "transition")?,
        active: audience["mode"] == json!("active"),
    })?;
    store.settle(&operation, true)?;
    Ok(())
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
    use ring::rand::{SecureRandom, SystemRandom};
    let op: [u8; 32] = crate::decode_hex(operation)?
        .try_into()
        .map_err(|_| "operation must be 32 bytes")?;
    let mut store = Store::open(state, crate::read_secret(storage)?.to_bytes())?;
    let (manifest, command) = store.pending_epoch(&op)?;
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
        let (host, config, socket) = crate::manifest_paths(dir)?;
        if socket.is_some() {
            return Err("object epoch recovery requires pinned local Host".into());
        }
        let mut random = [0; 16];
        SystemRandom::new()
            .fill(&mut random)
            .map_err(|_| "randomness unavailable")?;
        let recovery = dir.join(format!("recover-{}", crate::hex(&random)));
        crate::create_dir(&recovery)?;
        let intent = recovery.join("phase-intent.bin");
        crate::write_new(&intent, &command)?;
        if !manifest.is_empty() {
            crate::write_new(&recovery.join("epoch-manifest.bin"), &manifest)?;
        }
        let next = recovery.join("submission");
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
    let generation = crate::object_keys_hybrid::key_commitment(&public)?;
    let mut store = Store::open(state, crate::read_secret(storage)?.to_bytes())?;
    store.retain_device(&generation, &secret, &public)?;
    crate::write_json_new(
        output,
        &json!({"codec":"MINI/OBJECT-DEVICE/v1","generation":crate::hex(&generation),"deviceGeneration":decimal(&generation),"keyCommitment":decimal(&generation),"kemPublic":crate::hex(&public.kem),"dhPublic":crate::hex(&public.dh)}),
    )
}
