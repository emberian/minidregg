//! Native private-object path. Source views are obtained by an actual signed
//! resource observation on the pinned local Host, never loaded from a cache.
use crate::{
    object_keys::{AdmittedAnchor, Store},
    object_messages::Context,
    Result,
};
use serde_json::{json, Value};
use std::{ffi::OsStr, fs, path::Path};

/// Lossless source Nat -> fixed SHA256/context bytes, big endian. No felt fold.
fn source_bytes(v: &Value, name: &str) -> Result<[u8; 32]> {
    let text = v[name]
        .as_str()
        .ok_or_else(|| format!("source lacks {name}"))?;
    if text.is_empty()
        || !text.bytes().all(|c| c.is_ascii_digit())
        || (text.len() > 1 && text.starts_with('0'))
    {
        return Err(format!("noncanonical source {name}"));
    }
    let mut out = [0u8; 32];
    for digit in text.bytes() {
        let mut carry = (digit - b'0') as u16;
        for byte in out.iter_mut().rev() {
            carry += (*byte as u16) * 10;
            *byte = carry as u8;
            carry >>= 8;
        }
        if carry != 0 {
            return Err(format!("source {name} exceeds 256 bits"));
        }
    }
    Ok(out)
}
fn bytes(v: &Value, field: &str) -> Result<[u8; 32]> {
    crate::decode_hex(
        v[field]
            .as_str()
            .ok_or_else(|| format!("missing {field}"))?,
    )?
    .try_into()
    .map_err(|_| format!("{field} must be 32 bytes"))
}
pub(crate) fn observe(
    host: &Path,
    config: &Path,
    intent: &Path,
    key: &Path,
    dir: &Path,
) -> Result<Value> {
    crate::create_dir(dir)?;
    let retained_config = dir.join("config.json");
    crate::copy_new(config, &retained_config)?;
    let retained_intent = dir.join("intent.json");
    crate::copy_new(intent, &retained_intent)?;
    crate::write_manifest(dir, host, &retained_config, "object-audience")?;
    let signing = crate::read_secret(key)?;
    let signed = crate::authorize_observation(
        host,
        &retained_config,
        &retained_intent,
        OsStr::new("intent"),
        &signing,
        dir,
    )?;
    let output = dir.join("audience.json");
    crate::host_files(
        host,
        &retained_config,
        &[Path::new("object-audience"), &signed.signed, &output],
    )?;
    let v: Value = serde_json::from_slice(&fs::read(output).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    if v["type"] != json!("minidregg-object-audience-v1") {
        return Err("wrong native object view type".into());
    }
    Ok(v)
}
fn anchor(v: &Value) -> Result<AdmittedAnchor> {
    Ok(AdmittedAnchor {
        object: source_bytes(v, "object")?,
        epoch: v["epoch"]
            .as_str()
            .ok_or("missing source epoch")?
            .parse()
            .map_err(|_| "source epoch exceeds client u64")?,
        transition: source_bytes(v, "transition")?,
        active: v["active"].as_bool().ok_or("missing source mode")?,
    })
}
fn context(v: &Value, operation: [u8; 32]) -> Result<Context> {
    let a = anchor(v)?;
    Ok(Context {
        object: a.object,
        epoch: a.epoch,
        transition: a.transition,
        operation,
        law: source_bytes(v, "policyAddress")?,
    })
}
/// Verify the source-committed complete manifest, unwrap this device's package,
/// then retain the key under its source-owned epoch identity.
pub(crate) fn receive_epoch(v: &Value, request: &Path, state: &Path, storage: &Path) -> Result<()> {
    let r: Value = serde_json::from_slice(&fs::read(request).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let storage_key = crate::read_secret(storage)?.to_bytes();
    let mut store = Store::open(state, storage_key)?;
    let generation = bytes(&r, "generation")?;
    let (secret, public) = if r.get("kemSecret").is_some() {
        (
            crate::object_keys_hybrid::DeviceSecret {
                kem: zeroize::Zeroizing::new(crate::decode_hex(
                    r["kemSecret"].as_str().ok_or("missing kemSecret")?,
                )?),
                dh: zeroize::Zeroizing::new(bytes(&r, "dhSecret")?),
            },
            crate::object_keys_hybrid::DevicePublic {
                kem: crate::decode_hex(r["kemPublic"].as_str().ok_or("missing kemPublic")?)?,
                dh: bytes(&r, "dhPublic")?,
            },
        )
    } else {
        let pair = store.load_device(&generation)?;
        if let Some(pk) = r.get("kemPublic") {
            if crate::decode_hex(pk.as_str().ok_or("invalid kemPublic")?)? != pair.1.kem {
                return Err("package public key differs from retained device".into());
            }
        }
        if r.get("dhPublic").is_some() && bytes(&r, "dhPublic")? != pair.1.dh {
            return Err("package DH key differs from retained device".into());
        }
        pair
    };
    let manifest = crate::decode_hex(r["manifest"].as_str().ok_or("missing manifest")?)?;
    let mut epoch_view = v.clone();
    if v["active"] == json!(false) && !v["audienceState"].is_null() {
        epoch_view["transition"] = v["audienceState"]["parent"].clone();
    }
    let a = anchor(&epoch_view)?;
    let ctx = context(&epoch_view, bytes(&r, "operation")?)?;
    // The fresh source observation authenticates the retained manifest commitment.
    // receive() recovers the original package law from that signed manifest while
    // checking its epoch identity; later source law revisions need not match it.
    let epoch_key = crate::object_epoch_packages::receive(
        &ctx,
        &source_bytes(v, "audience")?,
        &source_bytes(v, "devices")?,
        &source_bytes(v, "history")?,
        &source_bytes(v, "authoritySnapshot")?,
        &source_bytes(v, "deviceSnapshot")?,
        &source_bytes(v, "manifest")?,
        &bytes(&r, "writer")?,
        v["subject"].as_str().ok_or("missing source subject")?,
        &bytes(&r, "generation")?,
        &secret,
        &public,
        &manifest,
    )?;
    store.reconcile_anchor(&anchor(v)?)?;
    store.retain(&a, &epoch_key)
}
/// Prepare persists the exact ciphertext before it is returned. Every retry
/// reauthorizes current source and the store refuses changed operation meaning.
pub(crate) fn prepare(
    v: &Value,
    operation: &str,
    plaintext: &Path,
    writer: &Path,
    state: &Path,
    storage: &Path,
    output: &Path,
) -> Result<()> {
    let operation: [u8; 32] = crate::decode_hex(operation)?
        .try_into()
        .map_err(|_| "operation must be 32 bytes")?;
    let signing = crate::read_secret(writer)?;
    let a = anchor(v)?;
    let ctx = context(v, operation)?;
    let mut store = Store::open(state, crate::read_secret(storage)?.to_bytes())?;
    let wire = store.prepare(
        &a,
        &ctx,
        &signing,
        &fs::read(plaintext).map_err(|e| e.to_string())?,
    )?;
    crate::write_new(output, &wire)
}

/// Complete checked invocation through the ordinary signed Mini transaction
/// path, retaining the exact call/outcome for `mini retry` after restart.
pub(crate) fn invoke(
    v: &Value,
    request: &Path,
    operation: &str,
    host: &Path,
    config: &Path,
    key: &Path,
    dir: &Path,
) -> Result<()> {
    if v["active"] != json!(true) {
        return Err("protected object is frozen".into());
    }
    let mut intent: Value = serde_json::from_slice(&fs::read(request).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    if intent["purpose"]["type"] != json!("prepare")
        || intent["purpose"]["draft"]["type"] != json!("invoke")
        || intent["subject"] != v["subject"]
    {
        return Err(
            "object invocation must be this observed subject's prepare/invoke intent".into(),
        );
    }
    let command = &mut intent["purpose"]["draft"]["command"];
    if command["subject"] != v["subject"]
        || command.get("run").is_none()
        || command.get("meaning").is_none_or(Value::is_null)
    {
        return Err(
            "protected invocation requires exact checked run and immutable method meaning".into(),
        );
    }
    let operation: [u8; 32] = crate::decode_hex(operation)?
        .try_into()
        .map_err(|_| "operation must be 32 bytes")?;
    if source_bytes(command, "nonce")? != operation {
        return Err("source invocation nonce must equal encrypted operation label".into());
    }
    let targets = command["targets"]
        .as_array_mut()
        .ok_or("missing invocation targets")?;
    let mut bound = false;
    for target in targets {
        if target["target"] == v["object"] {
            if let Some(old) = target.get("audienceEpoch") {
                if !old.is_null() && old != &v["epoch"] {
                    return Err("draft is bound to a stale audience epoch".into());
                }
            }
            target["audienceEpoch"] = v["epoch"].clone();
            bound = true;
        }
    }
    if !bound {
        return Err("invocation does not target the observed protected object".into());
    }
    let source = dir.join("bound-invocation.json");
    crate::write_json_new(&source, &intent)?;
    crate::submit(
        host,
        config,
        &source,
        OsStr::new("intent"),
        key,
        &dir.join("invocation"),
        false,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn source_digest_mapping_is_lossless_and_bounded() {
        let mut value = json!({"x":"255"});
        let mut expected = [0; 32];
        expected[31] = 255;
        assert_eq!(source_bytes(&value, "x").unwrap(), expected);
        value["x"] = json!("256");
        expected[30] = 1;
        expected[31] = 0;
        assert_eq!(source_bytes(&value, "x").unwrap(), expected);
        value["x"] =
            json!("115792089237316195423570985008687907853269984665640564039457584007913129639935");
        assert_eq!(source_bytes(&value, "x").unwrap(), [255; 32]);
        value["x"] =
            json!("115792089237316195423570985008687907853269984665640564039457584007913129639936");
        assert!(source_bytes(&value, "x").is_err());
        value["x"] = json!("0255");
        assert!(source_bytes(&value, "x").is_err());
    }

    #[test]
    #[cfg(unix)]
    fn receive_epoch_recovers_package_law_through_durable_device_custody() {
        use crate::{object_epoch_packages::{self, Recipient}, object_keys_hybrid};
        use ed25519_dalek::SigningKey;
        use ring::rand::{SecureRandom, SystemRandom};
        use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
        use std::io::Write;

        fn decimal(bytes: &[u8]) -> String {
            let mut digits=vec![0u8];
            for byte in bytes {
                let mut carry=*byte as u16;
                for digit in &mut digits {
                    carry+=(*digit as u16)*256;
                    *digit=(carry%10) as u8;
                    carry/=10;
                }
                while carry>0 { digits.push((carry%10) as u8); carry/=10; }
            }
            digits.iter().rev().map(|digit|(b'0'+digit) as char).collect()
        }

        let mut random=[0;16];SystemRandom::new().fill(&mut random).unwrap();
        let root=std::env::temp_dir().join(format!("mini-receive-epoch-{}",crate::hex(&random)));
        fs::create_dir(&root).unwrap();
        fs::set_permissions(&root,fs::Permissions::from_mode(0o700)).unwrap();
        let state=root.join("keys.json");
        let storage=root.join("storage.key");
        let storage_bytes=[3;32];
        let mut key_file=fs::OpenOptions::new().write(true).create_new(true).mode(0o600).open(&storage).unwrap();
        key_file.write_all(&storage_bytes).unwrap();key_file.sync_all().unwrap();drop(key_file);

        let (secret,public)=object_keys_hybrid::generate().unwrap();
        let generation=object_keys_hybrid::key_commitment(&public).unwrap();
        let mut retained=Store::open(&state,storage_bytes).unwrap();
        retained.retain_device(&generation,&secret,&public).unwrap();
        drop(retained);
        let writer=SigningKey::from_bytes(&[6;32]);
        let mut view=json!({"type":"minidregg-object-audience-v1","subject":"7","object":"72",
            "worldRoot":"600","policyAddress":"401","semanticLawDigest":"400",
            "policyEpoch":"1","policyRevision":"2","currentAuthorityRoot":"501","currentObjectRoot":"502",
            "epoch":"2","transition":"3","audience":"8","devices":"9","history":"10",
            "manifest":"0","authoritySnapshot":"11","deviceSnapshot":"12","active":true,
            "audienceState":{"object":"72","epoch":"2","parent":"1","transition":"3",
                "audience":"8","devices":"9","history":"10","manifest":"0","mode":"active",
                "authoritySnapshot":"11","deviceSnapshot":"12"}});
        let operation=[4;32];
        let mut package_context=context(&view,operation).unwrap();
        package_context.law=source_bytes(&view,"semanticLawDigest").unwrap();
        assert_ne!(package_context.law,source_bytes(&view,"policyAddress").unwrap());
        let recipients=[Recipient {subject:"7".into(),capability:"20".into(),device_source:"99".into(),
            generation,key_commitment:generation,public}];
        // This unit boundary receives an already source-checked roster preimage;
        // source admission itself is exercised by the Host acceptance journey.
        let prepared=object_epoch_packages::prepare(&package_context,
            &source_bytes(&view,"audience").unwrap(),&source_bytes(&view,"devices").unwrap(),
            &source_bytes(&view,"history").unwrap(),&source_bytes(&view,"authoritySnapshot").unwrap(),
            &source_bytes(&view,"deviceSnapshot").unwrap(),&recipients,b"source-checked-roster-fixture",
            "7",&generation,&writer).unwrap();
        let commitment=decimal(&prepared.commitment);
        view["manifest"]=json!(commitment);view["audienceState"]["manifest"]=view["manifest"].clone();
        let request_path=root.join("receive.json");
        let request=json!({"generation":crate::hex(&generation),"manifest":crate::hex(&prepared.manifest),
            "operation":crate::hex(&operation),"writer":crate::hex(&writer.verifying_key().to_bytes())});
        fs::write(&request_path,serde_json::to_vec(&request).unwrap()).unwrap();
        receive_epoch(&view,&request_path,&state,&storage).unwrap();
        let reopened=Store::open(&state,storage_bytes).unwrap();
        assert_eq!(*reopened.historical_key(&anchor(&view).unwrap()).unwrap(),*prepared.key);
        drop(reopened);
        // A later law revision may retain this exact admitted epoch manifest.
        // Package authentication uses its original signed law, not the new source hash.
        let mut later=view.clone();later["semanticLawDigest"]=json!("402");
        later["policyAddress"]=json!("403");later["policyRevision"]=json!("3");
        receive_epoch(&later,&request_path,&state,&storage).unwrap();
        let reopened=Store::open(&state,storage_bytes).unwrap();
        assert_eq!(*reopened.historical_key(&anchor(&later).unwrap()).unwrap(),*prepared.key);
        drop(reopened);
        let journal=fs::read(&state).unwrap();

        for field in ["epoch","devices","deviceSnapshot","manifest"] {
            let mut altered=view.clone();altered[field]=json!("13");
            assert!(receive_epoch(&altered,&request_path,&state,&storage).is_err(),"accepted altered {field}");
            assert_eq!(fs::read(&state).unwrap(),journal,"refused receive modified custody");
        }
        let mut damaged_manifest=prepared.manifest.clone();damaged_manifest[8]^=1;
        let mut altered=request.clone();altered["manifest"]=json!(crate::hex(&damaged_manifest));
        fs::write(&request_path,serde_json::to_vec(&altered).unwrap()).unwrap();
        assert!(receive_epoch(&view,&request_path,&state,&storage).is_err());
        let mut altered=request.clone();altered["dhPublic"]=json!(crate::hex(&[99;32]));
        fs::write(&request_path,serde_json::to_vec(&altered).unwrap()).unwrap();
        assert!(receive_epoch(&view,&request_path,&state,&storage).is_err());
        assert_eq!(fs::read(&state).unwrap(),journal);
        fs::remove_dir_all(root).unwrap();
    }
}

pub(crate) fn release(
    host: &Path,
    _config: &Path,
    request: &Path,
    key: &Path,
    dir: &Path,
) -> Result<()> {
    use ed25519_dalek::Signer;
    // observe() already retained exact config/intent and source authorization.
    let config = dir.join("config.json");
    let requested = dir.join("release-spec.request.bin");
    crate::author(
        host,
        &config,
        OsStr::new("object-message-release-spec"),
        request,
        &requested,
    )?;
    let canonical = dir.join("release-spec.bin");
    let header = dir.join("release-header.bin");
    crate::host_files(
        host,
        &config,
        &[
            Path::new("object-message-release-plan"),
            &dir.join("signed-observation.bin"),
            &requested,
            &canonical,
            &header,
        ],
    )?;
    let signature = crate::read_secret(key)?
        .sign(&fs::read(&header).map_err(|e| e.to_string())?)
        .to_bytes();
    let detached = dir.join("release-signature.bin");
    crate::write_new(&detached, &signature)?;
    let ingress = dir.join("release-ingress.bin");
    crate::host_files(
        host,
        &config,
        &[
            Path::new("object-message-release-assemble"),
            &canonical,
            &header,
            &detached,
            &ingress,
        ],
    )?;
    crate::sync_retained_call(dir, &ingress)?;
    let binary = dir.join("release-outcome.bin");
    let rendered = dir.join("release-outcome.json");
    crate::host_files(
        host,
        &config,
        &[
            Path::new("object-message-release-submit"),
            &ingress,
            &binary,
        ],
    )?;
    let outcome = crate::inspect(host, &config, "outcome", &binary, &rendered)?;
    crate::print_confirmed_outcome(&outcome)
}
/// Source publication exact retry; this does not report receiver execution.
pub(crate) fn release_retry(dir: &Path, lookup: bool) -> Result<()> {
    let (host, config, socket) = crate::manifest_paths(dir)?;
    if socket.is_some() {
        return Err("object release retry requires pinned local Host".into());
    }
    let ingress = dir.join("release-ingress.bin");
    let (binary, rendered) = crate::next_retry(dir)?;
    let verb = if lookup {
        "object-message-release-lookup"
    } else {
        "object-message-release-submit"
    };
    crate::host_files(&host, &config, &[Path::new(verb), &ingress, &binary])?;
    let outcome = crate::inspect(&host, &config, "outcome", &binary, &rendered)?;
    crate::print_confirmed_outcome(&outcome)
}

/// Retain the exact already signed receiver ingress before any emission.
pub(crate) fn consume(host: &Path, config: &Path, input: &Path, dir: &Path) -> Result<()> {
    fs::create_dir(dir).map_err(|e| e.to_string())?;
    let pinned = dir.join("config.json");
    crate::write_new(&pinned, &fs::read(config).map_err(|e| e.to_string())?)?;
    crate::write_manifest(dir, host, &pinned, "object-consume")?;
    let ingress = dir.join("consumption-ingress.bin");
    crate::write_new(&ingress, &fs::read(input).map_err(|e| e.to_string())?)?;
    crate::sync_retained_call(dir, &ingress)?;
    consume_retry(dir, false)
}

pub(crate) fn consume_retry(dir: &Path, lookup: bool) -> Result<()> {
    let (host, config, socket) = crate::manifest_paths(dir)?;
    if socket.is_some() {
        return Err("object consumption requires pinned local Host".into());
    }
    let ingress = dir.join("consumption-ingress.bin");
    let (binary, rendered) = crate::next_retry(dir)?;
    let verb = if lookup {
        "object-message-consumption-lookup"
    } else {
        "object-message-consumption-submit"
    };
    crate::host_files(&host, &config, &[Path::new(verb), &ingress, &binary])?;
    let outcome = crate::inspect(&host, &config, "outcome", &binary, &rendered)?;
    crate::print_confirmed_outcome(&outcome)
}

/// Decrypt a record in the freshly observed current object context. Historical
/// disclosure needs its separately verified historical source context.
pub(crate) fn open_message(
    v: &Value,
    request: &Path,
    state: &Path,
    storage: &Path,
    output: &Path,
) -> Result<()> {
    let r: Value = serde_json::from_slice(&fs::read(request).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let a = anchor(v)?;
    let ctx = context(v, bytes(&r, "operation")?)?;
    let mut store = Store::open(state, crate::read_secret(storage)?.to_bytes())?;
    store.reconcile_anchor(&a)?;
    let key = store.historical_key(&a)?;
    let wire = crate::decode_hex(r["ciphertext"].as_str().ok_or("ciphertext must be hex")?)?;
    let plain = zeroize::Zeroizing::new(crate::object_messages::open(
        &ctx,
        &key,
        &bytes(&r, "writer")?,
        &wire,
    )?);
    crate::write_new(output, &plain)
}
