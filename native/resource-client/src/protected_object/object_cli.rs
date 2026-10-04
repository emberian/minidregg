//! Epoch package import into durable participant custody. The caller supplies
//! an actual currently authorized source observation, never a cached view.
//! Typed-object execution and private release are separate receiver paths.
use crate::{
    object_keys::{AdmittedAnchor, Store},
    object_messages::Context,
    Result,
};
use serde_json::{json, Value};
use std::{fs, path::Path};

/// Lossless source Nat -> fixed SHA256/context bytes, big endian. No felt fold.
fn source_bytes(v: &Value, name: &str) -> Result<[u8; 32]> {
    let text = v[name]
        .as_str()
        .ok_or_else(|| format!("source lacks {name}"))?;
    if !mini_sdk::decimal::is_canonical(text)
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
    crate::object_keys_hybrid::refuse_pre_hybrid(&r)?;
    let generation = bytes(&r, "generation")?;
    let (secret, public) = if r.get("hybridSecret").is_some() {
        (
            crate::object_keys_hybrid::secret_from_record(&r)?,
            crate::object_keys_hybrid::public_from_record(&r)?,
        )
    } else {
        let pair = store.load_device(&generation)?;
        if r.get("hybridPublic").is_some()
            && crate::object_keys_hybrid::public_from_record(&r)? != pair.1
        {
            return Err("package public key differs from retained device".into());
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

        use mini_sdk::decimal::from_be_bytes as decimal;

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
        let generation=object_keys_hybrid::key_commitment(&public);
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
        let (_,stranger)=object_keys_hybrid::generate().unwrap();
        let mut altered=request.clone();altered["hybridPublic"]=json!(crate::hex(&stranger.to_bytes()));
        fs::write(&request_path,serde_json::to_vec(&altered).unwrap()).unwrap();
        assert!(receive_epoch(&view,&request_path,&state,&storage).unwrap_err().contains("differs from retained device"));
        // A request in the pre-hybrid shape is refused by name, before custody is consulted.
        for field in ["kemPublic","dhPublic","kemSecret"] {
            let mut old=request.clone();old[field]=json!("00");
            fs::write(&request_path,serde_json::to_vec(&old).unwrap()).unwrap();
            assert!(receive_epoch(&view,&request_path,&state,&storage).unwrap_err().contains("pre-hybrid"),"{field}");
        }
        assert_eq!(fs::read(&state).unwrap(),journal);
        fs::remove_dir_all(root).unwrap();
    }
}
