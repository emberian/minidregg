//! Prospective conversion preserves earlier disclosure and source history.
//! The epoch is enrolled first; packages remain withheld until all selected
//! current text and carried formatting have actual guarded receipts.
use super::*;
use super::super as ws;
use std::path::Path;

pub(super) fn snapshot(root:&Path,workspace:&Value,name:&str,view:&Value,signed:&Path)->Result<Value> {
    let read=ws::rendered_document(root,workspace,name,None,None)?;
    if read.view["cell"]["root"]!=view["cell"]["root"] {
        return Err("document moved while taking its conversion plan; read and retry".into());
    }
    rewriting::validate_current(&read)?;
    let entries=ws::entries(view)?;
    let count=|tag:&str|entries.iter().filter(|r|r["type"]==tag).count();
    Ok(json!({"type":"mini-current-text-conversion-basis-v1","root":view["cell"]["root"],
        "signedObservation":crate::hex(&std::fs::read(signed).map_err(|e|e.to_string())?),
        "rawView":view,"document":read.document,
        "exposure":{"prospectiveCurrentTextOnly":true,"historyAlreadyDisclosed":true,
            "annotationsRemainAtOriginalRevision":count("annotation"),"linkRecordsRemainReadable":count("link"),
            "markRecordsRetained":count("mark"),"structureAndNonTextMetadataRemainUnderCurrentReadLaw":true}}))
}

pub(super) fn preflight(root:&Path,workspace:&Value,name:&str,home:&Path,view:&Value,signed:&Path)->Result<()> {
    let path=home.join(format!("conversion-basis-{}.json",text(&view["cell"],"root")?));
    let basis=snapshot(root,workspace,name,view,signed)?;
    if path.exists() {
        let retained=ws::bounded_json(&path)?;
        same_basis(&retained,&basis)?;
        // A new signed observation has a fresh nonce. Keep the original valid
        // basis while the fresh current read above checks authority/readability.
        Ok(())
    } else {retain_json(&path,&basis)}
}

pub(super) fn finish(root:&Path,workspace:&Value,name:&str,home:&Path,source:&Value,meta:&Value)->Result<()> {
    let dir=home.join("conversion");
    if dir.exists(){ws::private_dir(&dir)?;}else{ws::make_private_dir(&dir)?;}
    if dir.join("published.json").exists() {
        if ws::bounded_json(&dir.join("published.json"))?["audience"]!=source["audienceState"] {
            return Err("completed conversion belongs to another audience; recover that exact membership instead".into());
        }
        return Ok(());
    }
    let namespace=crate::hex(&Sha256::digest([b"MINI/DOCUMENT-CONVERSION/v1".as_slice(),text(meta,"operation")?.as_bytes()].concat()));
    retain_json(&dir.join("epoch.json"),&source["audienceState"])?;
    retain_json(&dir.join("identity.json"),&json!({"object":meta["object"],"name":name,
        "subject":workspace["subject"],"namespace":namespace,"currentTextOnly":true}))?;
    members::publish_current(root,workspace,name,&dir,&json!({"namespace":namespace}),
        &json!({"audience":source["audienceState"]}))?;
    Ok(())
}

fn same_basis(retained:&Value,current:&Value)->Result<()> {
    if retained["type"]!=current["type"] || retained["root"]!=current["root"]
        || retained["rawView"]["cell"]!=current["rawView"]["cell"] {
        return Err("retained conversion basis differs from this exact source cell".into());
    }
    Ok(())
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn repeated_preflight_preserves_basis_across_fresh_signed_observations() {
        let prior=json!({"type":"mini-current-text-conversion-basis-v1","root":"4",
            "rawView":{"cell":{"root":"4","kind":"content"}},"signedObservation":"1111"});
        let mut fresh=prior.clone();fresh["signedObservation"]=json!("2222");
        assert!(same_basis(&prior,&fresh).is_ok());
        fresh["rawView"]["cell"]["root"]=json!("5");
        assert!(same_basis(&prior,&fresh).is_err());
        assert_eq!(prior["signedObservation"],"1111");
    }
}
