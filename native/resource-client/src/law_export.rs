//! Member-authored descendant restrictions. The signed policy view supplies
//! the exact predecessor and every untouched v6 facet; Host source validates
//! and encodes the record and receiving authority decides its installation.
use super::*;

const EXTENSIONS: [&str; 5] = [
    "localSelector",
    "parents",
    "descendants",
    "audience",
    "objectDescriptor",
];

fn next_revision(value: &str) -> Result<String> {
    field_decimal(value, "policy revision")?;
    let mut digits = value.as_bytes().to_vec();
    for index in (0..digits.len()).rev() {
        if digits[index] != b'9' {
            digits[index] += 1;
            return String::from_utf8(digits).map_err(|e| e.to_string());
        }
        digits[index] = b'0';
    }
    digits.insert(0, b'1');
    String::from_utf8(digits).map_err(|e| e.to_string())
}

/// A facet update cannot erase another facet by reconstructing an old six-field
/// record. A partially upgraded readback refuses rather than guessing defaults.
pub(super) fn source(policy: &Value, request: &Value) -> Result<Value> {
    let exporting = member(request, "action")? == "install-export";
    let count = EXTENSIONS
        .iter()
        .filter(|key| policy.get(**key).is_some())
        .count();
    if count != 0 && count != EXTENSIONS.len() || exporting && count != EXTENSIONS.len() {
        return Err(
            "signed policy view must expose all v6 composition and audience fields for law export"
                .into(),
        );
    }
    let mut source = json!({"policyId":member(policy,"policyId")?,
        "version":next_revision(member(policy,"version")?)?,
        "domain":member(policy,"domain")?,"semantics":member(policy,"semantics")?,
        "previous":member(policy,"address")?,"predicate":policy.get("predicate").ok_or("signed policy lacks predicate")?});
    for key in EXTENSIONS {
        if let Some(value) = policy.get(key) {
            source[key] = value.clone();
        }
    }
    if exporting {
        let component = request
            .get("component")
            .ok_or("export request lacks component")?;
        if !component.is_null() && !component.is_object() {
            return Err("export component must be an object or null".into());
        }
        source["descendants"] = component.clone();
    } else {
        source["predicate"] = request
            .get("predicate")
            .ok_or("law request lacks predicate")?
            .clone();
    }
    Ok(source)
}

/// Reissuing the same export proposal ID reuses its original source and exact
/// old version/digest. It never quietly authors against a newly read policy.
pub(super) fn retained(root: &Path, id: &str, request: &Value) -> Result<Option<Value>> {
    let directory = root.join("proposals").join(id);
    if !directory.exists() {
        return Ok(None);
    }
    private_dir(&directory)?;
    if bounded_json(&directory.join("request.json"))? != *request {
        return Err("export proposal ID already names a different request".into());
    }
    let summary = bounded_json(&directory.join("proposal.json"))
        .map_err(|_| format!("incomplete export proposal retained at {}; recover its existing intent rather than preparing a new revision",directory.display()))?;
    let intent = fs::read(directory.join("intent.json")).map_err(|e| e.to_string())?;
    if format!("{:x}", Sha256::digest(&intent)) != member(&summary, "intentSha256")? {
        return Err("retained export source differs from its proposal digest".into());
    }
    if !directory.join("intent.bin").is_file() {
        return Err("retained export lacks its source-authored binary".into());
    }
    Ok(Some(summary))
}

pub(super) fn show(root: &Path, workspace: &Value, name: &str) -> Result<()> {
    let reference = reference(root, name)?;
    let (policy, challenge, _) = signed_view(root, workspace, &reference, "policy")?;
    if EXTENSIONS.iter().any(|key| policy.get(*key).is_none()) {
        return Err("signed policy view does not expose the complete v6 law source".into());
    }
    print_json(&json!({"name":name,"judgedAt":challenge,"policy":policy}))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn policy() -> Value {
        json!({"policyId":"9","version":"18446744073709551616","domain":"3","semantics":"4","address":"50",
        "predicate":{"type":"all","predicates":[]},"localSelector":{"verbs":["2"]},
        "parents":[{"policyId":"8","facet":"local","selection":{"type":"head"}}],
        "descendants":null,"audience":{"object":"7","epoch":"2"},"objectDescriptor":"99"})
    }
    #[test]
    fn export_preserves_local_law_and_protected_metadata() {
        let old = policy();
        let component = json!({"selector":{"physicalKinds":["18"]},"predicate":{"type":"all","predicates":[]},"parents":[]});
        let source = source(
            &old,
            &json!({"action":"install-export","component":component}),
        )
        .unwrap();
        for field in [
            "predicate",
            "localSelector",
            "parents",
            "audience",
            "objectDescriptor",
        ] {
            assert_eq!(source[field], old[field]);
        }
        assert_eq!(source["descendants"], component);
        assert_eq!(source["previous"], "50");
        assert_eq!(source["version"], "18446744073709551617");
    }
    #[test]
    fn local_update_cannot_erase_export() {
        let mut old = policy();
        old["descendants"] =
            json!({"selector":{},"predicate":{"type":"all","predicates":[]},"parents":[]});
        let source = source(
            &old,
            &json!({"action":"install-policy","predicate":{"type":"any","predicates":[]}}),
        )
        .unwrap();
        for field in EXTENSIONS {
            assert_eq!(source[field], old[field]);
        }
        let mut partial = old;
        partial.as_object_mut().unwrap().remove("audience");
        assert!(super::source(
            &partial,
            &json!({"action":"install-export","component":null})
        )
        .is_err());
    }
    #[test]
    fn retained_export_never_uses_a_new_policy_head() {
        let root = std::env::temp_dir().join(format!(
            "mini-export-{}-{}",
            std::process::id(),
            random_nonce().unwrap()
        ));
        make_private_dir(&root).unwrap();
        make_private_dir(&root.join("proposals")).unwrap();
        let dir = root.join("proposals/change");
        make_private_dir(&dir).unwrap();
        let request = json!({"action":"install-export","component":null});
        create_private(
            &dir.join("request.json"),
            &serde_json::to_vec(&request).unwrap(),
        )
        .unwrap();
        let intent = b"source with original expected revision/digest";
        create_private(&dir.join("intent.json"), intent).unwrap();
        create_private(&dir.join("intent.bin"), b"canonical").unwrap();
        let summary = json!({"intentSha256":format!("{:x}",Sha256::digest(intent))});
        create_private(
            &dir.join("proposal.json"),
            &serde_json::to_vec(&summary).unwrap(),
        )
        .unwrap();
        assert_eq!(retained(&root, "change", &request).unwrap(), Some(summary));
        assert!(retained(
            &root,
            "change",
            &json!({"action":"install-export","component":{}})
        )
        .is_err());
        fs::write(dir.join("intent.json"), b"changed head").unwrap();
        assert!(retained(&root, "change", &request).is_err());
        fs::remove_dir_all(root).unwrap();
    }
}
