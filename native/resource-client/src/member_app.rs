//! Held app selectors are discovery provenance. Only authenticated native
//! preparation and specialized current admission establish app readiness.
use crate::{workspace, Result};
use ed25519_dalek::Signer;
use serde_json::{json, Value};
use std::ffi::OsStr;
use std::path::Path;
#[path = "../../host-operations.rs"]
mod host_operations;
const PLAN_OP: u8 = host_operations::APPLICATION_DISPATCH_AUTHENTICATED_PLAN;
const READY_OP: u8 = host_operations::APPLICATION_DISPATCH_READY;

fn text<'a>(v: &'a Value, key: &str) -> Result<&'a str> {
    workspace::member(v, key)
}
fn decimal(v: &Value, key: &str) -> Result<()> {
    workspace::decimal(text(v, key)?, key)
}
fn exact(v: &Value, keys: &[&str]) -> Result<()> {
    let object = v
        .as_object()
        .ok_or("App session selectors must be an object")?;
    if object.len() != keys.len() || keys.iter().any(|k| !object.contains_key(*k)) {
        return Err("App session selectors have unexpected or missing fields".into());
    }
    Ok(())
}
fn selectors(reference: &Value, pin: &Value) -> Result<Value> {
    let selected = reference
        .pointer("/provenance/memberApp")
        .ok_or("App session is not configured for this reference")?;
    exact(
        selected,
        &[
            "type",
            "subject",
            "appId",
            "generation",
            "session",
            "sessionGeneration",
            "descriptor",
            "ticketResource",
            "issueIndex",
            "packageManifest",
            "snapshotManifest",
            "references",
            "browser",
        ],
    )?;
    if selected["type"] != "mini-member-app-v1"
        || selected["subject"] != pin["subject"]
        || selected["appId"] != reference["target"]
        || reference["kind"] != "object"
    {
        return Err("App session selectors do not belong to this member and reference".into());
    }
    for key in [
        "subject",
        "appId",
        "session",
        "descriptor",
        "ticketResource",
        "issueIndex",
        "packageManifest",
        "snapshotManifest",
    ] {
        decimal(selected, key)?;
    }
    for key in ["generation", "sessionGeneration"] {
        let n = text(selected, key)?;
        let magnitude = n.strip_prefix('-').unwrap_or(n);
        workspace::decimal(magnitude, key)?;
        if n == "-0" {
            return Err("App generation must be canonical".into());
        }
    }
    exact(
        &selected["references"],
        &["package", "session", "enrollment", "ticket"],
    )?;
    for key in ["package", "session", "enrollment", "ticket"] {
        workspace::validate_ref_name(text(&selected["references"], key)?)?;
    }
    Ok(selected.clone())
}
fn pair(first: &[u8], second: &[u8]) -> Result<Vec<u8>> {
    let width = u32::try_from(first.len()).map_err(|_| "App request exceeds frame bound")?;
    let mut bytes = width.to_le_bytes().to_vec();
    bytes.extend(first);
    bytes.extend(second);
    if bytes.len() >= crate::transport::HOST_MAX_FRAME {
        return Err("App request exceeds frame bound".into());
    }
    Ok(bytes)
}
fn authentication_bytes(domain: &str, semantics: &str, request: &[u8]) -> Vec<u8> {
    [
        format!("MINI/APPLICATION/AUTHENTICATED-PLAN/v1\n{domain}\n{semantics}\n").as_bytes(),
        request,
    ]
    .concat()
}
fn check_plan(
    plan: &Value,
    bytes: &[u8],
    request: &Value,
    request_bytes: &[u8],
    selected: &Value,
    pin: &Value,
    challenge: &Value,
) -> Result<Vec<Vec<u8>>> {
    let mut decoded = plan["request"]
        .as_object()
        .ok_or("App plan lacks its exact request")?
        .clone();
    let kind = decoded.remove("type");
    let canonical = decoded.remove("canonicalRequest");
    if plan["type"] != "application-dispatch-author-plan-v1"
        || plan["canonicalPlan"] != crate::hex(bytes)
        || kind != Some(json!("application-dispatch-author-request-v1"))
        || canonical != Some(json!(crate::hex(request_bytes)))
        || Value::Object(decoded) != *request
        || plan["appResource"] != selected["appId"]
        || plan["appGeneration"] != selected["generation"]
        || plan["sessionResource"] != selected["session"]
        || plan["sessionGeneration"] != selected["sessionGeneration"]
        || plan["subject"] != pin["subject"]
        || plan["domain"] != challenge["domain"]
        || plan["semantics"] != challenge["semantics"]
        || plan["worldRoot"] != challenge["worldRoot"]
        || plan["height"] != challenge["height"]
    {
        return Err("App plan differs from the selected current request".into());
    }
    let own = challenge["signing"]
        .as_array()
        .and_then(|a| a.first())
        .ok_or("Current observation lacks its key identity")?;
    let slots = plan["slots"]
        .as_array()
        .ok_or("App plan lacks signing slots")?;
    if slots.is_empty() || slots.len() > 64 {
        return Err("App signing slot bound refused".into());
    }
    slots
        .iter()
        .map(|slot| {
            let header = text(slot, "header")?;
            let signing = &slot["signing"];
            if signing["decoded"] != true
                || signing["canonical"] != header
                || signing["algorithm"] != "1"
                || own["decoded"] != true
                || own["algorithm"] != "1"
                || signing["keyId"] != own["keyId"]
                || signing["keyEpoch"] != own["keyEpoch"]
            {
                return Err("App signing slot differs from this member's current key".into());
            }
            let bytes = crate::decode_hex(header)?;
            if bytes.is_empty() || bytes.len() > 65536 {
                return Err("App signing header bound refused".into());
            }
            Ok(bytes)
        })
        .collect()
}
fn check_ready(v: &Value, selected: &Value, pin: &Value, challenge: &Value) -> Result<()> {
    if v["type"] != "mini-application-ready-v1" || v["status"] != "admitted" {
        return Err("App authorization is refused by current Mini state".into());
    }
    for (field, expected) in [
        ("app", &selected["appId"]),
        ("generation", &selected["generation"]),
        ("session", &selected["session"]),
        ("sessionGeneration", &selected["sessionGeneration"]),
        ("ticket", &selected["ticketResource"]),
        ("enrollment", &selected["descriptor"]),
        ("subject", &pin["subject"]),
        ("domain", &challenge["domain"]),
        ("semantics", &challenge["semantics"]),
    ] {
        if &v[field] != expected {
            return Err("Current app admission differs from the selected member session".into());
        }
    }
    if v["physicalDispatch"] != false {
        return Err("App readiness must not dispatch a physical request".into());
    }
    Ok(())
}

pub(super) fn status(root: &Path, pin: &Value, name: &str) -> Result<Value> {
    let app = workspace::reference(root, name)?;
    let selected = selectors(&app, pin)?;
    let mut refs = vec![app];
    for (role, target) in [
        ("package", "packageManifest"),
        ("session", "session"),
        ("enrollment", "descriptor"),
        ("ticket", "ticketResource"),
    ] {
        let r = workspace::reference(root, text(&selected["references"], role)?)?;
        if r["kind"] != "object" || r["target"] != selected[target] {
            return Err("Held app observation reference differs from selected session".into());
        }
        refs.push(r);
    }
    let mut reads = vec![];
    let mut challenge: Option<Value> = None;
    for (_, current, signed) in workspace::signed_views(root, pin, &refs, "resource")? {
        if let Some(first) = &challenge {
            for key in ["domain", "semantics", "height", "worldRoot", "authorityRoot"] {
                if current[key] != first[key] {
                    return Err("App state changed during inspection; run app status again".into());
                }
            }
        } else {
            challenge = Some(current);
        }
        reads.push(crate::agent_reserve::private_bytes(
            &signed,
            crate::transport::HOST_MAX_FRAME,
        )?);
    }
    let challenge: Value = challenge.unwrap();
    let (attempt, nonce) = workspace::new_attempt(root)?;
    let request = json!({"issueIndex":selected["issueIndex"],"ticketResource":selected["ticketResource"],
        "packageManifest":selected["packageManifest"],"snapshotManifest":selected["snapshotManifest"],
        "sessionObserveCapability":refs[2]["observeCapability"],"manifestObserveCapability":refs[1]["observeCapability"],
        "enrollmentObserveCapability":refs[3]["observeCapability"],
        "http":{"operationId":nonce,"methodHex":"474554","pathHex":"2f","queryHex":"","headers":[],"bodyHex":""}});
    let host = workspace::workspace_host(pin)?;
    let config = workspace::member_path(pin, "config")?;
    let socket = workspace::member_path(pin, "socket")?;
    crate::create_private(
        &attempt.join("app-request.json"),
        &serde_json::to_vec(&request).map_err(|e| e.to_string())?,
    )?;
    crate::author(
        &host,
        &config,
        OsStr::new("application-dispatch-request"),
        &attempt.join("app-request.json"),
        &attempt.join("app-request.bin"),
    )?;
    let request_bytes = crate::agent_reserve::private_bytes(
        &attempt.join("app-request.bin"),
        crate::transport::HOST_MAX_FRAME,
    )?;
    let key = crate::read_secret(&workspace::member_path(pin, "key")?)?;
    let auth = key
        .sign(&authentication_bytes(
            text(&challenge, "domain")?,
            text(&challenge, "semantics")?,
            &request_bytes,
        ))
        .to_bytes();
    let mut observed = reads.pop().unwrap();
    while let Some(read) = reads.pop() {
        observed = pair(&read, &observed)?;
    }
    let payload = pair(&request_bytes, &pair(&auth, &observed)?)?;
    let plan_bytes = crate::key_rotation::call(&host, &socket, &config, PLAN_OP, &payload)?;
    crate::create_private(&attempt.join("app-plan.bin"), &plan_bytes)?;
    let plan = crate::inspect(
        &host,
        &config,
        "application-dispatch-plan",
        &attempt.join("app-plan.bin"),
        &attempt.join("app-plan.json"),
    )?;
    let headers = check_plan(
        &plan,
        &plan_bytes,
        &request,
        &request_bytes,
        &selected,
        pin,
        &challenge,
    )?;
    let signatures = crate::sign_headers(&key, &headers);
    crate::create_private(
        &attempt.join("app-signatures.json"),
        &serde_json::to_vec(&signatures).map_err(|e| e.to_string())?,
    )?;
    crate::process(
        &host,
        &config,
        &[
            OsStr::new("signatures"),
            attempt.join("app-signatures.json").as_os_str(),
            attempt.join("app-signatures.bin").as_os_str(),
        ],
    )?;
    let signed = crate::agent_reserve::private_bytes(
        &attempt.join("app-signatures.bin"),
        crate::transport::HOST_MAX_FRAME,
    )?;
    let bytes = crate::key_rotation::call(
        &host,
        &socket,
        &config,
        READY_OP,
        &pair(&plan_bytes, &signed)?,
    )?;
    let mut ready: Value =
        serde_json::from_slice(&bytes).map_err(|e| format!("Invalid native app readiness: {e}"))?;
    check_ready(&ready, &selected, pin, &challenge)?;
    ready["name"] = json!(name);
    ready["browser"] = json!({"status":"unavailable"});
    Ok(ready)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exact_member_request_signature_cannot_redirect_across_worlds_or_requests() {
        use ed25519_dalek::{Signature, SigningKey};
        let key = SigningKey::from_bytes(&[7; 32]);
        let bytes = authentication_bytes("8501", "3", b"request");
        let signature = key.sign(&bytes);
        let public = key.verifying_key();
        assert!(public.verify_strict(&bytes, &signature).is_ok());
        for changed in [
            authentication_bytes("8502", "3", b"request"),
            authentication_bytes("8501", "4", b"request"),
            authentication_bytes("8501", "3", b"other"),
        ] {
            assert!(public
                .verify_strict(&changed, &Signature::from_bytes(&signature.to_bytes()))
                .is_err());
        }
    }
    #[test]
    fn plan_rejects_foreign_key_slots_and_changed_request_before_signing() {
        let request = json!({"issueIndex":"1"});
        let bytes = b"plan";
        let request_bytes = b"request";
        let selected = json!({"appId":"9","generation":"2","session":"10","sessionGeneration":"3"});
        let pin = json!({"subject":"7"});
        let challenge = json!({"domain":"8501","semantics":"4","height":"20","worldRoot":"21",
            "signing":[{"decoded":true,"algorithm":"1","keyId":"7","keyEpoch":"2"}]});
        let plan = json!({"type":"application-dispatch-author-plan-v1","canonicalPlan":crate::hex(bytes),
            "request":{"type":"application-dispatch-author-request-v1","canonicalRequest":crate::hex(request_bytes),"issueIndex":"1"},
            "appResource":"9","appGeneration":"2","sessionResource":"10","sessionGeneration":"3","subject":"7",
            "domain":"8501","semantics":"4","height":"20","worldRoot":"21",
            "slots":[{"header":"01","signing":{"decoded":true,"canonical":"01","algorithm":"1","keyId":"7","keyEpoch":"2"}}]});
        assert!(check_plan(
            &plan,
            bytes,
            &request,
            request_bytes,
            &selected,
            &pin,
            &challenge
        )
        .is_ok());
        let mut foreign = plan.clone();
        foreign["slots"][0]["signing"]["keyId"] = json!("8");
        assert!(check_plan(
            &foreign,
            bytes,
            &request,
            request_bytes,
            &selected,
            &pin,
            &challenge
        )
        .is_err());
        let mut changed = plan.clone();
        changed["request"]["issueIndex"] = json!("3");
        assert!(check_plan(
            &changed,
            bytes,
            &request,
            request_bytes,
            &selected,
            &pin,
            &challenge
        )
        .is_err());
        let mut stale = plan.clone();
        stale["slots"][0]["signing"]["keyEpoch"] = json!("1");
        assert!(check_plan(
            &stale,
            bytes,
            &request,
            request_bytes,
            &selected,
            &pin,
            &challenge
        )
        .is_err());
    }
    #[test]
    fn readiness_never_accepts_another_member_generation_or_physical_dispatch() {
        let s = json!({"appId":"9","generation":"2","session":"10","sessionGeneration":"3","ticketResource":"11","descriptor":"12"});
        let p = json!({"subject":"7"});
        let c = json!({"domain":"8501","semantics":"4"});
        let v = json!({"type":"mini-application-ready-v1","status":"admitted","app":"9","generation":"2","session":"10","sessionGeneration":"3","ticket":"11","enrollment":"12","subject":"7","domain":"8501","semantics":"4","physicalDispatch":false});
        assert!(check_ready(&v, &s, &p, &c).is_ok());
        for (field, value) in [
            ("subject", json!("8")),
            ("generation", json!("4")),
            ("sessionGeneration", json!("5")),
            ("physicalDispatch", json!(true)),
        ] {
            let mut wrong = v.clone();
            wrong[field] = value;
            assert!(check_ready(&wrong, &s, &p, &c).is_err());
        }
    }
}
