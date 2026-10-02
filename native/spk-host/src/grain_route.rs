//! `spk-host grain route PROFILE APP ROUTE_REQUEST.json`: bind one
//! participant entrance to an installed application.
//!
//! Everything the entrance pins is read from the participant's retained,
//! Mini-accepted evidence: the session birth (session, descriptor, subject,
//! kind, owner capabilities) and the event22 ticket issue (ticket resource,
//! admitted issue index). A delegated participant may explicitly select its
//! manifest observation capability; that selector grants no authority. The
//! session enrollment is not an input: it binds the
//! session to one serving app generation, so the participant enrolls (and
//! renews after every restart) against the running app, after START. None of
//! this confers authority: every HTTP request is still authored, signed and
//! admitted by Mini (op36/37/34), including the current enrollment, before
//! fd3 delivery.

use crate::dispatch_author::FixedAuthoring;
use crate::dispatch_native::{private_dir, write_new};
use crate::grain::HostView;
use serde::Deserialize;
use serde_json::{json, Value};
use std::fs::{self, DirBuilder, File};

/// Human dispatch signing slots in Mini's plan order: the one session target's
/// invocation (4:0; a single target needs no role-8 observation), the
/// authority leg (1:0), then the app, manifest, enrollment and ticket
/// observations (9:0..9:3). Mini's plan inspection is decisive: any other
/// shape refuses before a header is signed.
const DISPATCH_SLOTS: &[(&str, &str)] = &[
    ("4", "0"),
    ("1", "0"),
    ("9", "0"),
    ("9", "1"),
    ("9", "2"),
    ("9", "3"),
];
use std::io;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};

fn invalid(reason: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason.into())
}

fn decimal(value: &str) -> bool {
    crate::lifecycle_selector::decimal(value)
}

fn read_json(path: &Path) -> io::Result<Value> {
    let meta = fs::symlink_metadata(path)?;
    if !meta.is_file()
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.permissions().mode() & 0o077 != 0
        || meta.len() == 0
        || meta.len() > 4 * 1024 * 1024
    {
        return Err(invalid(format!(
            "retained evidence custody refused: {}",
            path.display()
        )));
    }
    Ok(serde_json::from_slice(&fs::read(path)?)?)
}

fn text<'a>(value: &'a Value, pointer: &str) -> io::Result<&'a str> {
    value
        .pointer(pointer)
        .and_then(Value::as_str)
        .ok_or_else(|| invalid(format!("retained evidence lacks {pointer}")))
}

fn number(value: &Value, pointer: &str) -> io::Result<String> {
    let found = value
        .pointer(pointer)
        .ok_or_else(|| invalid(format!("retained evidence lacks {pointer}")))?;
    let text = found
        .as_str()
        .map(str::to_owned)
        .or_else(|| found.as_u64().map(|n| n.to_string()))
        .ok_or_else(|| invalid(format!("{pointer} is not a decimal")))?;
    if !decimal(&text) {
        return Err(invalid(format!("{pointer} is not canonical")));
    }
    Ok(text)
}

fn confirmed(receipt: &Value) -> bool {
    receipt.get("type").and_then(Value::as_str) == Some("confirmed")
        && matches!(
            receipt.get("confirmation").and_then(Value::as_str),
            Some("installed" | "replayed")
        )
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ParticipantKey {
    key_id: String,
    key_epoch: String,
    public_key_hex: String,
    seed_path: PathBuf,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RouteRequest {
    protocol: String,
    name: String,
    expected_host: String,
    display_name: String,
    preferred_handle: String,
    session_source: PathBuf,
    session_receipt: PathBuf,
    ticket_issue: PathBuf,
    /// A participant's delegated manifest observation grant. Omission preserves
    /// the legacy owner entrance selector. Native admission checks authority.
    #[serde(default)]
    manifest_observe_capability: Option<String>,
    /// Opt in only a source-derived API session to bounded export custody.
    #[serde(default)]
    export_capture: bool,
    participant_key: ParticipantKey,
}

struct Derived {
    subject: String,
    session: String,
    descriptor: String,
    kind: String,
    ticket: String,
    issue_index: String,
    session_observe: String,
    manifest_observe: String,
    enrollment_observe: String,
}

fn derive(
    app: &str,
    selector: &crate::lifecycle_selector::LifecycleSelector,
    request: &RouteRequest,
) -> io::Result<Derived> {
    let manifest_observe = request
        .manifest_observe_capability
        .as_ref()
        .unwrap_or(&selector.package_observe_capability)
        .clone();
    if !decimal(&manifest_observe) {
        return Err(invalid("manifest observation capability is not canonical"));
    }
    let session_source = read_json(&request.session_source)?;
    let session = session_source
        .pointer("/applicationSessionGrainBirth/applicationSessionBirth/session")
        .ok_or_else(|| invalid("session source is not a current-session birth"))?;
    if !confirmed(&read_json(&request.session_receipt)?) {
        return Err(invalid("session birth receipt is not confirmed"));
    }
    let subject = number(session, "/participant")?;
    let session_id = number(session, "/session")?;
    let descriptor = number(session, "/descriptor")?;
    let kind = text(session, "/kind")?.to_owned();
    if number(session, "/app")? != app || !matches!(kind.as_str(), "web" | "api") {
        return Err(invalid("session birth names another app or kind"));
    }
    let ticket_request = read_json(&request.ticket_issue.join("request.json"))?;
    let anchor = read_json(&request.ticket_issue.join("receipt-anchor.json"))?;
    let accepted: u128 = number(&anchor, "/receipt/acceptedCount")?
        .parse()
        .map_err(|_| invalid("ticket receipt count exceeds bound"))?;
    if accepted == 0 {
        return Err(invalid("ticket receipt count is zero"));
    }
    let participant =
        |name: &str| number(&ticket_request, &format!("/spec/ticket/participant/{name}"));
    if number(&ticket_request, "/spec/ticket/scope/app")? != app
        || participant("session")? != session_id
        || participant("descriptorResource")? != descriptor
        || participant("subject")? != subject
        || text(&ticket_request, "/spec/ticket/participant/kind")? != kind
    {
        return Err(invalid("event22 ticket differs from the session birth"));
    }
    let ticket = number(&ticket_request, "/spec/ticket/resource")?;
    let issue_index = (accepted - 1).to_string();
    Ok(Derived {
        subject,
        session: session_id,
        descriptor,
        kind,
        ticket,
        issue_index,
        session_observe: number(session, "/sessionOwnerCapability")?,
        manifest_observe,
        enrollment_observe: number(session, "/descriptorOwnerCapability")?,
    })
}

fn custody_json(
    app: &str,
    selector: &crate::lifecycle_selector::LifecycleSelector,
    derived: &Derived,
    key: &ParticipantKey,
    slots: &[(String, String)],
) -> Value {
    json!({
        "protocol":"mini-spk-human-dispatch-custody-v1",
        "app":app,
        "subject":derived.subject,
        "session":derived.session,
        "sessionKind":derived.kind,
        "issueIndex":derived.issue_index,
        "ticketResource":derived.ticket,
        "packageManifest":selector.package_manifest,
        "snapshotManifest":selector.snapshot_manifest,
        "sessionObserveCapability":derived.session_observe,
        "manifestObserveCapability":derived.manifest_observe,
        "enrollmentObserveCapability":derived.enrollment_observe,
        "signers":slots.iter().map(|(role, index)| json!({
            "role":role,"index":index,"keyId":key.key_id,"keyEpoch":key.key_epoch,
            "publicKeyHex":key.public_key_hex,"seedPath":key.seed_path})).collect::<Vec<_>>(),
    })
}

fn check_retained_custody(custody: &Value, derived: &Derived, route_name: &str) -> io::Result<()> {
    for (field, expected) in [
        ("/subject", &derived.subject),
        ("/session", &derived.session),
        ("/ticketResource", &derived.ticket),
        ("/issueIndex", &derived.issue_index),
        ("/manifestObserveCapability", &derived.manifest_observe),
    ] {
        if text(custody, field)? != expected {
            return Err(invalid(format!(
                "existing route {} differs from retained participant evidence",
                route_name
            )));
        }
    }
    Ok(())
}

pub(crate) fn route(host: &HostView<'_>, app: &str, request_path: &Path) -> io::Result<Value> {
    let request: RouteRequest = serde_json::from_slice(&fs::read(request_path)?)?;
    if request.protocol != "mini-spk-grain-route-request-v1"
        || request.name.is_empty()
        || request.name.len() > 32
        || !request
            .name
            .bytes()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
        || request.display_name.is_empty()
        || request.preferred_handle.is_empty()
    {
        return Err(invalid("grain route request refused"));
    }
    let app_dir = host.state_root.join("apps").join(app);
    private_dir(&app_dir)?;
    let placement = crate::grain::load_placement(&app_dir.join("placement.json"))?;
    let derived = derive(app, &placement.selector, &request)?;
    if request.export_capture && derived.kind != "api" {
        return Err(invalid(
            "export capture requires a source-derived api session",
        ));
    }
    let installed = crate::materialize::verify_installed_spk(
        &PathBuf::from(format!(
            "/var/lib/minidregg/spk/packages/sha256-{}",
            placement.raw_sha256
        )),
        placement.app_uid,
    )?;
    let bridge = minidregg_spk_rpc::decode_bridge_config(
        installed
            .signed_bridge_config
            .as_deref()
            .ok_or_else(|| invalid("installed package has no signed bridge"))?,
    )
    .map_err(io::Error::other)?;
    let routes = app_dir.join("routes");
    match DirBuilder::new().mode(0o700).create(&routes) {
        Ok(()) => File::open(&app_dir)?.sync_all()?,
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
        Err(error) => return Err(error),
    }
    private_dir(&routes)?;
    let directory = routes.join(&request.name);
    if derived.kind == "api" && bridge.api_path.is_none() {
        return Err(invalid("package has no signed API path for an api route"));
    }
    if !directory.exists() {
        let slots: Vec<(String, String)> = DISPATCH_SLOTS
            .iter()
            .map(|(role, index)| ((*role).to_owned(), (*index).to_owned()))
            .collect();
        let staging = routes.join(format!(".{}.staging", request.name));
        if staging.exists() {
            fs::remove_dir_all(&staging)?;
        }
        if request.export_capture {
            crate::http_entrance::initialize_connector_custodian(
                &staging,
                &request.expected_host,
                app,
                &derived.subject,
                &derived.session,
                &derived.ticket,
            )?;
        } else {
            crate::http_entrance::initialize_custodian(
                &staging,
                &request.expected_host,
                app,
                &derived.subject,
                &derived.session,
                &derived.ticket,
                &derived.kind,
            )?;
        }
        let custody = custody_json(
            app,
            &placement.selector,
            &derived,
            &request.participant_key,
            &slots,
        );
        let fixed: FixedAuthoring = serde_json::from_value(custody.clone())?;
        fixed.validate()?;
        write_new(
            &staging,
            "dispatch-custody.json",
            &serde_json::to_vec_pretty(&custody)?,
        )?;
        write_new(
            &staging,
            "route.json",
            &serde_json::to_vec_pretty(&json!({
                "protocol":"mini-spk-grain-route-v1",
                "displayName":request.display_name,
                "preferredHandle":request.preferred_handle,
            }))?,
        )?;
        File::open(&staging)?.sync_all()?;
        fs::rename(&staging, &directory)?;
        File::open(&routes)?.sync_all()?;
    }
    let custody = read_json(&directory.join("dispatch-custody.json"))?;
    check_retained_custody(&custody, &derived, &request.name)?;
    let policy = crate::http_entrance::CustodianPolicy::load(&directory)?;
    check_retained_policy(&policy, app, &derived, &request)?;
    Ok(json!({
        "protocol":"mini-spk-grain-route-v1",
        "app":app,
        "name":request.name,
        "directory":directory,
        "socket":directory.join("http.sock"),
        "kind":derived.kind,
        "subject":derived.subject,
        "session":derived.session,
        "descriptor":derived.descriptor,
        "ticket":derived.ticket,
        "issueIndex":derived.issue_index,
        "tokenFile":directory.join(if derived.kind == "api" { "api.token" } else { "bootstrap.token" }),
        "signedApiPath":bridge.api_path,
    }))
}

fn check_retained_policy(
    policy: &crate::http_entrance::CustodianPolicy,
    app: &str,
    derived: &Derived,
    request: &RouteRequest,
) -> io::Result<()> {
    let api = policy.fixed_session_kind == crate::http_entrance::EntranceKind::Api;
    if policy.expected_host != request.expected_host
        || policy.fixed_app != app
        || policy.fixed_subject != derived.subject
        || policy.fixed_session != derived.session
        || policy.fixed_ticket != derived.ticket
        || api != (derived.kind == "api")
        || policy.export_capture != request.export_capture
        || (policy.export_capture && !api)
    {
        return Err(invalid(
            "retained route custody differs from requested authority or export opt-in",
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lifecycle_selector::LifecycleSelector;
    use std::os::unix::fs::OpenOptionsExt;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT: AtomicU64 = AtomicU64::new(0);

    struct Evidence(PathBuf);
    impl Evidence {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "spk-route-delegate-{}-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            DirBuilder::new().mode(0o700).create(&path).unwrap();
            Self(path)
        }
        fn write(&self, name: &str, value: Value) -> PathBuf {
            use std::io::Write;
            let path = self.0.join(name);
            let mut file = fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(&path)
                .unwrap();
            file.write_all(&serde_json::to_vec(&value).unwrap())
                .unwrap();
            path
        }
    }
    impl Drop for Evidence {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
    fn selector() -> LifecycleSelector {
        LifecycleSelector {
            app: "4601".into(),
            package_manifest: "4602".into(),
            snapshot_manifest: "4603".into(),
            app_capability: "3101".into(),
            app_observe_capability: "3101".into(),
            package_capability: "3103".into(),
            package_observe_capability: "3103".into(),
        }
    }
    fn request(e: &Evidence, subject: &str, manifest: Option<&str>) -> RouteRequest {
        let session_source = e.write(
            "session.json",
            json!({"applicationSessionGrainBirth":{"applicationSessionBirth":{"session":{
            "app":"4601","session":"4610","descriptor":"4611","participant":subject,"kind":"web",
            "sessionOwnerCapability":"3211","descriptorOwnerCapability":"3213"}}}}),
        );
        let session_receipt = e.write(
            "birth.json",
            json!({"type":"confirmed","confirmation":"installed"}),
        );
        e.write(
            "request.json",
            json!({"spec":{"ticket":{"resource":"4620","scope":{"app":"4601"},"participant":{
            "session":"4610","descriptorResource":"4611","subject":subject,"kind":"web"}}}}),
        );
        e.write(
            "receipt-anchor.json",
            json!({"receipt":{"acceptedCount":"42"}}),
        );
        RouteRequest {
            protocol: "mini-spk-grain-route-request-v1".into(),
            name: "delegate".into(),
            expected_host: "grain.test".into(),
            display_name: "Delegate".into(),
            preferred_handle: "delegate".into(),
            session_source,
            session_receipt,
            ticket_issue: e.0.clone(),
            manifest_observe_capability: manifest.map(str::to_owned),
            export_capture: false,
            participant_key: ParticipantKey {
                key_id: format!("{subject}00{subject}"),
                key_epoch: "2".into(),
                public_key_hex: "00".repeat(32),
                seed_path: e.0.join("seed"),
            },
        }
    }

    #[test]
    fn retained_capture_route_cannot_switch_authority_or_opt_in() {
        let e = Evidence::new();
        let mut req = request(&e, "91", None);
        let mut d = derive("4601", &selector(), &req).unwrap();
        let mut p = crate::http_entrance::CustodianPolicy {
            expected_host: req.expected_host.clone(),
            fixed_app: "4601".into(),
            fixed_subject: d.subject.clone(),
            fixed_session: d.session.clone(),
            fixed_ticket: d.ticket.clone(),
            fixed_session_kind: crate::http_entrance::EntranceKind::Browser,
            export_capture: false,
            browser_token_sha256: [0; 32],
            bootstrap_token_sha256: [0; 32],
            api_token_sha256: [0; 32],
        };
        check_retained_policy(&p, "4601", &d, &req).unwrap();
        req.export_capture = true;
        assert!(check_retained_policy(&p, "4601", &d, &req).is_err());
        p.export_capture = true;
        assert!(check_retained_policy(&p, "4601", &d, &req).is_err());
        p.fixed_session_kind = crate::http_entrance::EntranceKind::Api;
        d.kind = "api".into();
        check_retained_policy(&p, "4601", &d, &req).unwrap();
        p.fixed_subject = "92".into();
        assert!(check_retained_policy(&p, "4601", &d, &req).is_err());
    }
    #[test]
    fn delegate_manifest_selector_reaches_dispatch_custody() {
        for (subject, cap) in [("7", "3231"), ("9", "3241")] {
            let evidence = Evidence::new();
            let request = request(&evidence, subject, Some(cap));
            let selector = selector();
            let derived = derive("4601", &selector, &request).unwrap();
            assert_eq!(derived.subject, subject);
            assert_eq!(derived.manifest_observe, cap);
            let custody = custody_json("4601", &selector, &derived, &request.participant_key, &[]);
            assert_eq!(custody["manifestObserveCapability"], cap);
        }
    }

    #[test]
    fn absent_selector_preserves_owner_entrance() {
        let evidence = Evidence::new();
        let request = request(&evidence, "8", None);
        assert_eq!(
            derive("4601", &selector(), &request)
                .unwrap()
                .manifest_observe,
            "3103"
        );
    }

    #[test]
    fn noncanonical_manifest_selector_is_refused() {
        for bad in ["", "03231", "+3231", "-1", " 3231", "3.2"] {
            let evidence = Evidence::new();
            let request = request(&evidence, "7", Some(bad));
            assert!(derive("4601", &selector(), &request).is_err());
        }
    }

    #[test]
    fn existing_route_cannot_silently_change_manifest_selector() {
        let evidence = Evidence::new();
        let request = request(&evidence, "7", Some("3231"));
        let selector = selector();
        let mut derived = derive("4601", &selector, &request).unwrap();
        let retained = custody_json("4601", &selector, &derived, &request.participant_key, &[]);
        check_retained_custody(&retained, &derived, "delegate").unwrap();
        derived.manifest_observe = "3241".into();
        assert!(check_retained_custody(&retained, &derived, "delegate").is_err());
        assert_eq!(retained["manifestObserveCapability"], "3231");
    }
}
