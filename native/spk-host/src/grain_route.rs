//! `spk-host grain route PROFILE APP ROUTE_REQUEST.json`: bind one
//! participant entrance to an installed application.
//!
//! Everything the entrance pins is read from the participant's retained,
//! Mini-accepted evidence: the session birth (session, descriptor, subject,
//! kind), the event22 ticket issue (ticket resource, admitted issue index,
//! observe capabilities) and the event28 session enrollment (observe
//! selectors). The dispatch signer slots come from a real, effect-free op36
//! plan preview. None of it confers authority: every HTTP request is still
//! authored, signed and admitted by Mini (op36/37/34) before fd3 delivery.

use crate::dispatch_author::FixedAuthoring;
use crate::dispatch_inspection::{HttpProjection, Route};
use crate::dispatch_native::{private_dir, write_new};
use crate::grain::HostView;
use serde::Deserialize;
use serde_json::{json, Value};
use std::fs::{self, DirBuilder, File};
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
    enrollment: PathBuf,
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

fn derive(app: &str, request: &RouteRequest) -> io::Result<Derived> {
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
    let participant = |name: &str| number(&ticket_request, &format!("/spec/ticket/participant/{name}"));
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
    let enrollment_source = read_json(&request.enrollment.join("source.json"))?;
    let enrollment_receipt = read_json(&request.enrollment.join("receipt.json"))?;
    if number(&enrollment_source, "/issueIndex")? != issue_index
        || number(&enrollment_source, "/ticketResource")? != ticket
        || enrollment_receipt.is_null()
    {
        return Err(invalid("session enrollment differs from the ticket issue"));
    }
    Ok(Derived {
        subject,
        session: session_id,
        descriptor,
        kind,
        ticket,
        issue_index,
        session_observe: number(&enrollment_source, "/sessionObserveCapability")?,
        manifest_observe: number(&enrollment_source, "/manifestObserveCapability")?,
        enrollment_observe: number(&enrollment_source, "/descriptorObserveCapability")?,
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

/// Effect-free op36 authoring: the plan's ordered signing slots are the only
/// ones this custody will ever sign; each must name the participant's key.
fn preview_slots(
    host: &HostView<'_>,
    app: &str,
    selector: &crate::lifecycle_selector::LifecycleSelector,
    derived: &Derived,
    key: &ParticipantKey,
    signed_api_path: Option<&str>,
    preview_dir: &Path,
) -> io::Result<Vec<(String, String)>> {
    let provisional: FixedAuthoring = serde_json::from_value(custody_json(
        app,
        selector,
        derived,
        key,
        &[("0".into(), "0".into())],
    ))?;
    let headers: Vec<(String, String)> = Vec::new();
    let route = if derived.kind == "api" {
        Route::Api {
            signed_path: signed_api_path.ok_or_else(|| invalid("package has no signed API path"))?,
        }
    } else {
        Route::Browser
    };
    let http = HttpProjection {
        method: "GET",
        path_and_query: "",
        ordered_headers: &headers,
        body: b"",
        route,
    };
    let request = provisional.request_json("1", &http)?;
    let request_path = write_new(preview_dir, "request.json", &serde_json::to_vec(&request)?)?;
    let request_bytes = host.operator.tool(
        "author",
        "application-dispatch-request",
        &request_path,
        &preview_dir.join("request.bin"),
    )?;
    let reply = host.operator.invoke(36, &request_bytes)?;
    if reply.get(4) != Some(&36) {
        let _ = write_new(preview_dir, "op36-refusal.bin", &reply);
        return Err(invalid(
            "Mini refused the dispatch plan preview (session, ticket or enrollment not current)",
        ));
    }
    let plan = write_new(preview_dir, "plan.bin", &reply[5..])?;
    let inspected = host.operator.tool(
        "inspect",
        "application-dispatch-plan",
        &plan,
        &preview_dir.join("plan.json"),
    )?;
    let view: Value = serde_json::from_slice(&inspected)?;
    let slots = view
        .get("slots")
        .and_then(Value::as_array)
        .ok_or_else(|| invalid("dispatch plan preview lacks slots"))?;
    let mut pins = Vec::with_capacity(slots.len());
    for slot in slots {
        let role = text(slot, "/role")?;
        let index = text(slot, "/index")?;
        if text(slot, "/signing/keyId")? != key.key_id
            || text(slot, "/signing/keyEpoch")? != key.key_epoch
        {
            return Err(invalid(
                "a dispatch slot names a key other than the participant's",
            ));
        }
        pins.push((role.to_owned(), index.to_owned()));
    }
    if pins.is_empty() {
        return Err(invalid("dispatch plan preview has no slots"));
    }
    Ok(pins)
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
    let derived = derive(app, &request)?;
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
    let preview = app_dir.join(format!("route-preview-{}", request.name));
    if !directory.exists() {
        if preview.exists() {
            fs::remove_dir_all(&preview)?;
        }
        DirBuilder::new().mode(0o700).create(&preview)?;
        let slots = preview_slots(
            host,
            app,
            &placement.selector,
            &derived,
            &request.participant_key,
            bridge.api_path.as_deref(),
            &preview,
        )?;
        let staging = routes.join(format!(".{}.staging", request.name));
        if staging.exists() {
            fs::remove_dir_all(&staging)?;
        }
        crate::http_entrance::initialize_custodian(
            &staging,
            &request.expected_host,
            app,
            &derived.subject,
            &derived.session,
            &derived.ticket,
            &derived.kind,
        )?;
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
    for (field, expected) in [
        ("/subject", &derived.subject),
        ("/session", &derived.session),
        ("/ticketResource", &derived.ticket),
        ("/issueIndex", &derived.issue_index),
    ] {
        if text(&custody, field)? != expected {
            return Err(invalid(format!(
                "existing route {} differs from retained participant evidence",
                request.name
            )));
        }
    }
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
