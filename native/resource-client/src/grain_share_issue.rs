//! Operator custody for the distinct event-22 grain-backed share ticket.
//! Mini owns every Request, Plan, signing-header, and Ingress codec. This
//! client retains one exact plan/ingress and never retries an uncertain issue.
use super::share_issue as custody;
use super::*;
use std::os::unix::fs::DirBuilderExt;

const REQUEST_LIMIT: usize = 256 * 1024;
const INSPECT_LIMIT: usize = 1_048_576;
const FORMAT: &str = "minidregg-application-grain-share-issue-custody-v1";

struct Retained {
    host: PathBuf,
    config: PathBuf,
    socket: PathBuf,
    ingress: Vec<u8>,
    pin_bytes: Vec<u8>,
}

fn retained(directory: &Path, socket_override: Option<&Path>) -> Result<Retained> {
    drain::private_dir(directory)?;
    let pin_bytes = custody::bounded(&directory.join("pin.json"), 65_536)?;
    let pin: Value = serde_json::from_slice(&pin_bytes)
        .map_err(|e| format!("invalid grain share custody pin: {e}"))?;
    if custody::member(&pin, "format")? != FORMAT {
        return Err("unsupported grain share custody pin".into());
    }
    let host = PathBuf::from(custody::member(&pin, "host")?);
    let config = PathBuf::from(custody::member(&pin, "config")?);
    let socket = match socket_override {
        Some(path) => absolute(path)?,
        None => PathBuf::from(custody::member(&pin, "operatorSocket")?),
    };
    let ingress = custody::bounded(
        &directory.join("ingress.bin"),
        transport::HOST_MAX_FRAME - 1,
    )?;
    if host_image_sha256(&host)? != custody::member(&pin, "hostSha256")?
        || custody::digest(&custody::bounded(&config, 65_536)?)
            != custody::member(&pin, "configSha256")?
        || custody::digest(&custody::bounded(
            &directory.join("request.bin"),
            REQUEST_LIMIT,
        )?) != custody::member(&pin, "requestSha256")?
        || custody::digest(&custody::bounded(
            &directory.join("plan.bin"),
            transport::HOST_MAX_FRAME - 1,
        )?) != custody::member(&pin, "planSha256")?
        || custody::digest(&custody::private_bytes(
            &directory.join("approval.json"),
            65_536,
        )?) != custody::member(&pin, "approvalSha256")?
        || custody::digest(&ingress) != custody::member(&pin, "ingressSha256")?
    {
        return Err("retained grain share Host, config, approval or ingress changed".into());
    }
    Ok(Retained {
        host,
        config,
        socket,
        ingress,
        pin_bytes,
    })
}

fn verify_retained(directory: &Path, state: &Retained) -> Result<()> {
    let current = retained(directory, Some(&state.socket))?;
    if current.pin_bytes != state.pin_bytes
        || current.host != state.host
        || current.config != state.config
        || current.socket != state.socket
        || current.ingress != state.ingress
    {
        return Err("grain share retained Host, config or ingress changed after operation".into());
    }
    Ok(())
}

fn inspect_bounded(
    host: &Path,
    config: &Path,
    kind: &str,
    input: &Path,
    output: &Path,
    maximum: usize,
) -> Result<Value> {
    custody::source_process(
        host,
        config,
        &[
            OsStr::new("inspect"),
            OsStr::new(kind),
            input.as_os_str(),
            output.as_os_str(),
        ],
    )?;
    serde_json::from_slice(&custody::bounded(output, maximum)?)
        .map_err(|error| format!("invalid bounded grain share Host inspection: {error}"))
}

fn confirmed_outcome(
    directory: &Path,
    stem: &str,
    frame: &[u8],
    operation: u8,
    state: &Retained,
) -> Result<Value> {
    let body = custody::expect_reply(frame, operation)?;
    let binary = directory.join(format!("{stem}.outcome.bin"));
    create_private(&binary, body)?;
    sync_directory_ancestors(directory)?;
    inspect_bounded(
        &state.host,
        &state.config,
        "outcome",
        &binary,
        &directory.join(format!("{stem}.outcome.json")),
        65_536,
    )
}

fn reinspect(directory: &Path, state: &Retained, stem: &str) -> Result<Option<Value>> {
    let binary = directory.join(format!("{stem}.outcome.bin"));
    let frame_path = directory.join(format!("{stem}.frame"));
    if !frame_path.exists() {
        if binary.exists() {
            return Err("grain share outcome lacks exact retained frame".into());
        }
        return Ok(None);
    }
    let frame = custody::bounded(&frame_path, transport::HOST_MAX_FRAME)?;
    let operation = if stem == "submit" { 54 } else { 55 };
    if frame.first() == Some(&255) && !binary.exists() {
        return Ok(None);
    }
    if frame.first() != Some(&operation) || frame.len() < 2 {
        return Err("grain share outcome differs from exact Host reply frame".into());
    }
    if binary.exists() {
        if custody::bounded(&binary, transport::HOST_MAX_FRAME - 1)? != frame[1..] {
            return Err("grain share outcome differs from exact Host reply frame".into());
        }
    } else {
        // Reply frame is synced first; recover after a crash before extraction.
        create_private(&binary, &frame[1..])?;
        sync_directory_ancestors(directory)?;
    }
    let presentation = directory.join(format!(
        "{stem}.reinspect-{:04}.json",
        (0..10_000)
            .find(|index| !directory
                .join(format!("{stem}.reinspect-{index:04}.json"))
                .exists())
            .ok_or("grain share reinspection names exhausted")?
    ));
    let observed = inspect_bounded(
        &state.host,
        &state.config,
        "outcome",
        &binary,
        &presentation,
        65_536,
    )?;
    let cached = directory.join(format!("{stem}.outcome.json"));
    if cached.exists() {
        let saved: Value = serde_json::from_slice(&custody::bounded(&cached, 65_536)?)
            .map_err(|e| format!("invalid retained grain share outcome: {e}"))?;
        if saved != observed {
            return Err("retained grain share outcome presentation changed".into());
        }
    }
    Ok(Some(observed))
}

fn historical_anchor(directory: &Path, state: &Retained, lookups: usize) -> Result<Option<Value>> {
    let mut first: Option<(String, String, Value)> = None;
    for stem in std::iter::once("submit".to_owned())
        .chain((0..lookups).map(|index| format!("lookup-{index:04}")))
    {
        let Some(observed) = reinspect(directory, state, &stem)? else {
            continue;
        };
        if custody::confirmed(&observed).is_err() {
            continue;
        }
        let binary_hash = custody::digest(&custody::bounded(
            &directory.join(format!("{stem}.outcome.bin")),
            transport::HOST_MAX_FRAME - 1,
        )?);
        if let Some((_, _, original)) = &first {
            custody::same_receipt(original, &observed)?;
        } else {
            first = Some((stem, binary_hash, observed));
        }
    }
    let Some((stem, binary_hash, original)) = first else {
        if directory.join("receipt-anchor.json").exists() {
            return Err("grain share receipt anchor lacks exact retained outcome".into());
        }
        return Ok(None);
    };
    let expected = json!({"type":"minidregg-grain-share-issue-receipt-anchor-v1",
        "source":stem,"outcomeSha256":binary_hash,
        "receipt":custody::receipt_projection(&original)?});
    let anchor = directory.join("receipt-anchor.json");
    if anchor.exists() {
        let saved: Value = serde_json::from_slice(&custody::bounded(&anchor, 4096)?)
            .map_err(|e| format!("invalid grain share receipt anchor: {e}"))?;
        if saved != expected {
            return Err("grain share receipt anchor differs from original exact outcome".into());
        }
    } else {
        custody::retain_json(&anchor, &expected)?;
    }
    Ok(Some(original))
}

fn approved_request(approval: &Value, request: &[u8], inspection: &Value) -> Result<()> {
    if custody::member(approval, "type")? != "minidregg-grain-share-issue-approval-v1"
        || custody::member(inspection, "type")? != "application-grain-share-issue-request-v1"
        || custody::member(approval, "requestSha256")? != custody::digest(request)
        || custody::member(inspection, "canonicalRequest")? != hex(request)
        || custody::member(approval, "canonicalSpec")?
            != custody::member(inspection, "canonicalSpec")?
    {
        return Err("grain share approval differs from exact source Request".into());
    }
    let spec = inspection
        .get("spec")
        .ok_or("grain share Request lacks Spec")?;
    let ticket = spec
        .get("ticket")
        .ok_or("grain share Request lacks ticket")?;
    let participant = ticket
        .get("participant")
        .ok_or("grain share Request lacks participant")?;
    for (field, actual) in [
        ("issuer", custody::member(spec, "issuer")?),
        (
            "appDelegateCapability",
            custody::member(spec, "appDelegateCapability")?,
        ),
        ("ticketResource", custody::member(ticket, "resource")?),
        (
            "participantSubject",
            custody::member(participant, "subject")?,
        ),
        ("payer", custody::member(inspection, "payer")?),
    ] {
        if custody::member(approval, field)? != actual {
            return Err(format!("grain share approved {field} differs from Request"));
        }
    }
    for field in ["funding", "sourceCapabilities", "tool", "parent"] {
        if approval.get(field) != inspection.get(field) || inspection.get(field).is_none() {
            return Err(format!("grain share approved {field} differs from Request"));
        }
    }
    Ok(())
}

fn ordered_slots(plan: &Value) -> Result<&[Value]> {
    let birth = plan
        .get("birthSlots")
        .and_then(Value::as_array)
        .ok_or("grain share Plan lacks birth signing slots")?;
    let app = plan
        .get("appSlot")
        .ok_or("grain share Plan lacks app signing slot")?;
    let slots = plan
        .get("slots")
        .and_then(Value::as_array)
        .ok_or("grain share Plan lacks ordered signing slots")?;
    if birth.is_empty()
        || slots.len() != birth.len() + 1
        || slots[..birth.len()] != birth[..]
        || slots[birth.len()] != *app
    {
        return Err("grain share Plan did not preserve birth-then-app slot order".into());
    }
    Ok(slots)
}

/// Selection is private and current-image dependent. Approval pins the full
/// source Request and every exact Host-selected signing header before any key
/// signs. Plan and detached assembly are selectors, not native admission.
pub(super) fn prepare(
    host: &Path,
    config: &Path,
    operator_socket: &Path,
    request_json: &Path,
    approval_json: &Path,
    directory: &Path,
) -> Result<()> {
    let host = absolute(host)?;
    let config = absolute(config)?;
    let operator_socket = absolute(operator_socket)?;
    custody::operator_socket_owned(&operator_socket)?;
    let directory = absolute(directory)?;
    let source = custody::bounded(request_json, REQUEST_LIMIT)?;
    let approval_bytes = custody::private_bytes(approval_json, 65_536)?;
    let initial_host_sha = host_image_sha256(&host)?;
    let initial_config = custody::bounded(&config, 65_536)?;
    let check_inputs = || -> Result<()> {
        if host_image_sha256(&host)? != initial_host_sha
            || custody::bounded(&config, 65_536)? != initial_config
            || custody::private_bytes(approval_json, 65_536)? != approval_bytes
        {
            return Err("grain share Host, config or approval changed during custody".into());
        }
        Ok(())
    };
    let approval: Value = serde_json::from_slice(&approval_bytes)
        .map_err(|e| format!("invalid grain share approval: {e}"))?;
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&directory)
        .map_err(|e| format!("cannot create grain share custody directory: {e}"))?;
    sync_directory_ancestors(&directory)?;
    create_private(&directory.join("request.json"), &source)?;
    create_private(&directory.join("approval.json"), &approval_bytes)?;
    create_private(&directory.join("config.json"), &initial_config)?;
    let request_bin = directory.join("request.bin");
    custody::source_process(
        &host,
        &config,
        &[
            OsStr::new("author"),
            OsStr::new("application-share-issue-grain-request"),
            directory.join("request.json").as_os_str(),
            request_bin.as_os_str(),
        ],
    )?;
    sync_retained_call(&directory, &request_bin)?;
    let request = custody::bounded(&request_bin, REQUEST_LIMIT)?;
    let request_inspected = inspect_bounded(
        &host,
        &config,
        "application-share-issue-grain-request",
        &request_bin,
        &directory.join("request-inspected.json"),
        INSPECT_LIMIT,
    )?;
    check_inputs()?;
    approved_request(&approval, &request, &request_inspected)?;

    let frame = session_invoke(&host, &operator_socket, &config, 56, &request)?;
    check_inputs()?;
    create_private(&directory.join("plan.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    let plan = custody::expect_reply(&frame, 56)?;
    let plan_path = directory.join("plan.bin");
    create_private(&plan_path, plan)?;
    let plan_inspected = inspect_bounded(
        &host,
        &config,
        "application-share-issue-grain-plan",
        &plan_path,
        &directory.join("plan-inspected.json"),
        INSPECT_LIMIT,
    )?;
    if custody::member(&plan_inspected, "type")? != "application-grain-share-issue-plan-v1"
        || custody::member(&plan_inspected, "canonicalRequest")? != hex(&request)
        || custody::member(&plan_inspected, "canonicalPlanHex")? != hex(plan)
    {
        return Err("grain share Plan differs from exact approved Request or Plan bytes".into());
    }
    let plan_request = plan_inspected
        .get("request")
        .ok_or("grain share Plan lacks exact Request presentation")?;
    approved_request(&approval, &request, plan_request)?;
    check_inputs()?;
    let slots = ordered_slots(&plan_inspected)?;
    let signers = approval
        .get("signers")
        .and_then(Value::as_array)
        .ok_or("grain share approval lacks ordered signers")?;
    if signers.len() != slots.len() {
        return Err("grain share signing slot count differs from approval".into());
    }
    let mut signatures = Vec::with_capacity(slots.len());
    for (slot, signer) in slots.iter().zip(signers) {
        check_inputs()?;
        let key_path = Path::new(custody::member(signer, "keyPath")?);
        if !key_path.is_absolute() {
            return Err("grain share custody key path must be absolute".into());
        }
        let key = custody::custody_key(key_path)?;
        let header = custody::approved_header(slot, signer, &key)?;
        signatures.push(Value::String(hex(&key.sign(&header).to_bytes())));
    }
    let signatures_json = directory.join("signatures.json");
    custody::retain_json(&signatures_json, &Value::Array(signatures))?;
    let signatures_path = directory.join("signatures.bin");
    custody::source_process(
        &host,
        &config,
        &[
            OsStr::new("signatures"),
            signatures_json.as_os_str(),
            signatures_path.as_os_str(),
        ],
    )?;
    let signatures_bytes = custody::bounded(&signatures_path, REQUEST_LIMIT)?;
    check_inputs()?;
    let mut assembly = Vec::with_capacity(4 + plan.len() + signatures_bytes.len());
    assembly.extend_from_slice(&(plan.len() as u32).to_le_bytes());
    assembly.extend_from_slice(plan);
    assembly.extend_from_slice(&signatures_bytes);
    let assembled_frame = session_invoke(&host, &operator_socket, &config, 57, &assembly)?;
    check_inputs()?;
    create_private(&directory.join("assembly.frame"), &assembled_frame)?;
    let ingress = custody::expect_reply(&assembled_frame, 57)?;
    create_private(&directory.join("ingress.bin"), ingress)?;
    let pin = json!({"format":FORMAT,"host":utf8_path(&host)?,
        "hostSha256":initial_host_sha,"config":utf8_path(&config)?,
        "configSha256":custody::digest(&initial_config),
        "operatorSocket":utf8_path(&operator_socket)?,
        "approvalSha256":custody::digest(&approval_bytes),
        "requestSha256":custody::digest(&request),"planSha256":custody::digest(plan),
        "ingressSha256":custody::digest(ingress)});
    custody::retain_json(&directory.join("pin.json"), &pin)?;
    check_inputs()?;
    println!("{}", directory.join("ingress.bin").display());
    Ok(())
}

/// Exactly one submit attempt; all recovery selects the retained event-22 ingress.
pub(super) fn submit(directory: &Path, socket: Option<&Path>) -> Result<()> {
    let directory = absolute(directory)?;
    let state = retained(&directory, socket)?;
    let marker = directory.join("submit-marker.json");
    if marker.exists() {
        return Err("grain share submit already attempted; use exact lookup".into());
    }
    custody::retain_json(
        &marker,
        &json!({"type":"minidregg-grain-share-issue-submit-v1",
        "ingressSha256":custody::digest(&state.ingress),"socket":utf8_path(&state.socket)?}),
    )?;
    let frame = session_invoke(
        &state.host,
        &state.socket,
        &state.config,
        54,
        &state.ingress,
    )
    .map_err(|e| format!("grain share submit uncertain; exact ingress retained: {e}"))?;
    create_private(&directory.join("submit.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    verify_retained(&directory, &state)?;
    let outcome = confirmed_outcome(&directory, "submit", &frame, 54, &state)?;
    verify_retained(&directory, &state)?;
    custody::confirmed(&outcome)?;
    historical_anchor(&directory, &state, 0)?;
    verify_retained(&directory, &state)?;
    print_json(&outcome)
}

pub(super) fn lookup(directory: &Path, socket: Option<&Path>) -> Result<()> {
    let directory = absolute(directory)?;
    let state = retained(&directory, socket)?;
    let marker_path = directory.join("submit-marker.json");
    let marker: Value = serde_json::from_slice(&custody::bounded(&marker_path, 4096)?)
        .map_err(|e| format!("invalid grain share submit marker: {e}"))?;
    if custody::member(&marker, "type")? != "minidregg-grain-share-issue-submit-v1"
        || custody::member(&marker, "ingressSha256")? != custody::digest(&state.ingress)
    {
        return Err("grain share submit marker differs from exact ingress".into());
    }
    let index = (0..10_000)
        .find(|index| {
            !directory
                .join(format!("lookup-{index:04}.marker.json"))
                .exists()
        })
        .ok_or("grain share lookup evidence names exhausted")?;
    historical_anchor(&directory, &state, index)?;
    verify_retained(&directory, &state)?;
    let stem = format!("lookup-{index:04}");
    custody::retain_json(
        &directory.join(format!("{stem}.marker.json")),
        &json!({"type":"minidregg-grain-share-issue-lookup-v1",
        "ingressSha256":custody::digest(&state.ingress),"socket":utf8_path(&state.socket)?}),
    )?;
    let frame = session_invoke(
        &state.host,
        &state.socket,
        &state.config,
        55,
        &state.ingress,
    )?;
    create_private(&directory.join(format!("{stem}.frame")), &frame)?;
    sync_directory_ancestors(&directory)?;
    verify_retained(&directory, &state)?;
    let outcome = confirmed_outcome(&directory, &stem, &frame, 55, &state)?;
    verify_retained(&directory, &state)?;
    custody::confirmed(&outcome)?;
    historical_anchor(&directory, &state, index + 1)?;
    verify_retained(&directory, &state)?;
    print_json(&outcome)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    fn inspected(request: &[u8]) -> Value {
        json!({"type":"application-grain-share-issue-request-v1",
            "canonicalRequest":hex(request),"canonicalSpec":"abcd",
            "spec":{"issuer":"8","appDelegateCapability":"141",
                "ticket":{"resource":"8500","participant":{"subject":"8"}}},
            "payer":"8","funding":[],"sourceCapabilities":["42"],
            "tool":{"task":"7902","capability":"81","observeCapability":"81"},
            "parent":{"task":"7901","capability":"73","observeCapability":"73"}})
    }

    fn approval(request: &[u8]) -> Value {
        let source = inspected(request);
        json!({"type":"minidregg-grain-share-issue-approval-v1",
            "requestSha256":custody::digest(request),"canonicalSpec":"abcd",
            "issuer":"8","appDelegateCapability":"141",
            "ticketResource":"8500","participantSubject":"8","payer":"8",
            "funding":source["funding"],"sourceCapabilities":source["sourceCapabilities"],
            "tool":source["tool"],"parent":source["parent"]})
    }

    #[test]
    fn full_request_approval_pins_funding_and_both_grain_selectors() {
        let request = b"source-authored exact request";
        let source = inspected(request);
        let approved = approval(request);
        approved_request(&approved, request, &source).unwrap();
        let mut changed = approved.clone();
        changed["funding"] = json!([{"amount":"1"}]);
        assert!(approved_request(&changed, request, &source).is_err());
        let mut changed = approved.clone();
        changed["tool"]["task"] = json!("7903");
        assert!(approved_request(&changed, request, &source).is_err());
        let mut changed = approved;
        changed["parent"]["observeCapability"] = json!("74");
        assert!(approved_request(&changed, request, &source).is_err());
    }

    #[test]
    fn detached_signatures_follow_birth_slots_then_app_slot() {
        let birth = json!([{"role":"1"},{"role":"8"}]);
        let app = json!({"role":"5"});
        let valid = json!({"birthSlots":birth,"appSlot":app,
            "slots":[{"role":"1"},{"role":"8"},{"role":"5"}]});
        assert_eq!(ordered_slots(&valid).unwrap().len(), 3);
        let mut changed = valid;
        changed["slots"][1] = json!({"role":"5"});
        assert!(ordered_slots(&changed).is_err());
    }

    #[test]
    fn frame_only_recovery_anchors_receipt_and_rejects_changed_lookup() {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "grain-share-recovery-{}-{unique:x}",
            std::process::id()
        ));
        fs::create_dir(&directory).unwrap();
        let host = directory.join("host-inspect.sh");
        fs::write(&host, concat!(
            "#!/bin/sh\n",
            "case \"$4\" in\n",
            "  *lookup-*) printf '%s\\n' '{\"type\":\"confirmed\",\"confirmation\":\"replayed\",",
            "\"transactionId\":\"1\",\"eventId\":\"99\",\"acceptedCount\":\"3\",\"imageBoundary\":\"4\"}' > \"$5\" ;;\n",
            "  *) printf '%s\\n' '{\"type\":\"confirmed\",\"confirmation\":\"installed\",",
            "\"transactionId\":\"1\",\"eventId\":\"2\",\"acceptedCount\":\"3\",\"imageBoundary\":\"4\"}' > \"$5\" ;;\n",
            "esac\n"
        )).unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        let config = directory.join("config.json");
        fs::write(&config, b"{}").unwrap();
        let state = Retained {
            host,
            config,
            socket: directory.join("socket"),
            ingress: b"exact ingress".to_vec(),
            pin_bytes: vec![],
        };
        fs::write(directory.join("submit.frame"), [54, 1]).unwrap();
        historical_anchor(&directory, &state, 0).unwrap();
        assert_eq!(fs::read(directory.join("submit.outcome.bin")).unwrap(), [1]);
        assert!(directory.join("receipt-anchor.json").exists());
        fs::write(directory.join("lookup-0000.frame"), [55, 2]).unwrap();
        assert!(historical_anchor(&directory, &state, 1).is_err());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn retained_pin_is_rechecked_after_native_operation() {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory =
            std::env::temp_dir().join(format!("grain-share-pin-{}-{unique:x}", std::process::id()));
        fs::create_dir(&directory).unwrap();
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
        let host = directory.join("host");
        let config = directory.join("config.json");
        let approval = directory.join("approval.json");
        fs::write(&host, b"pinned host").unwrap();
        fs::write(&config, b"pinned config").unwrap();
        create_private(&approval, b"approved").unwrap();
        create_private(&directory.join("request.bin"), b"request").unwrap();
        create_private(&directory.join("plan.bin"), b"plan").unwrap();
        create_private(&directory.join("ingress.bin"), b"ingress").unwrap();
        let pin = json!({"format":FORMAT,
            "host":host,"hostSha256":host_image_sha256(&host).unwrap(),
            "config":config,"configSha256":custody::digest(b"pinned config"),
            "operatorSocket":directory.join("socket"),
            "approvalSha256":custody::digest(b"approved"),
            "requestSha256":custody::digest(b"request"),
            "planSha256":custody::digest(b"plan"),
            "ingressSha256":custody::digest(b"ingress")});
        custody::retain_json(&directory.join("pin.json"), &pin).unwrap();
        let state = retained(&directory, None).unwrap();
        verify_retained(&directory, &state).unwrap();
        fs::write(&config, b"replaced config").unwrap();
        assert!(verify_retained(&directory, &state).is_err());
        fs::remove_dir_all(directory).unwrap();
    }
}
