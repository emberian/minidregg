//! Sponsor custody for one factory-observation grant to an enrolled subject.
//! The source Host derives the capability and the single signing header; Rust
//! retains every frame, signs that header, and never resubmits an uncertain
//! ingress. Enrollment of the holder and the sponsor's current factory law are
//! checked only by the Host.
use crate::agent_reserve::{bounded, digest, field, private_bytes};
use crate::participant_enrollment::{
    confirmed, decimal, inspect, json_private, key, nonce, pair, pinned, retain_exact, save_json,
    save_json_staged, signed_factory_observation, staged_invoke, transform, FactoryObservation,
};
use crate::participant_namespace::{self, IdKind, Role};
use crate::*;
use serde_json::{json, Value};
use std::os::unix::fs::DirBuilderExt;

const FORMAT: &str = "minidregg-participant-factory-observation-custody-v1";
const COMMAND_KIND: &str = "participant-factory-provisioning";
const PLAN_KIND: &str = "participant-factory-provisioning-plan";
const INGRESS_KIND: &str = "participant-factory-provisioning-ingress";
const PLAN_OPERATION: u8 = 92;
const ASSEMBLE_OPERATION: u8 = 93;
const SUBMIT_OPERATION: u8 = 94;
const LOOKUP_OPERATION: u8 = 95;
const LIMIT: usize = transport::HOST_MAX_FRAME - 1;

/// Everything the sponsor's workspace pins; `holder` is data the Host checks.
pub(crate) struct ObserveGrant<'a> {
    pub(crate) host: &'a Path,
    pub(crate) config: &'a Path,
    pub(crate) socket: &'a Path,
    pub(crate) sponsor_key: &'a Path,
    pub(crate) namespace_root: &'a Path,
    pub(crate) domain: &'a str,
    pub(crate) name: &'a str,
    pub(crate) sponsor: &'a str,
    pub(crate) control: &'a str,
    pub(crate) observe: &'a str,
    pub(crate) factory: &'a str,
    pub(crate) holder: &'a str,
    pub(crate) directory: &'a Path,
}

fn validate_plan(view: &Value, command: &[u8], plan: &[u8]) -> Result<()> {
    if field(view, "type")? != "participant-factory-provisioning-plan-v1"
        || field(view, "canonical")? != hex(plan)
        || field(view, "commandBytes")? != hex(command)
        || view
            .get("sponsorHeader")
            .and_then(|header| header.get("decoded"))
            != Some(&Value::Bool(true))
        || view
            .get("sponsorHeader")
            .and_then(|header| header.get("canonical"))
            .and_then(Value::as_str)
            .is_none_or(str::is_empty)
    {
        return Err("provisioning Plan differs from canonical command or signing header".into());
    }
    Ok(())
}

fn reservation(
    grant: &ObserveGrant<'_>,
    request_bytes: &[u8],
) -> Result<participant_namespace::Reservation> {
    let roles = [Role {
        label: "capability".into(),
        kind: IdKind::Capability,
    }];
    participant_namespace::reserve(
        grant.namespace_root,
        grant.domain,
        grant.sponsor,
        &format!("observe-{}", grant.name),
        request_bytes,
        &roles,
    )
}

/// The stable record: one request (nonce), one reserved capability identity.
/// Every generation authors this same request; the operation marker is derived
/// from the nonce, so at most one generation's ingress can ever be admitted.
fn record(grant: &ObserveGrant<'_>) -> Result<(Value, participant_namespace::Reservation)> {
    let config_bytes = bounded(grant.config, 65_536)?;
    let request_path = grant.directory.join("request.json");
    let expected = json!({"type":"minidregg-participant-factory-observation-request-v1",
        "name":grant.name,"sponsor":grant.sponsor,"control":grant.control,
        "factory":grant.factory,"observeCapability":grant.observe,"holder":grant.holder,
        "hostSha256":host_image_sha256(grant.host)?,"configSha256":digest(&config_bytes)});
    let request = if request_path.exists() {
        let retained = json_private(&request_path)?;
        for name in [
            "type",
            "name",
            "sponsor",
            "control",
            "factory",
            "observeCapability",
            "holder",
            "hostSha256",
            "configSha256",
        ] {
            pinned(&retained, name, field(&expected, name)?)?;
        }
        retained
    } else {
        let mut fresh = expected;
        fresh["nonce"] = json!(nonce()?);
        save_json_staged(&request_path, &fresh)?;
        fresh
    };
    decimal(field(&request, "nonce")?, "provisioning nonce")?;
    let request_bytes = private_bytes(&request_path, 256 * 1024)?;
    let reserved = reservation(grant, &request_bytes)?;
    participant_namespace::bind_attempt(&reserved, grant.directory, &digest(&request_bytes))?;
    retain_exact(&grant.directory.join("config.json"), &config_bytes)?;
    Ok((request, reserved))
}

/// One generation: signed factory observation, canonical command, source Plan.
/// A retained Plan is reused only while the Host still derives the same bytes.
fn plan(
    grant: &ObserveGrant<'_>,
    request: &Value,
    capability: &str,
    directory: &Path,
) -> Result<(Vec<u8>, Vec<u8>)> {
    let config_bytes = bounded(grant.config, 65_536)?;
    retain_exact(&directory.join("config.json"), &config_bytes)?;
    let retained_config = directory.join("config.json");
    let (signed, factory_root, authority_root) = signed_factory_observation(
        &FactoryObservation {
            host: grant.host,
            socket: grant.socket,
            config: &retained_config,
            directory,
            sponsor: grant.sponsor,
            nonce: field(request, "nonce")?,
            factory: grant.factory,
            observe: grant.observe,
        },
        &key(grant.sponsor_key)?,
    )?;
    let command_source = json!({"sponsor":grant.sponsor,"control":grant.control,
        "nonce":field(request,"nonce")?,"expectedFactoryRoot":factory_root,
        "expectedAuthorityRoot":authority_root,"holder":grant.holder,
        "capability":capability});
    save_json_staged(&directory.join("source.json"), &command_source)?;
    transform(
        grant.host,
        grant.socket,
        &retained_config,
        7,
        Some(COMMAND_KIND),
        &directory.join("source.json"),
        &directory.join("command.bin"),
    )?;
    let command = private_bytes(&directory.join("command.bin"), LIMIT)?;
    let command_view = inspect(
        grant.host,
        grant.socket,
        &retained_config,
        COMMAND_KIND,
        &directory.join("command.bin"),
        &directory.join("command.json"),
    )?;
    if field(&command_view, "type")? != "participant-factory-provisioning-v1"
        || field(&command_view, "canonical")? != hex(&command)
        || field(&command_view, "holder")? != grant.holder
        || field(&command_view, "capability")? != capability
    {
        return Err("provisioning canonical command differs from reserved source".into());
    }
    let plan = staged_invoke(
        grant.host,
        grant.socket,
        &retained_config,
        directory,
        "plan",
        PLAN_OPERATION,
        &pair(&signed, &command)?,
    )?;
    let plan_view = inspect(
        grant.host,
        grant.socket,
        &retained_config,
        PLAN_KIND,
        &directory.join("plan.bin"),
        &directory.join("plan.json"),
    )?;
    validate_plan(&plan_view, &command, &plan)?;
    Ok((command, plan))
}

fn seal(
    grant: &ObserveGrant<'_>,
    directory: &Path,
    command: &[u8],
    plan: &[u8],
) -> Result<Vec<u8>> {
    let config = directory.join("config.json");
    let plan_view = json_private(&directory.join("plan.json"))?;
    validate_plan(&plan_view, command, plan)?;
    let header = decode_hex(field(&plan_view["sponsorHeader"], "canonical")?)?;
    let signature = key(grant.sponsor_key)?.sign(&header).to_bytes();
    retain_exact(&directory.join("sponsor-signature.bin"), &signature)?;
    let ingress = staged_invoke(
        grant.host,
        grant.socket,
        &config,
        directory,
        "ingress",
        ASSEMBLE_OPERATION,
        &pair(plan, &signature)?,
    )?;
    let view = inspect(
        grant.host,
        grant.socket,
        &config,
        INGRESS_KIND,
        &directory.join("ingress.bin"),
        &directory.join("ingress.json"),
    )?;
    if field(&view, "type")? != "participant-factory-provisioning-ingress-v1"
        || field(&view, "canonical")? != hex(&ingress)
        || field(&view, "commandBytes")? != hex(command)
    {
        return Err("provisioning assembled ingress differs from signed exact Plan".into());
    }
    save_json_staged(
        &directory.join("seal.json"),
        &json!({"format":FORMAT,"planSha256":digest(plan),"commandSha256":digest(command),
            "ingressSha256":digest(&ingress),"sponsorSignatureSha256":digest(&signature)}),
    )?;
    Ok(ingress)
}

fn outcome(grant: &ObserveGrant<'_>, stem: &str, frame: &[u8], operation: u8) -> Result<Value> {
    let directory = grant.directory;
    let config = directory.join("config.json");
    retain_exact(&directory.join(format!("{stem}.frame")), frame)?;
    let body = match frame {
        [actual, body @ ..] if *actual == operation && !body.is_empty() => body,
        _ => {
            return Err(format!(
                "provisioning op{operation} was refused; frame retained"
            ))
        }
    };
    retain_exact(&directory.join(format!("{stem}.bin")), body)?;
    inspect(
        grant.host,
        grant.socket,
        &config,
        "outcome",
        &directory.join(format!("{stem}.bin")),
        &directory.join(format!("{stem}.json")),
    )
}

fn result(grant: &ObserveGrant<'_>, capability: &str, receipt: &Value) -> Result<Value> {
    confirmed(receipt)?;
    let value = json!({"type":"minidregg-participant-factory-observation-result-v1",
        "holder":grant.holder,"factory":grant.factory,"capability":capability,
        "verbs":["observe"],
        "receipt":{"transactionId":field(receipt,"transactionId")?,
            "eventId":field(receipt,"eventId")?,
            "acceptedCount":field(receipt,"acceptedCount")?,
            "imageBoundary":field(receipt,"imageBoundary")?},
        "authority":"admitted-factory-observation"});
    let path = grant.directory.join("result.json");
    if path.exists() {
        if json_private(&path)? != value {
            return Err("prior provisioning result differs from exact receipt".into());
        }
    } else {
        save_json(&path, &value)?;
    }
    Ok(value)
}

fn lookup_exact(grant: &ObserveGrant<'_>, capability: &str, ingress: &[u8]) -> Result<Value> {
    let count = fs::read_dir(grant.directory)
        .map_err(|error| error.to_string())?
        .filter_map(|entry| entry.ok())
        .filter(|entry| {
            let name = entry.file_name().to_string_lossy().into_owned();
            name.starts_with("lookup-") && name.ends_with(".frame")
        })
        .count();
    let frame = session_invoke(
        grant.host,
        grant.socket,
        &grant.directory.join("config.json"),
        LOOKUP_OPERATION,
        ingress,
    )?;
    let value = outcome(
        grant,
        &format!("lookup-{count:04}"),
        &frame,
        LOOKUP_OPERATION,
    )?;
    result(grant, capability, &value)
}

fn generations(directory: &Path) -> Result<Vec<PathBuf>> {
    let mut numbers = Vec::new();
    for entry in fs::read_dir(directory).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        let name = entry.file_name().to_string_lossy().into_owned();
        if let Some(digits) = name.strip_prefix('g') {
            if digits.len() == 4 && digits.bytes().all(|byte| byte.is_ascii_digit()) {
                numbers.push(digits.parse::<u32>().map_err(|error| error.to_string())?);
            }
        }
    }
    numbers.sort_unstable();
    if numbers
        .iter()
        .enumerate()
        .any(|(index, number)| *number != index as u32 + 1)
    {
        return Err("provisioning generations are not contiguous".into());
    }
    Ok(numbers
        .into_iter()
        .map(|number| directory.join(format!("g{number:04}")))
        .collect())
}

fn new_generation(directory: &Path, count: usize) -> Result<PathBuf> {
    let next = directory.join(format!("g{:04}", count + 1));
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&next)
        .map_err(|error| format!("cannot create provisioning generation: {error}"))?;
    sync_directory_ancestors(directory)?;
    Ok(next)
}

fn sealed(generation: &Path) -> Result<(Vec<u8>, Vec<u8>, Vec<u8>)> {
    let command = private_bytes(&generation.join("command.bin"), LIMIT)?;
    let plan = private_bytes(&generation.join("plan.bin"), LIMIT)?;
    let seal = json_private(&generation.join("seal.json"))?;
    pinned(&seal, "format", FORMAT)?;
    pinned(&seal, "planSha256", &digest(&plan))?;
    pinned(&seal, "commandSha256", &digest(&command))?;
    let ingress = private_bytes(&generation.join("ingress.bin"), LIMIT)?;
    pinned(&seal, "ingressSha256", &digest(&ingress))?;
    Ok((command, plan, ingress))
}

/// Plan, seal and submit once; after a possible submission only the exact
/// retained ingress is looked up. Before any submission, a generation whose
/// retained Plan the Host no longer derives (a stale observation) is superseded
/// once per call by a new generation of the same request. Re-running resumes.
pub(crate) fn observe_grant(grant: &ObserveGrant<'_>) -> Result<Value> {
    decimal(grant.holder, "provisioning holder")?;
    match fs::DirBuilder::new().mode(0o700).create(grant.directory) {
        Ok(()) => (),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            drain::private_dir(grant.directory)?;
        }
        Err(error) => return Err(format!("cannot create provisioning attempt: {error}")),
    }
    sync_directory_ancestors(grant.directory)?;
    let _lock = transport::service_lock(&grant.directory.join("provision.lock"))?;
    if grant.directory.join("result.json").exists() {
        return json_private(&grant.directory.join("result.json"));
    }
    let (request, reserved) = record(grant)?;
    let capability = reserved.ids["capability"].clone();
    let marker = grant.directory.join("submit-marker.json");
    if marker.exists() {
        let prior = json_private(&marker)?;
        let generation = PathBuf::from(field(&prior, "generation")?);
        let (_, _, ingress) = sealed(&generation)?;
        pinned(&prior, "ingressSha256", &digest(&ingress))?;
        return lookup_exact(grant, &capability, &ingress);
    }
    let mut existing = generations(grant.directory)?;
    let mut superseded = false;
    let generation = loop {
        let current = match existing.last() {
            Some(current) => current.clone(),
            None => new_generation(grant.directory, 0)?,
        };
        drain::private_dir(&current)?;
        if current.join("seal.json").exists() {
            break current;
        }
        let retained_plan = current.join("plan.frame").exists();
        match plan(grant, &request, &capability, &current) {
            Ok(_) => break current,
            Err(error) if retained_plan && !superseded => {
                eprintln!(
                    "provisioning generation {} is stale ({error}); authoring the same request anew",
                    current.display()
                );
                existing.push(new_generation(grant.directory, existing.len())?);
                superseded = true;
            }
            Err(error) => return Err(error),
        }
    };
    let ingress = if generation.join("seal.json").exists() {
        sealed(&generation)?.2
    } else {
        let command = private_bytes(&generation.join("command.bin"), LIMIT)?;
        let plan = private_bytes(&generation.join("plan.bin"), LIMIT)?;
        seal(grant, &generation, &command, &plan)?
    };
    save_json(
        &marker,
        &json!({"format":FORMAT,"operation":SUBMIT_OPERATION,"generation":generation,
            "ingressSha256":digest(&ingress),"status":"may-have-submitted"}),
    )?;
    match session_invoke(
        grant.host,
        grant.socket,
        &grant.directory.join("config.json"),
        SUBMIT_OPERATION,
        &ingress,
    ) {
        Ok(frame) => {
            let value = outcome(grant, "submit", &frame, SUBMIT_OPERATION)?;
            if confirmed(&value).is_ok() {
                return result(grant, &capability, &value);
            }
            lookup_exact(grant, &capability, &ingress)
        }
        Err(_) => lookup_exact(grant, &capability, &ingress),
    }
}

/// Receipt-only replay of an already sealed and possibly submitted grant.
pub(crate) fn observe_lookup(grant: &ObserveGrant<'_>) -> Result<Value> {
    let _lock = transport::service_lock(&grant.directory.join("provision.lock"))?;
    let marker = grant.directory.join("submit-marker.json");
    if !marker.exists() {
        return Err("provisioning has no submitted or uncertain attempt".into());
    }
    let prior_marker = json_private(&marker)?;
    let (_, _, ingress) = sealed(&PathBuf::from(field(&prior_marker, "generation")?))?;
    pinned(&prior_marker, "ingressSha256", &digest(&ingress))?;
    let prior = json_private(&grant.directory.join("result.json"))?;
    let value = {
        let count = fs::read_dir(grant.directory)
            .map_err(|error| error.to_string())?
            .filter_map(|entry| entry.ok())
            .filter(|entry| {
                let name = entry.file_name().to_string_lossy().into_owned();
                name.starts_with("lookup-") && name.ends_with(".frame")
            })
            .count();
        let frame = session_invoke(
            grant.host,
            grant.socket,
            &grant.directory.join("config.json"),
            LOOKUP_OPERATION,
            &ingress,
        )?;
        outcome(
            grant,
            &format!("lookup-{count:04}"),
            &frame,
            LOOKUP_OPERATION,
        )?
    };
    confirmed(&value)?;
    if prior["receipt"]["transactionId"] != value["transactionId"]
        || prior["receipt"]["eventId"] != value["eventId"]
        || prior["receipt"]["acceptedCount"] != value["acceptedCount"]
    {
        return Err("historical provisioning lookup differs from retained result".into());
    }
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plan_view_must_name_the_exact_command_and_one_decoded_header() {
        let command = [1u8, 2];
        let plan = [3u8, 4];
        let good = json!({"type":"participant-factory-provisioning-plan-v1",
            "canonical":hex(&plan),"commandBytes":hex(&command),
            "sponsorHeader":{"decoded":true,"canonical":"ab"}});
        validate_plan(&good, &command, &plan).unwrap();
        let mut other = good.clone();
        other["commandBytes"] = json!(hex(&[9u8]));
        assert!(validate_plan(&other, &command, &plan).is_err());
        let mut undecoded = good.clone();
        undecoded["sponsorHeader"]["decoded"] = json!(false);
        assert!(validate_plan(&undecoded, &command, &plan).is_err());
        let mut enrollment = good;
        enrollment["type"] = json!("participant-key-enrollment-plan-v1");
        assert!(validate_plan(&enrollment, &command, &plan).is_err());
    }

    #[test]
    fn refused_or_malformed_frames_never_become_outcomes() {
        let root = std::env::temp_dir().join(format!(
            "mini-provision-frame-{}-{}",
            std::process::id(),
            nonce().unwrap()
        ));
        fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
        let grant = ObserveGrant {
            host: Path::new("/missing"),
            config: Path::new("/missing"),
            socket: Path::new("/missing"),
            sponsor_key: Path::new("/missing"),
            namespace_root: Path::new("/missing"),
            domain: "1",
            name: "n",
            sponsor: "7",
            control: "53",
            observe: "54",
            factory: "10",
            holder: "9",
            directory: &root,
        };
        assert!(outcome(&grant, "submit", &[255, 1, 2], SUBMIT_OPERATION).is_err());
        assert!(outcome(
            &grant,
            "lookup-0000",
            &[SUBMIT_OPERATION, 1],
            LOOKUP_OPERATION
        )
        .is_err());
        assert_eq!(fs::read(root.join("submit.frame")).unwrap(), [255, 1, 2]);
        assert!(!root.join("submit.bin").exists());
        fs::remove_dir_all(root).unwrap();
    }
}
