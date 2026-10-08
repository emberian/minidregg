//! The operator checks retained settled pauses before the typed helper copies volumes.
use super::*;
use crate::checkpoint_control::{Intent, Request as PauseRequest};
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Inventory {
    protocol: String,
    apps: Vec<AppPause>,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct AppPause {
    store: String,
    request: PauseRequest,
}
struct Checked {
    pins: Value,
    locks: Vec<File>,
}
fn op_bytes(broker: &Broker, parts: &[&str]) -> io::Result<Vec<u8>> {
    let mut file = open_operator_file(broker.root(), parts, broker.operator_uid)?;
    if file.metadata()?.len() > 1024 * 1024 {
        return Err(invalid("checkpoint custody file exceeds bound"));
    }
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)?;
    Ok(bytes)
}
fn checked(broker: &Broker, input: &Path) -> io::Result<Checked> {
    if !input.is_absolute()
        || input.components().any(|part| {
            matches!(
                part,
                std::path::Component::ParentDir | std::path::Component::CurDir
            )
        })
    {
        return Err(invalid("checkpoint inventory path invalid"));
    }
    for parent in input.ancestors().skip(1) {
        let meta = fs::symlink_metadata(parent)?;
        if !meta.is_dir()
            || ![0, broker.operator_uid].contains(&meta.uid())
            || meta.mode() & 0o022 != 0
        {
            return Err(invalid("checkpoint inventory ancestry invalid"));
        }
    }
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(input)?;
    let meta = file.metadata()?;
    if !meta.is_file()
        || meta.nlink() != 1
        || ![0, broker.operator_uid].contains(&meta.uid())
        || meta.mode() & 0o077 != 0
        || meta.len() > 65536
    {
        return Err(invalid("checkpoint inventory custody invalid"));
    }
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)?;
    let inventory: Inventory = serde_json::from_slice(&bytes)?;
    if inventory.protocol != "mini-spk-checkpoint-pause-inventory-v1" || inventory.apps.len() > 256
    {
        return Err(invalid("checkpoint inventory protocol or capacity invalid"));
    }
    let mut locks = Vec::new();
    let mut pins = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for entry in inventory.apps {
        let request = entry.request;
        let b = &request.binding;
        if !store_key(&entry.store)
            || !decimal(&b.app)
            || !decimal(&b.generation)
            || request.protocol != "mini-spk-checkpoint-control-v1"
            || request.action != "pause"
            || !(request.nonce_hex.len() == 64
                && request
                    .nonce_hex
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)))
        {
            return Err(invalid("checkpoint pause selector invalid"));
        }
        if !seen.insert((entry.store.clone(), b.app.clone())) {
            return Err(invalid("checkpoint app repeated"));
        }
        let gen = format!("g{}", b.generation);
        let base = [entry.store.as_str(), "host", "apps", b.app.as_str()];
        let journal = broker
            .root()
            .join(&entry.store)
            .join("host/apps")
            .join(&b.app)
            .join(&gen);
        if b.journal_dir != journal || b.resident_config != journal.join("resident.json") {
            return Err(invalid("checkpoint journal coordinate differs"));
        }
        let lock = open_operator_file(
            broker.root(),
            &[base[0], base[1], base[2], base[3], ".checkpoint.lock"],
            broker.operator_uid,
        )?;
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
            return Err(invalid("checkpoint pause or resume active"));
        }
        let pause = op_bytes(
            broker,
            &[base[0], base[1], base[2], base[3], "checkpoint-pause.json"],
        )?;
        let intent: Intent = serde_json::from_slice(&pause)?;
        if intent.request != request {
            return Err(invalid("checkpoint retained pause differs"));
        }
        let receipt_name = format!("checkpoint-{}-pause.json", request.nonce_hex);
        if op_bytes(
            broker,
            &[base[0], base[1], base[2], base[3], &gen, &receipt_name],
        )? != pause
        {
            return Err(invalid(
                "checkpoint complete pause receipt absent or different",
            ));
        }
        let resident_bytes = op_bytes(
            broker,
            &[base[0], base[1], base[2], base[3], &gen, "resident.json"],
        )?;
        let resident: Value = serde_json::from_slice(&resident_bytes)?;
        let record_bytes = op_bytes(
            broker,
            &[base[0], base[1], base[2], base[3], &gen, "record.json"],
        )?;
        let record: crate::hostd::Record = serde_json::from_slice(&record_bytes)?;
        let unit = resident_unit(&entry.store, &b.app, &b.generation)?;
        if format!("{:x}", Sha256::digest(&resident_bytes)) != b.resident_config_sha256
            || format!("{:x}", Sha256::digest(&record_bytes)) != intent.journal_sha256
            || resident["miniConfigSha256"] != b.mini_config_sha256
            || resident["store"] != entry.store
            || resident["unit"] != unit
            || resident["grainsRoot"] != broker.root().to_string_lossy().as_ref()
            || record.app().to_string() != b.app
            || record.generation().to_string() != b.generation
            || record.phase != crate::hostd::Phase::Running
        {
            return Err(invalid(
                "checkpoint resident or physical journal pin differs",
            ));
        }
        record.verify_running_instance()?;
        let active = broker.app_units_active(&entry.store, &b.app)?;
        if active != vec![unit.clone()] {
            return Err(invalid("checkpoint active incarnation differs"));
        }
        pins.push(json!({"store":entry.store,"app":b.app,"generation":b.generation,"unit":unit,"intent":intent,"pauseSha256":format!("{:x}",Sha256::digest(&pause))}));
        locks.push(lock);
    }
    // Every running registered app must be paused. Stopped apps remain covered
    // by the original exact stopped-volume path.
    for volume in crate::volume_helper::volumes_status(&broker.config.volume_helper,&broker.config.store)? {
            if !volume.settled {return Err(invalid("checkpoint volume has unresolved freeze obligation"));}
            let store=volume.request.store.as_str();
            let app=volume.request.grain.as_str();
            if !broker.app_units_active(store, app)?.is_empty()
                && !seen.contains(&(store.into(), app.into()))
            {
                return Err(invalid(
                    "running app lacks a complete settled checkpoint pause",
                ));
            }
    }
    let units: Vec<_> = pins.iter().map(|pin| pin["unit"].clone()).collect();
    Ok(Checked {
        pins: json!({"protocol":"mini-spk-checkpoint-pause-check-v1","activePausedUnits":units,"pausePins":pins,"inventorySha256":format!("{:x}",Sha256::digest(&bytes))}),
        locks,
    })
}
pub(super) fn check(config: &Path, input: &Path) -> io::Result<Value> {
    if unsafe { libc::geteuid() } == 0 {
        return Err(invalid("checkpoint check requires the unprivileged operator"));
    }
    let broker = Broker::load(config)?;
    let checked = checked(&broker, input)?;
    Ok(checked.pins)
}
pub(super) fn backup(config: &Path, out: &Path, input: &Path) -> io::Result<Value> {
    if unsafe { libc::geteuid() } == 0 {
        return Err(invalid("checkpoint backup requires the unprivileged operator"));
    }
    let broker = Broker::load(config)?;
    let checked = checked(&broker, input)?;
    let mut manifest = broker.backup_into(out)?;
    for grain in manifest["grains"]
        .as_array_mut()
        .ok_or_else(|| invalid("backup grains absent"))?
    {
        if grain["state"] == "running-frozen-crash-consistent" {
            let pin = checked.pins["pausePins"]
                .as_array()
                .and_then(|pins| {
                    pins.iter()
                        .find(|pin| pin["app"] == grain["app"] && pin["store"] == grain["store"])
                })
                .ok_or_else(|| invalid("backup active app pause pin missing"))?;
            grain["state"] = json!("paused-frozen-crash-consistent");
            grain["checkpointPause"] = pin.clone();
        }
    }
    manifest["checkpointPauseCheck"] = checked.pins;
    write_operator_text(
        &out.join("checkpoint-grains-backup.json"),
        &serde_json::to_string_pretty(&manifest)?,
        0o600,
        false,
    )?;
    // All app pause/resume locks span fsfreeze/copy/thaw and manifest publication.
    drop(checked.locks);
    Ok(manifest)
}
