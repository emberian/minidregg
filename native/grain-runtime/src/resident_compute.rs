//! Sandbox CPU paid as room turns (docs/HERMES-TOOLS-2026-10-27.md §5).
//!
//! Before a resident prompt that the controller will grant sandbox tools is
//! sent, `intend` retains the prompt's identity and block size. Once the
//! prompt is decided (completed, refused or failed), `settle` reads the launch
//! gate's CPU record for that prompt's worker unit, fixes the turn count in
//! `compute-OP.json`, and pays each turn through `RoomTools::pay` under its own
//! exact operation (`cOP-I`), so a rerun looks a sent payment up and never pays
//! twice. A worker the gate started but left no record for is charged as its
//! whole wall time at the CPU quota; a worker never started costs nothing.
use crate::*;

const INTENT: &str = "compute-intent.json";

/// The block size for a prompt: the room's `hermes/compute` when set, never
/// larger than the operator's (a founder can only make compute dearer).
pub(crate) fn seconds_per_turn(sandbox: &sandbox_tools::Sandbox, prompt: &str) -> u64 {
    let room = serde_json::from_str::<Value>(prompt.strip_prefix(room_resident::ASSIGNMENT_PREFIX).unwrap_or(""))
        .ok().and_then(|a| a.get("sandboxCompute").and_then(Value::as_u64)).unwrap_or(0);
    if room == 0 { sandbox.compute_seconds_per_turn } else { room.min(sandbox.compute_seconds_per_turn) }
}

/// Retain the intent before the prompt is sent; nothing when no sandbox
/// toolset is granted.
pub(crate) fn intend(config: &Config, state: &Path, resident_prompt_id: &str, prompt: &str) -> Result<()> {
    let Some(sandbox) = &config.sandbox else { return Ok(()) };
    if sandbox.grant(Some(prompt)).is_empty() { return Ok(()); }
    let wall = config.commands.iter().find(|c| c.name == "hermes-acp")
        .and_then(|c| c.wall_time_seconds).unwrap_or(600);
    atomic_json(&state.join(INTENT), &json!({"type":"mini-resident-compute-intent-v1",
        "residentPromptId":resident_prompt_id,"secondsPerTurn":seconds_per_turn(sandbox, prompt),
        "pessimisticUsec":wall.saturating_mul(sandbox.cpu_quota_percent).saturating_mul(10_000)}))
}

/// Fix and pay the compute turns of the decided prompt `completion` names.
/// Returns the turns still owed (0 when settled or nothing was intended).
pub(crate) fn settle(config: &Config, room: &resource_tools::RoomToolsConfig, state: &Path, completion: Option<&Value>) -> Result<u64> {
    let intent_path = state.join(INTENT);
    if intent_path.exists() {
        let intent: Value = serde_json::from_slice(&bounded_regular_file(&intent_path, 4096)?).map_err(|e| e.to_string())?;
        match completion {
            Some(frame) if frame["residentOrigin"]["residentPromptId"] == intent["residentPromptId"] => {
                let op = frame["residentOrigin"]["promptOperationId"].as_u64().ok_or("compute: completion has no prompt operation")?;
                let unit = format!("mini-grain-t{}-o{op}", config.task);
                let usec = match sandbox_tools::recorded_cpu_usec(&config.state_dir, &unit)? {
                    Some(usec) => usec,
                    None if worker_started(&config.state_dir, &unit)? => intent["pessimisticUsec"].as_u64().unwrap_or(u64::MAX),
                    None => 0,
                };
                let turns = sandbox_tools::compute_turns(usec, intent["secondsPerTurn"].as_u64().unwrap_or(1));
                let ledger = state.join(format!("compute-{op:016}.json"));
                if !ledger.exists() {
                    atomic_json(&ledger, &json!({"type":"mini-resident-compute-v1","promptOperationId":op,
                        "unit":unit,"usec":usec,"secondsPerTurn":intent["secondsPerTurn"],"turns":turns,"paid":0}))?;
                }
                fs::remove_file(&intent_path).map_err(|e| e.to_string())?;
            }
            // A preadmission refusal, or a frame for another prompt: no worker of
            // this intent ran under its identity.
            Some(frame) if frame["type"] == "mini-resident-prompt-preadmission-refused-v1" => {
                fs::remove_file(&intent_path).map_err(|e| e.to_string())?;
            }
            _ => {}
        }
    }
    let mut owed = 0;
    for entry in fs::read_dir(state).map_err(|e| e.to_string())? {
        let path = entry.map_err(|e| e.to_string())?.path();
        let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if name.starts_with("compute-") && name.ends_with(".json") && name != INTENT {
            owed += pay(room, &path)?;
        }
    }
    Ok(owed)
}

fn worker_started(state_dir: &Path, unit: &str) -> Result<bool> {
    let gate = state_dir.join(format!("{unit}.gate"));
    if !gate.exists() { return Ok(false); }
    let text = String::from_utf8_lossy(&bounded_regular_file(&gate, 1024)?).into_owned();
    Ok(!text.starts_with("armed"))
}

fn pay(room: &resource_tools::RoomToolsConfig, ledger: &Path) -> Result<u64> {
    let mut record: Value = serde_json::from_slice(&bounded_regular_file(ledger, 4096)?).map_err(|e| e.to_string())?;
    let op = record["promptOperationId"].as_u64().ok_or("compute ledger has no operation")?;
    let turns = record["turns"].as_u64().ok_or("compute ledger has no turn count")?;
    let tools = resource_tools::RoomTools { config: room };
    while record["paid"].as_u64().unwrap_or(0) < turns {
        let i = record["paid"].as_u64().unwrap_or(0);
        let payment = format!("c{op}-{i}");
        match tools.pay(&payment, "compute") {
            Ok(_) => {}
            Err(error) => match tools.lookup_operation(&payment, "payment") {
                Ok(lookup) if lookup["resolution"] == "performed" => {}
                // The payment never reached the Host: the exact operation is retried (the Host dedups on its
                // operation record), it is not a refusal.
                Ok(lookup) if lookup["resolution"] == "not-submitted" => {
                    tools.pay(&payment, "compute").map_err(|retry| format!("compute turn {payment}: not submitted, exact retry: {retry}"))?;
                }
                Ok(lookup) => return Err(format!("compute turn {payment}: {error}; {}", lookup["resolution"])),
                Err(lookup) => return Err(format!("compute turn {payment}: {error}; lookup {lookup}")),
            },
        }
        record["paid"] = json!(i + 1);
        atomic_json(ledger, &record)?;
    }
    Ok(0)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn prompt(compute: u64) -> String {
        format!("{}{}", room_resident::ASSIGNMENT_PREFIX, json!({"sandboxTools":7,"sandboxCompute":compute}))
    }
    #[test]
    fn a_founder_can_only_make_compute_dearer() {
        let sandbox = sandbox_tools::Sandbox::for_class("M").unwrap();
        assert_eq!(seconds_per_turn(&sandbox, &prompt(0)), 10, "unset: the operator's block");
        assert_eq!(seconds_per_turn(&sandbox, &prompt(5)), 5);
        assert_eq!(seconds_per_turn(&sandbox, &prompt(60)), 10, "a larger block than the operator's is refused");
    }
    #[test]
    fn a_started_worker_without_a_record_is_charged_and_an_unstarted_one_is_not() {
        let dir = std::env::temp_dir().join(format!("resident-compute-{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        assert!(!worker_started(&dir, "mini-grain-t7-o3").unwrap());
        fs::write(dir.join("mini-grain-t7-o3.gate"), "armed\n").unwrap();
        assert!(!worker_started(&dir, "mini-grain-t7-o3").unwrap());
        fs::write(dir.join("mini-grain-t7-o3.gate"), "started\n").unwrap();
        assert!(worker_started(&dir, "mini-grain-t7-o3").unwrap());
        fs::remove_dir_all(dir).unwrap();
    }
}
