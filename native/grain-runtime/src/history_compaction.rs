//! Journal retention for a room resident's controller (deploy/hermes/README.md
//! "One uid per resident"). Each decided operation leaves a directory of small
//! files (`attempt-N/`, `query-N/`, `provider-meter-N/`, `source-N.json`, the
//! provider request files, ...): about 3.8 MiB allocated and 780 inodes per
//! paid model call on J14. Once the journal retains no work at all (the
//! quiescence census is empty), operations below `nextOperationId` are
//! decided, but retained birth/publication/dispatch records still verify their
//! exact evidence. Compaction preserves those referenced operation groups, then
//! appends one line per operation to `history.jsonl` (its file names, the
//! exact attempt outcome, the source digest) and only after that line is
//! durable removes the operation's files. The outcome is what an exact
//! lookup of the decided transaction needs ([`retained_outcome`]); retry is
//! only ever of retained work, which the census keeps out of compaction.
use crate::*;
use std::io::Write;
use std::os::unix::fs::OpenOptionsExt;

pub(crate) const HISTORY: &str = "history.jsonl";

/// Per-operation entries of the controller's state directory, longest
/// prefix first (`provider-` also prefixes `provider-meter-`).
const PER_OPERATION: &[&str] = &[
    "provider-continuity-", "provider-meter-", "policy-attempt-", "policy-source-", "policy-query-",
    "policy-check-", "current-author-", "provider-", "attempt-", "source-", "query-",
];

fn operation_of(name: &str) -> Option<u64> {
    let prefix = PER_OPERATION.iter().find(|p| name.starts_with(**p))?;
    let digits = name.get(prefix.len()..prefix.len() + 16)?;
    if !digits.bytes().all(|b| b.is_ascii_digit()) { return None; }
    let rest = &name[prefix.len() + 16..];
    (rest.is_empty() || rest.starts_with('.')).then(|| digits.parse().ok()).flatten()
}

/// Nothing is retained: no pending, held, attempted, owned, uncertain or
/// unresolved work, and no provider retry gate.
pub(crate) fn quiescent(journal: &Journal) -> bool {
    quiescence::retained(journal, quiescence::ResidentEvidence::NotConfigured)
        .iter().all(|field| *field == "connection_fenced")
        && journal.provider_retry_gate.is_none()
}

/// The first operation whose files stay even when quiescent: the latest
/// provider settlement (the next model call's continuity anchor, which names
/// its provider attempt and settle directories) and the current resident
/// prompt's origin are kept with everything after them.
fn keep_from(journal: &Journal) -> u64 {
    let mut keep = journal.next_operation_id;
    if let Some(s) = &journal.provider_settlement {
        keep = keep.min(s.provider_attempt_id).min(s.operation_id);
    }
    if let Some(o) = &journal.resident_prompt_origin {
        keep = keep.min(o.prompt_operation_id);
    }
    keep
}

/// Decided does not mean unreferenced. A retained receipt's attempt also needs
/// its source/query/current-author siblings for exact verification. Collect all
/// journal paths, including nested settlement and replay records, and retain
/// their operation group without pinning every later operation behind a birth.
fn referenced_evidence(journal: &Journal, state: &Path) -> Result<(std::collections::BTreeSet<u64>, std::collections::BTreeSet<PathBuf>)> {
    fn visit(value: &Value, state: &Path, operations: &mut std::collections::BTreeSet<u64>, paths: &mut std::collections::BTreeSet<PathBuf>) {
        match value {
            Value::String(text) => {
                let path = Path::new(text);
                let Ok(relative) = path.strip_prefix(state) else { return };
                if let Some(name) = relative.components().next().and_then(|p| p.as_os_str().to_str()) {
                    if let Some(id) = operation_of(name) { operations.insert(id); }
                }
                for ancestor in path.ancestors().take_while(|p| *p != state) {
                    paths.insert(ancestor.to_owned());
                }
            }
            Value::Array(values) => for value in values { visit(value, state, operations, paths); },
            Value::Object(values) => for value in values.values() { visit(value, state, operations, paths); },
            _ => {}
        }
    }
    let (mut operations, mut paths) = (std::collections::BTreeSet::new(), std::collections::BTreeSet::new());
    visit(&serde_json::to_value(journal).map_err(|e| e.to_string())?, state, &mut operations, &mut paths);
    Ok((operations, paths))
}

fn outcome(path: &Path) -> Value {
    bounded_regular_file(path, 131_072).ok()
        .and_then(|bytes| serde_json::from_slice(&bytes).ok()).unwrap_or(Value::Null)
}

/// Every attempt directory a room write record names
/// (`WORKSPACE/room-operations/*.json`, `HOME/requests/*.json`).
fn referenced_attempts(workspace: &Path, homes: &[&Path]) -> Result<std::collections::BTreeSet<PathBuf>> {
    let mut out = std::collections::BTreeSet::new();
    let mut dirs = vec![workspace.join("room-operations")];
    dirs.extend(homes.iter().map(|h| h.join("requests")));
    for dir in dirs {
        let Ok(listing) = fs::read_dir(&dir) else { continue };
        for entry in listing {
            let path = entry.map_err(|e| e.to_string())?.path();
            if path.extension().and_then(|e| e.to_str()) != Some("json") { continue; }
            let Ok(bytes) = bounded_regular_file(&path, 1 << 20) else { continue };
            if let Ok(value) = serde_json::from_slice::<Value>(&bytes) {
                if let Some(a) = value["attempt"].as_str() { out.insert(PathBuf::from(a)); }
            }
        }
    }
    Ok(out)
}

fn remove(path: &Path) -> Result<()> {
    let meta = fs::symlink_metadata(path).map_err(|e| format!("{}: {e}", path.display()))?;
    if meta.is_dir() { fs::remove_dir_all(path) } else { fs::remove_file(path) }
        .map_err(|e| format!("remove {}: {e}", path.display()))
}

#[derive(Debug, Default, PartialEq)]
pub(crate) struct Summary { pub operations: usize, pub workspace_attempts: usize, pub transient: usize, pub entries: usize }

/// Superseded signed reads: `HOME/chat/reads/ROOM/LABEL.NONCE` keeps only the
/// newest entry per label (the room as last read, which `chat` renders
/// offline); one-shot query sources `WORKSPACE/sources/q-NONCE.json` are named
/// by a random nonce no later command asks for.
fn transient(homes: &[&Path], workspaces: &[&Path]) -> Result<Vec<PathBuf>> {
    let mut doomed = Vec::new();
    for home in homes {
        let Ok(rooms) = fs::read_dir(home.join("chat/reads")) else { continue };
        for room in rooms {
            let room = room.map_err(|e| e.to_string())?.path();
            if !room.is_dir() { continue; }
            let mut by_label: BTreeMap<String, Vec<(std::time::SystemTime, PathBuf)>> = BTreeMap::new();
            for entry in fs::read_dir(&room).map_err(|e| e.to_string())? {
                let entry = entry.map_err(|e| e.to_string())?;
                let name = entry.file_name().to_string_lossy().into_owned();
                let Some((label, _)) = name.split_once('.') else { continue };
                let modified = fs::symlink_metadata(entry.path()).and_then(|m| m.modified()).map_err(|e| e.to_string())?;
                by_label.entry(label.to_owned()).or_default().push((modified, entry.path()));
            }
            for (_, mut reads) in by_label {
                reads.sort();
                reads.pop();
                doomed.extend(reads.into_iter().map(|(_, p)| p));
            }
        }
    }
    for workspace in workspaces {
        let Ok(sources) = fs::read_dir(workspace.join("sources")) else { continue };
        for entry in sources {
            let entry = entry.map_err(|e| e.to_string())?;
            let name = entry.file_name().to_string_lossy().into_owned();
            if name.starts_with("q-") && name.ends_with(".json") { doomed.push(entry.path()); }
        }
    }
    Ok(doomed)
}

/// Compact the decided history of `state` (and of each room workspace's
/// `attempts/`). A no-op unless the journal is quiescent.
pub(crate) fn compact(journal: &Journal, state: &Path, workspaces: &[&Path], homes: &[&Path]) -> Result<Option<Summary>> {
    if !quiescent(journal) { return Ok(None); }
    let end = keep_from(journal);
    let (referenced_operations, referenced_paths) = referenced_evidence(journal, state)?;
    let mut groups: BTreeMap<u64, Vec<String>> = BTreeMap::new();
    for entry in fs::read_dir(state).map_err(|e| format!("state: {e}"))? {
        let name = entry.map_err(|e| e.to_string())?.file_name();
        let Some(name) = name.to_str() else { continue };
        if let Some(id) = operation_of(name).filter(|id| *id < end && !referenced_operations.contains(id)) {
            groups.entry(id).or_default().push(name.to_owned());
        }
    }
    let mut lines = Vec::new();
    let mut doomed = Vec::new();
    let mut summary = Summary::default();
    for (id, mut names) in groups {
        names.sort();
        let attempt = state.join(format!("attempt-{id:016}"));
        let source = state.join(format!("source-{id:016}.json"));
        lines.push(json!({"id":id.to_string(),"entries":names,
            "outcome":outcome(&attempt.join("outcome.json")),
            "sourceSha256":sha256_file(&source).ok()}));
        summary.operations += 1;
        summary.entries += names.len();
        doomed.extend(names.iter().map(|n| state.join(n)));
    }
    for workspace in workspaces {
        let attempts = workspace.join("attempts");
        let Ok(listing) = fs::read_dir(&attempts) else { continue };
        // Room write records (RoomTools::lookup) name their attempt
        // directories; those stay whatever they hold.
        let referenced = referenced_attempts(workspace, homes)?;
        for entry in listing {
            let entry = entry.map_err(|e| e.to_string())?;
            let path = entry.path();
            if referenced.contains(&path) || referenced_paths.contains(&path) { continue; }
            // A decided attempt (its outcome or result); a finished signed read
            // (its view, or the Host's refusal of the read or of a proposal before
            // any submission) with no call or submission of any kind; or a local
            // render (a document, its context or transclusions) that never signed
            // an intent for the Host.
            let has = |f: &str| path.join(f).exists();
            let decided = path.join("outcome.json").is_file() || path.join("result.json").is_file();
            let host = ["call.bin", "submit.json", "plan.json", "command.bin", "assembled.bin"].into_iter().any(has);
            let read = !host && ["view.json", "query-refusal.json", "pre-submit-refusal.json"].into_iter().any(has);
            let local = !host && !has("intent.bin")
                && ["document.json", "context.json", "transclusions.json"].into_iter().any(has);
            if !decided && !read && !local { continue; }
            let name = entry.file_name().to_string_lossy().into_owned();
            lines.push(json!({"workspace":workspace,"attempt":name,"outcome":outcome(&path.join("outcome.json"))}));
            summary.workspace_attempts += 1;
            summary.entries += 1;
            doomed.push(path);
        }
    }
    let reads: Vec<_> = transient(homes, workspaces)?.into_iter()
        .filter(|path| !referenced_paths.contains(path)).collect();
    summary.transient = reads.len();
    summary.entries += reads.len();
    for path in reads { remove(&path)?; }
    if lines.is_empty() { return Ok(Some(summary)); }
    let mut bytes = Vec::new();
    for line in &lines {
        bytes.extend(serde_json::to_vec(line).map_err(|e| e.to_string())?);
        bytes.push(b'\n');
    }
    let mut file = fs::OpenOptions::new().create(true).append(true).mode(0o600).open(state.join(HISTORY))
        .map_err(|e| format!("history: {e}"))?;
    file.write_all(&bytes).map_err(|e| format!("history: {e}"))?;
    // A crash between the append and the removals repeats the same lines on
    // the next pass; the records are identical, so a reader takes the first.
    for path in doomed { remove(&path)?; }
    Ok(Some(summary))
}

/// The exact outcome of decided operation `id`: from its attempt directory
/// while it exists, otherwise from its compacted history line.
pub(crate) fn retained_outcome(state: &Path, id: u64) -> Result<Option<Value>> {
    let direct = state.join(format!("attempt-{id:016}/outcome.json"));
    if direct.is_file() {
        return serde_json::from_slice(&bounded_regular_file(&direct, 131_072)?).map(Some).map_err(|e| e.to_string());
    }
    let Ok(text) = fs::read_to_string(state.join(HISTORY)) else { return Ok(None) };
    let id = id.to_string();
    Ok(text.lines().filter_map(|l| serde_json::from_str::<Value>(l).ok())
        .find(|v| v["id"] == id.as_str()).map(|v| v["outcome"].clone()).filter(|v| !v.is_null()))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn dir(tag: &str) -> PathBuf {
        let d = std::env::temp_dir().join(format!("mini-history-{tag}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&d);
        fs::create_dir_all(&d).unwrap();
        d
    }
    fn decided(state: &Path, id: u64) {
        let a = state.join(format!("attempt-{id:016}"));
        fs::create_dir(&a).unwrap();
        for f in ["plan.json", "seal.record", "intent.json"] { fs::write(a.join(f), b"{}").unwrap(); }
        fs::write(a.join("outcome.json"), format!(r#"{{"transactionId":"{id}","confirmation":"installed"}}"#)).unwrap();
        fs::write(state.join(format!("source-{id:016}.json")), b"{\"s\":1}").unwrap();
        let q = state.join(format!("query-{id:016}"));
        fs::create_dir_all(q.join("attempt")).unwrap();
        fs::write(q.join("intent-source.json"), b"{}").unwrap();
        fs::write(state.join(format!("provider-{id:016}.request")), b"x").unwrap();
        fs::write(state.join(format!("provider-meter-{id:016}.metadata.json")), b"{}").unwrap();
    }

    #[test]
    fn decided_history_packs_into_one_line_per_operation_and_lookup_still_finds_the_outcome() {
        let state = dir("pack");
        let ws = state.join("resource-workspace");
        fs::create_dir_all(ws.join("attempts/hr-g2")).unwrap();
        fs::write(ws.join("attempts/hr-g2/outcome.json"), br#"{"transactionId":"w2"}"#).unwrap();
        fs::create_dir_all(ws.join("attempts/undecided")).unwrap();
        fs::create_dir_all(ws.join("attempts/a-write")).unwrap();
        fs::write(ws.join("attempts/a-write/result.json"), b"{}").unwrap();
        fs::create_dir_all(ws.join("room-operations")).unwrap();
        fs::write(ws.join("room-operations/g7-write.json"),
            serde_json::to_vec(&json!({"attempt": ws.join("attempts/a-write")})).unwrap()).unwrap();
        fs::create_dir_all(ws.join("attempts/a-read")).unwrap();
        fs::write(ws.join("attempts/a-read/view.json"), b"{}").unwrap();
        // A read the Host refused, and a local document render: both finished.
        fs::create_dir_all(ws.join("attempts/a-refused-read")).unwrap();
        for f in ["intent.bin", "query-refusal.json"] { fs::write(ws.join("attempts/a-refused-read").join(f), b"{}").unwrap(); }
        fs::create_dir_all(ws.join("attempts/a-render")).unwrap();
        for f in ["context-in.json", "context.json"] { fs::write(ws.join("attempts/a-render").join(f), b"{}").unwrap(); }
        // A proposal with a plan, and an intent signed for a render-named file: neither is a read or a render.
        fs::create_dir_all(ws.join("attempts/a-planned")).unwrap();
        for f in ["plan.json", "document.json"] { fs::write(ws.join("attempts/a-planned").join(f), b"{}").unwrap(); }
        fs::create_dir_all(ws.join("attempts/a-signed")).unwrap();
        for f in ["intent.bin", "document.json"] { fs::write(ws.join("attempts/a-signed").join(f), b"{}").unwrap(); }
        for id in 1..=3 { decided(&state, id); }
        fs::write(state.join("journal.json"), b"{}").unwrap();
        fs::write(state.join("resident-origin-0000000000000002.admitted.json"), b"{}").unwrap();
        let mut journal = Journal::fresh(json!({}));
        journal.next_operation_id = 4;
        let before: Vec<_> = (1..=3).map(|id| retained_outcome(&state, id).unwrap().unwrap()).collect();
        let home = state.join("room-home");
        for name in ["feed.old", "feed.new", "roster.only"] {
            let p = home.join("chat/reads/lab").join(name);
            fs::create_dir_all(&p).unwrap();
            fs::write(p.join("view.bin"), b"v").unwrap();
            std::thread::sleep(std::time::Duration::from_millis(20));
        }
        fs::create_dir_all(ws.join("sources")).unwrap();
        fs::write(ws.join("sources/q-123.json"), b"{}").unwrap();
        fs::write(ws.join("sources/apps-bootstrap.json"), b"{}").unwrap();
        let summary = compact(&journal, &state, &[ws.as_path()], &[home.as_path()]).unwrap().unwrap();
        assert_eq!(summary.transient, 2, "the superseded read and the query source");
        assert!(!home.join("chat/reads/lab/feed.old").exists() && home.join("chat/reads/lab/feed.new").exists()
            && home.join("chat/reads/lab/roster.only").exists());
        assert!(!ws.join("sources/q-123.json").exists() && ws.join("sources/apps-bootstrap.json").exists());
        assert_eq!((summary.operations, summary.workspace_attempts), (3, 4));
        for id in 1..=3u64 {
            assert!(!state.join(format!("attempt-{id:016}")).exists() && !state.join(format!("query-{id:016}")).exists());
            assert_eq!(retained_outcome(&state, id).unwrap().unwrap(), before[id as usize - 1], "exact lookup survives the prune");
        }
        // Kept: the journal, the resident's records, an undecided workspace attempt.
        assert!(state.join("journal.json").exists() && state.join("resident-origin-0000000000000002.admitted.json").exists());
        assert!(ws.join("attempts/undecided").exists() && !ws.join("attempts/hr-g2").exists());
        assert!(ws.join("attempts/a-write").exists(), "a room write record's attempt stays for RoomTools::lookup");
        assert!(!ws.join("attempts/a-read").exists(), "a finished signed read goes");
        assert!(!ws.join("attempts/a-refused-read").exists() && !ws.join("attempts/a-render").exists(),
            "a refused read and a local render go");
        assert!(ws.join("attempts/a-planned").exists() && ws.join("attempts/a-signed").exists(),
            "a planned proposal and a signed intent stay");
        let history = fs::read_to_string(state.join(HISTORY)).unwrap();
        assert_eq!(history.lines().count(), 7);
        // A second pass finds nothing more and changes nothing.
        assert_eq!(compact(&journal, &state, &[ws.as_path()], &[home.as_path()]).unwrap().unwrap(), Summary::default());
        assert_eq!(fs::read_to_string(state.join(HISTORY)).unwrap(), history);
        fs::remove_dir_all(state).unwrap();
    }

    #[test]
    fn retained_work_keeps_everything_so_recovery_and_retry_find_their_attempt() {
        let state = dir("retained");
        for id in 1..=2 { decided(&state, id); }
        let mut journal = Journal::fresh(json!({}));
        journal.next_operation_id = 3;
        journal.pending = Some(Pending { operation_id: 2, operation: "submit".into(),
            attempt: state.join("attempt-0000000000000002"), uncertain: true, publication: None });
        assert_eq!(compact(&journal, &state, &[], &[]).unwrap(), None, "a pending operation blocks compaction");
        assert!(state.join("attempt-0000000000000001").exists() && state.join("attempt-0000000000000002/outcome.json").exists());
        journal.pending = None;
        journal.unresolved_external.push("note".into());
        assert_eq!(compact(&journal, &state, &[], &[]).unwrap(), None, "an unresolved note blocks compaction");
        // Ids at or above nextOperationId are never touched.
        journal.unresolved_external.clear();
        journal.next_operation_id = 2;
        assert_eq!(keep_from(&journal), 2);
        // The current resident prompt and everything after it stay.
        journal.next_operation_id = 3;
        journal.resident_prompt_origin = Some(resident_origin::ResidentPromptOrigin { resident_prompt_id: "a".repeat(64),
            prompt_sha256: "b".repeat(64), prompt_operation_id: 2, session_id: None });
        assert_eq!(keep_from(&journal), 2);
        journal.resident_prompt_origin = None;
        journal.next_operation_id = 2;
        compact(&journal, &state, &[], &[]).unwrap().unwrap();
        assert!(!state.join("attempt-0000000000000001").exists() && state.join("attempt-0000000000000002").exists());
        fs::remove_dir_all(state).unwrap();
    }

    #[test]
    fn compacted_history_preserves_a_births_exact_verification_evidence() {
        // Controlled source/receipt fixture: exercises the actual verifier,
        // not native admission (which the live apps journey checks).
        let (mut rt, root) = crate::publication_refusal_tests::fixture(false, false, false);
        rt.config.tool_task.as_mut().unwrap().allowed_birth_families = vec![serde_json::from_value(json!({
            "name":"page","genesis":{},"template":{},"predicate":{"type":"all","predicates":[]},
            "factoryTarget":"10","factoryObserveCapability":"54","payerAccount":"11","payerCapability":"41","payerObserveCapability":"42",
            "tariffBase":"1","tariffPerBirth":"1","targetStart":"9000","ownerCapabilityStart":"9100","controlCapabilityStart":"9200",
            "maxBirths":2,"maxResultBytes":1024
        })).unwrap()];
        rt.journal = Journal::fresh(json!({}));
        let state = rt.config.state_dir.clone();
        let tool = rt.config.tool_task.as_ref().unwrap();
        let family = &tool.allowed_birth_families[0];
        let view = json!({"authorityRoot":"123","targetRoot":"111","height":"20",
            "worldRoot":"456","grain":{"generation":"1","status":"3","remaining":"97","reserved":"3"}});
        let (source, born) = resource_tools::plan_content_birth(family, tool, &rt.config.task, 31, 0, &view, &view).unwrap();
        let source_path = state.join("source-0000000000000031.json");
        atomic_json(&source_path, &source).unwrap();
        let origin = BirthPending { operation_id:31, family:family.name.clone(), ordinal:0,
            source_sha256:sha256_file(&source_path).unwrap(), born:born.clone(), route:None, born_bundle:vec![],
            selected_application:None, selected_shared:None, authored_intent_sha256:None,
            tool_view:view.clone(), parent_view:view, prompt_operation_id:1, session_id:"session".into(), work_origin:None };
        let attempt = state.join("attempt-0000000000000031"); fs::create_dir(&attempt).unwrap();
        fs::write(attempt.join("call.bin"), b"exact call").unwrap();
        fs::write(attempt.join("outcome.bin"), b"exact outcome").unwrap();
        let outcome = attempt.join("outcome.json");
        atomic_json(&outcome, &json!({"type":"confirmed","confirmation":"installed",
            "transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"})).unwrap();
        let pending = Pending { operation_id:31, operation:"tool birth".into(), attempt,
            uncertain:false, publication:None };
        let record = rt.confirmed_birth_record(&pending, &origin, &outcome).unwrap().unwrap();
        rt.journal.birth_next_ordinal.insert(origin.family.clone(), 1);
        rt.journal.born_resources.push(record);
        rt.journal.next_operation_id = 100;
        assert!(rt.verified_born_target(&born.kind, &born.target).unwrap().is_some());
        let author = state.join("current-author-0000000000000031"); fs::create_dir(&author).unwrap();
        fs::write(author.join("intent.bin"), b"exact authored input").unwrap();
        decided(&state, 32);
        compact(&rt.journal, &state, &[], &[]).unwrap().unwrap();
        assert!(rt.verified_born_target(&born.kind, &born.target).unwrap().is_some());
        assert_eq!(fs::read(author.join("intent.bin")).unwrap(), b"exact authored input");
        assert!(!state.join("source-0000000000000032.json").exists(), "an early birth does not pin unrelated later history");
        fs::write(&source_path, b"changed preimage").unwrap();
        assert!(rt.verified_born_target(&born.kind, &born.target).unwrap_err().contains("source changed"));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn only_canonical_operation_names_are_history() {
        assert_eq!(operation_of("attempt-0000000000000007"), Some(7));
        assert_eq!(operation_of("provider-0000000000000013.controller-request"), Some(13));
        assert_eq!(operation_of("provider-meter-0000000000000013.metadata.json"), Some(13));
        assert_eq!(operation_of("resident-origin-0000000000000011.admitted.json"), None);
        assert_eq!(operation_of("prompt-outcome-0000000000000011.json"), None);
        assert_eq!(operation_of("attempt-7"), None);
        assert_eq!(operation_of("attempt-0000000000000007x"), None);
    }
}
