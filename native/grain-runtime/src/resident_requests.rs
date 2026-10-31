//! Bounded source request custody. This cache cannot grant authority: every
//! admission and selected request is compared with a fresh signed room read.
//! Native completion and final delivery receipts own the terminal transition.
use crate::*;
const MAX_STATE_BYTES:usize=16_777_216;
const METADATA_RESERVE:usize=524_288;

#[derive(Clone, Copy)]
pub(crate) struct Limits { pub pending: usize, pub per_author: usize, pub page_size: u64 }
impl Default for Limits {fn default()->Self {Self {pending:64,per_author:8,page_size:64}}}
impl Limits {
    pub(crate) fn validate(&self)->Result<()> {
        if !(1..=1024).contains(&self.pending) || !(1..=self.pending).contains(&self.per_author) || !(1..=256).contains(&self.page_size) {
            return Err("resident admission requires maxPendingRequests1..1024, maxRequestsPerAuthor1..maxPendingRequests, discoveryPageSize1..256".into());
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all="camelCase", deny_unknown_fields)]
struct Request {
    identity: Value,
    entry: Value,
    #[serde(default, skip_serializing_if="Option::is_none")]
    started: Option<Value>,
}
#[derive(Default, Serialize, Deserialize)]
#[serde(rename_all="camelCase", deny_unknown_fields)]
struct Queue {
    binding: Value,
    pending: Vec<Request>,
    selected: Option<Request>,
    last_author: Option<String>,
    #[serde(default)]
    cursors:std::collections::BTreeMap<String,u64>,
    #[serde(default)]
    maintenance_revision:Option<String>,
    #[serde(default)]
    maintenance_pending:Option<Value>,
}
fn digest(value: &impl Serialize) -> Result<String> {
    sha256_bytes(&serde_json::to_vec(value).map_err(|e|e.to_string())?)
}
fn path(state: &Path) -> PathBuf { state.join("requests.json") }
fn decode_queue(bytes:&[u8])->Result<Queue> {
    let q:Queue=serde_json::from_slice(bytes).map_err(|e|format!("resident request custody: {e}"))?;
    if q.pending.len()+usize::from(q.selected.is_some())>1024 {
        return Err("resident request custody exceeds admission limit".into());
    }
    Ok(q)
}
fn open(state: &Path) -> Result<Queue> {
    let p=path(state);
    if !p.exists() { return Ok(Queue::default()); }
    decode_queue(&bounded_regular_file(&p,MAX_STATE_BYTES)?)
}
/// Read-only snapshot under the resident driver's lock. This retains exact
/// bytes, including an absent file, so publication cannot overlook a request
/// admitted or started between its inspection and restart.
pub(crate) struct CustodySnapshot {
    pub bytes:Option<Vec<u8>>,
    pub queued:bool,
    pub started:bool,
    pub maintenance_pending:bool,
}
pub(crate) fn custody_snapshot(state:&Path)->Result<CustodySnapshot> {
    let file=path(state);
    let bytes=match fs::symlink_metadata(&file) {
        Err(e) if e.kind()==io::ErrorKind::NotFound=>None,
        Err(e)=>return Err(format!("resident request custody: {e}")),
        Ok(meta)=>{
            if !meta.is_file() || meta.uid()!=unsafe{libc::geteuid()} || meta.mode()&0o077!=0 || meta.nlink()!=1 {
                return Err("resident request custody must be an owned private regular file".into());
            }
            Some(bounded_regular_file(&file,MAX_STATE_BYTES)?)
        }
    };
    let q=bytes.as_deref().map(decode_queue).transpose()?.unwrap_or_default();
    Ok(CustodySnapshot {
        bytes,
        queued:!q.pending.is_empty() || q.selected.as_ref().is_some_and(|r|r.started.is_none()),
        started:q.selected.as_ref().is_some_and(|r|r.started.is_some()),
        maintenance_pending:q.maintenance_pending.is_some(),
    })
}

fn record(state: &Path, request: &Request, status: &str, evidence: Value) -> Result<()> {
    let receipt=json!({"type":"mini-resident-request-outcome-v1","identity":request.identity,
        "status":status,"evidence":evidence});
    let mut receipt=receipt;
    if status!="completed" && request.started.is_none() {receipt["modelRequests"]=json!(0);}
    let name=state.join(format!("request-{}-{}.json",digest(&request.identity)?,status));
    retain_exact_private(&name,&serde_json::to_vec_pretty(&receipt).map_err(|e|e.to_string())?,1_048_576)?;
    File::open(state).and_then(|f|f.sync_all()).map_err(|e|e.to_string())?;
    println!("{receipt}");
    owe(state,request,notice_status(status),&terminal_text(status,&evidence))
}

/// The request-status a terminal outcome is published as. A notice carries one of STATUSES (the
/// client's `say --status`, and `hermes status`'s states); a turn that failed after admission (its
/// model call refused: `no-credential`, a cap) is published as `refused`, its text naming why, so
/// the asker's `hermes status` shows the reason instead of a request left `unacknowledged`.
fn notice_status(status:&str)->&str {
    if status=="failed-after-admission" {"refused"} else {status}
}

/// The request's native terminal receipt proves the resident consumed this
/// exact delivery, rather than merely dropping its selected queue entry.
pub(crate) fn consumed_delivery_receipt(
    state: &Path,
    queue_bytes: &[u8],
    entry: &Value,
    subject: &str,
    delivery_path: &Path,
    delivery: &Value,
) -> Result<Value> {
    let queue = decode_queue(queue_bytes)?;
    if !queue.pending.is_empty() || queue.selected.is_some() || queue.maintenance_pending.is_some()
    {
        return Err("completed request custody is not drained".into());
    }
    let request = request(&queue.binding, entry, subject)?;
    let status = match delivery["result"]["result"]["resolution"].as_str() {
        Some("performed") => "completed",
        Some("refused") => "refused",
        _ => return Err("consumed request lacks a definite delivery".into()),
    };
    let path = state.join(format!(
        "request-{}-{status}.json",
        digest(&request.identity)?
    ));
    let bytes = bounded_regular_file(&path, 1_048_576)?;
    let receipt: Value = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    let expected = json!({"type":"mini-resident-request-outcome-v1","identity":request.identity,"status":status,
        "evidence":{"deliveryReceipt":delivery_path,"sha256":digest(delivery)?,"origin":delivery["origin"]}});
    if receipt != expected {
        return Err("consumed request differs from its native final receipt".into());
    }
    Ok(json!({"path":path,"sha256":sha256_bytes(&bytes)?}))
}

fn terminal_text(status:&str,evidence:&Value)->String {
    match (status,evidence["basis"].as_str()) {
        ("cancelled",Some("author-withdrew"))=>"cancelled: you withdrew it before it started".into(),
        ("cancelled",Some("source-assignment-replaced"))=>"cancelled: the room's Hermes assignment was replaced; ask again".into(),
        ("cancelled",Some("source-assignment-dismissed"))=>"cancelled: Hermes was dismissed from this room".into(),
        ("cancelled",Some("source-membership-revoked"))=>"cancelled: your room membership was revoked".into(),
        ("refused",Some("bounded-admission"))=>"refused: Hermes's queue is full; ask again later".into(),
        ("refused",Some(basis))=>format!("refused: {basis}"),
        ("completed",_)=>"completed: replied".into(),
        ("failed-after-admission",_)=>match provider_refusal(evidence) {
            // A named refusal of the turn's model call is the author's to know:
            // it says which cap, not merely that no reply came.
            Some(code)=>format!("failed: Hermes's model call was refused ({code}); no reply was written"),
            None=>"failed: Hermes's turn ended without a reply after it started; ask again".into(),
        },
        _=>status.into(),
    }
}

/// The key broker's or gateway's refusal name in a failed turn's typed
/// outcome (its decoded reason carries the gateway's `error.code`).
const PROVIDER_REFUSALS:&[&str]=&["member-day-ceiling","member-total-ceiling","per-day-cap","per-call-cap",
    "spend-ceiling","no-credit","no-credential","grant-expired","no-route"];
fn provider_refusal(evidence:&Value)->Option<&'static str> {
    let text=evidence.get("outcome")?.to_string();
    PROVIDER_REFUSALS.iter().copied().find(|code|text.contains(code))
}

// ---------------------------------------------------------------- notices
//
// Members see a request's state as typed request-status entries Hermes
// publishes in its own stream, replying to the request: one at each
// transition (queued, started, one terminal outcome), never a heartbeat.
// They are paid through the same room-turn budget as replies. A notice that
// cannot be afforded or is refused is skipped; publication never blocks or
// replaces the request's terminal outcome, which is the retained record above.

const MAX_NOTICES:usize=256;

#[derive(Clone,Debug,Default,Serialize,Deserialize,PartialEq)]
#[serde(rename_all="camelCase", deny_unknown_fields)]
pub(crate) struct Notice {
    pub identity: Value,
    pub author: String,
    pub cell: String,
    pub sequence: u64,
    /// The request's feed number when the notice was owed. Informational:
    /// the write re-reads the current number for its stable cell/sequence.
    pub number: u64,
    pub status: String,
    pub text: String,
    /// owed, published or skipped; `op` is set before any payment.
    pub state: String,
    #[serde(default, skip_serializing_if="Option::is_none")]
    pub op: Option<String>,
    #[serde(default, skip_serializing_if="Option::is_none")]
    pub evidence: Option<Value>,
}
#[derive(Default,Serialize,Deserialize)]
#[serde(rename_all="camelCase", deny_unknown_fields)]
pub(crate) struct Notices { next: u64, notices: Vec<Notice> }

fn notices_path(state:&Path)->PathBuf { state.join("notices.json") }
pub(crate) fn notices(state:&Path)->Result<Notices> {
    let p=notices_path(state);
    if !p.exists() { return Ok(Notices::default()); }
    serde_json::from_slice(&bounded_regular_file(&p,MAX_STATE_BYTES)?).map_err(|e|format!("resident notices: {e}"))
}
/// The request states a notice may carry (the client's `say --status`).
pub(crate) const STATUSES:&[&str]=&["queued","started","completed","refused","cancelled"];
fn is_terminal(status:&str)->bool { matches!(status,"completed"|"refused"|"cancelled") }

/// Owe one notice for a transition. Bounded per request by construction: one
/// per status and one terminal. Retention is bounded; settled notices are
/// pruned first, and a backlog of unsettled ones skips the new notice.
fn owe(state:&Path,request:&Request,status:&str,text:&str)->Result<()> {
    let (Some(author),Some(cell),Some(sequence),Some(number))=(request.entry["author"].as_str(),request.entry["cell"].as_str(),
        request.entry["sequence"].as_u64(),request.entry["n"].as_u64()) else { return Ok(()) };
    let mut all=notices(state)?;
    if all.notices.iter().any(|n|n.identity==request.identity && (n.status==status || (is_terminal(status) && is_terminal(&n.status)))) {
        return Ok(());
    }
    while all.notices.len()>=MAX_NOTICES {
        match all.notices.iter().position(|n|n.state!="owed") { Some(i)=>{all.notices.remove(i);} None=>break }
    }
    let skipped=all.notices.len()>=MAX_NOTICES;
    all.notices.push(Notice{identity:request.identity.clone(),author:author.into(),cell:cell.into(),sequence,number,
        status:status.into(),text:text.into(),state:if skipped {"skipped".into()} else {"owed".into()},op:None,
        evidence:skipped.then(||json!({"basis":"notice-backlog","maxNotices":MAX_NOTICES}))});
    atomic_json(&notices_path(state),&all)
}

/// One publication step's outcome, decided by the exact operation record.
pub(crate) enum Published { Done(Value), Skipped(Value), Uncertain(String) }

/// Publish owed notices in order. `pay(op)` and `write(op, notice)` use the
/// notice's exact operation record, so entering them again after a crash
/// looks the operation up instead of paying or writing twice. An uncertain
/// notice stays owed and is retried later; others still publish.
pub(crate) fn publish_notices(state:&Path,mut pay:impl FnMut(&str)->Published,
    mut write:impl FnMut(&str,&Notice)->Published)->Result<Vec<String>> {
    let mut all=notices(state)?;
    let mut uncertain=Vec::new();
    for index in 0..all.notices.len() {
        if all.notices[index].state!="owed" { continue; }
        if all.notices[index].op.is_none() {
            all.next+=1;
            all.notices[index].op=Some(format!("rs{}",all.next));
            atomic_json(&notices_path(state),&all)?; // durable identity before any payment
        }
        let op=all.notices[index].op.clone().unwrap();
        let outcome=match pay(&op) {
            Published::Done(_)=>write(&op,&all.notices[index]),
            other=>other,
        };
        match outcome {
            Published::Done(evidence)=>{all.notices[index].state="published".into();all.notices[index].evidence=Some(evidence);}
            Published::Skipped(evidence)=>{all.notices[index].state="skipped".into();all.notices[index].evidence=Some(evidence);}
            Published::Uncertain(reason)=>uncertain.push(format!("{op}: {reason}")),
        }
        atomic_json(&notices_path(state),&all)?;
    }
    Ok(uncertain)
}

/// The author's own `withdraw` entry replying to this request, addressed to
/// the resident.
fn withdrawal<'a>(entries:&'a [Value],request:&Request,subject:&str)->Option<&'a Value> {
    entries.iter().find(|e| e["kind"]=="withdraw" && e["author"]==request.entry["author"] && e["to"]==subject
        && e["reCell"]==request.entry["cell"] && e["reSequence"]==request.entry["sequence"])
}
fn terminal(state: &Path, request: &Request) -> Result<bool> {
    let id=digest(&request.identity)?;
    for status in ["completed","refused","cancelled","failed-after-admission"] {
        let p=state.join(format!("request-{id}-{status}.json"));
        if !p.exists() {continue;}
        let receipt:Value=serde_json::from_slice(&bounded_regular_file(&p,1_048_576)?).map_err(|e|e.to_string())?;
        if receipt["type"]!="mini-resident-request-outcome-v1" || receipt["identity"]!=request.identity || receipt["status"]!=status {
            return Err("request outcome changed identity or status".into());
        }
        return Ok(true);
    }
    Ok(false)
}
fn request(binding: &Value, entry: &Value, subject: &str) -> Result<Request> {
    let author=entry["author"].as_str().ok_or("request author absent")?;
    let cell=entry["cell"].as_str().ok_or("request stream cell absent")?;
    decimal(author,"request author")?; decimal(cell,"request stream cell")?;
    if author==subject || entry["to"]!=subject || entry["kind"]!="say"
        || entry["sequence"].as_u64().is_none_or(|n|n==0)
        || entry["height"].as_u64().is_none()
        || entry["n"].as_u64().is_none_or(|n|n==0 || n>9_999_999_999)
        || entry["text"].as_str().is_none_or(|s|s.len()>12_000) {
        return Err("addressed source request malformed".into());
    }
    Ok(Request { identity:json!({"binding":binding,"cell":cell,
        "sequence":entry["sequence"],"author":author}),entry:entry.clone(),started:None })
}
fn same_entry(a:&Value,b:&Value)->bool {
    ["author","cell","height","sequence","text","to","kind"].iter().all(|k|a[*k]==b[*k])
}
/// A discovery request describes only source positions and retained refs.
/// It confers no read authority; the participant's signed room grant does that.
pub(crate) fn discovery(state:&Path,binding:&Value)->Result<Value> {
    let q=open(state)?;
    let same=q.binding==*binding;
    Ok(json!({"type":"mini-resident-discovery-v1",
        "cursors":if same {q.cursors} else {Default::default()},
        "retained":if same {q.pending.iter().chain(q.selected.iter()).map(|r|json!([r.entry["cell"],r.entry["sequence"]])).collect::<Vec<_>>()} else {Vec::new()}}))
}
/// Select one FIFO request, rotating among authors. Admission overflow and
/// source revocation are durable outcomes, never silently displaced prompts.
pub(crate) fn select(prepared:&Value,state:&Path,limits:Limits)->Result<Option<Value>> {
    limits.validate()?;
    let binding=&prepared["requestBinding"];
    if !binding.is_object() || binding["roomCell"].as_str().is_none()
        || binding["world"].is_null() || binding["assignment"].is_null() {
        return Err("resident request binding absent".into());
    }
    let entries=prepared["sourceRequests"].as_array().ok_or("signed request history absent")?;
    let subject=prepared["me"].as_str().ok_or("resident subject absent")?;
    let accepted_height=prepared["acceptedHeight"].as_str().ok_or("assignment accepted height absent")?
        .parse::<u64>().map_err(|_|"assignment accepted height invalid")?;
    let members=prepared["sourceRoom"]["members"].as_array().ok_or("signed source members absent")?;
    let eligible=|entry:&Value|members.iter().any(|m|m["subject"]==entry["author"] && m["stream"]==entry["cell"]);
    let mut q=open(state)?;
    if !q.binding.is_null() && q.binding!=*binding {
        if q.selected.as_ref().is_some_and(|r|r.started.is_some()) {return Err("started request belongs to replaced assignment; retained for exact recovery".into());}
        for r in q.pending.iter().chain(q.selected.iter()) {record(state,r,"cancelled",json!({"basis":"source-assignment-replaced","currentBinding":binding}))?;}
        q=Queue::default();
    }
    q.binding=binding.clone();
    let mut retained=Vec::new();
    for mut r in q.pending.drain(..) {
        if terminal(state,&r)? { continue; }
        if !eligible(&r.entry) {record(state,&r,"cancelled",json!({"basis":"source-membership-revoked"}))?;continue;}
        if let Some(w)=withdrawal(entries,&r,subject) {record(state,&r,"cancelled",json!({"basis":"author-withdrew","withdraw":w}))?;continue;}
        if let Some(fresh)=entries.iter().find(|e|same_entry(e,&r.entry)) {r.entry=fresh.clone();}
        retained.push(r);
    }
    q.pending=retained;
    if let Some(r)=&mut q.selected {
        if terminal(state,r)? {q.last_author=r.entry["author"].as_str().map(str::to_owned);q.selected=None;}
        else if !eligible(&r.entry) {
            if r.started.is_some() {return Err("started request author revoked; retained for exact recovery".into());}
            record(state,r,"cancelled",json!({"basis":"source-membership-revoked"}))?;q.selected=None;
        }
        // A withdraw cancels only a request that has not started; a started
        // request ends only by pre-admission proof or native terminal receipt.
        else if let (None,Some(w))=(&r.started,withdrawal(entries,r,subject)) {
            record(state,r,"cancelled",json!({"basis":"author-withdrew","withdraw":w}))?;q.selected=None;
        }
        else if let Some(fresh)=entries.iter().find(|e|same_entry(e,&r.entry)) {r.entry=fresh.clone();}
        else if r.started.is_some() {return Err("started request source unreadable; exact recovery required".into());}
        else {q.pending.push(q.selected.take().unwrap());}
    }
    let mut ordered:Vec<&Value>=entries.iter().filter(|e|e["to"]==subject && e["author"]!=subject && e["kind"]=="say" && e["height"].as_u64().is_some_and(|h|h>accepted_height)).collect();
    ordered.sort_by_key(|e|(e["height"].as_u64(),e["author"].as_str(),e["cell"].as_str(),e["sequence"].as_u64()));
    for entry in ordered {
        let r=request(binding,entry,subject)?;
        if terminal(state,&r)? || q.pending.iter().chain(q.selected.iter()).any(|p|p.identity==r.identity) {continue;}
        if !eligible(entry) {record(state,&r,"cancelled",json!({"basis":"source-membership-revoked"}))?;continue;}
        if let Some(w)=withdrawal(entries,&r,subject) {record(state,&r,"cancelled",json!({"basis":"author-withdrew","withdraw":w}))?;continue;}
        let author_count=q.pending.iter().chain(q.selected.iter()).filter(|p|p.entry["author"]==entry["author"]).count();
        if author_count>=limits.per_author || q.pending.len()+usize::from(q.selected.is_some())>=limits.pending {
            record(state,&r,"refused",json!({"basis":"bounded-admission","maxPending":limits.pending,"maxPerAuthor":limits.per_author}))?;
        } else {
            q.pending.push(r);
            if serde_json::to_vec_pretty(&q).map_err(|e|e.to_string())?.len()>MAX_STATE_BYTES-METADATA_RESERVE {
                let r=q.pending.pop().unwrap();
                record(state,&r,"refused",json!({"basis":"bounded-custody-bytes","maxStateBytes":MAX_STATE_BYTES,"metadataReserve":METADATA_RESERVE}))?;
            } else {
                let queued=q.pending.last().unwrap().clone();
                owe(state,&queued,"queued",&format!("queued: {} ahead of it",q.pending.len()-1+usize::from(q.selected.is_some())))?;
            }
        }
    }
    if q.selected.is_none() && !q.pending.is_empty() {
        let authors:std::collections::BTreeSet<String>=q.pending.iter().filter(|r|entries.iter().any(|e|same_entry(e,&r.entry))).map(|r|r.entry["author"].as_str().unwrap().to_owned()).collect();
        if let Some(author)=authors.iter().find(|a|q.last_author.as_ref().is_none_or(|last|*a>last)).or_else(||authors.first()) {
            let index=q.pending.iter().position(|r|r.entry["author"]==*author && entries.iter().any(|e|same_entry(e,&r.entry))).unwrap();
            q.selected=Some(q.pending.remove(index));
        }
    }
    if let Some(cursors)=prepared["sourceRoom"]["discoveryCursors"].as_object() {
        for (cell,value) in cursors {let seq=value.as_u64().ok_or("signed discovery cursor invalid")?;let old=q.cursors.entry(cell.clone()).or_default();*old=(*old).max(seq);}
    }
    q.cursors.retain(|cell,_|members.iter().any(|m|m["stream"]==*cell));
    atomic_json(&path(state),&q)?;
    let Some(selected)=q.selected else{return Ok(None)};
    let mut brief=prepared.clone();
    brief.as_object_mut().unwrap().remove("sourceRequests");
    brief.as_object_mut().unwrap().remove("sourceRoom");
    brief["selectedRequest"]=selected.identity;
    // Exactly one addressed request enters both prompting and final routing.
    brief["recentMemberEntries"]=json!([selected.entry]);
    Ok(Some(brief))
}
pub(crate) fn refuse_selected(state:&Path,evidence:Value)->Result<()> {
    let mut q=open(state)?;let r=q.selected.as_ref().ok_or("request refusal has no selection")?;
    if r.started.is_some() {return Err("started request cannot be refused without exact native terminal evidence".into());}
    record(state,r,"refused",evidence)?;q.last_author=r.entry["author"].as_str().map(str::to_owned);q.selected=None;
    atomic_json(&path(state),&q)
}
/// Only the source's exact lexical pre-admission proof can close started
/// custody without an operation. Absence or local request counts cannot.
pub(crate) fn receive_preadmission_refusal(state:&Path,pending:&Value,proof:&Value)->Result<()> {
    if proof["type"]!="mini-resident-prompt-preadmission-refused-v1" || proof["admitted"]!=false
        || proof["effects"]!="none" || proof["modelRequests"]!=0
        || proof["residentPromptId"]!=pending["residentPromptId"] || proof["promptSha256"]!=pending["promptSha256"] {
        return Err("request refusal requires exact source preadmission proof".into());
    }
    let mut q=open(state)?;
    let identity=&pending["selectedRequest"];
    let expected_started=json!({"residentPromptId":pending["residentPromptId"],"inputSha256":pending["inputSha256"]});
    if q.maintenance_pending.as_ref().is_some_and(|maintenance|maintenance["residentPromptId"]!=pending["residentPromptId"]) {
        return Err("maintenance refusal names another source prompt".into());
    }
    if !identity.is_null() {
        let evidence=json!({"basis":"source-pre-admission-refusal","admission":proof,"started":expected_started});
        if let Some(selected)=q.selected.as_ref() {
            if selected.identity!=*identity || selected.started.as_ref()!=Some(&expected_started) {
                return Err("source refusal differs from retained selected request".into());
            }
            let mut projection=selected.clone();projection.started=None;
            record(state,&projection,"refused",evidence)?;
            q.last_author=selected.entry["author"].as_str().map(str::to_owned);q.selected=None;
        } else {
            // Queue publication may have committed before resident.json was
            // cleared; require the exact already retained terminal record.
            let file=state.join(format!("request-{}-refused.json",digest(identity)?));
            let receipt:Value=serde_json::from_slice(&bounded_regular_file(&file,1_048_576)?).map_err(|e|e.to_string())?;
            if receipt!=json!({"type":"mini-resident-request-outcome-v1","identity":identity,"status":"refused","evidence":evidence,"modelRequests":0}) {
                return Err("retained request refusal is not this source preadmission proof".into());
            }
        }
    }
    if let Some(maintenance)=&q.maintenance_pending {
        if maintenance["residentPromptId"]!=pending["residentPromptId"] {return Err("maintenance refusal names another source prompt".into());}
        q.maintenance_pending=None;
    }
    atomic_json(&path(state),&q)
}
pub(crate) fn maintenance_needed(state:&Path,revision:&str)->Result<bool> {
    Ok(open(state)?.maintenance_revision.as_deref()!=Some(revision))
}
pub(crate) fn maintenance_started(state:&Path,prompt_id:&str,revision:&str)->Result<()> {
    let mut q=open(state)?;q.maintenance_pending=Some(json!({"residentPromptId":prompt_id,"revision":revision}));atomic_json(&path(state),&q)
}
pub(crate) fn started(state:&Path,prompt_id:&str,input:&str)->Result<()> {
    let mut q=open(state)?;
    if let Some(r)=q.selected.as_mut() {r.started=Some(json!({"residentPromptId":prompt_id,"inputSha256":input}));}
    else {return Err("resident prompt has no durably selected request".into());}
    atomic_json(&path(state),&q)?;
    let selected=q.selected.as_ref().unwrap();
    owe(state,selected,"started","started: Hermes is working on it")
}
pub(crate) fn dismiss(state:&Path)->Result<()> {
    let mut q=open(state)?;
    if q.selected.as_ref().is_some_and(|r|r.started.is_some()) {
        return Err("dismissed resident has a started request requiring exact recovery".into());
    }
    for r in q.pending.iter().chain(q.selected.iter()) {record(state,r,"cancelled",json!({"basis":"source-assignment-dismissed"}))?;}
    q.pending.clear();q.selected=None;atomic_json(&path(state),&q)
}
/// Recovery follows the native receipt, so a lost driver completion frame does
/// not run a second model or silently classify an uncertain write as done.
/// A maintenance prompt closes when its completion is received, before the
/// reply it may carry is delivered: the delivery boundary admits nothing
/// retained but the delivery and the request it answers.
pub(crate) fn receive_maintenance(state:&Path,controller:&Path,completion:Option<&Value>)->Result<()> {
    let mut q=open(state)?;
    if let (Some(pending),Some(frame))=(&q.maintenance_pending,completion) {
        if frame["outcome"]=="completed" && frame["residentOrigin"]["residentPromptId"]==pending["residentPromptId"] {
            q.maintenance_revision=Some(pending["revision"].as_str().ok_or("maintenance revision absent")?.to_owned());
            q.maintenance_pending=None;atomic_json(&path(state),&q)?;
        } else if frame["outcome"]!="completed" && frame["residentOrigin"]["residentPromptId"]==pending["residentPromptId"] {
            // A maintenance prompt the controller decided as refused is closed:
            // the revision stays unsatisfied (so maintenance is retried) but the
            // pending marker must not outlive the decision. Undecided and
            // admitted prompts keep it.
            let op=frame["residentOrigin"]["promptOperationId"].as_u64().ok_or("maintenance completion origin absent")?;
            let id=pending["residentPromptId"].as_str().ok_or("maintenance prompt identity absent")?;
            let sha=frame["residentOrigin"]["promptSha256"].as_str().ok_or("maintenance completion origin has no prompt digest")?;
            let decided=prompt_outcome::read_bound(controller,op,id,sha)?;
            if matches!(decided.outcome,prompt_outcome::Outcome::Refused{..}) {
                q.maintenance_pending=None;atomic_json(&path(state),&q)?;
            }
        }
    }
    Ok(())
}
pub(crate) fn reconcile(state:&Path,controller:&Path,completion:Option<&Value>)->Result<()> {
    receive_maintenance(state,controller,completion)?;
    let mut q=open(state)?;
    let Some(r)=q.selected.as_ref() else{return Ok(())};
    if terminal(state,r)? {q.last_author=r.entry["author"].as_str().map(str::to_owned);q.selected=None;return atomic_json(&path(state),&q);}
    let Some(start)=&r.started else{return Ok(())};
    let Some(frame)=completion else{return Ok(())};
    if frame["residentOrigin"]["residentPromptId"]!=start["residentPromptId"] {return Ok(())};
    let op=frame["residentOrigin"]["promptOperationId"].as_u64().ok_or("request completion origin absent")?;
    // The controller's typed record decides the prompt (gr §4.3); the
    // frame's outcome label is presentation and is never consulted.
    let started_id=start["residentPromptId"].as_str().ok_or("started request has no prompt identity")?;
    let sha=frame["residentOrigin"]["promptSha256"].as_str().ok_or("request completion origin has no prompt digest")?;
    let outcome=prompt_outcome::read_bound(controller,op,started_id,sha)?;
    match &outcome.outcome {
        prompt_outcome::Outcome::Undecided{retry,..}=>{
            return Err(format!("selected request's prompt {op} is undecided; resolve it with admin {:?} (operation {:?}) before another request starts",retry.admin,retry.operation));
        }
        prompt_outcome::Outcome::Refused{..}=>{
            let mut evidence=prompt_outcome::evidence(controller,op)?;
            evidence["origin"]=frame["residentOrigin"].clone();
            // H13: no deliverable result is claimed. Audited closure names
            // both immutable original uncertainty and its validated resolution.
            record(state,r,"failed-after-admission",evidence)?;
            q.last_author=r.entry["author"].as_str().map(str::to_owned);q.selected=None;
            return atomic_json(&path(state),&q);
        }
        prompt_outcome::Outcome::Admitted{..}=>{}
    }
    let performed_path=controller.join(format!("resident-delivered-{op:016}.json"));
    let refused_path=controller.join(format!("resident-final-refused-{op:016}.json"));
    if performed_path.exists() && refused_path.exists() {return Err("request has conflicting native terminal receipts".into());}
    let refused=refused_path.exists();let receipt_path=if refused {refused_path} else {performed_path};
    if !receipt_path.exists() {return Err("selected request completed without native terminal receipt; recovery required".into());}
    let receipt:Value=serde_json::from_slice(&bounded_regular_file(&receipt_path,1_048_576)?).map_err(|e|e.to_string())?;
    if receipt["type"]!=if refused {"mini-resident-final-refused-v1"} else {"mini-resident-delivered-v1"} || receipt["origin"]!=frame["residentOrigin"]
        || receipt["result"]["result"]["resolution"]!=if refused {"refused"} else {"performed"}
        || receipt["result"]["expectedReply"]!=json!([r.entry["cell"],r.entry["sequence"]])
        || receipt["result"]["arguments"]["to"]!=r.entry["author"] {
        return Err("request receipt does not confirm selected source identity".into());
    }
    record(state,r,if refused {"refused"} else {"completed"},json!({"deliveryReceipt":receipt_path,"sha256":digest(&receipt)?,"origin":receipt["origin"]}))?;
    q.last_author=r.entry["author"].as_str().map(str::to_owned);q.selected=None;
    atomic_json(&path(state),&q)
}
#[cfg(test)]
mod tests {
    use super::*;
    fn fixture(tag:&str)->PathBuf {let p=std::env::temp_dir().join(format!("resident-queue-{tag}-{}",std::process::id()));fs::create_dir_all(&p).unwrap();fs::set_permissions(&p,std::os::unix::fs::PermissionsExt::from_mode(0o700)).unwrap();p}
    fn entry(author:&str,n:u64)->Value {json!({"author":author,"cell":author,"sequence":n,"height":n,"n":n,"kind":"say","text":"question","to":"8"})}
    fn prepared(entries:Vec<Value>)->Value {json!({"requestBinding":{"world":{"domain":"1","expectedSeed":"2"},"roomCell":"99","assignment":"1","task":"7"},"sourceRoom":{"entries":entries.len(),"selectedEntries":entries.len(),"members":[{"subject":"20","stream":"20"},{"subject":"21","stream":"21"}]},"sourceRequests":entries,"acceptedHeight":"0","me":"8","recentMemberEntries":[]})}
    #[test]
    fn a_failed_turn_names_the_cap_its_model_call_hit() {
        let failed=json!({"basis":"typed-prompt-outcome","outcome":{"refused":{"stage":"turn-failure",
            "reason":"ACP session/prompt error: HTTP 403 {\"error\":{\"code\":\"member-day-ceiling\"}}"}}});
        assert_eq!(terminal_text("failed-after-admission",&failed),
            "failed: Hermes's model call was refused (member-day-ceiling); no reply was written");
        let plain=json!({"basis":"typed-prompt-outcome","outcome":{"refused":{"stage":"turn-failure","reason":"worker exited"}}});
        assert!(terminal_text("failed-after-admission",&plain).ends_with("ask again"));
    }

    #[test]fn a_refused_model_call_is_published_to_the_asker_by_name() {
        let state=fixture("refused-call");let p=prepared(vec![entry("20",1)]);
        select(&p,&state,Limits::default()).unwrap().unwrap();
        let mut q=open(&state).unwrap();let r=q.selected.take().unwrap();
        let failed=json!({"basis":"typed-prompt-outcome","outcome":{"refused":{"stage":"turn-failure",
            "reason":"provider refused: {\"error\":{\"code\":\"no-credential\"}}"}}});
        record(&state,&r,"failed-after-admission",failed).unwrap();
        let last=notices(&state).unwrap().notices.pop().unwrap();
        assert!(STATUSES.contains(&last.status.as_str()),"a status the room write accepts: {}",last.status);
        assert_eq!((last.status.as_str(),last.state.as_str()),("refused","owed"));
        assert_eq!(last.text,"failed: Hermes's model call was refused (no-credential); no reply was written");
        fs::remove_dir_all(state).unwrap();
    }
    #[test]fn fair_fifo_restart_and_bounded_admission() {
        let state=fixture("fair");let p=prepared((1..=12).map(|n|entry("20",n)).chain([entry("21",13),entry("21",14)]).collect());
        let first=select(&p,&state,Limits::default()).unwrap().unwrap();assert_eq!(first["recentMemberEntries"][0]["sequence"],1);
        assert_eq!(select(&p,&state,Limits::default()).unwrap().unwrap(),first,"restart retains selection");
        let mut q=open(&state).unwrap();assert_eq!(q.pending.len(),9);let r=q.selected.take().unwrap();record(&state,&r,"completed",json!({})).unwrap();q.last_author=Some("20".into());atomic_json(&path(&state),&q).unwrap();
        assert_eq!(select(&p,&state,Limits::default()).unwrap().unwrap()["recentMemberEntries"][0]["author"],"21");
        assert_eq!(fs::read_dir(&state).unwrap().flatten().filter(|e|e.file_name().to_string_lossy().ends_with("-refused.json")).count(),4);
        fs::remove_dir_all(state).unwrap();
    }
    #[test]fn revocation_and_reassignment_cancel_before_generation() {
        let state=fixture("cancel");let mut p=prepared(vec![entry("20",1),entry("21",2)]);select(&p,&state,Limits::default()).unwrap();
        p["sourceRoom"]["members"]=json!([{"subject":"21","stream":"21"}]);
        assert_eq!(select(&p,&state,Limits::default()).unwrap().unwrap()["recentMemberEntries"][0]["author"],"21");
        p["requestBinding"]["assignment"]=json!("2");assert!(select(&p,&state,Limits::default()).unwrap().is_some());
        started(&state,"prompt","input").unwrap();p["requestBinding"]["assignment"]=json!("3");assert!(select(&p,&state,Limits::default()).is_err());
        fs::remove_dir_all(state).unwrap();
    }
    #[test]fn started_revoked_request_retains_native_recovery_custody() {
        let state=fixture("started-revoked");let mut p=prepared(vec![entry("20",1),entry("21",2)]);
        select(&p,&state,Limits::default()).unwrap();started(&state,"source-prompt","input").unwrap();
        let before=fs::read(path(&state)).unwrap();
        p["sourceRoom"]["members"]=json!([{"subject":"21","stream":"21"}]);
        let error=select(&p,&state,Limits::default()).unwrap_err();assert!(error.contains("exact recovery"));
        assert_eq!(fs::read(path(&state)).unwrap(),before,"revocation cannot erase a started request");
        assert!(!fs::read_dir(&state).unwrap().flatten().any(|e|e.file_name().to_string_lossy().ends_with("-cancelled.json")));
        fs::remove_dir_all(state).unwrap();
    }
    #[test]fn initial_history_over_hundred_is_not_limited_to_recent_tail() {
        let state=fixture("history");let mut p=prepared((1..=130).map(|n|{let mut e=entry("20",n);if n>1 {e["to"]=Value::Null;}e}).collect());
        assert_eq!(select(&p,&state,Limits::default()).unwrap().unwrap()["recentMemberEntries"][0]["n"],1);
        fs::remove_dir_all(state).unwrap();
    }
    #[test]fn cursor_progress_is_durable_and_same_height_streams_do_not_skip() {
        let state=fixture("cursor");let mut p=prepared(vec![entry("20",1),entry("21",1)]);
        p["sourceRoom"]["discoveryCursors"]=json!({"20":1,"21":1});
        select(&p,&state,Limits::default()).unwrap();
        let spec=discovery(&state,&p["requestBinding"]).unwrap();
        assert_eq!(spec["cursors"],json!({"20":1,"21":1}));assert_eq!(spec["retained"].as_array().unwrap().len(),2);
        p["sourceRequests"]=json!([entry("20",1),entry("21",1),entry("21",2)]);
        p["sourceRequests"][2]["height"]=json!(1);
        p["sourceRoom"]["discoveryCursors"]=json!({"20":1,"21":2});
        select(&p,&state,Limits::default()).unwrap();
        assert_eq!(open(&state).unwrap().pending.len(),2);
        assert_eq!(discovery(&state,&p["requestBinding"]).unwrap()["cursors"]["21"],2);
        fs::remove_dir_all(state).unwrap();
    }
    fn outcome(controller:&Path,op:u64,id:&str,outcome:prompt_outcome::Outcome) {
        prompt_outcome::write(controller,&prompt_outcome::Record {kind:prompt_outcome::KIND.into(),prompt_operation_id:op,
            resident_prompt_id:Some(id.into()),prompt_sha256:Some("b".repeat(64)),session_id:None,outcome}).unwrap();
    }
    fn admitted()->prompt_outcome::Outcome {
        prompt_outcome::Outcome::Admitted {stop_reason:"end_turn".into(),settled_charge:"1".into(),provider_response_sha256:None,provider_metered_charge:None}
    }
    #[test]fn completion_recovery_requires_exact_native_delivery_and_never_zero_models_claim() {
        let state=fixture("receipt");let controller=state.join("controller");fs::create_dir(&controller).unwrap();fs::set_permissions(&controller,std::os::unix::fs::PermissionsExt::from_mode(0o700)).unwrap();
        let id="a".repeat(64);
        let p=prepared(vec![entry("20",1),entry("21",2)]);select(&p,&state,Limits::default()).unwrap();started(&state,&id,"input").unwrap();
        let frame=json!({"residentOrigin":{"residentPromptId":id,"promptSha256":"b".repeat(64),"promptOperationId":1}});
        assert!(reconcile(&state,&controller,Some(&frame)).is_err(),"no outcome record: undecided");
        outcome(&controller,1,&id,admitted());
        assert!(reconcile(&state,&controller,Some(&frame)).is_err(),"admitted still needs its delivery receipt");
        let receipt=json!({"type":"mini-resident-delivered-v1","origin":frame["residentOrigin"],"result":{"expectedReply":["20",1],"arguments":{"to":"20"},"result":{"resolution":"performed"}}});
        atomic_json(&controller.join("resident-delivered-0000000000000001.json"),&receipt).unwrap();
        reconcile(&state,&controller,Some(&frame)).unwrap();reconcile(&state,&controller,Some(&frame)).unwrap();
        assert!(open(&state).unwrap().selected.is_none());
        let file=fs::read_dir(&state).unwrap().flatten().find(|e|e.file_name().to_string_lossy().ends_with("-completed.json")).unwrap().path();
        let record:Value=serde_json::from_slice(&fs::read(file).unwrap()).unwrap();assert!(record.get("modelRequests").is_none());
        assert_eq!(select(&p,&state,Limits::default()).unwrap().unwrap()["recentMemberEntries"][0]["author"],"21");
        fs::remove_dir_all(state).unwrap();
    }
    #[test]fn failed_admitted_prompt_closes_its_request_and_the_next_is_selectable() {
        let state=fixture("failed-admitted");let controller=state.join("controller");fs::create_dir(&controller).unwrap();fs::set_permissions(&controller,std::os::unix::fs::PermissionsExt::from_mode(0o700)).unwrap();
        let id="d".repeat(64);
        let p=prepared(vec![entry("20",1),entry("21",2)]);select(&p,&state,Limits::default()).unwrap();started(&state,&id,"input").unwrap();
        // The frame label says "failed", but only the record decides. While
        // the record is undecided the request stays started and names its retry.
        let frame=json!({"outcome":"failed","residentOrigin":{"residentPromptId":id,"promptSha256":"b".repeat(64),"promptOperationId":5}});
        let undecided=prompt_outcome::Outcome::Undecided {retry:prompt_outcome::Retry {admin:vec!["reconcile parent audited".into(),"reconcile effects".into()],operation:None},detail:"ACP stream closed".into()};
        outcome(&controller,4,&id,undecided);
        assert!(reconcile(&state,&controller,Some(&json!({"outcome":"failed","residentOrigin":{"residentPromptId":id,"promptSha256":"b".repeat(64),"promptOperationId":4}})))
            .unwrap_err().contains("reconcile parent audited"));
        assert!(open(&state).unwrap().selected.unwrap().started.is_some(),"undecided is never a refusal");
        // H13: the turn failed at a settled boundary. No delivery receipt can
        // ever exist; the record closes the request instead of wedging it.
        outcome(&controller,5,&id,prompt_outcome::Outcome::Refused {stage:prompt_outcome::RefusalStage::TurnFailure,reason:"format_error".into()});
        reconcile(&state,&controller,Some(&frame)).unwrap();
        reconcile(&state,&controller,Some(&frame)).unwrap();
        assert!(open(&state).unwrap().selected.is_none());
        let closed=fs::read_dir(&state).unwrap().flatten().find(|e|e.file_name().to_string_lossy().ends_with("-failed-after-admission.json")).unwrap().path();
        let receipt:Value=serde_json::from_slice(&fs::read(closed).unwrap()).unwrap();
        assert_eq!(receipt["evidence"]["outcome"]["state"],"refused");assert!(receipt.get("modelRequests").is_none());
        assert_eq!(select(&p,&state,Limits::default()).unwrap().unwrap()["recentMemberEntries"][0]["author"],"21");
        fs::remove_dir_all(state).unwrap();
    }
    #[test]fn audited_prompt_closure_receipt_preserves_both_native_evidence_files() {
        let (mut rt, controller_root, _) = prompt_outcome::tests::audited_fixture();
        let state=fixture("audited-admitted"); let id="a".repeat(64);
        let p=prepared(vec![entry("20",1),entry("21",2)]);
        select(&p,&state,Limits::default()).unwrap(); started(&state,&id,"input").unwrap();
        let frame=json!({"outcome":"failed","residentOrigin":{"residentPromptId":id,
            "promptSha256":"b".repeat(64),"promptOperationId":67}});
        assert!(reconcile(&state,&rt.config.state_dir,Some(&frame)).is_err());
        assert!(open(&state).unwrap().selected.is_some());
        rt.reconcile_prompt_audited("67").unwrap();
        reconcile(&state,&rt.config.state_dir,Some(&frame)).unwrap();
        assert!(open(&state).unwrap().selected.is_none());
        let closed=fs::read_dir(&state).unwrap().flatten().find(|e|e.file_name().to_string_lossy().ends_with("-failed-after-admission.json")).unwrap().path();
        let receipt:Value=serde_json::from_slice(&fs::read(closed).unwrap()).unwrap();
        assert!(receipt.get("modelRequests").is_none(), "audited closure makes no zero-model claim");
        let e=&receipt["evidence"];assert_eq!(e["outcome"]["state"],"refused");
        let original=Path::new(e["promptOutcome"].as_str().unwrap());
        let original_json:Value=serde_json::from_slice(&fs::read(original).unwrap()).unwrap();
        assert_eq!(original_json["outcome"]["state"],"undecided");
        assert_eq!(e["sha256"],sha256_file(original).unwrap());
        let resolved=Path::new(e["resolution"]["path"].as_str().unwrap());
        assert_eq!(e["resolution"]["sha256"],sha256_file(resolved).unwrap());
        let resolution:Value=serde_json::from_slice(&fs::read(resolved).unwrap()).unwrap();
        assert_eq!(resolution["originalSha256"],e["sha256"]);
        assert_eq!(select(&p,&state,Limits::default()).unwrap().unwrap()["recentMemberEntries"][0]["author"],"21");
        fs::remove_dir_all(state).unwrap();fs::remove_dir_all(controller_root).unwrap();
    }
    #[test]fn assignment_cutoff_reassignment_does_not_readmit_answered_old_requests() {
        let state=fixture("cutoff");let mut p=prepared(vec![entry("20",1),entry("21",9)]);p["acceptedHeight"]=json!("5");
        assert_eq!(select(&p,&state,Limits::default()).unwrap().unwrap()["recentMemberEntries"][0]["sequence"],9);
        fs::remove_dir_all(state).unwrap();
    }
    #[test]fn unreadable_pending_author_does_not_block_other_members() {
        let state=fixture("unreadable");let mut p=prepared(vec![entry("20",1),entry("21",2)]);select(&p,&state,Limits::default()).unwrap();
        p["sourceRequests"]=json!([entry("21",2)]);
        assert_eq!(select(&p,&state,Limits::default()).unwrap().unwrap()["recentMemberEntries"][0]["author"],"21");
        assert_eq!(open(&state).unwrap().pending.len(),1);fs::remove_dir_all(state).unwrap();
    }

    #[test]fn escaped_text_byte_admission_remains_reopenable_at_default_and_configured_limits() {
        let state=fixture("bytes");
        let entries:Vec<Value>=(1..=250).map(|n|{let mut e=entry("20",n);e["text"]=json!("\0".repeat(12000));e}).collect();
        let p=prepared(entries);
        let default=Limits {pending:64,per_author:64,page_size:64};
        select(&p,&state,default).unwrap();assert_eq!(open(&state).unwrap().pending.len(),63);
        // A fresh assignment carries no prior refusals into this larger policy.
        let mut p=p;p["requestBinding"]["assignment"]=json!("2");
        select(&p,&state,Limits {pending:1024,per_author:1024,page_size:256}).unwrap();
        let q=open(&state).unwrap();assert!(q.pending.len()<249);assert!(q.pending.len()>64);
        assert!(fs::metadata(path(&state)).unwrap().len()<MAX_STATE_BYTES as u64);
        select(&p,&state,Limits {pending:1024,per_author:1024,page_size:256}).unwrap();open(&state).unwrap();
        fs::remove_dir_all(state).unwrap();
    }

    #[test]fn source_preadmission_receiving_is_exact_and_restarts_after_queue_publication() {
        let state=fixture("source-refusal");let p=prepared(vec![entry("20",1),entry("21",2)]);
        let selected=select(&p,&state,Limits::default()).unwrap().unwrap();started(&state,"source-id","input").unwrap();
        maintenance_started(&state,"source-id","baseline").unwrap();
        let pending=json!({"residentPromptId":"source-id","promptSha256":"sha","inputSha256":"input","selectedRequest":selected["selectedRequest"]});
        let proof=json!({"type":"mini-resident-prompt-preadmission-refused-v1","residentPromptId":"source-id","promptSha256":"sha","admitted":false,"effects":"none","modelRequests":0});
        let before=fs::read(path(&state)).unwrap();let mut wrong=proof.clone();wrong["residentPromptId"]=json!("other-id");
        assert!(receive_preadmission_refusal(&state,&pending,&wrong).is_err());assert_eq!(fs::read(path(&state)).unwrap(),before);
        receive_preadmission_refusal(&state,&pending,&proof).unwrap();
        // A killed driver can retain old pending after the queue outcome commits.
        receive_preadmission_refusal(&state,&pending,&proof).unwrap();
        let q=open(&state).unwrap();assert!(q.selected.is_none());assert!(q.maintenance_pending.is_none());assert!(q.maintenance_revision.is_none());
        let record:Value=serde_json::from_slice(&fs::read(state.join(format!("request-{}-refused.json",digest(&pending["selectedRequest"]).unwrap()))).unwrap()).unwrap();
        assert_eq!(record["modelRequests"],0);assert_eq!(record["evidence"]["started"]["residentPromptId"],"source-id");
        assert_eq!(select(&p,&state,Limits::default()).unwrap().unwrap()["selectedRequest"]["author"],"21");
        assert!(receive_preadmission_refusal(&state,&pending,&proof).is_err(),"old proof cannot close next author's selection");
        fs::remove_dir_all(state).unwrap();
    }
    #[test]fn deterministic_prompt_refusal_advances_author_without_provider_dispatch() {
        let state=fixture("prompt-refusal");let p=prepared(vec![entry("20",1),entry("21",2)]);
        select(&p,&state,Limits::default()).unwrap();refuse_selected(&state,json!({"basis":"prompt-frame-byte-bound"})).unwrap();
        assert_eq!(select(&p,&state,Limits::default()).unwrap().unwrap()["recentMemberEntries"][0]["author"],"21");
        started(&state,"source-id","input").unwrap();assert!(refuse_selected(&state,json!({})).is_err());
        fs::remove_dir_all(state).unwrap();
    }

    #[test]fn selected_completion_satisfies_unchanged_maintenance_without_another_prompt() {
        let state=fixture("maintenance");let controller=state.join("controller");fs::create_dir(&controller).unwrap();fs::set_permissions(&controller,std::os::unix::fs::PermissionsExt::from_mode(0o700)).unwrap();
        let p=prepared(vec![entry("20",1)]);select(&p,&state,Limits::default()).unwrap();
        let id="c".repeat(64);
        started(&state,&id,"request-input").unwrap();maintenance_started(&state,&id,"maintenance-revision").unwrap();
        let frame=json!({"outcome":"completed","residentOrigin":{"residentPromptId":id,"promptSha256":"b".repeat(64),"promptOperationId":1}});
        outcome(&controller,1,&id,admitted());
        let receipt=json!({"type":"mini-resident-delivered-v1","origin":frame["residentOrigin"],"result":{"expectedReply":["20",1],"arguments":{"to":"20"},"result":{"resolution":"performed"}}});
        atomic_json(&controller.join("resident-delivered-0000000000000001.json"),&receipt).unwrap();
        reconcile(&state,&controller,Some(&frame)).unwrap();
        assert!(select(&p,&state,Limits::default()).unwrap().is_none());
        assert!(!maintenance_needed(&state,"maintenance-revision").unwrap(),"empty queue does not dispatch another provider for unchanged maintenance");
        assert!(maintenance_needed(&state,"changed-program-revision").unwrap());
        fs::remove_dir_all(state).unwrap();
    }


    fn withdraw(author:&str,cell:&str,sequence:u64)->Value {
        json!({"author":author,"cell":author,"sequence":99,"height":99,"n":99,"kind":"withdraw","to":"8","reCell":cell,"reSequence":sequence})
    }
    fn statuses(state:&Path)->Vec<(String,String)> {
        notices(state).unwrap().notices.iter().map(|n|(n.author.clone(),n.status.clone())).collect()
    }

    /// A withdraw cancels the author's queued (or selected, unstarted)
    /// request; another author's withdraw, or one for a started request,
    /// changes nothing.
    #[test]fn author_withdraw_cancels_only_its_own_unstarted_requests() {
        let state=fixture("withdraw");
        let mut p=prepared(vec![entry("20",1),entry("20",2),entry("21",3)]);
        select(&p,&state,Limits::default()).unwrap();
        assert_eq!(open(&state).unwrap().selected.unwrap().entry["sequence"],1);
        // 21 withdrawing 20's request is not a withdrawal.
        p["sourceRequests"]=json!([entry("20",1),entry("20",2),entry("21",3),withdraw("21","20",2)]);
        select(&p,&state,Limits::default()).unwrap();
        assert_eq!(open(&state).unwrap().pending.len(),2);
        // 20 withdraws its queued #2 and its selected-but-unstarted #1.
        p["sourceRequests"]=json!([entry("20",1),entry("20",2),entry("21",3),withdraw("20","20",2),withdraw("20","20",1)]);
        let next=select(&p,&state,Limits::default()).unwrap().unwrap();
        assert_eq!(next["recentMemberEntries"][0]["author"],"21");
        let cancelled:Vec<_>=fs::read_dir(&state).unwrap().flatten().filter(|e|e.file_name().to_string_lossy().ends_with("-cancelled.json")).collect();
        assert_eq!(cancelled.len(),2);
        let record:Value=serde_json::from_slice(&fs::read(cancelled[0].path()).unwrap()).unwrap();
        assert_eq!(record["evidence"]["basis"],"author-withdrew");assert_eq!(record["modelRequests"],0);
        // Started: a withdraw never clears it.
        started(&state,"prompt","input").unwrap();
        p["sourceRequests"]=json!([entry("21",3),withdraw("21","21",3)]);
        select(&p,&state,Limits::default()).unwrap();
        let q=open(&state).unwrap();assert_eq!(q.selected.unwrap().entry["sequence"],3);
        fs::remove_dir_all(state).unwrap();
    }

    /// Transitions owe bounded notices (queued, started, one terminal), and
    /// a replaced assignment tells each affected author instead of silently
    /// dropping its queued request.
    #[test]fn transitions_owe_one_notice_each_and_reassignment_tells_authors() {
        let state=fixture("notices");
        let mut p=prepared(vec![entry("20",1),entry("21",2)]);
        select(&p,&state,Limits::default()).unwrap();
        select(&p,&state,Limits::default()).unwrap();
        assert_eq!(statuses(&state),[("20".into(),"queued".into()),("21".into(),"queued".into())]);
        p["requestBinding"]["assignment"]=json!("2");
        select(&p,&state,Limits::default()).unwrap();
        let all=notices(&state).unwrap().notices;
        let cancelled:Vec<_>=all.iter().filter(|n|n.status=="cancelled").collect();
        assert_eq!(cancelled.len(),2);
        assert!(cancelled.iter().all(|n|n.text.contains("assignment was replaced")));
        // The re-admitted requests under the new assignment are new identities.
        assert_eq!(all.iter().filter(|n|n.status=="queued").count(),4);
        started(&state,"prompt","input").unwrap();
        let q=open(&state).unwrap();let r=q.selected.clone().unwrap();
        record(&state,&r,"completed",json!({})).unwrap();
        record(&state,&r,"cancelled",json!({})).unwrap();
        let mine:Vec<_>=notices(&state).unwrap().notices.into_iter().filter(|n|n.identity==r.identity).map(|n|n.status).collect();
        assert_eq!(mine,["queued","started","completed"],"one terminal notice per request");
        fs::remove_dir_all(state).unwrap();
    }

    /// Publication: an unaffordable notice is skipped, an undecided one stays
    /// owed with its exact operation and is retried with the same identity,
    /// and none of it touches the request's own outcome.
    #[test]fn notice_publication_skips_unaffordable_and_retries_undecided_with_same_operation() {
        let state=fixture("publish");
        let p=prepared(vec![entry("20",1),entry("21",2),entry("20",3)]);
        select(&p,&state,Limits::default()).unwrap();
        let before=fs::read(path(&state)).unwrap();
        let mut paid=Vec::new();let mut written=Vec::new();
        let uncertain=publish_notices(&state,|op|{paid.push(op.to_owned());match op {
                "rs2"=>Published::Skipped(json!({"basis":"out of budget"})),
                _=>Published::Done(json!({"paid":true}))}},
            |op,n|{written.push((op.to_owned(),n.status.clone()));
                if op=="rs3" {Published::Uncertain("lost reply".into())} else {Published::Done(json!({"said":op}))}}).unwrap();
        assert_eq!(paid,["rs1","rs2","rs3"]);assert_eq!(uncertain,["rs3: lost reply"]);
        let states:Vec<_>=notices(&state).unwrap().notices.iter().map(|n|(n.op.clone().unwrap(),n.state.clone())).collect();
        assert_eq!(states,[("rs1".into(),"published".into()),("rs2".into(),"skipped".into()),("rs3".into(),"owed".into())]);
        let mut again=Vec::new();
        publish_notices(&state,|op|{again.push(op.to_owned());Published::Done(json!({}))},|_,_|Published::Done(json!({}))).unwrap();
        assert_eq!(again,["rs3"],"only the undecided notice re-enters, with its retained operation");
        assert_eq!(fs::read(path(&state)).unwrap(),before,"publication never changes request custody");
        fs::remove_dir_all(state).unwrap();
    }
    #[test]fn decided_maintenance_failure_clears_pending_and_keeps_revision_unsatisfied() {
        let state=fixture("maintenance-failed");let controller=state.join("controller");fs::create_dir(&controller).unwrap();fs::set_permissions(&controller,std::os::unix::fs::PermissionsExt::from_mode(0o700)).unwrap();
        let id="d".repeat(64);
        maintenance_started(&state,&id,"maintenance-revision").unwrap();
        let frame=json!({"outcome":"failed","residentOrigin":{"residentPromptId":id,"promptSha256":"b".repeat(64),"promptOperationId":1}});
        outcome(&controller,1,&id,prompt_outcome::Outcome::Undecided{retry:prompt_outcome::Retry{admin:vec!["recover".into()],operation:Some(1)},detail:"held".into()});
        reconcile(&state,&controller,Some(&frame)).unwrap();
        assert!(open(&state).unwrap().maintenance_pending.is_some(),"undecided keeps the marker");
        fs::remove_file(prompt_outcome::path(&controller,1)).unwrap();
        outcome(&controller,1,&id,prompt_outcome::Outcome::Refused{stage:prompt_outcome::RefusalStage::TurnFailure,reason:"turn failed".into()});
        reconcile(&state,&controller,Some(&frame)).unwrap();
        let q=open(&state).unwrap();assert!(q.maintenance_pending.is_none(),"decided failure clears the marker");
        assert!(maintenance_needed(&state,"maintenance-revision").unwrap(),"failed maintenance is not satisfied");
        fs::remove_dir_all(state).unwrap();
    }
}
