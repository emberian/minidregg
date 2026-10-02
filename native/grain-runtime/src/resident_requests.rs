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
}
fn digest(value: &impl Serialize) -> Result<String> {
    sha256_bytes(&serde_json::to_vec(value).map_err(|e|e.to_string())?)
}
fn path(state: &Path) -> PathBuf { state.join("requests.json") }
fn open(state: &Path) -> Result<Queue> {
    let p=path(state);
    if !p.exists() { return Ok(Queue::default()); }
    let q:Queue=serde_json::from_slice(&bounded_regular_file(&p, MAX_STATE_BYTES)?)
        .map_err(|e|format!("resident request custody: {e}"))?;
    if q.pending.len()+usize::from(q.selected.is_some())>1024 {
        return Err("resident request custody exceeds admission limit".into());
    }
    Ok(q)
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
    Ok(())
}
fn terminal(state: &Path, request: &Request) -> Result<bool> {
    let id=digest(&request.identity)?;
    for status in ["completed","refused","cancelled"] {
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
        if let Some(fresh)=entries.iter().find(|e|same_entry(e,&r.entry)) {r.entry=fresh.clone();}
        retained.push(r);
    }
    q.pending=retained;
    if let Some(r)=&mut q.selected {
        if terminal(state,r)? {q.last_author=r.entry["author"].as_str().map(str::to_owned);q.selected=None;}
        else if !eligible(&r.entry) {record(state,r,"cancelled",json!({"basis":"source-membership-revoked"}))?;q.selected=None;}
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
        let author_count=q.pending.iter().chain(q.selected.iter()).filter(|p|p.entry["author"]==entry["author"]).count();
        if author_count>=limits.per_author || q.pending.len()+usize::from(q.selected.is_some())>=limits.pending {
            record(state,&r,"refused",json!({"basis":"bounded-admission","maxPending":limits.pending,"maxPerAuthor":limits.per_author}))?;
        } else {
            q.pending.push(r);
            if serde_json::to_vec_pretty(&q).map_err(|e|e.to_string())?.len()>MAX_STATE_BYTES-METADATA_RESERVE {
                let r=q.pending.pop().unwrap();
                record(state,&r,"refused",json!({"basis":"bounded-custody-bytes","maxStateBytes":MAX_STATE_BYTES,"metadataReserve":METADATA_RESERVE}))?;
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
pub(crate) fn started(state:&Path,prompt_id:&str,input:&str)->Result<()> {
    let mut q=open(state)?;
    if let Some(r)=q.selected.as_mut() {r.started=Some(json!({"residentPromptId":prompt_id,"inputSha256":input}));}
    else {return Err("resident prompt has no durably selected request".into());}
    atomic_json(&path(state),&q)
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
pub(crate) fn reconcile(state:&Path,controller:&Path,completion:Option<&Value>)->Result<()> {
    let mut q=open(state)?;
    let Some(r)=q.selected.as_ref() else{return Ok(())};
    if terminal(state,r)? {q.last_author=r.entry["author"].as_str().map(str::to_owned);q.selected=None;return atomic_json(&path(state),&q);}
    let Some(start)=&r.started else{return Ok(())};
    let Some(frame)=completion else{return Ok(())};
    if frame["residentOrigin"]["residentPromptId"]!=start["residentPromptId"] {return Ok(())};
    let op=frame["residentOrigin"]["promptOperationId"].as_u64().ok_or("request completion origin absent")?;
    let receipt_path=controller.join(format!("resident-delivered-{op:016}.json"));
    if !receipt_path.exists() {return Err("selected request completed without final delivery receipt; recovery required".into());}
    let receipt:Value=serde_json::from_slice(&bounded_regular_file(&receipt_path,1_048_576)?).map_err(|e|e.to_string())?;
    if receipt["type"]!="mini-resident-delivered-v1" || receipt["origin"]!=frame["residentOrigin"]
        || receipt["result"]["result"]["resolution"]!="performed"
        || receipt["result"]["expectedReply"]!=json!([r.entry["cell"],r.entry["sequence"]])
        || receipt["result"]["arguments"]["to"]!=r.entry["author"] {
        return Err("request receipt does not confirm selected source identity".into());
    }
    record(state,r,"completed",json!({"deliveryReceipt":receipt_path,"sha256":digest(&receipt)?,"origin":receipt["origin"]}))?;
    q.last_author=r.entry["author"].as_str().map(str::to_owned);q.selected=None;
    atomic_json(&path(state),&q)
}
#[cfg(test)]
mod tests {
    use super::*;
    fn fixture(tag:&str)->PathBuf {let p=std::env::temp_dir().join(format!("resident-queue-{tag}-{}",std::process::id()));fs::create_dir_all(&p).unwrap();p}
    fn entry(author:&str,n:u64)->Value {json!({"author":author,"cell":author,"sequence":n,"height":n,"n":n,"kind":"say","text":"question","to":"8"})}
    fn prepared(entries:Vec<Value>)->Value {json!({"requestBinding":{"world":{"domain":"1","expectedSeed":"2"},"roomCell":"99","assignment":"1","task":"7"},"sourceRoom":{"entries":entries.len(),"selectedEntries":entries.len(),"members":[{"subject":"20","stream":"20"},{"subject":"21","stream":"21"}]},"sourceRequests":entries,"acceptedHeight":"0","me":"8","recentMemberEntries":[]})}
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
    #[test]fn completion_recovery_requires_exact_native_delivery_and_never_zero_models_claim() {
        let state=fixture("receipt");let controller=state.join("controller");fs::create_dir(&controller).unwrap();
        let p=prepared(vec![entry("20",1),entry("21",2)]);select(&p,&state,Limits::default()).unwrap();started(&state,"source-id","input").unwrap();
        let frame=json!({"residentOrigin":{"residentPromptId":"source-id","promptOperationId":1}});
        assert!(reconcile(&state,&controller,Some(&frame)).is_err());
        let receipt=json!({"type":"mini-resident-delivered-v1","origin":frame["residentOrigin"],"result":{"expectedReply":["20",1],"arguments":{"to":"20"},"result":{"resolution":"performed"}}});
        atomic_json(&controller.join("resident-delivered-0000000000000001.json"),&receipt).unwrap();
        reconcile(&state,&controller,Some(&frame)).unwrap();reconcile(&state,&controller,Some(&frame)).unwrap();
        assert!(open(&state).unwrap().selected.is_none());
        let file=fs::read_dir(&state).unwrap().flatten().find(|e|e.file_name().to_string_lossy().ends_with("-completed.json")).unwrap().path();
        let record:Value=serde_json::from_slice(&fs::read(file).unwrap()).unwrap();assert!(record.get("modelRequests").is_none());
        assert_eq!(select(&p,&state,Limits::default()).unwrap().unwrap()["recentMemberEntries"][0]["author"],"21");
        fs::remove_dir_all(state).unwrap();
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

}
