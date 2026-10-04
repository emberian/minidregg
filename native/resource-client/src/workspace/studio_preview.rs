//! Pure Objective source preview custody. Server configuration selects pinned
//! producers; browser input selects only this member's retained capture and its
//! typed argument values. One wire edition: preview-input.v2 / preview-result.v2
//! (typed-values-v1 arguments). The v1 wire is deleted; a v1 configuration,
//! request or result refuses to load.
use super::*;
use std::process::{Command, Stdio};

const CONFIG_ENV: &str = "MINIDREGG_STUDIO_PREVIEW_CONFIG";
const LIMITS: &str = r#"{"ticks":"4096","heap":"8192","stack":"1024","typeFuel":"4096"}"#;

fn sha(path: &Path) -> Result<String> { crate::host_image_sha256(path) }
fn checked_path(config: &Value, name: &str) -> Result<PathBuf> {
    let path=PathBuf::from(member(&config[name], "path")?);
    if sha(&path)? != member(&config[name], "sha256")? { return Err(format!("configured {name} changed")); }
    Ok(path)
}
const CONFIG_SCHEMA: &str = "mini-studio-preview-tooling-v2";
const REQUEST_SCHEMA: &str = "dregg.objective-bend.preview-input.v2";
const RESULT_SCHEMA: &str = "dregg.objective-bend.preview-result.v2";
const TYPED_SCHEMA: &str = "dregg.objective-bend.typed-preview.v2";
const ARGUMENT_ENCODING: &str = "typed-values-v1";
const CUSTODY: &str = "mini-studio-preview-custody-v2";

fn config() -> Result<Value> {
    let path=std::env::var_os(CONFIG_ENV).ok_or("Objective preview is not configured on this server")?;
    let value=bounded_json_limit(Path::new(&path), 65536)?;
    exact(&value, &["schema","bun","frontend","parser","adapter","tooling"])?;
    if value["schema"] != CONFIG_SCHEMA { return Err("unknown Studio preview configuration".into()); }
    Ok(value)
}
pub(super) fn available() -> bool { std::env::var_os(CONFIG_ENV).is_some() }
fn arguments(text:&str)->Result<Value>{
    if text.len()>16384{return Err("preview arguments exceed 16KiB".into());}
    let value:Value=serde_json::from_str(text).map_err(|e|format!("invalid argument JSON: {e}"))?;
    let values=value.as_array().ok_or("preview arguments must be an array")?;
    if values.len()>16{return Err("at most 16 preview arguments".into());}
    let mut budget=256usize;
    fn check(value:&Value,depth:usize,budget:&mut usize)->Result<()>{
        if depth>8 || *budget==0{return Err("preview argument nesting/size exceeds bound".into());}*budget-=1;
        match member(value,"tag")? {
            "natural"=>{exact(value,&["tag","value"])?;let n=member(value,"value")?;if n.len()>128 || n.is_empty() || !n.bytes().all(|b|b.is_ascii_digit()) || (n.len()>1 && n.starts_with('0')) {return Err("natural argument must be canonical decimal bytes".into());}},
            "boolean"=>{exact(value,&["tag","value"])?;if !value["value"].is_boolean(){return Err("boolean argument requires true or false".into());}},
            "label"=>{exact(value,&["tag","value"])?;let v=member(value,"value")?;if v.len()>4096 || v.contains('\0'){return Err("label argument exceeds bound or contains NUL".into());}},
            "record"=>{exact(value,&["tag","fields"])?;let fields=value["fields"].as_array().ok_or("record argument requires fields")?;if fields.len()>64{return Err("record argument has too many fields".into());}let mut names=std::collections::BTreeSet::new();for f in fields {exact(f,&["name","value"])?;let name=member(f,"name")?;if name.len()>256 || name.contains('\0') || !names.insert(name){return Err("record argument needs distinct bounded names".into());}check(&f["value"],depth+1,budget)?;}},
            _=>return Err("unsupported typed argument tag".into())
        }Ok(())
    }
    for value in values {check(value,0,&mut budget)?;}Ok(value)
}
fn validate_reference(source:&Value,current:&Value)->Result<()>{
    if member(&source["referenceBinding"],"target")? != member(current,"target")? {return Err("source reference now names a different resource; retained capture stays locked".into());}Ok(())
}
pub(super) fn admitted_capture(root:&Path, workspace:&Value, id:&str, snapshot:&str)->Result<Value> {
    let value=capture(root,workspace,id,snapshot)?;
    for source in value["sources"].as_array().ok_or("source capture missing sources")? {
        let name=member(source,"reference")?;
        validate_reference(source,&reference(root,name)?)?;
        let (read,_)=read_rendered(root,workspace,name,None)?;
        content_page(&read.view,name)?;
    }
    Ok(value)
}
fn child(bun:&Path, script:&Path, args:&[&Path], suffix:Option<&str>, dir:&Path, stage:&str)->Result<i32> {
    create_private(&dir.join(format!("{stage}.out")),&[])?;
    create_private(&dir.join(format!("{stage}.err")),&[])?;
    let out=fs::File::create(dir.join(format!("{stage}.out"))).map_err(|e|e.to_string())?;
    let err=fs::File::create(dir.join(format!("{stage}.err"))).map_err(|e|e.to_string())?;
    let mut command=Command::new("timeout");
    command.args(["--kill-after=2s","45s"]).arg(bun).arg(script);
    for arg in args { command.arg(arg); }
    if let Some(flag)=suffix { command.arg(flag); }
    let status=command.stdin(Stdio::null()).stdout(Stdio::from(out)).stderr(Stdio::from(err)).status().map_err(|e|format!("{stage}: {e}"))?;
    Ok(status.code().unwrap_or(125))
}
pub(super) fn validate_capture(input:&Value, captured:&Value, input_sha:&str, source_hashes:&[String])->Result<()> {
    if captured["schema"]!="dregg.objective-bend.captured-package.v1" || captured["edition"]!="objective-bend-1" || captured["requestSha256"]!=input_sha
        || captured["entryModule"]!=input["entryModule"] || captured["entryDefinition"]!=input["entryDefinition"] {return Err("Objective capture differs from selected source/edition/entry".into());}
    let old=input["modules"].as_array().ok_or("source modules absent")?;
    let new=captured["modules"].as_array().ok_or("captured modules absent")?;
    if old.len()!=new.len() || old.len()!=source_hashes.len() {return Err("captured module order changed".into());}
    for (i,(a,b)) in old.iter().zip(new).enumerate() {
        if a["name"]!=b["name"] || b["sha256"]!=source_hashes[i] {return Err("captured source bytes changed".into());}
        let ai=a["imports"].as_array().ok_or("source imports absent")?;
        let bi=b["imports"].as_array().ok_or("captured imports absent")?;
        if ai.len()!=bi.len() {return Err("captured imports changed".into());}
        for (x,y) in ai.iter().zip(bi) { if x["alias"]!=y["alias"] || x["module"]!=y["module"] {return Err("captured import binding changed".into());} }
    }
    Ok(())
}
fn validate_result(result:&Value, capture_sha:&str, input_sha:&str, tooling_sha:&str, captured:&Value,request_sha:&str)->Result<()> {
    let (schema,typed)=(RESULT_SCHEMA,TYPED_SCHEMA);
    if result["binding"]["previewRequestSha256"]!=request_sha {return Err("preview argument/limit request binding changed".into());}
    if !matches!(result["status"].as_str(),Some("finished"|"suspended"|"divergent"|"refused")){return Err("unknown preview outcome".into());}
    if result["schema"]!=schema || result["binding"]["sourceRequestSha256"]!=input_sha
        || result["binding"]["captureSha256"]!=capture_sha || result["binding"]["edition"]!="objective-bend-1"
        || result["binding"]["sourceEntry"]!=captured["sourceEntry"] {return Err("preview belongs to different source/edition/entry".into());}
    if result["status"]!="refused" && (result["preview"]["status"]!=result["status"] || result["binding"]["toolingManifestSha256"]!=tooling_sha
        || result["preview"]["schema"]!=typed || result["preview"]["sameDecodedTerm"]!=true || result["preview"]["typing"]!="accepted by actual annotated checker") {return Err("preview lacks matched checked execution".into());}
    let cm=captured["modules"].as_array().ok_or("captured modules absent")?;
    let rm=result["binding"]["modules"].as_array().ok_or("preview module binding absent")?;
    if cm.len()!=rm.len(){return Err("preview module bindings changed".into());}
    for (a,b) in cm.iter().zip(rm) {
        if a["name"]!=b["name"] || a["sha256"]!=b["sourceSha256"] || a["astSha256"]!=b["astSha256"] || a["imports"]!=b["imports"] {return Err("preview source/AST/import binding changed".into());}
    }
    Ok(())
}
pub(super) fn run(root:&Path, workspace:&Value, id:&str, snapshot:&str, edition:&str,args:&str)->Result<Value> {
    if edition!="objective-bend-1" {return Err("choose the Objective Bend edition explicitly".into());}
    let args=arguments(args)?;
    admitted_capture(root,workspace,id,snapshot)?;
    let cfg=config()?;
    let bun=checked_path(&cfg,"bun")?;let frontend=checked_path(&cfg,"frontend")?;
    checked_path(&cfg,"parser")?;let adapter=checked_path(&cfg,"adapter")?;let tooling=checked_path(&cfg,"tooling")?;
    let source=directory(root,id)?.join(snapshot);
    let input_path=source.join("package-input.json");let input=bounded_json_limit(&input_path,MAX_PROJECT as u64)?;let input_sha=sha(&input_path)?;
    let source_hashes=input["modules"].as_array().ok_or("source modules absent")?.iter().enumerate().map(|(i,m)|{
        let expected=source.join(format!("module-{i}.bend"));
        if Path::new(member(m,"sourcePath")?)!=expected {return Err("capture module path differs".into());} sha(&expected)
    }).collect::<Result<Vec<_>>>()?;
    let parent=source.join("previews");
    if !parent.exists(){make_private_dir(&parent)?;}else{private_dir(&parent)?;}
    let run=token()?;let dir=parent.join(&run);make_private_dir(&dir)?;
    let start=json!({"type":CUSTODY,"package":id,"snapshot":snapshot,"run":run,"subject":member(workspace,"subject")?,"edition":edition,"arguments":args,"sourceRequestSha256":input_sha,"sourceHashes":source_hashes,"toolingSha256":cfg["tooling"]["sha256"],"status":"started"});
    atomic_json(&dir.join("started.json"),&start,None)?;
    let result=(||->Result<Value>{
        let captured_dir=dir.join("objective");
        let rc=child(&bun,&frontend,&[&input_path,&captured_dir],Some("--objective-edition-1"),&dir,"capture")?;
        if rc!=0 {let diagnostic=bounded_json_limit(&captured_dir.join("diagnostic.json"),1024*1024).unwrap_or_else(|_|json!({"stage":"objective-capture","message":format!("source capture stopped with status {rc}")}));return Ok(json!({"status":"refused","diagnostic":diagnostic}));}
        let capture_path=captured_dir.join("objective.json");let captured=bounded_json_limit(&capture_path,4*1024*1024)?;
        validate_capture(&input,&captured,&input_sha,&source_hashes)?;
        let capture_sha=sha(&capture_path)?;
        let request=json!({"schema":REQUEST_SCHEMA,"capturePath":capture_path,"captureSha256":capture_sha,"arguments":args,"argumentEncoding":ARGUMENT_ENCODING,"projections":[],"limits":serde_json::from_str::<Value>(LIMITS).map_err(|e|e.to_string())?});
        let request_path=dir.join("request.json");create_private(&request_path,&serde_json::to_vec(&request).map_err(|e|e.to_string())?)?;
        let output_dir=dir.join("output");let rc=child(&bun,&adapter,&[&request_path,&output_dir,&tooling],None,&dir,"preview")?;
        let path=output_dir.join(if rc==0 {"preview.json"} else {"diagnostic.json"});
        let output=bounded_json_limit(&path,4*1024*1024)?;
        validate_result(&output,&capture_sha,&input_sha,member(&cfg["tooling"],"sha256")?,&captured,&sha(&request_path)?)?;
        Ok(output)
    })();
    let mut record=start;
    match result { Ok(output)=>{record["status"]=output["status"].clone();record["result"]=output;},Err(error)=>{record["status"]=json!("unavailable");record["diagnostic"]=json!({"stage":"studio-preview-receiver","message":error});} }
    atomic_json(&dir.join("result.json"),&record,None)?;
    atomic_json(&dir.join("status.json"),&json!({"run":run,"status":record["status"]}),None)?;
    Ok(record)
}
pub(super) fn load(root:&Path,workspace:&Value,id:&str,snapshot:&str,run:&str)->Result<Value>{
    admitted_capture(root,workspace,id,snapshot)?;directory(root,run)?;
    let dir=directory(root,id)?.join(snapshot).join("previews").join(run);
    let value=if dir.join("result.json").exists(){bounded_json_limit(&dir.join("result.json"),4*1024*1024)?}else{
        let mut started=bounded_json_limit(&dir.join("started.json"),MAX_PROJECT as u64)?;
        started["status"]=json!("unavailable");started["diagnostic"]=json!({"stage":"studio-preview-custody","message":"No finished result is retained. This preview may have been interrupted; the captured source remains available."});started
    };
    if value["type"]!=CUSTODY || value["package"]!=id || value["snapshot"]!=snapshot || value["run"]!=run || value["subject"]!=member(workspace,"subject")? {return Err("preview does not belong to this member/capture".into());}
    if value["result"]["binding"]["previewRequestSha256"].is_string(){
        let input_path=dir.parent().and_then(Path::parent).ok_or("invalid preview custody path")?.join("package-input.json");
        let input=bounded_json_limit(&input_path,MAX_PROJECT as u64)?;
        let input_sha=sha(&input_path)?;
        let hashes=input["modules"].as_array().ok_or("source modules absent")?.iter().enumerate().map(|(i,m)|{
            let expected=input_path.parent().ok_or("invalid source directory")?.join(format!("module-{i}.bend"));
            if Path::new(member(m,"sourcePath")?)!=expected {return Err("capture module path differs".into());}sha(&expected)
        }).collect::<Result<Vec<_>>>()?;
        let captured_path=dir.join("objective/objective.json");
        let captured=bounded_json_limit(&captured_path,4*1024*1024)?;
        validate_capture(&input,&captured,&input_sha,&hashes)?;
        let request_path=dir.join("request.json");let request=bounded_json_limit(&request_path,65536)?;
        if request["schema"]!=REQUEST_SCHEMA || request["argumentEncoding"]!=ARGUMENT_ENCODING || request["arguments"]!=value["arguments"] || request["projections"]!=json!([]) || request["limits"]!=serde_json::from_str::<Value>(LIMITS).map_err(|e|e.to_string())? {return Err("retained preview request differs from custody".into());}
        validate_result(&value["result"],&sha(&captured_path)?,&input_sha,member(&value,"toolingSha256")?,&captured,&sha(&request_path)?)?;
    }
    Ok(value)
}
pub(super) fn runs(root:&Path,workspace:&Value,id:&str,snapshot:&str)->Result<Vec<Value>> {
    admitted_capture(root,workspace,id,snapshot)?;
    let parent=directory(root,id)?.join(snapshot).join("previews");
    if !parent.exists(){return Ok(Vec::new());}
    let mut entries=fs::read_dir(&parent).map_err(|e|e.to_string())?.take(257).collect::<std::io::Result<Vec<_>>>().map_err(|e|e.to_string())?;
    if entries.len()>256{return Err("preview history exceeds its listing bound".into());}
    entries.sort_by_key(|e|e.file_name());
    let mut values=Vec::new();
    for entry in entries.into_iter().rev().take(32) {
        let run=entry.file_name().to_string_lossy().into_owned();directory(root,&run)?;
        let status=bounded_json_limit(&entry.path().join("status.json"),4096).unwrap_or_else(|_|json!({"run":run,"status":"started"}));
        values.push(json!({"run":run,"status":status["status"]}));
    }
    Ok(values)
}

#[cfg(test)] mod tests {
    use super::*;
    #[test] fn source_preview_rejects_substituted_entry_and_bytes(){
        let input=json!({"entryModule":"0","entryDefinition":"run","modules":[{"name":"A","imports":[]}]});
        let good=json!({"schema":"dregg.objective-bend.captured-package.v1","edition":"objective-bend-1","requestSha256":"request","entryModule":"0","entryDefinition":"run","modules":[{"name":"A","sha256":"source","imports":[]}]});
        assert!(validate_capture(&input,&good,"request",&["source".into()]).is_ok());
        let mut wrong=good.clone();wrong["entryDefinition"]=json!("other");assert!(validate_capture(&input,&wrong,"request",&["source".into()]).is_err());
        assert!(validate_capture(&input,&good,"request",&["different".into()]).is_err());
    }
    #[test] fn preview_v2_arguments_preserve_types_and_reject_ambiguity(){
        assert!(arguments(r#"[{"tag":"label","value":"true"},{"tag":"boolean","value":true},{"tag":"natural","value":"42"}]"#).is_ok());
        for text in [r#"[{"tag":"natural","value":"042"}]"#,r#"[{"tag":"boolean","value":"true"}]"#,r#"[{"tag":"record","fields":[{"name":"x","value":{"tag":"natural","value":"1"}},{"name":"x","value":{"tag":"natural","value":"2"}}]}]"#,r#"[{"tag":"label","value":"x","authority":true}]"#] {assert!(arguments(text).is_err());}
    }
    #[test] fn preview_v2_result_rejects_changed_wire_or_argument_request(){
        let capture=json!({"sourceEntry":"A.run","modules":[]});
        let output=json!({"schema":"dregg.objective-bend.preview-result.v2","status":"finished","binding":{"previewRequestSha256":"request","sourceRequestSha256":"source","captureSha256":"capture","edition":"objective-bend-1","sourceEntry":"A.run","toolingManifestSha256":"tooling","modules":[]},"preview":{"schema":"dregg.objective-bend.typed-preview.v2","status":"finished","sameDecodedTerm":true,"typing":"accepted by actual annotated checker"}});
        assert!(validate_result(&output,"capture","source","tooling",&capture,"request").is_ok());
        assert!(validate_result(&output,"capture","source","tooling",&capture,"changed arguments").is_err());
        let mut retired=output.clone();retired["schema"]=json!("dregg.objective-bend.preview-result.v1");
        assert!(validate_result(&retired,"capture","source","tooling",&capture,"request").is_err());
    }

    #[test] fn source_capture_retarget_does_not_authorize_retained_bytes(){
        let source=json!({"referenceBinding":{"target":"A","observeCapability":"old"}});
        assert!(validate_reference(&source,&json!({"target":"A","observeCapability":"rotated"})).is_ok());
        assert!(validate_reference(&source,&json!({"target":"B","observeCapability":"readable"})).is_err());
        assert!(validate_reference(&source,&json!({"observeCapability":"readable"})).is_err());
    }

}
