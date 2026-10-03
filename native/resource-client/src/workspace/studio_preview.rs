//! Pure Objective source preview custody. Server configuration selects pinned
//! producers; browser input selects only this member's retained capture.
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
fn config() -> Result<Value> {
    let path=std::env::var_os(CONFIG_ENV).ok_or("Objective preview is not configured on this server")?;
    let value=bounded_json_limit(Path::new(&path), 65536)?;
    exact(&value, &["schema","bun","frontend","parser","adapter","tooling"])?;
    if value["schema"] != "mini-studio-preview-tooling-v1" { return Err("unknown Studio preview configuration".into()); }
    Ok(value)
}
pub(super) fn available() -> bool { std::env::var_os(CONFIG_ENV).is_some() }
fn admitted_capture(root:&Path, workspace:&Value, id:&str, snapshot:&str)->Result<Value> {
    let value=capture(root,workspace,id,snapshot)?;
    for source in value["sources"].as_array().ok_or("source capture missing sources")? {
        let name=member(source,"reference")?;
        let (read,_)=read_rendered(root,workspace,name,None)?;
        content_page(&read.view,name)?;
    }
    Ok(value)
}
fn child(bun:&Path, script:&Path, args:&[&Path], suffix:Option<&str>, dir:&Path, stage:&str)->Result<i32> {
    private_file(&dir.join(format!("{stage}.out")),&[])?;
    private_file(&dir.join(format!("{stage}.err")),&[])?;
    let out=fs::File::create(dir.join(format!("{stage}.out"))).map_err(|e|e.to_string())?;
    let err=fs::File::create(dir.join(format!("{stage}.err"))).map_err(|e|e.to_string())?;
    let mut command=Command::new("timeout");
    command.args(["--kill-after=2s","45s"]).arg(bun).arg(script);
    for arg in args { command.arg(arg); }
    if let Some(flag)=suffix { command.arg(flag); }
    let status=command.stdin(Stdio::null()).stdout(Stdio::from(out)).stderr(Stdio::from(err)).status().map_err(|e|format!("{stage}: {e}"))?;
    Ok(status.code().unwrap_or(125))
}
fn validate_capture(input:&Value, captured:&Value, input_sha:&str, source_hashes:&[String])->Result<()> {
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
fn validate_result(result:&Value, capture_sha:&str, input_sha:&str, tooling_sha:&str, captured:&Value)->Result<()> {
    if result["schema"]!="dregg.objective-bend.preview-result.v1" || result["binding"]["sourceRequestSha256"]!=input_sha
        || result["binding"]["captureSha256"]!=capture_sha || result["binding"]["edition"]!="objective-bend-1"
        || result["binding"]["sourceEntry"]!=captured["sourceEntry"] {return Err("preview belongs to different source/edition/entry".into());}
    if result["status"]!="refused" && (result["binding"]["toolingManifestSha256"]!=tooling_sha
        || result["preview"]["sameDecodedTerm"]!=true || result["preview"]["typing"]!="accepted by actual annotated checker") {return Err("preview lacks matched checked execution".into());}
    let cm=captured["modules"].as_array().ok_or("captured modules absent")?;
    let rm=result["binding"]["modules"].as_array().ok_or("preview module binding absent")?;
    if cm.len()!=rm.len(){return Err("preview module bindings changed".into());}
    for (a,b) in cm.iter().zip(rm) {
        if a["name"]!=b["name"] || a["sha256"]!=b["sourceSha256"] || a["astSha256"]!=b["astSha256"] || a["imports"]!=b["imports"] {return Err("preview source/AST/import binding changed".into());}
    }
    Ok(())
}
pub(super) fn run(root:&Path, workspace:&Value, id:&str, snapshot:&str, edition:&str)->Result<Value> {
    if edition!="objective-bend-1" {return Err("choose the Objective Bend edition explicitly".into());}
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
    let start=json!({"type":"mini-studio-preview-custody-v1","package":id,"snapshot":snapshot,"run":run,"subject":member(workspace,"subject")?,"edition":edition,"sourceRequestSha256":input_sha,"sourceHashes":source_hashes,"toolingSha256":cfg["tooling"]["sha256"],"status":"started"});
    atomic_json(&dir.join("started.json"),&start,None)?;
    let result=(||->Result<Value>{
        let captured_dir=dir.join("objective");
        let rc=child(&bun,&frontend,&[&input_path,&captured_dir],Some("--objective-edition-1"),&dir,"capture")?;
        if rc!=0 {let diagnostic=bounded_json_limit(&captured_dir.join("diagnostic.json"),1024*1024).unwrap_or_else(|_|json!({"stage":"objective-capture","message":format!("source capture stopped with status {rc}")}));return Ok(json!({"status":"refused","diagnostic":diagnostic}));}
        let capture_path=captured_dir.join("objective.json");let captured=bounded_json_limit(&capture_path,4*1024*1024)?;
        validate_capture(&input,&captured,&input_sha,&source_hashes)?;
        let capture_sha=sha(&capture_path)?;
        let request=json!({"schema":"dregg.objective-bend.preview-input.v1","capturePath":capture_path,"captureSha256":capture_sha,"arguments":[],"projections":[],"limits":serde_json::from_str::<Value>(LIMITS).map_err(|e|e.to_string())?});
        let request_path=dir.join("request.json");private_file(&request_path,&serde_json::to_vec(&request).map_err(|e|e.to_string())?)?;
        let output_dir=dir.join("output");let rc=child(&bun,&adapter,&[&request_path,&output_dir,&tooling],None,&dir,"preview")?;
        let path=output_dir.join(if rc==0 {"preview.json"} else {"diagnostic.json"});
        let output=bounded_json_limit(&path,4*1024*1024)?;
        validate_result(&output,&capture_sha,&input_sha,member(&cfg["tooling"],"sha256")?,&captured)?;
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
    if value["type"]!="mini-studio-preview-custody-v1" || value["package"]!=id || value["snapshot"]!=snapshot || value["run"]!=run || value["subject"]!=member(workspace,"subject")? {return Err("preview does not belong to this member/capture".into());} Ok(value)
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
}
