//! One bounded projection per iteration from current participant source tools.
//! No cached conversation/history store; exact started input stays in existing
//! request/controller custody. Display height and unrelated world movement do
//! not produce another paid invocation.
use crate::*;
const MAX_CONTEXT_DOCS:usize=8;
fn semantic_source(source:&Value)->Result<Value> {
    if source["type"]!="mini-context-document-v1"||source["authority"]!="participant-current-signed-read" {
        return Err("resident context requires current participant source projection".into());
    }
    let mut stable=source.clone();
    let fields=stable.as_object_mut().ok_or("context source not an object")?;
    fields.remove("observedHeight");
    fields.remove("readAuthorityRoot");
    Ok(stable)
}
pub(crate) fn collect(tools:&resource_tools::RoomTools<'_>,manifest:&Value)->Result<(String,Value)> {
    let name=manifest["program"]["name"].as_str().ok_or("context program name absent")?;
    let program=tools.read("mini_doc_context",&json!({"doc":name,"maxRows":"256","maxBytes":"12000"}))?;
    if program["omittedRows"].as_str()!=Some("0")||program["unavailableRows"]!=0
        || program["unsupportedRows"].as_str()!=Some("0") {
        return Err("resident program projection is incomplete; read/repair the authored source before invoking".into());
    }
    let text=program["rows"].as_array().ok_or("program context rows absent")?.iter()
        .map(|row|row["text"].as_str().ok_or_else(||"program row is not current source text".to_owned()))
        .collect::<Result<Vec<_>>>()?.join("\n");
    let docs=manifest["docs"].as_array().ok_or("context declared documents absent")?;
    if docs.len()>MAX_CONTEXT_DOCS {
        return Err("resident context exceeds8 declared documents; author a narrowed context assignment".into());
    }
    let mut sources=vec![semantic_source(&program)?];
    let mut names=std::collections::BTreeSet::from([name.to_owned()]);
    for doc in docs {
        let name=doc["name"].as_str().ok_or("declared context name absent")?;
        if !names.insert(name.to_owned()){continue;}
        // Only declared refs are read. Names/discovery never confer authority.
        let source=tools.read("mini_doc_context",&json!({"doc":name,"maxRows":"4","maxBytes":"1024"}))?;
        if source["source"]!=doc["target"] {
            return Err("resident context document reference rebound from accepted assignment".into());
        }
        sources.push(semantic_source(&source)?);
    }
    if program["source"]!=manifest["program"]["target"] {
        return Err("resident context program reference rebound from accepted assignment".into());
    }
    // Exact selected bytes/revisions, placement and summary status enter the
    // existing assignment fingerprint. No new invocation ID is minted here.
    Ok((text,json!({"type":"mini-context-bundle-v1","sources":sources})))
}
/// Keep support/dependency metadata even when row bodies are too large for the
/// framed brief. The complete projection still owns the durable fingerprint.
pub(crate) fn brief(bundle:&Value)->Result<Value> {
    if bundle["type"]!="mini-context-bundle-v1"{return Err("resident context bundle differs".into());}
    let mut compact=bundle.clone();
    let mut budget=4096usize;
    for (index,source) in compact["sources"].as_array_mut().ok_or("context sources absent")?.iter_mut().enumerate() {
        let rows=source["rows"].as_array_mut().ok_or("context rows absent")?;
        for row in rows {
            if let Some(text)=row["text"].as_str() {
                if index==0 || text.len()>budget {
                    row.as_object_mut().ok_or("context row malformed")?.remove("text");
                    row["inBrief"]=json!(false);
                } else {budget-=text.len();row["inBrief"]=json!(true);}
            }
        }
    }
    Ok(compact)
}

/// Explicit reviewed-write arguments remain authored data. The client checks
/// every selected root against independent signed current reads and constructs
/// the ordinary native intent. No model-supplied paths, capabilities or run
/// claims enter this tool; the controller supplies the operation identity.
pub(crate) fn reviewed_arguments(arguments:&Value)->Result<(String,String)> {
    let fields=arguments.as_object().ok_or("review arguments must be an object")?;
    if fields.len()!=2 || !fields.contains_key("context") || !fields.contains_key("targets") {
        return Err("review arguments require only context and targets".into());
    }
    let context=&arguments["context"];
    if context["type"]!="mini-context-bundle-v1" {
        return Err("review requires the selected context bundle".into());
    }
    let sources=context["sources"].as_array().ok_or("review context sources absent")?;
    if sources.is_empty()||sources.len()>16 {return Err("review requires1..16 source projections".into());}
    let mut names=std::collections::BTreeSet::new();
    for source in sources {
        semantic_source(source)?;
        let name=source["name"].as_str().ok_or("review source reference name absent")?;
        if !names.insert(name) {return Err("review duplicates source name".into());}
        crate::decimal(source["source"].as_str().ok_or("review source identity absent")?,"review source identity")?;
        crate::decimal(source["sourceRoot"].as_str().ok_or("review source root absent")?,"review source root")?;
    }
    let targets=arguments["targets"].as_array().ok_or("review targets absent")?;
    if targets.is_empty()||targets.len()>8 {return Err("review requires1..8 intended document writes".into());}
    for target in targets {
        let object=target.as_object().ok_or("review target must be an object")?;
        if object.len()!=2 || !object.contains_key("name") || !object.contains_key("payload") {
            return Err("review target requires name and ordinary document payload".into());
        }
        let name=target["name"].as_str().ok_or("review target name absent")?;
        if name.is_empty()||name.len()>128||name.contains(char::is_whitespace) {
            return Err("review target name differs from a declared source reference".into());
        }
        if !names.contains(name) {return Err("review write target has no selected source".into());}
        let payload=target["payload"].as_object().ok_or("review document payload absent")?;
        if payload.len()!=2 || target["payload"]["type"]!="document" {
            return Err("review accepts ordinary document actions only".into());
        }
        let actions=target["payload"]["actions"].as_array().ok_or("review actions absent")?;
        if actions.is_empty()||actions.len()>16 {return Err("review requires1..16 ordinary actions per document".into());}
    }
    let request=json!({"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":targets});
    let context=serde_json::to_string(context).map_err(|e|e.to_string())?;
    let request=serde_json::to_string(&request).map_err(|e|e.to_string())?;
    if context.len()>65_536||request.len()>16_384 {return Err("review context/request exceeds bounded tool input".into());}
    Ok((context,request))
}

/// Use the existing requests directory, without replacing any pending bytes.
/// Same operation/name accepts exactly the same authored content; a different
/// value refuses. The proposal/attempt directories remain the native custody.
pub(crate) fn retain_review_file(path:&Path,text:&str)->Result<()> {
    use std::io::{Read,Write};
    use std::os::unix::fs::{OpenOptionsExt,MetadataExt};
    let mut file=match std::fs::OpenOptions::new().write(true).create_new(true).mode(0o600).open(path) {
        Ok(file)=>file,
        Err(error) if error.kind()==std::io::ErrorKind::AlreadyExists=>{
            let mut retained=std::fs::OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW).open(path).map_err(|e|e.to_string())?;
            let metadata=retained.metadata().map_err(|e|e.to_string())?;
            if !metadata.is_file()||metadata.uid()!=unsafe{libc::geteuid()}||metadata.mode()&0o077!=0||metadata.len()!=text.len() as u64 {
                return Err("review input must be an owned private exact regular file".into());
            }
            let mut existing=Vec::with_capacity(text.len());
            retained.read_to_end(&mut existing).map_err(|e|e.to_string())?;
            if existing!=text.as_bytes(){return Err("review operation input changed; recover the original operation".into());}
            return Ok(());
        }
        Err(error)=>return Err(error.to_string())
    };
    file.write_all(text.as_bytes()).map_err(|e|e.to_string())?;
    file.sync_all().map_err(|e|e.to_string())?;
    std::fs::File::open(path.parent().ok_or("review input parent absent")?).and_then(|dir|dir.sync_all()).map_err(|e|e.to_string())
}
#[cfg(test)]
mod tests {
    use super::*;
    fn source(root:&str,height:u64)->Value {
        json!({"type":"mini-context-document-v1","authority":"participant-current-signed-read",
            "name":"notes","source":"22","sourceRoot":root,"observedHeight":height,
            "readAuthorityRoot":height.to_string(),"rows":[{"element":"4","revision":"5","parent":"6","predecessor":null,"text":"remember"}]})
    }
    #[test]
    fn projection_ignores_observation_churn_but_keeps_content_and_placement() {
        assert_eq!(semantic_source(&source("9",1)).unwrap(),semantic_source(&source("9",99)).unwrap());
        assert_ne!(semantic_source(&source("9",1)).unwrap(),semantic_source(&source("10",1)).unwrap());
        let mut moved=source("9",1);moved["rows"][0]["parent"]=json!("7");
        assert_ne!(semantic_source(&source("9",1)).unwrap(),semantic_source(&moved).unwrap());
    }
    #[test]
    fn projection_requires_native_tool_response_schema() {
        assert!(semantic_source(&json!({"type":"mini-context-document-v1","authority":"true"})).is_err());
    }
    #[test]
    fn brief_never_truncates_authored_text_or_loses_support_pin() {
        let mut s=source("9",1);s["rows"][0]["text"]=json!("x".repeat(5000));
        let v=brief(&json!({"type":"mini-context-bundle-v1","sources":[s]})).unwrap();
        assert!(v["sources"][0]["rows"][0].get("text").is_none());
        assert_eq!(v["sources"][0]["sourceRoot"],"9");
        assert_eq!(v["sources"][0]["rows"][0]["revision"],"5");
    }
    #[test]
    fn reviewed_operation_retains_exact_input_and_refuses_replacement_or_symlink() {
        let dir=std::env::temp_dir().join(format!("mini-review-input-{}",format!("{}-{}",std::process::id(),std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos())));
        std::fs::create_dir(&dir).unwrap();
        let file=dir.join("input.json");
        retain_review_file(&file,"selected-root-before").unwrap();
        retain_review_file(&file,"selected-root-before").unwrap();
        assert!(retain_review_file(&file,"selected-root-after").is_err());
        assert_eq!(std::fs::read_to_string(&file).unwrap(),"selected-root-before");
        let link=dir.join("link.json");
        std::os::unix::fs::symlink(&file,&link).unwrap();
        assert!(retain_review_file(&link,"selected-root-before").is_err());
        // These are isolated test artifacts; no shared workspace file is touched.
    }
    #[test]
    fn review_accepts_ordinary_document_actions_without_computation_or_authority_fields() {
        let args=json!({"context":{"type":"mini-context-bundle-v1","sources":[source("9",1)]},
            "targets":[{"name":"notes","payload":{"type":"document","actions":[{"type":"edit","line":1,"text":"reviewed"}]}}]});
        let (context,request)=reviewed_arguments(&args).unwrap();
        assert_eq!(serde_json::from_str::<Value>(&context).unwrap(),args["context"]);
        let request:Value=serde_json::from_str(&request).unwrap();
        assert_eq!(request["targets"],args["targets"]);
        assert!(request.get("run").is_none());
        let mut forged=args.clone();forged["run"]=json!({"output":"true"});
        assert!(reviewed_arguments(&forged).is_err());
        let mut authority=args.clone();authority["targets"][0]["capability"]=json!("1");
        assert!(reviewed_arguments(&authority).is_err());
        let mut other=args;other["targets"][0]["payload"]["type"]=json!("invoke");
        assert!(reviewed_arguments(&other).is_err());
    }

}
