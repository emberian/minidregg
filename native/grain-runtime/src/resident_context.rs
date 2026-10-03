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
}
