//! Discord presentation of the shared `home --json` member projection.
//! Commands and resource names come from that participant's native client; this
//! module grants no authority and never interprets an action label as execution.
use serde_json::Value;
use crate::reply;

pub fn home_line(target: Option<&str>) -> Result<String,String> {
    match target.filter(|s|!s.is_empty()) {
        None=>Ok("home --json".into()),
        Some(s) if s.len()<=160 && s.split('/').all(|p| p.as_bytes().first().is_some_and(u8::is_ascii_alphanumeric) && p.bytes().all(|b|b.is_ascii_alphanumeric() || matches!(b,b'-'|b'_'))) => Ok(format!("home {s} --json")),
        _=>Err("target must be a held Mini resource name, optionally ROOM/NAME".into()),
    }
}
fn text(v:&Value)->String {v.as_str().map(str::to_owned).unwrap_or_else(||v.to_string())}
fn actions(lines:&mut Vec<String>,v:&Value){
    for a in v.as_array().into_iter().flatten(){
        if let Some(cmd)=a["command"].as_str(){lines.push(format!("  {} → /mini line:{}",a["label"].as_str().unwrap_or("open"),cmd));}
    }
}
pub fn render(stdout:&str,page:usize)->Result<String,String>{
    let v:Value=serde_json::from_str(stdout).map_err(|_|"native home projection was not JSON")?;
    if v["type"]!="mini-member-workspace-v1" {return Err("native home projection type differs".into())}
    let mut lines=vec![format!("Mini · subject {} · {}",text(&v["subject"]),text(&v["currentness"]))];
    if let Some(o)=v.get("observation") {lines.push(format!("Source target {} · height {} · root {}",text(&o["target"]),text(&o["height"]),text(&o["resourceRoot"])));}
    for r in v["resources"].as_array().into_iter().flatten(){
        let name=r["name"].as_str().unwrap_or("?");
        lines.push(format!("\n{name} · {} {}",if r["room"]==true {"room"} else {r["kind"].as_str().unwrap_or("resource")},text(&r["target"])));
        lines.push(format!("  /mini-world target:{name}"));
        actions(&mut lines,&r["actions"]);
    }
    if let Some(o)=v.get("object") {lines.push(format!("Object {} · revision {}",text(&o["type"]),text(&o["descriptor"]["revision"])));}
    if let Some(r)=v.get("resident") {lines.push(format!("Resident {} · request {}",text(&r["subject"]),text(&r["requestStatus"]["status"])));}
    for (key,label) in [("recovery","Retained activity"),("documentExports","Document export"),("appLifecycles","App lifecycle")] {
        for r in v[key].as_array().into_iter().flatten(){
            lines.push(format!("{label} {} · {}",text(&r["id"]),text(r.get("status").or_else(||r.get("phase")).unwrap_or(&Value::Null))));
            actions(&mut lines,&r["actions"]);
        }
    }
    actions(&mut lines,&v["actions"]);
    lines.push("Discovery is this session's held references. Open a target for a current signed check. Actions run under current Mini rules; copy a command into /mini. Same session: home NAME over SSH or the member web entrance.".into());
    // Split all content, rather than silently losing resource/action rows at 2000 chars.
    let text=lines.join("\n");let chars:Vec<char>=text.chars().collect();let pages=chars.len().div_ceil(1650).max(1);
    if page==0 || page>pages{return Err(format!("page must be 1..{pages}"))}
    let body: String=chars.iter().skip((page-1)*1650).take(1650).collect();
    Ok(reply::code_block(&format!("{body}\n\nPage {page}/{pages} · /mini-world with the same target and page:{}",(page+1).min(pages))))
}
#[cfg(test)] mod tests {
    use super::*;
    #[test] fn names_never_become_shell_syntax(){assert!(home_line(Some("lab/notes")).is_ok());for s in ["../x","lab;submit p","a\nb","--json","a//b"]{assert!(home_line(Some(s)).is_err(),"{s}");}}
    #[test] fn source_actions_and_all_pages_are_retained(){
        let rows:Vec<_>=(0..50).map(|i|serde_json::json!({"name":format!("held-{i}"),"kind":"object","target":i,"actions":[{"label":"source","command":format!("doc show held-{i}")}]})).collect();
        let s=serde_json::json!({"type":"mini-member-workspace-v1","subject":"7","currentness":"discovery-only","resources":rows}).to_string();
        let mut all=String::new();for p in 1..100{match render(&s,p){Ok(s)=>{assert!(s.chars().count()<=2000);all+=&s},Err(_)=>break}}
        assert!(all.contains("doc show held-49"));assert!(!all.contains("foreign"));
    }
}
