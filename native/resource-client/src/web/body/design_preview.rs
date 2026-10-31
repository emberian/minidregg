//! Opt-in visual fixtures: real renderers, fixture observations, no Host.
use super::*;
use serde_json::json;
use std::path::Path;

#[test]
#[ignore = "writes visual fixtures to MINI_WEB_PREVIEW"]
fn design_preview() {
    let out = PathBuf::from(std::env::var("MINI_WEB_PREVIEW").expect("MINI_WEB_PREVIEW"));
    let root = out.join("workspace");
    for dir in ["refs", "home/story", "home/requests", "bend/objects"] {
        fs::create_dir_all(root.join(dir)).unwrap();
    }
    for (name, target) in [("welcome", "11"), ("operations", "12"), ("garden", "13")] {
        fs::write(root.join(format!("refs/{name}.json")), json!({"target":target,"kind":"resource"}).to_string()).unwrap();
    }
    fs::write(root.join("home/requests/tale-invite.json"), json!({"type":"mini-story-invitation-v1","story":"tale","role":"player","author":"7","grant":{"recipient":"42"}}).to_string()).unwrap();
    fs::write(root.join("home/story/garden.json"), json!({"role":"player","author":"7","gm":"7"}).to_string()).unwrap();
    let mut site = Site {
        refs: Mutex::new(None),
        mutations: Mutex::new(()), home: Some(root.join("home")), root: root.clone(),
        workspace: Value::Null, subject: "42".into(), token: String::new(),
        front: Front { origins: vec![], read_only: true }, base: String::new(), face: Face::Body,
        shell: Some(Shell { host: "/unused".into(), config: "/unused".into(), home: root.join("home"), public_subject: Some("99".into()), front_doc: None, pool: Default::default() }),
    };
    // Use the real market parser, ordering and JSON projection for catalogue screenshots.
    // MINI_WEB_CATALOGUE is a captured upstream index, never a second production list.
    let index = std::env::var("MINI_WEB_CATALOGUE").expect("MINI_WEB_CATALOGUE: captured market index JSON");
    let entries = crate::apps::load_index(Path::new(&index)).unwrap();
    redteam::FAKE_SHELL.with(|f| *f.borrow_mut() = Some(Box::new(move |lines| {
        let line = lines.join("\n");
        let stdout = if line.starts_with("apps search") {
            let words = crate::shell::words(&line).unwrap();
            let term = words.get(2).filter(|w| !w.starts_with("--")).map(String::as_str).unwrap_or("");
            let category = words.iter().position(|w| w == "--category").and_then(|i| words.get(i+1)).map(String::as_str);
            let apps: Vec<Value> = crate::apps::search(&entries, term, category).iter().map(|e| crate::apps::entry_json(e, &crate::apps::Verdict {
                state:"unverified".into(), reason:None, raw_bytes:None, signed_app_id:None, running:0
            })).collect();
            json!({"total":entries.len(),"apps":apps}).to_string()
        } else if line.starts_with("tail") {
            "mini-s-box · backup complete\nThe world's receipts and documents are retained.\n\nmini-s-box · certifier tick\nThe latest checkpoint is available.\n".into()
        } else { String::new() };
        Ending { code: 0, stdout, stderr: String::new() }
    })));
    let mut pages = Vec::new();
    for (name, path, parts) in [("front", "/", vec![]), ("apps", "/apps", vec!["apps"]), ("apps-filtered", "/apps?q=Gogs&category=DevTools", vec!["apps"]), ("rooms", "/room", vec!["room"])] {
        let page = get(&site, &parts, path);
        pages.push(json!({"name":name,"path":path,"title":page.title,"body":page.body,"member":false}));
    }
    site.front.read_only = false;
    for (name, path, parts) in [("stories", "/story", vec!["story"]), ("programs", "/bend", vec!["bend"]), ("command", "/verb/say", vec!["verb","say"])] {
        let page = get(&site, &parts, path);
        pages.push(json!({"name":name,"path":path,"title":page.title,"body":page.body,"member":true}));
    }
    let texts = ["A small world, built together.", "Welcome to Mini. This is a place for shared documents, conversations, applications and the people and agents who make them.", "Every change has a receipt. When a rule stops a change, you can read the reason and decide what to do next."];
    let order: Vec<Value> = texts.iter().enumerate().map(|(i,t)| json!({"element":(i+2).to_string(),"parent":"1","kind":"atom","atom":(i+2).to_string(),"payload":hex(t.as_bytes()),"revision":"1","createdBy":{"subject":"7"},"struck":false,"marks":[]})).collect();
    let document = json!({"root":"1","rootRevision":"60","order":order,"transclusions":[]});
    let rendered = crate::render::render(&crate::render::View { document: &document, entries: &[], names: &std::collections::BTreeMap::new(), sources: &std::collections::BTreeMap::new(), me: "42" }).unwrap();
    pages.push(json!({"name":"reader","path":"/doc/welcome","title":"Welcome to Mini","body":rendered.html("welcome"),"member":false}));
    pages.push(json!({"name":"resident","path":"/room/garden/resident","title":"Resident work in garden","body":super::super::resident::tools_html("garden",Some("3"),Some("60"),Some("42"),"42",true),"member":true}));
    let refusal = outcome_html(&Ending { code: 3, stdout: String::new(), stderr: "refused: oracle-not-granted: this room has not granted the Oracle tool".into() }, &[("Review room permissions", "/room/garden/resident#hermes-tools")]);
    pages.push(json!({"name":"refusal","path":"/receipts/w-1","title":"Attempt w-1","body":refusal,"member":true}));
    // The real front-page composition with the same document renderer as the reader.
    site.front.read_only = true;
    let welcome = Page { status: 200, title: "Welcome to Mini".into(), stamp: Stamp::None, body: rendered.html("welcome") };
    let front = public_front_with_welcome(&site, Some(welcome));
    pages[0] = json!({"name":"front","path":"/","title":front.title,"body":front.body,"member":false});
    fs::write(out.join("pages.json"), serde_json::to_vec_pretty(&pages).unwrap()).unwrap();
    redteam::FAKE_SHELL.with(|f| *f.borrow_mut() = None);
}
