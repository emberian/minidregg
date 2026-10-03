//! Ordinary module documents compose a source workspace. Editing/history stay
//! on existing signed document routes; compiler/publication results are absent
//! until the real producer supplies them, never inferred from draft metadata.
use super::*;
use crate::workspace::studio::{self, Manifest};
use serde_json::json;

const EXAMPLE: &str = r#"{"entryModule":"0","entryDefinition":"remember","modules":[{"name":"Notebook","reference":"source-module","imports":[]}]}"#;

pub(super) fn index(site: &Site) -> Page {
    match studio::projects(&site.root,&site.workspace) {
        Err(error)=>failure_page("Source studio",&error),
        Ok(projects)=>Page {status:200,title:"Source studio".into(),stamp:Stamp::None,
            body:format!("<p>Author modules as documents, compose their imports, and retain source revisions.</p><p><a href=\"{}/studio/new\">New source package</a> | <a href=\"{}/new-document\">Create a module document</a></p><ul>{}</ul>",site.base(),site.base(),projects.iter().map(|p|format!("<li><a href=\"{}/studio/{}\">{}</a></li>",site.base(),escape(p["id"].as_str().unwrap_or("")),escape(p["title"].as_str().unwrap_or("Source package")))).collect::<String>())}
    }
}
pub(super) fn new(site: &Site) -> Page {
    Page {status:200,title:"New source package".into(),stamp:Stamp::None,
        body:format!("<p>Start from an ordinary source document, then add modules and their imports.</p><form method=post action=\"{}/studio/new\"><label>Package title<input name=title required maxlength=16384></label><label>Module name<input name=name required value=Notebook maxlength=16384></label><label>Source document reference<input name=reference required maxlength=16384></label><label>Entry definition<input name=definition required value=remember maxlength=16384></label><button>Create source workspace</button></form><p><a href=\"{}/new-document\">Create a source module document first</a></p><details><summary>Import an ordered composition manifest</summary><form method=post action=\"{}/studio/new\"><label>Title<input name=title required></label><label>Composition<textarea name=manifest required rows=16>{}</textarea></label><button>Import composition</button></form></details>",site.base(),site.base(),site.base(),escape(EXAMPLE))}
}
pub(super) fn package(site: &Site, id: &str) -> Page {
    match studio::load(&site.root, &site.workspace, id) {
        Ok(value) => render(site, &value, ""),
        Err(error) => failure_page("Source package", &error),
    }
}
fn render(site: &Site, value: &Value, message: &str) -> Page {
    let manifest = match Manifest::parse(&value["manifest"]) {
        Ok(m) => m,
        Err(e) => return failure_page("Source package", &e),
    };
    let id = value["id"].as_str().unwrap_or("");
    let base = format!("{}/studio/{id}", site.base());
    let mut body=format!("<p><a href=\"{}/studio\">All source packages</a> | <a href=\"{}/new-document\">Add a module document</a></p><p class=note>{}</p><p>Entry: <code>{}.{}</code>; composition revision <code>{}</code>.</p><section><h2>Modules and imports</h2><ol>",site.base(),site.base(),escape(message),escape(&manifest.modules[manifest.entry_module].name),escape(&manifest.entry_definition),escape(value["revision"].as_str().unwrap_or("?")));
    for (index, module) in manifest.modules.iter().enumerate() {
        let imports = module
            .imports
            .iter()
            .map(|i| {
                format!(
                    "{} → {}",
                    if i.alias.is_empty() { "Base" } else { &i.alias },
                    manifest.modules[i.module].name
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        body.push_str(&format!("<li><strong>{}</strong> <code>{}</code><p>{}</p><a href=\"{base}/module/{index}\">Edit source</a> | <a href=\"{}/doc/{}/inspect\">Source and history</a> | <a href=\"{base}/module/{index}/fresh\">Open current source in a new draft</a></li>",escape(&module.name),escape(&module.reference),escape(&imports),site.base(),escape(&module.reference)));
    }
    body.push_str("</ol></section>");
    body.push_str(&composition_controls(site, value, &manifest));
    body.push_str(&format!("<details><summary>Edit package composition</summary><form method=post action=\"{base}/manifest\"><input type=hidden name=revision value=\"{}\"><label>Ordered modules, imports and entry<textarea name=manifest required maxlength=65536 rows=18>{}</textarea></label><button>Save composition draft</button></form></details><section><h2>Preview and publish</h2><p>Save your module edits before capturing source. Each capture opens the saved documents with your current access and keeps their exact revisions.</p><form method=post action=\"{base}/snapshot\"><button>Capture saved source for preview</button></form><p data-preview-state=unavailable>Compiler preview is unavailable. Your source documents and composition draft remain editable.</p><button disabled>Publish source</button> <button disabled>Instantiate prototype</button> <button disabled>Evolve instance</button><p>These actions become available with a prepared native operation and its exact source preview.</p></section>",escape(value["revision"].as_str().unwrap_or("")),escape(&serde_json::to_string_pretty(&value["manifest"]).unwrap_or_default())));
    let prototype = value
        .get("prototype")
        .cloned()
        .unwrap_or_else(studio::empty_declaration);
    body.push_str(&format!("<section><h2>Prototype requirements and provisions</h2><p>Declare ordered parent identities, required final-self or prior-super selectors, and source entries provided by this module. Reflection and linking will check these declarations against your captured source.</p><form method=post action=\"{base}/prototype\"><input type=hidden name=revision value=\"{}\"><label>Partial declaration<textarea name=declaration required rows=18 maxlength=65536>{}</textarea></label><button>Save prototype declaration</button></form><p>Publication and construction remain unavailable until the actual emitted Book and canonical Partial preview are produced.</p></section>",escape(value["revision"].as_str().unwrap_or("")),escape(&serde_json::to_string_pretty(&prototype).unwrap_or_default())));
    if let Some(editors) = value["editors"].as_array() {
        if !editors.is_empty() {
            body.push_str("<section><h2>Retained source drafts</h2><ul>");
            for e in editors.iter().rev().take(32) {
                body.push_str(&format!(
                    "<li><a href=\"{}/doc/{}/edit/{}\">{}</a></li>",
                    site.base(),
                    escape(e["reference"].as_str().unwrap_or("")),
                    escape(e["edit"].as_str().unwrap_or("")),
                    escape(e["name"].as_str().unwrap_or("Source"))
                ));
            }
            body.push_str("</ul></section>");
        }
    }
    if let Some(captures) = value["snapshots"].as_array() {
        if !captures.is_empty() {
            body.push_str("<section><h2>Retained source snapshots</h2>");
            for c in captures.iter().rev().take(8) {
                body.push_str(&format!("<details><summary>Composition {} / snapshot {}</summary><p>Retained source roots; this capture has no publication or compiler result.</p><ul>",escape(c["revision"].as_str().unwrap_or("?")),escape(c["id"].as_str().unwrap_or("?"))));
                if let Some(sources) = c["sources"].as_array() {
                    for source in sources.iter().take(256) {
                        body.push_str(&format!(
                            "<li>{} — height {}, source root {}</li>",
                            escape(source["name"].as_str().unwrap_or("Module")),
                            escape(source["height"].as_str().unwrap_or("?")),
                            short(source["cellRoot"].as_str().unwrap_or("?"))
                        ));
                    }
                }
                body.push_str(&format!("</ul><a href=\"{base}/snapshot/{}\">Inspect retained source roots</a></details>",escape(c["id"].as_str().unwrap_or(""))));
                body.push_str(&preview_form(site,id,c["id"].as_str().unwrap_or("")));
            }
            body.push_str("</section>");
        }
    }
    if studio::preview_available() {
        body=body.replace("Compiler preview is unavailable. Your source documents and composition draft remain editable.","Run a retained source capture below to inspect its type, result or source diagnostics.").replace("data-preview-state=unavailable","data-preview-state=ready");
    }
    Page {
        status: 200,
        title: value["title"].as_str().unwrap_or("Source package").into(),
        stamp: Stamp::None,
        body,
    }
}
fn composition_controls(site: &Site, value: &Value, manifest: &Manifest) -> String {
    let base = format!(
        "{}/studio/{}",
        site.base(),
        value["id"].as_str().unwrap_or("")
    );
    let revision = escape(value["revision"].as_str().unwrap_or(""));
    let form = |operation: &str| {
        format!("<form method=post action=\"{base}/compose\"><input type=hidden name=revision value=\"{revision}\"><input type=hidden name=operation value=\"{operation}\">")
    };
    let options = manifest
        .modules
        .iter()
        .enumerate()
        .map(|(i, m)| format!("<option value=\"{i}\"{}>{}</option>", if i == manifest.entry_module { " selected" } else { "" }, escape(&m.name)))
        .collect::<String>();
    let mut body=format!("<section><h2>Compose modules</h2>{}<label>Module name<input name=name required></label><label>Source document reference<input name=reference required></label><button>Add module</button></form>{}<label>Entry module<select name=module>{options}</select></label><label>Entry definition<input name=definition required value=\"{}\"></label><button>Select entry</button></form>",form("add-module"),form("entry"),escape(&manifest.entry_definition));
    for (i, module) in manifest.modules.iter().enumerate().skip(1) {
        let earlier = manifest
            .modules
            .iter()
            .enumerate()
            .take(i)
            .map(|(j, m)| format!("<option value=\"{j}\">{}</option>", escape(&m.name)))
            .collect::<String>();
        body.push_str(&format!("<details><summary>Imports for {}</summary>{}<input type=hidden name=module value=\"{i}\"><label>Earlier module<select name=dependency>{earlier}</select></label><label>Alias<input name=alias maxlength=16384></label><p>Leave the alias empty only for Base.</p><button>Add import</button></form>",escape(&module.name),form("add-import")));
        for (edge, import) in module.imports.iter().enumerate() {
            body.push_str(&format!("{}<input type=hidden name=module value=\"{i}\"><input type=hidden name=import value=\"{edge}\"><span>{} → {}</span><button>Remove import</button></form>",form("remove-import"),escape(&import.alias),escape(&manifest.modules[import.module].name)));
        }
        body.push_str("</details>");
    }
    body.push_str(&format!("</section><section><h2>Composition history and forks</h2><p><a href=\"{base}/history/{revision}\">Inspect this composition revision</a></p><form method=post action=\"{base}/fork\"><input type=hidden name=revision value=\"{revision}\"><label>Fork title<input name=title required value=\"{} fork\"></label><button>Fork composition</button></form><p>A composition fork keeps these document references. Source edits still use each document's current access.</p></section>",escape(value["title"].as_str().unwrap_or("Source"))));
    body
}
pub(super) fn history(site: &Site, id: &str, revision: &str) -> Page {
    match studio::manifest_version(&site.root, &site.workspace, id, revision) {
        Err(e) => failure_page("Composition history", &e),
        Ok(value) => {
            let previous = revision
                .parse::<u64>()
                .ok()
                .filter(|r| *r > 0)
                .map(|r| {
                    format!(
                        "<a href=\"{}/studio/{}/history/{}\">Previous composition</a>",
                        site.base(),
                        escape(id),
                        r - 1
                    )
                })
                .unwrap_or_default();
            Page {status:200,title:"Composition history".into(),stamp:Stamp::None,body:format!("<p>Composition revision {}. These references do not reopen historical document text.</p><pre>{}</pre><p>{previous} | <a href=\"{}/studio/{}\">Current package</a></p><form method=post action=\"{}/studio/{}/fork\"><input type=hidden name=revision value=\"{}\"><label>Fork title<input name=title required></label><button>Fork this composition revision</button></form>",escape(revision),escape(&serde_json::to_string_pretty(&json!({"manifest":value["manifest"],"prototype":value["prototype"]})).unwrap_or_default()),site.base(),escape(id),site.base(),escape(id),escape(revision))}
        }
    }
}
pub(super) fn module(site: &Site, id: &str, index: &str, fresh: bool) -> Page {
    let index = match index.parse::<usize>() {
        Ok(i) if i < 256 => i,
        _ => return simple(400, "Source module", "invalid module index"),
    };
    match studio::editor(&site.root, &site.workspace, id, index, fresh) {
        Err(error) => failure_page("Source module", &error),
        Ok(edit) => {
            let mut page = editor::open(site, &edit.name, Some(&edit.id));
            page.body = format!(
                "<p><a href=\"{}/studio/{}\">Back to source package</a></p>{}",
                site.base(),
                escape(id),
                page.body
            );
            page
        }
    }
}
pub(super) fn captured(site: &Site, id: &str, snapshot: &str) -> Page {
    match studio::capture(&site.root, &site.workspace, id, snapshot) {
        Err(error) => failure_page("Source snapshot", &error),
        Ok(value) => {
            let mut body=format!("<p><a href=\"{}/studio/{}\">Source package</a></p><p>Retained saved source, composition revision {}. Entry {}.{}.</p><ul>",site.base(),escape(id),escape(value["revision"].as_str().unwrap_or("?")),escape(value["entryModule"].as_str().unwrap_or("?")),escape(value["entryDefinition"].as_str().unwrap_or("?")));
            if let Some(sources) = value["sources"].as_array() {
                for source in sources {
                    body.push_str(&format!("<li>{} at height {}, root {} — <a href=\"{}/doc/{}/inspect\">Inspect current source</a></li>",escape(source["name"].as_str().unwrap_or("Module")),escape(source["height"].as_str().unwrap_or("?")),short(source["cellRoot"].as_str().unwrap_or("?")),site.base(),escape(source["reference"].as_str().unwrap_or(""))));
                }
            }
            body.push_str("</ul><p>Compiler preview and publication are unavailable. This retained source capture has not installed a program or changed a prototype.</p>");
            body.push_str(&preview_form(site,id,snapshot));
            if studio::preview_available() {body=body.replace("Compiler preview and publication are unavailable.","Run this capture with the selected source edition below. Native publication remains unavailable.");}
            match studio::source_preview_runs(&site.root,&site.workspace,id,snapshot) {
                Ok(runs) if !runs.is_empty()=>{body.push_str("<section><h2>Retained previews</h2><ul>");for run in runs {body.push_str(&format!("<li><a href=\"{}/studio/{}/snapshot/{}/preview/{}\">{} — {}</a></li>",site.base(),escape(id),escape(snapshot),escape(run["run"].as_str().unwrap_or("")),escape(run["run"].as_str().unwrap_or("")),escape(run["status"].as_str().unwrap_or("started"))));}body.push_str("</ul></section>");},
                Err(e)=>body.push_str(&format!("<p>Preview history unavailable: {}</p>",escape(&e))),
                _=>{},
            }
            Page {
                status: 200,
                title: "Source snapshot".into(),
                stamp: Stamp::None,
                body,
            }
        }
    }
}
pub(super) fn submitted(site: &Site, id: &str, submission: &str) -> Page {
    match studio::submission(&site.root,&site.workspace,id,submission){
        Err(e)=>failure_page("Retained source composition",&e),
        Ok(value)=>Page{status:200,title:"Retained source composition".into(),stamp:Stamp::None,body:format!("<p>This authored draft was retained against composition revision <code>{}</code>.</p><textarea readonly rows=24>{}</textarea><p><a href=\"{}/studio/{}\">Open the selected current composition to reconcile this draft</a></p>",escape(value["revision"].as_str().unwrap_or("?")),escape(value["text"].as_str().unwrap_or("")),site.base(),escape(id))}
    }
}
pub(super) fn post(site: &Site, id: Option<&str>, action: &str, body: &[u8]) -> Page {
    let mut fields = match editor::form(body) {
        Ok(f) => f,
        Err(e) => return simple(400, "Source workspace", &e),
    };
    if action == "new" {
        let simple_fields = fields.len() == 4
            && ["title", "name", "reference", "definition"]
                .iter()
                .all(|k| fields.contains_key(*k));
        let advanced =
            fields.len() == 2 && fields.contains_key("title") && fields.contains_key("manifest");
        if !simple_fields && !advanced {
            return simple(
                400,
                "Source workspace",
                "expected title and source module or composition manifest",
            );
        }
        let title = fields.remove("title").unwrap();
        let manifest = if simple_fields {
            json!({"entryModule":"0","entryDefinition":fields.remove("definition").unwrap(),"modules":[{"name":fields.remove("name").unwrap(),"reference":fields.remove("reference").unwrap(),"imports":[]}]})
        } else {
            let raw = fields.remove("manifest").unwrap();
            match serde_json::from_str(&raw) {
                Ok(m) => m,
                Err(e) => {
                    return simple(400, "Source workspace", &format!("Invalid manifest: {e}"))
                }
            }
        };
        return match studio::create(&site.root, &site.workspace, &title, &manifest) {
            Ok(v) => render(
                site,
                &v,
                "Source workspace created. Open a module to edit its document.",
            ),
            Err(e) => simple(400, "Source workspace", &e),
        };
    }
    let Some(id) = id else {
        return simple(400, "Source workspace", "package identity required");
    };
    if action == "preview" {
        if fields.len()!=2 || !fields.contains_key("snapshot") || !fields.contains_key("edition") {return simple(400,"Source preview","expected retained snapshot and explicit edition");}
        return match studio::source_preview(&site.root,&site.workspace,id,&fields["snapshot"],&fields["edition"]) {
            Ok(value)=>preview_render(site,id,&fields["snapshot"],&value),
            Err(e)=>failure_page("Source preview",&e),
        };
    }
    if action == "fork" {
        if fields.len() != 2 || !fields.contains_key("revision") || !fields.contains_key("title") {
            return simple(400, "Fork composition", "expected revision and title");
        }
        return match studio::fork(
            &site.root,
            &site.workspace,
            id,
            &fields["revision"],
            &fields["title"],
        ) {
            Ok(v) => render(
                site,
                &v,
                "Composition fork created. Source documents retain their current authority.",
            ),
            Err(e) => failure_page("Fork composition", &e),
        };
    }
    if action == "compose" {
        let Some(revision) = fields.remove("revision") else {
            return simple(400, "Source composition", "revision required");
        };
        let change = Value::Object(fields.into_iter().map(|(k, v)| (k, json!(v))).collect());
        let text = serde_json::to_string_pretty(&change).unwrap_or_default();
        let submission =
            match studio::retain_submission(&site.root, &site.workspace, id, &revision, &text) {
                Ok(s) => s,
                Err(e) => return failure_page("Retain source composition", &e),
            };
        return match studio::compose(&site.root, &site.workspace, id, &revision, &change) {
            Ok(v) => render(
                site,
                &v,
                "Composition saved; source editor drafts remain retained.",
            ),
            Err(e) => {
                let mut page = submitted(site, id, &submission);
                page.status = 400;
                page.body = format!("<p class=refusal>{}</p>{}", escape(&e), page.body);
                page
            }
        };
    }
    if action == "snapshot" {
        if !fields.is_empty() {
            return simple(400, "Source capture", "unexpected fields");
        }
        return match studio::snapshot(&site.root,&site.workspace,id){Ok(_)=>match studio::load(&site.root,&site.workspace,id){Ok(v)=>render(site,&v,"Saved source captured. Compiler preview is unavailable; this has not published or installed code."),Err(e)=>failure_page("Source capture",&e)},Err(e)=>failure_page("Source capture",&e)};
    }
    let input_key = match action {
        "manifest" => "manifest",
        "prototype" => "declaration",
        _ => return simple(400, "Source workspace", "unknown authoring operation"),
    };
    if fields.len() != 2 || !fields.contains_key("revision") || !fields.contains_key(input_key) {
        return simple(
            400,
            "Source workspace",
            "expected composition revision and authored draft",
        );
    }
    let revision = fields.remove("revision").unwrap();
    let raw = fields.remove(input_key).unwrap();
    let submission =
        match studio::retain_submission(&site.root, &site.workspace, id, &revision, &raw) {
            Ok(s) => s,
            Err(e) => return failure_page("Retain source composition", &e),
        };
    let result = serde_json::from_str::<Value>(&raw)
        .map_err(|e| format!("Invalid manifest: {e}"))
        .and_then(|manifest| {
            if action == "prototype" {
                studio::save_declaration(&site.root, &site.workspace, id, &revision, &manifest)
            } else {
                studio::save_manifest(&site.root, &site.workspace, id, &revision, &manifest)
            }
        });
    match result {
        Ok(v) => render(
            site,
            &v,
            "Composition saved. Prior module editor drafts remain available.",
        ),
        Err(e) => {
            let mut page = submitted(site, id, &submission);
            page.status = 400;
            page.body=format!("<p class=refusal>{}</p><p><a href=\"{}/studio/{}/draft/{}\">This submitted draft is retained</a>.</p>{}",escape(&e),site.base(),escape(id),escape(&submission),page.body);
            page
        }
    }
}

fn preview_form(site:&Site,id:&str,snapshot:&str)->String {
    if !studio::preview_available() {return String::new();}
    format!("<form method=post action=\"{}/studio/{}/preview\"><input type=hidden name=snapshot value=\"{}\"><label>Source edition<select name=edition><option value=objective-bend-1>Objective Bend 1</option></select></label><button>Typecheck and run captured source</button><p>Pure preview of this saved source revision, with bounded execution. Native actions require a separate governed operation.</p></form>",site.base(),escape(id),escape(snapshot))
}
pub(super) fn preview(site:&Site,id:&str,snapshot:&str,run:&str)->Page {
    match studio::source_preview_result(&site.root,&site.workspace,id,snapshot,run) {Ok(value)=>preview_render(site,id,snapshot,&value),Err(e)=>failure_page("Source preview",&e)}
}
fn preview_render(site:&Site,id:&str,snapshot:&str,value:&Value)->Page {
    let status=value["status"].as_str().unwrap_or("unavailable");
    let output=&value["result"];
    let mut body=format!("<p><a href=\"{}/studio/{}\">Source package</a> | <a href=\"{}/studio/{}/snapshot/{}\">Captured source revisions</a></p><p role=status data-preview-status=\"{}\">Objective Bend 1 preview: {}.</p><p>This result belongs to the retained source capture. It does not publish code or authorize a native action.</p>",site.base(),escape(id),site.base(),escape(id),escape(snapshot),escape(status),escape(status));
    if let Some(run)=value["run"].as_str(){body.push_str(&format!("<p><a href=\"{}/studio/{}/snapshot/{}/preview/{}\">Permalink to this preview</a></p>",site.base(),escape(id),escape(snapshot),escape(run)));}
    if output["preview"].is_object() {body.push_str(&format!("<section><h2>Typed result and execution</h2><pre>{}</pre></section>",escape(&serde_json::to_string_pretty(&output["preview"]).unwrap_or_default())));}
    let diagnostic=if output["diagnostic"].is_null(){&value["diagnostic"]}else{&output["diagnostic"]};
    if !diagnostic.is_null(){body.push_str(&format!("<section><h2>Source diagnostics</h2><pre>{}</pre></section>",escape(&serde_json::to_string_pretty(diagnostic).unwrap_or_default())));}
    body.push_str(&format!("<details><summary>Exact source, edition and compiler bindings</summary><pre>{}</pre></details>",escape(&serde_json::to_string_pretty(&serde_json::json!({"sourceRequestSha256":value["sourceRequestSha256"],"sourceHashes":value["sourceHashes"],"edition":value["edition"],"toolingSha256":value["toolingSha256"],"resultBinding":output["binding"]})).unwrap_or_default())));
    Page {status:200,title:"Source preview".into(),stamp:Stamp::None,body}
}
