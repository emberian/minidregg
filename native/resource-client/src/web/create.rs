//! Ordinary member birth and document initialization, rendered without scripts.
use super::*;
use crate::workspace::web_create;

pub(super) fn recent(site: &Site) -> String {
    let rows = match web_create::recent(&site.root, &site.workspace) {
        Ok(r) => r,
        Err(_) => return "<p>Retained creations are unavailable.</p>".into(),
    };
    if rows.is_empty() {
        return String::new();
    }
    let mut body="<section><h2>Your retained document creations</h2><p>Open a creation to check its exact outcome or continue writing.</p><ul>".to_owned();
    for row in rows {
        body.push_str(&format!(
            "<li><a href=\"{}/new-document/{}\">{}</a></li>",
            site.base(),
            escape(row["id"].as_str().unwrap_or("")),
            escape(row["name"].as_str().unwrap_or("unnamed document"))
        ));
    }
    body.push_str("</ul></section>");
    body
}
pub(super) fn open(site: &Site, id: Option<&str>, room: Option<&str>) -> Page {
    let result = match id {
        Some(id) => web_create::load(&site.root, &site.workspace, id),
        None => web_create::open(&site.root, &site.workspace, room),
    };
    match result {
        Ok(state) => render(site, &state),
        Err(e) => failure_page("Create document", &e),
    }
}
pub(super) fn post(site: &Site, id: &str, body: &[u8], op: &str) -> Page {
    let result = (|| -> Result<Value> {
        let mut fields = editor::form(body)?;
        let value = match op {
            "create" => {
                let name = fields.remove("name").ok_or("document name absent")?;
                let law = fields.remove("law").ok_or("document law absent")?;
                if !fields.is_empty() {
                    return Err("unexpected creation field".into());
                }
                web_create::submit(&site.root, &site.workspace, id, &name, &law)
            }
            "lookup" | "finish" => {
                if !fields.is_empty() {
                    return Err("this action takes no form fields".into());
                }
                if op == "lookup" {
                    web_create::lookup(&site.root, &site.workspace, id)
                } else {
                    web_create::finish(&site.root, &site.workspace, id)
                }
            }
            _ => Err("unknown creation action".into()),
        }?;
        Ok(value)
    })();
    match result {
        Ok(state) => render(site, &state),
        Err(e) => simple(409, "Creation retained", &e),
    }
}
fn render(site: &Site, state: &Value) -> Page {
    let id = state["id"].as_str().unwrap_or("");
    let status = state["status"].as_str().unwrap_or("uncertain");
    let base = site.base();
    let action = format!("{base}/new-document/{id}");
    let mut body = format!(
        "<p data-create-status=\"{}\">{}</p>",
        escape(status),
        escape(state["message"].as_str().unwrap_or(""))
    );
    if let Some(room) = state["room"].as_str() {
        body.push_str(&format!("<p>Inside room <a href=\"{base}/room/{0}\">{0}</a>. Your placing grant and its current law decide admission.</p>",escape(room)));
    }
    if status == "editing" {
        body.push_str(&format!("<form method=post action=\"{action}\"><label>Document name <input name=name pattern=\"[A-Za-z0-9-]+\" required></label><label>Document law <select name=law><option value=draft>Draft — bounded editable document</option><option value=note>Note — append only</option></select></label><button>Create document</button></form>"));
    } else {
        body.push_str(&format!(
            "<p>Document: <strong>{}</strong>; law: {}.</p>",
            escape(state["name"].as_str().unwrap_or("?")),
            escape(state["law"].as_str().unwrap_or("?"))
        ));
        if status == "created" {
            let name = escape(state["name"].as_str().unwrap_or(""));
            body.push_str(&format!("<p><a href=\"{base}/doc/{name}/edit\">Write in this document</a> | <a href=\"{base}/doc/{name}/inspect\">Inspect source</a></p>"));
        } else {
            body.push_str(&format!("<form method=post action=\"{action}/lookup\"><button>Check exact outcome</button></form>"));
            if status == "birth-complete" {
                body.push_str(&format!("<form method=post action=\"{action}/finish\"><button>Finish the empty document</button></form>"));
            }
        }
        for (key, title) in [
            ("birthReceipt", "Resource birth receipt"),
            ("receipt", "Document receipt"),
        ] {
            if let Some(receipt) = state.get(key) {
                body.push_str(&format!(
                    "<details><summary>{title}</summary><pre>{}</pre></details>",
                    escape(&serde_json::to_string_pretty(receipt).unwrap_or_default())
                ));
            }
        }
    }
    Page {
        status: 200,
        title: "Create document".into(),
        stamp: Stamp::None,
        body,
    }
}
