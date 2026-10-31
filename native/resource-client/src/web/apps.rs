//! The app market and the member's grains, as L13's seam names them (docs/APP-MARKET-2026-10-27.md
//! §5a): every route is one `apps …` shell line run as the member (`body::verb`), and its `--json`
//! reply (`{decided, state, detail, receipt}`) is drawn: the catalogue with claims beside verdicts,
//! a grain's state, routes and held identities, the one-time bootstrap hand-off to the grain's own
//! origin. The `apps` verb is one row of the shell's table, so `/verb/apps` already has every form;
//! these are the bespoke views. Where the verb is absent (a tree without L13's lane) the shell's
//! usage ending is shown by the one outcome partial, never a blank.

use super::body::{act, quote, verb, Ending};
use super::*;

/// The worker's JSON reply on stdout, when the ending carries one.
fn reply(ending: &Ending) -> Option<Value> {
    let text = ending.stdout.trim();
    let start = text.find('{')?;
    serde_json::from_str(&text[start..]).ok()
}

fn grain_id(n: &str) -> Option<String> {
    let id = n.strip_prefix('a').unwrap_or(n);
    (!id.is_empty() && id.len() <= 40 && id.bytes().all(|b| b.is_ascii_alphanumeric())).then(|| format!("a{id}"))
}

/// `/apps[?q=TERM&category=C]`: the catalogue, with shell-owned search semantics.
pub(super) fn market(site: &Site, target: &str) -> Page {
    let term = super::body::query(target, "q").unwrap_or_default();
    let category = super::body::query(target, "category").unwrap_or_default();
    let body = format!(
        "<p class=\"eyebrow\">The app market</p><p class=\"lede\">Your next project starts here. Write together, organise a team, build something, or make room to play.</p>\
         <p class=\"note\">Names, descriptions and publishers are catalogue claims. Package verdicts and declared agent interfaces are shown separately.</p>{installed}{}",
        catalogue(site, &term, &category, false),
        installed = if site.front.read_only { "" } else { "<p><a href=\"/grain\">Open your installed apps →</a></p>" }
    );
    Page { status: 200, title: "Apps".into(), stamp: Stamp::None, body }
}

fn search(site: &Site, term: &str, category: &str) -> std::result::Result<Value, String> {
    let mut line = String::from("apps search");
    if !term.is_empty() { line.push(' '); line.push_str(&quote(term)); }
    if !category.is_empty() { line.push_str(" --category "); line.push_str(&quote(category)); }
    line.push_str(" --json");
    let Some(ending) = verb(site, &[line]) else {
        return Err("<p class=note>The app catalogue is unavailable: this body has no shell paths.</p>".into());
    };
    reply(&ending).filter(|_| ending.code == 0).ok_or_else(||
        super::body::answer_html(&ending, &[("Browse app commands", "/verb/apps")]))
}

fn entries(value: &Value) -> &[Value] {
    value["apps"].as_array().or_else(|| value["receipt"]["apps"].as_array()).map(Vec::as_slice).unwrap_or(&[])
}

/// One catalogue, shared by the market and landing page. No copied featured set or cap.
/// Unfiltered data supplies category choices; the shell performs the actual filtering.
pub(super) fn catalogue(site: &Site, term: &str, category: &str, featured_only: bool) -> String {
    let all = match search(site, "", "") { Ok(v) => v, Err(html) => return html };
    let categories: std::collections::BTreeSet<&str> = entries(&all).iter()
        .flat_map(|a| a["categories"].as_array().into_iter().flatten().filter_map(Value::as_str)).collect();
    let mut options = String::from("<option value=\"\">Every category</option>");
    // Keep an unknown selection visible too, so a bookmarked query explains its empty result.
    for c in categories.iter().copied().chain((!category.is_empty() && !categories.contains(category)).then_some(category)) {
        options.push_str(&format!("<option value=\"{}\"{}>{}</option>", escape(c),
            if c == category { " selected" } else { "" }, escape(c)));
    }
    let mut out = format!(
        "<form method=\"get\" action=\"/apps\" class=\"row catalogue-search\">\
         <div><label>Find an app<input name=\"q\" type=\"search\" placeholder=\"Search the catalogue\" value=\"{}\"></label></div>\
         <div><label>Category<select name=\"category\">{options}</select></label></div><button>Find apps</button></form>", escape(term));
    let filtered;
    let value = if term.is_empty() && category.is_empty() { &all } else {
        filtered = match search(site, term, category) { Ok(v) => v, Err(html) => { out.push_str(&html); return out; } };
        &filtered
    };
    let (mut featured, rest): (Vec<_>, Vec<_>) = entries(value).iter().partition(|a| a["featured"]["rank"].as_u64().is_some());
    featured.sort_by_key(|a| a["featured"]["rank"].as_u64());
    let writes = !site.front.read_only;
    if featured_only {
        let mut groups: std::collections::BTreeMap<&str, Vec<&Value>> = std::collections::BTreeMap::new();
        for app in &featured {
            groups.entry(app["categories"][0].as_str().unwrap_or("Other")).or_default().push(app);
        }
        out.push_str(&format!("<p class=\"catalogue-count\"><strong>{}</strong> featured apps · <a href=\"/apps\">Explore the whole catalogue</a></p>", featured.len()));
        for (category, apps) in groups {
            out.push_str(&format!("<section class=\"catalogue-category\"><h3>{} <span class=\"note\">{}</span></h3><div class=\"app-gallery\">{}</div></section>",
                escape(category), apps.len(), apps.iter().map(|a| app_card(a, writes, 4)).collect::<String>()));
        }
    } else {
        out.push_str(&format!("<p class=\"catalogue-count\"><strong>{}</strong> apps found · {} featured</p>", featured.len() + rest.len(), featured.len()));
        for (title, apps) in [("Featured apps", &featured), ("More from the catalogue", &rest)] {
            if !apps.is_empty() {
                out.push_str(&format!("<section><h2>{title} <span class=\"note\">{}</span></h2><div class=\"app-gallery\">{}</div></section>",
                    apps.len(), apps.iter().map(|a| app_card(a, writes, 3)).collect::<String>()));
            }
        }
    }
    if featured.is_empty() && (featured_only || rest.is_empty()) {
        out.push_str("<div class=\"empty\"><h3>No apps found</h3><p>Try another search, or <a href=\"/apps\">browse the whole catalogue</a>.</p></div>");
    }
    out
}

/// Typed declarations describe agent capabilities without claiming qualification.
fn agent_interface(app: &Value) -> String {
    let interface = &app["interface"];
    let Some(operations) = interface["operations"].as_array().filter(|o| !o.is_empty()) else { return String::new() };
    let names = operations.iter().filter_map(|o| o["name"].as_str()).map(|n| format!("<code>{}</code>", escape(n))).collect::<Vec<_>>().join(", ");
    let details: String = operations.iter().map(|op| format!(
        "<li><strong><code>{}</code></strong> <span class=\"note\">{}</span><p>{}</p><details><summary>Input and output types</summary><p>Input</p>{}<p>Output</p>{}</details></li>",
        escape(op["name"].as_str().unwrap_or("")), if op["write"] == true { "writes" } else { "reads" },
        escape(op["description"].as_str().unwrap_or("")), super::body::json_tree_html(&op["input"]), super::body::json_tree_html(&op["output"]))).collect();
    format!("<div class=\"app-agent\"><p class=\"eyebrow\">For agents</p><p>{names}</p><details><summary>Declared operations · {}</summary><ul>{details}</ul><details><summary>Shared types</summary>{}</details></details></div>",
        escape(interface["status"].as_str().unwrap_or("qualification not reported")), super::body::json_tree_html(&interface["$defs"]))
}

fn app_card(app: &Value, writes: bool, level: u8) -> String {
    let text = |key: &str| escape(app[key].as_str().unwrap_or(""));
    let reported = |key: &str| app[key].as_str().filter(|value| !value.is_empty()).unwrap_or("not reported");
    let id = text("appId");
    let name = text("name");
    let mark = escape(&app["name"].as_str().unwrap_or("?").chars().next().unwrap_or('?').to_string());
    let state = escape(app["verdict"]["state"].as_str().unwrap_or("unchecked"));
    // What the verdict means for the member, and what they can still do (`apps::verdict_says`).
    let reason = escape(app["verdict"]["says"].as_str().or(app["verdict"]["reason"].as_str()).unwrap_or("No additional verdict details reported."));
    let categories = app["categories"].as_array().into_iter().flatten().filter_map(Value::as_str)
        .map(|c| format!("<span class=\"category\">{}</span>", escape(c))).collect::<String>();
    let install = if writes {
        format!("<form method=\"post\" action=\"/apps/install\" class=\"inline\"><input type=\"hidden\" name=\"app\" value=\"{id}\"><button class=\"quiet\">Install</button></form>")
    } else { String::new() };
    format!(
        "<article class=\"app-card\" data-app=\"{id}\"><header><span class=\"app-mark\" aria-hidden=\"true\">{mark}</span><div><h{level}><a href=\"/apps/{id}\">{name}</a></h{level}><span class=\"publisher\">{}</span></div></header>\
         <p class=\"app-description\">{}</p><p class=\"app-categories\">{categories}</p>{}<p class=\"note\">Package version {} · Built {}<br>Upstream version {} · Size {}</p>\
         <div class=\"verdict {state}\"><span class=\"badge\">{state}</span><p class=\"note\">{reason}</p></div>\
         <div class=\"actions\"><a href=\"/apps/{id}\">View app →</a>{install}</div></article>",
        text("publisher"), text("shortDescription"), agent_interface(app), text("version"),
        escape(reported("packageBuiltAt")), escape(reported("upstreamVersion")), text("suggestedClass")
    )
}

/// `/apps/APP-ID`: one entry whole.
pub(super) fn show(site: &Site, app: &str) -> Page {
    let Some(ending) = verb(site, &[format!("apps show {} --json", quote(app))]) else { return simple(500, "Apps", "this body has no shell paths") };
    let mut body = match reply(&ending).filter(|_| ending.code == 0) {
        Some(value) => format!("{}<details><summary>Package details and publisher claims</summary>{}</details>", app_card(&value, false, 2), super::body::json_tree_html(&value)),
        None => super::body::outcome_html(&ending, &[("the market", "/apps")]),
    };
    if !site.front.read_only {
        body.push_str(&format!(
            "<form method=\"post\" action=\"/apps/install\" class=\"row\"><input type=\"hidden\" name=\"app\" value=\"{}\"><div><label for=\"cls\">Class</label><select id=\"cls\" name=\"class\"><option value=\"\">auto</option><option>S</option><option>M</option><option>L</option></select></div><button>Install</button></form>",
            escape(app)
        ));
    }
    Page { status: 200, title: format!("App {app}"), stamp: Stamp::None, body }
}

/// `POST /apps/install` (fields `app`, `class`).
pub(super) fn install(site: &Site, form: &std::collections::BTreeMap<String, String>) -> Page {
    let app = form.get("app").map(|s| s.trim()).unwrap_or("");
    if app.is_empty() {
        return simple(400, "Install", "which app?");
    }
    let mut line = format!("apps install {}", quote(app));
    if let Some(class) = form.get("class").map(|c| c.trim()).filter(|c| matches!(*c, "S" | "M" | "L")) {
        line.push_str(&format!(" --class {class}"));
    }
    act(site, &format!("Install {app}"), vec![line], "", &[("your grains", "/grain"), ("the market", "/apps")])
}

/// `/grain`: the grains this member owns or was shared.
pub(super) fn grains(site: &Site) -> Page {
    let Some(ending) = verb(site, &["apps list --json".to_owned()]) else { return simple(500, "Grains", "this body has no shell paths") };
    let body = match reply(&ending).filter(|_| ending.code == 0) {
        Some(value) => {
            let mut rows = String::new();
            for g in value["receipt"]["grains"].as_array().into_iter().flatten() {
                let id = g["grain"].as_str().unwrap_or("");
                rows.push_str(&format!(
                    "<tr><td><a href=\"/grain/{id}\"><code>{id}</code></a></td><td>{}</td><td>{}</td><td>{}</td><td><a href=\"{}\" data-full>{}</a></td></tr>",
                    escape(g["indexName"].as_str().unwrap_or("")),
                    escape(g["state"].as_str().unwrap_or("")),
                    if g["shared"] == true { "shared with you" } else { "yours" },
                    url(g["origin"].as_str().unwrap_or("")),
                    escape(g["origin"].as_str().unwrap_or("")),
                    id = escape(id)
                ));
            }
            format!(
                "<table><thead><tr><th>grain</th><th>app</th><th>state</th><th></th><th>origin</th></tr></thead><tbody>{rows}</tbody></table>{}",
                notice(&value["receipt"])
            )
        }
        None => super::body::outcome_html(&ending, &[("the market", "/apps")]),
    };
    Page { status: 200, title: "Grains".into(), stamp: Stamp::None, body }
}

fn notice(receipt: &Value) -> String {
    receipt["identityNotice"].as_str().map(|n| format!("<p class=\"outcome undecided\">{}</p>", escape(n))).unwrap_or_default()
}

/// `/grain/N`: the grain's state, routes, identities, and the actions on it.
pub(super) fn grain(site: &Site, n: &str) -> Page {
    let Some(id) = grain_id(n) else { return simple(404, "Grain", "not a grain id") };
    let Some(ending) = verb(site, &[format!("apps status {id} --json")]) else { return simple(500, "Grain", "this body has no shell paths") };
    let mut body = match reply(&ending).filter(|_| ending.code == 0) {
        Some(value) => {
            let r = &value["receipt"];
            let origin = r["origin"].as_str().unwrap_or("");
            let mut out = format!(
                "<p><strong>{}</strong> <code>{id}</code>: {} (class {}); origin <a href=\"{u}\" data-full>{o}</a></p>",
                escape(r["indexName"].as_str().unwrap_or("")),
                escape(value["state"].as_str().unwrap_or("?")),
                escape(r["class"].as_str().unwrap_or("?")),
                u = url(origin),
                o = escape(origin)
            );
            if let Some(runs) = r["runs"].as_array() {
                out.push_str("<section><h2>Runs</h2>");
                out.push_str(&super::body::json_tree_html(&Value::Array(runs.clone())));
                out.push_str("</section>");
            }
            let routes: Vec<String> = r["routes"].as_array().into_iter().flatten().filter_map(|v| v.as_str().map(str::to_owned)).collect();
            out.push_str(&format!("<section><h2>Routes</h2><p>{}</p></section>", if routes.is_empty() { "none".to_owned() } else { routes.iter().map(|r| format!("<code>{}</code>", escape(r))).collect::<Vec<_>>().join(" ") }));
            if let Some(identities) = r["identities"].as_array() {
                out.push_str("<section><h2>Identities this grain holds</h2>");
                if identities.is_empty() {
                    out.push_str("<p class=note>none</p>");
                } else {
                    out.push_str(&super::body::json_tree_html(&Value::Array(identities.clone())));
                    if !site.front.read_only {
                        out.push_str(&format!("<form method=\"post\" action=\"/grain/{id}/revoke-identity\" class=\"row\"><div><label for=\"tok\">Revoke a saved identity (its token)</label><input id=\"tok\" name=\"token\" type=\"text\" required></div><button class=\"quiet\">Revoke</button></form>"));
                    }
                }
                out.push_str("</section>");
            }
            out.push_str(&notice(r));
            out
        }
        None => super::body::outcome_html(&ending, &[("your grains", "/grain")]),
    };
    if !site.front.read_only {
        body.push_str(&format!(
            "<section><h2>Act</h2><p>\
             <form method=\"post\" action=\"/grain/{id}/open\" class=\"inline\"><button>Open</button></form> \
             <form method=\"post\" action=\"/grain/{id}/start\" class=\"inline\"><button class=\"quiet\">Start</button></form> \
             <form method=\"post\" action=\"/grain/{id}/stop\" class=\"inline\"><button class=\"quiet\">Stop</button></form> \
             <form method=\"post\" action=\"/grain/{id}/renew\" class=\"inline\"><button class=\"quiet\">Renew</button></form> \
             <form method=\"post\" action=\"/grain/{id}/export\" class=\"inline\"><input name=\"file\" type=\"text\" placeholder=\"export.spk\" aria-label=\"Export file name\" required pattern=\"[A-Za-z0-9._-]+\"><button class=\"quiet\">Export</button></form> \
             <form method=\"post\" action=\"/grain/{id}/delete\" class=\"inline\"><button class=\"quiet\">Delete</button></form></p>\
             <form method=\"post\" action=\"/grain/{id}/share\" class=\"row\"><div><label for=\"sh\">Share with (member name)</label><input id=\"sh\" name=\"member\" type=\"text\" pattern=\"[a-z][a-z0-9-]*\" required></div><button class=\"quiet\">Share</button></form></section>"
        ));
    }
    Page { status: 200, title: format!("Grain {id}"), stamp: Stamp::None, body }
}

/// `POST /grain/N/ACTION`.
pub(super) fn grain_action(site: &Site, n: &str, action: &str, form: &std::collections::BTreeMap<String, String>) -> Page {
    let Some(id) = grain_id(n) else { return simple(404, "Grain", "not a grain id") };
    let field = |k: &str| form.get(k).map(|v| v.trim().to_owned()).unwrap_or_default();
    match action {
        "open" => {
            let Some(ending) = verb(site, &[format!("apps open {id} --json")]) else { return simple(500, "Grain", "no shell paths") };
            match reply(&ending).filter(|_| ending.code == 0) {
                Some(value) => {
                    let r = &value["receipt"];
                    let origin = r["origin"].as_str().unwrap_or("").to_owned();
                    let body = match r["bootstrapToken"].as_str() {
                        Some(token) => format!(
                            "<p>Your route on <code>{id}</code> is ready. The grain lives on its own origin and keeps its own cookie, so the one-time token is posted there from your browser, not from here:</p>\
                             <form method=\"post\" action=\"{}\" target=\"_blank\" data-full data-autosubmit><input type=\"hidden\" name=\"token\" value=\"{}\"><button>Sign in to {id} on {o}</button></form>\
                             <p class=\"note\">Then <a href=\"/grain/{id}/pane\">open it in a pane</a>. The token works once; a fresh route needs a new share.</p>{}",
                            url(&format!("{origin}{}", r["bootstrapPath"].as_str().unwrap_or("/__mini/bootstrap"))),
                            escape(token),
                            notice(r),
                            o = escape(&origin)
                        ),
                        None => format!(
                            "<p>{}</p><p><a href=\"{u}\" data-full>{o}</a> · <a href=\"/grain/{id}/pane\">open in a pane</a></p>{}",
                            escape(value["detail"].as_str().unwrap_or("")),
                            notice(r),
                            u = url(&origin),
                            o = escape(&origin)
                        ),
                    };
                    Page { status: 200, title: format!("Open {id}"), stamp: Stamp::None, body }
                }
                None => Page { status: 200, title: format!("Open {id}"), stamp: Stamp::None, body: super::body::outcome_html(&ending, &[("the grain", &format!("/grain/{id}"))]) },
            }
        }
        "share" => act(site, &format!("Share {id}"), vec![format!("apps share {id} {}", quote(&field("member")))], "", &[("the grain", &format!("/grain/{id}"))]),
        "revoke-identity" => act(site, &format!("Revoke an identity on {id}"), vec![format!("apps revoke-identity {id} {}", quote(&field("token")))], "", &[("the grain", &format!("/grain/{id}"))]),
        "export" => act(site, &format!("export {id}"), vec![format!("apps export {id} {}", quote(&field("file")))], "", &[("the grain", &format!("/grain/{id}"))]),
        "renew" => act(site, &format!("Renew the enrollment on {id}"), vec![format!("apps renew {id}")], "", &[("the grain", &format!("/grain/{id}"))]),
        "stop" | "start" | "delete" => act(site, &format!("{action} {id}"), vec![format!("apps {action} {id}")], "", &[("the grain", &format!("/grain/{id}")), ("your grains", "/grain")]),
        _ => simple(404, "Grain", "no such action"),
    }
}

/// `/grain/N/pane`: the grain's origin in a frame (the gateway's `frame-src` names the grain origins).
pub(super) fn pane(site: &Site, n: &str) -> Page {
    let Some(id) = grain_id(n) else { return simple(404, "Grain", "not a grain id") };
    let Some(ending) = verb(site, &[format!("apps status {id} --json")]) else { return simple(500, "Grain", "no shell paths") };
    match reply(&ending).and_then(|v| v["receipt"]["origin"].as_str().map(str::to_owned)) {
        Some(origin) => Page {
            status: 200,
            title: format!("{id}"),
            stamp: Stamp::None,
            body: format!("<iframe class=\"grain\" src=\"{u}\" title=\"{id}\" sandbox=\"allow-scripts allow-forms allow-same-origin allow-popups\"></iframe><p class=note><a href=\"{u}\" data-full>{o}</a></p>", u = url(&origin), o = escape(&origin)),
        },
        None => Page { status: 200, title: format!("Grain {id}"), stamp: Stamp::None, body: super::body::outcome_html(&ending, &[]) },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn grain_ids_and_worker_replies_parse() {
        assert_eq!(grain_id("7").as_deref(), Some("a7"));
        assert_eq!(grain_id("a7").as_deref(), Some("a7"));
        assert!(grain_id("../x").is_none());
        let ending = Ending { code: 0, stdout: "request 9\n{\"decided\":true,\"state\":\"open\",\"receipt\":{\"origin\":\"https://a7.demo.dregg.online\",\"bootstrapToken\":\"t\"}}\n".into(), stderr: String::new() };
        let value = reply(&ending).unwrap();
        assert_eq!(value["receipt"]["bootstrapToken"], "t");
        assert!(notice(&serde_json::json!({"identityNotice": "one user"})).contains("one user"));
    }
}
