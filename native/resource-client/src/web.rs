//! `mini web`: the participant's own view of the node as plain hypertext.
//!
//! A loopback HTTP server beside the client. Every page that shows kernel
//! state is one or more signed reads under the workspace's own key, through
//! `workspace::signed_view` (the same path `workspace --action read` takes);
//! quotes render through the Host's `inspect view-quotes`, fed only the source
//! views this reader's own grants obtained. There is no write route: the router
//! answers GET and HEAD and nothing else. It binds 127.0.0.1 only, accepts only
//! `Host: 127.0.0.1:PORT` / `localhost:PORT` (the DNS-rebinding guard), refuses a
//! foreign `Origin`, and every path sits under a per-launch secret printed at
//! start, so another local user or a page in the browser cannot read it.

use crate::workspace;
use crate::{absolute, hex, inspect, path, Args, Result};
use serde_json::{json, Value};
use std::collections::BTreeSet;
use std::fs;
use std::io::{Read, Write};
use std::net::{Ipv4Addr, SocketAddr, TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::time::Duration;

const MAX_REQUEST: usize = 16 * 1024;

const CSS: &str = "body{font:15px/1.45 system-ui,sans-serif;max-width:60rem;margin:1rem auto;\
padding:0 1rem;color:#1d1d1f;background:#fdfdfb}a{color:#0b5cad}\
header{border-bottom:1px solid #ccc;margin-bottom:1rem}.ctx{font-size:12px;color:#555}\
table{border-collapse:collapse;width:100%}td,th{border-bottom:1px solid #e3e3e3;padding:.2rem .4rem;\
text-align:left;vertical-align:top}code,.id{font:12px ui-monospace,monospace}\
.refusal{border-left:4px solid #b3261e;padding:.4rem .8rem;background:#fbeeee}\
.note{color:#555;font-size:13px}blockquote{border-left:3px solid #999;margin:.3rem 0;padding:0 .7rem}\
.stale{color:#8a5a00}.ann{font-size:13px;color:#333;margin:.2rem 0 .2rem 1rem}";

pub(crate) fn run(mut args: Args) -> Result<()> {
    let listen = args
        .required("listen")?
        .into_string()
        .map_err(|_| "--listen must be UTF-8".to_owned())?;
    let root = absolute(&path(args.required("dir")?))?;
    args.finish()?;
    let address = loopback_address(&listen)?;
    let workspace = workspace::load(&root)?;
    let token = launch_token()?;
    let listener =
        TcpListener::bind(address).map_err(|error| format!("cannot bind {address}: {error}"))?;
    let bound = listener
        .local_addr()
        .map_err(|error| format!("cannot read bound address: {error}"))?;
    if !matches!(bound, SocketAddr::V4(v4) if *v4.ip() == Ipv4Addr::LOCALHOST) {
        return Err(format!("bound {bound}, which is not 127.0.0.1"));
    }
    let site = Site {
        subject: workspace::member(&workspace, "subject")?.to_owned(),
        root,
        workspace,
        token,
        port: bound.port(),
    };
    println!(
        "mini web: read-only view for subject {} at http://127.0.0.1:{}/{}/",
        site.subject, site.port, site.token
    );
    println!("mini web: the path secret changes every launch; no write route exists");
    std::io::stdout().flush().map_err(|error| error.to_string())?;
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                if let Err(error) = site.serve(stream) {
                    eprintln!("mini web: {error}");
                }
            }
            Err(error) => eprintln!("mini web: accept: {error}"),
        }
    }
    Ok(())
}

/// The listen address, refused unless its host is exactly 127.0.0.1.
pub(crate) fn loopback_address(text: &str) -> Result<SocketAddr> {
    let address: SocketAddr = text
        .parse()
        .map_err(|_| format!("--listen {text} is not ADDRESS:PORT"))?;
    match address {
        SocketAddr::V4(v4) if *v4.ip() == Ipv4Addr::LOCALHOST => Ok(address),
        _ => Err(format!(
            "refused --listen {text}: mini web binds 127.0.0.1 only (reach it from elsewhere over ssh -L)"
        )),
    }
}

fn launch_token() -> Result<String> {
    let mut bytes = [0u8; 16];
    fs::File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut bytes))
        .map_err(|error| format!("cannot obtain launch secret: {error}"))?;
    Ok(hex(&bytes))
}

struct Site {
    root: PathBuf,
    workspace: Value,
    subject: String,
    token: String,
    port: u16,
}

#[derive(Debug)]
pub(crate) struct Request {
    pub method: String,
    pub target: String,
    pub headers: Vec<(String, String)>,
}

pub(crate) fn parse_request(bytes: &[u8]) -> Result<Request> {
    let text = std::str::from_utf8(bytes).map_err(|_| "request head is not UTF-8".to_owned())?;
    let mut lines = text.split("\r\n");
    let line = lines.next().ok_or("empty request")?;
    let mut parts = line.split(' ');
    let (Some(method), Some(target), Some(version), None) =
        (parts.next(), parts.next(), parts.next(), parts.next())
    else {
        return Err("malformed request line".into());
    };
    if !version.starts_with("HTTP/1.") {
        return Err("unsupported HTTP version".into());
    }
    let mut headers = Vec::new();
    for line in lines {
        if line.is_empty() {
            break;
        }
        let (name, value) = line.split_once(':').ok_or("malformed header")?;
        headers.push((name.trim().to_ascii_lowercase(), value.trim().to_owned()));
    }
    Ok(Request {
        method: method.to_owned(),
        target: target.to_owned(),
        headers,
    })
}

/// What the gate decides before any read happens.
#[derive(Debug, PartialEq)]
pub(crate) enum Gate {
    Route(Vec<String>),
    Refuse(u16, String),
}

fn token_equal(left: &str, right: &str) -> bool {
    left.len() == right.len()
        && left
            .bytes()
            .zip(right.bytes())
            .fold(0u8, |acc, (a, b)| acc | (a ^ b))
            == 0
}

/// Method, Host, Origin, fetch-site and path-secret checks. Pure, so tested.
pub(crate) fn gate(request: &Request, port: u16, token: &str) -> Gate {
    if request.method != "GET" && request.method != "HEAD" {
        return Gate::Refuse(
            405,
            format!("{}: this server has no write route; it answers GET and HEAD only", request.method),
        );
    }
    let hosts: Vec<&str> = request
        .headers
        .iter()
        .filter(|(name, _)| name == "host")
        .map(|(_, value)| value.as_str())
        .collect();
    let allowed_hosts = [format!("127.0.0.1:{port}"), format!("localhost:{port}")];
    if hosts.len() != 1 || !allowed_hosts.iter().any(|allowed| allowed == hosts[0]) {
        return Gate::Refuse(
            421,
            format!(
                "Host header {:?} refused: only 127.0.0.1:{port} or localhost:{port} (DNS-rebinding guard)",
                hosts
            ),
        );
    }
    for (name, value) in &request.headers {
        if name == "origin"
            && value != &format!("http://127.0.0.1:{port}")
            && value != &format!("http://localhost:{port}")
        {
            return Gate::Refuse(403, format!("Origin {value} refused: another origin may not read this view"));
        }
        if name == "sec-fetch-site" && value == "cross-site" {
            return Gate::Refuse(403, "cross-site request refused".into());
        }
    }
    let target = request.target.split(['?', '#']).next().unwrap_or("");
    let Some(rest) = target.strip_prefix('/') else {
        return Gate::Refuse(404, "not found".into());
    };
    let mut segments = rest.split('/');
    let secret = segments.next().unwrap_or("");
    if !token_equal(secret, token) {
        return Gate::Refuse(404, "not found (use the URL mini web printed at launch)".into());
    }
    let segments: Vec<String> = segments
        .filter(|segment| !segment.is_empty())
        .map(str::to_owned)
        .collect();
    if segments.iter().any(|segment| {
        !segment
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
    }) {
        return Gate::Refuse(404, "not found".into());
    }
    Gate::Route(segments)
}

/// One HTML response.
pub(crate) struct Page {
    pub status: u16,
    pub title: String,
    pub stamp: Stamp,
    pub body: String,
}

/// What the page header says about the read behind it.
pub(crate) enum Stamp {
    /// No signed read: workspace references only, or a refusal before any read.
    None,
    Read(ReadContext),
    /// A signed read was made and the Host refused it.
    Refused,
}

/// Where a page's signed read landed: the challenge's height and authority
/// root, and the cell root the view reports.
#[derive(Clone)]
pub(crate) struct ReadContext {
    pub height: String,
    pub authority_root: String,
    pub cell_root: String,
}

impl ReadContext {
    fn of(challenge: &Value, view: &Value) -> Self {
        let text = |value: &Value| value.as_str().unwrap_or("?").to_owned();
        ReadContext {
            height: text(&challenge["height"]),
            authority_root: text(&challenge["authorityRoot"]),
            cell_root: text(&view["cell"]["root"]),
        }
    }
}

pub(crate) fn escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for character in text.chars() {
        match character {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            other => out.push(other),
        }
    }
    out
}

fn short(id: &str) -> String {
    if id.len() > 14 {
        format!("<span class=id title=\"{}\">{}...</span>", escape(id), escape(&id[..12]))
    } else {
        format!("<span class=id>{}</span>", escape(id))
    }
}

fn bytes_text(hex_text: &str) -> String {
    match crate::decode_hex(hex_text) {
        Ok(bytes) => String::from_utf8_lossy(&bytes).into_owned(),
        Err(_) => format!("<payload {hex_text}>"),
    }
}

fn subject_of(principal: &Value) -> &str {
    principal
        .get("subject")
        .and_then(Value::as_str)
        .unwrap_or("?")
}

pub(crate) fn wrap(page: &Page, base: &str, subject: &str) -> String {
    let context = match &page.stamp {
        Stamp::Read(read) => format!(
            "read as subject <span class=id>{}</span> at height <span class=id data-height=\"{}\">{}</span> \
             | authority root {} | cell root {}",
            escape(subject),
            escape(&read.height),
            escape(&read.height),
            short(&read.authority_root),
            short(&read.cell_root)
        ),
        Stamp::Refused => format!(
            "subject <span class=id>{}</span> | the Host refused this page's signed read",
            escape(subject)
        ),
        Stamp::None => format!(
            "subject <span class=id>{}</span> | no signed read on this page",
            escape(subject)
        ),
    };
    format!(
        "<!doctype html>\n<html lang=en><head><meta charset=utf-8>\
         <meta name=viewport content=\"width=device-width\"><meta name=referrer content=no-referrer>\
         <title>{title} | mini</title><style>{CSS}</style></head><body>\n\
         <header><nav><a href=\"{base}/\">workspace</a></nav><h1>{title}</h1><p class=ctx>{context}</p></header>\n\
         <main>\n{body}</main></body></html>\n",
        title = escape(&page.title),
        body = page.body,
    )
}

/// A refusal the Host encoded, as text: the printable runs of the frame, the
/// same reading the journey hooks give it. `None` for a client-side failure.
pub(crate) fn refusal_text(error: &str) -> Option<String> {
    if !error.contains("host refused") {
        return None;
    }
    let Some((_, encoded)) = error.split_once("encoded refusal: ") else {
        return Some(error.to_owned());
    };
    let encoded: String = encoded
        .chars()
        .take_while(char::is_ascii_hexdigit)
        .collect();
    let bytes = crate::decode_hex(&encoded).unwrap_or_default();
    let mut runs: Vec<String> = Vec::new();
    let mut current = String::new();
    for byte in bytes {
        if (0x20..0x7f).contains(&byte) {
            current.push(byte as char);
        } else if !current.is_empty() {
            runs.push(std::mem::take(&mut current));
        }
    }
    if !current.is_empty() {
        runs.push(current);
    }
    runs.retain(|run| run.trim().len() > 1);
    Some(runs.join(" "))
}

pub(crate) fn failure_page(title: &str, error: &str) -> Page {
    match refusal_text(error) {
        Some(text) => Page {
            status: 403,
            title: title.to_owned(),
            stamp: Stamp::Refused,
            body: format!(
                "<p class=refusal data-refusal>refused: {}</p>\n<p class=note>The Host refused this \
                 signed read under your key; nothing about the resource is shown.</p>\n",
                escape(&text)
            ),
        },
        None => Page {
            status: 502,
            title: title.to_owned(),
            stamp: Stamp::None,
            body: format!(
                "<p class=refusal>the client could not complete the read: {}</p>\n",
                escape(error)
            ),
        },
    }
}

fn simple(status: u16, title: &str, text: &str) -> Page {
    Page {
        status,
        title: title.to_owned(),
        stamp: Stamp::None,
        body: format!("<p>{}</p>\n", escape(text)),
    }
}

/// A backlink found by folding over a readable page.
pub(crate) struct Backlink {
    pub from: String,
    pub kind: &'static str,
    pub id: String,
    pub creator: String,
    pub detail: String,
}

/// Everything `render_document` needs; built from real reads, or from fixtures.
pub(crate) struct DocInput<'a> {
    pub base: &'a str,
    pub entries: &'a [Value],
    pub quotes: std::result::Result<Option<Value>, String>,
    pub backlinks: Vec<Backlink>,
    pub unread: Vec<(String, String)>,
    /// workspace reference name for a cell or document id
    pub names: &'a dyn Fn(&str) -> Option<String>,
}

/// Atom entries in line order, as `doc show` orders them: the numeric order of
/// atom ids (shorter first, then lexicographic).
pub(crate) fn lines(entries: &[Value]) -> Vec<&Value> {
    let mut lines: Vec<&Value> = entries
        .iter()
        .filter(|entry| entry.get("type").and_then(Value::as_str) == Some("atom"))
        .collect();
    lines.sort_by_key(|entry| {
        let id = entry.get("id").and_then(Value::as_str).unwrap_or("").to_owned();
        (id.len(), id)
    });
    lines
}

fn of_type<'a>(entries: &'a [Value], kind: &str) -> Vec<&'a Value> {
    entries
        .iter()
        .filter(|entry| entry.get("type").and_then(Value::as_str) == Some(kind))
        .collect()
}

pub(crate) fn is_content(entries: &[Value]) -> bool {
    entries.iter().any(|entry| entry.get("type").is_some())
}

fn doc_link(base: &str, names: &dyn Fn(&str) -> Option<String>, document: &str) -> String {
    match names(document) {
        Some(name) => format!("<a href=\"{base}/doc/{0}\">{0}</a>", escape(&name)),
        None => format!("document {} (not in your workspace)", short(document)),
    }
}

pub(crate) fn render_document(input: &DocInput<'_>) -> String {
    let base = input.base;
    let mut out = String::new();
    let annotations = of_type(input.entries, "annotation");
    let lines = lines(input.entries);
    out.push_str(&format!(
        "<section><h2>Lines</h2>\n<table data-lines=\"{}\"><tr><th>#</th><th>text</th><th>creator</th>\
         <th>revision</th><th>atom</th></tr>\n",
        lines.len()
    ));
    for (index, atom) in lines.iter().enumerate() {
        let id = atom["id"].as_str().unwrap_or("?");
        let creator = subject_of(&atom["createdBy"]);
        let revision = atom["revision"].as_str().unwrap_or("?");
        let tombstoned = !atom["tombstonedAt"].is_null() && atom.get("tombstonedAt").is_some();
        let text = bytes_text(atom["payload"].as_str().unwrap_or(""));
        let shown = if tombstoned {
            format!("<del>{}</del>", escape(&text))
        } else {
            escape(&text)
        };
        let mut notes = String::new();
        for annotation in annotations.iter().filter(|annotation| {
            annotation["anchor"]["type"].as_str() == Some("atom")
                && annotation["anchor"]["atom"].as_str() == Some(id)
        }) {
            let fresh = annotation["fresh"].as_bool();
            let body = match annotation["body"]["type"].as_str() {
                Some("inline") => escape(&bytes_text(annotation["body"]["bytes"].as_str().unwrap_or(""))),
                _ => format!("<code>{}</code>", escape(&annotation["body"].to_string())),
            };
            notes.push_str(&format!(
                "<p class=\"ann{}\" data-annotation=\"{}\" data-fresh=\"{}\">annotation by {}: {}{}</p>",
                if fresh == Some(false) { " stale" } else { "" },
                escape(annotation["id"].as_str().unwrap_or("?")),
                fresh.map(|value| value.to_string()).unwrap_or_else(|| "?".into()),
                escape(subject_of(&annotation["author"])),
                body,
                if fresh == Some(false) {
                    " <em>(the line moved since this was written)</em>"
                } else {
                    ""
                }
            ));
        }
        out.push_str(&format!(
            "<tr id=\"line-{n}\" data-atom=\"{a}\" data-creator=\"{c}\" data-revision=\"{r}\"><td>{n}</td>\
             <td>{shown}{notes}</td><td>{c}</td><td>{rs}</td><td class=id>{a}</td></tr>\n",
            n = index + 1,
            a = escape(id),
            c = escape(creator),
            r = escape(revision),
            rs = short(revision),
        ));
    }
    out.push_str("</table></section>\n");

    let embeds: Vec<&Value> = of_type(input.entries, "element")
        .into_iter()
        .filter(|element| element["body"]["type"].as_str() == Some("embed"))
        .collect();
    if !embeds.is_empty() {
        out.push_str("<section><h2>Quotes and transclusions</h2>\n");
        let rendered: Vec<Value> = match &input.quotes {
            Ok(Some(value)) => value["quotes"].as_array().cloned().unwrap_or_default(),
            Ok(None) => Vec::new(),
            Err(error) => {
                out.push_str(&format!(
                    "<p class=refusal>view-quotes could not render: {}</p>\n",
                    escape(error)
                ));
                Vec::new()
            }
        };
        for element in embeds {
            let id = element["id"].as_str().unwrap_or("?");
            let reference = &element["body"]["reference"];
            let mode = reference["mode"].as_str().unwrap_or("?");
            let render = rendered
                .iter()
                .find(|quote| quote["element"].as_str() == Some(id))
                .map(|quote| &quote["render"]);
            let (state, shown) = match render.and_then(|render| render["view"].as_str()) {
                Some("quoted") => {
                    let revised = render.and_then(|r| r["revised"].as_bool()) == Some(true);
                    (
                        "quoted",
                        format!(
                            "<blockquote>{}</blockquote>{}",
                            escape(&bytes_text(render.and_then(|r| r["bytes"].as_str()).unwrap_or(""))),
                            if revised { "<p class=note>revised since it was quoted</p>" } else { "" }
                        ),
                    )
                }
                Some("stale") => (
                    "stale",
                    "<p class=stale>stale: the quoted line has moved past the pinned revision</p>".to_owned(),
                ),
                Some("unavailable") => (
                    "unavailable",
                    "<p class=note>unavailable: you hold no read of the source</p>".to_owned(),
                ),
                _ => ("unrendered", "<p class=note>not rendered</p>".to_owned()),
            };
            out.push_str(&format!(
                "<div data-quote=\"{}\" data-mode=\"{}\" data-render=\"{state}\"><p>{} of line atom {} in {} \
                 by {}</p>{shown}</div>\n",
                escape(id),
                escape(mode),
                if mode == "live" { "transclusion" } else { "quote" },
                escape(reference["atom"].as_str().unwrap_or("?")),
                doc_link(base, input.names, reference["document"].as_str().unwrap_or("?")),
                escape(subject_of(&element["createdBy"])),
            ));
        }
        out.push_str("</section>\n");
    }

    let links = of_type(input.entries, "link");
    if !links.is_empty() {
        out.push_str("<section><h2>Links out</h2>\n<ul>\n");
        for link in links {
            let id = link["id"].as_str().unwrap_or("?");
            let target = &link["target"];
            let shown = match target["type"].as_str() {
                Some("document") => doc_link(base, input.names, target["id"].as_str().unwrap_or("?")),
                Some("range") => doc_link(base, input.names, target["document"].as_str().unwrap_or("?")),
                Some(other) => format!("{} {}", escape(other), escape(&target.to_string())),
                None => "target not spelled by this Host's view".to_owned(),
            };
            out.push_str(&format!("<li data-link=\"{}\">link {} -> {}</li>\n", escape(id), short(id), shown));
        }
        out.push_str("</ul></section>\n");
    }

    out.push_str(&format!(
        "<section><h2>Backlinks</h2>\n<ul data-backlinks=\"{}\">\n",
        input.backlinks.len()
    ));
    for backlink in &input.backlinks {
        out.push_str(&format!(
            "<li data-backlink=\"{from}\" data-kind=\"{kind}\"><a href=\"{base}/doc/{from}\">{from}</a> {kind} {id} \
             by {creator}{detail}</li>\n",
            from = escape(&backlink.from),
            kind = backlink.kind,
            id = short(&backlink.id),
            creator = escape(&backlink.creator),
            detail = escape(&backlink.detail),
        ));
    }
    out.push_str("</ul>\n");
    for (name, why) in &input.unread {
        out.push_str(&format!(
            "<p class=note data-unread=\"{0}\">{0}: not read ({1})</p>\n",
            escape(name),
            escape(why)
        ));
    }
    out.push_str(
        "<p class=note>Backlinks are a fold over every page this workspace can read now; a page the \
         Host refuses you contributes nothing.</p></section>\n",
    );
    out
}

/// Backlinks found in one readable page to any of `documents`.
pub(crate) fn backlinks_in(from: &str, entries: &[Value], documents: &BTreeSet<String>) -> Vec<Backlink> {
    let mut found = Vec::new();
    for entry in entries {
        match entry["type"].as_str() {
            Some("link") => {
                let target = &entry["target"];
                let hit = match target["type"].as_str() {
                    Some("document") => target["id"].as_str(),
                    Some("range") => target["document"].as_str(),
                    _ => None,
                };
                if hit.is_some_and(|id| documents.contains(id)) {
                    found.push(Backlink {
                        from: from.to_owned(),
                        kind: "link",
                        id: entry["id"].as_str().unwrap_or("?").to_owned(),
                        creator: subject_of(&entry["createdBy"]).to_owned(),
                        detail: String::new(),
                    });
                }
            }
            Some("element") if entry["body"]["type"].as_str() == Some("embed") => {
                let reference = &entry["body"]["reference"];
                if reference["document"]
                    .as_str()
                    .is_some_and(|id| documents.contains(id))
                {
                    found.push(Backlink {
                        from: from.to_owned(),
                        kind: if reference["mode"].as_str() == Some("live") {
                            "transclusion"
                        } else {
                            "quote"
                        },
                        id: entry["id"].as_str().unwrap_or("?").to_owned(),
                        creator: subject_of(&entry["createdBy"]).to_owned(),
                        detail: format!(" of atom {}", reference["atom"].as_str().unwrap_or("?")),
                    });
                }
            }
            _ => {}
        }
    }
    found
}

/// A scalar cell's fields, and the board reading of them (P-SHELL-DOCS' layout:
/// task n's state is field 2n+2, its owner field 2n+3).
pub(crate) fn render_fields(entries: &[Value], board: bool) -> String {
    let mut fields: Vec<(u128, String)> = entries
        .iter()
        .filter_map(|entry| {
            let field = entry["key"]["field"].as_str()?.parse().ok()?;
            Some((field, entry["value"].as_str().unwrap_or("?").to_owned()))
        })
        .collect();
    fields.sort();
    let mut out = String::new();
    if board {
        let value = |field: u128| fields.iter().find(|(f, _)| *f == field).map(|(_, v)| v.as_str());
        out.push_str("<section><h2>Tasks</h2>\n<table><tr><th>task</th><th>state</th><th>owner</th></tr>\n");
        let mut count = 0;
        for n in 0..=(fields.last().map(|(f, _)| *f).unwrap_or(0) / 2) {
            if let Some(state) = value(2 * n + 2) {
                count += 1;
                out.push_str(&format!(
                    "<tr data-task=\"{n}\"><td>{n}</td><td>{}</td><td>{}</td></tr>\n",
                    escape(state),
                    escape(value(2 * n + 3).unwrap_or("(none)"))
                ));
            }
        }
        out.push_str(&format!(
            "</table><p class=note>{count} task(s), read with the board layout (state = field 2n+2, owner = \
             field 2n+3); the law that keeps state forward is the cell's own.</p></section>\n"
        ));
    }
    out.push_str(&format!(
        "<section><h2>Fields</h2>\n<table data-fields=\"{}\"><tr><th>field</th><th>value</th></tr>\n",
        fields.len()
    ));
    for (field, value) in &fields {
        out.push_str(&format!(
            "<tr data-field=\"{field}\"><td>{field}</td><td class=id>{}</td></tr>\n",
            escape(value)
        ));
    }
    out.push_str("</table></section>\n");
    out
}

impl Site {
    fn base(&self) -> String {
        format!("/{}", self.token)
    }

    fn serve(&self, mut stream: TcpStream) -> Result<()> {
        stream
            .set_read_timeout(Some(Duration::from_secs(10)))
            .map_err(|error| error.to_string())?;
        let mut head = Vec::new();
        let mut buffer = [0u8; 2048];
        while !head.windows(4).any(|window| window == b"\r\n\r\n") {
            let read = stream.read(&mut buffer).map_err(|error| error.to_string())?;
            if read == 0 {
                return Ok(());
            }
            head.extend_from_slice(&buffer[..read]);
            if head.len() > MAX_REQUEST {
                return respond(&mut stream, false, &simple(431, "Too large", "request head too large"), "", "");
            }
        }
        let request = match parse_request(&head) {
            Ok(request) => request,
            Err(error) => {
                return respond(&mut stream, false, &simple(400, "Bad request", &error), "", "");
            }
        };
        let head_only = request.method == "HEAD";
        let page = match gate(&request, self.port, &self.token) {
            Gate::Refuse(status, text) => simple(status, "Refused", &text),
            Gate::Route(segments) => self.route(&segments),
        };
        respond(&mut stream, head_only, &page, &self.base(), &self.subject)
    }

    fn route(&self, segments: &[String]) -> Page {
        let parts: Vec<&str> = segments.iter().map(String::as_str).collect();
        match parts.as_slice() {
            [] => self.index(),
            ["doc", name] => self.doc(name),
            ["board", name] => self.board(name),
            ["room", name] => self.room(name),
            ["stream", _] => simple(
                501,
                "Not on this tree",
                "streams are K-STREAM (branch k-stream: the `tail` view); this mini was built from k-content, \
                 which has no stream kind",
            ),
            ["at", _, "doc", _] => simple(
                501,
                "Not on this tree",
                "a read at a past height is K-INDEX (branch k-index: `at h`); this mini was built from \
                 k-content, which has no past-height view",
            ),
            _ => simple(404, "Not found", "no such route"),
        }
    }

    fn names(&self) -> Vec<String> {
        let mut names: Vec<String> = fs::read_dir(self.root.join("refs"))
            .map(|dir| {
                dir.flatten()
                    .filter_map(|entry| {
                        entry
                            .file_name()
                            .to_str()
                            .and_then(|file| file.strip_suffix(".json"))
                            .map(str::to_owned)
                    })
                    .collect()
            })
            .unwrap_or_default();
        names.sort();
        names
    }

    fn reference(&self, name: &str) -> std::result::Result<Value, Page> {
        workspace::reference(&self.root, name).map_err(|error| {
            simple(404, name, &format!("no usable workspace reference named {name}: {error}"))
        })
    }

    fn read(&self, reference: &Value) -> Result<(Value, Value, PathBuf)> {
        workspace::signed_view(&self.root, &self.workspace, reference, "resource")
    }

    /// The room a reference was born in, from this workspace's retained birth source.
    fn born_in(&self, name: &str) -> Option<String> {
        let source = self
            .root
            .join("sources")
            .join(format!("create-{name}.current"))
            .join("source.json");
        let value = workspace::bounded_json(&source).ok()?;
        value["birth"]["resources"][0]["room"].as_str().map(str::to_owned)
    }

    fn index(&self) -> Page {
        let base = self.base();
        let names = self.names();
        let mut rows = String::new();
        let mut rooms = BTreeSet::new();
        for name in &names {
            if let Some(room) = self.born_in(name) {
                rooms.insert(room);
            }
        }
        for name in &names {
            let Ok(reference) = workspace::reference(&self.root, name) else {
                rows.push_str(&format!("<tr><td>{}</td><td colspan=3>unreadable reference</td></tr>\n", escape(name)));
                continue;
            };
            let target = reference["target"].as_str().unwrap_or("?");
            let room = if rooms.contains(target) { " (room)" } else { "" };
            rows.push_str(&format!(
                "<tr data-ref=\"{n}\"><td><a href=\"{base}/doc/{n}\">{n}</a>{room}</td><td>{k}</td><td>{t}</td>\
                 <td><a href=\"{base}/doc/{n}\">doc</a> | <a href=\"{base}/board/{n}\">board</a> | \
                 <a href=\"{base}/room/{n}\">room</a></td></tr>\n",
                n = escape(name),
                k = escape(reference["kind"].as_str().unwrap_or("?")),
                t = short(target),
            ));
        }
        Page {
            status: 200,
            title: "Your workspace".into(),
            stamp: Stamp::None,
            body: format!(
                "<p class=note>The resources this workspace holds a reference to. Opening one is a signed \
                 read under your key; what you see is what your grants cover.</p>\n<table data-refs=\"{}\">\
                 <tr><th>name</th><th>kind</th><th>cell</th><th>views</th></tr>\n{rows}</table>\n",
                names.len()
            ),
        }
    }

    fn doc(&self, name: &str) -> Page {
        let reference = match self.reference(name) {
            Ok(reference) => reference,
            Err(page) => return page,
        };
        let (view, challenge, signed) = match self.read(&reference) {
            Ok(read) => read,
            Err(error) => return failure_page(name, &error),
        };
        let context = ReadContext::of(&challenge, &view);
        let entries = view["cell"]["entries"].as_array().cloned().unwrap_or_default();
        let base = self.base();
        if !is_content(&entries) {
            return Page {
                status: 200,
                title: name.to_owned(),
                stamp: Stamp::Read(context),
                body: format!(
                    "<p class=note>{0} is not a document; its fields are below (<a href=\"{base}/board/{0}\">as a \
                     board</a>).</p>\n{1}",
                    escape(name),
                    render_fields(&entries, false)
                ),
            };
        }
        let target = reference["target"].as_str().unwrap_or("").to_owned();
        let mut documents: BTreeSet<String> = of_type(&entries, "document")
            .iter()
            .filter_map(|entry| entry["id"].as_str().map(str::to_owned))
            .collect();
        documents.insert(target);
        let targets: Vec<(String, String)> = self
            .names()
            .into_iter()
            .filter_map(|other| {
                let reference = workspace::reference(&self.root, &other).ok()?;
                Some((reference["target"].as_str()?.to_owned(), other))
            })
            .collect();
        let names = |id: &str| {
            targets
                .iter()
                .find(|(target, _)| target == id)
                .map(|(_, name)| name.clone())
        };
        let quotes = self.quotes(&entries, &signed, &targets);
        let mut backlinks = Vec::new();
        let mut unread = Vec::new();
        for other in self.names() {
            if other == name {
                backlinks.extend(backlinks_in(name, &entries, &documents));
                continue;
            }
            let Ok(other_ref) = workspace::reference(&self.root, &other) else {
                continue;
            };
            match self.read(&other_ref) {
                Ok((other_view, _, _)) => {
                    let other_entries = other_view["cell"]["entries"].as_array().cloned().unwrap_or_default();
                    backlinks.extend(backlinks_in(&other, &other_entries, &documents));
                }
                Err(error) => unread.push((
                    other,
                    refusal_text(&error).map(|text| format!("refused: {text}")).unwrap_or(error),
                )),
            }
        }
        let body = render_document(&DocInput {
            base: &base,
            entries: &entries,
            quotes,
            backlinks,
            unread,
            names: &names,
        });
        Page {
            status: 200,
            title: name.to_owned(),
            stamp: Stamp::Read(context),
            body,
        }
    }

    /// Render this page's quotes through the Host's `inspect view-quotes`, with
    /// the source views this reader's own grants obtain. A refused source read
    /// contributes no source, so its quotes render `unavailable`.
    fn quotes(
        &self,
        entries: &[Value],
        signed: &Path,
        targets: &[(String, String)],
    ) -> std::result::Result<Option<Value>, String> {
        let documents: BTreeSet<&str> = entries
            .iter()
            .filter(|entry| entry["body"]["type"].as_str() == Some("embed"))
            .filter_map(|entry| entry["body"]["reference"]["document"].as_str())
            .collect();
        if documents.is_empty() {
            return Ok(None);
        }
        let attempt = signed.parent().ok_or("signed read lacks its attempt directory")?;
        let host_view = fs::read(attempt.join("view.bin")).map_err(|error| error.to_string())?;
        let mut sources = Vec::new();
        for document in documents {
            for (target, other) in targets.iter().filter(|(target, _)| target == document) {
                let Ok(reference) = workspace::reference(&self.root, other) else {
                    continue;
                };
                if let Ok((_, _, source_signed)) = self.read(&reference) {
                    let view = source_signed
                        .parent()
                        .map(|dir| dir.join("view.bin"))
                        .ok_or("source read lacks its attempt directory")?;
                    let bytes = fs::read(&view).map_err(|error| error.to_string())?;
                    sources.push(json!({"target": target, "view": hex(&bytes)}));
                }
            }
        }
        let input = json!({"host": hex(&host_view), "sources": sources});
        let input_path = attempt.join("view-quotes.in.json");
        workspace::private_file(
            &input_path,
            &serde_json::to_vec(&input).map_err(|error| error.to_string())?,
        )?;
        let output = attempt.join("view-quotes.json");
        let host = workspace::member_path(&self.workspace, "host")?;
        let config = workspace::member_path(&self.workspace, "config")?;
        inspect(&host, &config, "view-quotes", &input_path, &output).map(Some)
    }

    fn board(&self, name: &str) -> Page {
        let reference = match self.reference(name) {
            Ok(reference) => reference,
            Err(page) => return page,
        };
        match self.read(&reference) {
            Ok((view, challenge, _)) => {
                let entries = view["cell"]["entries"].as_array().cloned().unwrap_or_default();
                let body = if is_content(&entries) {
                    format!(
                        "<p class=note>{0} is a document, not a board: <a href=\"{1}/doc/{0}\">read it as one</a>.</p>\n",
                        escape(name),
                        self.base()
                    )
                } else {
                    render_fields(&entries, true)
                };
                Page {
                    status: 200,
                    title: name.to_owned(),
                    stamp: Stamp::Read(ReadContext::of(&challenge, &view)),
                    body,
                }
            }
            Err(error) => failure_page(name, &error),
        }
    }

    fn room(&self, name: &str) -> Page {
        let reference = match self.reference(name) {
            Ok(reference) => reference,
            Err(page) => return page,
        };
        let target = reference["target"].as_str().unwrap_or("?").to_owned();
        let (view, challenge, _) = match self.read(&reference) {
            Ok(read) => read,
            Err(error) => return failure_page(name, &error),
        };
        let base = self.base();
        let entries = view["cell"]["entries"].as_array().cloned().unwrap_or_default();
        let children: Vec<String> = self
            .names()
            .into_iter()
            .filter(|other| self.born_in(other).as_deref() == Some(target.as_str()))
            .collect();
        let mut body = format!(
            "<p>The room cell itself: {} entries, <a href=\"{base}/doc/{n}\">open it</a>.</p>\n\
             <section><h2>In this room</h2>\n<ul data-children=\"{}\">\n",
            entries.len(),
            children.len(),
            n = escape(name),
        );
        for child in &children {
            body.push_str(&format!(
                "<li data-child=\"{0}\"><a href=\"{base}/doc/{0}\">{0}</a></li>\n",
                escape(child)
            ));
        }
        body.push_str(
            "</ul><p class=note>Listed: resources this workspace itself created in the room (its retained birth \
             sources). Opening each is a signed read; a room grant (`under R`) is what lets it succeed.</p>\
             </section>\n<section><h2>Members</h2><p class=note>Who holds a standing grant over this room is \
             K-INDEX's `who` view (branch k-index), not on this tree.</p></section>\n",
        );
        Page {
            status: 200,
            title: format!("room {name}"),
            stamp: Stamp::Read(ReadContext::of(&challenge, &view)),
            body,
        }
    }
}

fn reason(status: u16) -> &'static str {
    match status {
        200 => "OK",
        400 => "Bad Request",
        403 => "Forbidden",
        404 => "Not Found",
        405 => "Method Not Allowed",
        421 => "Misdirected Request",
        431 => "Request Header Fields Too Large",
        501 => "Not Implemented",
        _ => "Bad Gateway",
    }
}

fn respond(stream: &mut TcpStream, head_only: bool, page: &Page, base: &str, subject: &str) -> Result<()> {
    let body = wrap(page, base, subject);
    let mut response = format!(
        "HTTP/1.1 {} {}\r\nContent-Type: text/html; charset=utf-8\r\nContent-Length: {}\r\n\
         Cache-Control: no-store\r\nX-Content-Type-Options: nosniff\r\nX-Frame-Options: DENY\r\n\
         Referrer-Policy: no-referrer\r\n\
         Content-Security-Policy: default-src 'none'; style-src 'unsafe-inline'; frame-ancestors 'none'\r\n\
         {}Connection: close\r\n\r\n",
        page.status,
        reason(page.status),
        body.len(),
        if page.status == 405 { "Allow: GET, HEAD\r\n" } else { "" },
    )
    .into_bytes();
    if !head_only {
        response.extend_from_slice(body.as_bytes());
    }
    stream.write_all(&response).map_err(|error| error.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    const PAPER: &str = include_str!("web/fixtures/paper-read.json");
    const NOTES: &str = include_str!("web/fixtures/notes-read.json");
    const QUOTES: &str = include_str!("web/fixtures/notes-quotes-stale.json");
    const FIELDS: &str = include_str!("web/fixtures/scalar-read.json");
    const REFUSAL: &str = include_str!("web/fixtures/refused-read.err");

    fn entries(text: &str) -> Vec<Value> {
        let value: Value = serde_json::from_str(text).unwrap();
        value["cell"]["entries"].as_array().unwrap().clone()
    }

    fn request(method: &str, target: &str, headers: &[(&str, &str)]) -> Request {
        Request {
            method: method.into(),
            target: target.into(),
            headers: headers
                .iter()
                .map(|(name, value)| (name.to_ascii_lowercase(), (*value).to_owned()))
                .collect(),
        }
    }

    fn no_names(_: &str) -> Option<String> {
        None
    }

    #[test]
    fn lines_follow_doc_show_order_with_creator_and_revision() {
        let entries = entries(PAPER);
        let html = render_document(&DocInput {
            base: "/t",
            entries: &entries,
            quotes: Ok(None),
            backlinks: Vec::new(),
            unread: Vec::new(),
            names: &no_names,
        });
        let first = html.find("data-atom=\"1001\"").unwrap();
        let second = html.find("data-atom=\"1002\"").unwrap();
        assert!(first < second);
        assert!(html.contains("data-lines=\"2\""));
        assert!(html.contains("the first line"));
        assert!(html.contains("the second line, revised"));
        assert!(html.contains("id=\"line-2\" data-atom=\"1002\" data-creator=\"7\" data-revision=\"75608161264795635450568153077390084790153955599406130858924037196896369833322\""));
        assert!(html.contains("data-annotation=\"7001\" data-fresh=\"false\""));
        assert!(html.contains("cite this"));
    }

    #[test]
    fn quotes_render_from_view_quotes_and_links_resolve_to_workspace_names() {
        let entries = entries(NOTES);
        let quotes: Value = serde_json::from_str(QUOTES).unwrap();
        let names = |id: &str| (id == "15383085687320778865").then(|| "paper".to_owned());
        let html = render_document(&DocInput {
            base: "/t",
            entries: &entries,
            quotes: Ok(Some(quotes)),
            backlinks: Vec::new(),
            unread: Vec::new(),
            names: &names,
        });
        assert!(html.contains("data-quote=\"8001\" data-mode=\"snapshot\" data-render=\"stale\""));
        assert!(html.contains("data-quote=\"8002\" data-mode=\"live\" data-render=\"quoted\""));
        assert!(html.contains("the second line, final"));
        assert!(html.contains("<a href=\"/t/doc/paper\">paper</a>"));
        assert!(html.contains("data-link=\"9001\""));
    }

    #[test]
    fn backlinks_fold_quotes_and_spelled_links() {
        let mut documents = BTreeSet::new();
        documents.insert("15383085687320778865".to_owned());
        let found = backlinks_in("notes", &entries(NOTES), &documents);
        let kinds: Vec<&str> = found.iter().map(|backlink| backlink.kind).collect();
        assert_eq!(kinds, ["quote", "transclusion"]);
        let spelled = vec![json!({"type":"link","id":"9101","target":{"type":"document","id":"15383085687320778865"},
            "createdBy":{"subject":"9"}})];
        let found = backlinks_in("other", &spelled, &documents);
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].kind, "link");
        assert!(backlinks_in("paper", &entries(PAPER), &documents).is_empty());
    }

    #[test]
    fn scalar_cells_render_fields_and_board_tasks() {
        let entries = entries(FIELDS);
        assert!(!is_content(&entries));
        let html = render_fields(&entries, false);
        assert!(html.contains("data-field=\"1\""));
        let board = render_fields(
            &[json!({"key":{"field":"2"},"value":"1"}), json!({"key":{"field":"3"},"value":"7"})],
            true,
        );
        assert!(board.contains("<tr data-task=\"0\"><td>0</td><td>1</td><td>7</td></tr>"));
    }

    #[test]
    fn kernel_refusal_renders_as_refusal_not_server_error() {
        let page = failure_page("paper", REFUSAL.trim());
        assert_eq!(page.status, 403);
        assert!(page.body.contains("data-refusal"));
        assert!(page.body.contains("observation refused"));
        assert!(wrap(&page, "/t", "9").contains("the Host refused this page's signed read"));
        let page = failure_page("paper", "cannot open socket: no such file");
        assert_eq!(page.status, 502);
    }

    #[test]
    fn escapes_every_text_path() {
        assert_eq!(escape("<a href=\"x\">&'"), "&lt;a href=&quot;x&quot;&gt;&amp;&#39;");
        let hostile = vec![json!({"type":"atom","id":"1","createdBy":{"subject":"7"},"revision":"1",
            "tombstonedAt":null,"payload":hex(b"<script>alert(1)</script>")})];
        let html = render_document(&DocInput {
            base: "/t",
            entries: &hostile,
            quotes: Ok(None),
            backlinks: Vec::new(),
            unread: Vec::new(),
            names: &no_names,
        });
        assert!(!html.contains("<script>"));
        assert!(html.contains("&lt;script&gt;"));
    }

    #[test]
    fn listen_address_must_be_127_0_0_1() {
        assert!(loopback_address("127.0.0.1:8080").is_ok());
        assert!(loopback_address("127.0.0.1:0").is_ok());
        for refused in ["0.0.0.0:8080", "192.168.1.5:8080", "[::]:8080", "[::1]:8080", "127.0.0.2:8080", "localhost:8080"] {
            assert!(loopback_address(refused).is_err(), "{refused}");
        }
    }

    #[test]
    fn gate_refuses_writes_foreign_hosts_origins_and_wrong_secret() {
        let host = [("Host", "127.0.0.1:8080")];
        assert_eq!(
            gate(&request("GET", "/s3cret/doc/paper", &host), 8080, "s3cret"),
            Gate::Route(vec!["doc".into(), "paper".into()])
        );
        assert_eq!(gate(&request("HEAD", "/s3cret/", &[("Host", "localhost:8080")]), 8080, "s3cret"), Gate::Route(vec![]));
        for method in ["POST", "PUT", "DELETE", "PATCH", "OPTIONS"] {
            assert!(matches!(gate(&request(method, "/s3cret/", &host), 8080, "s3cret"), Gate::Refuse(405, _)));
        }
        for foreign in ["evil.example:8080", "127.0.0.1:9999", "127.0.0.1", "attacker.127.0.0.1.nip.io:8080"] {
            assert!(matches!(gate(&request("GET", "/s3cret/", &[("Host", foreign)]), 8080, "s3cret"), Gate::Refuse(421, _)));
        }
        assert!(matches!(gate(&request("GET", "/s3cret/", &[]), 8080, "s3cret"), Gate::Refuse(421, _)));
        assert!(matches!(
            gate(&request("GET", "/s3cret/", &[("Host", "127.0.0.1:8080"), ("Host", "evil:8080")]), 8080, "s3cret"),
            Gate::Refuse(421, _)
        ));
        assert!(matches!(
            gate(&request("GET", "/s3cret/", &[("Host", "127.0.0.1:8080"), ("Origin", "http://evil.example")]), 8080, "s3cret"),
            Gate::Refuse(403, _)
        ));
        assert!(matches!(
            gate(&request("GET", "/s3cret/", &[("Host", "127.0.0.1:8080"), ("Origin", "http://127.0.0.1:8080")]), 8080, "s3cret"),
            Gate::Route(_)
        ));
        assert!(matches!(
            gate(&request("GET", "/s3cret/", &[("Host", "127.0.0.1:8080"), ("Sec-Fetch-Site", "cross-site")]), 8080, "s3cret"),
            Gate::Refuse(403, _)
        ));
        for target in ["/", "/wrong/", "/s3cre/", "/s3cret0/", "/s3cret/doc/..%2f", "doc"] {
            assert!(matches!(gate(&request("GET", target, &host), 8080, "s3cret"), Gate::Refuse(404, _)), "{target}");
        }
    }

    #[test]
    fn router_source_names_no_write_route() {
        let source = include_str!("web.rs");
        let router = &source[source.find("fn route(").unwrap()..source.find("fn names(").unwrap()];
        for word in ["POST", "PUT", "DELETE", "PATCH", "propose", "submit"] {
            assert!(!router.contains(word), "{word}");
        }
    }

    #[test]
    fn parses_a_request_head() {
        let parsed = parse_request(b"GET /x/doc/a HTTP/1.1\r\nHost: 127.0.0.1:1\r\nOrigin: o\r\n\r\n").unwrap();
        assert_eq!(parsed.method, "GET");
        assert_eq!(parsed.headers[0], ("host".into(), "127.0.0.1:1".into()));
        assert!(parse_request(b"GET /x\r\n\r\n").is_err());
    }
}
