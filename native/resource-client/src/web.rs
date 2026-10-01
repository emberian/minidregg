//! `mini web`: the participant's own view of the node as plain hypertext.
//!
//! A loopback HTTP server beside the client. Every page that shows kernel
//! state is one or more signed reads under the workspace's own key, through
//! `workspace::signed_view` / `workspace::rendered_document` (the paths
//! `workspace --action read` and `doc-show` take). A document renders through
//! the Host's `inspect view-document`: the kernel's element-tree order, with
//! transclusions inline as this reader's own source reads render them; links
//! and backlinks are the Host's link-index views; history, a page at a past
//! height and a diff are K-DOC-HISTORY's `at`-height reads. There is no write route: the router
//! answers GET and HEAD and nothing else. It binds 127.0.0.1 only, accepts only
//! `Host: 127.0.0.1:PORT` / `localhost:PORT` (the DNS-rebinding guard), refuses a
//! foreign `Origin`, and every path sits under a per-launch secret printed at
//! start, so another local user or a page in the browser cannot read it.

use crate::workspace;
use crate::{absolute, hex, path, Args, Result};
use serde_json::Value;
use std::collections::BTreeSet;
use std::fs;
use std::io::{Read, Write};
use std::net::{Ipv4Addr, SocketAddr, TcpListener, TcpStream};
use std::path::PathBuf;
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

/// Everything `render_document` needs; built from real reads, or from fixtures.
pub(crate) struct DocInput<'a> {
    pub base: &'a str,
    /// The page's lines in the kernel's order (`workspace::document_lines`).
    pub lines: &'a [Value],
    /// The host page's entries (annotations, link records).
    pub entries: &'a [Value],
    /// The K-DOC-INDEX `links` / `backlinks` view rows; `None` on a page at a
    /// past height (the index answers the current height only).
    pub links: Option<&'a [Value]>,
    pub backlinks: Option<&'a [Value]>,
    /// workspace reference name for a cell or document id
    pub names: &'a dyn Fn(&str) -> Option<String>,
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

fn annotations_of(annotations: &[&Value], atom: &str) -> String {
    let mut notes = String::new();
    for annotation in annotations.iter().filter(|annotation| {
        annotation["anchor"]["type"].as_str() == Some("atom")
            && annotation["anchor"]["atom"].as_str() == Some(atom)
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
                " <em>(stale: the line moved since this was written)</em>"
            } else {
                " <em>(fresh)</em>"
            }
        ));
    }
    notes
}

/// One transclusion, inline at its place: its mark (snapshot, snapshot at H,
/// live, live revised) and lines when this reader's own source read rendered
/// it; the placeholder (shape only) when it did not.
fn transclusion_cell(base: &str, names: &dyn Fn(&str) -> Option<String>, item: &Value) -> (String, String) {
    let render = &item["render"];
    let view = render["view"].as_str().unwrap_or("unrendered").to_owned();
    let source = item["opening"]["source"].as_str().unwrap_or("?");
    let atoms = item["opening"]["atoms"].as_str().unwrap_or("?");
    let from = doc_link(base, names, source);
    let shown = match view.as_str() {
        "snapshot" | "live" => {
            let mark = if view == "snapshot" {
                match item["at"].as_str() {
                    Some(height) => format!("snapshot at height {}", escape(height)),
                    None => "snapshot".to_owned(),
                }
            } else if render["revised"] == true {
                "live, revised since it was transcluded".to_owned()
            } else {
                "live".to_owned()
            };
            let lines: Vec<String> = render["lines"]
                .as_array()
                .map(|lines| {
                    lines
                        .iter()
                        .filter_map(Value::as_str)
                        .map(|line| escape(&bytes_text(line)))
                        .collect()
                })
                .unwrap_or_default();
            format!(
                "<p class=note>[{mark} of {from}]</p><blockquote>{}</blockquote>",
                lines.join("<br>")
            )
        }
        "unavailable" => format!(
            "<p class=note data-placeholder>[transclusion: {} atoms of {from}, not readable by you]</p>",
            escape(atoms)
        ),
        "moved" => format!(
            "<p class=stale data-placeholder>[snapshot of {from}: its lines moved since height {}, and your grant \
             did not cover the source then]</p>",
            escape(render["height"].as_str().unwrap_or("?"))
        ),
        other => format!("<p class=stale>[transclusion of {from}: {}]</p>", escape(other)),
    };
    (view, shown)
}

pub(crate) fn render_document(input: &DocInput<'_>, shown: &[Value]) -> String {
    let base = input.base;
    let mut out = String::new();
    let annotations = of_type(input.entries, "annotation");
    let numbered = input.lines.iter().filter(|line| !line["line"].is_null()).count();
    out.push_str(&format!(
        "<section><h2>Lines</h2>\n<p class=note>In the kernel's document order (the element tree's walk); \
         nothing is sorted here.</p>\n<table data-lines=\"{numbered}\"><tr><th>#</th><th>text</th>\
         <th>creator</th><th>revision</th><th>element</th></tr>\n"
    ));
    for line in input.lines {
        let element = line["element"].as_str().unwrap_or("?");
        let kind = line["kind"].as_str().unwrap_or("?");
        let depth = line["depth"].as_u64().unwrap_or(1).saturating_sub(1) as usize;
        let indent = format!(" style=\"padding-left:{}rem\"", depth);
        let number = line["line"]
            .as_u64()
            .map(|n| n.to_string())
            .unwrap_or_else(|| if kind == "atom" { "-".into() } else { String::new() });
        let (attrs, cell, creator, revision) = match kind {
            "atom" => {
                let atom = line["atom"].as_str().unwrap_or("?");
                let text = bytes_text(line["payload"].as_str().unwrap_or(""));
                let struck = line["struck"] == true;
                let shown_text = if struck {
                    format!("<del>{}</del>", escape(&text))
                } else {
                    escape(&text)
                };
                (
                    format!(
                        " data-atom=\"{}\" data-creator=\"{}\" data-revision=\"{}\" data-struck=\"{struck}\"",
                        escape(atom),
                        escape(subject_of(&line["createdBy"])),
                        escape(line["revision"].as_str().unwrap_or("?"))
                    ),
                    format!("{shown_text}{}", annotations_of(&annotations, atom)),
                    escape(subject_of(&line["createdBy"])),
                    short(line["revision"].as_str().unwrap_or("?")),
                )
            }
            "embed" => {
                let id = line["transclusion"].as_str().unwrap_or("?");
                let item = shown.iter().find(|item| item["id"].as_str() == Some(id));
                let (view, cell) = match item {
                    Some(item) => transclusion_cell(base, input.names, item),
                    None => ("unrendered".to_owned(), "<p class=note>[transclusion]</p>".to_owned()),
                };
                let mode = item.and_then(|item| item["mode"].as_str()).unwrap_or("?");
                (
                    format!(
                        " data-transclusion=\"{}\" data-mode=\"{}\" data-render=\"{}\"",
                        escape(id),
                        escape(mode),
                        escape(&view)
                    ),
                    cell,
                    String::new(),
                    String::new(),
                )
            }
            "container" => (
                format!(" data-section=\"{}\"", escape(line["revision"].as_str().unwrap_or("?"))),
                format!("<strong>section {}</strong>", short(element)),
                String::new(),
                short(line["revision"].as_str().unwrap_or("?")),
            ),
            other => (String::new(), format!("[{}]", escape(other)), String::new(), String::new()),
        };
        out.push_str(&format!(
            "<tr data-element=\"{e}\" data-kind=\"{k}\" data-line=\"{n}\"{attrs}><td>{n}</td><td{indent}>{cell}</td>\
             <td>{creator}</td><td>{revision}</td><td class=id>{e}</td></tr>\n",
            e = escape(element),
            k = escape(kind),
            n = escape(&number),
        ));
    }
    out.push_str("</table></section>\n");

    match input.links {
        Some(rows) => {
            out.push_str(&format!(
                "<section><h2>Links out</h2>\n<ul data-links=\"{}\">\n",
                rows.len()
            ));
            for row in rows {
                let kind = row["kind"].as_str().unwrap_or("?");
                let target = row["target"].as_str().unwrap_or("?");
                let shown = match kind {
                    "document" | "range" => doc_link(base, input.names, target),
                    other => format!("{} {}", escape(other), short(target)),
                };
                out.push_str(&format!(
                    "<li data-link=\"{}\" data-kind=\"{}\">link {} -> {} (live since height {})</li>\n",
                    escape(row["link"].as_str().unwrap_or("?")),
                    escape(kind),
                    short(row["link"].as_str().unwrap_or("?")),
                    shown,
                    escape(row["height"].as_str().unwrap_or("?"))
                ));
            }
            out.push_str("</ul></section>\n");
        }
        None => out.push_str(
            "<section><h2>Links</h2><p class=note>Links and backlinks are the link index's current view; \
             a page at a past height does not show them.</p></section>\n",
        ),
    }

    if let Some(rows) = input.backlinks {
        out.push_str(&format!(
            "<section><h2>Backlinks</h2>\n<ul data-backlinks=\"{}\">\n",
            rows.len()
        ));
        for row in rows {
            let source = row["source"].as_str().unwrap_or("?");
            let from = (input.names)(source).unwrap_or_else(|| source.to_owned());
            let kind = row["kind"].as_str().unwrap_or("?");
            out.push_str(&format!(
                "<li data-backlink=\"{from}\" data-kind=\"{kind}\">{link} {kind} {id} (live since height {since})</li>\n",
                from = escape(&from),
                link = doc_link(base, input.names, source),
                kind = escape(kind),
                id = short(row["link"].as_str().unwrap_or("?")),
                since = escape(row["height"].as_str().unwrap_or("?")),
            ));
        }
        out.push_str(
            "</ul>\n<p class=note>From the Host's link index, cut to the documents a standing grant of yours \
             covers; a transclusion of this document counts as a backlink of it.</p></section>\n",
        );
    }
    out
}

fn change_text(change: &Value) -> String {
    let element = short(change["element"].as_str().unwrap_or("?"));
    let line = |value: &Value| -> String {
        match value["kind"].as_str() {
            Some("atom") => format!(
                "\"{}\"{}",
                escape(&bytes_text(value["payload"].as_str().unwrap_or(""))),
                if value["struck"] == true { " (struck)" } else { "" }
            ),
            Some("embed") => format!("transclusion {}", short(value["transclusion"].as_str().unwrap_or("?"))),
            Some("container") => "section".to_owned(),
            Some(other) => escape(other),
            None => "?".to_owned(),
        }
    };
    match change["type"].as_str() {
        Some("added") => format!("+ {element} {}", line(&change["after"])),
        Some("removed") => format!("- {element} {}", line(&change["before"])),
        Some("changed") => format!("~ {element} {} -> {}", line(&change["before"]), line(&change["after"])),
        Some("moved") => {
            let side = |value: &Value| value.as_str().map(short).unwrap_or_else(|| "the start".to_owned());
            format!("moved {element}: after {} -> after {}", side(&change["before"]), side(&change["after"]))
        }
        _ => escape(&change.to_string()),
    }
}

fn changes_list(changes: &Value) -> String {
    match changes.as_array() {
        Some(changes) if changes.is_empty() => "<p class=note>no change</p>".to_owned(),
        Some(changes) => {
            let mut out = format!("<ul data-changes=\"{}\">", changes.len());
            for change in changes {
                out.push_str(&format!(
                    "<li data-change=\"{}\" data-element=\"{}\">{}</li>",
                    escape(change["type"].as_str().unwrap_or("?")),
                    escape(change["element"].as_str().unwrap_or("?")),
                    change_text(change)
                ));
            }
            out.push_str("</ul>");
            out
        }
        None => "<p class=note data-no-content>content not shown: your grant did not cover this document at \
                 that height</p>"
            .to_owned(),
    }
}

/// `/doc/NAME/history`: K-DOC-HISTORY's rows. Every row says who wrote the
/// document at which height; its changes are shown only where this reader's
/// grant stood at the height (and the one below).
pub(crate) fn render_history(base: &str, name: &str, history: &Value) -> String {
    let rows = history["rows"].as_array().cloned().unwrap_or_default();
    let mut out = format!(
        "<section><h2>History</h2>\n<table data-history=\"{}\"><tr><th>height</th><th>subject</th>\
         <th>transaction</th><th>changes</th></tr>\n",
        rows.len()
    );
    for row in &rows {
        let height = row["height"].as_str().unwrap_or("?");
        let below = height.parse::<u64>().ok().and_then(|h| h.checked_sub(1));
        let links = match below {
            Some(below) => format!(
                " <a href=\"{base}/at/{h}/doc/{n}\">show</a> | <a href=\"{base}/doc/{n}/diff/{below}/{h}\">diff</a>",
                h = escape(height),
                n = escape(name)
            ),
            None => String::new(),
        };
        out.push_str(&format!(
            "<tr data-row=\"{h}\" data-subject=\"{s}\" data-content=\"{c}\"><td>{h}{links}</td><td>{s}</td>\
             <td>{t}</td><td>{changes}</td></tr>\n",
            h = escape(height),
            s = escape(row["subject"].as_str().unwrap_or("-")),
            t = short(row["transaction"].as_str().unwrap_or("?")),
            c = !row["changes"].is_null(),
            changes = changes_list(&row["changes"]),
        ));
    }
    out.push_str(
        "</table><p class=note>Rows are the signed log's writes of this document (your current grant decides \
         which you see); a row's content is read `at` its height, which the Host answers only when your grant \
         stood then.</p></section>\n",
    );
    out
}

/// `/doc/NAME/diff/H1/H2`: the changes between two pages at past heights.
pub(crate) fn render_diff(diff: &Value) -> String {
    format!(
        "<section><h2>Changes from height {} to height {}</h2>\n{}</section>\n",
        escape(diff["from"]["height"].as_str().unwrap_or("?")),
        escape(diff["to"]["height"].as_str().unwrap_or("?")),
        changes_list(&diff["changes"])
    )
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
            ["doc", name] => self.doc(name, None),
            ["doc", name, "history"] => self.history(name),
            ["doc", name, "diff", from, to] => self.diff(name, from, to),
            ["at", height, "doc", name] => self.doc(name, Some(height)),
            ["board", name] => self.board(name),
            ["room", name] => self.room(name),
            ["stream", _] => simple(
                501,
                "Not on this tree",
                "streams are K-STREAM (branch k-stream: the `tail` view); this mini was built from the \
                 docuverse braid, which does not carry k-stream",
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

    /// Cell id -> this workspace's reference name for it.
    fn targets(&self) -> Vec<(String, String)> {
        self.names()
            .into_iter()
            .filter_map(|other| {
                let reference = workspace::reference(&self.root, &other).ok()?;
                Some((reference["target"].as_str()?.to_owned(), other))
            })
            .collect()
    }

    fn reference(&self, name: &str) -> std::result::Result<Value, Page> {
        workspace::reference(&self.root, name).map_err(|error| {
            simple(404, name, &format!("no usable workspace reference named {name}: {error}"))
        })
    }

    fn read(&self, reference: &Value, view: &str) -> Result<(Value, Value, PathBuf)> {
        workspace::signed_view(&self.root, &self.workspace, reference, view)
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
                 <td><a href=\"{base}/doc/{n}\">doc</a> | <a href=\"{base}/doc/{n}/history\">history</a> | \
                 <a href=\"{base}/board/{n}\">board</a> | <a href=\"{base}/room/{n}\">room</a></td></tr>\n",
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

    /// `/doc/NAME` and `/at/H/doc/NAME`. Reads: the host page (current, or `at
    /// H` under the grant as it stood at H), one read per transcluded source
    /// (at H too, for a past page; plus an `at` read for a moved snapshot), and,
    /// for the current page, the link index's `links` and `backlinks` views.
    fn doc(&self, name: &str, at: Option<&str>) -> Page {
        let title = match at {
            Some(height) => format!("{name} at height {height}"),
            None => name.to_owned(),
        };
        if let Err(page) = self.reference(name) {
            return page;
        }
        let rendered = match workspace::rendered_document(&self.root, &self.workspace, name, None, at) {
            Ok(rendered) => rendered,
            Err(error) => return failure_page(&title, &error),
        };
        let challenge = workspace::bounded_json(&rendered.attempt.join("challenge.json")).unwrap_or(Value::Null);
        let context = ReadContext {
            height: challenge["height"].as_str().unwrap_or("?").to_owned(),
            authority_root: challenge["authorityRoot"].as_str().unwrap_or("?").to_owned(),
            cell_root: rendered.document["cellRoot"].as_str().unwrap_or("?").to_owned(),
        };
        let entries = rendered.view["cell"]["entries"].as_array().cloned().unwrap_or_default();
        let base = self.base();
        if at.is_none() && !is_content(&entries) {
            return Page {
                status: 200,
                title,
                stamp: Stamp::Read(context),
                body: format!(
                    "<p class=note>{0} is not a document; its fields are below (<a href=\"{base}/board/{0}\">as a \
                     board</a>).</p>\n{1}",
                    escape(name),
                    render_fields(&entries, false)
                ),
            };
        }
        let lines = match workspace::document_lines(&rendered) {
            Ok((lines, _)) => lines,
            Err(error) => return failure_page(&title, &error),
        };
        let reference = match self.reference(name) {
            Ok(reference) => reference,
            Err(page) => return page,
        };
        let index_view = |view: &str| -> std::result::Result<Option<Vec<Value>>, Page> {
            if at.is_some() {
                return Ok(None);
            }
            match self.read(&reference, view) {
                Ok((value, _, _)) => Ok(Some(value["rows"].as_array().cloned().unwrap_or_default())),
                Err(error) => Err(failure_page(&title, &error)),
            }
        };
        let links = match index_view("links") {
            Ok(rows) => rows,
            Err(page) => return page,
        };
        let backlinks = match index_view("backlinks") {
            Ok(rows) => rows,
            Err(page) => return page,
        };
        let targets = self.targets();
        let names = |id: &str| {
            targets
                .iter()
                .find(|(target, _)| target == id)
                .map(|(_, name)| name.clone())
        };
        let mut body = String::new();
        if let Some(height) = at {
            body.push_str(&format!(
                "<p class=note data-at=\"{h}\">This page is {n} as it stood at height {h} (state {s}), read under \
                 your grant as it stood then. <a href=\"{base}/doc/{n}\">current</a> | \
                 <a href=\"{base}/doc/{n}/history\">history</a></p>\n",
                h = escape(height),
                n = escape(name),
                s = escape(rendered.document["state"].as_str().unwrap_or("?")),
            ));
        } else {
            body.push_str(&format!(
                "<p class=note><a href=\"{base}/doc/{n}/history\">history</a></p>\n",
                n = escape(name)
            ));
        }
        body.push_str(&render_document(
            &DocInput {
                base: &base,
                lines: &lines,
                entries: &entries,
                links: links.as_deref(),
                backlinks: backlinks.as_deref(),
                names: &names,
            },
            &rendered.shown,
        ));
        Page {
            status: 200,
            title,
            stamp: Stamp::Read(context),
            body,
        }
    }

    fn history(&self, name: &str) -> Page {
        let title = format!("history of {name}");
        if let Err(page) = self.reference(name) {
            return page;
        }
        match workspace::doc_history(&self.root, &self.workspace, name) {
            Ok(history) => Page {
                status: 200,
                title,
                stamp: Stamp::None,
                body: render_history(&self.base(), name, &history),
            },
            Err(error) => failure_page(&title, &error),
        }
    }

    fn diff(&self, name: &str, from: &str, to: &str) -> Page {
        let title = format!("{name}: height {from} to {to}");
        if let Err(page) = self.reference(name) {
            return page;
        }
        if !from.bytes().all(|byte| byte.is_ascii_digit()) || !to.bytes().all(|byte| byte.is_ascii_digit()) {
            return simple(404, "Not found", "a height is a decimal");
        }
        match workspace::doc_diff(&self.root, &self.workspace, name, from, to) {
            Ok(diff) => Page {
                status: 200,
                title,
                stamp: Stamp::None,
                body: render_diff(&diff),
            },
            Err(error) => failure_page(&title, &error),
        }
    }

    fn board(&self, name: &str) -> Page {
        let reference = match self.reference(name) {
            Ok(reference) => reference,
            Err(page) => return page,
        };
        match self.read(&reference, "resource") {
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

    /// `/room/NAME`: the room cell, what this workspace created in it, and its
    /// members (K-INDEX's `who`: the subjects a standing grant covers the room
    /// with, and when each was last seen writing).
    fn room(&self, name: &str) -> Page {
        let reference = match self.reference(name) {
            Ok(reference) => reference,
            Err(page) => return page,
        };
        let target = reference["target"].as_str().unwrap_or("?").to_owned();
        let (view, challenge, _) = match self.read(&reference, "resource") {
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
             </section>\n<section><h2>Members</h2>\n",
        );
        match self.read(&reference, "who") {
            Ok((who, _, _)) => {
                let members = who["members"].as_array().cloned().unwrap_or_default();
                body.push_str(&format!("<ul data-members=\"{}\">\n", members.len()));
                for member in &members {
                    let subject = member["subject"].as_str().unwrap_or("?");
                    body.push_str(&format!(
                        "<li data-member=\"{0}\">subject {0}{1}</li>\n",
                        escape(subject),
                        match member["lastSeen"].as_str() {
                            Some(height) => format!(", last wrote at height {}", escape(height)),
                            None => ", has not written".to_owned(),
                        }
                    ));
                }
                body.push_str(
                    "</ul><p class=note>The subjects a standing grant covers this room with (the Host's `who` \
                     view, cut by your grant).</p>",
                );
            }
            Err(error) => body.push_str(&format!(
                "<p class=note data-members-refused>members not shown: {}</p>",
                escape(&refusal_text(&error).unwrap_or(error))
            )),
        }
        body.push_str("</section>\n");
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
    use serde_json::json;

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

    /// A page in the kernel's order (`workspace::document_lines`' shape): a
    /// struck line, a section, a transclusion, a line after it.
    fn page_lines() -> Vec<Value> {
        vec![
            json!({"element":"1002","parent":"1","kind":"atom","atom":"1002","payload":hex(b"second, placed first"),
                "revision":"71","createdBy":{"subject":"7"},"struck":false,"line":1,"depth":1}),
            json!({"element":"1001","parent":"1","kind":"atom","atom":"1001","payload":hex(b"the first line"),
                "revision":"70","createdBy":{"subject":"7"},"struck":true,"line":null,"depth":1}),
            json!({"element":"5","parent":"1","kind":"container","revision":"72","children":"1","line":null,"depth":1}),
            json!({"element":"8001","parent":"5","kind":"embed","transclusion":"8001","line":2,"depth":2}),
            json!({"element":"8002","parent":"1","kind":"embed","transclusion":"8002","line":3,"depth":1}),
        ]
    }

    fn shown() -> Vec<Value> {
        vec![
            json!({"id":"8001","mode":"snapshot","opening":{"source":"15383085687320778865","atoms":"2"},
                "render":{"view":"snapshot","lines":[hex(b"w2"),hex(b"w3")]},"at":"27"}),
            json!({"id":"8002","mode":"live","opening":{"source":"15383085687320778865","atoms":"3"},
                "render":{"view":"unavailable","atoms":"3","source":"15383085687320778865"}}),
        ]
    }

    #[test]
    fn lines_follow_the_kernel_order_with_transclusions_inline() {
        let lines = page_lines();
        let entries = vec![json!({"type":"annotation","id":"7001","anchor":{"type":"atom","atom":"1002"},
            "fresh":false,"author":{"subject":"9"},"body":{"type":"inline","bytes":hex(b"cite this")}})];
        let names = |id: &str| (id == "15383085687320778865").then(|| "wall".to_owned());
        let html = render_document(
            &DocInput {
                base: "/t",
                lines: &lines,
                entries: &entries,
                links: Some(&[]),
                backlinks: Some(&[]),
                names: &names,
            },
            &shown(),
        );
        let first = html.find("data-element=\"1002\"").unwrap();
        let struck = html.find("data-element=\"1001\"").unwrap();
        let section = html.find("data-section=\"72\"").unwrap();
        let embed = html.find("data-transclusion=\"8001\"").unwrap();
        assert!(first < struck && struck < section && section < embed);
        assert!(html.contains("data-lines=\"3\""));
        assert!(html.contains("<del>the first line</del>"));
        assert!(html.contains("data-transclusion=\"8001\" data-mode=\"snapshot\" data-render=\"snapshot\""));
        assert!(html.contains("[snapshot at height 27 of <a href=\"/t/doc/wall\">wall</a>]"));
        assert!(html.contains("w2<br>w3"));
        assert!(html.contains("data-transclusion=\"8002\" data-mode=\"live\" data-render=\"unavailable\""));
        assert!(html.contains("data-placeholder>[transclusion: 3 atoms of <a href=\"/t/doc/wall\">wall</a>, not readable by you]"));
        assert!(html.contains("data-annotation=\"7001\" data-fresh=\"false\""));
        assert!(html.contains("cite this"));
    }

    #[test]
    fn links_and_backlinks_come_from_the_index_views() {
        let lines = page_lines();
        let links = vec![json!({"source":"3","link":"9101","kind":"document","target":"15383085687320778865",
            "relation":"0","revision":"1","height":"20"})];
        let backlinks = vec![
            json!({"source":"44","link":"9201","kind":"document","target":"3","relation":"0","revision":"1","height":"21"}),
            json!({"source":"45","link":"9301","kind":"transclusion","target":"8009","relation":"5","revision":"1","height":"22"}),
        ];
        let names = |id: &str| match id {
            "15383085687320778865" => Some("paper".to_owned()),
            "44" => Some("notes".to_owned()),
            _ => None,
        };
        let html = render_document(
            &DocInput {
                base: "/t",
                lines: &lines,
                entries: &[],
                links: Some(&links),
                backlinks: Some(&backlinks),
                names: &names,
            },
            &shown(),
        );
        assert!(html.contains("data-link=\"9101\" data-kind=\"document\">link <span class=id>9101</span> -> <a href=\"/t/doc/paper\">paper</a>"));
        assert!(html.contains("data-backlinks=\"2\""));
        assert!(html.contains("data-backlink=\"notes\" data-kind=\"document\""));
        assert!(html.contains("data-backlink=\"45\" data-kind=\"transclusion\""));
        let past = render_document(
            &DocInput {
                base: "/t",
                lines: &lines,
                entries: &[],
                links: None,
                backlinks: None,
                names: &names,
            },
            &shown(),
        );
        assert!(!past.contains("data-backlinks"));
        assert!(past.contains("a page at a past height does not show them"));
    }

    #[test]
    fn history_rows_show_content_only_where_the_grant_stood() {
        let history = json!({"rows":[
            {"height":"99","subject":"7","transaction":"1","changes":null},
            {"height":"103","subject":"8","transaction":"2","changes":[
                {"type":"changed","element":"1001","before":{"kind":"atom","payload":hex(b"a")},
                    "after":{"kind":"atom","payload":hex(b"b")}},
                {"type":"moved","element":"1002","before":null,"after":"1001"}]}]});
        let html = render_history("/t", "paper", &history);
        assert!(html.contains("data-history=\"2\""));
        assert!(html.contains("data-row=\"99\" data-subject=\"7\" data-content=\"false\""));
        assert!(html.contains("data-no-content"));
        assert!(html.contains("data-row=\"103\" data-subject=\"8\" data-content=\"true\""));
        assert!(html.contains("~ <span class=id>1001</span> \"a\" -> \"b\""));
        assert!(html.contains("data-change=\"moved\""));
        assert!(html.contains("<a href=\"/t/at/103/doc/paper\">show</a> | <a href=\"/t/doc/paper/diff/102/103\">diff</a>"));
        let diff = render_diff(&json!({"from":{"height":"100"},"to":{"height":"104"},"changes":[
            {"type":"added","element":"1003","after":{"kind":"atom","payload":hex(b"c")}}]}));
        assert!(diff.contains("from height 100 to height 104"));
        assert!(diff.contains("+ <span class=id>1003</span> \"c\""));
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
        let hostile = vec![json!({"element":"1","parent":"0","kind":"atom","atom":"1","createdBy":{"subject":"7"},
            "revision":"1","struck":false,"line":1,"depth":1,"payload":hex(b"<script>alert(1)</script>")})];
        let html = render_document(
            &DocInput {
                base: "/t",
                lines: &hostile,
                entries: &[],
                links: None,
                backlinks: None,
                names: &no_names,
            },
            &[],
        );
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
