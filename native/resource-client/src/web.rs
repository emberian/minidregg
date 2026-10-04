//! `mini web`: the participant's own view of the node as plain hypertext.
//!
//! A loopback HTTP server beside the client. Every page that shows kernel
//! state is one or more signed reads under the workspace's own key, through
//! `workspace::signed_view` / `workspace::rendered_document` (the paths
//! `workspace --action read` and `doc-show` take). A document renders through
//! the Host's `inspect view-document`: the kernel's element-tree order, with
//! transclusions inline as this reader's own source reads render them; links
//! and backlinks are the Host's link-index views; history, a page at a past
//! height and a diff are K-DOC-HISTORY's `at`-height reads. Document POST forms
//! use the native client's pinned diff and durable attempt. It binds 127.0.0.1 only, accepts only
//! `Host: 127.0.0.1:PORT` / `localhost:PORT` (the DNS-rebinding guard), refuses a
//! foreign `Origin`, and every path sits under a per-launch secret printed at
//! start, so another local user or a page in the browser cannot read it.

mod editor;
#[path = "web_admission.rs"]
mod admission;
mod create;
mod inspect;
mod resident;
#[path = "web/world.rs"]
mod world;
mod surface;
mod studio;
#[path = "web/search.rs"]
mod search;

use crate::workspace;
use crate::{absolute, hex, path, Args, Result};
use serde_json::Value;
use std::collections::BTreeSet;
use std::fs;
use std::io::{Read, Write};
use std::net::{Ipv4Addr, SocketAddr, TcpListener, TcpStream};
use std::path::PathBuf;
use std::time::{Duration, Instant};
use std::sync::{Arc, Mutex};

const MAX_REQUEST: usize = 16 * 1024;

const CSS: &str = "body{font:15px/1.45 system-ui,sans-serif;max-width:60rem;margin:1rem auto;\
padding:0 1rem;color:#1d1d1f;background:#fdfdfb}a{color:#0b5cad}\
header{border-bottom:1px solid #ccc;margin-bottom:1rem}.ctx{font-size:12px;color:#555}\
table{border-collapse:collapse;width:100%}td,th{border-bottom:1px solid #e3e3e3;padding:.2rem .4rem;\
text-align:left;vertical-align:top}code,.id{font:12px ui-monospace,monospace;overflow-wrap:anywhere}\
pre{white-space:pre-wrap;overflow-wrap:anywhere}\
.refusal{border-left:4px solid #b3261e;padding:.4rem .8rem;background:#fbeeee}\
.note{color:#555;font-size:13px}blockquote{border-left:3px solid #999;margin:.3rem 0;padding:0 .7rem}\
.stale{color:#8a5a00}.ann{font-size:13px;color:#333;margin:.2rem 0 .2rem 1rem}";

pub(crate) fn run(mut args: Args) -> Result<()> {
    let listen = args
        .required("listen")?
        .into_string()
        .map_err(|_| "--listen must be UTF-8".to_owned())?;
    let root = absolute(&path(args.required("dir")?))?;
    let home = args.optional("home").map(|v| absolute(&path(v))).transpose()?;
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
        mutations: Mutex::new(()),
        home,
        subject: workspace::member(&workspace, "subject")?.to_owned(),
        root,
        workspace,
        token,
        port: bound.port(),
    };
    println!(
        "mini web: workspace for subject {} at http://127.0.0.1:{}/{}/",
        site.subject, site.port, site.token
    );
    println!("mini web: the path secret changes every launch; document forms use your current authority");
    std::io::stdout().flush().map_err(|error| error.to_string())?;
    let site = Arc::new(site);
    let handler: Arc<dyn Fn(TcpStream, Instant) + Send + Sync> = Arc::new(move |stream, deadline| {
        if let Err(error) = site.serve(stream, deadline) {
            eprintln!("mini web: {error}");
        }
    });
    let connections = admission::Pool::new(admission::MAX_CONNECTIONS);
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                if let Err(error) = connections.dispatch(stream, handler.clone()) {
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
    // Forms and draft-opening GETs may mutate owner-private custody. Complete
    // ingress first, then serialize those paths without blocking signed views.
    mutations: Mutex<()>,
    home: Option<PathBuf>,
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
    if !matches!(request.method.as_str(), "GET" | "HEAD" | "POST") {
        return Gate::Refuse(
            405,
            format!("{}: this server answers GET, HEAD and document POST forms only", request.method),
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
    if request.method == "POST" {
        let parts: Vec<_> = segments.iter().map(String::as_str).collect();
        if !matches!(parts.as_slice(), ["doc",_,"edit",_] | ["doc",_,"edit",_,"lookup"] | ["doc",_,"edit",_,"action"] | ["new-document",_] | ["new-document",_,"lookup"] | ["new-document",_,"finish"] | ["studio","new"] | ["studio",_,"manifest" | "snapshot" | "compose" | "fork" | "preview"]) {
            return Gate::Refuse(405,"this address accepts reads only".into());
        }
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
    /// A retained editing base; sidebar observations may be newer.
    EditBase(ReadContext),
    /// Search results use independent current authorized reads, not one shared head.
    CurrentReads(usize),
    /// Fresh content could not be obtained; never label a retained hit current.
    Unavailable,
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

pub(crate) fn wrap(page: &Page, base: &str, subject: &str) -> String {
    let context = match &page.stamp {
        Stamp::Read(read) | Stamp::EditBase(read) => format!(
            "{}read as subject <span class=id>{}</span> at height <span class=id data-height=\"{}\">{}</span> \
             | authority root {} | cell root {}",
            if matches!(&page.stamp,Stamp::EditBase(_)) {"Editor base snapshot: "} else {""},
            escape(subject),
            escape(&read.height),
            escape(&read.height),
            short(&read.authority_root),
            short(&read.cell_root)
        ),
        Stamp::CurrentReads(0) => "No readable documents in this search page".into(),
        Stamp::CurrentReads(count) => format!(
            "Current authorized {}", if *count == 1 { "document read".to_owned() } else { format!("reads of {count} documents") }
        ),
        Stamp::Unavailable => "Current text unavailable".into(),
        Stamp::Refused => format!(
            "subject <span class=id>{}</span> | the Host refused this page's signed read",
            escape(subject)
        ),
        Stamp::None => format!(
            "subject <span class=id>{}</span> | no signed read on this page",
            escape(subject)
        ),
    };
    let context = match &page.stamp {
        Stamp::Read(_) => format!("<details><summary>Authorized read</summary><p>{context}</p></details>"),
        Stamp::EditBase(_) => format!("<details><summary>Editor base snapshot</summary><p>{context}</p></details>"),
        _ => context,
    };
    format!(
        "<!doctype html>\n<html lang=en><head><meta charset=utf-8>\
         <meta name=viewport content=\"width=device-width\"><meta name=referrer content=same-origin>\
         <title>{title} | mini</title><style>{CSS}</style></head><body>\n\
         <header><nav><a href=\"{base}/\">workspace</a> | <a href=\"{base}/search\">search</a></nav><h1>{title}</h1><div class=ctx>{context}</div></header>\n\
         <main>\n{body}</main></body></html>\n",
        title = escape(&page.title),
        body = page.body,
    )
}

/// A refusal the Host decided, as the Host's own decoding of its refusal frame
/// names it (`<reason>: <text>`, P-LAW's clause for a law refusal; the client's
/// `refusal_line`). `None` for a client-side failure. The frame is never read
/// for printable runs: a frame the Host did not decode says so.
pub(crate) fn refusal_text(error: &str) -> Option<String> {
    let rest = error.split_once("host refused ")?.1;
    let line = rest.split_once("; encoded refusal: ").map_or(rest, |(head, _)| head);
    Some(match line.split_once(": ") {
        Some((_, decoded)) => decoded.strip_prefix("refused: ").unwrap_or(decoded).to_owned(),
        None => "the Host refused this read; its refusal frame was not decoded".to_owned(),
    })
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

pub(crate) fn is_content(entries: &[Value]) -> bool {
    entries.iter().any(|entry| entry.get("type").is_some())
}

fn doc_link(base: &str, names: &dyn Fn(&str) -> Option<String>, document: &str) -> String {
    match names(document) {
        Some(name) => format!("<a href=\"{base}/doc/{0}\">{0}</a>", escape(&name)),
        None => format!("document {} (not in your workspace)", short(document)),
    }
}

/// The link index's views on a current page: links out (the `links` view) and
/// backlinks (the `backlinks` view, cut by the Host to the documents a standing
/// grant of this reader covers). Not part of the document: `doc show` prints
/// the document, `doc links` / `doc backlinks` print these.
pub(crate) fn index_sections(
    base: &str,
    names: &dyn Fn(&str) -> Option<String>,
    links: Option<&[Value]>,
    backlinks: Option<&[Value]>,
) -> String {
    let mut out = String::new();
    match links {
        Some(rows) => {
            out.push_str(&format!(
                "<section><h2>Links out</h2>\n<ul data-links=\"{}\">\n",
                rows.len()
            ));
            for row in rows {
                let kind = row["kind"].as_str().unwrap_or("?");
                let target = row["target"].as_str().unwrap_or("?");
                let shown = match kind {
                    "document" | "range" => doc_link(base, names, target),
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
            "<section><h2>Links</h2><p class=note>Links and backlinks are available in the current document view.</p></section>\n",
        ),
    }
    if let Some(rows) = backlinks {
        out.push_str(&format!(
            "<section><h2>Backlinks</h2>\n<ul data-backlinks=\"{}\">\n",
            rows.len()
        ));
        for row in rows {
            let source = row["source"].as_str().unwrap_or("?");
            let from = names(source).unwrap_or_else(|| source.to_owned());
            let kind = row["kind"].as_str().unwrap_or("?");
            out.push_str(&format!(
                "<li data-backlink=\"{from}\" data-kind=\"{kind}\">{link} {kind} {id} (live since height {since})</li>\n",
                from = escape(&from),
                link = doc_link(base, names, source),
                kind = escape(kind),
                id = short(row["link"].as_str().unwrap_or("?")),
                since = escape(row["height"].as_str().unwrap_or("?")),
            ));
        }
        out.push_str(
            "</ul>\n<p class=note>Incoming links and embedded quotations visible to you.</p></section>\n",
        );
    }
    out
}

/// `/doc/NAME/history`: K-DOC-HISTORY's rows through the one renderer
/// (`render::history`), each height linked to its page and its diff.
pub(crate) fn render_history(base: &str, name: &str, history: &Value) -> String {
    let links = |height: &str| match height.parse::<u64>().ok().and_then(|h| h.checked_sub(1)) {
        Some(below) => format!(
            " <a href=\"{base}/at/{h}/doc/{n}\">show</a> | <a href=\"{base}/doc/{n}/diff/{below}/{h}\">diff</a>",
            h = escape(height),
            n = escape(name)
        ),
        None => String::new(),
    };
    format!(
        "<section><h2>History</h2>\n{}<p class=note>Rows are the signed log's writes of this document (your current \
         grant decides which you see); a row's content is read `at` its height, which the Host answers only when \
         your grant stood then.</p></section>\n",
        crate::render::history::history_html(history, &links)
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
        // Field addresses are sparse u128 values. Visit only present state
        // fields; scanning all task numbers up to the largest field would let
        // a single high address stall every browser worker. Keep the first
        // sorted value for duplicate addresses, as the prior lookup did.
        let mut values = std::collections::BTreeMap::new();
        for (field, value) in &fields {
            values.entry(*field).or_insert(value.as_str());
        }
        out.push_str("<section><h2>Tasks</h2>\n<table><tr><th>task</th><th>state</th><th>owner</th></tr>\n");
        let mut count = 0;
        for (&field, &state) in &values {
            if field < 2 || field % 2 != 0 { continue; }
            let n = (field - 2) / 2;
            // A state field is even, so its following owner field cannot
            // overflow u128 (whose maximum is odd).
            let owner = values.get(&(field + 1)).copied().unwrap_or("(none)");
            count += 1;
            out.push_str(&format!(
                "<tr data-task=\"{n}\"><td>{n}</td><td>{}</td><td>{}</td></tr>\n",
                escape(state),
                escape(owner)
            ));
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

    fn serve(&self, mut stream: TcpStream, deadline: Instant) -> Result<()> {
        stream
            .set_write_timeout(Some(Duration::from_secs(10)))
            .map_err(|error| error.to_string())?;
        let mut head = Vec::new();
        let mut buffer = [0u8; 2048];
        while !head.windows(4).any(|window| window == b"\r\n\r\n") {
            let read = admission::read_ingress(&mut stream, &mut buffer, deadline).map_err(|error| error.to_string())?;
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
            Gate::Route(segments) if request.method == "POST" => {
                let length = match editor::body_length(&request) {
                    Ok(length) => length,
                    Err(error) => return respond(&mut stream,false,&simple(400,"Cannot save",&error),&self.base(),&self.subject),
                };
                let end = head.windows(4).position(|w| w == b"\r\n\r\n").unwrap() + 4;
                let mut body = head[end..].to_vec();
                if body.len() > length { return respond(&mut stream,false,&simple(400,"Cannot save","unexpected bytes after the form"),&self.base(),&self.subject); }
                while body.len() < length {
                    let remaining = (length-body.len()).min(buffer.len());
                    let read = admission::read_ingress(&mut stream, &mut buffer[..remaining], deadline).map_err(|e|e.to_string())?;
                    if read == 0 { return respond(&mut stream,false,&simple(400,"Cannot save","incomplete document form"),&self.base(),&self.subject); }
                    body.extend_from_slice(&buffer[..read]);
                }
                let _mutation = self.mutations.lock().map_err(|_| "browser custody lock poisoned")?;
                let parts: Vec<_> = segments.iter().map(String::as_str).collect();
                match parts.as_slice() {
                    ["doc",name,"edit",id] => editor::post(self,name,id,&body,false),
                    ["doc",name,"edit",id,"lookup"] => editor::post(self,name,id,&body,true),
                    ["doc",name,"edit",id,"action"] => editor::action(self,name,id,&body),
                    ["studio","new"] => studio::post(self,None,"new",&body),
                    ["studio",id,action @ ("manifest" | "snapshot" | "compose" | "fork" | "preview")] => studio::post(self,Some(id),action,&body),
                    ["new-document",id] => create::post(self,id,&body,"create"),
                    ["new-document",id,op] => create::post(self,id,&body,op),
                    _ => simple(405,"Cannot save","this address accepts reads only"),
                }
            }
            Gate::Route(segments) if segments == ["search"] => search::page(self, &request.target),
            Gate::Route(segments) => {
                let draft = matches!(segments.first().map(String::as_str), Some("new-document"))
                    || segments.get(2).is_some_and(|part| part == "edit" || part == "new-document")
                    || segments.first().is_some_and(|part| part == "studio")
                        && segments.get(2).is_some_and(|part| part == "module");
                let _mutation = if draft {
                    Some(self.mutations.lock().map_err(|_| "browser custody lock poisoned")?)
                } else { None };
                self.route(&segments)
            },
        };
        respond(&mut stream, head_only, &page, &self.base(), &self.subject)
    }

    fn route(&self, segments: &[String]) -> Page {
        let parts: Vec<&str> = segments.iter().map(String::as_str).collect();
        match parts.as_slice() {
            [] => self.index(),
            ["studio"] => studio::index(self),
            ["studio","new"] => studio::new(self),
            ["studio",id] => studio::package(self,id),
            ["studio",id,"module",index] => studio::module(self,id,index,false),
            ["studio",id,"module",index,"fresh"] => studio::module(self,id,index,true),
            ["studio",id,"draft",submission] => studio::submitted(self,id,submission),
            ["studio",id,"snapshot",snapshot] => studio::captured(self,id,snapshot),
            ["studio",id,"snapshot",snapshot,"preview",run] => studio::preview(self,id,snapshot,run),
            ["studio",id,"history",revision] => studio::history(self,id,revision),
            ["new-document"] => create::open(self,None,None),
            ["new-document",id] => create::open(self,Some(id),None),
            ["room",name,"new-document"] => create::open(self,None,Some(name)),
            ["doc",name,"inspect"] => inspect::page(self,name),
            ["search-hit", name, target, atom, revision] => search::hit(self,name,target,atom,revision),
            ["doc", name] => self.doc(name, None),
            ["doc",name,"edit"] => editor::open(self,name,None),
            ["doc",name,"edit",id] => editor::open(self,name,Some(id)),
            ["doc", name, "history"] => self.history(name),
            ["doc", name, "diff", from, to] => self.diff(name, from, to),
            ["at", height, "doc", name] => self.doc(name, Some(height)),
            ["object",name] => world::page(self,name,false),
            ["object",name,"behavior"] => world::page(self,name,true),
            ["board", name] => self.board(name),
            ["room", name] => self.room(name),
            ["room",name,"resident"] => resident::page(self,name),
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
        // The birth source `create` retains (sources/create-NAME.json on final).
        let source = self.root.join("sources").join(format!("create-{name}.json"));
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
                 <a href=\"{base}/board/{n}\">board</a> | <a href=\"{base}/room/{n}\">room</a> | \
                 <a href=\"{base}/object/{n}\">object</a></td></tr>\n",
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
            ) + &format!("<p><a href=\"{base}/studio\">Source studio</a> | <a href=\"{base}/new-document\">Create a document</a></p>") + &create::recent(self),
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
        let (read, rendered) = match workspace::read_rendered(&self.root, &self.workspace, name, at) {
            Ok(both) => both,
            Err(error) => return failure_page(&title, &error),
        };
        let challenge = workspace::bounded_json(&read.attempt.join("challenge.json")).unwrap_or(Value::Null);
        let context = ReadContext {
            height: challenge["height"].as_str().unwrap_or("?").to_owned(),
            authority_root: challenge["authorityRoot"].as_str().unwrap_or("?").to_owned(),
            cell_root: read.document["cellRoot"].as_str().unwrap_or("?").to_owned(),
        };
        let entries = read.entries.clone();
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
                s = escape(read.document["state"].as_str().unwrap_or("?")),
            ));
        } else {
            body.push_str(&format!(
                "<p class=note><a href=\"{base}/doc/{n}/edit\">Edit and inspect</a> | <a href=\"{base}/doc/{n}/history\">history</a> | <a href=\"{base}/doc/{n}/inspect\">source and comments</a></p>\n",
                n = escape(name)
            ));
        }
        // The document is the one renderer's HTML, byte for byte what
        // `doc show --format html` prints for this read.
        body.push_str(&rendered.html(name));
        body.push_str(&index_sections(&base, &names, links.as_deref(), backlinks.as_deref()));
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
                body: crate::render::history::diff_html(&diff),
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
                let body = if let Some(body) = world::body(self,name,&view,false) {
                    body
                } else if is_content(&entries) {
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
            "<p><a href=\"{base}/room/{n}/new-document\">Create a document in this room</a> | <a href=\"{base}/room/{n}/resident\">Resident requests and output</a></p><p>The room cell itself: {} entries, <a href=\"{base}/doc/{n}\">open it</a>.</p>\n\
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
        409 => "Conflict",
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
         Referrer-Policy: same-origin\r\n\
         Content-Security-Policy: default-src 'none'; style-src 'unsafe-inline'; frame-ancestors 'none'; form-action 'self'; base-uri 'none'\r\n\
         {}Connection: close\r\n\r\n",
        page.status,
        reason(page.status),
        body.len(),
        if page.status == 405 { "Allow: GET, HEAD, POST\r\n" } else { "" },
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

    #[test]
    fn board_rendering_visits_sparse_state_fields_without_address_scan() {
        let high_state = u128::MAX - 1;
        let entries = vec![
            serde_json::json!({"key":{"field":u128::MAX.to_string()},"value":"high owner"}),
            serde_json::json!({"key":{"field":"3"},"value":"low owner"}),
            serde_json::json!({"key":{"field":high_state.to_string()},"value":"high state"}),
            serde_json::json!({"key":{"field":"2"},"value":"z duplicate"}),
            serde_json::json!({"key":{"field":"2"},"value":"a state"}),
            serde_json::json!({"key":{"field":"8"},"value":"unowned"}),
            serde_json::json!({"key":{"field":"0"},"value":"metadata"}),
        ];
        let html = render_fields(&entries, true);
        let low = "<tr data-task=\"0\"><td>0</td><td>a state</td><td>low owner</td></tr>";
        let unowned = "<tr data-task=\"3\"><td>3</td><td>unowned</td><td>(none)</td></tr>";
        let high = format!("<tr data-task=\"{}\"><td>{}</td><td>high state</td><td>high owner</td></tr>",
            (high_state - 2) / 2, (high_state - 2) / 2);
        assert!(html.find(low).unwrap() < html.find(unowned).unwrap());
        assert!(html.find(unowned).unwrap() < html.find(&high).unwrap());
        assert_eq!(html.matches("data-task=").count(), 3);
        assert!(html.contains("3 task(s)"));
        assert!(html.contains("data-fields=\"7\""));
    }
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

    /// A `view-document` in the kernel's order: a marked line, a struck line, a
    /// section holding a snapshot transclusion, a live transclusion after it.
    fn document() -> Value {
        json!({"root":"1","rootRevision":"60","order":[
            {"element":"1002","parent":"1","kind":"atom","atom":"1002","payload":hex(b"second, placed first"),
                "revision":"71","createdBy":{"subject":"7"},"struck":false,
                "marks":[{"kind":"bold","fresh":true},{"kind":"italic","fresh":false}]},
            {"element":"1001","parent":"1","kind":"atom","atom":"1001","payload":hex(b"the first line"),
                "revision":"70","createdBy":{"subject":"7"},"struck":true},
            {"element":"5","parent":"1","kind":"container","revision":"72","children":"1"},
            {"element":"8001","parent":"5","kind":"embed","transclusion":"8001"},
            {"element":"8002","parent":"1","kind":"embed","transclusion":"8002"}],
          "transclusions":[
            {"id":"8001","mode":"snapshot","opening":{"source":"15383085687320778865","atoms":"2","height":"27",
                "pins":[]},"render":{"view":"snapshot","lines":[hex(b"w2"),hex(b"w3")]},"at":"27"},
            {"id":"8002","mode":"live","opening":{"source":"15383085687320778865","atoms":"3","height":"28"},
                "render":{"view":"unavailable","atoms":"3","source":"15383085687320778865"}}]})
    }

    fn rendered(document: &Value, entries: &[Value]) -> crate::render::Rendered {
        let names = std::collections::BTreeMap::from([("15383085687320778865".to_owned(), "wall".to_owned())]);
        crate::render::render(&crate::render::View {
            document,
            entries,
            names: &names,
            sources: &std::collections::BTreeMap::new(),
            me: "7",
        })
        .unwrap()
    }

    #[test]
    fn lines_follow_the_kernel_order_with_transclusions_inline() {
        let entries = vec![json!({"type":"annotation","id":"7001","anchor":{"type":"atom","atom":"1002"},
            "fresh":false,"author":{"subject":"9"},"body":{"type":"inline","bytes":hex(b"cite this")}})];
        let html = rendered(&document(), &entries).html("paper");
        let first = html.find("data-element=\"1002\"").unwrap();
        let struck = html.find("data-element=\"1001\"").unwrap();
        assert!(!html.contains("data-section=\"72\"")); // empty structural row is not a visible line
        let embed = html.find("data-transclusion=\"8001\"").unwrap();
        assert!(first < struck && struck < embed);
        assert!(html.contains("class=\"line struck\" style=\"list-style:none\""));
        assert!(html.contains(
            "data-element=\"1002\" data-kind=\"atom\" data-line=\"1\" data-atom=\"1002\" data-creator=\"7\" \
             data-revision=\"71\" data-struck=\"false\" data-marks=\"bold,~italic\""
        ));
        assert!(html.contains("data-element=\"1001\" data-kind=\"atom\" data-line=\"-\""));
        assert!(html.contains("<del>the first line</del>"));
        assert!(html.contains("data-transclusion=\"8001\" data-mode=\"snapshot\" data-render=\"snapshot\""));
        assert!(html.contains("snapshot@27"));
        assert!(html.contains("<p class=\"quoted\">w2</p><p class=\"quoted\">w3</p>"));
        assert!(html.contains("data-transclusion=\"8002\" data-mode=\"live\" data-render=\"unavailable\""));
        assert!(html.contains("[transclusion: 3 atoms of wall, not readable by you]"));
        assert!(html.contains("data-annotation=\"7001\" data-fresh=\"false\""));
        assert!(html.contains("cite this"));
    }

    #[test]
    fn links_and_backlinks_come_from_the_index_views() {
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
        let html = index_sections("/t", &names, Some(&links), Some(&backlinks));
        assert!(html.contains("data-link=\"9101\" data-kind=\"document\">link <span class=id>9101</span> -> <a href=\"/t/doc/paper\">paper</a>"));
        assert!(html.contains("data-backlinks=\"2\""));
        assert!(html.contains("data-backlink=\"notes\" data-kind=\"document\""));
        assert!(html.contains("data-backlink=\"45\" data-kind=\"transclusion\""));
        let past = index_sections("/t", &names, None, None);
        assert!(!past.contains("data-backlinks"));
        assert!(past.contains("Links and backlinks are available in the current document view"));
    }

    /// A moved snapshot whose `at` read was refused `no-grant` renders the
    /// placeholder, in the shell and on the web alike (one renderer).
    #[test]
    fn a_refused_snapshot_read_is_the_moved_placeholder() {
        let mut document = document();
        document["transclusions"][0]["render"] = json!({"view":"moved","height":"27"});
        document["transclusions"][0]["atRefused"] = json!("27");
        let rendered = rendered(&document, &[]);
        let placeholder = "[snapshot of wall: its lines moved since height 27, and your grant did not cover wall then]";
        assert!(rendered.text().contains(placeholder));
        assert!(rendered.html("paper").contains(placeholder));
        assert!(!rendered.html("paper").contains(">w2<"));
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
        assert!(html.contains("~ 1001 &quot;a&quot; -&gt; &quot;b&quot;"));
        assert!(html.contains("data-change=\"moved\""));
        assert!(html.contains("<a href=\"/t/at/103/doc/paper\">show</a> | <a href=\"/t/doc/paper/diff/102/103\">diff</a>"));
        let diff = crate::render::history::diff_html(&json!({"from":{"height":"100"},"to":{"height":"104"},"changes":[
            {"type":"added","element":"1003","after":{"kind":"atom","payload":hex(b"c")}}]}));
        assert!(diff.contains("from height 100 to height 104"));
        assert!(diff.contains("+ 1003 &quot;c&quot;"));
        let text = crate::render::history::diff_text(&json!({"from":{"height":"100"},"to":{"height":"104"},
            "changes":[{"type":"moved","element":"1002","before":null,"after":"1001"}]}));
        assert_eq!(text, "# changes from height 100 to height 104
moved 1002: after the start -> after 1001
");
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
        assert!(page.body.contains("refused: no-grant: this key holds no grant"));
        let undecoded = failure_page("paper", "mini: host refused query; encoded refusal: 00ff");
        assert_eq!(undecoded.status, 403);
        assert!(undecoded.body.contains("frame was not decoded"));
        assert!(wrap(&page, "/t", "9").contains("the Host refused this page's signed read"));
        let page = failure_page("paper", "cannot open socket: no such file");
        assert_eq!(page.status, 502);
    }

    #[test]
    fn escapes_every_text_path() {
        assert_eq!(escape("<a href=\"x\">&'"), "&lt;a href=&quot;x&quot;&gt;&amp;&#39;");
        let hostile = json!({"root":"0","order":[{"element":"1","parent":"0","kind":"atom","atom":"1",
            "createdBy":{"subject":"7"},"revision":"1","struck":false,"payload":hex(b"<script>alert(1)</script>")}]});
        let html = rendered(&hostile, &[]).html("<p>");
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
    fn get_router_calls_no_submit_path() {
        let source = include_str!("web.rs");
        let router = &source[source.find("fn route(").unwrap()..source.find("fn names(").unwrap()];
        for word in ["POST", "PUT", "DELETE", "PATCH", "propose", "submit"] {
            assert!(!router.contains(word), "{word}");
        }
    }

    #[test]
    fn creation_posts_are_bounded_to_exact_session_routes() {
        for target in ["/secret/new-document/0123456789abcdef0123456789abcdef", "/secret/new-document/0123456789abcdef0123456789abcdef/lookup", "/secret/new-document/0123456789abcdef0123456789abcdef/finish"] {
            assert!(matches!(gate(&request("POST",target,&[("host","127.0.0.1:8080")]),8080,"secret"),Gate::Route(_)));
        }
        assert!(matches!(gate(&request("POST","/secret/room/lab/new-document",&[("host","127.0.0.1:8080")]),8080,"secret"),Gate::Refuse(405,_)));
    }

    #[test]
    fn parses_a_request_head() {
        let parsed = parse_request(b"GET /x/doc/a HTTP/1.1\r\nHost: 127.0.0.1:1\r\nOrigin: o\r\n\r\n").unwrap();
        assert_eq!(parsed.method, "GET");
        assert_eq!(parsed.headers[0], ("host".into(), "127.0.0.1:1".into()));
        assert!(parse_request(b"GET /x\r\n\r\n").is_err());
    }
}
