//! `mini-web`: the Mini web front end's gateway (docs/WEB-FRONTEND-2026-10-27.md). Loopback HTTP
//! behind Caddy, uid `mini-web`, no key, no Store, no socket path but the helper's. It serves the
//! page shell and the assets, keeps cookies, bridges terminals, and asks the member's body (through
//! `mini-web-spawn`) for everything about kernel state.
//!
//!   mini-web --listen 127.0.0.1:8797 --helper /run/mini-web-spawn.sock --origin https://demo.dregg.online
//!            [--shutdown "11 November 2026"] [--frame-src https://*.demo.dregg.online] [--registry PATH]
//!
//! A dev gateway (`--origin http://127.0.0.1:PORT`) carries the cookie without `Secure`.

// print!/println!/eprint!/eprintln!: a closed standard output ends the command with 141, never a
// panic (`mini_streams`).
#[macro_use]
extern crate mini_streams;
mod http;
mod limits;
mod page;
mod proxy;
mod session;
mod term;
mod ws;

use std::io::Write;
use std::net::{Ipv4Addr, SocketAddr, TcpListener, TcpStream};
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;

use mini_web_spawn::{is_token, Client, Error as HelperError, Request as Helper};

use http::{read_request, Request, Response};
use page::{page, refusal};
use proxy::Target;
use session::{Sessions, Who};
use term::Terminals;

const MAX_CONNECTIONS: usize = 64;
const INGRESS: Duration = Duration::from_secs(10);
const COOKIE_MAX_AGE: u64 = 7 * 24 * 3600;

struct Gateway {
    sessions: Sessions,
    /// Each member's body requests in flight (at most `limits::PER_MEMBER`).
    inflight: limits::InFlight,
    terminals: Terminals,
    shutdown: String,
    frame_src: String,
    registry: Option<PathBuf>,
    defaults: Option<PathBuf>,
}

fn run_main() {
    if let Err(error) = run() {
        eprintln!("mini-web: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    let (mut listen, mut helper, mut origin, mut shutdown, mut frame_src, mut registry, mut defaults) = (None, None, None, String::new(), String::new(), None, None);
    while let Some(flag) = args.next() {
        let value = args.next().ok_or_else(|| format!("{flag} takes a value"))?;
        match flag.as_str() {
            "--listen" => listen = Some(value),
            "--helper" => helper = Some(PathBuf::from(value)),
            "--origin" => origin = Some(value),
            "--shutdown" => shutdown = value,
            "--frame-src" => frame_src = value,
            "--registry" => registry = Some(PathBuf::from(value)),
            "--defaults" => defaults = Some(PathBuf::from(value)),
            other => return Err(format!("unknown option {other}")),
        }
    }
    let listen = listen.ok_or("--listen 127.0.0.1:PORT is required")?;
    let address: SocketAddr = listen.parse().map_err(|_| format!("--listen {listen} is not ADDRESS:PORT"))?;
    if !matches!(address, SocketAddr::V4(v4) if *v4.ip() == Ipv4Addr::LOCALHOST) {
        return Err(format!("refused --listen {listen}: the gateway binds 127.0.0.1 only; Caddy is the public face"));
    }
    let origin = origin.ok_or("--origin https://HOST is required (the one origin browsers address)")?;
    let secure = origin.starts_with("https://");
    if !secure && !origin.starts_with("http://127.0.0.1") && !origin.starts_with("http://localhost") {
        return Err("--origin is https://HOST, or http://127.0.0.1:PORT for a dev gateway".into());
    }
    let helper = helper.ok_or("--helper PATH (mini-web-spawn's socket) is required")?;
    let listener = TcpListener::bind(address).map_err(|e| format!("bind {address}: {e}"))?;
    let bound = listener.local_addr().map_err(|e| e.to_string())?;
    println!("mini-web: {origin} on {bound} (helper {})", helper.display());
    let _ = std::io::stdout().flush();
    let gateway = Arc::new(Gateway {
        inflight: limits::InFlight::default(),
        sessions: Sessions { client: Client::new(&helper), origin, secure },
        terminals: Terminals::default(),
        shutdown,
        frame_src,
        registry,
        defaults,
    });
    let sweeper = gateway.clone();
    std::thread::Builder::new().name("mini-web-sweep".into()).spawn(move || loop {
        std::thread::sleep(Duration::from_secs(5));
        sweeper.terminals.sweep();
    }).map_err(|e| e.to_string())?;
    let live = Arc::new(AtomicUsize::new(0));
    for stream in listener.incoming() {
        let mut stream = match stream {
            Ok(s) => s,
            Err(e) => {
                eprintln!("mini-web: accept: {e}");
                continue;
            }
        };
        if live.fetch_update(Ordering::AcqRel, Ordering::Acquire, |n| (n < MAX_CONNECTIONS).then_some(n + 1)).is_err() {
            let _ = stream.set_write_timeout(Some(Duration::from_secs(1)));
            let _ = Response::text(503, "busy").with("Retry-After", "1").write(&mut stream, false);
            continue;
        }
        let gateway = gateway.clone();
        let live = live.clone();
        let _ = std::thread::Builder::new().name("mini-web-client".into()).spawn(move || {
            struct Permit(Arc<AtomicUsize>);
            impl Drop for Permit {
                fn drop(&mut self) {
                    self.0.fetch_sub(1, Ordering::AcqRel);
                }
            }
            let _permit = Permit(live);
            gateway.serve(stream);
        });
    }
    Ok(())
}

/// What the router decides for one request.
enum Reply {
    /// A whole page or a fragment around `html`, with `status` and `title`.
    Stage { status: u16, title: String, html: String, who: Option<Who>, path: String, set_cookie: Option<String> },
    Raw(Response),
    /// A file the body hands the member (their export), streamed from the body as it arrives.
    Download(proxy::Download, Option<limits::Slot>),
    /// The connection now belongs to a terminal.
    Upgraded,
}

impl Gateway {
    fn serve(&self, mut stream: TcpStream) {
        let _ = stream.set_read_timeout(Some(INGRESS));
        let _ = stream.set_write_timeout(Some(Duration::from_secs(30)));
        let request = match read_request(&mut stream) {
            Ok(r) => r,
            Err((status, why)) => {
                let _ = self.finish(Response::text(status, &why)).write(&mut stream, false);
                return;
            }
        };
        let fragment = request.fragment();
        let head_only = request.method == "HEAD";
        let reply = self.route(&request, &mut stream);
        let response = match reply {
            Reply::Upgraded => return,
            Reply::Download(download, _slot) => {
                if let Err(e) = self.stream_download(download, &mut stream, head_only) {
                    eprintln!("mini-web: download: {e}");
                }
                return;
            }
            Reply::Raw(response) => self.finish(response),
            Reply::Stage { status, title, html, who, path, set_cookie } => {
                // Every POST form on the page (the shell's and the stage's) gets this session's
                // token; the body's forms are plain and the token never reaches the body.
                let document = if fragment { html } else { page(&title, status, who.as_ref(), &path, &html, &self.shutdown) };
                let document = match &who {
                    Some(who) => page::inject_csrf(&document, &who.csrf),
                    None => document,
                };
                let mut response = Response::html(status, document);
                if fragment {
                    response = response.with("X-Mini-Title", &title.replace(['\r', '\n'], " "));
                }
                if let Some(cookie) = set_cookie {
                    response = response.with("Set-Cookie", &cookie);
                }
                self.finish(response)
            }
        };
        if let Err(e) = response.write(&mut stream, head_only) {
            eprintln!("mini-web: write: {e}");
        }
    }

    /// The security headers every answer carries. Scripts come only from this origin (the
    /// vendored xterm.js and app.js); the one inline head script is allowed by its hash; styles may be inline because xterm.js lays its terminal out
    /// with inline styles (`mini web`'s own CSP made the same allowance).
    fn finish(&self, response: Response) -> Response {
        let frame = if self.frame_src.is_empty() { "'none'".to_owned() } else { self.frame_src.clone() };
        // A grain's one-time bootstrap is a form posted to the grain's own origin: the origins the
        // pane may frame are the only other targets a form may name.
        let forms = if self.frame_src.is_empty() { "'self'".to_owned() } else { format!("'self' {}", self.frame_src) };
        let cache = response.header("Cache-Control").is_some();
        let early = page::EARLY_JS_HASH;
        let response = response
            .with("Content-Security-Policy", &format!("default-src 'none'; script-src 'self' '{early}'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; connect-src 'self'; frame-src {frame}; form-action {forms}; frame-ancestors 'none'; base-uri 'none'"))
            .with("X-Content-Type-Options", "nosniff")
            .with("X-Frame-Options", "DENY")
            .with("Referrer-Policy", "same-origin");
        if cache { response } else { response.with("Cache-Control", "no-store") }
    }

    fn stage(&self, status: u16, title: &str, html: String, who: Option<Who>, request: &Request) -> Reply {
        Reply::Stage { status, title: title.to_owned(), html, who, path: request.path.clone(), set_cookie: None }
    }

    fn route(&self, request: &Request, stream: &mut TcpStream) -> Reply {
        let Some(segments) = request.segments() else {
            return self.stage(404, "Not found", refusal("Not found", "no such page"), None, request);
        };
        if !matches!(request.method.as_str(), "GET" | "HEAD" | "POST") {
            return Reply::Raw(Response::text(405, "GET, HEAD and POST only"));
        }
        // GET and POST may not come from another origin at all.
        if let Err(why) = self.sessions.same_origin(request) {
            return self.stage(403, "Refused", refusal("Cross-origin request refused", &why), None, request);
        }
        match (request.method.as_str(), segments.as_slice()) {
            (_, ["assets", rest @ ..]) => Reply::Raw(self.asset(&rest.join("/"), &request.query)),
            (_, ["healthz"]) => Reply::Raw(Response::text(200, "ok")),
            ("GET" | "HEAD", ["login", code]) => {
                if !is_token(code) {
                    return self.stage(404, "Not a login link", refusal("Not a login link", "the code is malformed"), None, request);
                }
                self.stage(200, "Open your session", page::login_confirm(code), None, request)
            }
            ("POST", ["login"]) => self.login(request),
            ("POST", ["logout"]) => self.with_session(request, |who| {
                let _ = self.sessions.client.call(&Helper::Logout { sid: who.sid.clone() });
                self.terminals.end(&who.prefix());
                Reply::Raw(Response::redirect("/").with("Set-Cookie", &self.sessions.clear_cookie()))
            }),
            (_, ["sessions"]) => self.with_session(request, |who| self.sessions_page(request, &who)),
            ("POST", ["sessions", "revoke"]) => self.with_session(request, |who| {
                let prefix = request.form_value("prefix").unwrap_or_default();
                match self.sessions.client.call(&Helper::Revoke { sid: who.sid.clone(), prefix: prefix.clone() }) {
                    Ok(_) => {
                        self.terminals.end(&prefix);
                        Reply::Raw(Response::redirect("/sessions"))
                    }
                    Err(e) => self.stage(403, "Refused", refusal("Revoke refused", &e.to_string()), Some(who), request),
                }
            }),
            (_, ["term"]) => self.with_session(request, |who| self.term(request, &who)),
            ("GET" | "HEAD", ["term", id]) => self.with_session(request, |who| match self.terminals.get(id, &who.prefix()) {
                Some(_) => self.stage(200, "Terminal", page::term_page(id), Some(who), request),
                None => self.stage(404, "No such terminal", refusal("No such terminal", "it ended, or it is another session's"), Some(who), request),
            }),
            ("POST", ["term", id, "close"]) => self.with_session(request, |who| {
                self.terminals.close(id, &who.prefix());
                Reply::Raw(Response::redirect("/term"))
            }),
            ("GET", ["ws", "term", id]) => match self.sessions.who(request) {
                Some(who) => self.websocket(request, stream, id, &who),
                None => Reply::Raw(Response::text(401, "no session")),
            },
            ("GET" | "HEAD", ["registry"]) => {
                let who = self.sessions.who(request);
                let html = format!("{}{}", page::registry(self.registry.as_deref()), page::default_laws(self.defaults.as_deref()));
                self.stage(200, "Registry", html, who, request)
            }
            (_, ["join", ..]) => Reply::Raw(Response::redirect("/join")),
            _ => self.body(request),
        }
    }

    fn with_session(&self, request: &Request, then: impl FnOnce(Who) -> Reply) -> Reply {
        let Some(who) = self.sessions.who(request) else {
            return self.stage(401, "Open a session", page::public_only("This page"), None, request);
        };
        if request.method == "POST" && !Sessions::csrf_ok(request, &who) {
            return self.stage(403, "Refused", refusal("Form refused", "the form's token does not match this session; reload the page and try again"), Some(who), request);
        }
        then(who)
    }

    fn login(&self, request: &Request) -> Reply {
        let code = request.form_value("code").unwrap_or_default();
        if !is_token(&code) {
            return self.stage(400, "Not a login link", refusal("Not a login link", "the code is malformed"), None, request);
        }
        match self.sessions.client.call(&Helper::Login { code }) {
            Ok(answer) if answer.words.len() == 4 => {
                let sid = answer.words[0].clone();
                Reply::Raw(Response::redirect("/").with("Set-Cookie", &self.sessions.set_cookie(&sid, COOKIE_MAX_AGE)))
            }
            Ok(_) => self.stage(502, "Helper", refusal("The helper answered strangely", ""), None, request),
            Err(HelperError::Refused(why)) => self.stage(403, "Login refused", refusal("This link does not open a session", &format!("{why}. A login link works once and expires; the door's status page shows yours.")), None, request),
            Err(HelperError::Failed(why)) | Err(HelperError::Transport(why)) => self.stage(502, "Helper", refusal("The helper is not answering", &why), None, request),
        }
    }

    fn sessions_page(&self, request: &Request, who: &Who) -> Reply {
        match self.sessions.client.call(&Helper::Sessions { sid: who.sid.clone() }) {
            Ok(answer) => {
                let rows: Vec<(String, u64, u64, bool)> = answer
                    .lines
                    .iter()
                    .filter_map(|line| {
                        let w: Vec<&str> = line.split(' ').collect();
                        Some((w.first()?.to_string(), w.get(1)?.parse().ok()?, w.get(2)?.parse().ok()?, w.get(3) == Some(&"1")))
                    })
                    .collect();
                self.stage(200, "Sessions", page::sessions_page(&rows), Some(who.clone()), request)
            }
            Err(e) => self.stage(502, "Sessions", refusal("Cannot list sessions", &e.to_string()), Some(who.clone()), request),
        }
    }

    fn term(&self, request: &Request, who: &Who) -> Reply {
        if request.method == "POST" {
            let cols = request.form_value("cols").and_then(|c| c.parse().ok()).filter(|c| (20..=500).contains(c)).unwrap_or(100u16);
            let rows = request.form_value("rows").and_then(|r| r.parse().ok()).filter(|r| (5..=500).contains(r)).unwrap_or(30u16);
            return match self.sessions.client.call(&Helper::Shell { sid: who.sid.clone(), cols, rows }) {
                Ok(answer) => {
                    let pid: u32 = answer.words.first().and_then(|p| p.parse().ok()).unwrap_or(0);
                    let Some(master) = answer.fd else {
                        return self.stage(502, "Terminal", refusal("The helper passed no pty", ""), Some(who.clone()), request);
                    };
                    let terminal = self.terminals.create(&who.prefix(), pid, master);
                    Reply::Raw(Response::redirect(&format!("/term/{}", terminal.id)))
                }
                Err(e) => self.stage(403, "Terminal", refusal("No terminal", &e.to_string()), Some(who.clone()), request),
            };
        }
        let list: Vec<(String, bool, bool)> = self.terminals.of(&who.prefix()).iter().map(|t| (t.id.clone(), t.attached(), t.exited())).collect();
        self.stage(200, "Terminal", page::term_index(&list), Some(who.clone()), request)
    }

    fn websocket(&self, request: &Request, stream: &mut TcpStream, id: &str, who: &Who) -> Reply {
        let Some(terminal) = self.terminals.get(id, &who.prefix()) else {
            return Reply::Raw(Response::text(404, "no such terminal"));
        };
        let upgrade = request.header("upgrade").is_some_and(|u| u.eq_ignore_ascii_case("websocket"));
        let Some(key) = request.header("sec-websocket-key").filter(|_| upgrade) else {
            return Reply::Raw(Response::text(426, "this address speaks WebSocket"));
        };
        if request.header("sec-websocket-version") != Some("13") {
            return Reply::Raw(Response::text(426, "WebSocket version 13").with("Sec-WebSocket-Version", "13"));
        }
        // A WebSocket upgrade has no Sec-Fetch-Site in some browsers; Origin is mandatory here.
        if request.header("origin") != Some(self.sessions.origin.as_str()) {
            return Reply::Raw(Response::text(403, "Origin refused"));
        }
        let head = format!(
            "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: {}\r\n\r\n",
            ws::accept_key(key)
        );
        if stream.write_all(head.as_bytes()).is_err() {
            return Reply::Upgraded;
        }
        let _ = stream.set_read_timeout(None);
        let Ok(sink) = stream.try_clone() else { return Reply::Upgraded };
        if terminal.attach(sink).is_err() {
            return Reply::Upgraded;
        }
        loop {
            match ws::read_frame(stream) {
                Ok(ws::Frame::Binary(bytes)) => {
                    if terminal.input(&bytes).is_err() {
                        break;
                    }
                }
                Ok(ws::Frame::Text(text)) => {
                    if let Ok(v) = serde_json::from_str::<serde_json::Value>(&text) {
                        if let (Some(cols), Some(rows)) = (v["resize"][0].as_u64(), v["resize"][1].as_u64()) {
                            if (1..=500).contains(&cols) && (1..=500).contains(&rows) {
                                terminal.resize(cols as u16, rows as u16);
                            }
                        }
                    }
                }
                Ok(ws::Frame::Ping(payload)) => {
                    if ws::write_frame(stream, &ws::Frame::Pong(payload)).is_err() {
                        break;
                    }
                }
                Ok(ws::Frame::Pong(_)) => {}
                Ok(ws::Frame::Close(..)) | Err(_) => break,
            }
        }
        terminal.detach();
        let _ = ws::write_frame(stream, &ws::Frame::Close(1000, String::new()));
        Reply::Upgraded
    }

    /// Everything about kernel state: the member's body, or the public reader's.
    fn body(&self, request: &Request) -> Reply {
        let who = self.sessions.who(request);
        let target = match &who {
            Some(who) => {
                if request.method == "POST" && !Sessions::csrf_ok(request, who) {
                    return self.stage(403, "Refused", refusal("Form refused", "the form's token does not match this session; reload the page and try again"), Some(who.clone()), request);
                }
                Target::Session(&who.sid)
            }
            None if request.method == "POST" => {
                return self.stage(401, "Open a session", page::public_only("Writing"), None, request);
            }
            None => Target::Public,
        };
        // One member holds at most PER_MEMBER body requests at once; the slot is held until the
        // body's answer (or the download it streams) is done.
        let slot = match &who {
            Some(w) => match self.inflight.acquire(&w.name) {
                Some(slot) => Some(slot),
                None => {
                    return self.stage(429, "Too many requests", refusal("Too many requests at once",
                        &format!("you already have {} requests waiting on your workspace; this one was refused, not queued. Let one finish, then try again.", limits::PER_MEMBER)), who.clone(), request);
                }
            },
            None => None,
        };
        match proxy::fetch(&self.sessions.client, target, request) {
            Ok(proxy::Answer::Download(download)) => Reply::Download(download, slot),
            Ok(proxy::Answer::Page(fragment)) => {
                if let Some(location) = fragment.location.filter(|_| (300..400).contains(&fragment.status)) {
                    if !http::same_origin_path(&location) {
                        return self.stage(502, "Unavailable", refusal("The body asked for a redirect elsewhere", "a body redirects only within this origin"), who, request);
                    }
                    return Reply::Raw(Response::redirect(&location));
                }
                self.stage(fragment.status, &fragment.title, fragment.html, who, request)
            }
            Err((status, why)) => {
                // The visitor's page is unchanged; the gateway's journal keeps why the body could not answer.
                let whose = who.as_ref().map_or("the public reader", |w| w.name.as_str());
                eprintln!("mini-web: body for {whose}: {} {}: {status}: {why}", request.method, request.path);
                let headline = match status {
                    403 => "This body refused",
                    504 => "The body did not answer in time",
                    _ => "The body is not answering",
                };
                self.stage(status, "Unavailable", refusal(headline, &why), who, request)
            }
        }
    }

    /// The head the gateway's own answers carry (`finish`), then the body's bytes as they come.
    fn stream_download(&self, mut download: proxy::Download, stream: &mut TcpStream, head_only: bool) -> std::io::Result<()> {
        use std::io::{Read, Write};
        let head = self.finish(Response::new(200).with("Content-Type", &download.content_type).with("Content-Disposition", &download.disposition));
        let mut out = String::from("HTTP/1.1 200 OK\r\n");
        for (k, v) in &head.headers {
            out.push_str(&format!("{k}: {v}\r\n"));
        }
        if let Some(n) = download.length {
            out.push_str(&format!("Content-Length: {n}\r\n"));
        }
        out.push_str("Connection: close\r\n\r\n");
        let _ = stream.set_write_timeout(Some(std::time::Duration::from_secs(60)));
        stream.write_all(out.as_bytes())?;
        if head_only {
            return stream.flush();
        }
        stream.write_all(&download.first)?;
        let mut buffer = [0u8; 65536];
        loop {
            let n = download.stream.read(&mut buffer)?;
            if n == 0 {
                break;
            }
            stream.write_all(&buffer[..n])?;
        }
        stream.flush()
    }

    /// A request for `?v=TAG` naming the asset's current tag is cached for a year, `immutable`;
    /// any other asks the short cache, so an old link still resolves and a stale one cannot stick.
    fn asset(&self, name: &str, query: &str) -> Response {
        let Some((_, kind, bytes)) = page::ASSETS.iter().find(|(n, _, _)| *n == name) else { return Response::text(404, "no such asset") };
        let tagged = page::asset_tag(name).is_some_and(|tag| query.strip_prefix("v=") == Some(tag));
        let cache = if tagged { "public, max-age=31536000, immutable" } else { "public, max-age=3600" };
        Response::new(200).with("Content-Type", kind).with("Cache-Control", cache).body(bytes.to_vec())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn vendored_assets_match_their_pinned_sha256() {
        use sha2::Digest;
        for (file, bytes, want) in [
            ("xterm.js", &include_bytes!("../assets/vendor/xterm.js")[..], "1f991ac3b4b283ebf96e60ae23a00a52765dd3a2e46fa6fdda9f1aab032f7495"),
            ("xterm.css", &include_bytes!("../assets/vendor/xterm.css")[..], "ba8e6985669488981ccf40c0cefe3aba80722cb6c92de7ad628b0bd717faf2b6"),
            ("addon-fit.js", &include_bytes!("../assets/vendor/addon-fit.js")[..], "bdaefa370b1bfc42ee88d46fe6072400902a4d4b2d45cd93438dda9b23c97089"),
        ] {
            let got = sha2::Sha256::digest(bytes).iter().map(|b| format!("{b:02x}")).collect::<String>();
            assert_eq!(got, want, "{file}");
            let table = include_str!("../assets/vendor/VENDOR.md");
            assert!(table.contains(want), "VENDOR.md lists {file}");
        }
    }
}

fn main() -> std::process::ExitCode {
    mini_streams::guard(|| {
        run_main();
        std::process::ExitCode::SUCCESS
    })
}
