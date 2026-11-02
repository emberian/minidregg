//! The one page shell and the gateway's own partials. Everything about kernel state is rendered
//! by the body and arrives as a stage fragment; this file is the chrome around it: the top bar,
//! the rail of places, the footer with the world-readable sentence, and the few pages that are the
//! gateway's own (login, terminals, sessions, refusals).

use crate::http::html_escape as h;
use crate::session::Who;

pub const PLACES: &[(&str, &str, &str)] = &[
    ("Documents", "/doc", "Documents you hold: pages, history, diffs, append and edit."),
    ("Boards", "/board", "Tasks on columns: add, move, take."),
    ("Rooms", "/room", "Members, streams as chat, residents."),
    ("Apps", "/apps", "App market: claims beside verdicts; install; grains opened on their own origins."),
    ("Receipts", "/receipts", "Attempts and decoded outcomes."),
    ("Stories", "/story", "Interactive stories: invitations, join, invite, enter."),
    ("Programs", "/bend", "Bend programs: active awaits and reply forms."),
    ("Purse", "/purse", "Account meter, payments, top-ups, tariffs."),
    ("Grants & laws", "/grants", "Held grants; delegate, revoke, install a law."),
    ("Subscribe", "/subscribe", "Subscriber tier: house Hermes in the subscribers room."),
    ("Export", "/export", "Download your workspace archive."),
    ("Keys & sessions", "/keys", "Hosted key status and browser sessions."),
    ("Registry", "/registry", "Host operations, receivers, response markers, consent plans, default laws."),
    ("Tour", "/tour", "Twelve guided steps with live forms."),
    ("Commands", "/verb", "Shell verbs rendered as forms."),
    ("Terminal", "/term", "mini shell in the browser."),
];

pub const WORLD_READABLE: &str = "Everything on this box is world-readable: every member can read the whole demo Store, and a hosted account's signing key lives on the box. Keep nothing private or precious here.";

/// The static assets: name, content type, bytes. One table, so the served bytes, the cache tag in
/// the page's links and the hash tests all read the same thing.
pub const ASSETS: &[(&str, &str, &[u8])] = &[
    ("app.css", "text/css; charset=utf-8", include_bytes!("../assets/app.css")),
    ("app.js", "text/javascript; charset=utf-8", include_bytes!("../assets/app.js")),
    ("vendor/xterm.js", "text/javascript; charset=utf-8", include_bytes!("../assets/vendor/xterm.js")),
    ("vendor/addon-fit.js", "text/javascript; charset=utf-8", include_bytes!("../assets/vendor/addon-fit.js")),
    ("vendor/xterm.css", "text/css; charset=utf-8", include_bytes!("../assets/vendor/xterm.css")),
];

/// The first twelve hex digits of an asset's SHA-256: its cache tag. A link carrying `?v=TAG` is
/// served `immutable` for a year (the bytes behind a tag never change); the bare URL keeps the
/// short cache. A changed asset changes its tag, so no page ever pairs new markup with old CSS.
pub fn asset_tag(name: &str) -> Option<&'static str> {
    use sha2::Digest;
    // The assets are `include_bytes!`, so a tag is constant for the process: hash each once.
    static TAGS: std::sync::LazyLock<Vec<String>> = std::sync::LazyLock::new(|| {
        ASSETS
            .iter()
            .map(|(_, _, bytes)| sha2::Sha256::digest(bytes).iter().take(6).map(|b| format!("{b:02x}")).collect())
            .collect()
    });
    let index = ASSETS.iter().position(|(n, _, _)| *n == name)?;
    Some(TAGS[index].as_str())
}

fn asset_href(name: &str) -> String {
    format!("/assets/{name}?v={}", asset_tag(name).unwrap_or(""))
}

/// The one inline script in the document head. It runs before the body is parsed and marks the
/// root `js`, so the workspace layout (tiled panes) is the first frame for a browser that will run
/// app.js, and the plain one-pane layout stays the first frame for one that will not. Allowed by
/// the CSP through its hash (`EARLY_JS_HASH`), never `unsafe-inline`; a test pins the pair.
pub const EARLY_JS: &str = "document.documentElement.classList.add('js')";
pub const EARLY_JS_HASH: &str = "sha256-Du+OJKJSbdUgz5nrHeWWINvez6XKDDU/tyj/5c2uvwo=";

/// The whole document around a stage fragment.
pub fn page(title: &str, status: u16, who: Option<&Who>, path: &str, stage: &str, shutdown: &str) -> String {
    let xterm = if stage.contains("data-ws=") {
        format!(
            "<link rel=\"stylesheet\" href=\"{}\">\n<script defer src=\"{}\"></script>\n<script defer src=\"{}\"></script>\n",
            asset_href("vendor/xterm.css"),
            asset_href("vendor/xterm.js"),
            asset_href("vendor/addon-fit.js")
        )
    } else {
        String::new()
    };
    let mut rail = String::new();
    for (label, href, hint) in PLACES {
        let group = match *href { "/doc" => Some("Explore"), "/purse" => Some("Your workspace"), "/registry" => Some("Understand & build"), _ => None };
        if let Some(group) = group { rail.push_str(&format!("<li class=\"nav-group\">{group}</li>")); }
        let current = if path == *href || path.starts_with(&format!("{href}/")) { " aria-current=\"page\"" } else { "" };
        rail.push_str(&format!("<li><a href=\"{href}\" title=\"{}\" data-pane{current}>{label}</a></li>", h(hint)));
    }
    let identity = match who {
        Some(who) => format!(
            "<span class=\"me\" title=\"session {}\">{}</span>\
             <form method=\"post\" action=\"/logout\" class=\"inline\" data-full><button class=\"quiet\">Log out</button></form>",
            h(&who.prefix()),
            h(&who.name)
        ),
        None => "<span class=\"me public\">public reader</span><a class=\"button\" href=\"/join\" data-full>Join</a>".to_owned(),
    };
    let shutdown_line = if shutdown.is_empty() { String::new() } else { format!(" This demo is torn down on {}; nothing you make here persists beyond it.", h(shutdown)) };
    let report = report_href(path, status, title);
    format!(
        "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n<meta name=\"color-scheme\" content=\"light dark\">\n\
         <script>{EARLY_JS}</script>\n<title>{title} · Mini</title>\n<link rel=\"stylesheet\" href=\"{css}\">\n{xterm}<script defer src=\"{js}\"></script>\n</head>\n\
         <body data-path=\"{path}\">\n\
         <a class=\"skip\" href=\"#stage\">Skip to content</a>\n\
         <header class=\"top\"><a class=\"brand\" href=\"/\" data-full>Mini</a>\
         <form method=\"get\" action=\"/search\" class=\"search\" role=\"search\"><input type=\"search\" name=\"query\" placeholder=\"Search documents\" aria-label=\"Search documents\"></form>\
         <div class=\"identity\">{identity}</div></header>\n\
         <nav class=\"rail\" aria-label=\"Places\"><ul>{rail}</ul></nav>\n\
         <main class=\"stage\" id=\"stage\" tabindex=\"-1\"><section class=\"pane\" data-path=\"{path}\" data-title=\"{title}\"><div class=\"pane-head\"><h1 class=\"pane-title\">{title}</h1></div><div class=\"pane-body\">\n{stage}\n</div></section></main>\n\
         <footer class=\"foot\"><p>{world}{shutdown_line}</p><p><a class=\"report\" href=\"{report}\" data-pane>Report a problem</a></p></footer>\n</body>\n</html>\n",
        title = h(title),
        path = h(path),
        css = asset_href("app.css"),
        js = asset_href("app.js"),
        world = h(WORLD_READABLE),
        report = h(&report),
    )
}

/// The "Report a problem" link every page's footer carries: the member shell's own `feedback`
/// form (derived from its grammar, `/verb/feedback`), prefilled with the page the person is on,
/// and with the status and title when the page itself is an error or a refusal. The form needs
/// no script; `app.js` only keeps this link current when a pane swaps.
pub fn report_href(path: &str, status: u16, title: &str) -> String {
    let mut query = format!("page={}", encode(path));
    if status >= 400 {
        query.push_str(&format!("&clause={}", encode(&format!("HTTP {status}: {title}"))));
    }
    format!("/verb/feedback?{query}")
}

/// Percent-encode a query value: only the unreserved characters pass.
fn encode(text: &str) -> String {
    text.bytes().map(|b| if b.is_ascii_alphanumeric() || b"-._~".contains(&b) { (b as char).to_string() } else { format!("%{b:02X}") }).collect()
}

/// Every POST form on the stage carries the session's CSRF token: the body renders plain forms
/// and never learns the token; the gateway adds one hidden field after each `<form … method=post>`
/// opening tag (case-insensitive, quoted or bare). GET forms (search, lookups) are left alone.
pub fn inject_csrf(html: &str, csrf: &str) -> String {
    let field = format!("<input type=\"hidden\" name=\"csrf\" value=\"{}\">", h(csrf));
    let lower = html.to_ascii_lowercase();
    let mut out = String::with_capacity(html.len() + 256);
    let mut at = 0;
    while let Some(start) = lower[at..].find("<form") {
        let start = at + start;
        let Some(end) = lower[start..].find('>') else { break };
        let end = start + end + 1;
        let tag = &lower[start..end];
        out.push_str(&html[at..end]);
        let post = tag.contains("method=\"post\"") || tag.contains("method='post'") || tag.contains("method=post");
        if post && form_stays_here(&html[start..end]) {
            out.push_str(&field);
        }
        at = end;
    }
    out.push_str(&html[at..]);
    out
}

/// A form whose `action` is this origin (absent, or a same-origin path): only those carry the
/// session's token. A form posting elsewhere (a grain's one-time bootstrap to its own origin) is
/// left as the body drew it, so the token never reaches another origin.
fn form_stays_here(tag: &str) -> bool {
    let lower = tag.to_ascii_lowercase();
    let Some(at) = lower.find(" action=") else { return true };
    let rest = &tag[at + " action=".len()..];
    let value = match rest.chars().next() {
        Some(q @ ('"' | '\'')) => rest[1..].split(q).next().unwrap_or(""),
        _ => rest.split(|c: char| c.is_whitespace() || c == '>').next().unwrap_or(""),
    };
    value.is_empty() || crate::http::same_origin_path(value)
}

/// The outcome partial the gateway uses for its own actions; the body renders the same shape for
/// verbs (`admitted`, `refused`, `undecided`).
pub fn outcome(class: &str, headline: &str, detail: &str, next: &[(&str, &str)]) -> String {
    let mut links = String::new();
    for (label, href) in next {
        links.push_str(&format!("<a href=\"{}\" data-pane>{}</a> ", h(href), h(label)));
    }
    if matches!(class, "refused" | "error" | "undecided") {
        let clause: String = headline.chars().take(400).collect();
        links.push_str(&format!("<a class=\"report\" href=\"/verb/feedback?clause={}\" data-pane>Report a problem</a> ", encode(&clause)));
    }
    format!(
        "<div class=\"outcome {class}\" role=\"status\" aria-live=\"polite\" aria-atomic=\"true\"><p class=\"headline\">{}</p>{}{}</div>",
        h(headline),
        if detail.is_empty() { String::new() } else { format!("<pre>{}</pre>", h(detail)) },
        if links.is_empty() { String::new() } else { format!("<p class=\"next\">{links}</p>") }
    )
}

pub fn refusal(headline: &str, detail: &str) -> String {
    outcome("refused", headline, detail, &[])
}

pub fn login_confirm(code: &str) -> String {
    format!(
        "<p>This link opens a browser session for the account the door made for you. It works once.</p>\
         <form method=\"post\" action=\"/login\" data-full><input type=\"hidden\" name=\"code\" value=\"{}\"><button>Open my session</button></form>\
         <p class=\"note\">Your session is a cookie that names your hosted account; it is never a key. Your signing key stays on the box, in your account's home. Log out from any page; see every session under Keys &amp; sessions.</p>",
        h(code)
    )
}

pub fn public_only(what: &str) -> String {
    format!(
        "<p>{} needs a session. The door at <a href=\"/join\" data-full>/join</a> makes you an account and gives you a one-time link that opens one here.</p>",
        h(what)
    )
}

pub fn term_index(terminals: &[(String, bool, bool)]) -> String {
    let mut rows = String::new();
    for (id, attached, exited) in terminals {
        let state = match (attached, exited) { (_, true) => "ended", (true, _) => "attached", (false, _) => "waiting" };
        rows.push_str(&format!(
            "<tr><td><a href=\"/term/{id}\" data-pane>shell {}</a></td><td>{state}</td>\
             <td><form method=\"post\" action=\"/term/{id}/close\" class=\"inline\"><button class=\"quiet\">Close</button></form></td></tr>",
            h(&id[..6])
        ));
    }
    format!(
        "<p><code>mini shell</code> as your account, in the page: the same shell <code>ssh -t</code> opens, with the same verbs, Tab completion and history.</p>\
         <form method=\"post\" action=\"/term\"><button>Open a terminal</button></form>\
         {}",
        if rows.is_empty() { String::new() } else { format!("<table><thead><tr><th>terminal</th><th>state</th><th></th></tr></thead><tbody>{rows}</tbody></table>") }
    )
}

pub fn term_page(id: &str) -> String {
    format!(
        "<div class=\"term\" data-ws=\"/ws/term/{}\" role=\"region\" tabindex=\"0\" aria-label=\"Terminal: mini shell in the page (every verb is also a form under Commands)\">\
         <p class=\"vh\">This pane is a terminal: the same shell <code>ssh -t</code> opens. Every verb it understands is also a keyboard-friendly form: <a href=\"/verb\">every shell verb as a form</a>. Recent terminal output is mirrored in text at the end of this region.</p>\
         <noscript><p>The terminal needs JavaScript. Without it, the same shell is <code>ssh -t</code> to your account.</p></noscript></div>",
        h(id)
    )
}

pub fn sessions_page(sessions: &[(String, u64, u64, bool)]) -> String {
    let mut rows = String::new();
    for (prefix, created, last, current) in sessions {
        rows.push_str(&format!(
            "<tr><td><code>{prefix}</code>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>",
            if *current { " <em>this one</em>" } else { "" },
            when(*created),
            when(*last),
            if *current {
                "<form method=\"post\" action=\"/logout\" class=\"inline\"><button class=\"quiet\">Log out</button></form>".to_owned()
            } else {
                format!("<form method=\"post\" action=\"/sessions/revoke\" class=\"inline\"><input type=\"hidden\" name=\"prefix\" value=\"{prefix}\"><button class=\"quiet\">Revoke</button></form>")
            }
        ));
    }
    format!(
        "<p>Every browser session of this account. A session ends after a day idle, a week at most, or when you revoke it; revoking ends its terminals and its rendering process.</p>\
         <table><thead><tr><th>session</th><th>opened</th><th>last seen</th><th></th></tr></thead><tbody>{rows}</tbody></table>"
    )
}

/// `/registry`: the operation registry the box runs (`protocol/host-operations.json`, the one
/// place L1, L2 and L8 meet), rendered as data: every operation byte, its symbol, status, routes,
/// owner, receiver and effect; the response markers; the consent plans. Public: it is the law of
/// the box, not a member's state.
/// A rendered page fragment kept until its source changes: `key` names the source files' identity
/// (path, length, mtime), so an edited registry or law file re-renders and an untouched one does not.
struct Rendered(std::sync::Mutex<Option<(String, String)>>);

impl Rendered {
    const fn new() -> Self {
        Self(std::sync::Mutex::new(None))
    }
    fn get(&self, key: String, render: impl FnOnce() -> String) -> String {
        let mut slot = self.0.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some((have, html)) = slot.as_ref() {
            if *have == key {
                return html.clone();
            }
        }
        let html = render();
        *slot = Some((key, html.clone()));
        html
    }
}

fn file_identity(path: &std::path::Path) -> String {
    use std::os::unix::fs::MetadataExt;
    match std::fs::metadata(path) {
        Ok(m) => format!("{}:{}:{}:{}:{}", path.display(), m.ino(), m.len(), m.mtime(), m.mtime_nsec()),
        Err(error) => format!("{}:{:?}", path.display(), error.kind()),
    }
}

pub fn registry(path: Option<&std::path::Path>) -> String {
    static RENDERED: Rendered = Rendered::new();
    match path {
        Some(path) => RENDERED.get(file_identity(path), || registry_uncached(Some(path))),
        None => registry_uncached(None),
    }
}

fn registry_uncached(path: Option<&std::path::Path>) -> String {
    let Some(path) = path else {
        return "<p>The operation registry is the law of this box: every Host operation byte, who receives it and what it may change. This gateway was started without <code>--registry PATH</code>, so it cannot show it here; the file is <code>protocol/host-operations.json</code> in the candidate.</p>".to_owned();
    };
    let value: serde_json::Value = match std::fs::read(path).ok().and_then(|b| serde_json::from_slice(&b).ok()) {
        Some(v) => v,
        None => return refusal("No registry", &format!("{} is missing or malformed", path.display())),
    };
    registry_html(&value)
}

pub fn registry_html(value: &serde_json::Value) -> String {
    let text = |v: &serde_json::Value| match v {
        serde_json::Value::String(s) => s.clone(),
        serde_json::Value::Array(a) => a.iter().map(|x| x.as_str().unwrap_or("").to_owned()).collect::<Vec<_>>().join(" "),
        serde_json::Value::Null => String::new(),
        other => other.to_string(),
    };
    let mut out = format!(
        "<p>Every Host operation this box answers, by byte: the receiver that decides it and the effect it may have. Format <code>{}</code>. An <em>active</em> row is live; a <em>reserved</em> one is a number held for a receiver not yet landed.</p>\n",
        h(&text(&value["format"]))
    );
    let mut rows = String::new();
    let mut active = 0;
    for op in value["operations"].as_array().into_iter().flatten() {
        let status = text(&op["status"]);
        if status == "active" {
            active += 1;
        }
        rows.push_str(&format!(
            "<tr class=\"{s}\"><td><code>{}</code></td><td><code>{}</code></td><td>{s}</td><td>{}</td><td>{}</td><td><code>{}</code></td><td>{}</td><td class=\"note\">{}</td></tr>\n",
            h(&text(&op["code"])),
            h(&text(&op["symbol"])),
            h(&text(&op["routes"])),
            h(&text(&op["owner"])),
            h(&text(&op["receiver"])),
            h(&text(&op["effect"])),
            h(&text(&op["purpose"])),
            s = h(&status)
        ));
    }
    out.push_str(&format!(
        "<section><h2>Operations ({active} active)</h2><table class=\"registry\"><thead><tr><th>byte</th><th>symbol</th><th>status</th><th>routes</th><th>owner</th><th>receiver</th><th>effect</th><th>purpose</th></tr></thead><tbody>{rows}</tbody></table></section>\n"
    ));
    if let Some(markers) = value["response_markers"].as_object() {
        let mut rows = String::new();
        for (k, v) in markers {
            rows.push_str(&format!("<tr><td><code>{}</code></td><td>{}</td></tr>", h(k), h(&text(v))));
        }
        out.push_str(&format!("<section><h2>Response markers</h2><p class=note>What a reply byte means before any frame is decoded: the classes a client turns into admitted, refused and undecided.</p><table><tbody>{rows}</tbody></table></section>\n"));
    } else if let Some(markers) = value["response_markers"].as_array() {
        let mut rows = String::new();
        for m in markers {
            rows.push_str(&format!("<tr><td><code>{}</code></td><td>{}</td><td class=note>{}</td></tr>", h(&text(&m["code"])), h(&text(&m["symbol"])), h(&text(&m["purpose"]))));
        }
        out.push_str(&format!("<section><h2>Response markers</h2><table><tbody>{rows}</tbody></table></section>\n"));
    }
    if !value["consent_plans"].is_null() {
        out.push_str(&format!("<section><h2>Consent plans</h2><p class=note>What a member's client is asked to consent to before it signs, by plan.</p><pre>{}</pre></section>\n", h(&serde_json::to_string_pretty(&value["consent_plans"]).unwrap_or_default())));
    }
    out
}

/// The default laws Lean emits (`deploy/shell/templates/defaults/law.*.json`, from
/// `Kernel/DefaultLaw.lean`: the owner-only account law, the founder-governed room law), as the
/// files say them: the predicate, with its `@OWNER`/`@FOUNDER` placeholder named. The clause text
/// as the Host prints it is `law show REF` on a reference that carries the law (`/verb/law`).
pub fn default_laws(dir: Option<&std::path::Path>) -> String {
    static RENDERED: Rendered = Rendered::new();
    let Some(dir) = dir else { return default_laws_uncached(None) };
    let mut names: Vec<_> = std::fs::read_dir(dir)
        .map(|d| d.flatten().map(|e| e.path()).filter(|p| p.file_name().and_then(|n| n.to_str()).is_some_and(|n| n.starts_with("law.") && n.ends_with(".json"))).collect())
        .unwrap_or_default();
    names.sort();
    let key = format!("{}|{}", file_identity(dir), names.iter().map(|p| file_identity(p)).collect::<Vec<_>>().join("|"));
    RENDERED.get(key, || default_laws_uncached(Some(dir)))
}

fn default_laws_uncached(dir: Option<&std::path::Path>) -> String {
    let Some(dir) = dir else {
        return "<section><h2>Default laws</h2><p class=note>The laws every member account and room is installed under are emitted from Lean (<code>Kernel/DefaultLaw.lean</code>); this gateway was started without <code>--defaults DIR</code>, so they are not shown here.</p></section>".to_owned();
    };
    let mut files: Vec<_> = std::fs::read_dir(dir).map(|d| d.flatten().filter_map(|e| e.file_name().into_string().ok()).filter(|n| n.starts_with("law.") && n.ends_with(".json")).collect()).unwrap_or_default();
    files.sort();
    if files.is_empty() {
        return format!("<section><h2>Default laws</h2><p class=note>No <code>law.*.json</code> under <code>{}</code>: this candidate carries no Lean-emitted default laws yet (L1's <code>scripts/gen-default-laws.sh</code> writes them).</p></section>", h(&dir.display().to_string()));
    }
    let mut out = String::from("<section><h2>Default laws</h2><p>Emitted from Lean (<code>Kernel/DefaultLaw.lean</code>) and installed on every member account and room; the placeholder is substituted by the client at install (<code>@OWNER</code> the account's owner, <code>@FOUNDER</code> the room's founder). <code>law show REF</code> prints the clause as the Host holds it on any reference.</p>");
    for name in files {
        let text = std::fs::read_to_string(dir.join(&name)).unwrap_or_default();
        let pretty = serde_json::from_str::<serde_json::Value>(&text).map(|v| serde_json::to_string_pretty(&v).unwrap_or(text.clone())).unwrap_or(text.clone());
        let placeholder = ["@OWNER", "@FOUNDER"].iter().find(|p| text.contains(*p)).copied().unwrap_or("");
        out.push_str(&format!("<h3><code>{}</code>{}</h3><pre>{}</pre>", h(&name), if placeholder.is_empty() { String::new() } else { format!(" <span class=note>placeholder {}</span>", h(placeholder)) }, h(&pretty)));
    }
    out + "</section>"
}

pub fn when(t: u64) -> String {
    // Unix seconds as an ISO-like UTC stamp, without a clock library.
    let days = t / 86400;
    let secs = t % 86400;
    let (y, m, d) = civil(days as i64);
    format!("{y:04}-{m:02}-{d:02} {:02}:{:02}Z", secs / 3600, (secs % 3600) / 60)
}

fn civil(z: i64) -> (i64, u32, u32) {
    let z = z + 719468;
    let era = z.div_euclid(146097);
    let doe = z.rem_euclid(146097);
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    (if m <= 2 { y + 1 } else { y }, m, d)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore = "wraps visual fixtures in the real page shell"]
    fn design_preview() {
        let dir = std::path::PathBuf::from(std::env::var("MINI_WEB_PREVIEW").expect("MINI_WEB_PREVIEW"));
        let pages: serde_json::Value = serde_json::from_slice(&std::fs::read(dir.join("pages.json")).unwrap()).unwrap();
        let who = Who { sid: "preview".into(), name: "alice".into(), csrf: "fixture".into() };
        for p in pages.as_array().unwrap() {
            if p["standalone"] == true { continue; }
            let s = |key: &str| p[key].as_str().unwrap();
            let html = page(s("title"), 200, (p["member"] == true).then_some(&who), s("path"), s("body"), "11 November 2026");
            std::fs::write(dir.join(format!("{}.html", s("name"))), html).unwrap();
        }
        for (name, _, bytes) in ASSETS {
            let file = dir.join("assets").join(name);
            std::fs::create_dir_all(file.parent().unwrap()).unwrap();
            std::fs::write(file, bytes).unwrap();
        }
    }

    /// The heading levels of a rendered page, in document order. `<h2` names a heading
    /// only as a whole tag (`<header` is not one), so the character after the level is
    /// checked; the scan collects (offset, level) pairs and sorts once.
    fn heading_levels(html: &str) -> Vec<u8> {
        let mut levels: Vec<(usize, u8)> = Vec::new();
        for n in 1..=6u8 {
            let marker = format!("<h{n}");
            let mut at = 0;
            while let Some(start) = html[at..].find(&marker) {
                let start = at + start;
                let after = html[start + 3..].chars().next();
                if after.is_none_or(|c| c == ' ' || c == '>' || c == '\n' || c == '\t') {
                    levels.push((start, n));
                }
                at = start + 3;
            }
        }
        levels.sort_unstable();
        levels.into_iter().map(|(_, n)| n).collect()
    }

    /// Headings nest: no level jumps more than one step down (h1 then h3 is the failure).
    fn headings_nest(html: &str) -> bool {
        let mut last = 0u8;
        for n in heading_levels(html) {
            if n > last + 1 {
                return false;
            }
            last = n;
        }
        true
    }

    /// The shell is one landmark set with a keyboard route past the chrome: one `main`, one
    /// `nav`, a skip link as the first thing focusable, headings that nest, the outcome
    /// partial as a live region, and a terminal pane that names itself and its alternative.
    #[test]
    fn a11y_page_shell_landmarks_skip_link_and_nested_headings() {
        let who = Who { sid: "s".into(), name: "al".into(), csrf: "c".into() };
        let stage = "<section><h2>A place</h2><p>body</p><h3>Under it</h3></section><div class=\"outcome admitted\" role=\"status\"><p class=\"headline\">Admitted</p></div>";
        let html = page("Documents", 200, Some(&who), "/doc", stage, "");
        assert_eq!(html.matches("<main").count(), 1, "exactly one main");
        assert_eq!(html.matches("<nav").count(), 1, "exactly one nav");
        assert!(html.contains("<nav class=\"rail\" aria-label=\"Places\""));
        assert!(html.contains("<main class=\"stage\" id=\"stage\" tabindex=\"-1\""));
        let skip = html.find("<a class=\"skip\" href=\"#stage\"").expect("a skip link to the stage");
        let first_other_link = html.find("<a ").filter(|at| *at != skip);
        assert!(skip < html.find("<nav").unwrap(), "the skip link comes before the rail");
        assert!(first_other_link.is_none_or(|at| skip < at), "the skip link is the page's first link");
        assert!(html.contains(">Skip to content</a>"));
        assert_eq!(heading_levels(&html).first(), Some(&1), "the page's first heading is the h1 title");
        assert!(headings_nest(&html), "headings nest under the h1: {:?}", heading_levels(&html));
        // Red-proof the walker: a stage that opens at h3 must be named.
        let bad = page("Bad", 200, Some(&who), "/doc", "<section><h3>Skipped a level</h3></section>", "");
        assert!(!headings_nest(&bad), "the nesting check must catch an h1 to h3 jump");
        // The gateway's own outcome partial and the terminal.
        let outcome_html = outcome("undecided", "Undecided", "the attempt is retained", &[("the receipt", "/receipts/w-1")]);
        assert!(outcome_html.contains("role=\"status\"") && outcome_html.contains("aria-live=\"polite\"") && outcome_html.contains("Undecided"));
        let term = term_page("abc123");
        assert!(term.contains("role=\"region\"") && term.contains("aria-label=\"Terminal"), "{term}");
        assert!(term.contains("href=\"/verb\""), "the terminal names the keyboard route to the same verbs");
    }

    #[test]
    fn the_first_frame_needs_no_script_to_be_final() {
        use sha2::Digest;
        // The CSP's hash is the hash of the one inline head script, byte for byte.
        let bytes = sha2::Sha256::digest(EARLY_JS.as_bytes());
        let b64 = {
            const T: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
            let mut out = String::new();
            for c in bytes.chunks(3) {
                let n = (c[0] as u32) << 16 | (*c.get(1).unwrap_or(&0) as u32) << 8 | *c.get(2).unwrap_or(&0) as u32;
                for i in 0..4 {
                    if i <= c.len() { out.push(T[(n >> (18 - 6 * i) & 63) as usize] as char) } else { out.push('=') }
                }
            }
            out
        };
        assert_eq!(EARLY_JS_HASH, format!("sha256-{b64}"));
        let html = page("Keys", 200, None, "/keys", "<p>x</p>", "");
        let head = html.split("</head>").next().unwrap();
        // Order in the head: the script that marks the root, then the blocking stylesheet; app.js is deferred.
        let script = head.find(&format!("<script>{EARLY_JS}</script>")).expect("the early script");
        let sheet = head.find("rel=\"stylesheet\" href=\"/assets/app.css?v=").expect("a versioned stylesheet in the head");
        assert!(script < sheet, "{head}");
        assert_eq!(head.matches("<script").count() - head.matches("<script defer").count(), 1, "the only non-deferred script is the early one: {head}");
        assert!(!head.contains("@import") && !html.contains("<style"));
        // The pane head is in the markup, so dressing it with buttons changes no height.
        assert!(html.contains("<div class=\"pane-head\"><h1 class=\"pane-title\">Keys</h1></div>"));
        // Every asset has a tag and a content type.
        for (name, kind, _) in ASSETS {
            assert!(asset_tag(name).is_some_and(|t| t.len() == 12), "{name}");
            assert!(kind.starts_with("text/css") || kind.starts_with("text/javascript"));
        }
    }

    #[test]
    fn the_shell_carries_the_rail_identity_and_the_sentence() {
        let who = Who { sid: "s".into(), name: "alice".into(), csrf: "c".into() };
        let html = page("Documents", 200, Some(&who), "/doc", "<p>x</p>", "11 November 2026");
        assert!(html.contains("aria-current=\"page\">Documents"));
        assert!(html.contains("alice"));
        assert!(html.contains("action=\"/logout\""));
        assert!(html.contains(WORLD_READABLE.split(':').next().unwrap()));
        assert!(html.contains("11 November 2026"));
        assert!(!html.contains("xterm.js"), "xterm loads only with a terminal on the stage");
        let injected = inject_csrf("<form method=\"post\" action=\"/x\"><button>Go</button></form><form method=\"get\"><input></form><FORM METHOD=POST class=\"row\">", "tok");
        assert_eq!(injected.matches("name=\"csrf\" value=\"tok\"").count(), 2, "{injected}");
        let foreign = inject_csrf("<form method=\"post\" action=\"https://a7.demo.dregg.online/__mini/bootstrap\" target=\"_blank\"><input name=\"token\"></form><form method=post action=//evil.example/x></form><form method=\"post\" action=\"/doc/a/append\"></form><form method=\"post\"></form>", "tok");
        assert_eq!(foreign.matches("name=\"csrf\"").count(), 2, "only the same-origin forms carry the token: {foreign}");
        assert!(!foreign.split("</form>").next().unwrap().contains("csrf"), "{foreign}");
        assert!(injected.starts_with("<form method=\"post\" action=\"/x\"><input type=\"hidden\" name=\"csrf\" value=\"tok\"><button>"), "{injected}");
        let anon = page("Mini", 200, None, "/", &term_page("abc"), "");
        assert!(anon.contains("public reader") && anon.contains("/join") && anon.contains("xterm.js"));
        let table = registry_html(&serde_json::json!({"format": 3, "operations": [{"code": 0, "symbol": "DESCRIBE", "status": "active", "routes": ["public"], "owner": "kernel-client", "purpose": "describe", "receiver": "dispatchSession", "effect": "none"}, {"code": 9, "symbol": "X", "status": "reserved"}], "response_markers": {"253": "NO_RECORD"}}));
        assert!(table.contains("DESCRIBE") && table.contains("(1 active)") && table.contains("NO_RECORD"), "{table}");
        assert!(registry(None).contains("--registry"));
        let dir = std::env::temp_dir().join(format!("mini-web-defaults-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("law.account.json"), "{\"type\":\"all\",\"predicates\":[{\"type\":\"eq\",\"slot\":\"request/subject\",\"value\":\"@OWNER\"}]}").unwrap();
        let laws = default_laws(Some(&dir));
        assert!(laws.contains("law.account.json") && laws.contains("placeholder @OWNER") && laws.contains("request/subject"), "{laws}");
        assert!(default_laws(None).contains("--defaults"));
        assert_eq!(when(0), "1970-01-01 00:00Z");
        assert_eq!(when(1_761_600_000), "2025-10-27 21:20Z");
    }

    /// Every page's footer links the derived feedback form, prefilled with the page; an error page
    /// also carries its status, and the gateway's own refusal partial carries its clause.
    #[test]
    fn every_footer_and_failed_outcome_offers_the_report_form() {
        let who = Who { sid: "s".into(), name: "al".into(), csrf: "c".into() };
        let ok = page("Documents", 200, Some(&who), "/doc/a b", "<p>x</p>", "");
        assert!(ok.contains("<footer class=\"foot\">") && ok.contains("href=\"/verb/feedback?page=%2Fdoc%2Fa%20b\""), "{ok}");
        assert!(ok.contains(">Report a problem</a></p></footer>"));
        let public = page("Open a session", 401, None, "/grants", "<p>x</p>", "");
        assert!(public.contains("page=%2Fgrants&amp;clause=HTTP%20401%3A%20Open%20a%20session"), "{public}");
        let refused = refusal("refused: no-grant: nothing", "");
        assert!(refused.contains("href=\"/verb/feedback?clause=refused%3A%20no-grant%3A%20nothing\""), "{refused}");
        assert!(!outcome("admitted", "Admitted", "", &[]).contains("Report a problem"));
    }
}
