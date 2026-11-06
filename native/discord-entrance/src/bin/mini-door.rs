//! `mini-door`: the `/join` form of the self-serve door (deploy/door/README.md).
//!
//! Runs as the unprivileged uid `mini-door` behind Caddy on loopback. It holds no key, reaches
//! no Mini socket and has no sudo: a POST writes one bounded request to the queue
//! (`crate::door`), and a GET of `/join/status/ID` shows the status file the root processor
//! wrote. Every check here is repeated by the processor; these are for the stranger's sake.
//!
//! Plain HTML forms, no script. Environment (the unit's; nothing on argv):
//!
//! | variable | default |
//! |---|---|
//! | `MINI_DOOR_LISTEN` | `127.0.0.1:8796` (loopback only) |
//! | `MINI_DOOR_QUEUE` | `/var/lib/mini-door/queue` (this uid's, 0700) |
//! | `MINI_DOOR_STATUS` | `/var/lib/mini-door-status` (root:mini-door 0750; the processor writes it) |
//! | `MINI_DOOR_TRUSTED_PROXY` | `127.0.0.1` (the only peer whose `X-Real-IP` is believed) |
//! | `MINI_DOOR_MAX_QUEUED` | `32` requests waiting at once |
//! | `MINI_DOOR_POSTS_PER_HOUR` | `3` per IPv4 address or IPv6 /64 |

use std::collections::HashMap;
use std::net::{IpAddr, TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use minidregg_discord_entrance::door::{self, html, Request, Route};
use minidregg_discord_entrance::http::{read_request, write_attachment, write_response};
use minidregg_discord_entrance::{env_u64, now_s};
use serde_json::Value;

const MAX_CONNECTIONS: usize = 16;
const MAX_FORM: usize = 4096;
const RATE_TABLE: usize = 1024;

struct Door {
    queue: PathBuf,
    status: PathBuf,
    trusted: IpAddr,
    max_queued: usize,
    per_hour: u64,
    /// source key -> POST times in the last hour.
    seen: Mutex<HashMap<String, Vec<u64>>>,
}

fn fail(msg: impl std::fmt::Display) -> ! {
    eprintln!("mini-door: {msg}");
    std::process::exit(78);
}

fn env_or(name: &str, default: &str) -> String {
    std::env::var(name).ok().filter(|v| !v.is_empty()).unwrap_or_else(|| default.to_owned())
}

/// `application/x-www-form-urlencoded`, decoded; a repeated or malformed field refuses.
fn form(body: &[u8]) -> Result<HashMap<String, String>, String> {
    if body.len() > MAX_FORM {
        return Err("the form is larger than 4 KiB".into());
    }
    let text = std::str::from_utf8(body).map_err(|_| "the form is not UTF-8")?;
    let mut out = HashMap::new();
    for pair in text.split('&').filter(|p| !p.is_empty()) {
        let (k, v) = pair.split_once('=').unwrap_or((pair, ""));
        let decode = |s: &str| -> Result<String, String> {
            let bytes = s.as_bytes();
            let mut raw = Vec::with_capacity(bytes.len());
            let mut i = 0;
            while i < bytes.len() {
                match bytes[i] {
                    b'+' => raw.push(b' '),
                    b'%' if i + 2 < bytes.len() => {
                        let hex = std::str::from_utf8(&bytes[i + 1..i + 3]).map_err(|_| "bad escape")?;
                        raw.push(u8::from_str_radix(hex, 16).map_err(|_| "bad escape")?);
                        i += 2;
                    }
                    b'%' => return Err("bad escape".into()),
                    c => raw.push(c),
                }
                i += 1;
            }
            String::from_utf8(raw).map_err(|_| "a field is not UTF-8".into())
        };
        if out.insert(decode(k)?, decode(v)?).is_some() {
            return Err("a form field is repeated".into());
        }
    }
    Ok(out)
}

/// The rate-limit key: the client's IPv4 address or IPv6 /64, from `X-Real-IP` only when the
/// connection comes from the trusted proxy.
fn source_key(peer: IpAddr, real_ip: Option<&str>, trusted: IpAddr) -> String {
    let ip = if peer == trusted {
        real_ip.and_then(|v| v.trim().parse::<IpAddr>().ok()).unwrap_or(peer)
    } else {
        peer
    };
    match ip {
        IpAddr::V4(v4) => v4.to_string(),
        IpAddr::V6(v6) => {
            let s = v6.segments();
            format!("{:x}:{:x}:{:x}:{:x}::/64", s[0], s[1], s[2], s[3])
        }
    }
}

/// Refuse cross-origin browser `POST` submissions (`Origin` and `Sec-Fetch-Site`).
fn same_origin_post(req: &minidregg_discord_entrance::http::Request) -> Result<(), &'static str> {
    if let Some(site) = req.header("sec-fetch-site").map(str::trim) {
        if !site.eq_ignore_ascii_case("same-origin") && !site.eq_ignore_ascii_case("none") {
            return Err("cross-site POST refused");
        }
    }
    if let Some(origin) = req.header("origin").map(str::trim) {
        let origin_host = origin
            .strip_prefix("https://")
            .or_else(|| origin.strip_prefix("http://"))
            .unwrap_or("");
        if origin_host.is_empty() || origin_host.contains('/') {
            return Err("cross-origin POST refused");
        }
        if let Some(host) = req.header("host").map(str::trim).filter(|h| !h.is_empty()) {
            if !origin_host.eq_ignore_ascii_case(host) {
                return Err("cross-origin POST refused");
            }
        }
    }
    Ok(())
}

const STYLE: &str = include_str!("../../../mini-web/assets/app.css");

/// The vendored scripts the wallet page loads (assets/vendor/VENDOR.md pins them) and the page's
/// own payment script; nothing is fetched from anywhere else.
fn asset(path: &str) -> Option<(&'static [u8], &'static str)> {
    Some(match path {
        "/join/assets/solpay.js" => (include_bytes!("../../assets/solpay.js"), "application/javascript; charset=utf-8"),
        "/join/assets/wallet.js" => (include_bytes!("../../assets/vendor/wallet.js"), "application/javascript; charset=utf-8"),
        "/join/assets/pay.js" => (include_bytes!("../../assets/pay.js"), "application/javascript; charset=utf-8"),
        _ => return None,
    })
}

/// The status page's wallet wiring: list the wallets the browser has (sol-misc's adapter), one
/// button each; a press runs pay.js's `pay` and says each step; the door's answer is the status
/// page itself, reloaded once the signature is posted.
const WALLET_PAGE: &str = r#"(async () => {
  const out = document.getElementById("wallet-pay"); if (!out) return;
  const say = (t) => { out.querySelector(".status").textContent = t; };
  try {
    const quote = JSON.parse(document.getElementById("quote").textContent);
    const conn = new solpay.Connection(quote.rpc, "confirmed", (u, o) => fetch(u, o));
    const pay = makeDoorPay(solpay, quote, { conn, fetch: (u, o) => fetch(u, o) });
    const late = pay.stale();
    if (late) { say(late); return; }
    const wallets = await passwapWallets.list(solpay, { chain: quote.network === "devnet" ? "solana:devnet" : "solana:mainnet" });
    if (!wallets.length) { say("No Solana wallet extension was found in this browser (Phantom, Solflare, Backpack, Talisman, ...); the paste path below works with any wallet."); return; }
    for (const w of wallets) {
      const b = document.createElement("button"); b.textContent = "Pay with " + w.name;
      b.onclick = async () => {
        for (const x of out.querySelectorAll("button")) x.disabled = true;
        try {
          // The signature is shown, and put into the paste form, the moment the cluster returns it.
          const sent = (sig) => {
            out.querySelector(".sent").innerHTML = "Your transaction: <code></code>";
            out.querySelector(".sent code").textContent = sig;
            const field = document.querySelector("form[action='/join/paid'] input[name=transaction]");
            if (field) field.value = sig;
          };
          const r = await pay.pay(w, say, sent);
          say("Sent and posted: " + r.signature + ". The door decides within a minute; this page reloads to show it.");
          setTimeout(() => location.reload(), 65000);
        } catch (e) { say(String(e && e.message || e)); for (const x of out.querySelectorAll("button")) x.disabled = false; }
      };
      out.querySelector(".wallets").append(b, " ");
    }
  } catch (e) { say("The wallet page could not start: " + String(e && e.message || e) + ". The paste path below still works."); }
})();"#;

/// A page that reloads itself every `seconds` while the door waits on the processor.
fn page_refreshing(title: &str, body: &str, seconds: u32) -> Vec<u8> {
    let mut bytes = page(title, body);
    let tag = format!("<meta http-equiv=\"refresh\" content=\"{seconds}\">");
    if let Some(at) = bytes.windows(7).position(|w| w == b"<title>") {
        bytes.splice(at..at, tag.into_bytes());
    }
    bytes
}

fn page(title: &str, body: &str) -> Vec<u8> {
    format!(
        "<!doctype html><html lang=en><meta charset=utf-8><meta name=viewport content=\"width=device-width,initial-scale=1\"><meta name=color-scheme content=\"light dark\">\
         <title>{} · Mini</title><style>{STYLE}</style><body class=\"standalone\"><a class=\"skip\" href=\"#main\">Skip to content</a><header><a class=\"brand\" href=\"/\">Mini</a><a href=\"/tour\">Explore the demo</a></header><main id=\"main\"><p class=\"eyebrow\">Account signup</p><h1>{}</h1>{body}</main></body></html>",
        html(title),
        html(title)
    )
    .into_bytes()
}

impl Door {
    fn state(&self) -> Value {
        read_json(&self.status.join("door-state.json")).unwrap_or(Value::Null)
    }

    fn join_page(&self) -> Vec<u8> {
        let state = self.state();
        let free = state["free"].as_bool().unwrap_or(false);
        let paid = state["paid"].as_bool().unwrap_or(false);
        let port = state["sshPort"].as_u64().unwrap_or(2222);
        let port_flag = if port == 22 { String::new() } else { format!("-p {port} ") };
        let mut body = format!(
            "<p class=warn><strong>Public demo box:</strong> everything here is readable by other members, and your account key \
             is hosted on the box. Do not post private data.</p>\
             <p>Get a Mini account with a browser workspace and (if you add an SSH key) shell access via \
             <code>ssh -t {port_flag}mini-s-NAME@demo.dregg.online</code>.</p>"
        );
        if !free && !paid {
            let why = state["freeReason"].as_str().unwrap_or("the door is not open yet");
            body.push_str(&format!("<p><strong>The door is closed:</strong> {}.</p>", html(why)));
            return page("Join the Mini demo", &body);
        }
        body.push_str("<form method=post action=/join>\
            <p><label>Account name (2–25 lowercase letters, digits or <code>-</code>, starting with a letter)<br>\
            <input type=text name=name required maxlength=25 pattern=\"[A-Za-z][A-Za-z0-9-]{1,24}\" title=\"2 to 25 letters, digits or -, starting with a letter\"></label></p>\
            <p><label>SSH public key (<code>ssh-ed25519 …</code>; optional for free accounts, required for paid entry)<br>\
            <textarea name=key rows=3 maxlength=600></textarea></label></p>");
        if free {
            body.push_str("<p><label><input type=radio name=route value=free checked> Free: sponsored starter account</label><br>");
            if state["inviteReserve"].as_u64().unwrap_or(0) > 0 {
                let open = state["openSeats"].as_u64().unwrap_or(0);
                let held = state["reservedSeats"].as_u64().unwrap_or(0);
                body.push_str(&format!("{open} open free seats remain ({held} reserved for invite codes).<br>\
                    <label>Invite code, <em>optional</em><br><input type=text name=invite maxlength=64 pattern=\"[A-Za-z0-9-]{{8,64}}\" autocomplete=off></label><br>"));
            }
        } else {
            let why = state["freeReason"].as_str().unwrap_or("closed");
            body.push_str(&format!("<p>The free route is closed ({}).<br>", html(why)));
        }
        if paid {
            let network = state["network"].as_str().unwrap_or("?");
            body.push_str(&format!(
                "<label><input type=radio name=route value=paid{}> Pay: 50 DREGG / week on Solana ({})</label>",
                if free { "" } else { " checked" },
                html(network)
            ));
        }
        body.push_str(&format!("</p><p class=policy>{}</p><p><label><input type=checkbox name=research value=cc0> Contribute my activity for research (CC0)</label></p>", html(door::RETENTION_POLICY)));
        body.push_str("<p><label><input type=checkbox name=discord value=on> Link a Discord account</label></p>\
            <p><button>Create account</button></p></form>");
        page("Join the Mini demo", &body)
    }

    fn status_page(&self, id: &str) -> (u16, Vec<u8>) {
        // What the door has queued for this request and the processor has not taken yet: the status page
        // says so, and refreshes itself until the processor's answer is on it.
        let queued = ["join", "sign", "paid"].into_iter().find(|k| self.queue.join(format!("{k}-{id}.json")).exists());
        let Some(v) = read_json(&self.status.join(format!("{id}.json"))) else {
            if queued.is_some() {
                return (200, page_refreshing("Request queued", "<p>Your request is queued; the box takes it within seconds. This page refreshes itself.</p>", 4));
            }
            return (404, page("Unknown request", "<p>No request has this id.</p>"));
        };
        let phase = v["phase"].as_str().unwrap_or("");
        let name = v["name"].as_str().unwrap_or("");
        let mut body = format!("<p>Request <code>{}</code> for <code>{}</code>: <strong>{}</strong>.</p>", html(id), html(name), html(phase));
        let mut refresh = None;
        if let Some(kind) = queued {
            let what = match kind { "sign" => "signature", "paid" => "payment notice", _ => "request" };
            body.push_str(&format!("<p>Your {what} is queued; the box checks it within seconds. This page refreshes itself.</p>"));
            refresh = Some(4);
        } else if let Some(detail) = v["detail"].as_str() {
            body.push_str(&format!("<p>{}</p>", html(detail)));
            if detail.starts_with("the box will retry") {
                body.push_str("<p>The box retries this step on its own, about once a minute. This page refreshes itself.</p>");
                refresh = Some(20);
            }
        } else if matches!(phase, "account" | "keyed" | "signed" | "paid") {
            body.push_str("<p>Provisioning in progress: the box is making your account and workspace. This page refreshes itself.</p>");
            refresh = Some(6);
        }
        if phase == "enrolled" {
            if let Some(login) = v["login"].as_str() {
                body.push_str(&format!("<p>Log in with:</p><pre>ssh -t {}</pre>", html(login)));
            }
        }
        if let Some(web) = v["webLogin"].as_str() {
            body.push_str(&format!(
                "<p>{lead} open your workspace in the browser (one-time link, valid for 7 days):</p><pre><a href=\"{web}\">{web}</a></pre>",
                web = html(web),
                lead = if phase != "enrolled" || v["login"].is_null() { "Browser workspace —" } else { "Or" }
            ));
        }
        if let Some(code) = v["linkCode"].as_str() {
            body.push_str(&format!("<p>In Discord, run once within 7 days:</p><pre>/mini line:link {}</pre>", html(code)));
        }
        body.push_str(&story_section(&v["story"]));
        if phase == "sign" {
            if v["sign"]["message"].as_str().is_some() {
                body.push_str(&format!(
                    "<p>1. <a href=\"/join/status/{id}/dregg-enrol.msg\" download=\"dregg-enrol.msg\">Download <code>dregg-enrol.msg</code></a> and sign it with your SSH key:</p>\
                     <pre>ssh-keygen -Y sign -n {namespace} -f ~/.ssh/id_ed25519 dregg-enrol.msg</pre>\
                     <p>2. Paste <code>dregg-enrol.msg.sig</code> (before chain hour {expiry}):</p>\
                     <form method=post action=/join/sign><input type=hidden name=id value=\"{id}\">\
                     <textarea name=signature rows=8 required maxlength=2048></textarea><p><button>Submit signature</button></p></form>",
                    id = html(id),
                    namespace = html(v["sign"]["namespace"].as_str().unwrap_or("dregg-enrol@v2")),
                    expiry = html(&v["sign"]["expiryHour"].to_string()),
                ));
            }
        }
        if phase == "awaiting-payment" {
            let p = &v["payment"];
            let mut quote = p.clone();
            quote["id"] = Value::String(id.to_owned());
            let quote_json = serde_json::to_string(&quote).unwrap_or_default().replace("</", "<\\/");
            body.push_str(&format!(
                "<p>Send <strong>{}</strong> (<code>{}</code> atomic units) to:</p><pre>{}</pre><p>with SPL Memo:</p><pre>{}</pre>\
                 <script type=\"application/json\" id=\"quote\">{quote_json}</script>\
                 <section id=\"wallet-pay\"><h2>Pay with your wallet</h2>\
                 <p>Connect a Solana wallet to sign and send this transfer via <code>{}</code>. <noscript>Requires JavaScript; or paste the transaction signature below.</noscript></p>\
                 <p class=wallets></p><p class=status role=status></p><p class=sent></p></section>\
                 <section><h2>Or paste the transaction signature</h2>\
                 <form method=post action=/join/paid><input type=hidden name=id value=\"{}\">\
                 <input type=text name=transaction required maxlength=88><p><button>I have paid</button></p></form></section>\
                 <script src=/join/assets/solpay.js></script><script src=/join/assets/wallet.js></script><script src=/join/assets/pay.js></script>\
                 <script>{WALLET_PAGE}</script>",
                html(p["amountTokens"].as_str().unwrap_or("?")),
                html(p["amountAtomic"].as_str().unwrap_or("?")),
                html(p["recipient"].as_str().unwrap_or("?")),
                html(p["memo"].as_str().unwrap_or("?")),
                html(p["rpc"].as_str().unwrap_or("the cluster")),
                html(id)
            ));
        }
        body.push_str("<p>Bookmark this page to check your request status.</p>");
        match refresh {
            Some(seconds) => (200, page_refreshing("Your Mini account", &body, seconds)),
            None => (200, page("Your Mini account", &body)),
        }
    }

    fn challenge_file(&self, id: &str) -> Option<Vec<u8>> {
        if !door::is_request_id(id) {
            return None;
        }
        let v = read_json(&self.status.join(format!("{id}.json")))?;
        door::b64_decode(v["sign"]["message"].as_str()?)
    }

    fn admit_post(&self, key: &str, now: u64) -> Result<(), (u16, String)> {
        let queued = door::spool_list(&self.queue).map_err(|e| (503, format!("the queue is unavailable: {e}")))?;
        if queued.len() >= self.max_queued {
            return Err((503, "the door is busy; try again in a few minutes".into()));
        }
        let mut seen = self.seen.lock().unwrap_or_else(|p| p.into_inner());
        if seen.len() >= RATE_TABLE && !seen.contains_key(key) {
            // Forget the source whose newest POST is oldest.
            if let Some(oldest) = seen.iter().min_by_key(|(_, t)| t.last().copied().unwrap_or(0)).map(|(k, _)| k.clone()) {
                seen.remove(&oldest);
            }
        }
        let times = seen.entry(key.to_owned()).or_default();
        times.retain(|t| now.saturating_sub(*t) < 3600);
        if times.len() as u64 >= self.per_hour {
            return Err((429, "too many requests from your address this hour; try later".into()));
        }
        times.push(now);
        Ok(())
    }

    fn post(&self, path: &str, body: &[u8], key: &str, now: u64) -> (u16, Vec<u8>) {
        // The stranger's page is unchanged; the door's journal keeps every refusal by its reason.
        let refuse = |status: u16, why: &str| {
            eprintln!("mini-door: refused {path} from {key}: {status}: {why}");
            (status, page("Not accepted", &format!("<p>{}</p><p><a href=/join>Back</a></p>", html(why))))
        };
        let fields = match form(body) {
            Ok(f) => f,
            Err(e) => return refuse(400, &e),
        };
        let field = |name: &str| fields.get(name).map(String::as_str).unwrap_or("");
        let request = match path {
            "/join" => {
                let lowered = field("name").trim().to_ascii_lowercase();
                let name = lowered.as_str();
                if !door::is_door_name(name) {
                    let why = if door::RESERVED.contains(&name) {
                        format!("the name {name} is reserved for the box; choose another")
                    } else if !(2..=25).contains(&name.len()) {
                        "a name is 2 to 25 characters".to_owned()
                    } else if !name.starts_with(|c: char| c.is_ascii_lowercase()) {
                        "a name starts with a letter".to_owned()
                    } else if name.ends_with('-') {
                        "a name does not end with -".to_owned()
                    } else {
                        "a name uses only letters, digits and - (no spaces, dots or _)".to_owned()
                    };
                    return refuse(400, &why);
                }
                let ssh_key = if field("key").trim().is_empty() {
                    String::new()
                } else {
                    match door::ssh_ed25519(field("key")) {
                        Ok(k) => k,
                        Err(e) => return refuse(400, &e),
                    }
                };
                let state = self.state();
                let route = match field("route") {
                    "free" if state["free"] == true => Route::Free,
                    "paid" if ssh_key.is_empty() => return refuse(400, "the paid route needs your ssh key: its memo is signed with it"),
                    "paid" if state["paid"] == true => Route::Paid,
                    _ => return refuse(400, "choose a route the door offers"),
                };
                let invite = field("invite").trim();
                if !invite.is_empty() && (route != Route::Free || state["inviteReserve"].as_u64().unwrap_or(0) == 0) {
                    return refuse(400, "invite-unknown: this door takes an invite code only on the free route, and only while it holds seats for them");
                }
                if !invite.is_empty() && !door::is_invite_code(invite) {
                    return refuse(400, "invite-unknown: that is not the shape of an invite code");
                }
                if invite.is_empty() && route == Route::Free && state["inviteReserve"].as_u64().unwrap_or(0) > 0 && state["openSeats"].as_u64() == Some(0) {
                    let held = state["reservedSeats"].as_u64().unwrap_or(0);
                    return refuse(409, &format!("open-seats-gone: the open free seats are taken; {held} remain for people with an invite code"));
                }
                let id = match door::new_request_id() {
                    Ok(id) => id,
                    Err(e) => return refuse(503, &e),
                };
                Request::Join { id, at: now, name: name.into(), ssh_key, discord: field("discord") == "on", route, research: field("research") == "cc0",
                    invite: (!invite.is_empty()).then(|| invite.to_owned()) }
            }
            "/join/sign" | "/join/paid" => {
                let id = field("id");
                if !door::is_request_id(id) || !self.status.join(format!("{id}.json")).exists() {
                    return refuse(400, "no request has this id");
                }
                if path == "/join/sign" {
                    let signature = field("signature").replace("\r\n", "\n");
                    if !door::is_signature_armour(&signature) {
                        return refuse(400, "paste the whole dregg-enrol.msg.sig file, from -----BEGIN SSH SIGNATURE----- to -----END SSH SIGNATURE-----");
                    }
                    Request::Sign { id: id.into(), at: now, signature: signature.trim().to_owned() + "\n" }
                } else {
                    let transaction = field("transaction").trim();
                    if !door::is_tx_signature(transaction) {
                        return refuse(400, "that is not a Solana transaction signature (base58, about 88 characters)");
                    }
                    Request::Paid { id: id.into(), at: now, transaction: transaction.into() }
                }
            }
            _ => return (404, page("Not found", "")),
        };
        // The per-source budget counts new requests only: a later step (`/join/sign`, `/join/paid`)
        // names a request the budget already admitted, is refused twice before the processor
        // consumes it, and so cannot be spammed; counting it let one stranger's happy path spend a
        // shared address's whole hour.
        if path == "/join" {
            if let Err((status, why)) = self.admit_post(key, now) {
                return refuse(status, &why);
            }
        }
        // A later step of the same request is a new file each time it is retried after the
        // processor consumed the previous one; the same step twice before that is refused.
        match door::spool_write(&self.queue, &request.file_name(), &request.to_json()) {
            Ok(()) => {
                let id = request.id();
                eprintln!("mini-door: queued {} from {key}", request.file_name());
                // The browser lands on the status page itself (303), which names what is queued and refreshes
                // itself until the processor has taken it: a bare "queued, follow this link" page sent every
                // submitter to a dead end and a manual reload (ember, 2026-11-06).
                (303, format!("/join/status/{id}").into_bytes())
            }
            Err(e) => refuse(409, &e),
        }
    }

    fn connection(&self, mut stream: TcpStream) {
        let peer = stream.peer_addr().map(|a| a.ip()).unwrap_or(IpAddr::from([0, 0, 0, 0]));
        let req = match read_request(&mut stream) {
            Ok(r) => r,
            Err(e) => {
                if let Some((status, reason)) = e.status {
                    eprintln!("mini-door: refused a request from {peer}: {status} {reason}: {}", e.detail);
                    let _ = write_response(&mut stream, status, reason, "text/plain", e.detail.as_bytes());
                }
                return;
            }
        };
        let now = now_s();
        // The wallet page's scripts: vendored, pinned (assets/vendor/VENDOR.md), served by the door itself.
        if req.method == "GET" {
            if let Some((bytes, kind)) = asset(&req.path) {
                let _ = write_response(&mut stream, 200, "OK", kind, bytes);
                return;
            }
            if let Some(id) = req.path.strip_prefix("/join/status/").and_then(|s| s.strip_suffix("/dregg-enrol.msg")) {
                if let Some(bytes) = self.challenge_file(id) {
                    let _ = write_attachment(&mut stream, "dregg-enrol.msg", &bytes);
                    return;
                }
            }
        }
        let (status, body) = match (req.method.as_str(), req.path.as_str()) {
            ("GET", "/join") | ("GET", "/join/") => (200, self.join_page()),
            ("GET", p) if p.starts_with("/join/status/") => {
                let id = &p["/join/status/".len()..];
                if door::is_request_id(id) { self.status_page(id) } else { (404, page("Unknown request", "")) }
            }
            ("POST", p) if matches!(p, "/join" | "/join/sign" | "/join/paid") => {
                let key = source_key(peer, req.header("x-real-ip"), self.trusted);
                match same_origin_post(&req) {
                    Ok(()) => self.post(p, &req.body, &key, now),
                    Err(why) => {
                        eprintln!("mini-door: refused {p} from {key}: 403: {why}");
                        (403, page("Forbidden", &format!("<p>{}</p><p><a href=/join>Back</a></p>", html(why))))
                    }
                }
            }
            ("GET", "/healthz") => (200, b"ok\n".to_vec()),
            _ => (404, page("Not found", "")),
        };
        let reason = match status { 200 => "OK", 303 => "See Other", 400 => "Bad Request", 403 => "Forbidden", 404 => "Not Found", 409 => "Conflict", 429 => "Too Many Requests", _ => "Service Unavailable" };
        let _ = write_response(&mut stream, status, reason, "text/html; charset=utf-8", &body);
    }
}

fn read_json(path: &Path) -> Option<Value> {
    let meta = std::fs::symlink_metadata(path).ok()?;
    if !meta.is_file() || meta.len() > 64 * 1024 {
        return None;
    }
    serde_json::from_slice(&std::fs::read(path).ok()?).ok()
}

fn main() {
    if std::env::args_os().len() > 1 {
        fail("takes no arguments; configuration is the environment");
    }
    let listen = env_or("MINI_DOOR_LISTEN", "127.0.0.1:8796");
    let addr: std::net::SocketAddr = listen.parse().unwrap_or_else(|_| fail("MINI_DOOR_LISTEN is not an address"));
    if !addr.ip().is_loopback() {
        fail("MINI_DOOR_LISTEN must be a loopback address: Caddy is the only client");
    }
    let door = Arc::new(Door {
        queue: PathBuf::from(env_or("MINI_DOOR_QUEUE", "/var/lib/mini-door/queue")),
        status: PathBuf::from(env_or("MINI_DOOR_STATUS", "/var/lib/mini-door-status")),
        trusted: env_or("MINI_DOOR_TRUSTED_PROXY", "127.0.0.1").parse().unwrap_or_else(|_| fail("MINI_DOOR_TRUSTED_PROXY is not an address")),
        max_queued: env_u64("MINI_DOOR_MAX_QUEUED", 32).unwrap_or_else(|e| fail(e)) as usize,
        per_hour: env_u64("MINI_DOOR_POSTS_PER_HOUR", 3).unwrap_or_else(|e| fail(e)),
        seen: Mutex::new(HashMap::new()),
    });
    if let Err(e) = mini_sdk::private::ensure_dir(&door.queue) {
        fail(format!("{}: {e}", door.queue.display()));
    }
    let listener = TcpListener::bind(addr).unwrap_or_else(|e| fail(format!("bind {listen}: {e}")));
    eprintln!("mini-door: listening on {listen}");
    let open = Arc::new(AtomicUsize::new(0));
    for stream in listener.incoming() {
        let Ok(stream) = stream else { continue };
        if open.fetch_add(1, Ordering::SeqCst) >= MAX_CONNECTIONS {
            open.fetch_sub(1, Ordering::SeqCst);
            continue;
        }
        let (door, open) = (door.clone(), open.clone());
        std::thread::spawn(move || {
            door.connection(stream);
            open.fetch_sub(1, Ordering::SeqCst);
        });
    }
}

/// The stranger's view of the story welcome (`story` on the published status), or nothing.
fn story_section(story: &Value) -> String {
    let Some(name) = story["name"].as_str().filter(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')) else {
        return String::new();
    };
    let lead = format!("<section class=story data-story=\"{0}\"><h2>Story <code>{0}</code></h2>", html(name));
    let state = if story["joined"] == true {
        format!("<p data-story-state=joined>The box invited you to play <code>{0}</code> and you have joined it. Play it from your workspace: <a href=/story>your stories</a> (or <code>look</code> in your shell).</p>", html(name))
    } else if let Some(error) = story["error"].as_str() {
        format!("<p data-story-state=stopped>The box invited you to play <code>{0}</code>, but joining did not finish: <code>{1}</code>. The door tries again on its next run; or join it yourself from your workspace, where the invitation waits: <a href=/story#invitations>join {0}</a>.</p>", html(name), html(error))
    } else if story["invited"].is_string() {
        format!("<p data-story-state=invited>The box invited you to play <code>{0}</code>; the invitation is in your requests and the door joins you on its next run. <a href=/story#invitations>Join it now</a> from your workspace.</p>", html(name))
    } else {
        return String::new();
    };
    format!("{lead}{state}</section>")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore = "writes the real join page to MINI_WEB_PREVIEW"]
    fn design_preview() {
        let dir = std::path::PathBuf::from(std::env::var("MINI_WEB_PREVIEW").expect("MINI_WEB_PREVIEW"));
        let d = door("design-preview");
        std::fs::write(dir.join("join.html"), d.join_page()).unwrap();
        let file = dir.join("pages.json");
        let mut pages: Value = serde_json::from_slice(&std::fs::read(&file).unwrap()).unwrap();
        pages.as_array_mut().unwrap().push(serde_json::json!({"name":"join","path":"/join","title":"Join the Mini demo","standalone":true}));
        std::fs::write(file, serde_json::to_vec_pretty(&pages).unwrap()).unwrap();
    }

    const KEY: &str = "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIOMqqnkVzrm0SdG6UOoqKLsabgH5C9okWi0dh2l9GKJl";

    fn door(tag: &str) -> Door {
        let root = std::env::temp_dir().join(format!("mini-door-{tag}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        for d in ["queue", "status"] {
            std::fs::create_dir_all(root.join(d)).unwrap();
        }
        std::fs::write(root.join("status/door-state.json"), r#"{"type":"minidregg-door-state-v1","free":true,"paid":false,"funding":"10000"}"#).unwrap();
        Door { queue: root.join("queue"), status: root.join("status"), trusted: "127.0.0.1".parse().unwrap(),
            max_queued: 2, per_hour: 3, seen: Mutex::new(HashMap::new()) }
    }

    fn enc(s: &str) -> String {
        s.bytes().map(|b| if b.is_ascii_alphanumeric() { (b as char).to_string() } else { format!("%{b:02X}") }).collect()
    }

    #[test]
    fn forms_decode_and_refuse_repeats() {
        let f = form(b"name=al+ice&key=ssh-ed25519%20AAAA").unwrap();
        assert_eq!(f["name"], "al ice");
        assert_eq!(f["key"], "ssh-ed25519 AAAA");
        assert!(form(b"a=1&a=2").is_err());
        assert!(form(b"a=%zz").is_err());
        assert!(form(b"a=%2").is_err());
        assert!(form(&vec![b'a'; MAX_FORM + 1]).is_err());
    }

    #[test]
    fn the_source_is_the_proxys_word_only_from_the_proxy() {
        let proxy: IpAddr = "127.0.0.1".parse().unwrap();
        assert_eq!(source_key(proxy, Some("203.0.113.9"), proxy), "203.0.113.9");
        assert_eq!(source_key("198.51.100.1".parse().unwrap(), Some("203.0.113.9"), proxy), "198.51.100.1");
        assert_eq!(source_key(proxy, Some("2001:db8:1:2:3:4:5:6"), proxy), "2001:db8:1:2::/64");
    }

    #[test]
    fn cross_origin_and_cross_site_posts_are_refused() {
        let req = |headers: Vec<(&str, &str)>| minidregg_discord_entrance::http::Request {
            method: "POST".into(),
            path: "/join".into(),
            query: String::new(),
            headers: headers.into_iter().map(|(k, v)| (k.to_string(), v.to_string())).collect(),
            body: Vec::new(),
        };
        assert!(same_origin_post(&req(vec![("Host", "demo.dregg.online")])).is_ok());
        assert!(same_origin_post(&req(vec![("Host", "demo.dregg.online"), ("Origin", "https://demo.dregg.online"), ("Sec-Fetch-Site", "same-origin")])).is_ok());
        assert!(same_origin_post(&req(vec![("Host", "demo.dregg.online"), ("Origin", "https://evil.example")])).is_err());
        assert!(same_origin_post(&req(vec![("Host", "demo.dregg.online"), ("Origin", "null")])).is_err());
        assert!(same_origin_post(&req(vec![("Host", "demo.dregg.online"), ("Sec-Fetch-Site", "cross-site")])).is_err());
        assert!(same_origin_post(&req(vec![("Host", "demo.dregg.online"), ("Sec-Fetch-Site", "same-site")])).is_err());
    }

    #[test]
    fn a_join_post_queues_one_exact_request_and_limits_apply() {
        let d = door("post");
        let body = format!("name=alice&key={}&route=free&discord=on", enc(KEY));
        let (status, _) = d.post("/join", body.as_bytes(), "203.0.113.9", 100);
        assert_eq!(status, 303);
        let files = door::spool_list(&d.queue).unwrap();
        assert_eq!(files.len(), 1);
        match Request::parse(&std::fs::read(&files[0]).unwrap()).unwrap() {
            Request::Join { name, ssh_key, discord, route, .. } => {
                assert_eq!((name.as_str(), ssh_key.as_str(), discord, route), ("alice", KEY, true, Route::Free));
            }
            other => panic!("{other:?}"),
        }
        // A route the door does not offer, a reserved name, a bad key: refused, nothing queued.
        for bad in [format!("name=bob&key={}&route=paid", enc(KEY)), format!("name=ember&key={}&route=free", enc(KEY)),
            "name=bob&key=ssh-rsa%20AAAA&route=free".to_string()] {
            assert_eq!(d.post("/join", bad.as_bytes(), "203.0.113.9", 101).0, 400, "{bad}");
        }
        assert_eq!(door::spool_list(&d.queue).unwrap().len(), 1);
        // The queue bound, then the per-source bound.
        assert_eq!(d.post("/join", format!("name=bob&key={}&route=free", enc(KEY)).as_bytes(), "198.51.100.7", 102).0, 303);
        assert_eq!(d.post("/join", format!("name=carol&key={}&route=free", enc(KEY)).as_bytes(), "198.51.100.8", 103).0, 503);
        let mut d = door("rate");
        d.max_queued = 10;
        for (i, name) in ["aa", "bb", "cc", "dd"].iter().enumerate() {
            let status = d.post("/join", format!("name={name}&key={}&route=free", enc(KEY)).as_bytes(), "203.0.113.1", 200 + i as u64).0;
            assert_eq!(status, if i < 3 { 200 } else { 429 }, "{name}");
        }
        // An hour later the source may post again.
        assert_eq!(d.post("/join", format!("name=ee&key={}&route=free", enc(KEY)).as_bytes(), "203.0.113.1", 3900).0, 200);
    }

    #[test]
    fn status_pages_escape_and_show_the_next_step() {
        let d = door("status");
        let id = door::new_request_id().unwrap();
        std::fs::write(d.status.join(format!("{id}.json")), serde_json::json!({"phase":"sign","name":"alice",
            "detail":"<script>","sign":{"message":"QUJD","namespace":"dregg-enrol@v2","expiryHour":1001}}).to_string()).unwrap();
        let (status, body) = d.status_page(&id);
        let body = String::from_utf8(body).unwrap();
        assert_eq!(status, 200);
        assert!(body.contains("&lt;script&gt;") && !body.contains("<script>"));
        assert!(body.contains(&format!("/join/status/{id}/dregg-enrol.msg")) && !body.contains("base64 -d"), "{body}");
        assert!(body.contains("ssh-keygen -Y sign -n dregg-enrol@v2 -f ~/.ssh/id_ed25519 dregg-enrol.msg"));
        assert!(body.contains("action=/join/sign"));
        assert_eq!(d.challenge_file(&id).as_deref(), Some(&b"ABC"[..]));
        assert_eq!(d.challenge_file("not-a-request-id"), None);
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        let mut client = TcpStream::connect(addr).unwrap();
        let (server, _) = listener.accept().unwrap();
        use std::io::{Read, Write};
        client.write_all(format!("GET /join/status/{id}/dregg-enrol.msg HTTP/1.1\r\nHost: localhost\r\n\r\n").as_bytes()).unwrap();
        d.connection(server);
        let mut resp = Vec::new();
        client.read_to_end(&mut resp).unwrap();
        let resp_str = String::from_utf8(resp).unwrap();
        assert!(resp_str.starts_with("HTTP/1.1 200 OK\r\n"), "{resp_str}");
        assert!(resp_str.contains("Content-Type: application/octet-stream\r\n"), "{resp_str}");
        assert!(resp_str.contains("Content-Disposition: attachment; filename=\"dregg-enrol.msg\"\r\n"), "{resp_str}");
        assert!(resp_str.ends_with("\r\n\r\nABC"), "{resp_str}");
        assert_eq!(d.status_page(&door::new_request_id().unwrap()).0, 404);
    }

    #[test]
    fn the_paid_status_page_carries_the_quote_as_data_the_wallet_button_and_the_paste_path() {
        let d = door("paid-status");
        let id = door::new_request_id().unwrap();
        std::fs::write(d.status.join(format!("{id}.json")), serde_json::json!({"phase":"awaiting-payment","name":"alice",
            "payment":{"recipient":"7f","amountAtomic":"50000007","memo":"enrol:v2:AAAA</script>","expiryHour":1001,"network":"mainnet",
                       "mint":"8k","tokenProgram":"TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA","decimals":"6","rpc":"https://solana-rpc.publicnode.com"}}).to_string()).unwrap();
        let (status, body) = d.status_page(&id);
        let body = String::from_utf8(body).unwrap();
        assert_eq!(status, 200);
        let quote_start = body.find("<script type=\"application/json\" id=\"quote\">").unwrap();
        let quote = &body[quote_start..];
        let quote = &quote[quote.find('>').unwrap() + 1..quote.find("</script>").unwrap()];
        let quote: serde_json::Value = serde_json::from_str(quote).unwrap();
        assert_eq!(quote["id"], id);
        assert_eq!(quote["memo"], "enrol:v2:AAAA</script>", "the memo survives, byte for byte, with the closing tag escaped in transit");
        assert_eq!(quote["decimals"], "6");
        assert!(body.contains("Pay with your wallet") && body.contains("/join/assets/pay.js") && body.contains("action=/join/paid"));
        assert!(body.contains("solana-rpc.publicnode.com"));
        for a in ["/join/assets/solpay.js", "/join/assets/wallet.js", "/join/assets/pay.js"] {
            assert!(asset(a).is_some(), "{a}");
        }
        assert!(asset("/join/assets/other.js").is_none());
        assert!(asset("/join/assets/web3.js").is_none(), "no SDK bundle is served");
    }

    #[test]
    fn a_requests_later_steps_do_not_spend_the_sources_hourly_budget() {
        let d = door("budget");
        let id = door::new_request_id().unwrap();
        std::fs::write(d.status.join(format!("{id}.json")), r#"{"phase":"awaiting-payment","name":"alice"}"#).unwrap();
        let tx = "5".repeat(87);
        for _ in 0..3 {
            let (status, _) = d.post("/join", b"name=bob&route=free", "1.2.3.4", 1000);
            assert_ne!(status, 429);
            for f in std::fs::read_dir(&d.queue).unwrap().flatten() { let _ = std::fs::remove_file(f.path()); }
        }
        let (status, _) = d.post("/join/paid", format!("id={id}&transaction={tx}").as_bytes(), "1.2.3.4", 1001);
        assert_eq!(status, 303, "the paid step of an admitted request is not counted against the address");
        let (status, _) = d.post("/join", b"name=carol&route=free", "1.2.3.4", 1002);
        assert_eq!(status, 429, "a fourth new request from the address is still refused");
    }

    #[test]
    fn the_join_and_status_pages_omit_internal_credits_and_show_ssh_login_only_when_enrolled() {
        let d = door("funding");
        let page = String::from_utf8(d.join_page()).unwrap();
        assert!(page.contains("Free: sponsored starter account") && !page.contains("credits") && !page.contains("10000"), "{page}");
        assert!(page.contains("ssh -t -p 2222 mini-s-NAME@demo.dregg.online"), "{page}");
        let id = door::new_request_id().unwrap();
        std::fs::write(d.status.join(format!("{id}.json")), serde_json::json!({"phase":"sign","name":"alice","login":"-p 2222 mini-s-alice@demo.dregg.online"}).to_string()).unwrap();
        let signing = String::from_utf8(d.status_page(&id).1).unwrap();
        assert!(!signing.contains("Log in with:"), "not shown before enrolled: {signing}");
        std::fs::write(d.status.join(format!("{id}.json")), serde_json::json!({"phase":"enrolled","name":"alice","funding":"10000",
            "login":"-p 2222 mini-s-alice@demo.dregg.online","webLogin":"https://demo.example/login/X"}).to_string()).unwrap();
        let body = String::from_utf8(d.status_page(&id).1).unwrap();
        assert!(!body.contains("credits") && !body.contains("10000"), "{body}");
        assert!(body.contains("<pre>ssh -t -p 2222 mini-s-alice@demo.dregg.online</pre>"), "{body}");
    }

    #[test]
    fn the_status_page_shows_the_story_welcome_joined_invited_or_stopped() {
        let d = door("story");
        let id = door::new_request_id().unwrap();
        let shown = |story: serde_json::Value| {
            std::fs::write(d.status.join(format!("{id}.json")), serde_json::json!({"phase":"enrolled","name":"alice","story":story}).to_string()).unwrap();
            String::from_utf8(d.status_page(&id).1).unwrap()
        };
        let joined = shown(serde_json::json!({"name":"tale","invited":"w","world":"w","joined":true}));
        assert!(joined.contains("data-story-state=joined") && joined.contains("href=/story"), "{joined}");
        let invited = shown(serde_json::json!({"name":"tale","invited":"w"}));
        assert!(invited.contains("data-story-state=invited") && invited.contains("/story#invitations"));
        let stopped = shown(serde_json::json!({"name":"tale","invited":"w","error":"story join: refused: <busy>"}));
        assert!(stopped.contains("data-story-state=stopped") && stopped.contains("refused: &lt;busy&gt;") && stopped.contains("/story#invitations"), "{stopped}");
        assert!(!shown(serde_json::json!({"name":"Tale<x>","joined":true})).contains("data-story"), "a story name that is not a door word is not shown");
        assert!(!shown(serde_json::Value::Null).contains("data-story"));
    }

    #[test]
    fn vendored_assets_match_their_pins() {
        use sha2::Digest;
        let table = include_str!("../../assets/vendor/VENDOR.md");
        for (file, bytes) in [("wallet.js", &include_bytes!("../../assets/vendor/wallet.js")[..]), ("solpay.js", &include_bytes!("../../assets/solpay.js")[..])] {
            let digest = format!("{:x}", sha2::Sha256::digest(bytes));
            assert!(table.contains(&digest), "{file}: sha256 {digest} is not in VENDOR.md");
        }
    }

    #[test]
    fn the_wallet_page_builds_the_quoted_transfer_and_posts_its_signature() {
        // The page test runs under node (or bun if node's dylibs are unavailable) against a fake wallet and a fake cluster (tests/pay-page.test.mjs).
        let test = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/pay-page.test.mjs");
        let home_bun = std::env::var("HOME").ok().map(|h| format!("{h}/.bun/bin/bun")).unwrap_or_default();
        let out = std::process::Command::new("node").arg(test).output()
            .ok()
            .filter(|o| o.status.success() || !String::from_utf8_lossy(&o.stderr).contains("dyld"))
            .or_else(|| std::process::Command::new("bun").arg(test).output().ok())
            .or_else(|| (!home_bun.is_empty()).then(|| std::process::Command::new(&home_bun).arg(test).output().ok()).flatten())
            .expect("node or bun is available (the wallet page test needs it)");
        assert!(out.status.success(), "{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
        assert!(String::from_utf8_lossy(&out.stdout).starts_with("ok: transfer 50000007 atomic"));
    }

    #[test]
    fn the_page_and_the_post_speak_of_invite_codes_only_when_the_door_holds_a_reserve() {
        let d = door("invite");
        let page = String::from_utf8(d.join_page()).unwrap();
        assert!(!page.to_lowercase().contains("invite"), "no reserve, no mention of codes");
        std::fs::write(d.status.join("door-state.json"), r#"{"type":"minidregg-door-state-v1","free":true,"paid":false,"funding":"10000","inviteReserve":20,"openSeats":12,"reservedSeats":20}"#).unwrap();
        let page = String::from_utf8(d.join_page()).unwrap();
        assert!(page.contains("12 open free seats remain (20 reserved for invite codes)."), "{page}");
        assert!(page.contains("name=invite"));
        // A code rides in the queued request; open seats gone and no code is refused by name.
        let (status, _) = d.post("/join", b"name=alice&route=free&invite=INVITE001-abcdef", "203.0.113.9", 100);
        assert_eq!(status, 303);
        let files = door::spool_list(&d.queue).unwrap();
        assert!(matches!(Request::parse(&std::fs::read(&files[0]).unwrap()).unwrap(), Request::Join { invite: Some(c), .. } if c == "INVITE001-abcdef"));
        std::fs::write(d.status.join("door-state.json"), r#"{"type":"minidregg-door-state-v1","free":true,"paid":false,"inviteReserve":20,"openSeats":0,"reservedSeats":20}"#).unwrap();
        let (status, body) = d.post("/join", b"name=bob&route=free", "203.0.113.10", 101);
        assert_eq!(status, 409);
        assert!(String::from_utf8(body).unwrap().contains("open-seats-gone: the open free seats are taken; 20 remain for people with an invite code"));
        let (status, _) = d.post("/join", b"name=bob&route=free&invite=short", "203.0.113.10", 102);
        assert_eq!(status, 400);
    }
}
