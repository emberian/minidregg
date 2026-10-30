//! `mini web --body`: the member's rendering process behind the web gateway
//! (docs/WEB-FRONTEND-2026-10-27.md §2). It serves the listener the root helper bound and handed
//! it on fd 3 (a root-only path, so only the gateway, through the helper, reaches it), and answers
//! stage FRAGMENTS: the `Site` renders this file's parent already has (documents, history, diffs,
//! boards, rooms, inspection, search, the editor), plus the places the one front end adds
//! (receipts, grants and laws, keys) and the actions behind every form.
//!
//! Every action is a `mini shell` line run as this member, through the same `shell` subcommand
//! the ssh login runs (`mini shell --workspace … --home …`, script mode on stdin), and its ending
//! is rendered by one partial: exit 0 admitted, 3 refused (the Host's own clause), 4 undecided
//! (the attempt is retained; `lookup` and `retry` are offered), 1 and 2 the client's error or
//! usage. There is no admission logic here: the shell decides, the body shows.
//!
//! `--anonymous` is the public reader: no write affordance, every POST refused before any read.

use super::*;
use std::io::Read;
use std::os::fd::FromRawFd;
use std::os::unix::net::{UnixListener, UnixStream};
use std::process::{Command, Stdio};

/// The cost ceiling of a publication's `observe` grant. Every signed read is judged with a cost
/// (the encoded intent's length, `Kernel/NativeObservationController.lean` `requestAt`) and a
/// grant covers it only while `cost <= maxCost`; a grant with ceiling 0 therefore covers no read at
/// all and the Host answers every visitor `no-grant`. The value lives in one file, which the seed
/// (`deploy/demo-seed/seed.sh`) reads too; it bounds one read, it is not a budget.
pub(super) const PUBLIC_READ_MAX_COST: &str = include_str!("../../../../deploy/demo-seed/public-read-max-cost");

/// The shell's paths this body runs lines with.
pub(super) struct Shell {
    pub host: PathBuf,
    pub config: PathBuf,
    pub home: PathBuf,
    /// The public reader's subject: who a member publishes to (`delegate ID DOC SUBJECT observe MAX`, MAX = [`PUBLIC_READ_MAX_COST`]).
    pub public_subject: Option<String>,
    /// The published document the public reader's front page shows (`--front-doc`, from the
    /// operator's `/etc/mini/front-doc` through `mini-web-spawn`); `None`: the front page is the index.
    pub front_doc: Option<String>,
}

pub(super) fn run(mut args: Args, root: PathBuf) -> Result<()> {
    let fd: i32 = args
        .required("listen-fd")?
        .to_str()
        .and_then(|s| s.parse().ok())
        .filter(|fd| *fd >= 3)
        .ok_or("--listen-fd takes an inherited descriptor number (3 or above)")?;
    let anonymous = args.optional("anonymous").is_some();
    let home = absolute(&path(args.required("home")?))?;
    let host = absolute(&path(args.required("host")?))?;
    let config = absolute(&path(args.required("config")?))?;
    let public_subject = args
        .optional("public-subject")
        .map(|v| v.to_string_lossy().into_owned())
        .filter(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()));
    let front_doc = args
        .optional("front-doc")
        .map(|v| v.to_string_lossy().into_owned())
        .filter(|s| !s.is_empty() && s.len() <= 64 && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-'));
    args.finish()?;
    let workspace = workspace::load(&root)?;
    let site = Arc::new(Site {
        mutations: Mutex::new(()),
        home: Some(home.clone()),
        subject: workspace::member(&workspace, "subject")?.to_owned(),
        root,
        workspace,
        token: String::new(),
        front: Front { origins: Vec::new(), read_only: anonymous },
        base: String::new(),
        face: Face::Body,
        shell: Some(Shell { host, config, home, public_subject, front_doc }),
    });
    let listener = unsafe { UnixListener::from_raw_fd(fd) };
    eprintln!("mini web --body: subject {} serving fd {fd}{}", site.subject, if anonymous { " (anonymous)" } else { "" });
    let handler: Arc<dyn Fn(UnixStream, Instant) + Send + Sync> = Arc::new(move |stream, deadline| {
        if let Err(error) = serve(&site, stream, deadline) {
            eprintln!("mini web --body: {error}");
        }
    });
    let connections = admission::Pool::new(admission::MAX_CONNECTIONS);
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                if let Err(error) = connections.dispatch(stream, handler.clone()) {
                    eprintln!("mini web --body: {error}");
                }
            }
            Err(error) => eprintln!("mini web --body: accept: {error}"),
        }
    }
    Ok(())
}

const ANONYMOUS: &str = "the public reader shows what members published; writing needs your own session (Join, then open the link the door gives you)";

fn serve(site: &Site, mut stream: UnixStream, deadline: Instant) -> Result<()> {
    stream.set_write_timeout(Some(Duration::from_secs(10))).map_err(|e| e.to_string())?;
    let mut head = Vec::new();
    let mut buffer = [0u8; 2048];
    while !head.windows(4).any(|w| w == b"\r\n\r\n") {
        let read = admission::read_ingress(&mut stream, &mut buffer, deadline).map_err(|e| e.to_string())?;
        if read == 0 {
            return Ok(());
        }
        head.extend_from_slice(&buffer[..read]);
        if head.len() > MAX_REQUEST {
            return answer(&mut stream, &simple(431, "Too large", "request head too large"), site);
        }
    }
    let request = match parse_request(&head) {
        Ok(request) => request,
        Err(error) => return answer(&mut stream, &simple(400, "Bad request", &error), site),
    };
    let target = request.target.split(['?', '#']).next().unwrap_or("").to_owned();
    let segments: Vec<String> = target.split('/').filter(|s| !s.is_empty()).map(str::to_owned).collect();
    if segments.iter().any(|s| !s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')) {
        return answer(&mut stream, &simple(404, "Not found", "no such page"), site);
    }
    let parts: Vec<&str> = segments.iter().map(String::as_str).collect();
    let page = match request.method.as_str() {
        "GET" | "HEAD" => {
            let draft = matches!(parts.as_slice(), ["new-document", ..] | ["doc", _, "edit", ..]);
            if draft && site.front.read_only {
                simple(403, "Read only", ANONYMOUS)
            } else {
                let _mutation = if draft { Some(site.mutations.lock().map_err(|_| "custody lock poisoned")?) } else { None };
                get(site, &parts, &request.target)
            }
        }
        "POST" => {
            if site.front.read_only {
                outcome_page("Refused", "refused", "This body is the public reader", ANONYMOUS, &[])
            } else {
                let length = request
                    .headers
                    .iter()
                    .find(|(k, _)| k == "content-length")
                    .and_then(|(_, v)| v.parse::<usize>().ok())
                    .filter(|n| *n <= editor::MAX_FORM)
                    .ok_or("a form needs one bounded Content-Length")?;
                let end = head.windows(4).position(|w| w == b"\r\n\r\n").unwrap() + 4;
                let mut body = head[end..].to_vec();
                while body.len() < length {
                    let remaining = (length - body.len()).min(buffer.len());
                    let read = admission::read_ingress(&mut stream, &mut buffer[..remaining], deadline).map_err(|e| e.to_string())?;
                    if read == 0 {
                        return answer(&mut stream, &simple(400, "Incomplete", "incomplete form"), site);
                    }
                    body.extend_from_slice(&buffer[..read]);
                }
                body.truncate(length);
                if let ["export", name, "download"] = parts.as_slice() {
                    return export_download(&mut stream, site, name);
                }
                let _mutation = site.mutations.lock().map_err(|_| "custody lock poisoned")?;
                post(site, &parts, &body)
            }
        }
        _ => simple(405, "Method", "GET, HEAD and POST only"),
    };
    let mut page = page;
    if site.front.read_only && page.status >= 400 {
        log_public_failure(&format!("{} {target}", request.method), &page);
    }
    page.body = page.body.replace(PAGE_MARK, &pct(&target));
    answer(&mut stream, &page, site)
}

/// The public reader is the operator's own hosted member, and its stderr is the helper's journal:
/// a page it could not serve reaches the operator's log with its status, title and text (the
/// refusal's clause among it). What the reader's visitor sees is unchanged.
fn log_public_failure(what: &str, page: &Page) {
    let mut text = String::new();
    let mut in_tag = false;
    for c in page.body.chars() {
        match c {
            '<' => in_tag = true,
            '>' if in_tag => {
                in_tag = false;
                text.push(' ');
            }
            _ if !in_tag => text.push(c),
            _ => {}
        }
    }
    let text: String = text.split_whitespace().collect::<Vec<_>>().join(" ").chars().take(600).collect();
    eprintln!("mini web --body (public reader): {what}: {} {}: {text}", page.status, page.title);
}

/// The fragment: the read context line, then the body. The gateway adds the chrome.
fn answer(stream: &mut UnixStream, page: &Page, site: &Site) -> Result<()> {
    let context = match &page.stamp {
        Stamp::Read(read) => format!(
            "<details class=\"ctx\"><summary>Authorized read</summary><p>read as subject <span class=id>{}</span> at height <span class=id data-height=\"{h}\">{h}</span> | authority root {} | cell root {} | world root <span class=id data-world-root=\"{w}\">{ws}</span></p></details>\n",
            escape(&site.subject),
            short(&read.authority_root),
            short(&read.cell_root),
            h = escape(&read.height),
            w = escape(&read.world_root),
            ws = short(&read.world_root)
        ),
        Stamp::EditBase(read) => format!("<p class=\"ctx\">Editor base snapshot at height <span class=id>{}</span>; sidebar observations may be newer.</p>\n", escape(&read.height)),
        Stamp::Refused => format!("<p class=\"ctx\">subject <span class=id>{}</span> | the Host refused this page's signed read</p>\n", escape(&site.subject)),
        Stamp::Unavailable => "<p class=\"ctx\">Current text unavailable</p>\n".to_owned(),
        Stamp::CurrentReads(_) | Stamp::None => String::new(),
    };
    let body = format!("{context}{}", page.body);
    let title = page.title.replace(['\r', '\n'], " ");
    let head = format!(
        "HTTP/1.1 {} {}\r\nContent-Type: text/html; charset=utf-8\r\nContent-Length: {}\r\nX-Mini-Title: {}\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n",
        page.status,
        reason(page.status),
        body.len(),
        title
    );
    stream.write_all(head.as_bytes()).and_then(|_| stream.write_all(body.as_bytes())).map_err(|e| e.to_string())
}

// ---------------------------------------------------------------- GET

fn get(site: &Site, parts: &[&str], target: &str) -> Page {
    match parts {
        ["tour"] => tour(site, None),
        ["activity"] => Page { status: 200, title: "Life in this world".into(), stamp: Stamp::None, body: operations(site) },
        ["export"] if !site.front.read_only => export_page(site, None),
        ["subscribe"] if !site.front.read_only => super::subscribe::page(site, None),
        [] | ["doc"] => {
            if site.front.read_only {
                import_inbox(site);
                if parts.is_empty() {
                    return public_front(site);
                }
            }
            let mut page = site.index();
            if site.front.read_only {
                page.title = "Mini".into();
                page.body = format!(
                    "<p>The world as the public reader sees it: the documents members published, the box's own operations room, \
                     the <a href=\"/receipts\">receipts stream</a> and the <a href=\"/registry\">laws of the box</a>. A <a href=\"/tour\">tour</a> shows what a member can do.</p>\n{}{}",
                    operations(site),
                    page.body
                );
            }
            if let Some(summary) = super::subscribe::summary() {
                let next = if site.front.read_only { "<a href=\"/join\">Join</a>, then subscribe from your workspace" } else { "<a href=\"/subscribe\">Subscribe</a>" };
                page.body.push_str(&format!("<section><h2>Subscribers</h2><p>{summary} {next}.</p></section>\n"));
            }
            // An invitation to a story the member does not play yet (the door hands the built-in
            // tale's): said first, with where to join it.
            if !site.front.read_only {
                let waiting = stories::waiting(site);
                if !waiting.is_empty() {
                    let names: Vec<String> = waiting.iter().map(|i| format!("<code>{}</code>", escape(&i.story))).collect();
                    page.body.insert_str(0, &format!("<section class=\"notice\" data-invited=\"{}\"><h2>You are invited to play</h2><p>An invitation to {} waits in your requests: <a href=\"/story#invitations\">join it</a>.</p></section>\n", waiting.len(), names.join(", ")));
                }
            }
            if !site.front.read_only && now_secs() >= EXPORT_NOTICE_FROM {
                page.body.insert_str(0, "<section class=\"notice\"><h2>This demo ends on 11 November</h2><p>Take your world with you: <a href=\"/export\">Export my world</a> hands you one archive of your documents, attempts, rooms and keys' public half, with the world root it was read at.</p></section>\n");
            }
            if !site.front.read_only {
                page.body.push_str(
                    "<section><h2>New document</h2><form method=\"post\" action=\"/doc/new\" class=\"row\"><div><label for=\"dn\">Name</label><input id=\"dn\" name=\"name\" type=\"text\" required pattern=\"[A-Za-z0-9-]+\"></div>\
                     <div><label for=\"dl\">Law</label><select id=\"dl\" name=\"law\"><option>note</option><option>draft</option><option>index</option></select></div>\
                     <div><label for=\"dr\">In room (optional)</label><input id=\"dr\" name=\"room\" type=\"text\" pattern=\"[A-Za-z0-9/-]*\"></div><button>Create</button></form></section>\n",
                );
            }
            page
        }
        ["board"] | ["room"] => place_index(site, parts[0]),
        ["search"] => search::page(site, target),
        ["purse"] => purse(site),
        ["purse", "meter"] => Page { status: 200, title: "Purse".into(), stamp: Stamp::None, body: purse_meter(site, false) },
        ["apps"] => apps::market(site, target),
        ["apps", app] => apps::show(site, app),
        ["grain"] => apps::grains(site),
        ["grain", n] => apps::grain(site, n),
        ["grain", n, "pane"] => apps::pane(site, n),
        ["bend"] => programs::index(site),
        ["bend", "await"] => match (query(target, "object"), query(target, "transaction")) {
            (Some(object), Some(transaction)) => programs::awaits(site, object.trim(), transaction.trim()),
            _ => simple(400, "Programs", "give an object cell and a birth transaction"),
        },
        ["bend", "await", object, transaction] => programs::awaits(site, object, transaction),
        ["story"] => stories::page(site),
        ["verb"] => verbs::index(site),
        ["verb", name] => verbs::page(site, name, target),
        ["verb", name, "dry"] => verbs::dry(site, name),
        ["receipts"] => receipts(site),
        ["receipts", "lookup"] => match query(target, "id") {
            Some(id) => receipt(site, &id),
            None => simple(400, "Receipts", "give an attempt id"),
        },
        ["receipts", id] => receipt(site, id),
        ["grants"] => grants(site),
        // One grant judged (`can REF --all`): the grants page fills in one of these per reference
        // as each answer lands; without JavaScript each is a page of its own.
        ["grants", "judge", name] => {
            let ending = verb(site, &[format!("can {} --all", quote(name))]);
            Page { status: 200, title: format!("What my grants cover on {name}"), stamp: Stamp::None, body: ending.map(|e| answered(&e, &[])).unwrap_or_else(|| "<p>this body has no shell paths</p>".into()) }
        }
        ["laws"] => laws(site),
        ["keys"] => keys(site),
        ["room", name] => room(site, name),
        ["room", name, "resident"] => {
            let mut page = resident::page(site, name);
            if !site.front.read_only {
                page.body.push_str(&summon_form(name));
            }
            page
        }
        ["laws", "show"] => match query(target, "ref") {
            Some(name) => match verb(site, &[format!("law show {}", quote(&name))]) {
                Some(ending) => Page { status: 200, title: format!("Law on {name}"), stamp: Stamp::None, body: answered(&ending, &[("laws", "/laws")]) },
                None => simple(500, "Laws", "this body has no shell paths"),
            },
            None => simple(400, "Laws", "give a reference"),
        },
        ["doc", name] if !site.front.read_only => {
            let mut page = site.route(&["doc".to_owned(), name.to_string()]);
            if page.status == 200 {
                page.body.push_str(&append_form(name));
                if let Some(subject) = site.shell.as_ref().and_then(|s| s.public_subject.as_deref()) {
                    page.body.push_str(&publish_form(name, subject));
                }
            }
            page
        }
        ["board", name] if !site.front.read_only => {
            let mut page = site.route(&["board".to_owned(), name.to_string()]);
            if page.status == 200 {
                page.body.push_str(&board_forms(name));
            }
            page
        }
        ["stream", ..] => simple(404, "Not here", "not a page"),
        _ => site.route(&parts.iter().map(|s| s.to_string()).collect::<Vec<_>>()),
    }
}

/// The public front page as the operator's published document (`--front-doc`), rendered through
/// the same page path as `/doc/NAME`, so it carries the same shell and styles as every page. `None`
/// (no setting, or the document is not published to the public reader): the caller serves the
/// index. A failed read keeps its explanation. `/doc` stays the index, linked from here.
fn front_doc_page(site: &Site) -> Option<Page> {
    let name = site.shell.as_ref()?.front_doc.as_deref()?;
    if !site.names().iter().any(|n| n == name) {
        eprintln!("mini web --body (public reader): front document {name} is not among the reader's references (nothing published to the reader under that name yet); the index is shown");
        return None;
    }
    let page = site.route(&["doc".to_owned(), name.to_owned()]);
    if page.status != 200 {
        log_public_failure(&format!("front document {name}, the index is shown instead"), &page);
        return None;
    }
    Some(page)
}

/// Compose the existing signed document, activity and app views into one public entrance.
/// The published welcome is still `Site::doc`, never a second copy of its contents.
fn public_front(site: &Site) -> Page {
    public_front_with_welcome(site, front_doc_page(site))
}

fn public_front_with_welcome(site: &Site, welcome: Option<Page>) -> Page {
    let (stamp, reading) = match welcome {
        Some(page) => (page.stamp, format!("<section><h2>{}</h2>{}<p><a href=\"/doc\">Every published document →</a> · <a href=\"/receipts\">Receipts</a> · <a href=\"/registry\">The laws of the box</a> · <a href=\"/tour\">The tour</a> · <a href=\"/join\">Join</a></p></section>", escape(&page.title), page.body)),
        None => (Stamp::None, format!("<section><h2>From the community</h2><p>Explore what members have shared with the public reader.</p>{}</section>", site.index().body)),
    };
    Page { status: 200, title: "Welcome to Mini".into(), stamp, body: format!(
        "<section class=\"hero\"><p class=\"eyebrow\">A shared world, with rules you can read</p><h2>Make a little world together.</h2>\
         <p class=\"lede\">Mini brings documents, rooms, apps and AI residents into one shared workspace. Every change meets the world's rules. When a change is refused, the reason is there to read.</p>\
         <div class=\"actions\"><a class=\"button\" href=\"/join\" data-full>Join this world</a><a class=\"button secondary\" href=\"/tour\">Take the tour</a></div>\
         <p class=\"note\">You are browsing as the public reader. Explore first; join when you want to make something.</p></section>\
         <div class=\"front-grid\">{reading}{}</div>\
         <section><div class=\"section-heading\"><h2>Tools to make it yours</h2><a href=\"/apps\">Browse all apps →</a></div>\
         <p class=\"note\">Apps from the Sandstorm catalogue. Publisher claims and this box's verdict are shown separately.</p>{}</section>\
         <section><div class=\"section-heading\"><h2>Find your way around</h2><a href=\"/registry\">Read the world's laws →</a></div>\
         <ul class=\"place-list\"><li><a href=\"/room\">Gather in a room</a></li><li><a href=\"/story\">Step into a story</a></li><li><a href=\"/receipts\">Follow the receipts</a></li></ul></section>",
        operations(site), apps::catalogue(site, "", "", true)
    ) }
}

/// `/board` and `/room`: the workspace's references, each opened as that place.
fn place_index(site: &Site, place: &str) -> Page {
    let mut rows = String::new();
    for name in site.names() {
        // The shell's `room list` shows only references that name a room; every other reference
        // (an account, a document, a story cast) is not a room and is not offered as one.
        if place == "room" && crate::workspace::reference(&site.root, &name).ok().is_none_or(|r| r.get("room").and_then(Value::as_str).is_none()) {
            continue;
        }
        rows.push_str(&format!("<li><a href=\"/{place}/{n}\">{n}</a></li>\n", n = escape(&name)));
    }
    let (title, note) = match place {
        "board" => ("Boards", "See work as a board: tasks, their state and who has taken them. Open a reference below in the board layout."),
        _ => ("Rooms", "Gather around a conversation, shared documents and a resident. Open a reference below as a room to see what your grants cover."),
    };
    Page { status: 200, title: title.into(), stamp: Stamp::None, body: format!("<p>{note}</p>\n<ul class=\"place-list\">{rows}</ul>{}", if place == "room" && !site.front.read_only { room_new_form() } else { String::new() }) }
}

fn room(site: &Site, name: &str) -> Page {
    let mut page = site.route(&["room".to_owned(), name.to_owned()]);
    if page.status != 200 {
        return page;
    }
    // The room's streams as chat: the shell's own `tail`, read as this member.
    if let Some(ending) = verb(site, &[format!("tail -n 40 --in {}", quote(name))]) {
        page.body.push_str("<section class=\"chat\" data-live=\"5000\"><h2>Chat</h2>\n");
        if ending.code == 0 {
            page.body.push_str(&format!("<pre class=\"turns\">{}</pre>\n", escape(ending.text().trim())));
        } else {
            page.body.push_str(&answered(&ending, &[]));
        }
        if !site.front.read_only {
            page.body.push_str(&format!(
                "<form method=\"post\" action=\"/room/{n}/say\" class=\"row\"><div><label for=\"say-{n}\">Add to the conversation</label><input id=\"say-{n}\" type=\"text\" name=\"text\" maxlength=\"2000\" required autocomplete=\"off\"></div><button>Send</button></form>\n",
                n = escape(name)
            ));
        }
        page.body.push_str("</section>\n");
    }
    page
}

fn receipts(site: &Site) -> Page {
    let mut body = String::from(
        "<p>Every retained attempt of this workspace with its last Host outcome, as <code>history all</code> prints it. \
         Open an attempt to see the Host's receipt and refusal frame, ask again (<code>lookup</code>) or retry an undecided one (<code>retry</code>: exact, never a second write).</p>\n",
    );
    match verb(site, &["history all".to_owned()]) {
        Some(ending) if ending.code == 0 => {
            let text = ending.text();
            let mut rows = String::new();
            // Newest first: the stream reads down from the latest attempt.
            for line in text.lines().rev() {
                let id = line.split_whitespace().next().unwrap_or("");
                if id.len() > 1 && id.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-') {
                    rows.push_str(&format!("<tr><td><a href=\"/receipts/{id}\">{id}</a></td><td>{}</td></tr>\n", escape(line[id.len()..].trim())));
                }
            }
            if rows.is_empty() {
                body.push_str(&format!("<pre>{}</pre>", escape(text.trim())));
            } else {
                body.push_str(&format!("<table><thead><tr><th>attempt</th><th>outcome</th></tr></thead><tbody>{rows}</tbody></table>"));
            }
        }
        Some(ending) => body.push_str(&answered(&ending, &[])),
        None => body.push_str("<p class=note>no shell paths: receipts are shown through the shell</p>"),
    }
    body.push_str("<form method=\"get\" action=\"/receipts/lookup\" class=\"row\"><label for=\"rid\">Attempt id</label><input id=\"rid\" type=\"text\" name=\"id\" pattern=\"[A-Za-z0-9-]+\" required><button>Open</button></form>");
    Page { status: 200, title: "Receipts".into(), stamp: Stamp::None, body }
}

fn receipt(site: &Site, id: &str) -> Page {
    if workspace_id(id).is_err() {
        return simple(404, "Receipts", "not an attempt id");
    }
    let mut body = String::new();
    // `lookup` asks the Host for the retained attempt's decided outcome (a transition's class);
    // the receipt and the explanation are reads.
    for (heading, line, transition) in [("Outcome", format!("lookup {id}"), true), ("Receipt", format!("inspect receipt {id}"), false), ("Why", format!("why {id}"), false)] {
        if let Some(ending) = verb(site, &[line]) {
            body.push_str(&format!("<section><h2>{heading}</h2>{}</section>\n", outcome_of(&ending, &[], transition)));
        }
    }
    body.push_str(&anchor(&site.root.join("attempts").join(id)));
    if !site.front.read_only {
        body.push_str(&format!(
            "<p class=\"next\"><form method=\"post\" action=\"/receipts/{id}/retry\" class=\"inline\"><button class=\"quiet\">retry {id}</button></form> \
             <form method=\"post\" action=\"/receipts/{id}/lookup\" class=\"inline\"><button class=\"quiet\">lookup {id}</button></form> \
             <form method=\"post\" action=\"/receipts/{id}/publish\" class=\"inline\"><button class=\"quiet\">publish {id}</button></form></p>\n"
        ));
    }
    Page { status: 200, title: format!("Attempt {id}"), stamp: Stamp::None, body }
}

/// What the retained attempt anchors to, said without overclaiming: the exact bytes the client
/// sealed before sending (`call.bin`, by digest and length) and the Host's confirmation point
/// (`acceptedCount`, `worldRoot`, the transaction and event ids). The inclusion opening of that
/// receipt against the published world root (op 151, DEMO-EXPERIENCE A10) is L1's and is not
/// here yet: the page says so rather than implying the receipt is verifiable today.
fn anchor(attempt: &std::path::Path) -> String {
    use sha2::Digest;
    if !attempt.is_dir() {
        return String::new();
    }
    let call = std::fs::read(attempt.join("call.bin")).ok();
    let bytes = match &call {
        Some(b) => format!("<p>Exact call: <code>sha256 {:x}</code>, {} bytes, sealed before it was sent (a retry resends these bytes and no others).</p>", sha2::Sha256::digest(b), b.len()),
        None => "<p>No sealed call is retained for this attempt (it was never sent).</p>".to_owned(),
    };
    let point = match crate::workspace::retained_attempt_outcome(attempt) {
        Ok(crate::workspace::AttemptOutcome::Confirmed(v)) | Ok(crate::workspace::AttemptOutcome::Charged(v)) => {
            let s = |k: &str| v.get(k).and_then(Value::as_str).unwrap_or("?").to_owned();
            format!(
                "<p>Confirmation point: <code>acceptedCount {}</code>, <code>worldRoot {}</code> (transaction {}, event {}, {}{}).</p>\
                 <p class=\"outcome undecided\">Anchored to a point; inclusion proof pending: the opening of this receipt against the published world root (op 151) is not yet issued by the Host, so this page shows the point the Host named and does not claim a stranger can verify it offline.</p>",
                escape(&s("acceptedCount")), escape(&s("worldRoot")), escape(&s("transactionId")), escape(&s("eventId")), escape(&s("confirmation")),
                if v.get("disposition").and_then(Value::as_str) == Some("charged") { ", charged: only its price was posted" } else { "" }
            )
        }
        Ok(crate::workspace::AttemptOutcome::Refused) => "<p>Refused: the Host named no point; the refusal's clause is the receipt.</p>".to_owned(),
        Ok(crate::workspace::AttemptOutcome::Pending) => "<p>Undecided: no confirmation point yet; <code>lookup</code> or <code>retry</code> resolves it.</p>".to_owned(),
        Err(e) => format!("<p>The retained history could not be read: {}</p>", escape(&e)),
    };
    format!("<section class=\"anchor\"><h2>Anchor</h2>{bytes}{point}</section>\n")
}

fn grants(site: &Site) -> Page {
    let mut body = String::from("<p>The grants you hold, as the Host's capability view names them (capability, scope, expiry, ancestors), drawn as a tree; then what they cover, verb by verb, prepared and dry-run against the Host (<code>can --all</code>; nothing is submitted).</p>\n");
    if let Some(ending) = verb(site, &["inspect caps --json".to_owned()]) {
        match serde_json::from_str::<Value>(ending.stdout.trim()) {
            Ok(view) if ending.code == 0 => body.push_str(&format!("<section class=\"grants\"><h2>Capability tree</h2>{}</section>\n", json_tree(&view))),
            _ => body.push_str(&answered(&ending, &[])),
        }
    }
    // What the grants cover, one reference at a time: each is its own dry run (op 130 per verb),
    // so the page is whole at once and fills in as each answer lands (app.js loads `data-load`
    // sections in turn; without JavaScript each section is a link to its own page). One bare
    // `can` over every grant would outlast a browser on a used workspace.
    let names = site.names();
    body.push_str(&format!("<section><h2>What they cover</h2><p class=\"note\">{} reference(s), each judged by its own dry run as the page fills; <code>can REF</code> in the shell is the same question for one.</p>\n", names.len()));
    for name in &names {
        body.push_str(&format!(
            "<section class=\"grant\" data-load=\"/grants/judge/{0}\"><h3><code>{0}</code></h3><div class=\"fill\"><p class=\"note\"><a href=\"/grants/judge/{0}\">judge what my grants cover on {0}</a></p></div></section>\n",
            escape(name)
        ));
    }
    body.push_str("</section>\n");
    // Grains: the identities an app holds for you, and the v1 notice (members of a shared grain look
    // like one user to the app), said here as L13's receipts say it.
    if let Some(ending) = verb(site, &["apps list --json".to_owned()]) {
        if ending.code == 0 {
            if let Some(start) = ending.stdout.find('{') {
                if let Ok(value) = serde_json::from_str::<Value>(&ending.stdout[start..]) {
                    let grains = value["receipt"]["grains"].as_array().map(|g| g.len()).unwrap_or(0);
                    body.push_str(&format!(
                        "<section><h2>Grains</h2><p>{grains} grain(s) hold a route for you (<a href=\"/grain\">your grains</a>).</p>{}</section>\n",
                        value["receipt"]["identityNotice"].as_str().map(|n| format!("<p class=\"outcome undecided\">{}</p>", escape(n))).unwrap_or_default()
                    ));
                }
            }
        }
    }
    if !site.front.read_only {
        body.push_str(
            "<section><h2>Delegate</h2><p class=note>Delegate verbs on one of your references to another subject, with a cost ceiling; the proposal is submitted at once, and <code>publish</code> hands the recipient their reference.</p>\
             <form method=\"post\" action=\"/grants/delegate\" class=\"row\">\
             <div><label for=\"d-ref\">Reference</label><input id=\"d-ref\" name=\"ref\" type=\"text\" required pattern=\"[A-Za-z0-9/-]+\"></div>\
             <div><label for=\"d-to\">Recipient subject</label><input id=\"d-to\" name=\"recipient\" type=\"text\" required pattern=\"[0-9a-z-]+\"></div>\
             <div><label for=\"d-verbs\">Verbs (comma-separated)</label><input id=\"d-verbs\" name=\"verbs\" type=\"text\" required pattern=\"[a-z,-]+\" value=\"observe\"></div>\
             <div><label for=\"d-max\">Max cost</label><input id=\"d-max\" name=\"max\" type=\"text\" required pattern=\"[0-9]+\" value=\"@MAX@\"></div>\
             <button>Delegate</button></form></section>\n\
             <section><h2>Revoke</h2><form method=\"post\" action=\"/grants/revoke\" class=\"row\">\
             <div><label for=\"r-ref\">Reference</label><input id=\"r-ref\" name=\"ref\" type=\"text\" required pattern=\"[A-Za-z0-9/-]+\"></div>\
             <div><label for=\"r-to\">Recipient subject</label><input id=\"r-to\" name=\"recipient\" type=\"text\" required pattern=\"[0-9a-z-]+\"></div>\
             <button>Revoke</button></form></section>\n"
                .replace("@MAX@", PUBLIC_READ_MAX_COST.trim())
                .as_str(),
        );
    }
    Page { status: 200, title: "Grants".into(), stamp: Stamp::None, body }
}

fn laws(site: &Site) -> Page {
    let mut body = String::from(
        "<p>The law on a reference, as the Host holds it (<code>law show REF</code>); install a law with clauses (<code>law ID REF \"CLAUSE; …\"</code>). The Host first asks whether the law can ever pass.</p>\
         <form method=\"get\" action=\"/laws/show\" class=\"row\"><label for=\"l-ref\">Reference</label><input id=\"l-ref\" name=\"ref\" type=\"text\" required pattern=\"[A-Za-z0-9/-]+\"><button>Show</button></form>\n",
    );
    if !site.front.read_only {
        body.push_str(
            "<section><h2>Install a law</h2><form method=\"post\" action=\"/laws/install\">\
             <label for=\"li-ref\">Reference</label><input id=\"li-ref\" name=\"ref\" type=\"text\" required pattern=\"[A-Za-z0-9/-]+\">\
             <label for=\"li-clauses\">Clauses (semicolon-separated), or the predicate JSON</label><textarea id=\"li-clauses\" name=\"clauses\" required maxlength=\"4000\"></textarea>\
             <p><button>Install</button></p></form></section>\n",
        );
    }
    let _ = site;
    Page { status: 200, title: "Laws".into(), stamp: Stamp::None, body }
}

fn keys(site: &Site) -> Page {
    let mut body = String::from(
        "<p>Your signing key is <strong>hosted</strong>: it lives in your account's home on this box (readable by the operator, by your own account, and by no other member), and everything on this box is world-readable. \
         The browser never holds it; this session is a cookie that names your account.</p>\n",
    );
    for (heading, line) in [("Who am I", "whoami"), ("Key status", "key-status")] {
        if let Some(ending) = verb(site, &[line.to_owned()]) {
            body.push_str(&format!("<section><h2>{heading}</h2>{}</section>\n", answered(&ending, &[])));
        }
    }
    body.push_str("<p><a href=\"/sessions\">Your browser sessions</a> (list and revoke) · <a href=\"/term\">Terminal</a> for <code>rotate-key</code> and <code>adopt-next-key</code>, which take the next key's file.</p>");
    Page { status: 200, title: "Keys".into(), stamp: Stamp::None, body }
}

fn append_form(name: &str) -> String {
    format!(
        "<section><h2>Append</h2><form method=\"post\" action=\"/doc/{n}/append\">\
         <label for=\"ap-{n}\">Text to append (one proposal, submitted at once)</label><textarea id=\"ap-{n}\" name=\"text\" required maxlength=\"4096\"></textarea>\
         <p><button>Append</button> <a href=\"/doc/{n}/edit\">Edit and inspect</a></p></form></section>\n\
         <section><h2>Link</h2><form method=\"post\" action=\"/doc/{n}/link\" class=\"row\">\
         <div><label for=\"lk-{n}\">To (a reference)</label><input id=\"lk-{n}\" name=\"to\" type=\"text\" required pattern=\"[A-Za-z0-9/-]+\"></div>\
         <div><label for=\"lr-{n}\">Relation</label><input id=\"lr-{n}\" name=\"relation\" type=\"text\" pattern=\"[A-Za-z0-9-]*\" value=\"\"></div>\
         <button>Link</button></form></section>\n",
        n = escape(name)
    )
}

/// Publish: delegate `observe` on the document to the public reader's subject (then `submit` and
/// `publish`, which writes the recipient reference the helper hands over); unpublish revokes it.
fn publish_form(name: &str, subject: &str) -> String {
    format!(
        "<section><h2>Publish</h2><p class=note>Publishing delegates <code>observe</code> on <code>{n}</code> to the public reader (subject <code>{s}</code>); every visitor then reads it as the public reader does. Revoking takes it down; the page says everything on this box is world-readable anyway.</p>\
         <form method=\"post\" action=\"/doc/{n}/publish\" class=\"inline\"><button>Publish to the public reader</button></form> \
         <form method=\"post\" action=\"/doc/{n}/unpublish\" class=\"inline\"><button class=\"quiet\">Unpublish</button></form></section>\n",
        n = escape(name),
        s = escape(subject)
    )
}

/// The public reader imports what the helper handed it (`HOME/inbox/NAME.TARGET.json`): the
/// first publication of a name gets NAME; a later one of the same target replaces it (a fresh
/// grant for the same document), one of another target with another capability gets
/// NAME-CAPABILITY, so no author takes over another's page; a capability already imported is skipped. Import records a
/// hint; the signed read decides what is shown.
fn import_inbox(site: &Site) {
    let Some(shell) = site.shell.as_ref() else { return };
    let Ok(entries) = fs::read_dir(shell.home.join("inbox")) else { return };
    let Ok(exe) = std::env::current_exe() else { return };
    let held: Vec<String> = site
        .names()
        .iter()
        .filter_map(|n| workspace::reference(&site.root, n).ok())
        .filter_map(|r| r["observeCapability"].as_str().map(str::to_owned))
        .collect();
    for entry in entries.flatten() {
        let file = entry.path();
        let Some(base) = file.file_name().and_then(|f| f.to_str()).and_then(|f| f.strip_suffix(".json")) else { continue };
        let name = base.split('.').next().unwrap_or("");
        if name.is_empty() || name.len() > 64 || !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-') {
            continue;
        }
        let Some(capability) = fs::read(&file).ok().and_then(|b| serde_json::from_slice::<Value>(&b).ok()).and_then(|v| v["capability"].as_str().map(str::to_owned)) else { continue };
        if held.contains(&capability) {
            continue;
        }
        let mut chosen = name.to_owned();
        let existing = site.root.join("refs").join(format!("{chosen}.json"));
        if existing.exists() {
            // The same document published again with a new grant (the earlier one revoked, expired or
            // too narrow to cover a read): the author's newer publication replaces the hint, so the
            // name a front page or a link uses reads again. Another target keeps the old name apart.
            let target = fs::read(&file).ok().and_then(|b| serde_json::from_slice::<Value>(&b).ok()).and_then(|v| v["target"].as_str().map(str::to_owned));
            let held_target = fs::read(&existing).ok().and_then(|b| serde_json::from_slice::<Value>(&b).ok()).and_then(|v| v["target"].as_str().map(str::to_owned));
            if target.is_some() && target == held_target && fs::remove_file(&existing).is_ok() {
                // import under the same name below
            } else {
                chosen = format!("{name}-{capability}");
                if chosen.len() > 64 {
                    chosen = format!("p-{capability}");
                }
            }
        }
        let status = Command::new(&exe)
            .arg("workspace").arg("--action").arg("import").arg("--dir").arg(&site.root).arg("--name").arg(&chosen).arg("--from-ref").arg(&file)
            .env_clear().env("PATH", "/usr/bin:/bin").env("HOME", &shell.home)
            .stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::inherit())
            .status();
        // The import's own refusal is on the inherited stderr above; this line says which hint it was.
        match status {
            Ok(status) if status.success() => {}
            Ok(status) => eprintln!("mini web --body: inbox {} not imported as {chosen}: workspace import {status}", file.display()),
            Err(error) => eprintln!("mini web --body: inbox {} not imported as {chosen}: {error}", file.display()),
        }
    }
}

/// The box's own operations room: the reference `operations` in this workspace (the public reader
/// is granted it; `mini-s-box` posts the ships, drills, certifier ticks and backup receipts into it
/// as signed turns). Until it is shared, the page says so by name.
fn operations(site: &Site) -> String {
    if !site.names().iter().any(|n| n == "operations") {
        return "<section class=\"ops\"><h2>Operations room</h2><p class=note>The box's operations room (<code>operations</code>, posted into by the box's own member <code>mini-s-box</code>) is not yet shared with the public reader: nothing to show by that name.</p></section>\n".to_owned();
    }
    // The reference alone is not the room: this session reads it once it holds the room record
    // (`chat join operations INVITATION`). Without one the shell's refusal ("this session has no room
    // operations") is not news worth a red outcome on the front page and the tour: say what is missing.
    if site.shell.as_ref().is_some_and(|shell| !shell.home.join("chat").join("rooms").join("operations.json").is_file()) {
        return "<section class=\"ops\"><h2>Operations room</h2><p class=note>The box's operations room (<code>operations</code>) is shared with this workspace, but this session has not joined it: <code>chat join operations INVITATION</code> brings its signed turns here.</p></section>\n".to_owned();
    }
    match verb(site, &["tail -n 20 --in operations".to_owned()]) {
        Some(ending) if ending.code == 0 => format!(
            "<section class=\"ops chat\" data-live=\"30000\" data-live-path=\"/activity\"><p class=\"eyebrow\">From the operations room</p><h2>Life in this world</h2><p class=note>Ships, drills, checkpoints and backups, as signed turns of <code>mini-s-box</code>.</p><pre class=\"turns\">{}</pre><p><a href=\"/room/operations\">the room</a></p></section>\n",
            escape(ending.text().trim())
        ),
        Some(ending) => format!("<section class=\"ops\"><h2>Operations room</h2>{}</section>\n", answered(&ending, &[])),
        None => String::new(),
    }
}

/// `/tour`: the twelve steps of docs/DEMO-EXPERIENCE-2026-10-27.md §1 as one guided page whose
/// forms are the real forms (the derived verb forms, posted to `/tour/N`); a step's outcome
/// partial renders under it. The public reader reads the steps; a member runs them.
fn tour(site: &Site, outcome: Option<(usize, String)>) -> Page {
    let member = !site.front.read_only;
    let forms = |n: usize, specs: &[(&str, &str)]| -> String {
        if !member {
            return String::new();
        }
        specs
            .iter()
            .filter_map(|(verb, literals)| verbs::form_for(verb, literals, &format!("/tour/{n}"), &format!("<input type=\"hidden\" name=\"verb\" value=\"{}\">", escape(verb))))
            .collect()
    };
    let steps: Vec<(&str, String, String)> = vec![
        ("lands", "The world as the public reader may observe it: published documents, the laws of the box (the operation registry, the consent plans), the receipts stream, the operations room, the shutdown date, the world-readable sentence.".into(),
            format!("<p><a href=\"/\">the front page</a> · <a href=\"/registry\">the registry</a> · <a href=\"/receipts\">receipts</a></p>{}", operations(site))),
        ("joins", "A name; optionally an ssh public key, Discord, pay-to-enrol. Without an ssh key the box makes the hosted key and the door answers a one-time <em>Open your session</em> link.".into(),
            "<p><a href=\"/join\" data-full>the door</a></p>".into()),
        ("writes", "A new document, an append, a link to another document, a transclusion; after every action the outcome partial: admitted at a height, or the refusal's clause, or undecided with its exact retry. The append form carries the <em>lose this reply</em> switch: a fault in your own client (<code>submit ID --lose-reply-once</code>) that writes the exact call and never reads the answer; the Host admits once, the receipt is undecided with one link, the exact retry, which answers the same decided outcome: one append, one charge.".into(),
            if member {
                format!("{}{}{}{}",
                    forms(3, &[("doc", "doc new")]),
                    verbs::form_for("doc", "doc append", "/tour/3", "<input type=\"hidden\" name=\"verb\" value=\"doc\"><label class=\"check\"><input type=\"checkbox\" name=\"lose\" value=\"on\"> lose this reply once (a client-side fault; the Host still decides)</label>").unwrap_or_default(),
                    forms(3, &[("doc", "doc link")]),
                    forms(3, &[("doc", "doc transclude")]))
            } else { String::new() }),
        ("is refused, and reads why", "Try to edit a document you do not own: refused, with the clause of the law that refused it. <code>can</code> shows which verbs would pass; <code>why</code> explains the last refusal in the kernel's words.".into(),
            forms(4, &[("can", "can"), ("why", "why"), ("inspect", "inspect law")])),
        ("delegates, bounded", "A narrower grant on one document to another member, then its revocation; both are receipts; the other member's attempt after revocation is refused with that clause.".into(),
            forms(5, &[("delegate", "delegate"), ("revoke", "revoke"), ("renounce", "renounce")])),
        ("summons an agent", "Hermes lives in the <code>lobby</code>, the house's shared room every member joins at the door. First a bounded grant on one document to Hermes's subject (<code>delegate … --until H</code>: the grant's expiry is a height); <code>summon lobby as librarian</code> answers that it is already there (the house summoned it and pays its turns from the room's budget); ask it to read the document and post a summary: its turns land as paid, admitted writes with receipts, and every member of the lobby sees the reply; a write outside its grant is refused <code>no-grant</code> as a receipt; <code>revoke</code> ends the grant.".into(),
            if member {
                format!("{}{}", PURSE_LATER, forms(6, &[("delegate", "delegate"), ("summon", "summon"), ("ask", "ask"), ("tail", "tail"), ("hermes", "hermes status"), ("revoke", "revoke")]))
            } else { String::new() }),
        ("installs an application", "The Sandstorm store index; install any SPK; the grain opens on its own origin in a pane; its grants are Mini capabilities on the Grants page.".into(),
            format!("<p><a href=\"/apps\">the market</a> · <a href=\"/grain\">your grains</a></p>{}", forms(7, &[("apps", "apps search")]))),
        ("asks the oracle", "The veri7vn grain: a question, an answer with its evidence and the machine-checked function it rests on (the oracle appliance lands on the same grain path).".into(), String::new()),
        ("links Discord", "<code>/mini link CODE</code> in Discord with the code the door's status page shows; <code>/mini say</code> then lands as your turn and appears in the web room.".into(), String::new()),
        ("opens the terminal", "<code>mini shell</code> in the page, or over ssh with the key you gave: the same verbs, the same receipts.".into(),
            "<p><a href=\"/term\">Terminal</a></p>".into()),
        ("plays", "A story room from the built-in tale (<em>The Lamplighter's House</em>): <code>story new T --from tale</code>, <code>story seal T</code>, then invite yourself and join with the invitation the invite prints. <code>look</code> shows your scene; <code>go north</code> from the hallway is a legal move, admitted; <code>go north</code> again from the anteroom needs the key and is refused with that clause. The rule of the game is the Lean theorem <code>sealed_story_scene_monotone</code>, proved for the built-in tale's generator (the law of a table you write yourself is checked, not proved).".into(),
            forms(11, &[("story", "story new"), ("story", "story seal"), ("story", "story invite"), ("story", "story join"), ("story", "story enter"), ("look", "look"), ("go", "go"), ("take", "take"), ("act", "act"), ("narrate", "narrate")])),
        ("changes the rules", "A law on your own document that refuses even you: <code>law check</code> first says whether any write could ever pass it (nothing is installed); then install it; your next append is refused with the clause; revise the law (installs are not writes, so the law stays changeable: <code>--i-lock-myself-out</code> is a different door) and the append is admitted. Every outcome is a receipt.".into(),
            forms(12, &[("law", "law check"), ("law", "law"), ("doc", "doc append"), ("law", "law show")])),
    ];
    let mut body = String::from("<p>Fifteen minutes, from a browser, nothing installed. Every form below is the real form: the words of one shell verb, run as you, answered by the Host; its outcome lands under the step.</p>\n<ol class=\"tour\">");
    for (i, (title, text, forms_html)) in steps.iter().enumerate() {
        let n = i + 1;
        body.push_str(&format!("<li id=\"step-{n}\" class=\"step\"><h2>{n}. The stranger {title}</h2><p>{text}</p>{forms_html}"));
        if let Some((step, html)) = &outcome {
            if *step == n {
                body.push_str(&format!("<div class=\"step-outcome\">{html}</div>"));
            }
        }
        body.push_str("</li>\n");
    }
    body.push_str("</ol>");
    Page { status: 200, title: "Tour".into(), stamp: Stamp::None, body }
}

fn board_forms(name: &str) -> String {
    let n = escape(name);
    format!(
        "<section><h2>Act</h2>\
         <form method=\"post\" action=\"/board/{n}/add\" class=\"row\"><div><label for=\"ba-{n}\">Add task</label><input id=\"ba-{n}\" name=\"task\" type=\"text\" required pattern=\"[0-9]+\"></div><button>Add</button></form>\
         <form method=\"post\" action=\"/board/{n}/move\" class=\"row\"><div><label for=\"bm-{n}\">Move task</label><input id=\"bm-{n}\" name=\"task\" type=\"text\" required pattern=\"[0-9]+\"></div>\
         <div><label for=\"bf-{n}\">from</label><input id=\"bf-{n}\" name=\"from\" type=\"text\" required pattern=\"[A-Za-z0-9-]+\"></div><div><label for=\"bt-{n}\">to</label><input id=\"bt-{n}\" name=\"to\" type=\"text\" required pattern=\"[A-Za-z0-9-]+\"></div><button>Move</button></form>\
         <form method=\"post\" action=\"/board/{n}/take\" class=\"row\"><div><label for=\"bk-{n}\">Take task</label><input id=\"bk-{n}\" name=\"task\" type=\"text\" required pattern=\"[0-9]+\"></div><button>Take</button></form></section>\n"
    )
}

fn summon_form(name: &str) -> String {
    format!(
        "<section><h2>Summon a resident</h2><p class=note>The founder summons a Hermes resident into the room in a role, with a budget funded from the founder's account; in a room that already has one (the lobby), a member's summon says so, and every member asks it there.</p>\
         <form method=\"post\" action=\"/room/{n}/summon\" class=\"row\"><div><label for=\"sr-{n}\">Role</label><select id=\"sr-{n}\" name=\"role\"><option>librarian</option><option>runner</option></select></div>\
         <div><label for=\"sb-{n}\">Budget</label><input id=\"sb-{n}\" name=\"budget\" type=\"text\" pattern=\"[0-9]+\" value=\"100\"></div><button>Summon</button></form></section>\n",
        n = escape(name)
    )
}

fn room_new_form() -> String {
    "<section><h2>New room</h2><form method=\"post\" action=\"/room/new\" class=\"row\"><div><label for=\"rn\">Name</label><input id=\"rn\" name=\"name\" type=\"text\" required pattern=\"[A-Za-z0-9-]+\"></div>\
     <div><label for=\"rl\">Law</label><select id=\"rl\" name=\"law\"><option>open</option><option>realm</option></select></div><button>Create</button></form></section>\n".to_owned()
}

// ---------------------------------------------------------------- POST

fn post(site: &Site, parts: &[&str], body: &[u8]) -> Page {
    let form = match editor::form(body) {
        Ok(form) => form,
        Err(e) => return simple(400, "Form", &e),
    };
    let field = |key: &str| form.get(key).map(String::as_str).unwrap_or("").trim().to_owned();
    match parts {
        // The editor and creation forms keep their own pinned-diff path.
        ["doc", name, "edit", id] => editor::post(site, name, id, body, false),
        ["doc", name, "edit", id, "lookup"] => editor::post(site, name, id, body, true),
        ["doc", name, "edit", id, "action"] => editor::action(site, name, id, body),
        ["new-document", id] => create::post(site, id, body, "create"),
        ["new-document", id, op] => create::post(site, id, body, op),
        ["verb", name] => verbs::post(site, name, &form),
        // The line `can --any` composed, submitted as this member: `ID` becomes a fresh proposal
        // id; a leaf that proposes is followed by its `submit`. The shell parses the line as it
        // would any line typed at it.
        ["paste"] => {
            let raw = field("line");
            let id = fresh_id();
            let line = raw.split_whitespace().map(|w| if w == "ID" { id.as_str() } else { w }).collect::<Vec<_>>().join(" ");
            let proposes = crate::shell::words(&line).ok().and_then(|w| {
                let g = crate::shell_grammar::grammar(w.first()?)?;
                crate::shell_grammar::parse(g, &w).ok().map(|p| p.leaf.effect == crate::shell_grammar::Effect::Propose)
            });
            let Some(proposes) = proposes else { return simple(400, "Paste", "that line is not one the shell's grammar accepts") };
            let mut lines = vec![line];
            if proposes {
                lines.push(format!("submit {id}"));
            }
            act_as(site, "Pasted", lines, if proposes { &id } else { "" }, &[("all commands", "/verb")], true)
        }
        ["export", "consent"] => {
            // The member's own turns on their own fact: a write from the value read now (the
            // compare-and-write refuses if it changed meanwhile), or the cell's birth if absent.
            let want = if form.get("choice").map(String::as_str) == Some("cc0") { 1 } else { 0 };
            let id = fresh_id();
            let lines = match research_consent(site) {
                Some(now) if now == want => {
                    return export_page(site, Some(format!("Your world already records that choice (field 1 = {want}).")));
                }
                Some(now) => vec![format!("invoke {id} research-consent write 1 {want} {now}"), format!("submit {id}")],
                None => vec!["create research-consent declared open 1".to_owned(), format!("invoke {id} research-consent create 1 {want}"), format!("submit {id}")],
            };
            let mut page = act(site, "Research consent", lines, &id, &[("export", "/export")]);
            page.title = "Research consent".into();
            page
        }
        ["subscribe", "pay"] => super::subscribe::pay(site),
        ["subscribe", "join"] => super::subscribe::join(site),
        ["export"] => {
            // One export per member per EXPORT_COOLDOWN: it reads the whole world. Inside the
            // window the page names when the next is allowed and the last archive's digest.
            if let Some(refused) = site.shell.as_ref().and_then(|shell| export_refusal(&shell.home, now_secs())) {
                let mut page = export_page(site, Some(refused));
                page.status = 429;
                return page;
            }
            let name = format!("world-{}", now_secs());
            // The run's own words land beside the archive (NAME.log), so a failure is said on the page.
            let started = site.shell.as_ref().is_some_and(|shell| {
                let dir = shell.home.join("exports");
                fs::create_dir_all(&dir).is_ok()
                    && fs::set_permissions(&dir, std::os::unix::fs::PermissionsExt::from_mode(0o700)).is_ok()
                    && verb_detached(site, &format!("export world {name}"), &dir.join(format!("{name}.log")))
            });
            export_page(site, Some(if started { format!("Preparing <code>{name}</code>: every document is read as the Host renders it to you now. Reload this page; the download appears when it is ready.") } else { "The export could not be started (no shell paths for this body).".to_owned() }))
        }
        ["tour", step] => {
            let Some(name) = form.get("verb").map(String::as_str).filter(|v| v.bytes().all(|b| b.is_ascii_lowercase() || b == b'-')) else { return simple(400, "Tour", "which verb?") };
            let outcome = verbs::post(site, name, &form);
            tour(site, Some((step.parse().unwrap_or(0), outcome.body)))
        }
        ["apps", "install"] => apps::install(site, &form),
        ["grain", n, action] => apps::grain_action(site, n, action, &form),
        ["doc", "new"] => {
            let name = field("name");
            let room = field("room");
            let mut line = format!("doc new {} {}", quote(&name), quote(&field("law")));
            if !room.is_empty() {
                line.push_str(&format!(" --in {}", quote(&room)));
            }
            act(site, &format!("New document {name}"), vec![line], "", &[("the document", &format!("/doc/{name}")), ("documents", "/doc")])
        }
        ["doc", name, "append"] => {
            let id = fresh_id();
            let Some(file) = text_file(site, &id, &field("text")) else { return simple(400, "Append", "text must be 1..4096 bytes") };
            act(site, &format!("Append to {name}"), vec![format!("doc append {id} {} @{file}", quote(name)), format!("submit {id}")], &id, &[("the document", &format!("/doc/{name}"))])
        }
        ["doc", name, "publish"] => {
            let Some(subject) = site.shell.as_ref().and_then(|s| s.public_subject.clone()) else { return simple(400, "Publish", "this box has no public reader") };
            let id = fresh_id();
            act(site, &format!("Publish {name}"), vec![format!("delegate {id} {} {subject} observe {}", quote(name), PUBLIC_READ_MAX_COST.trim()), format!("submit {id}"), format!("publish {id}")], &id, &[("the document", &format!("/doc/{name}"))])
        }
        ["doc", name, "unpublish"] => {
            let Some(subject) = site.shell.as_ref().and_then(|s| s.public_subject.clone()) else { return simple(400, "Unpublish", "this box has no public reader") };
            let id = fresh_id();
            act(site, &format!("Unpublish {name}"), vec![format!("revoke {id} {} {subject}", quote(name)), format!("submit {id}")], &id, &[("the document", &format!("/doc/{name}"))])
        }
        ["doc", name, "link"] => {
            let id = fresh_id();
            let relation = field("relation");
            let mut line = format!("doc link {id} {} {}", quote(name), quote(&field("to")));
            if !relation.is_empty() {
                line.push_str(&format!(" {}", quote(&relation)));
            }
            act(site, &format!("Link from {name}"), vec![line, format!("submit {id}")], &id, &[("the document", &format!("/doc/{name}"))])
        }
        ["board", name, op @ ("add" | "move" | "take")] => {
            let id = fresh_id();
            let line = match *op {
                "add" => format!("board add {id} {} {}", quote(name), quote(&field("task"))),
                "move" => format!("board move {id} {} {} {} {}", quote(name), quote(&field("task")), quote(&field("from")), quote(&field("to"))),
                _ => format!("board take {id} {} {}", quote(name), quote(&field("task"))),
            };
            act(site, &format!("Board {name}: {op}"), vec![line, format!("submit {id}")], &id, &[("the board", &format!("/board/{name}"))])
        }
        ["room", "new"] => {
            let name = field("name");
            act(site, &format!("Room {name}"), vec![format!("room new {} --law {}", quote(&name), quote(&field("law")))], "", &[("rooms", "/room")])
        }
        ["room", name, "say"] => act(site, &format!("Say in {name}"), vec![format!("say --in {} {}", quote(name), quote(&field("text")))], "", &[("the room", &format!("/room/{name}"))]),
        // The founder's grant to the room's resident: the ticked tools summed to the bitmask, each
        // changed field one `tariff ROOM set FIELD N` line assembled by the verb's own grammar.
        ["room", name, "hermes-tools"] => {
            let bits: u64 = resident::TOOLS.iter().filter(|(bit, _, _)| field(&format!("tool{bit}")) == "on").map(|(bit, _, _)| bit).sum();
            let compute = field("compute");
            let compute = if compute.is_empty() { "0".to_owned() } else { compute };
            if !compute.bytes().all(|b| b.is_ascii_digit()) || compute.len() > 9 {
                return simple(400, "What Hermes may do", "the compute block is a whole number of seconds (0: the operator's default)");
            }
            let compute = compute.trim_start_matches('0').to_owned();
            let compute = if compute.is_empty() { "0".to_owned() } else { compute };
            let bits = bits.to_string();
            let mut lines = Vec::new();
            for (field_name, value, was) in [("hermes/tools", &bits, field("was-tools")), ("hermes/compute", &compute, field("was-compute"))] {
                if *value == was {
                    continue;
                }
                match verbs::assemble_named(site, "tariff", "tariff", &[("ROOM", name), ("set", "set"), (field_name, field_name), ("N", value)]) {
                    Ok((mut assembled, _, _, _)) => lines.append(&mut assembled),
                    Err(page) => return page,
                }
            }
            let back = format!("/room/{name}/resident#hermes-tools");
            if lines.is_empty() {
                return outcome_page("What Hermes may do", "answered", "Nothing changed: the room already grants exactly that.", "", &[("what Hermes may do here", &back)]);
            }
            act(site, &format!("What Hermes may do in {name}"), lines, "", &[("what Hermes may do here", &back)])
        }
        ["room", name, "summon"] => {
            let budget = field("budget");
            let mut line = format!("summon {} as {}", quote(name), quote(&field("role")));
            if !budget.is_empty() {
                line.push_str(&format!(" --budget {}", quote(&budget)));
            }
            act(site, &format!("Summon into {name}"), vec![line], "", &[("the resident", &format!("/room/{name}/resident"))])
        }
        ["receipts", id, op @ ("retry" | "lookup" | "publish")] => match workspace_id(id) {
            Ok(()) => act(site, &format!("{op} {id}"), vec![format!("{op} {id}")], id, &[("the attempt", &format!("/receipts/{id}"))]),
            Err(e) => simple(400, "Receipts", &e),
        },
        ["grants", "delegate"] => {
            let id = fresh_id();
            act(
                site,
                "Delegate",
                vec![format!("delegate {id} {} {} {} {}", quote(&field("ref")), quote(&field("recipient")), quote(&field("verbs")), quote(&field("max"))), format!("submit {id}")],
                &id,
                &[("publish it to the recipient", &format!("/receipts/{id}")), ("grants", "/grants")],
            )
        }
        ["grants", "revoke"] => {
            let id = fresh_id();
            act(site, "Revoke", vec![format!("revoke {id} {} {}", quote(&field("ref")), quote(&field("recipient"))), format!("submit {id}")], &id, &[("grants", "/grants")])
        }
        ["laws", "install"] => {
            let id = fresh_id();
            let clauses = field("clauses");
            let Some(file) = text_file(site, &id, &clauses) else { return simple(400, "Laws", "clauses must be 1..4096 bytes") };
            act(site, "Install a law", vec![format!("law {id} {} @{file}", quote(&field("ref"))), format!("submit {id}")], &id, &[("laws", "/laws")])
        }
        _ => simple(405, "Cannot act", "this address accepts reads only"),
    }
}

/// Run the lines as this member and render the ending.
pub(super) fn act(site: &Site, title: &str, lines: Vec<String>, id: &str, next: &[(&str, &str)]) -> Page {
    act_as(site, title, lines, id, next, true)
}

/// `act` for lines that are reads or local verbs: their endings are answers, not transitions.
pub(super) fn act_as(site: &Site, title: &str, lines: Vec<String>, id: &str, next: &[(&str, &str)], transition: bool) -> Page {
    let Some(ending) = verb(site, &lines) else {
        return simple(500, title, "this body has no shell paths");
    };
    let mut links: Vec<(String, String)> = next.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect();
    if !id.is_empty() {
        links.push(("the receipt".into(), format!("/receipts/{id}")));
    }
    let refs: Vec<(&str, &str)> = links.iter().map(|(a, b)| (a.as_str(), b.as_str())).collect();
    let status = match ending.code { 0 => 200, 3 => 403, 4 => 202, _ => 400 };
    // Only `can --any`'s own ending may offer its composed line as a one-click submit: any other
    // verb's stdout can carry a stranger's words (a document, a room, an app's claims), and a
    // `paste:` line planted there must stay text, never become a button that runs as this member.
    let paste = if lines.len() == 1 && asks_can_any(&lines[0]) { paste_form(&ending) } else { String::new() };
    Page { status, title: title.to_owned(), stamp: Stamp::None, body: format!("<p class=note><code>{}</code></p>\n{}", escape(&lines.join("\n")), outcome_parts(&ending, &refs, transition, &paste)) }
}

/// The line is the shell's `can … --any …` (the one verb that composes a line to paste).
fn asks_can_any(line: &str) -> bool {
    crate::shell::words(line).is_ok_and(|w| w.first().map(String::as_str) == Some("can") && w.iter().any(|x| x == "--any"))
}

/// `can --any`'s composed line (`  paste:` then the line): one button submits it as this member.
fn paste_form(ending: &Ending) -> String {
    ending.stdout.lines().skip_while(|l| l.trim() != "paste:").nth(1).map(str::trim).filter(|l| !l.is_empty()).map(|line| {
        format!("<form method=\"post\" action=\"/paste\" class=\"inline paste\"><input type=\"hidden\" name=\"line\" value=\"{}\"><button>paste and submit <code>{}</code></button></form>", escape(line), escape(line))
    }).unwrap_or_default()
}

// ---------------------------------------------------------------- the shell as the runner

pub(super) struct Ending {
    pub code: i32,
    pub stdout: String,
    pub stderr: String,
}

impl Ending {
    fn text(&self) -> String {
        let mut text = self.stdout.clone();
        if !self.stderr.trim().is_empty() {
            if !text.is_empty() && !text.ends_with('\n') {
                text.push('\n');
            }
            text.push_str(&self.stderr);
        }
        text
    }

    /// The class and the headline the one partial shows (shell.rs: 0 ok, 1 client error,
    /// 2 usage, 3 refused, 4 undecided). Admitted, refused and undecided name WORLD TRANSITIONS
    /// only; a local or read verb that returns 0 is "answered", a refused read "read refused".
    fn class(&self, transition: bool) -> (&'static str, String) {
        // Script mode echoes `mini> LINE` before each line, and the client may print notices
        // (`workspace continuity: legacy; ...`) before the ending; the ending is the first
        // `refused:`/`undecided:`/`error:`/`usage:` line, else the first line that is not an echo.
        let lines = || self.stderr.lines().filter(|l| !l.trim().is_empty() && !l.starts_with("mini> "));
        let first = lines()
            .find(|l| ["refused: ", "undecided: ", "error: ", "usage: "].iter().any(|p| l.starts_with(p)))
            .or_else(|| lines().next())
            .unwrap_or("")
            .to_owned();
        match (self.code, transition) {
            (0, true) => ("admitted", "Admitted".into()),
            (0, false) => ("answered", "Answered".into()),
            (3, true) => ("refused", if first.is_empty() { "Refused".into() } else { first }),
            (3, false) => ("refused", if first.is_empty() { "Read refused".into() } else { format!("read {first}") }),
            (4, _) => ("undecided", if first.is_empty() { "Undecided: the attempt is retained".into() } else { first }),
            (2, _) => ("error", if first.is_empty() { "Usage".into() } else { first }),
            _ => ("error", if first.is_empty() { "The client could not complete this".into() } else { first }),
        }
    }
}

/// Plan one line as this member without running it (`mini shell --line L --plan`): the shell's
/// parser and plan builder, no Host.
pub(super) fn plan_line(site: &Site, line: &str) -> Option<Ending> {
    let shell = site.shell.as_ref()?;
    let exe = std::env::current_exe().ok()?;
    if line.bytes().any(|b| b.is_ascii_control()) {
        return Some(Ending { code: 2, stdout: String::new(), stderr: "usage: a form field contains a control character\n".into() });
    }
    let mut command = Command::new(exe);
    command.arg("shell");
    if let Some(socket) = super::super::SOCKET.get() {
        command.arg("--socket").arg(socket);
    }
    let output = command
        .arg("--workspace").arg(&site.root).arg("--home").arg(&shell.home).arg("--host").arg(&shell.host).arg("--config").arg(&shell.config)
        .arg("--line").arg(line).arg("--plan")
        .env_clear().env("PATH", "/usr/bin:/bin").env("HOME", &shell.home)
        .stdin(Stdio::null()).output().ok()?;
    Some(Ending { code: output.status.code().unwrap_or(1), stdout: String::from_utf8_lossy(&output.stdout).into_owned(), stderr: String::from_utf8_lossy(&output.stderr).into_owned() })
}

/// From 10 November 2026 (UTC) the member's front page points at the export.
const EXPORT_NOTICE_FROM: u64 = 1_794_268_800;

fn now_secs() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

/// The member's research-consent fact: field 1 of their `research-consent` cell (1 = CC0, 0 =
/// none), by a signed read; None when the cell is not in this workspace or not readable.
fn research_consent(site: &Site) -> Option<i128> {
    let reference = site.reference("research-consent").ok()?;
    let (view, _, _) = site.read(&reference, "resource").ok()?;
    view["cell"]["entries"].as_array()?.iter().find(|e| e["key"]["field"] == "1")?["value"].as_str()?.parse().ok()
}

/// The last archive's name and sha256 (`mini export-world` writes NAME.sha256 beside the archive
/// and it is kept after the download): shown while the next export waits out its cooldown.
fn last_digest(dir: &std::path::Path) -> Option<(String, String)> {
    let mut sums: Vec<(std::time::SystemTime, String, String)> = fs::read_dir(dir).ok()?.flatten().filter_map(|e| {
        let name = e.file_name().to_string_lossy().strip_suffix(".sha256")?.to_owned();
        let at = e.metadata().and_then(|m| m.modified()).ok()?;
        Some((at, name, fs::read_to_string(e.path()).ok()?.trim().to_owned()))
    }).collect();
    sums.sort();
    sums.pop().map(|(_, name, sum)| (name, sum))
}

/// Why a new export may not start now (the shared rule, `world_export::may_export`, the shell's
/// own words), with the last archive's digest; None when it may.
fn export_refusal(home: &std::path::Path, now: u64) -> Option<String> {
    let why = crate::world_export::may_export(home, now).err()?;
    let digest = match last_digest(&home.join("exports")) {
        Some((name, sum)) => format!(" Your last archive, <code>{}</code>, has sha256 <code>{}</code>.", escape(&name), escape(&sum)),
        None => String::new(),
    };
    Some(format!("{}{digest}", escape(why.strip_prefix("export world: ").unwrap_or(&why))))
}

/// A finished export's file under HOME/exports, by its name (letters, digits, '-').
fn export_file(site: &Site, name: &str) -> Option<PathBuf> {
    let shell = site.shell.as_ref()?;
    (!name.is_empty() && name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')).then(|| shell.home.join("exports").join(name))
}

/// `/export`: what the archive holds, the exports ready to download (each a POST that streams the
/// file and then deletes it: no copy stays on the box), those still being prepared, and the button.
fn export_page(site: &Site, said: Option<String>) -> Page {
    let mut body = String::from(
        "<p>One <code>.tar</code> of your world, made by your own <code>mini</code> (<code>export world</code>, reads only): every reference you hold; each document as the Host renders it to you now, \
         as text and as its signed view; every retained attempt with its decided standing (admitted, refused, charged, or undecided with its exact <code>retry</code>); your room state; your public key and the custody statement; \
         and <code>manifest.json</code> with the world root and height of the last read and a sha256 per file. Your secret key is not in it.</p>\n",
    );
    if let Some(said) = said {
        body.push_str(&format!("<p class=\"note\">{said}</p>\n"));
    }
    body.push_str(&format!("<section><h2>What is kept</h2><p class=\"policy\">{}</p>", escape(super::subscribe::RETENTION.trim_end())));
    if let Some(waiting) = site.shell.as_ref().and_then(|shell| export_refusal(&shell.home, now_secs())) {
        body.push_str(&format!("<p class=\"note\">{waiting}</p>"));
    }
    let current = research_consent(site);
    let shown = match current {
        Some(1) => "contributed for research (CC0)".to_owned(),
        Some(0) => "not contributed".to_owned(),
        Some(other) => format!("an unknown value ({other})"),
        None => "not recorded in your world".to_owned(),
    };
    body.push_str(&format!(
        "<p>Your choice, as your world records it (<code>research-consent</code>, field 1): <strong>{shown}</strong>.</p>\
         <form method=\"post\" action=\"/export/consent\"><label><input type=\"checkbox\" name=\"choice\" value=\"cc0\"{}> contribute my data for research (CC0; kept private until reviewed)</label> <button>Record my choice</button></form></section>\n",
        if current == Some(1) { " checked" } else { "" }
    ));
    let mut ready = Vec::new();
    let mut preparing = Vec::new();
    let mut failed = Vec::new();
    if let Some(dir) = site.shell.as_ref().map(|s| s.home.join("exports")) {
        for entry in fs::read_dir(dir).into_iter().flatten().flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            if let Some(base) = name.strip_suffix(".log") {
                // A run whose archive is neither ready nor in progress ended without one: say why.
                let dir = entry.path().with_file_name("");
                if !dir.join(base).exists() && !dir.join(format!("{base}.part")).exists() {
                    let said = fs::read_to_string(entry.path()).unwrap_or_default();
                    let why = said.lines().rev().find(|l| l.contains("error") || l.contains("refused") || l.contains("usage")).unwrap_or("");
                    if !why.is_empty() {
                        failed.push((base.to_owned(), why.to_owned()));
                    } else {
                        preparing.push(base.to_owned());
                    }
                }
                continue;
            }
            match name.strip_suffix(".part") {
                Some(_) => {}
                None if export_file(site, &name).is_some() => ready.push((name, entry.metadata().map(|m| m.len()).unwrap_or(0))),
                None => {}
            }
        }
    }
    ready.sort();
    preparing.sort();
    for (name, bytes) in &ready {
        body.push_str(&format!(
            "<form method=\"post\" action=\"/export/{n}/download\" class=\"row\"><p><code>{n}</code>, {bytes} bytes</p><button>Download</button></form>\n",
            n = escape(name)
        ));
    }
    for name in &preparing {
        body.push_str(&format!("<p class=\"note\"><code>{}</code> is being prepared.</p>\n", escape(name)));
    }
    for (name, why) in &failed {
        body.push_str(&format!("<p class=\"note\"><code>{}</code> ended without an archive: <code>{}</code></p>\n", escape(name), escape(why)));
    }
    body.push_str("<form method=\"post\" action=\"/export\"><button>Export my world</button></form>\n");
    Page { status: 200, title: "Export my world".into(), stamp: Stamp::None, body }
}

/// Stream a finished export as an attachment, then delete it: the archive leaves the box with
/// the member, and nothing of it stays behind.
fn export_download(stream: &mut UnixStream, site: &Site, name: &str) -> Result<()> {
    let Some(path) = export_file(site, name).filter(|p| p.is_file()) else {
        return answer(stream, &simple(404, "Export", "no finished export by that name"), site);
    };
    let mut file = fs::File::open(&path).map_err(|e| e.to_string())?;
    let length = file.metadata().map_err(|e| e.to_string())?.len();
    let subject: String = site.subject.chars().filter(char::is_ascii_digit).collect();
    let head = format!(
        "HTTP/1.1 200 OK\r\nContent-Type: application/x-tar\r\nContent-Disposition: attachment; filename=\"mini-{subject}-{name}.tar\"\r\nContent-Length: {length}\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n"
    );
    stream.set_write_timeout(Some(Duration::from_secs(60))).map_err(|e| e.to_string())?;
    stream.write_all(head.as_bytes()).map_err(|e| e.to_string())?;
    let sent = std::io::copy(&mut file, stream).map_err(|e| e.to_string())?;
    if sent == length {
        let _ = fs::remove_file(&path);
        let _ = fs::remove_file(path.with_file_name(format!("{name}.log")));
    }
    Ok(())
}

/// `mini shell` as this member, in script mode, in its own process group: a read stopped at the
/// deadline is stopped whole, the client the shell ran for it included (a killed shell alone left
/// `mini workspace --action can` judging on, ahead of the member's next request).
fn shell_command(site: &Site, exe: &std::path::Path, shell: &Shell) -> Command {
    let mut command = Command::new(exe);
    command.arg("shell");
    // The deployment's socket, as the ssh wrapper passes it; a workspace that pins one takes it from the pin.
    if let Some(socket) = super::super::SOCKET.get() {
        command.arg("--socket").arg(socket);
    }
    command
        .arg("--workspace").arg(&site.root)
        .arg("--home").arg(&shell.home)
        .arg("--host").arg(&shell.host)
        .arg("--config").arg(&shell.config)
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("HOME", &shell.home);
    std::os::unix::process::CommandExt::process_group(&mut command, 0);
    command
}

/// Run one shell line as this member in the background, to its end (a thread reaps it): the
/// export, which reads every document and may take longer than one request.
fn verb_detached(site: &Site, line: &str, log: &std::path::Path) -> bool {
    let (Some(shell), Ok(exe)) = (site.shell.as_ref(), std::env::current_exe()) else { return false };
    let Ok(log) = fs::OpenOptions::new().write(true).create_new(true).open(log) else { return false };
    let Ok(log2) = log.try_clone() else { return false };
    let mut command = shell_command(site, &exe, shell);
    command.stdin(Stdio::piped()).stdout(Stdio::from(log)).stderr(Stdio::from(log2));
    let Ok(mut child) = command.spawn() else { return false };
    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(format!("{line}\n").as_bytes());
    }
    std::thread::spawn(move || {
        let _ = child.wait();
    });
    true
}

fn captured_ending(code: i32, stdout: Vec<u8>, stderr: Vec<u8>, lines: &[String]) -> Ending {
    let stdout = if code == 0 && structured_answer(lines) {
        match super::capture::structured(stdout) {
            Ok(value) => value,
            Err(reason) => return Ending { code: 1, stdout: String::new(), stderr: reason.into() },
        }
    } else { super::capture::text(stdout) };
    Ending { code, stdout, stderr: super::capture::text(stderr) }
}

/// Run shell lines as this member: `mini shell` in script mode (one line per form action, or the
/// proposal and its `submit`), the same binary and subcommand the ssh login runs.
pub(super) fn verb(site: &Site, lines: &[String]) -> Option<Ending> {
    let shell = site.shell.as_ref()?;
    #[cfg(test)]
    if let Some(ending) = redteam::FAKE_SHELL.with(|fake| fake.borrow().as_ref().map(|answer| answer(lines))) {
        return Some(captured_ending(ending.code, ending.stdout.into_bytes(), ending.stderr.into_bytes(), lines));
    }
    let exe = std::env::current_exe().ok()?;
    let script = lines.iter().map(|l| format!("{l}\n")).collect::<String>();
    if script.bytes().any(|b| b.is_ascii_control() && b != b'\n') {
        return Some(Ending { code: 2, stdout: String::new(), stderr: "usage: a form field contains a control character\n".into() });
    }
    let mut command = shell_command(site, &exe, shell);
    command.stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = command.spawn().ok()?;
    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(script.as_bytes());
    }
    let out = child.stdout.take()?;
    let err = child.stderr.take()?;
    // Both pipes are drained on their own threads into shared buffers: the deadline below can then
    // fire while the shell runs, and a page can carry what was printed so far.
    let drain = |mut pipe: Box<dyn Read + Send>| {
        let buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let sink = buf.clone();
        let handle = std::thread::spawn(move || {
            let mut chunk = [0u8; 8192];
            while let Ok(n) = pipe.read(&mut chunk) {
                if n == 0 { break; }
                if let Ok(mut b) = sink.lock() {
                    // Retain one overflow byte, then keep draining without growing memory.
                    let keep = n.min((super::capture::MAX_CAPTURE + 1).saturating_sub(b.len()));
                    b.extend_from_slice(&chunk[..keep]);
                }
            }
        });
        (buf, handle)
    };
    let (out_buf, out_thread) = drain(Box::new(out));
    let (err_buf, err_thread) = drain(Box::new(err));
    let snapshot = |b: &std::sync::Arc<std::sync::Mutex<Vec<u8>>>| b.lock().map(|v| v.clone()).unwrap_or_default();
    // Under the gateway's two minutes, so a run that cannot finish still ends as a page the
    // member can read, never as the gateway's 504.
    let deadline = Instant::now() + Duration::from_secs(100);
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break Some(status),
            Ok(None) if Instant::now() < deadline => std::thread::sleep(Duration::from_millis(25)),
            _ => break None,
        }
    };
    let cap = super::capture::text;
    if let Some(status) = status {
        let _ = out_thread.join();
        let _ = err_thread.join();
        return Some(captured_ending(status.code().unwrap_or(1), snapshot(&out_buf), snapshot(&err_buf), lines));
    }
    if !only_answers(lines) {
        // A line that may move the world is never cut short: the shell keeps running to its
        // decision (a thread reaps it), and the page says undecided, with where the outcome lands.
        std::thread::spawn(move || {
            let _ = child.wait();
            let _ = out_thread.join();
            let _ = err_thread.join();
        });
        let mut stderr = cap(snapshot(&err_buf));
        stderr.push_str("undecided: still deciding after 100 s; the shell keeps running to its decision, which lands under Receipts (or `lookup ID` / `retry ID` for this attempt)\n");
        return Some(Ending { code: 255, stdout: cap(snapshot(&out_buf)), stderr });
    }
    // Reads and local verbs are stopped at the deadline: nothing they do can be left half-done.
    // The group is the child's own (process_group(0) above), so its id is the child's pid.
    if let Ok(pgid) = i32::try_from(child.id()) {
        unsafe { libc::kill(-pgid, libc::SIGKILL) };
    }
    let _ = child.kill();
    let _ = child.wait();
    let _ = out_thread.join();
    let _ = err_thread.join();
    let stdout = cap(snapshot(&out_buf));
    // A bare `can` judges every reference held, printing each as it is decided: the notice counts them.
    let first = lines.first().map(String::as_str).unwrap_or("");
    let notice = if first == "can" || first == "can --all" {
        let judged = stdout.lines().filter(|l| !l.is_empty() && !l.starts_with(' ') && !l.starts_with("mini> ")).count();
        format!("error: {judged} of {} grants judged within 100 s; narrow with `can REF` (the Grants page judges them one at a time)\n", site.names().len())
    } else {
        "error: the read did not finish within 100 s; what it printed stands above\n".to_owned()
    };
    Some(Ending { code: 1, stdout, stderr: notice })
}

/// Only a grammar-declared JSON answer uses the structured capture. Transition
/// outcomes and unfinished requests retain their existing transcript/uncertainty path.
fn structured_answer(lines: &[String]) -> bool {
    use crate::shell_grammar::{grammar, parse, parse_line};
    if lines.len() != 1 || !only_answers(lines) { return false; }
    let Ok(words) = crate::shell::words(&lines[0]) else { return false; };
    let Some(g) = words.first().and_then(|w| grammar(w)) else { return false; };
    parse(g, &words).or_else(|_| parse_line(g, &lines[0])).is_ok_and(|p| p.flag("--json").is_some())
}

/// Whether every line is a read or a local verb by its grammar leaf (stopping one cannot leave the
/// world half-moved). A line the grammar cannot place counts as one that may move the world.
fn only_answers(lines: &[String]) -> bool {
    use crate::shell_grammar::{grammar, parse, parse_line, Effect};
    lines.iter().all(|line| {
        let Ok(words) = crate::shell::words(line) else { return false };
        let Some(g) = words.first().and_then(|w| grammar(w)) else { return false };
        let Ok(p) = parse(g, &words).or_else(|_| parse_line(g, line)) else { return false };
        matches!(p.leaf.effect, Effect::Read | Effect::Local)
    })
}

/// A world transition's outcome (admitted / refused / undecided).
pub(super) fn outcome_html(ending: &Ending, next: &[(&str, &str)]) -> String {
    outcome(ending, next)
}

/// A read's or a local verb's answer (answered / read refused / undecided).
pub(super) fn answer_html(ending: &Ending, next: &[(&str, &str)]) -> String {
    outcome_of(ending, next, false)
}

pub(super) fn json_tree_html(v: &Value) -> String {
    json_tree(v)
}

/// The one outcome partial (the gateway's CSS: `.outcome.admitted|refused|undecided|answered|error`).
fn outcome(ending: &Ending, next: &[(&str, &str)]) -> String {
    outcome_of(ending, next, true)
}

fn answered(ending: &Ending, next: &[(&str, &str)]) -> String {
    outcome_of(ending, next, false)
}

pub(super) fn outcome_of(ending: &Ending, next: &[(&str, &str)], transition: bool) -> String {
    outcome_parts(ending, next, transition, "")
}

fn outcome_parts(ending: &Ending, next: &[(&str, &str)], transition: bool, paste: &str) -> String {
    let (class, headline) = ending.class(transition);
    let mut links = String::new();
    for (label, href) in next {
        links.push_str(&format!("<a href=\"{}\">{}</a> ", url(href), escape(label)));
    }
    if class == "undecided" {
        if let Some(id) = ending.stderr.split("lookup ").nth(1).and_then(|r| r.split(|c: char| !(c.is_ascii_alphanumeric() || c == '-')).next()).filter(|s| !s.is_empty()) {
            links.push_str(&format!("<a href=\"/receipts/{id}\">the retained attempt {id}</a> "));
        }
    }
    if matches!(class, "refused" | "error" | "undecided") {
        links.push_str(&report_link(&headline, next));
    }
    let detail = ending.text();
    // A refusal by a name the table explains says what it means, inside the same partial.
    let explained: String = if matches!(class, "refused" | "error") {
        refusals_in(&detail).iter().map(|(name, meaning, _)| format!("<p class=\"note\" data-refusal=\"{}\">{}</p>", escape(name), escape(meaning))).collect()
    } else {
        String::new()
    };
    format!(
        "<div class=\"outcome {class}\" role=\"status\" aria-live=\"polite\" aria-atomic=\"true\"><p class=\"headline\">{}</p>{}{explained}{}{}</div>\n",
        headline_html(&headline),
        if detail.trim().is_empty() { String::new() } else { format!("<pre>{}</pre>", escape(detail.trim())) },
        paste,
        if links.is_empty() { String::new() } else { format!("<p class=\"next\">{links}</p>") }
    )
}

/// Where `report_link` puts the page the person was on; the dispatcher, which holds the request,
/// fills it in (`handle`), so no outcome partial has to know its own address.
const PAGE_MARK: &str = "@PAGE@";

/// Percent-encode a query value: only the unreserved characters pass.
pub(super) fn pct(text: &str) -> String {
    text.bytes().map(|b| if b.is_ascii_alphanumeric() || b"-._~".contains(&b) { (b as char).to_string() } else { format!("%{b:02X}") }).collect()
}

/// "Report a problem" from an outcome that went wrong: the derived `feedback` form, prefilled
/// with the clause the Host named (the headline) and the attempt the page links as its receipt.
fn report_link(headline: &str, next: &[(&str, &str)]) -> String {
    let clause: String = headline.chars().take(400).collect();
    let mut query = format!("clause={}&page={PAGE_MARK}", pct(&clause));
    if let Some(id) = next.iter().find_map(|(_, href)| href.strip_prefix("/receipts/")).filter(|id| workspace_id(id).is_ok()) {
        query.push_str(&format!("&from={}", pct(id)));
    }
    format!("<a class=\"report\" href=\"/verb/feedback?{}\">Report a problem</a> ", escape(&query))
}

/// Refusals a member meets by name whose name alone does not say what happened or who can change
/// it: the name, what it means, and (with the room it happened in) where the fix is. One table, so
/// an outcome partial and a resident's reply explain a name the same way.
pub(super) const EXPLAINED: &[(&str, &str, Option<&str>)] = &[
    ("oracle-not-granted", "Hermes may not ask the Oracle in this room: the room's hermes/tools field lacks bit 8. Only the room's founder grants it, under what Hermes may do here.", Some("/room/{room}/resident#hermes-tools")),
    ("oracle-not-configured", "This box's operator has bound no Oracle route for this Hermes, so no room grant reaches the Oracle.", None),
    ("typed-apps-not-granted", "Hermes may not use the hosted apps' typed tools in this room: the room's hermes/tools field lacks bit 16. Only the room's founder grants it, under what Hermes may do here.", Some("/room/{room}/resident#hermes-tools")),
    ("typed-apps-not-configured", "This box's operator has attached no hosted app to this Hermes, so no room grant reaches an app.", None),
    ("await-not-in-room", "Hermes answers only an await a member announced in this room (a say of await OBJECT TRANSACTION).", None),
    ("notDecider", "Only the slot's decider may answer it; the kernel refused an answer signed by anyone else (bend await names the decider).", None),
    ("member-day-ceiling", "Your share of the house Hermes's model calls for today is spent; it refills when the day turns.", None),
    ("member-total-ceiling", "Your share of the house Hermes's model calls until the plan's weekly reset is spent.", None),
];

/// The named refusals `text` carries, in table order.
pub(super) fn refusals_in(text: &str) -> Vec<&'static (&'static str, &'static str, Option<&'static str>)> {
    EXPLAINED
        .iter()
        .filter(|(name, _, _)| {
            text.match_indices(name).any(|(at, _)| {
                let before = text[..at].chars().next_back();
                let after = text[at + name.len()..].chars().next();
                let word = |c: Option<char>| c.is_some_and(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_');
                !word(before) && !word(after)
            })
        })
        .collect()
}

/// A named refusal said whole: the name as the clause, what it means, the fix when the room is
/// known (under `base`, the face's link prefix).
pub(super) fn explained_refusal(name: &str, meaning: &str, fix: Option<&str>, room: Option<&str>, base: &str) -> String {
    let fix = match (fix, room) {
        (Some(href), Some(room)) => format!("<p class=\"next\"><a href=\"{}\">where this is granted</a></p>", url(&format!("{base}{}", href.replace("{room}", room)))),
        _ => String::new(),
    };
    format!("<div class=\"outcome refused\" data-refusal=\"{0}\"><p class=\"headline\">refused: <mark class=\"clause\">{0}</mark></p><p>{1}</p>{fix}</div>", escape(name), escape(meaning))
}

/// A refusal is the clause, highlighted: `refused: law-denied: field 2 monotone (before 2, after 1)`
/// shows its kind and marks the clause the Host named.
fn headline_html(headline: &str) -> String {
    if let Some(rest) = headline.strip_prefix("refused: ") {
        if let Some((kind, clause)) = rest.split_once(": ") {
            return format!("refused: <span class=\"reason\">{}</span>: <mark class=\"clause\">{}</mark>", escape(kind), escape(clause));
        }
        return format!("refused: <mark class=\"clause\">{}</mark>", escape(rest));
    }
    escape(headline)
}

/// A JSON view drawn as a tree (the grants: capability, scope, expiry, ancestors as the Host's
/// `cap-tree` view names them), without a hand-written schema.
fn json_tree(v: &Value) -> String {
    match v {
        Value::Object(map) => {
            let mut out = String::from("<ul class=\"tree\">");
            for (k, v) in map {
                out.push_str(&format!("<li><span class=\"key\">{}</span> {}</li>", escape(k), json_tree(v)));
            }
            out + "</ul>"
        }
        Value::Array(items) => {
            let mut out = String::from("<ol class=\"tree\">");
            for v in items {
                out.push_str(&format!("<li>{}</li>", json_tree(v)));
            }
            out + "</ol>"
        }
        Value::String(s) if s.len() > 40 && s.bytes().all(|b| b.is_ascii_hexdigit()) => format!("<code class=\"id\" title=\"{}\">{}…</code>", escape(s), escape(&s[..16])),
        Value::String(s) => format!("<span class=\"val\">{}</span>", escape(s)),
        other => format!("<span class=\"val\">{}</span>", escape(&other.to_string())),
    }
}

/// The member's purse as a meter (`credit`): the balance a summon's budget is funded from and
/// that a resident's paid turns drain; on the purse page and in the tour's agent step.
/// The tour's purse meter, filled in after the page by app.js (`data-load`): the tour itself runs
/// no shell, so a form's answer is never held behind a Host read; without JS it is a link.
const PURSE_LATER: &str = "<section data-load=\"/purse/meter\"><div class=\"fill\"><p class=\"note\"><a href=\"/purse\">your purse, as a meter</a></p></div></section>\n";

fn purse_meter(site: &Site, live: bool) -> String {
    match verb(site, &["credit".to_owned()]) {
        Some(ending) if ending.code == 0 => {
            let line = ending.stdout.lines().find(|l| l.starts_with("credit ")).unwrap_or("").to_owned();
            let balance: u64 = line.split_whitespace().nth(1).and_then(|n| n.parse().ok()).unwrap_or(0);
            let scale = balance.max(1000);
            format!(
                "<section class=\"purse\"{}><p class=\"big\"><span class=\"n\">{balance}</span> credits</p>\
                 <meter min=\"0\" max=\"{scale}\" low=\"{}\" value=\"{balance}\" aria-label=\"Purse balance: {balance} credits\">{balance}</meter>\
                 <p class=\"note\">{}</p></section>\n",
                if live { " data-live=\"15000\"" } else { "" },
                scale / 10,
                escape(&line)
            )
        }
        Some(ending) => answered(&ending, &[]),
        None => "<p class=note>no shell paths</p>".to_owned(),
    }
}

/// `/purse`: the member's account as a meter (`credit`), then `pay status`.
fn purse(site: &Site) -> Page {
    let mut body = purse_meter(site, true);
    if let Some(ending) = verb(site, &["pay status".to_owned()]) {
        body.push_str(&format!("<section><h2>Pay</h2>{}</section>", answered(&ending, &[("pay", "/verb/pay"), ("topup", "/verb/topup"), ("tariff", "/verb/tariff")])));
    }
    Page { status: 200, title: "Purse".into(), stamp: Stamp::None, body }
}

fn outcome_page(title: &str, class: &str, headline: &str, detail: &str, next: &[(&str, &str)]) -> Page {
    let mut links = String::new();
    for (label, href) in next {
        links.push_str(&format!("<a href=\"{}\">{}</a> ", url(href), escape(label)));
    }
    Page {
        status: if class == "refused" { 403 } else { 200 },
        title: title.to_owned(),
        stamp: Stamp::None,
        body: format!("<div class=\"outcome {class}\" role=\"status\" aria-live=\"polite\" aria-atomic=\"true\"><p class=\"headline\">{}</p><pre>{}</pre>{}</div>\n", escape(headline), escape(detail), if links.is_empty() { String::new() } else { format!("<p class=\"next\">{links}</p>") }),
    }
}

/// One query value of the request target, form-decoded.
pub(super) fn query(target: &str, key: &str) -> Option<String> {
    let query = target.split_once('?')?.1.split('#').next()?;
    let pairs = editor::form(query.as_bytes()).ok()?;
    pairs.get(key).map(|v| v.trim().to_owned()).filter(|v| !v.is_empty())
}

/// A fresh proposal id: `w-` and 12 hex digits (the shell's `workspace_name` rule).
pub(super) fn fresh_id() -> String {
    format!("w-{}", crate::fsio::random::<6>().map(|b| hex(&b)).unwrap_or_else(|_| "000000000000".into()))
}

fn workspace_id(id: &str) -> std::result::Result<(), String> {
    if id.is_empty() || id.len() > 64 || !id.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-') {
        return Err("an attempt id is 1..64 letters, digits or hyphens".into());
    }
    Ok(())
}

/// TEXT arguments go through `@FILE` in HOME/requests, so a form's text can hold spaces, quotes
/// and newlines without touching the line syntax.
pub(super) fn text_file(site: &Site, id: &str, text: &str) -> Option<String> {
    if text.is_empty() || text.len() > 4096 {
        return None;
    }
    let shell = site.shell.as_ref()?;
    let dir = shell.home.join("requests");
    crate::fsio::ensure_private_dir(&dir).ok()?;
    let file = format!("web-{id}.txt");
    fs::write(dir.join(&file), text).ok()?;
    Some(file)
}

/// One word of the shell's line syntax (`shell::words`): bare when every byte is plain, else
/// double-quoted with `\` and `"` escaped.
pub(super) fn quote(word: &str) -> String {
    if !word.is_empty() && word.bytes().all(|b| b.is_ascii_alphanumeric() || b"-_./:@,=+".contains(&b)) {
        return word.to_owned();
    }
    let mut out = String::from("\"");
    for c in word.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
#[path = "body/redteam.rs"]
mod redteam;
#[cfg(test)]
#[path = "body/design_preview.rs"]
mod design_preview;

#[cfg(test)]
mod tests {
    #[test]
    fn a_second_export_inside_the_window_is_refused_with_the_time_named() {
        let home = std::env::temp_dir().join(format!("mini-export-cooldown-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&home);
        std::fs::create_dir_all(&home).unwrap();
        let t = 1_794_268_800;
        assert!(super::export_refusal(&home, t).is_none(), "the first export may start");
        drop(crate::world_export::claim_export(&home, t).unwrap());
        std::fs::write(home.join("exports/world-1.sha256"), "ab".repeat(32)).unwrap();
        let refused = super::export_refusal(&home, t + 60).expect("inside the window");
        assert!(refused.contains("the last began 2026-11-10 00:00 UTC, the next may begin from 2026-11-10 00:10 UTC"), "{refused}");
        assert!(refused.contains(&"ab".repeat(32)), "the last archive's digest is shown");
        assert!(super::export_refusal(&home, t + 600).is_none(), "after the window a new export may start");
        let held = crate::world_export::claim_export(&home, t + 600).unwrap();
        assert!(super::export_refusal(&home, t + 601).unwrap().contains("already running"), "a second export while one runs");
        drop(held);
        let _ = std::fs::remove_dir_all(&home);
    }

    #[test]
    fn only_reads_and_local_lines_may_be_stopped_at_the_deadline() {
        let l = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        assert!(super::only_answers(&l(&["can"])));
        assert!(super::only_answers(&l(&["whoami", "help"])));
        assert!(!super::only_answers(&l(&["story new t --from tale"])));
        assert!(!super::only_answers(&l(&["can", "submit p1"])));
        assert!(!super::only_answers(&l(&["no-such-verb x"])));
    }

    use super::*;

    #[test]
    fn quoting_round_trips_through_the_shell_word_syntax() {
        for word in ["plain", "lab/index", "has space", "a \"quote\"", "back\\slash", "", "{json: no}", "it's"] {
            let line = format!("say {}", quote(word));
            let words = crate::shell::words(&line).unwrap();
            assert_eq!(words, vec!["say".to_owned(), word.to_owned()], "{line}");
        }
    }

    /// The one outcome partial is a live region for every class: the line a form post
    /// produces (admitted, refused with its clause, undecided with its retry) must reach
    /// assistive tech, and the word — never the colour alone — carries the outcome.
    #[test]
    fn web_outcome_partial_is_a_live_region() {
        for (code, transition, class, word) in [
            (0, true, "admitted", "Admitted"),
            (0, false, "answered", "Answered"),
            (3, true, "refused", "refused"),
            (4, true, "undecided", "undecided"),
            (2, false, "error", "Usage"),
        ] {
            let ending = Ending { code, stdout: "done\n".into(), stderr: String::new() };
            let html = outcome_of(&ending, &[("next", "/x")], transition);
            assert!(
                html.contains(&format!("class=\"outcome {class}\" role=\"status\"")) && html.contains("aria-live=\"polite\"") && html.contains("aria-atomic=\"true\""),
                "{class}: {html}"
            );
            assert!(html.contains(word), "{class} carries its word: {html}");
        }
        // The partial the gateway renders for the anonymous POST refusal, same shape.
        let page = outcome_page("Refused", "refused", "This body is the public reader", ANONYMOUS, &[]);
        assert!(page.body.contains("role=\"status\"") && page.body.contains("aria-live=\"polite\""));
        // A refusal's clause is highlighted, and the word stays beside it.
        let refused = outcome_of(&Ending { code: 3, stdout: String::new(), stderr: "refused: law-denied: field 2 monotone\n".into() }, &[], true);
        assert!(refused.contains("refused") && refused.contains("mark class=\"clause\""), "{refused}");
    }

    #[test]
    fn endings_classify_by_exit_code_and_first_stderr_line() {
        let refused = Ending { code: 3, stdout: String::new(), stderr: "refused: law-denied: field 2 monotone\n  outcome: x\n".into() };
        assert_eq!(refused.class(true), ("refused", "refused: law-denied: field 2 monotone".into()));
        assert_eq!(refused.class(false).1, "read refused: law-denied: field 2 monotone");
        let undecided = Ending { code: 4, stdout: String::new(), stderr: "undecided: Host outcome uncertain; the attempt is retained, `lookup w-1` asks again\n".into() };
        assert_eq!(undecided.class(true).0, "undecided");
        let read = Ending { code: 0, stdout: "subject 1\n".into(), stderr: String::new() };
        assert_eq!(read.class(false), ("answered", "Answered".into()));
        assert!(answered(&read, &[]).contains("outcome answered"));
        let html = outcome(&undecided, &[]);
        assert!(html.contains("outcome undecided") && html.contains("/receipts/w-1"), "{html}");
        let ok = Ending { code: 0, stdout: "admitted at 12\n".into(), stderr: String::new() };
        assert!(outcome(&ok, &[("the doc", "/doc/a")]).contains("outcome admitted"));
        assert!(fresh_id().starts_with("w-") && fresh_id().len() == 14);
        assert!(workspace_id("w-1").is_ok() && workspace_id("../x").is_err());
    }

    /// A refusal, an error and an undecided attempt each offer the derived feedback form with the
    /// clause and the attempt id (the receipt the page links); an admitted write offers none.
    #[test]
    fn a_named_refusal_in_an_outcome_is_explained_in_the_same_partial() {
        let refused = Ending { code: 3, stdout: String::new(), stderr: "refused: kernel: notDecider\n".into() };
        let html = outcome_of(&refused, &[], true);
        assert!(html.contains("outcome refused") && html.contains("data-refusal=\"notDecider\"") && html.contains("Only the slot"), "{html}");
        let ok = Ending { code: 0, stdout: "notDecider is a word in this text".into(), stderr: String::new() };
        assert!(!outcome_of(&ok, &[], false).contains("data-refusal"), "an answer is never explained as a refusal");
    }

    #[test]
    fn a_failed_outcome_offers_a_prefilled_report_link() {
        let refused = Ending { code: 3, stdout: String::new(), stderr: "refused: law-denied: field 2 monotone (before 2, after 1)\n".into() };
        let html = outcome_of(&refused, &[("the receipt", "/receipts/w-abc")], true);
        let href = html.split("class=\"report\" href=\"").nth(1).and_then(|r| r.split('"').next()).unwrap_or_else(|| panic!("no report link: {html}")).replace("&amp;", "&");
        assert_eq!(query(&href, "from").as_deref(), Some("w-abc"), "{href}");
        assert_eq!(query(&href, "clause").as_deref(), Some("refused: law-denied: field 2 monotone (before 2, after 1)"), "{href}");
        assert_eq!(query(&href, "page").as_deref(), Some(PAGE_MARK), "{href}");
        assert!(href.starts_with("/verb/feedback?"), "{href}");
        let failed = Ending { code: 1, stdout: String::new(), stderr: "error: no such reference\n".into() };
        assert!(outcome_of(&failed, &[], true).contains("Report a problem"));
        let undecided = Ending { code: 4, stdout: String::new(), stderr: "undecided: the attempt is retained\n".into() };
        assert!(outcome_of(&undecided, &[], true).contains("Report a problem"));
        let ok = Ending { code: 0, stdout: "admitted\n".into(), stderr: String::new() };
        assert!(!outcome_of(&ok, &[("the receipt", "/receipts/w-abc")], true).contains("Report a problem"));
        // A receipt path that is not an attempt id is not offered as one.
        assert!(!outcome_of(&refused, &[("x", "/receipts/a/b")], true).contains("from="));
    }
}

#[cfg(test)]
#[test]
fn structured_capture_follows_the_grammar() {
    assert!(structured_answer(&["apps search --json".into()]));
    assert!(structured_answer(&["apps show app --json".into()]));
    assert!(!structured_answer(&["apps install app --json".into()]));
    assert!(!structured_answer(&["apps search".into()]));
    assert!(!structured_answer(&["say \"--json\"".into()]));
    assert!(!structured_answer(&["apps search --json".into(), "whoami".into()]));
}
