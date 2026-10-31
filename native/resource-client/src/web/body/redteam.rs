//! Red team (docs/review/2026-10-27-redteam/REDTEAM.md): strangers' words, planted where a
//! stranger can put them, rendered by the real body routes and the real document renderer, must
//! reach another member's browser as inert text. The shell is the one seam replaced: every line
//! the body runs as the member answers with a planted ending, so the routes, the partials and the
//! escaper are exactly the ones the gateway proxies.

use super::*;
use serde_json::json;
use std::cell::RefCell;

thread_local! {
    pub(super) static FAKE_SHELL: RefCell<Option<Box<dyn Fn(&[String]) -> Ending>>> = RefCell::new(None);
}

/// Every payload a stranger can type into a name, a line, a claim or a clause.
pub(crate) const PAYLOADS: &[&str] = &[
    "<script>alert(1)</script>",
    "<img src=x onerror=alert(1)>",
    "\"><svg onload=alert(1)>",
    "'><a href='javascript:alert(1)'>x</a>",
    "javascript:alert(1)",
    "data:text/html,<script>alert(1)</script>",
    "</textarea></pre></title><script>alert(1)</script>",
    "evil\u{202e}gnp.exe",
    "ali\u{200b}ce",
    "\u{1b}]52;c;c2VjcmV0\u{7}\u{9b}2J",
];

fn pct(text: &str) -> String {
    text.bytes().map(|b| if b.is_ascii_alphanumeric() { (b as char).to_string() } else { format!("%{b:02X}") }).collect()
}

fn hostile() -> String {
    let long = "A".repeat(20_000);
    format!("{} {long}", PAYLOADS.join(" "))
}

/// The rendered HTML carries no live markup or scheme a stranger chose, and no invisible
/// reordering or control character survives as itself.
pub(crate) fn assert_inert(where_: &str, html: &str) {
    let lower = html.to_ascii_lowercase();
    for tag in ["<script", "<img", "<svg", "<iframe src=\"javascript", "<a href='javascript"] {
        assert!(!lower.contains(tag), "{where_}: live {tag} in\n{html}");
    }
    for attr in ["href", "src", "action", "formaction"] {
        for scheme in ["javascript:", "data:", "vbscript:"] {
            for quote in ["\"", "'", ""] {
                let needle = format!("{attr}={quote}{scheme}");
                assert!(!lower.contains(&needle), "{where_}: {needle} in\n{html}");
            }
        }
    }
    for c in ['\u{202e}', '\u{200b}', '\u{1b}', '\u{7}', '\u{9b}'] {
        assert!(!html.contains(c), "{where_}: raw U+{:04X} survives", c as u32);
    }
}

fn site(tag: &str) -> (PathBuf, Site) {
    let stamp = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let root = std::env::temp_dir().join(format!("mini-redteam-{tag}-{}-{stamp}", std::process::id()));
    fs::create_dir_all(root.join("refs")).unwrap();
    fs::create_dir_all(root.join("home")).unwrap();
    // A reference name is a filename the member's workspace holds; an imported one can carry anything a
    // filename can.
    fs::write(root.join("refs").join("lab\"><img src=x onerror=alert(1)>.json"), "{}").unwrap();
    let site = Site {
        refs: Mutex::new(None),
        mutations: Mutex::new(()),
        home: Some(root.join("home")),
        root: root.clone(),
        workspace: Value::Null,
        subject: "7".into(),
        token: String::new(),
        front: Front { origins: Vec::new(), read_only: false },
        base: String::new(),
        face: Face::Body,
        shell: Some(Shell { host: "/unused".into(), config: "/unused".into(), home: root.join("home"), public_subject: Some("99".into()), front_doc: None, pool: Default::default() }),
    };
    (root, site)
}

/// What the shell "prints" for each line the body asks, with the stranger's words in every field.
fn planted(lines: &[String]) -> Ending {
    let h = hostile();
    let first = lines.first().cloned().unwrap_or_default();
    let ok = |stdout: String| Ending { code: 0, stdout, stderr: String::new() };
    if first.starts_with("apps search") {
        let app = json!({"appId": PAYLOADS[0], "name": PAYLOADS[1], "version": PAYLOADS[2], "publisher": PAYLOADS[7],
            "packageBuiltAt": PAYLOADS[0], "upstreamVersion": PAYLOADS[1],
            "suggestedClass": PAYLOADS[3], "categories":[PAYLOADS[0]], "featured":{"rank":1},
            "interface":{"status":PAYLOADS[2],"operations":[{"name":PAYLOADS[1],"description":h,"input":{PAYLOADS[0]:PAYLOADS[6]},"output":PAYLOADS[3]}]},
            "verdict": {"state": PAYLOADS[2], "reason": h}});
        return ok(json!({"apps": [app], "total": 1}).to_string());
    }
    if first.starts_with("apps show") {
        return ok(json!({"name": PAYLOADS[0], PAYLOADS[1]: h, "links": [PAYLOADS[4], PAYLOADS[5]]}).to_string());
    }
    if first.starts_with("apps list") {
        let grain = json!({"grain": PAYLOADS[0], "indexName": PAYLOADS[1], "state": PAYLOADS[2], "origin": PAYLOADS[4]});
        return ok(json!({"receipt": {"grains": [grain], "identityNotice": h}}).to_string());
    }
    if first.starts_with("apps status") {
        return ok(json!({"state": PAYLOADS[1], "receipt": {"origin": PAYLOADS[5], "indexName": PAYLOADS[0], "class": PAYLOADS[2],
            "runs": [{"note": h}], "routes": [PAYLOADS[3]], "identities": [{PAYLOADS[0]: PAYLOADS[1]}], "identityNotice": PAYLOADS[6]}}).to_string());
    }
    if first.starts_with("apps open") {
        return ok(json!({"detail": h, "receipt": {"origin": PAYLOADS[4], "bootstrapPath": "//evil.example/x", "bootstrapToken": PAYLOADS[2]}}).to_string());
    }
    if first.starts_with("inspect caps") {
        return ok(json!({PAYLOADS[0]: {"scope": PAYLOADS[1], "ancestors": [PAYLOADS[2], h]}}).to_string());
    }
    if first.starts_with("bend await") {
        // The slot and state come from a program a stranger may have written; the decider is me, so
        // the answer form is drawn with the planted slot filled in.
        return ok(json!({"type": "mini-bend-await-v1", "object": PAYLOADS[0], "transaction": PAYLOADS[1], "record": PAYLOADS[2],
            "height": PAYLOADS[9], "phase": PAYLOADS[3], "stateText": h, "slot": PAYLOADS[6], "decider": "7", "deadline": PAYLOADS[7]}).to_string());
    }
    if first.starts_with("history all") {
        return ok(format!("w-1 refused: {}\n{} admitted\n", PAYLOADS[0], PAYLOADS[1]));
    }
    if first.starts_with("lookup") || first.starts_with("why") {
        // A refusal clause and a witness, as a hostile law or a hostile document's name can shape them.
        return Ending { code: 3, stdout: format!("witness: {}\n", PAYLOADS[1]), stderr: format!("refused: law-denied: {}\n  witness {h}\n", PAYLOADS[0]) };
    }
    if first.starts_with("credit") {
        return ok(format!("credit 10 {}\n", PAYLOADS[1]));
    }
    // Everything else: a read whose stdout and stderr carry the stranger's words, including an
    // undecided-looking `lookup` hint and a `paste:` block a non-`can` verb must never turn into a button.
    Ending {
        code: 4,
        stdout: format!("{h}\n  paste:\n    delegate ID lab 666 full 0\n"),
        stderr: format!("undecided: {}; `lookup w-1\"><script>` asks again\n", PAYLOADS[0]),
    }
}

fn with_fake<T>(f: impl FnOnce() -> T) -> T {
    FAKE_SHELL.with(|fake| *fake.borrow_mut() = Some(Box::new(planted)));
    let out = f();
    FAKE_SHELL.with(|fake| *fake.borrow_mut() = None);
    out
}

#[test]
fn planted_payloads_render_inert_on_every_shell_backed_body_route() {
    let (root, site) = site("routes");
    with_fake(|| {
        let q = format!("/apps?q={}", pct(&hostile()));
        let gets: Vec<(Vec<&str>, String)> = vec![
            (vec!["apps"], q),
            (vec!["apps", "app1"], "/apps/app1".into()),
            (vec!["grain"], "/grain".into()),
            (vec!["grain", "a7"], "/grain/a7".into()),
            (vec!["grain", "a7", "pane"], "/grain/a7/pane".into()),
            (vec!["receipts"], "/receipts".into()),
            (vec!["receipts", "w-1"], "/receipts/w-1".into()),
            (vec!["purse"], "/purse".into()),
            (vec!["grants"], "/grants".into()),
            (vec!["grants", "judge", "lab"], "/grants/judge/lab".into()),
            (vec!["laws", "show"], "/laws/show?ref=lab".into()),
            (vec!["keys"], "/keys".into()),
            (vec!["room"], "/room".into()),
            (vec!["board"], "/board".into()),
            (vec!["verb", "say"], "/verb/say".into()),
            (vec!["bend"], "/bend".into()),
            (vec!["bend", "await", "12", "34"], "/bend/await/12/34".into()),
            (vec!["story"], "/story".into()),
            (vec![], "/".into()),
        ];
        // A story invitation and a story record carry an author's words; a bend registry row a
        // program's; all three are files a stranger's grant can shape.
        let home = root.join("home");
        fs::create_dir_all(home.join("requests")).unwrap();
        fs::create_dir_all(home.join("story")).unwrap();
        fs::create_dir_all(root.join("bend/objects")).unwrap();
        fs::write(home.join("requests/tale-invite.json"), json!({"type": "mini-story-invitation-v1", "story": "tale", "role": PAYLOADS[0],
            "author": PAYLOADS[2], "gm": PAYLOADS[1], "grant": {"recipient": "7"}}).to_string()).unwrap();
        fs::write(home.join("requests/odd-invite.json"), json!({"type": "mini-story-invitation-v1", "story": "odd", "role": PAYLOADS[3],
            "author": PAYLOADS[6], "grant": {"recipient": PAYLOADS[1]}}).to_string()).unwrap();
        fs::write(home.join("story/mine.json"), json!({"story": "mine", "role": PAYLOADS[0], "author": "7", "gm": PAYLOADS[7]}).to_string()).unwrap();
        fs::write(root.join("bend/objects/x.json"), json!({"bend": PAYLOADS[0], "object": PAYLOADS[2], "transaction": "34"}).to_string()).unwrap();
        for (parts, target) in gets {
            let page = get(&site, &parts, &target);
            assert_inert(&target, &page.body);
            assert_inert(&format!("{target} title"), &escape(&page.title));
        }
        let form = |pairs: &[(&str, &str)]| pairs.iter().map(|(k, v)| format!("{k}={}", pct(v))).collect::<Vec<_>>().join("&");
        let h = hostile();
        let posts: Vec<(Vec<&str>, String)> = vec![
            (vec!["grain", "a7", "open"], String::new()),
            (vec!["grain", "a7", "share"], form(&[("member", &h)])),
            (vec!["apps", "install"], form(&[("app", &h)])),
            (vec!["room", "lab", "say"], form(&[("text", &h)])),
            (vec!["doc", "new"], form(&[("name", &h), ("law", &h), ("room", &h)])),
            (vec!["paste"], form(&[("line", "say hello")])),
            (vec!["room", "lab", "hermes-tools"], form(&[("tool1", "on"), ("tool8", "on"), ("compute", "12"), ("was-tools", &h), ("was-compute", &h)])),
            (vec!["room", "lab", "hermes-tools"], form(&[("compute", &h)])),
        ];
        for (parts, body) in posts {
            let page = post(&site, &parts, body.as_bytes());
            assert_inert(&parts.join("/"), &page.body);
        }
    });
    fs::remove_dir_all(root).unwrap();
}

/// The grain hand-off draws URLs from a worker's reply: none of `javascript:`, `data:` or a
/// protocol-relative path reaches an `href`, `src` or `action`.
#[test]
fn worker_supplied_origins_never_reach_a_url_attribute_with_a_foreign_scheme() {
    let (root, site) = site("origins");
    with_fake(|| {
        let open = post(&site, &["grain", "a7", "open"], b"");
        assert!(open.body.contains("action=\"#refused-url\""), "{}", open.body);
        let pane = get(&site, &["grain", "a7", "pane"], "/grain/a7/pane");
        assert!(pane.body.contains("src=\"#refused-url\""), "{}", pane.body);
        let grains = get(&site, &["grain"], "/grain");
        assert!(grains.body.contains("href=\"#refused-url\""), "{}", grains.body);
    });
    for (input, safe) in [
        ("https://a7.demo.dregg.online", true), ("http://127.0.0.1:8080/x", true), ("/receipts/w-1", true),
        ("javascript:alert(1)", false), ("JaVaScRiPt:alert(1)", false), (" javascript:alert(1)", false),
        ("java\tscript:alert(1)", false), ("data:text/html,x", false), ("//evil.example", false),
        ("/\\evil.example", false), ("vbscript:x", false), ("doc/x", false), ("https://", false),
        ("https://a\u{202e}b", true),
    ] {
        assert_eq!(url(input) != "#refused-url", safe, "{input:?} -> {}", url(input));
    }
    assert_eq!(url("https://a\u{202e}b"), "https://a[U+202E]b");
    fs::remove_dir_all(root).unwrap();
}

/// A `paste:` block in any verb's output but `can --any`'s stays text: a stranger who gets their
/// words into a read (a document, a room, an app's claims) cannot plant a one-click
/// "paste and submit" that runs a line as the reading member.
#[test]
fn only_can_any_offers_a_paste_button() {
    let (root, site) = site("paste");
    with_fake(|| {
        for line in ["doc show lab", "tail -n 40 --in lab", "room members lab", "law show lab", "can lab --all"] {
            let page = act_as(&site, "x", vec![line.to_owned()], "", &[], false);
            assert!(!page.body.contains("action=\"/paste\""), "{line}: a planted paste line became a button:\n{}", page.body);
            assert!(page.body.contains("delegate ID lab 666 full 0"), "{line}: the planted line still shows, as text");
        }
        let page = act_as(&site, "x", vec!["can lab --any".to_owned()], "", &[], false);
        assert!(page.body.contains("action=\"/paste\""), "can --any keeps its button:\n{}", page.body);
        assert_inert("can --any", &page.body);
        // The tour's step 4 and `/verb/can` assemble the line from the grammar's form: the button stays.
        let page = post(&site, &["verb", "can"], b"alt=0&a1=lab&a3=on");
        assert!(page.body.contains("action=\"/paste\""), "the derived can form keeps its button:\n{}", page.body);
    });
    fs::remove_dir_all(root).unwrap();
}

/// The one renderer: a hostile document's text, marks, link targets, transclusion, annotations
/// and shared names, through `render::html` (the body's document page is this output).
#[test]
fn a_hostile_document_renders_inert() {
    let h = hostile();
    let doc = json!({"root":"1","rootRevision":"60","order":[
        {"element":"1002","parent":"1","kind":"atom","atom":"1002","payload":hex(h.as_bytes()),
            "revision":"71","createdBy":{"subject":PAYLOADS[0]},"struck":false,
            "marks":[{"kind":"bold","fresh":true},{"kind":"heading","fresh":true},
                {"kind":"link","fresh":true,"target":{"type":"document","id":PAYLOADS[4]}},
                {"kind":"link","fresh":true,"target":{"type":PAYLOADS[1],"id":PAYLOADS[5]}},
                {"kind":"link","fresh":false,"target":{"type":"range","document":"\"><script>alert(1)</script>"}}]},
        {"element":"8001","parent":"1","kind":"embed","transclusion":"8001"}],
      "transclusions":[{"id":PAYLOADS[2],"mode":PAYLOADS[3],"opening":{"source":"666","atoms":"2","height":"27","pins":[]},
            "render":{"view":"snapshot","lines":[hex(h.as_bytes())]},"at":"27"}]});
    let entries = vec![
        json!({"type":"annotation","id":PAYLOADS[1],"anchor":{"type":"atom","atom":"1002"},"fresh":true,
            "author":{"subject":PAYLOADS[0]},"body":{"type":"inline","bytes":hex(h.as_bytes())}}),
        json!({"type":"link","id":PAYLOADS[0],"name":PAYLOADS[1],"target":PAYLOADS[4]}),
    ];
    let names = std::collections::BTreeMap::from([("666".to_owned(), PAYLOADS[6].to_owned()), (PAYLOADS[4].to_owned(), PAYLOADS[0].to_owned())]);
    let rendered = crate::render::render(&crate::render::View { document: &doc, entries: &entries, names: &names, sources: &Default::default(), me: "7" }).unwrap();
    let html = rendered.html(PAYLOADS[0]);
    assert_inert("document", &html);
    assert!(html.contains("&lt;script&gt;alert(1)&lt;/script&gt;"), "the payload is rendered, as text");
    assert!(html.contains("evil[U+202E]gnp.exe") && html.contains("ali[U+200B]ce"), "invisible controls are made visible");
    assert!(!html.contains("href=\"javascript"), "a link mark carries no URL at all (data-target only)");
    let links = vec![json!({"source":"3","link":PAYLOADS[0],"kind":PAYLOADS[1],"target":PAYLOADS[4],"relation":"0","revision":"1","height":"20"})];
    let backlinks = vec![json!({"source":"\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}","link":"9","kind":"document","target":"3","relation":"0","revision":"1","height":"21"})];
    let index = index_sections("", &|id: &str| (id == PAYLOADS[4]).then(|| PAYLOADS[1].to_owned()), Some(&links), Some(&backlinks));
    assert_inert("links and backlinks", &index);
}

/// The one-partial outcome: a refusal clause, a witness, an undecided hint, the read context.
#[test]
fn outcome_partials_render_inert() {
    let h = hostile();
    for code in [0, 1, 2, 3, 4] {
        let ending = Ending { code, stdout: h.clone(), stderr: format!("refused: {}: {h}\nundecided: `lookup w-1\"><script>`\n", PAYLOADS[1]) };
        for transition in [true, false] {
            assert_inert("outcome", &outcome_of(&ending, &[(PAYLOADS[0], PAYLOADS[4])], transition));
        }
    }
    assert_inert("json tree", &json_tree(&json!({PAYLOADS[0]: [PAYLOADS[1], {"x": h}], "id": "a".repeat(64)})));
    assert_inert("outcome page", &outcome_page(PAYLOADS[0], "refused", PAYLOADS[1], &h, &[(PAYLOADS[2], PAYLOADS[5])]).body);
}

// A growing catalogue must never silently become a three-card sampler.
#[test]
fn catalogue_breadth_and_category_are_derived() {
    let (root, mut site) = site("catalogue-breadth");
    site.front.read_only = true;
    let apps: Vec<Value> = (1..=37).map(|i| json!({
        "appId":format!("app{i}"), "name":format!("Tool {i}"),
        "packageBuiltAt":if i == 1 { json!("2026-10-29T05:00:00Z") } else { Value::Null },
        "upstreamVersion":if i == 1 { json!("3.3.12") } else { Value::Null },
        "shortDescription":"A useful tool. ".repeat(160), "categories":["Office"],
        "featured":if i <= 36 { json!({"rank":i}) } else { Value::Null },
        "verdict":{"state":"unverified"}
    })).collect();
    FAKE_SHELL.with(|f| *f.borrow_mut() = Some(Box::new(move |_| Ending {
        code:0, stdout:json!({"apps":apps,"total":37}).to_string(), stderr:String::new()
    })));
    let front = public_front_with_welcome(&site, None);
    let market = apps::market(&site, "/apps");
    FAKE_SHELL.with(|f| *f.borrow_mut() = None);
    fs::remove_dir_all(root).unwrap();
    assert_eq!(front.body.matches("data-app=").count(), 36, "every featured app, no arbitrary cap");
    assert!(!front.body.contains("data-app=\"app37\""));
    assert_eq!(market.body.matches("data-app=").count(), 37);
    assert!(market.body.contains("Package version"));
    assert!(market.body.contains("Built 2026-10-29T05:00:00Z"));
    assert!(market.body.contains("Upstream version 3.3.12"));
    assert!(market.body.contains("Built not reported"));
    assert!(market.body.contains("name=\"category\""));
    assert!(market.body.contains("Office"));
    assert!(market.body.find("Featured apps").unwrap() < market.body.find("More from the catalogue").unwrap());
}

#[test]
fn catalogue_filters_use_the_shell_and_keep_failures_explained() {
    let (root, site) = site("catalogue-filter");
    FAKE_SHELL.with(|f| *f.borrow_mut() = Some(Box::new(|lines| {
        if lines == &["apps search Board --category Office --json".to_owned()] {
            Ending { code:3, stdout:String::new(), stderr:"refused: catalogue temporarily unavailable".into() }
        } else {
            Ending { code:0, stdout:json!({"apps":[{"appId":"board","name":"Board","categories":["Office"]}],"total":1}).to_string(), stderr:String::new() }
        }
    })));
    let page = apps::market(&site, "/apps?q=Board&category=Office");
    FAKE_SHELL.with(|f| *f.borrow_mut() = None);
    fs::remove_dir_all(root).unwrap();
    assert!(page.body.contains("catalogue temporarily unavailable"), "category must reach the shell, and its refusal stays visible");
    assert!(page.body.contains("value=\"Office\" selected"));
}

#[test]
fn the_operations_room_is_a_note_until_this_session_joined_it_and_the_turns_after() {
    // demo-path, the tour's web story reds on 2b8f75dcb: a workspace that holds the reference `operations`
    // but no room record for it printed the shell's "this session has no room operations" in a red
    // outcome <pre>, which the journey's first-<pre> reader took for the story's own output.
    let (root, site) = site("ops-room");
    fs::write(root.join("refs").join("operations.json"), "{}").unwrap();
    FAKE_SHELL.with(|f| *f.borrow_mut() = Some(Box::new(|_| Ending { code: 1, stdout: String::new(), stderr: "error: this session has no room operations (chat new operations, or chat join operations INVITATION)\n".into() })));
    let before = operations(&site);
    assert!(before.contains("has not joined it") && before.contains("chat join operations INVITATION"), "{before}");
    assert!(!before.contains("outcome error") && !before.contains("<pre"), "no red outcome, no pre: {before}");
    fs::create_dir_all(root.join("home").join("chat").join("rooms")).unwrap();
    fs::write(root.join("home").join("chat").join("rooms").join("operations.json"), "{}").unwrap();
    FAKE_SHELL.with(|f| *f.borrow_mut() = Some(Box::new(|_| Ending { code: 0, stdout: "alice: shipped\n".into(), stderr: String::new() })));
    let after = operations(&site);
    FAKE_SHELL.with(|f| *f.borrow_mut() = None);
    fs::remove_dir_all(root).unwrap();
    assert!(after.contains("From the operations room") && after.contains("alice: shipped"), "{after}");
}

/// G6: a re-posted form is the same attempt (its rendered `attempt` field), as the shell's exact retry
/// is: the second post of the same append runs `retry ID` (never a second proposal), and the same
/// attempt with other text is refused with nothing submitted.
#[test]
fn a_reposted_form_is_the_same_attempt() {
    let (root, site) = site("repost");
    let ran: std::rc::Rc<RefCell<Vec<Vec<String>>>> = Default::default();
    let seen = ran.clone();
    let ws = root.clone();
    FAKE_SHELL.with(|f| *f.borrow_mut() = Some(Box::new(move |lines: &[String]| {
        seen.borrow_mut().push(lines.to_vec());
        // what the shell leaves behind: the proposal the append authors, the attempt its submit writes
        if let Some(id) = lines.iter().find_map(|l| l.strip_prefix("doc append ").and_then(|r| r.split(' ').next())) {
            fs::create_dir_all(ws.join("proposals").join(id)).unwrap();
        }
        if let Some(id) = lines.iter().find_map(|l| l.strip_prefix("submit ")) {
            fs::create_dir_all(ws.join("attempts").join(id)).unwrap();
        }
        Ending { code: 0, stdout: "admitted".into(), stderr: String::new() }
    })));
    let page = post(&site, &["doc", "notes", "append"], b"attempt=w-0123456789ab&text=hello");
    assert_eq!(page.status, 200, "{}", page.body);
    let again = post(&site, &["doc", "notes", "append"], b"attempt=w-0123456789ab&text=hello");
    assert_eq!(again.status, 200, "{}", again.body);
    let other = post(&site, &["doc", "notes", "append"], b"attempt=w-0123456789ab&text=bye");
    FAKE_SHELL.with(|f| *f.borrow_mut() = None);
    let ran = ran.borrow();
    assert_eq!(ran.len(), 2, "the other text ran nothing: {ran:?}");
    assert!(ran[0][0].starts_with("doc append w-0123456789ab notes @web-w-0123456789ab.txt") && ran[0][1] == "submit w-0123456789ab", "{:?}", ran[0]);
    assert_eq!(ran[1], vec!["retry w-0123456789ab".to_owned()], "the same form again is the exact retry");
    assert_eq!(other.status, 409, "{}", other.body);
    assert!(other.body.contains("already submitted as attempt w-0123456789ab"), "{}", other.body);
    assert_eq!(fs::read_to_string(root.join("home/requests/web-w-0123456789ab.txt")).unwrap(), "hello", "the attempt's text is never rewritten");
    // a form without an attempt (a client that sent none) is a fresh attempt each time
    assert_ne!(form_attempt(&Default::default()), form_attempt(&Default::default()));
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn every_post_form_carries_its_own_attempt() {
    let html = with_attempts("<form method=\"post\" action=\"/a\"><button></button></form><form method=get action=/b></form><form method=post action=/c></form>");
    assert_eq!(html.matches("name=\"attempt\"").count(), 2, "{html}");
    let ids: Vec<&str> = html.match_indices("name=\"attempt\" value=\"").map(|(i, m)| &html[i + m.len()..i + m.len() + 14]).collect();
    assert_ne!(ids[0], ids[1]);
    assert!(html.contains("<form method=get action=/b></form>"), "a GET form is a read: {html}");
}
