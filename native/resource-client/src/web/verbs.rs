//! Every shell verb as a form, DERIVED from the shell's own verb table (`shell::command_catalog`:
//! `shell.rs`, `chat.rs`, `hermes.rs`, `story.rs`), never written per verb (ember 2026-10-27:
//! "everything that can be done over ssh and commands can also be done visually & via the web
//! interface"; docs/DEMO-EXPERIENCE-2026-10-27.md §1a). A verb's `usage` is its grammar: one
//! alternative per ` | `, literal words, UPPERCASE placeholders (optional in `[…]`), `--flags`
//! with or without a value. Each alternative renders as one form; its fields become the words of
//! one shell line, run as the member (`body::verb`), and the ending is the one outcome partial.
//! A new verb is visual the day its row enters the table. Bespoke pages (document, board, room,
//! receipt, grants, keys) sit beside this; they do not replace it.

use super::*;

#[derive(Debug, Clone, PartialEq)]
pub(super) enum Kind {
    /// A proposal id (`ID`): a fresh one is offered.
    Id,
    /// A reference name: a picker over this workspace's references (free text allowed).
    Ref,
    /// Free text, JSON or `@FILE`: a textarea, delivered through `HOME/requests` as `@FILE`.
    Text,
    Number,
    /// `a|b|c` of literals: a select.
    Choice(Vec<String>),
    Word,
    /// Free text given inline at the end of the line (chat, narrate): one line, as typed.
    Rest,
}

#[derive(Debug, Clone, PartialEq)]
pub(super) enum Tok {
    Lit(String),
    Arg { name: String, optional: bool, kind: Kind },
    /// `--flag` (bare: a checkbox) or `--flag VALUE` (a field; the flag is sent when filled).
    Flag { name: String, value: Option<(String, Kind)>, optional: bool },
}

#[derive(Debug, Clone, PartialEq)]
pub(super) struct Alt {
    pub tokens: Vec<Tok>,
}

impl Alt {
    /// The leading literal words: the leaf's name (`doc append`, `room template show`), as the
    /// journey's parity row reads it from `help`.
    pub fn literals(&self) -> String {
        self.tokens.iter().map_while(|t| if let Tok::Lit(l) = t { Some(l.as_str()) } else { None }).collect::<Vec<_>>().join(" ")
    }

    /// A proposal: its first placeholder is the proposal `ID`; `submit ID` is offered after it.
    pub fn proposes(&self, operation: &str) -> bool {
        operation.contains("propose") && self.tokens.iter().any(|t| matches!(t, Tok::Arg { kind: Kind::Id, .. }))
    }
}

/// Whether the alternative at `index` of `usage` is a WORLD TRANSITION (a proposal, a submit, a
/// birth, a payment) rather than a read or a local verb, read from the `operation` segment that
/// names it (the segments align with the usage alternatives; a verb with one segment applies it
/// to every alternative). Interim: the structured command grammar (A0) carries this as data.
pub(super) fn transition(usage: &str, operation: &str, index: usize, literals: &str) -> bool {
    let segments: Vec<&str> = operation.split(" | ").collect();
    let alternatives_count = usage.split(" | ").count();
    let segment = if segments.len() == alternatives_count {
        segments.get(index).copied().unwrap_or(operation)
    } else {
        // Fewer segments than alternatives (`doc`): the segment that names this subcommand
        // (`doc-show`, or the word inside `propose (payload document: append, edit, …)`).
        let mut words = literals.split(' ');
        let verb = words.next().unwrap_or("");
        match words.next() {
            Some(sub) => segments
                .iter()
                .find(|seg| seg.contains(&format!("{verb}-{sub}")) || seg.starts_with(sub) || seg.contains(&format!(" {sub},")) || seg.contains(&format!(" {sub})")) || seg.contains(&format!(": {sub}")))
                .copied()
                .unwrap_or(operation),
            None => operation,
        }
    };
    let lower = segment.to_ascii_lowercase();
    let read = lower.starts_with("local") || lower.contains("signed read") || lower.contains("signed view") || lower.contains("signed tail") || lower.contains("--action list") || lower.contains("--action read") || lower.contains("--action describe") || lower.contains("--action inspect") || lower.contains("--action can") || lower.contains("--action recover") || lower.contains("dry-run") || lower.contains("--format") || lower.contains("doc-show") || lower.contains("doc-history") || lower.contains("doc-diff") || lower.contains("--action status") || lower.contains("--action balance") || lower.contains("--action tariff") && !lower.contains("--set") || lower.starts_with("who") || lower.starts_with("describe") || lower.starts_with("chat:") || lower.starts_with("current app admission") || lower.contains("--action search") || lower.contains("--action key-status");
    // Anything the segment does not name as a read or a local verb is a world transition: the
    // safe default for a verb that may write (its exit 0 is then "admitted" only when it is).
    !read
}

/// The alternatives of a verb: from its grammar when the grammar is data (A0), else read from
/// its usage string (the interim).
pub(super) fn alternatives_of(name: &str, usage: &str) -> Vec<Alt> {
    match crate::shell_grammar::grammar(name) {
        Some(g) => g.leaves.iter().map(leaf_alt).collect(),
        None => alternatives(usage),
    }
}

/// One grammar leaf as form tokens: typed arguments, flags (a dangerous one is a checkbox the
/// person must tick), the leaf's literal path.
fn leaf_alt(leaf: &crate::shell_grammar::Leaf) -> Alt {
    use crate::shell_grammar::Kind as G;
    let kind = |k: G| match k {
        G::Id => Kind::Id,
        G::Ref => Kind::Ref,
        G::Subject | G::Word => Kind::Word,
        G::Number => Kind::Number,
        G::TextOrFile | G::File | G::FileOrStdin | G::Law => Kind::Text,
        G::KeyFile => Kind::Word,
        G::Rest => Kind::Rest,
        G::Choice(options) => Kind::Choice(options.iter().map(|o| o.to_string()).collect()),
    };
    let mut tokens: Vec<Tok> = leaf.path.iter().map(|w| Tok::Lit(w.to_string())).collect();
    for a in leaf.args {
        tokens.push(Tok::Arg { name: a.name.to_owned(), optional: a.optional, kind: kind(a.kind) });
    }
    for f in leaf.flags {
        tokens.push(Tok::Flag { name: f.name.to_owned(), value: f.value.map(|(p, k)| (p.to_owned(), kind(k))), optional: !f.required });
    }
    Alt { tokens }
}

/// Whether an alternative is a world transition: the grammar's effect when the verb has one.
fn transition_of(name: &str, usage: &str, operation: &str, index: usize, literals: &str) -> bool {
    match crate::shell_grammar::grammar(name) {
        Some(g) => g.leaves.get(index).is_some_and(|l| matches!(l.effect, crate::shell_grammar::Effect::Propose | crate::shell_grammar::Effect::Transition)),
        None => transition(usage, operation, index, literals),
    }
}

/// Split a usage into alternatives (` | ` between them; a `|` inside a word is a choice).
pub(super) fn alternatives(usage: &str) -> Vec<Alt> {
    usage.split(" | ").map(|alt| Alt { tokens: tokens(alt) }).filter(|a| !a.tokens.is_empty()).collect()
}

/// Group a usage alternative into raw words: bracket groups and quoted spans stay whole.
fn raw_words(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut word = String::new();
    let mut depth = 0usize;
    let mut quoted = false;
    for c in text.chars() {
        match c {
            '"' => {
                quoted = !quoted;
                word.push(c);
            }
            '[' if !quoted => {
                depth += 1;
                word.push(c);
            }
            ']' if !quoted && depth > 0 => {
                depth -= 1;
                word.push(c);
            }
            c if c.is_whitespace() && depth == 0 && !quoted => {
                if !word.is_empty() {
                    out.push(std::mem::take(&mut word));
                }
            }
            c => word.push(c),
        }
    }
    if !word.is_empty() {
        out.push(word);
    }
    out
}

fn is_literal(word: &str) -> bool {
    !word.is_empty() && word.bytes().all(|b| b.is_ascii_lowercase() || b == b'-' || b == b'/') && !word.starts_with('-')
}

fn kind_of(name: &str) -> Kind {
    let base = name.split(['|', '[']).next().unwrap_or(name).trim_end_matches("...");
    if name.contains("JSON") || name.contains("@FILE") || name.contains("@-") || name.starts_with('"') || base == "TEXT" || base == "INDEX-DOC" {
        return Kind::Text;
    }
    if base == "ID" {
        return Kind::Id;
    }
    if matches!(
        base,
        "REF" | "ROOM" | "BOARD" | "DOCUMENT" | "MARKET" | "JOB" | "PARENT" | "SOURCE" | "KIND" | "NAME" | "NEXT" | "TARGET" | "ACCOUNT-REF" | "FACTORY-REF" | "CATALOG" | "ROOM/NAME" | "ATTEMPT" | "PROGRAM" | "PROGRAM-ID" | "SCENE" | "TASK" | "SHARED" | "INDEX"
    ) {
        return Kind::Ref;
    }
    if matches!(base, "N" | "AMOUNT" | "COST" | "MAX-COST" | "PRICE" | "QTY" | "LINE" | "SECONDS" | "HEIGHT" | "H" | "H1" | "H2" | "FUNDING" | "OFFSET" | "SUPPLY" | "B" | "P" | "A" | "EPOCH" | "REVISION" | "ATOM") {
        return Kind::Number;
    }
    if name.contains('|') && name.split('|').all(|w| !w.is_empty() && w.bytes().all(|b| b.is_ascii_lowercase() || b == b'-')) {
        return Kind::Choice(name.split('|').map(str::to_owned).collect());
    }
    Kind::Word
}

fn tokens(alt: &str) -> Vec<Tok> {
    let mut out = Vec::new();
    for raw in raw_words(alt) {
        let (inner, optional) = match raw.strip_prefix('[').and_then(|r| r.strip_suffix(']')) {
            Some(inner) => (inner.to_owned(), true),
            None => (raw.clone(), false),
        };
        // A bracket may hold `--flag VALUE`, `--flag: a note`, or `a|b`; outside brackets a raw
        // word is one token (a quoted span stays whole).
        let pieces: Vec<&str> = if optional { inner.split_whitespace().collect() } else { vec![inner.as_str()] };
        let mut parts = pieces.into_iter();
        let Some(first) = parts.next() else { continue };
        if first.starts_with('-') {
            let name = first.trim_end_matches(':').to_owned();
            let rest: Vec<&str> = parts.collect();
            let value = match rest.first() {
                Some(v) if !first.ends_with(':') && (v.chars().any(|c| c.is_ascii_uppercase()) || v.contains('|') || v.starts_with('@')) => Some(((*v).to_owned(), kind_of(v))),
                _ => None,
            };
            out.push(Tok::Flag { name, value, optional });
            continue;
        }
        if is_literal(first) {
            if optional {
                // `[all]`, `[again]`, `[at N]`: an optional literal word is a choice of one.
                out.push(Tok::Arg { name: first.to_owned(), optional: true, kind: Kind::Choice(vec![first.to_owned()]) });
                for more in parts {
                    if !is_literal(more) {
                        out.push(Tok::Arg { name: more.to_owned(), optional: true, kind: kind_of(more) });
                    }
                }
            } else {
                out.push(Tok::Lit(first.to_owned()));
            }
            continue;
        }
        if first.contains('|') && first.split('|').all(is_literal) {
            out.push(Tok::Arg { name: first.to_owned(), optional, kind: Kind::Choice(first.split('|').map(str::to_owned).collect()) });
            continue;
        }
        out.push(Tok::Arg { name: first.to_owned(), optional, kind: kind_of(first) });
        // `[A B]`: further placeholders in one optional group are each optional.
        for more in parts {
            if more.starts_with('-') {
                out.push(Tok::Flag { name: more.to_owned(), value: None, optional: true });
            } else if is_literal(more) {
                out.push(Tok::Lit(more.to_owned()));
            } else {
                out.push(Tok::Arg { name: more.to_owned(), optional: true, kind: kind_of(more) });
            }
        }
    }
    out
}

// ---------------------------------------------------------------- rendering

/// `/verb`: every verb of the shell, as the shell lists it.
pub(super) fn index(site: &Site) -> Page {
    let mut rows = String::new();
    for v in crate::shell::command_catalog() {
        rows.push_str(&format!(
            "<tr><td><a href=\"/verb/{n}\">{n}</a></td><td><code>{}</code></td><td class=\"note\">{}</td></tr>\n",
            escape(v.usage),
            escape(&clip(v.operation, 160)),
            n = escape(v.name)
        ));
    }
    let note = if site.front.read_only {
        "<p>Everything you can do in Mini, in one place. <a href=\"/join\" data-full>Join</a> to use these commands as forms.</p>"
    } else {
        "<p>Everything you can do in Mini, in one place. Choose a command, fill in its fields, and read the result.</p>"
    };
    Page { status: 200, title: "Commands".into(), stamp: Stamp::None, body: format!("{note}\n<table><thead><tr><th>verb</th><th>usage</th><th>operation</th></tr></thead><tbody>{rows}</tbody></table>") }
}

fn clip(text: &str, n: usize) -> String {
    if text.chars().count() <= n { text.to_owned() } else { format!("{}…", text.chars().take(n).collect::<String>()) }
}

/// `/verb/NAME`: one form per alternative of the verb's usage.
pub(super) fn page(site: &Site, name: &str, target: &str) -> Page {
    let Some(verb) = crate::shell::command_catalog().find(|v| v.name == name) else {
        return simple(404, "No such verb", &format!("the shell has no verb {name}"));
    };
    let alts = alternatives_of(name, verb.usage);
    let refs = site.names();
    let mut body = format!(
        "<p>Choose an action below. Required fields must be filled before you run it.</p><details><summary>Command reference</summary><p><code>{}</code></p><p class=note>{}</p></details>\n<datalist id=\"refs\">{}</datalist>\n",
        escape(verb.usage), escape(verb.operation),
        refs.iter().map(|r| format!("<option value=\"{}\">", escape(r))).collect::<String>()
    );
    if site.front.read_only {
        body.push_str("<p class=note>The public reader runs no verb.</p>");
        return Page { status: 200, title: name.to_owned(), stamp: Stamp::None, body };
    }
    // A link may prefill the fields (`/verb/feedback?page=/doc&clause=...`): a query key is a
    // field's name, lowercased and without its dashes (`--from` is `from`, `TEXT` is `text`), and
    // reaches every alternative that has such a field. Values are fields to read and send, never
    // run: the person presses Run.
    let prefill = |key: &str| super::body::query(target, key);
    for (i, alt) in alts.iter().enumerate() {
        body.push_str(&form_with(name, i, alt, verb.operation, &format!("/verb/{}", escape(name)), "", &prefill));
    }
    Page { status: 200, title: name.to_owned(), stamp: Stamp::None, body }
}

/// The form of one verb alternative, by the literal words that name it (`"doc append"`), posted
/// to `action` with `hidden` fields before its own: the tour embeds the real forms this way.
pub(super) fn form_for(name: &str, literals: &str, action: &str, hidden: &str) -> Option<String> {
    let verb = crate::shell::command_catalog().find(|v| v.name == name)?;
    let alts = alternatives_of(name, verb.usage);
    let (index, alt) = alts.iter().enumerate().find(|(_, a)| a.literals() == literals)?;
    Some(form_with(name, index, alt, verb.operation, action, hidden, &|_| None))
}

/// `form_for` with fields prefilled by query key (`prefill_key`: `SLOT` is `slot`,
/// `INVITATION|@FILE` is `invitationfile`): a place's page embeds the real form with what the
/// place already knows filled in; the person still presses Run.
pub(super) fn form_for_filled(name: &str, literals: &str, action: &str, hidden: &str, filled: &[(&str, &str)]) -> Option<String> {
    let verb = crate::shell::command_catalog().find(|v| v.name == name)?;
    let alts = alternatives_of(name, verb.usage);
    let (index, alt) = alts.iter().enumerate().find(|(_, a)| a.literals() == literals)?;
    let prefill = |key: &str| filled.iter().find(|(k, _)| *k == key).map(|(_, v)| (*v).to_owned());
    Some(form_with(name, index, alt, verb.operation, action, hidden, &prefill))
}

/// The lines one leaf of `name` assembles to from values given by argument name (the grammar's
/// own names, `ROOM`, `N`, `set`), through the one assembler the forms use: the leaf is the one
/// whose literal path is `literals` and whose arguments include every name given. A place whose
/// control is not one field per argument (checkboxes summed to a bitmask) computes the values
/// and still speaks the verb's grammar.
pub(super) fn assemble_named(site: &Site, name: &str, literals: &str, values: &[(&str, &str)]) -> std::result::Result<(Vec<String>, String, bool, String), Page> {
    let Some(verb) = crate::shell::command_catalog().find(|v| v.name == name) else {
        return Err(simple(404, "No such verb", &format!("the shell has no verb {name}")));
    };
    let alts = alternatives_of(name, verb.usage);
    // A value names its argument, or (a choice given as itself: `("hermes/tools", "hermes/tools")`)
    // the choice argument that lists it.
    let names = |tok: &Tok, key: &str, value: &str| match tok {
        Tok::Arg { name, kind, .. } => name == key || (key == value && matches!(kind, Kind::Choice(options) if options.iter().any(|o| o == value))),
        _ => false,
    };
    let Some((index, alt)) = alts.iter().enumerate().find(|(_, a)| a.literals() == literals && values.iter().all(|(k, v)| a.tokens.iter().any(|t| names(t, k, v)))) else {
        return Err(simple(400, name, &format!("no leaf {literals} takes {}", values.iter().map(|(k, _)| *k).collect::<Vec<_>>().join(", "))));
    };
    let mut form = std::collections::BTreeMap::new();
    form.insert("alt".to_owned(), index.to_string());
    for (i, tok) in alt.tokens.iter().enumerate() {
        if let Some((_, v)) = values.iter().find(|(k, v)| names(tok, k, v)) {
            form.insert(format!("a{i}"), (*v).to_owned());
        }
    }
    assemble(site, name, &form)
}

fn form(name: &str, index: usize, alt: &Alt, operation: &str, action: &str, hidden: &str) -> String {
    form_with(name, index, alt, operation, action, hidden, &|_| None)
}

/// The query key that prefills a token: an argument's name or a flag's, lowercased, letters and
/// digits only (`TEXT|@FILE` is `textfile`, `--from` is `from`).
fn prefill_key(name: &str) -> String {
    name.chars().filter(char::is_ascii_alphanumeric).map(|c| c.to_ascii_lowercase()).collect()
}

fn form_with(name: &str, index: usize, alt: &Alt, operation: &str, action: &str, hidden: &str, prefill: &dyn Fn(&str) -> Option<String>) -> String {
    let mut out = format!(
        "<section class=\"verb-form\"><h2><code>{}</code></h2><form method=\"post\" action=\"{action}\">{hidden}<input type=\"hidden\" name=\"alt\" value=\"{index}\"><div class=\"fields\">",
        escape(&alt.literals()),
    );
    // Each form's fields carry ids unique on the page (a verb renders one form per
    // alternative, and the tour embeds several verbs' forms on one page), so a
    // `label for` always resolves to its own field; the `name` stays positional
    // (`a{i}`): the assembler reads it.
    let prefix = format!("{name}-{index}");
    for (i, tok) in alt.tokens.iter().enumerate() {
        let field = format!("a{i}");
        let id = format!("{prefix}-{i}");
        match tok {
            Tok::Lit(_) => {}
            Tok::Arg { name, optional, kind } => out.push_str(&input(&id, &field, name, *optional, kind, prefill(&prefill_key(name)).as_deref())),
            Tok::Flag { name, value: None, optional } => {
                out.push_str(&format!("<label class=\"check\" for=\"flag-{id}\"><input type=\"checkbox\" id=\"flag-{id}\" name=\"{field}\" value=\"on\"{}> <code>{}</code>{}</label>", if *optional { "" } else { " required" }, escape(name), if *optional { "" } else { " (required)" }));
            }
            Tok::Flag { name, value: Some((placeholder, kind)), optional } => {
                out.push_str(&input(&id, &field, &format!("{name} {placeholder}"), *optional, kind, prefill(&prefill_key(name)).as_deref()));
            }
        }
    }
    let proposes = match crate::shell_grammar::grammar(name) {
        Some(g) => g.leaves.get(index).is_some_and(|l| l.effect == crate::shell_grammar::Effect::Propose),
        None => alt.proposes(operation),
    };
    if proposes {
        out.push_str(&format!("<label class=\"check\" for=\"{prefix}-submit\"><input type=\"checkbox\" id=\"{prefix}-submit\" name=\"submit\" value=\"on\" checked> and <code>submit ID</code> at once</label>"));
    }
    out.push_str("</div><p><button>Run</button></p></form></section>\n");
    out
}

/// One field of a derived form: labelled by the grammar leaf's argument name (and kind, as the
/// placeholder shows), with a page-unique `id` so the label resolves to this field and no other.
fn input(id: &str, field: &str, label: &str, optional: bool, kind: &Kind, value: Option<&str>) -> String {
    let req = if optional { "" } else { " required" };
    let preset = value.map(|v| format!(" value=\"{}\"", escape(v))).unwrap_or_default();
    let shown = format!("{}{}", escape(label), if optional { " <span class=note>(optional)</span>" } else { "" });
    let control = match kind {
        Kind::Text => format!("<label for=\"{id}\">{shown}</label><textarea id=\"{id}\" name=\"{field}\" maxlength=\"4096\"{req}>{}</textarea>", value.map(escape).unwrap_or_default()),
        Kind::Choice(options) => format!(
            "<label for=\"{id}\">{shown}</label><select id=\"{id}\" name=\"{field}\">{}{}</select>",
            if optional { "<option value=\"\">—</option>" } else { "" },
            options.iter().map(|o| format!("<option>{}</option>", escape(o))).collect::<String>()
        ),
        Kind::Ref => format!("<label for=\"{id}\">{shown}</label><input id=\"{id}\" name=\"{field}\" type=\"text\" list=\"refs\" autocomplete=\"off\"{req}{preset}>"),
        Kind::Id => format!("<label for=\"{id}\">{shown}</label><input id=\"{id}\" name=\"{field}\" type=\"text\" value=\"{}\" pattern=\"[A-Za-z0-9-]+\"{req}>", escape(value.unwrap_or(&super::body::fresh_id()))),
        Kind::Number => format!("<label for=\"{id}\">{shown}</label><input id=\"{id}\" name=\"{field}\" type=\"text\" inputmode=\"numeric\"{req}{preset}>"),
        Kind::Word => format!("<label for=\"{id}\">{shown}</label><input id=\"{id}\" name=\"{field}\" type=\"text\"{req}{preset}>"),
        Kind::Rest => format!("<label for=\"{id}\">{shown}</label><input id=\"{id}\" name=\"{field}\" type=\"text\" maxlength=\"2000\"{req}{preset}>"),
    };
    format!("<div class=\"field\">{control}</div>")
}

// ---------------------------------------------------------------- running

/// The lines one alternative's fields assemble to (the verb line, and `submit ID` when asked),
/// the proposal id, and whether they are a world transition. `Err` is the page that names what is
/// missing. One assembler serves the POST and the dry run.
pub(super) fn assemble(site: &Site, name: &str, form: &std::collections::BTreeMap<String, String>) -> std::result::Result<(Vec<String>, String, bool, String), Page> {
    let Some(verb) = crate::shell::command_catalog().find(|v| v.name == name) else {
        return Err(simple(404, "No such verb", &format!("the shell has no verb {name}")));
    };
    let alts = alternatives_of(name, verb.usage);
    let Some(alt) = form.get("alt").and_then(|a| a.parse::<usize>().ok()).and_then(|i| alts.get(i)) else {
        return Err(simple(400, name, "which alternative of the usage?"));
    };
    let field = |i: usize| form.get(&format!("a{i}")).map(|v| v.trim().to_owned()).unwrap_or_default();
    let mut words: Vec<String> = Vec::new();
    let mut rest_text: Option<String> = None;
    let mut id = String::new();
    let mut files = 0usize;
    for (i, tok) in alt.tokens.iter().enumerate() {
        match tok {
            Tok::Lit(l) => words.push(l.clone()),
            Tok::Arg { name: label, optional, kind } => {
                let value = field(i);
                if value.is_empty() {
                    if *optional {
                        continue;
                    }
                    return Err(simple(400, name, &format!("{label} is required")));
                }
                if matches!(kind, Kind::Id) && id.is_empty() {
                    id = value.clone();
                }
                match kind {
                    // Free text rides on the line as typed (the verb takes the rest of the line).
                    // The grammar reads flags only BEFORE the free text, so the text goes last.
                    Kind::Rest => {
                        if value.contains('\n') {
                            return Err(simple(400, name, &format!("{label} is one line")));
                        }
                        rest_text = Some(value);
                    }
                    Kind::Text if !(value.starts_with('@') && !value.contains('\n')) => {
                        files += 1;
                        let stamp = if id.is_empty() { super::body::fresh_id() } else { id.clone() };
                        match super::body::text_file(site, &format!("{stamp}-{files}"), &value) {
                            Some(file) => words.push(format!("@{file}")),
                            None => return Err(simple(400, name, &format!("{label} must be 1..4096 bytes"))),
                        }
                    }
                    _ => words.push(super::body::quote(&value)),
                }
            }
            Tok::Flag { name: flag, value: None, .. } => {
                if field(i) == "on" {
                    words.push(flag.clone());
                }
            }
            Tok::Flag { name: flag, value: Some(_), .. } => {
                let value = field(i);
                if !value.is_empty() {
                    words.push(flag.clone());
                    words.push(super::body::quote(&value));
                }
            }
        }
    }
    words.extend(rest_text);
    let mut lines = vec![words.join(" ")];
    let index = form.get("alt").and_then(|a| a.parse::<usize>().ok()).unwrap_or(0);
    let mut is_transition = transition_of(name, verb.usage, verb.operation, index, &alt.literals());
    let proposes = match crate::shell_grammar::grammar(name) {
        Some(g) => g.leaves.get(index).is_some_and(|l| l.effect == crate::shell_grammar::Effect::Propose),
        None => alt.proposes(verb.operation),
    };
    if form.get("submit").map(String::as_str) == Some("on") && proposes && !id.is_empty() {
        // The tour's lost-reply switch rides on the submit line (DEMO-EXPERIENCE A11).
        let lose = if form.get("lose").map(String::as_str) == Some("on") { " --lose-reply-once" } else { "" };
        lines.push(format!("submit {id}{lose}"));
        is_transition = true;
    }
    Ok((lines, id, is_transition, alt.literals()))
}

/// POST `/verb/NAME`: the chosen alternative's fields become one shell line (plus `submit ID`
/// when asked), run as the member.
pub(super) fn post(site: &Site, name: &str, form: &std::collections::BTreeMap<String, String>) -> Page {
    let (lines, id, is_transition, title) = match assemble(site, name, form) {
        Ok(assembled) => assembled,
        Err(page) => return page,
    };
    let next: Vec<(String, String)> = vec![(format!("{name} again"), format!("/verb/{name}")), ("all commands".into(), "/verb".into())];
    let refs: Vec<(&str, &str)> = next.iter().map(|(a, b)| (a.as_str(), b.as_str())).collect();
    super::body::act_as(site, &title, lines, &id, &refs, is_transition)
}

/// A placeholder value for one grammar argument in the dry run, by its kind and name: a reference
/// this workspace holds (or `paper`), a fresh id, `1`, `sealed` for a law, the files the journey
/// seeds (`HOME/requests/x.txt`, `x.json`, `HOME/keys/x.txt`), a plausible word for a name.
fn placeholder(kind: crate::shell_grammar::Kind, name: &str, refs: &[String]) -> String {
    use crate::shell_grammar::Kind as G;
    match kind {
        G::Id => super::body::fresh_id(),
        G::Ref => refs.first().cloned().unwrap_or_else(|| "paper".into()),
        G::Subject | G::Number => "1".into(),
        G::TextOrFile => "hello".into(),
        G::File | G::FileOrStdin => "@x.txt".into(),
        G::KeyFile => "mini.key".into(),
        G::Law => "sealed".into(),
        G::Choice(options) => options.first().map(|o| o.to_string()).unwrap_or_default(),
        G::Rest => "hello there".into(),
        G::Word => {
            let n = name.to_ascii_uppercase();
            if n.contains("DECLARATION") { "@decl.json".into() }
            else if n.contains("JSON") { "@x.json".into() }
            else if n.starts_with("T|") { "social".into() }
            else if n.contains("GRAIN") { "a1".into() }
            else if n.contains("COSIGN") || n.contains("SIGNATURE") { "ab".repeat(64) }
            else if n.contains("HEX") { "ab".repeat(32) }
            else if n.contains("@FILE") || n.contains("FILE") { "@x.txt".into() }
            else if n.contains("CELL:SEQUENCE") { "1:1".into() }
            else if n.contains("ABS_PATH") { "/tmp/x".into() }
            else if n.contains("STORAGE") { "declared".into() }
            else if n.contains("LAW") { "sealed".into() }
            else if n.contains("EXIT") || n.contains("SCENE") || n.contains("ITEM") || n.contains("VERB") || n.contains("METHOD") || n.contains("TASK") || n.contains("PROVIDER") || n.contains("MODEL") || n.contains("RUNNER") || n.contains("MEMBER") || n.contains("NAME") || n.contains("ROOM") || n.contains("PETNAME") || n.contains("TERM") || n.contains("CATEGORY") || n.contains("APP") || n.contains("PACKAGE") || n.contains("REQUEST") || n.contains("ID") { "bob".into() }
            else if n.contains("FIELD") || n.contains("KEY") || n.contains("VALUE") || n.contains("EXPECTED") || n.contains("EMOJI") || n.contains("N") { "1".into() }
            else { "x1".into() }
        }
    }
}

/// `/verb/NAME/dry`: every leaf of the verb, its form filled with placeholders, assembled to its
/// shell line and run through the shell's planner (`mini shell --line … --plan`): the real parser
/// and plan builder, no Host, nothing written to the world. A leaf whose line the shell refuses
/// as usage is red by name: its form and its parser disagree. The parity row sums these.
pub(super) fn dry(site: &Site, name: &str) -> Page {
    let Some(verb) = crate::shell::command_catalog().find(|v| v.name == name) else {
        return simple(404, "No such verb", &format!("the shell has no verb {name}"));
    };
    let alts = alternatives_of(name, verb.usage);
    let grammar = crate::shell_grammar::grammar(name);
    let refs = site.names();
    // A PRIVATE-ROOM argument takes a private room this workspace founded (its reference names
    // its keys cell), when there is one; the journey founds one before it measures parity.
    let private_refs: Vec<String> = refs
        .iter()
        .filter(|r| std::fs::read(site.root.join("refs").join(format!("{r}.json"))).ok().and_then(|b| serde_json::from_slice::<Value>(&b).ok()).is_some_and(|v| v.get("private").is_some()))
        .cloned()
        .collect();
    let refs_for = |label: &str| if label.contains("PRIVATE") && !private_refs.is_empty() { &private_refs } else { &refs };
    let mut rows = String::new();
    let mut errors = 0usize;
    let mut world = 0usize;
    for (index, alt) in alts.iter().enumerate() {
        let leaf = grammar.and_then(|g| g.leaves.get(index));
        let mut form = std::collections::BTreeMap::new();
        form.insert("alt".to_owned(), index.to_string());
        // Every positional argument (optional ones too: every field of the form) and the required
        // flags, by the grammar's kinds; optional flags are left out.
        let mut position = 0usize;
        for (i, tok) in alt.tokens.iter().enumerate() {
            match tok {
                Tok::Arg { name: label, .. } => {
                    let kind = leaf.and_then(|l| l.args.get(position)).map(|a| a.kind).unwrap_or(crate::shell_grammar::Kind::Word);
                    position += 1;
                    form.insert(format!("a{i}"), placeholder(kind, label, refs_for(label)));
                }
                Tok::Flag { name: flag, value, optional: false } => {
                    let kind = leaf.and_then(|l| l.flags.iter().find(|f| f.name == flag)).and_then(|f| f.value).map(|(_, k)| k);
                    form.insert(format!("a{i}"), match (value, kind) {
                        (None, _) => "on".into(),
                        (Some((label, _)), Some(kind)) => placeholder(kind, label, &refs),
                        (Some((label, _)), None) => placeholder(crate::shell_grammar::Kind::Word, label, &refs),
                    });
                }
                _ => {}
            }
        }
        let (class, detail) = match assemble(site, name, &form) {
            Err(page) => ("usage", page.body),
            Ok((lines, _, _, _)) => match super::body::plan_line(site, &lines[0]) {
                Some(ending) if ending.code == 0 => ("answered", ending.stdout.trim().to_owned()),
                // The grammar refused the assembled line: the form and the parser disagree.
                Some(ending) if ending.code == 2 => ("usage", ending.stderr.trim().to_owned()),
                // The words parse; this workspace cannot plan them (a fact of the world).
                Some(ending) => ("world", ending.stderr.trim().to_owned()),
                None => ("usage", "no shell paths".to_owned()),
            },
        };
        match class {
            "usage" => errors += 1,
            "world" => world += 1,
            _ => {}
        }
        rows.push_str(&format!("<tr class=\"{class}\"><td><code>{}</code></td><td class=\"outcome {class}\">{class}</td><td><code>{}</code></td></tr>\n", escape(&alt.literals()), escape(&clip(&detail, 200))));
    }
    Page {
        status: 200,
        title: format!("{name}: dry run"),
        stamp: Stamp::None,
        body: format!(
            "<p>Each leaf of <code>{name}</code>, its form filled with placeholders, assembled and planned by the shell (nothing runs against the Host). \
             <em>usage</em>: the grammar refused the form's line (the form and the parser disagree); <em>world</em>: the words parse, this workspace cannot plan them.</p>\
             <table class=\"dry\" data-leaves=\"{}\" data-errors=\"{errors}\" data-world=\"{world}\"><thead><tr><th>leaf</th><th>class</th><th>plan</th></tr></thead><tbody>{rows}</tbody></table>",
            alts.len()
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The research door: its form is derived from the grammar leaf (no hand-written HTML), and
    /// the words the verb page prints (`verb.operation`) carry the word "research" and the label.
    #[test]
    fn the_private_compute_form_is_derived_and_the_page_text_carries_the_research_label() {
        let verb = crate::shell::command_catalog().find(|v| v.name == "private-compute").expect("in the catalog");
        assert_eq!(verb.usage, "private-compute LEFT RIGHT");
        assert!(verb.operation.contains("RESEARCH") && verb.operation.contains(crate::private_compute::LABEL), "{}", verb.operation);
        let html = form_for("private-compute", "private-compute", "/verb/private-compute", "").expect("one leaf");
        assert!(html.contains("LEFT") && html.contains("RIGHT") && html.contains("name=\"a1\"") && html.contains("name=\"a2\""), "{html}");
        assert!(!transition_of("private-compute", verb.usage, verb.operation, 0, "private-compute"), "a local computation is not a transition");
        assert!(!html.contains("submit ID"), "never a proposal");
    }

    #[test]
    fn every_catalog_usage_parses_into_literal_led_alternatives() {
        let mut verbs = 0;
        for v in crate::shell::command_catalog() {
            verbs += 1;
            let alts = alternatives(v.usage);
            assert!(!alts.is_empty(), "{}", v.name);
            for alt in &alts {
                assert!(matches!(alt.tokens.first(), Some(Tok::Lit(_))), "{}: {:?}", v.name, alt);
            }
        }
        assert!(verbs > 60, "{verbs} verbs");
    }

    /// The tags of one kind in generated HTML: `<input …>`, `<select …>`, whole opening tags.
    fn tags(html: &str, kind: &str) -> Vec<String> {
        let mut out = Vec::new();
        let mut at = 0;
        while let Some(start) = html[at..].find(&format!("<{kind}")) {
            let start = at + start;
            let end = start + html[start..].find('>').unwrap_or(html[start..].len());
            out.push(html[start..=end].to_owned());
            at = end + 1;
        }
        out
    }

    /// `attr="value"` of one tag, unescaped-enough for ids and labels (ids are `[a-z0-9-]`).
    fn attr<'a>(tag: &'a str, name: &str) -> Option<&'a str> {
        let marker = format!("{name}=\"");
        let start = tag.find(&marker)? + marker.len();
        let end = tag[start..].find('"')? + start;
        Some(&tag[start..end])
    }

    /// Every leaf form of every verb labels its fields and holds page-unique ids: the
    /// accessibility contract of the derived forms, checked at the one place they render
    /// (a `label for` resolving past its own form is the failure this catches).
    #[test]
    fn web_leaf_forms_label_every_field() {
        let mut verbs = 0;
        let mut forms = 0;
        let mut controls = 0;
        for v in crate::shell::command_catalog() {
            verbs += 1;
            let alts = alternatives_of(v.name, v.usage);
            // The page a verb renders: one form per alternative, concatenated.
            let page: String = alts
                .iter()
                .enumerate()
                .map(|(i, alt)| form(v.name, i, alt, v.operation, &format!("/verb/{}", v.name), ""))
                .collect();
            assert!(!page.is_empty(), "{} renders no form", v.name);
            forms += alts.len();
            // Every id (fields, checkboxes, the submit box) appears once on the page.
            let mut ids: Vec<String> = Vec::new();
            for tag in ["input", "select", "textarea", "datalist"].iter().flat_map(|k| tags(&page, k)) {
                if let Some(id) = attr(&tag, "id") {
                    ids.push(id.to_owned());
                }
            }
            let mut sorted = ids.clone();
            sorted.sort_unstable();
            sorted.dedup();
            assert_eq!(sorted.len(), ids.len(), "{}: duplicate field ids on one page", v.name);
            let label_fors: Vec<String> = tags(&page, "label")
                .iter()
                .filter_map(|label| attr(label, "for").map(str::to_owned))
                .collect();
            for tag in ["input", "select", "textarea"].iter().flat_map(|k| tags(&page, k)) {
                if attr(&tag, "type") == Some("hidden") {
                    continue; // hidden fields carry no meaning to label
                }
                controls += 1;
                let labelled = attr(&tag, "aria-label").is_some_and(|a| !a.is_empty())
                    || attr(&tag, "id").is_some_and(|id| label_fors.iter().any(|f| f == id));
                assert!(labelled, "{}: unlabelled control: {tag}", v.name);
            }
            // Every `label for` names exactly one field of this page and says something.
            for id in &label_fors {
                let named = ids.iter().filter(|x| *x == id).count();
                assert_eq!(named, 1, "{}: label for={id} names {named} fields", v.name);
            }
        }
        assert!(verbs >= 60 && forms >= 200 && controls > 500, "{verbs} verbs, {forms} forms, {controls} controls");
    }

    #[test]
    fn grammar_shapes_render_and_assemble() {
        let alts = alternatives("delegate ID REF RECIPIENT VERB[,VERB...] MAX-COST");
        assert_eq!(alts.len(), 1);
        let t = &alts[0].tokens;
        assert_eq!(t[0], Tok::Lit("delegate".into()));
        assert_eq!(t[1], Tok::Arg { name: "ID".into(), optional: false, kind: Kind::Id });
        assert_eq!(t[2], Tok::Arg { name: "REF".into(), optional: false, kind: Kind::Ref });
        assert_eq!(t[5], Tok::Arg { name: "MAX-COST".into(), optional: false, kind: Kind::Number });
        assert!(alts[0].proposes("mini workspace --action propose (action delegate)"));
        let room = alternatives("room new NAME [--law open|realm] [--referee SUBJECT] [--in PARENT] | room new NAME --private [--in PARENT]");
        assert_eq!(room.len(), 2);
        assert_eq!(room[0].tokens[3], Tok::Flag { name: "--law".into(), value: Some(("open|realm".into(), Kind::Choice(vec!["open".into(), "realm".into()]))), optional: true });
        assert_eq!(room[1].tokens[3], Tok::Flag { name: "--private".into(), value: None, optional: false });
        let hist = alternatives("history [all] | doc transclude NAME SOURCE FROM TO [snapshot|live] [at N] | invoke ID REF create FIELD VALUE | pay ROOM week|N [--account REF] [again]");
        assert_eq!(hist.iter().map(|a| a.literals()).collect::<Vec<_>>(), ["history", "doc transclude", "invoke", "pay"]);
        assert_eq!(hist[0].tokens[1], Tok::Arg { name: "all".into(), optional: true, kind: Kind::Choice(vec!["all".into()]) });
        let law = alternatives("law ID REF \"CLAUSE; CLAUSE; …\"|PREDICATE-JSON|@FILE [--allow-unsatisfiable] | law show REF");
        assert_eq!(law[0].tokens[3], Tok::Arg { name: "\"CLAUSE; CLAUSE; …\"|PREDICATE-JSON|@FILE".into(), optional: false, kind: Kind::Text });
        assert_eq!(law[0].tokens[4], Tok::Flag { name: "--allow-unsatisfiable".into(), value: None, optional: true });
        assert_eq!(law[1].literals(), "law show");
        let chat = alternatives("chat new ROOM [--private: devnet quality; privacy not audited] | tail [-n N] [--since HEIGHT]");
        assert_eq!(chat[0].tokens[3], Tok::Flag { name: "--private".into(), value: None, optional: true });
        assert_eq!(chat[1].tokens[1], Tok::Flag { name: "-n".into(), value: Some(("N".into(), Kind::Number)), optional: true });
        let create = alternatives("create NAME STORAGE LAW|PREDICATE-JSON|@FILE [FIELDS|open] [--in ROOM]");
        assert_eq!(create[0].tokens[4], Tok::Arg { name: "FIELDS|open".into(), optional: true, kind: Kind::Word });
        let html = form("delegate", 0, &alts[0], "propose", "/verb/delegate", "");
        assert!(form_for("doc", "doc append", "/tour/3", "<input type=\"hidden\" name=\"verb\" value=\"doc\">").unwrap().contains("action=\"/tour/3\""));
        assert!(form_for("doc", "doc nope", "/x", "").is_none());
        let doc = crate::shell::command_catalog().find(|v| v.name == "doc").unwrap();
        let alts = alternatives_of("doc", doc.usage);
        let show = alts.iter().position(|a| a.literals() == "doc show").unwrap();
        let append = alts.iter().position(|a| a.literals() == "doc append").unwrap();
        assert!(!transition_of("doc", doc.usage, doc.operation, show, "doc show"), "doc show is a read");
        assert!(transition_of("doc", doc.usage, doc.operation, append, "doc append"), "doc append proposes");
        assert_eq!(alts.len(), crate::shell_grammar::DOC.leaves.len(), "one form per grammar leaf");
        // `bend`: one derived form per leaf; publish, run and answer are transitions, show and await reads.
        let bend = crate::shell::command_catalog().find(|v| v.name == "bend").expect("the shell has bend");
        let bends = alternatives_of("bend", bend.usage);
        assert_eq!(bends.iter().map(|a| a.literals()).collect::<Vec<_>>(), ["bend publish", "bend run", "bend lookup", "bend retry", "bend show", "bend await", "bend answer", "bend deliver", "bend settle"]);
        assert_eq!(bends.len(), crate::shell_grammar::BEND.leaves.len(), "one form per grammar leaf");
        // `apps`: one derived form per leaf, and `apps renew` is among them as a transition.
        let apps = crate::shell::command_catalog().find(|v| v.name == "apps").expect("the shell has apps");
        let app_alts = alternatives_of("apps", apps.usage);
        assert_eq!(app_alts.len(), crate::shell_grammar::APPS.leaves.len(), "one form per grammar leaf");
        let renew = app_alts.iter().position(|a| a.literals() == "apps renew").expect("apps renew has a derived form");
        assert!(transition_of("apps", apps.usage, apps.operation, renew, "apps renew"), "apps renew writes an enrollment");
        for (i, is) in [true, true, false, true, false, false, true, true].into_iter().enumerate() {
            assert_eq!(transition_of("bend", bend.usage, bend.operation, i, &bends[i].literals()), is, "{}", bends[i].literals());
        }
        assert!(form("bend", 1, &bends[1], bend.operation, "/verb/bend", "").contains("--deposit"), "bend run's form carries --deposit");
        assert_eq!(alts[append].tokens[4], Tok::Arg { name: "TEXT|@FILE".into(), optional: false, kind: Kind::Text });
        // The rendered usage parses to the same leaves as the grammar names (help and the forms agree).
        assert_eq!(alternatives(doc.usage).iter().map(|a| a.literals()).collect::<Vec<_>>(), alts.iter().map(|a| a.literals()).collect::<Vec<_>>());
        for (name, is) in [("whoami", false), ("help", false), ("history", false), ("can", false), ("inspect", false), ("refs", false), ("submit", true), ("delegate", true), ("create", true), ("retry", true)] {
            let v = crate::shell::command_catalog().find(|v| v.name == name).unwrap();
            assert_eq!(transition(v.usage, v.operation, 0, name), is, "{name}: {}", v.operation);
        }
        assert!(html.contains("name=\"a1\"") && html.contains("list=\"refs\"") && html.contains("name=\"submit\""), "{html}");
        // The page-unique ids: this form's fields are `delegate-0-*`, not the bare `a{i}`
        // (token 0 is the literal `delegate`, so the first field is index 1).
        assert!(html.contains("id=\"delegate-0-1\"") && html.contains("id=\"delegate-0-submit\""), "{html}");
    }

    fn bare_site() -> Site {
        Site {
            mutations: Mutex::new(()),
            refs: Mutex::new(None),
            home: None,
            root: std::env::temp_dir(),
            workspace: Value::Null,
            subject: "7".into(),
            token: String::new(),
            front: Front { origins: Vec::new(), read_only: false },
            base: String::new(),
            face: Face::Body,
            shell: None,
        }
    }

    /// The feedback form is derived from the verb's grammar, a link's query prefills it, and what
    /// the person submits assembles to the line the shell parses back to the same report.
    #[test]
    fn the_feedback_form_is_derived_prefilled_and_assembles_to_a_report() {
        let verb = crate::shell::command_catalog().find(|v| v.name == "feedback").expect("the shell has feedback");
        let alts = alternatives_of("feedback", verb.usage);
        assert_eq!(alts.len(), crate::shell_grammar::FEEDBACK.leaves.len(), "one form per grammar leaf");
        let clause = r#"refused: law-denied: field 2 "monotone" (before 2)"#;
        let target = format!("/verb/feedback?clause={}&from=w-abc&page=%2Fdoc%2Fpaper", super::super::body::pct(clause));
        let html = form_with("feedback", 0, &alts[0], verb.operation, "/verb/feedback", "", &|k| super::super::body::query(&target, k));
        assert!(html.contains("value=\"w-abc\"") && html.contains("value=\"/doc/paper\""), "{html}");
        assert!(html.contains(&format!("value=\"{}\"", escape(clause))), "{html}");
        let blank = form("feedback", 0, &alts[0], verb.operation, "/verb/feedback", "");
        assert!(!blank.contains("w-abc") && !blank.contains("/doc/paper"), "no prefill without a query");
        // The person types the text; the fields assemble, the free text last.
        let mut fields = std::collections::BTreeMap::new();
        fields.insert("alt".to_owned(), "0".to_owned());
        for (i, tok) in alts[0].tokens.iter().enumerate() {
            let value = match tok {
                Tok::Arg { .. } => "the save button is gone",
                Tok::Flag { name, .. } if name == "--from" => "w-abc",
                Tok::Flag { name, .. } if name == "--clause" => clause,
                Tok::Flag { name, .. } if name == "--page" => "/doc/paper",
                _ => continue,
            };
            fields.insert(format!("a{i}"), value.to_owned());
        }
        let site = bare_site();
        let (lines, _, transition, _) = assemble(&site, "feedback", &fields).unwrap_or_else(|_| panic!("assemble"));
        assert!(transition, "feedback is a world transition");
        assert_eq!(
            crate::chat::plan(&lines[0]).unwrap().unwrap(),
            crate::chat::Line::Feedback { text: "the save button is gone".into(), from: Some("w-abc".into()), clause: Some(clause.into()), page: Some("/doc/paper".into()), via: None },
            "{}", lines[0]
        );
    }

    /// A place's computed control still speaks the verb's grammar: the founder's ticked tools become
    /// `tariff ROOM set hermes/tools N`, assembled by the one assembler and parsed back by the shell's
    /// grammar to the set leaf (a transition), and a filled form carries what its place knows.
    #[test]
    fn named_values_assemble_through_the_grammar_and_filled_forms_carry_them() {
        let site = bare_site();
        let (lines, _, transition, literals) = assemble_named(&site, "tariff", "tariff", &[("ROOM", "lab"), ("set", "set"), ("hermes/tools", "hermes/tools"), ("N", "9")]).unwrap_or_else(|p| panic!("{}", p.body));
        assert_eq!((lines, transition, literals.as_str()), (vec!["tariff lab set hermes/tools 9".to_owned()], true, "tariff"));
        let words = crate::shell::words("tariff lab set hermes/tools 9").unwrap();
        let parsed = crate::shell_grammar::parse(&crate::shell_grammar::TARIFF, &words).expect("the shell parses what the face assembles");
        assert_eq!(parsed.leaf.effect, crate::shell_grammar::Effect::Transition);
        assert!(assemble_named(&site, "tariff", "tariff", &[("ROOM", "lab"), ("set", "set"), ("hermes/nothing", "hermes/nothing"), ("N", "9")]).is_err(), "a field the grammar does not list is no leaf");
        let join = form_for_filled("story", "story join", "/verb/story", "", &[("name", "tale"), ("invitationfile", "@tale-invite.json")]).unwrap();
        assert!(join.contains("value=\"tale\"") && join.contains("value=\"@tale-invite.json\"") && join.contains("action=\"/verb/story\""), "{join}");
        let answer = form_for_filled("bend", "bend answer", "/verb/bend", "", &[("slot", "5551")]).unwrap();
        assert!(answer.contains("value=\"5551\"") && answer.contains("<textarea"), "{answer}");
    }
}
