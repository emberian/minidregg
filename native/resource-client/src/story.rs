//! Stories (PLACE §2.8, item 8): a friend writes a transition table, seals it,
//! and from then on the table is the LAW on every player's cell.
//!
//! THE TABLE is a document in the story's room (`NAME/table`), one row per
//! line (`deploy/shell/templates/story/README.md` has the grammar):
//!   title TEXT | scene N TITLE | TEXT | start N | end N | item NAME N
//!   exit N WORD M [needs ITEM] | act N VERB M [needs ITEM]
//! `table_of` parses and checks it (fail closed: a dangling exit, an
//! unreachable scene, a dead end that is not an ending each refuse it, naming
//! the row).
//!
//! THE LAW. `player_law` generates, from the table, the law of one player's
//! cell. The cell's fields are `PLAYER_FIELDS` (`scene`, `turn`) and then
//! `carries/ITEM` per item, in name order (`player_fields`, the ONE list a
//! cell is born with). Clause 0 admits reads and writes only, so nobody can
//! install another law, delegate or revoke; every other clause judges a write:
//! mover (only the player), turn (+1 exactly), exits (stay, or one table
//! edge), needs (per conditional edge: its item already held), here and once
//! (per item: taken in its scene, standing still, 0 to 1 and never back), and
//! progress (a turn moves or takes). The Lean file `Assurance/StoryLaw.lean` defines the same law for every table and
//! proves `sealed_story_scene_monotone`; `scripts/gen-storylaw.py` embeds this
//! generator's output for the tale and the build proves it is that `law`.
//!
//! WHO DOES WHAT.
//!   story new NAME --from tale|@FILE [--gm S]   the author: the room (template
//!       `story`), the table document (only the author writes it), its rows,
//!       and the map's link to it. The scenes stream is the GM's (the author by
//!       default).
//!   story seal NAME     the author: the table's law becomes `tableSealed` (a
//!       write is refused `sealed`; no law replaces it). Players can join only
//!       a sealed story.
//!   story invite NAME S [gm]   the author: for a player, births NAME/p-S
//!       (born under a law only the author satisfies), writes its start
//!       fields, installs the player's sealed law, and grants S the room
//!       (observe, mutate, append: each cell's and stream's own law decides
//!       what a player may write, so a player's narrate is refused by the
//!       scenes law, by name). For the GM: the room with observe, append.
//!       Prints the line S types: `story join NAME INVITATION`.
//!   look | go WORD | take ITEM | act VERB | narrate TEXT   players and GM.
//! Every read is signed. Before a player plays, `look` checks that the table's
//! law is the sealed table law and that the player's cell carries exactly the
//! law the table generates for them (and, on a cell nobody has moved, that it
//! stands at the start), so the author cannot hand a player a cell under a
//! different law.
//!
//! WHY THE AUTHOR BIRTHS A PLAYER'S CELL. The room's birth gate judges a
//! placement with the request's slots only; nothing in it names the law the
//! new cell is born with. A cell a player bore themselves would carry whatever
//! law their client chose, so a skip would be one modified client away. The
//! author's birth, checked by the player's own `look`, is the kernel-enforced
//! shape this store allows.

use crate::chat::{
    client, entries_of, error, get_json, import_from, import_stream, os, private_dirs,
    propose_submit, put_json, reference, signed_read, usage, workspace_record, Done, Payload,
};
use crate::shell::{Session, Verb, EXIT_OK, EXIT_REFUSED};
use crate::workspace::member;
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::PathBuf;

/// The built-in tale's table.
pub(crate) const TALE: &str = include_str!("../../../deploy/shell/templates/story/tale/table");

/// The fields every player cell has before its items, in field order.
pub(crate) const PLAYER_FIELDS: [&str; 2] = ["scene", "turn"];

pub(crate) const VERBS: &[Verb] = &[
    Verb { name: "story", usage: "story new NAME --from tale|@FILE [--gm SUBJECT] | story seal NAME | story invite NAME SUBJECT [gm] | story join NAME INVITATION|@FILE | story enter NAME | story list | story law NAME|tale|@FILE [SUBJECT]", operation: "a story: a room, a table document the author seals, and one cell per player under the law the table generates; `help story`" },
    Verb { name: "look", usage: "look", operation: "signed reads: the table, my cell and both their laws; print my scene, its exits, items and the GM's last words" },
    Verb { name: "go", usage: "go EXIT|SCENE", operation: "one write to my cell: scene := the exit's scene, turn + 1 (the sealed law judges it)" },
    Verb { name: "take", usage: "take ITEM", operation: "one write to my cell: carries/ITEM := 1, turn + 1" },
    Verb { name: "act", usage: "act VERB", operation: "one write to my cell: scene := the act's scene, turn + 1" },
    Verb { name: "narrate", usage: "narrate TEXT", operation: "append {\"type\":\"say\",\"text\":TEXT} to the story's scenes stream (the GM's)" },
];

pub(crate) const HELP: &str = "\
story: a table you write and seal; then the table is the law on each player's cell.

The author:
  story new tale --from tale         the room, its map, the scenes stream, and the table
                                     document (--from @FILE: your own table in requests/)
  story law tale                     the law sealing will give each player, clause by clause
  story seal tale                    no one edits the table again; players may now join
  story invite tale SUBJECT          births SUBJECT's cell at the start, under the sealed law,
                                     and prints the line to give them
  story invite tale SUBJECT gm       the GM: may narrate
A player (or the GM):
  story join tale INVITATION         take the invitation (JSON, or @FILE in requests/)
  look                               where you are, the ways on, what lies here
  go north   take key   act open     one write each; the table decides
  narrate the door groans            the GM's voice (anyone else is refused)

A refusal names the clause of the law that refused it. The table cannot be
changed once sealed, and the law on your cell cannot be replaced by anyone.
";

// ---------------------------------------------------------------- the table

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Scene {
    pub n: i64,
    pub title: String,
    pub text: String,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Way {
    pub from: i64,
    pub word: String,
    pub to: i64,
    pub needs: Option<String>,
    /// `exit` (go WORD) or `act` (act WORD).
    pub act: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Table {
    pub title: String,
    pub scenes: Vec<Scene>,
    pub start: i64,
    pub ends: BTreeSet<i64>,
    /// name -> scene, in name order (the field order).
    pub items: BTreeMap<String, i64>,
    /// In (from, to) order: the law's edge order.
    pub ways: Vec<Way>,
}

fn word_ok(w: &str) -> bool {
    !w.is_empty() && w.len() <= 32 && w.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
        && !w.bytes().all(|b| b.is_ascii_digit())
}

fn scene_number(w: &str, row: usize) -> Result<i64, String> {
    w.parse::<i64>().ok().filter(|n| *n >= 0 && *n < 1_000_000).ok_or_else(|| format!("row {row}: {w} is not a scene number"))
}

/// The table's rows: its non-empty, non-`#` lines.
pub(crate) fn rows(text: &str) -> Vec<String> {
    text.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#')).map(str::to_owned).collect()
}

/// Parse and check a table (its rows, in any order).
pub(crate) fn table_of(rows: &[String]) -> Result<Table, String> {
    let mut title = None;
    let mut scenes: BTreeMap<i64, Scene> = BTreeMap::new();
    let mut start = None;
    let mut ends = BTreeSet::new();
    let mut items = BTreeMap::new();
    let mut ways: Vec<Way> = Vec::new();
    for (i, row) in rows.iter().enumerate() {
        let n = i + 1;
        let w: Vec<&str> = row.split_whitespace().collect();
        match w.first().copied() {
            Some("title") if w.len() > 1 => {
                if title.replace(w[1..].join(" ")).is_some() {
                    return Err(format!("row {n}: a second title"));
                }
            }
            Some("scene") if w.len() > 2 => {
                let s = scene_number(w[1], n)?;
                let rest = row.splitn(3, char::is_whitespace).nth(2).unwrap_or("").trim();
                let (t, text) = rest.split_once('|').ok_or_else(|| format!("row {n}: scene N TITLE | TEXT"))?;
                if t.trim().is_empty() || text.trim().is_empty() {
                    return Err(format!("row {n}: a scene has a title and a text"));
                }
                if scenes.insert(s, Scene { n: s, title: t.trim().to_owned(), text: text.trim().to_owned() }).is_some() {
                    return Err(format!("row {n}: scene {s} twice"));
                }
            }
            Some("start") if w.len() == 2 => {
                if start.replace(scene_number(w[1], n)?).is_some() {
                    return Err(format!("row {n}: a second start"));
                }
            }
            Some("end") if w.len() == 2 => {
                ends.insert(scene_number(w[1], n)?);
            }
            Some("item") if w.len() == 3 => {
                if !word_ok(w[1]) {
                    return Err(format!("row {n}: an item name is lower-case letters, digits and hyphens"));
                }
                if items.insert(w[1].to_owned(), scene_number(w[2], n)?).is_some() {
                    return Err(format!("row {n}: item {} twice", w[1]));
                }
            }
            Some(kind @ ("exit" | "act")) if w.len() == 4 || (w.len() == 6 && w[4] == "needs") => {
                if !word_ok(w[2]) {
                    return Err(format!("row {n}: {} is not a word (lower-case letters, digits, hyphens; not a number)", w[2]));
                }
                ways.push(Way {
                    from: scene_number(w[1], n)?,
                    word: w[2].to_owned(),
                    to: scene_number(w[3], n)?,
                    needs: w.get(5).map(|s| (*s).to_owned()),
                    act: kind == "act",
                });
            }
            _ => return Err(format!("row {n}: not a table row: {row}")),
        }
    }
    let title = title.ok_or("the table has no title row")?;
    let start = start.ok_or("the table has no start row")?;
    let known = |s: i64, what: &str| -> Result<(), String> {
        if scenes.contains_key(&s) { Ok(()) } else { Err(format!("{what} names scene {s}, which the table does not have")) }
    };
    known(start, "start")?;
    for e in &ends {
        known(*e, "end")?;
    }
    for (name, s) in &items {
        known(*s, &format!("item {name}"))?;
    }
    let mut pairs = BTreeSet::new();
    let mut words = BTreeSet::new();
    for w in &ways {
        let what = format!("{} {} {}", if w.act { "act" } else { "exit" }, w.from, w.word);
        known(w.from, &what)?;
        known(w.to, &what)?;
        if w.from == w.to {
            return Err(format!("{what} leads back to its own scene; a turn that stays is a take"));
        }
        if ends.contains(&w.from) {
            return Err(format!("{what} leaves scene {}, which is an end", w.from));
        }
        if let Some(item) = &w.needs {
            if !items.contains_key(item) {
                return Err(format!("{what} needs {item}, which no item row places"));
            }
        }
        if !pairs.insert((w.from, w.to)) {
            return Err(format!("two rows lead from scene {} to scene {}; one way per pair", w.from, w.to));
        }
        if !words.insert((w.from, w.act, w.word.clone())) {
            return Err(format!("{what}: the word is used twice in scene {}", w.from));
        }
    }
    let mut seen = BTreeSet::from([start]);
    let mut frontier = vec![start];
    while let Some(s) = frontier.pop() {
        for w in ways.iter().filter(|w| w.from == s) {
            if seen.insert(w.to) {
                frontier.push(w.to);
            }
        }
    }
    for s in scenes.keys() {
        if !seen.contains(s) {
            return Err(format!("scene {s} cannot be reached from the start"));
        }
        if !ends.contains(s) && !ways.iter().any(|w| w.from == *s) {
            return Err(format!("scene {s} has no way on and is not an end"));
        }
    }
    ways.sort_by_key(|w| (w.from, w.to));
    Ok(Table { title, scenes: scenes.into_values().collect(), start, ends, items, ways })
}

impl Table {
    fn scene(&self, n: i64) -> Option<&Scene> {
        self.scenes.iter().find(|s| s.n == n)
    }
    fn item_field(&self, name: &str) -> Option<u64> {
        self.items.keys().position(|k| k == name).map(|i| (PLAYER_FIELDS.len() + i) as u64)
    }
}

/// THE field list of a player's cell: `PLAYER_FIELDS`, then `carries/ITEM`
/// per item in name order. Field number = position.
pub(crate) fn player_fields(table: &Table) -> Vec<String> {
    PLAYER_FIELDS.iter().map(|f| (*f).to_owned()).chain(table.items.keys().map(|i| format!("carries/{i}"))).collect()
}

// ---------------------------------------------------------------- the laws

fn slot(n: u64, view: &str) -> String {
    format!("resource/field/{n}/{view}")
}
fn eq(s: &str, v: impl ToString) -> Value {
    json!({"type":"eq","slot":s,"value":v.to_string()})
}
fn not(p: Value) -> Value {
    json!({"type":"not","predicate":p})
}
fn any(ps: Vec<Value>) -> Value {
    json!({"type":"any","predicates":ps})
}
fn all(ps: Vec<Value>) -> Value {
    json!({"type":"all","predicates":ps})
}
fn write_guard() -> Value {
    not(eq("request/verb", 2))
}
/// A game clause: one of `xs`, or the request is not a write.
fn guard(mut xs: Vec<Value>) -> Value {
    xs.push(write_guard());
    any(xs)
}

/// One clause of a generated law: its name and its predicate.
pub(crate) struct Clause {
    pub name: String,
    pub predicate: Value,
}

/// The law of player `subject`'s cell (`subject` may be a placeholder such as
/// `{S}`, for the template files). Clause order is the refusal order and is
/// `Assurance/StoryLaw.lean`'s `clauses`.
pub(crate) fn player_clauses(table: &Table, subject: &str) -> Vec<Clause> {
    let c = |name: String, predicate: Value| Clause { name, predicate };
    let step = |w: &Way| all(vec![eq(&slot(0, "before"), w.from), eq(&slot(0, "after"), w.to)]);
    let mut out = vec![
        c("management".into(), any(vec![eq("request/verb", 1), eq("request/verb", 2)])),
        c("mover".into(), guard(vec![eq("request/subject", subject)])),
        c("turn".into(), guard(vec![eq(&slot(1, "delta"), 1)])),
        c(
            "exits".into(),
            guard(std::iter::once(eq(&slot(0, "delta"), 0)).chain(table.ways.iter().map(step)).collect()),
        ),
    ];
    for w in &table.ways {
        if let Some(item) = &w.needs {
            let f = table.item_field(item).expect("checked");
            out.push(c(
                format!("needs {item} ({} {} -> {})", if w.act { "act" } else { "exit" }, w.from, w.to),
                guard(vec![not(step(w)), eq(&slot(f, "before"), 1)]),
            ));
        }
    }
    for (item, scene) in &table.items {
        let f = table.item_field(item).expect("item");
        out.push(c(
            format!("here {item} (scene {scene})"),
            guard(vec![eq(&slot(f, "delta"), 0), all(vec![eq(&slot(0, "before"), scene), eq(&slot(0, "delta"), 0)])]),
        ));
    }
    for item in table.items.keys() {
        let f = table.item_field(item).expect("item");
        out.push(c(
            format!("once {item}"),
            guard(vec![eq(&slot(f, "delta"), 0), all(vec![eq(&slot(f, "before"), 0), eq(&slot(f, "after"), 1)])]),
        ));
    }
    out.push(c(
        "progress".into(),
        guard(
            std::iter::once(not(eq(&slot(0, "delta"), 0)))
                .chain(table.items.keys().map(|i| not(eq(&slot(table.item_field(i).expect("item"), "delta"), 0))))
                .collect(),
        ),
    ));
    out
}

pub(crate) fn player_law(table: &Table, subject: &str) -> Value {
    all(player_clauses(table, subject).into_iter().map(|c| c.predicate).collect())
}

/// The table document's law until `story seal`: only the author writes it.
pub(crate) fn table_open_law(author: &str) -> Value {
    guard(vec![eq("request/subject", author)])
}

/// The table document's law after `story seal`: a write is refused `sealed`;
/// only reads and writes are verbs it judges at all, so no law replaces it.
/// (`Assurance/StoryLaw.lean` `tableSealed`.)
pub(crate) fn table_sealed_law() -> Value {
    all(vec![guard(vec![any(vec![])]), json!({"type":"memberOf","slot":"request/verb","values":["1","2"]})])
}

/// A player's cell between its birth and its sealed law: only the author.
fn staging_law(author: &str) -> Value {
    any(vec![eq("request/verb", 1), eq("request/subject", author)])
}

/// The scenes stream: only the GM writes or appends.
fn scenes_law(gm: &str) -> Value {
    any(vec![not(json!({"type":"memberOf","slot":"request/verb","values":["2","7"]})), eq("request/subject", gm)])
}

// --------------------------------------------- rendering, as the Host renders

fn verb_name(v: &str) -> String {
    match v {
        "1" => "read", "2" => "write", "3" => "delegate", "4" => "install", "5" => "revoke", "7" => "append", "10" => "place",
        other => other,
    }
    .to_owned()
}

fn render_slot(s: &str) -> String {
    let p: Vec<&str> = s.split('/').collect();
    match p.as_slice() {
        ["resource", "field", n, "after"] => format!("field {n}"),
        ["resource", "field", n, view] => format!("field {n} {view}"),
        ["resource", "pair", a, b, "delta"] => format!("pair {a},{b} delta"),
        ["request", "subject"] => "subject".into(),
        ["request", "verb"] => "verb".into(),
        ["request", "cost"] => "cost".into(),
        _ => format!("slot {s:?}"),
    }
}

fn render_value(s: &str, v: &str) -> String {
    if s == "request/verb" { verb_name(v) } else { v.to_owned() }
}

/// A clause in the shell's grammar, as `Compiler/RefusalReason.lean`
/// `renderClause` writes it.
pub(crate) fn render(p: &Value) -> String {
    let s = |k: &str| p.get(k).and_then(Value::as_str).unwrap_or("");
    match s("type") {
        "eq" => format!("{} == {}", render_slot(s("slot")), render_value(s("slot"), s("value"))),
        "le" => format!("{} <= {}", render_slot(s("slot")), render_value(s("slot"), s("value"))),
        "memberOf" => format!(
            "{} in {{{}}}",
            render_slot(s("slot")),
            p["values"].as_array().into_iter().flatten().filter_map(Value::as_str).map(|v| render_value(s("slot"), v)).collect::<Vec<_>>().join(",")
        ),
        "monotone" | "writeOnce" => format!("{} {}", render_slot(s("slot")), s("type")),
        "not" => format!("not ({})", render(&p["predicate"])),
        t @ ("all" | "any") => {
            let kids: Vec<String> = p["predicates"].as_array().into_iter().flatten().map(render).collect();
            match (t, kids.is_empty()) {
                ("any", true) => "sealed".into(),
                ("all", true) => "open".into(),
                _ => format!("{t} [ {} ]", kids.join(", ")),
            }
        }
        other => format!("<{other}>"),
    }
}

/// What the Host explains a refused clause as (`LawLeaf.explained`): a
/// disjunction loses its write guards; a guarded single clause is that clause.
pub(crate) fn explained(p: &Value) -> Value {
    if p["type"] == "any" {
        let kids: Vec<Value> = p["predicates"].as_array().cloned().unwrap_or_default();
        let rest: Vec<Value> = kids.iter().filter(|k| **k != write_guard()).cloned().collect();
        return match rest.len() {
            1 if kids.len() > 1 => rest[0].clone(),
            n if n == kids.len() => p.clone(),
            _ => any(rest),
        };
    }
    p.clone()
}

/// The law as grammar text, one clause per line (`law.player` and `story law`).
pub(crate) fn grammar(clauses: &[Clause]) -> String {
    clauses.iter().map(|c| render(&c.predicate)).collect::<Vec<_>>().join(";\n") + "\n"
}

/// The clause a Host refusal names: the text after `law-denied: ` begins with
/// the clause as the Host explains it.
fn clause_named<'a>(clauses: &'a [Clause], refusal: &str) -> Option<(usize, &'a Clause)> {
    let said = refusal.split("law-denied: ").nth(1)?;
    clauses
        .iter()
        .enumerate()
        .filter(|(_, c)| {
            let text = render(&explained(&c.predicate));
            said.starts_with(&text) && matches!(said[text.len()..].chars().next(), None | Some(' ') | Some('\n'))
        })
        .max_by_key(|(_, c)| render(&explained(&c.predicate)).len())
}

/// `mini story-law --table FILE [--player S]`: the client's own parse and
/// generation, as JSON, for `scripts/gen-storylaw.py`.
pub(crate) fn law_command(mut args: crate::Args) -> crate::Result<()> {
    let file = args.required("table")?;
    let player = args.optional("player").map(|p| p.to_string_lossy().into_owned()).unwrap_or_else(|| "{S}".into());
    args.finish()?;
    let text = fs::read_to_string(&file).map_err(|e| format!("cannot read {}: {e}", file.to_string_lossy()))?;
    let table = table_of(&rows(&text))?;
    let clauses = player_clauses(&table, &player);
    let out = json!({
        "type": "mini-story-law-v1",
        "title": table.title,
        "fields": player_fields(&table),
        "edges": table.ways.iter().map(|w| json!([w.from, w.to,
            w.needs.as_ref().map(|i| table.items.keys().position(|k| k == i).expect("item"))])).collect::<Vec<_>>(),
        "items": table.items.values().collect::<Vec<_>>(),
        "clauses": clauses.iter().map(|c| json!({"name":c.name,"text":render(&c.predicate)})).collect::<Vec<_>>(),
        "player": player_law(&table, &player),
        "tableSealed": table_sealed_law(),
        "grammar": grammar(&clauses),
    });
    println!("{}", serde_json::to_string_pretty(&out).expect("JSON"));
    Ok(())
}

// ---------------------------------------------------------------- lines

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Line {
    New { name: String, from: String, gm: Option<String> },
    Seal(String),
    Invite { name: String, subject: String, gm: bool },
    Join { name: String, invitation: String },
    Enter(String),
    List,
    Law { from: String, subject: Option<String> },
    Look,
    Go(String),
    Take(String),
    Act(String),
    Narrate(String),
}

fn split(text: &str) -> Option<(&str, &str)> {
    let text = text.trim_start();
    if text.is_empty() {
        return None;
    }
    let end = text.find(char::is_whitespace).unwrap_or(text.len());
    Some((&text[..end], &text[end..]))
}

fn free_text(rest: &str) -> String {
    let t = rest.trim();
    for q in ['\'', '"'] {
        if t.len() >= 2 && t.starts_with(q) && t.ends_with(q) {
            return t[1..t.len() - 1].to_owned();
        }
    }
    t.to_owned()
}

fn story_name(w: &str) -> Result<String, String> {
    if w.is_empty() || w.len() > 24 || !w.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-') {
        return Err("a story's name is 1..24 letters, digits or hyphens".into());
    }
    Ok(w.to_owned())
}

fn subject_word(w: &str) -> Result<String, String> {
    if w.is_empty() || w.len() > 40 || !w.bytes().all(|b| b.is_ascii_digit()) {
        return Err(format!("{w} is not a subject (a decimal number)"));
    }
    Ok(w.to_owned())
}

pub(crate) fn plan(line: &str) -> Option<Result<Line, String>> {
    let (verb, rest) = split(line)?;
    let usage_of = |name: &str| VERBS.iter().find(|v| v.name == name).map(|v| v.usage).unwrap_or("").to_owned();
    let words: Vec<&str> = rest.split_whitespace().collect();
    let one = |name: &str| -> Result<String, String> {
        match words.as_slice() {
            [w] => Ok((*w).to_owned()),
            _ => Err(usage_of(name)),
        }
    };
    Some(match verb {
        "look" if words.is_empty() => Ok(Line::Look),
        "look" => Err(usage_of("look")),
        "go" => one("go").map(Line::Go),
        "take" => one("take").map(Line::Take),
        "act" => one("act").map(Line::Act),
        "narrate" => {
            let t = free_text(rest);
            if t.is_empty() || t.len() > 2048 { Err("narrate TEXT (1..2048 bytes)".into()) } else { Ok(Line::Narrate(t)) }
        }
        "story" => (|| -> Result<Line, String> {
            let u = usage_of("story");
            match words.as_slice() {
                ["new", name, rest @ ..] => {
                    let name = story_name(name)?;
                    let (mut from, mut gm) = (None, None);
                    let mut i = 0;
                    while i < rest.len() {
                        match (rest[i], rest.get(i + 1)) {
                            ("--from", Some(v)) if from.is_none() => from = Some((*v).to_owned()),
                            ("--gm", Some(v)) if gm.is_none() => gm = Some(subject_word(v)?),
                            _ => return Err(u),
                        }
                        i += 2;
                    }
                    Ok(Line::New { name, from: from.ok_or(u)?, gm })
                }
                ["seal", name] => Ok(Line::Seal(story_name(name)?)),
                ["invite", name, subject] => Ok(Line::Invite { name: story_name(name)?, subject: subject_word(subject)?, gm: false }),
                ["invite", name, subject, "gm"] => Ok(Line::Invite { name: story_name(name)?, subject: subject_word(subject)?, gm: true }),
                ["join", name, _, ..] => {
                    let invitation = rest.trim_start()[4..].trim_start()[name.len()..].trim().to_owned();
                    Ok(Line::Join { name: story_name(name)?, invitation })
                }
                ["enter", name] => Ok(Line::Enter(story_name(name)?)),
                ["list"] => Ok(Line::List),
                ["law", from] => Ok(Line::Law { from: (*from).to_owned(), subject: None }),
                ["law", from, subject] => Ok(Line::Law { from: (*from).to_owned(), subject: Some(subject_word(subject)?) }),
                _ => Err(u),
            }
        })(),
        _ => return None,
    })
}

// ---------------------------------------------------------------- records

fn story_dir(session: &Session) -> PathBuf {
    session.home.join("story")
}

fn record_path(session: &Session, name: &str) -> PathBuf {
    story_dir(session).join(format!("{name}.json"))
}

fn load(session: &Session, name: &str) -> Result<Value, Done> {
    get_json(&record_path(session, name))
        .ok_or_else(|| usage(format!("this session has no story {name} (story new, or story join)")))
}

fn current(session: &Session) -> Result<Value, Done> {
    let name = fs::read_to_string(story_dir(session).join("current"))
        .map(|s| s.trim().to_owned())
        .map_err(|_| usage("no current story: story enter NAME (story list shows yours)"))?;
    load(session, &name)
}

fn set_current(session: &Session, name: &str) -> Result<(), Done> {
    private_dirs(&story_dir(session)).map_err(error)?;
    let path = story_dir(session).join("current");
    let _ = fs::remove_file(&path);
    crate::workspace::private_file(&path, format!("{name}\n").as_bytes()).map_err(error)
}

fn field<'a>(record: &'a Value, key: &str) -> Result<&'a str, Done> {
    record.get(key).and_then(Value::as_str).ok_or_else(|| error(format!("the story record lacks {key}")))
}

fn me(session: &Session) -> Result<String, Done> {
    let ws = workspace_record(session).map_err(error)?;
    Ok(member(&ws, "subject").map_err(error)?.to_owned())
}

/// A table source: `tale` (built in) or `@FILE` (HOME/requests/FILE).
fn source(session: &Session, from: &str) -> Result<String, Done> {
    if from == "tale" {
        return Ok(TALE.to_owned());
    }
    let file = from.strip_prefix('@').ok_or_else(|| usage("--from tale, or --from @FILE (a table in HOME/requests/)"))?;
    if file.is_empty() || file.contains('/') || file.starts_with('.') {
        return Err(usage("@FILE is a plain file name in HOME/requests"));
    }
    let path = session.home.join("requests").join(file);
    fs::read_to_string(&path).map_err(|e| error(format!("cannot read {}: {e}", path.display())))
}

// ---------------------------------------------------------------- reads

/// A signed read of a cell under the story's room with my room grant.
fn read(session: &Session, story: &Value, label: &str, target: &str, view: &str) -> Result<Value, Done> {
    let ws = workspace_record(session).map_err(error)?;
    let grant = reference(session, field(story, "grant")?).map_err(error)?;
    let synthetic = json!({"kind":"object","target":target,
        "observeCapability":member(&grant, "observeCapability").map_err(error)?});
    signed_read(session, &ws, &format!("story-{}", field(story, "story")?), label, &synthetic, view, &[])
}

/// The table's rows, from a signed read of its document (struck lines are not rows).
fn table_rows(view: &Value) -> Result<Vec<String>, Done> {
    let cell = view.get("cell").ok_or_else(|| error("the table read has no cell"))?;
    let mut atoms: Vec<&Value> = cell
        .get("entries")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter(|e| e.get("type").and_then(Value::as_str) == Some("atom"))
        .filter(|e| e.get("tombstonedAt").map_or(true, Value::is_null))
        .collect();
    atoms.sort_by_key(|e| {
        let id = e.get("id").and_then(Value::as_str).unwrap_or("").to_owned();
        (id.len(), id)
    });
    let mut out = Vec::new();
    for a in atoms {
        let hex = a.get("payload").and_then(Value::as_str).unwrap_or("");
        let bytes: Option<Vec<u8>> = (0..hex.len()).step_by(2).map(|i| u8::from_str_radix(hex.get(i..i + 2)?, 16).ok()).collect();
        let text = bytes.and_then(|b| String::from_utf8(b).ok()).ok_or_else(|| error("a table row is not UTF-8 text"))?;
        out.extend(rows(&text));
    }
    Ok(out)
}

fn fields_of(view: &Value) -> BTreeMap<u64, i64> {
    view.pointer("/cell/entries")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(|e| {
            Some((e.pointer("/key/field")?.as_str()?.parse().ok()?, e.get("value")?.as_str()?.parse().ok()?))
        })
        .collect()
}

/// A sealed story needs this local law on every step, including policy
/// replacement. Additional parents and exports may restrict it further.
fn carries_unconditional_local_law(policy: &Value, expected: &Value) -> bool {
    if policy.get("predicate") != Some(expected) {
        return false;
    }
    let Some(selector) = policy.get("localSelector").and_then(Value::as_object) else {
        return false;
    };
    selector.iter().all(|(key, value)| {
        matches!(key.as_str(), "physicalKinds" | "requestKinds" | "verbs") && value.is_null()
    })
}

/// The sealed table, read and checked: its rows parse, and its law is the
/// sealed table law.
fn sealed_table(session: &Session, story: &Value) -> Result<Table, Done> {
    let target = field(story, "table")?;
    let rows = table_rows(&read(session, story, "table", target, "resource")?)?;
    let table = table_of(&rows).map_err(|e| error(format!("the table does not parse: {e}")))?;
    let policy = read(session, story, "table-law", target, "policy")?;
    if !carries_unconditional_local_law(&policy, &table_sealed_law()) {
        return Err(error(format!(
            "the table of {} is not sealed (its sealed table law must apply to every step); a story is played only once sealed",
            field(story, "story")?
        )));
    }
    Ok(table)
}

// ---------------------------------------------------------------- running

pub(crate) fn run(session: &Session, line: Line) -> Done {
    match run_inner(session, line) {
        Ok(()) => (EXIT_OK, String::new()),
        Err(done) => done,
    }
}

fn run_inner(session: &Session, line: Line) -> Result<(), Done> {
    match line {
        Line::New { name, from, gm } => story_new(session, &name, &from, gm),
        Line::Seal(name) => story_seal(session, &name),
        Line::Invite { name, subject, gm } => story_invite(session, &name, &subject, gm),
        Line::Join { name, invitation } => story_join(session, &name, &invitation),
        Line::Enter(name) => {
            load(session, &name)?;
            set_current(session, &name)?;
            println!("{name} is your current story");
            Ok(())
        }
        Line::List => {
            let cur = fs::read_to_string(story_dir(session).join("current")).unwrap_or_default();
            let mut names: Vec<String> = fs::read_dir(story_dir(session))
                .into_iter()
                .flatten()
                .flatten()
                .filter_map(|e| e.file_name().to_string_lossy().strip_suffix(".json").map(str::to_owned))
                .collect();
            names.sort();
            for n in names {
                let r = load(session, &n)?;
                println!("{}{n}\t{}", if cur.trim() == n { "* " } else { "  " }, r["role"].as_str().unwrap_or("?"));
            }
            Ok(())
        }
        Line::Law { from, subject } => {
            let text = match from.as_str() {
                "tale" => TALE.to_owned(),
                f if f.starts_with('@') => source(session, f)?,
                name => {
                    let story = load(session, name)?;
                    table_rows(&read(session, &story, "table", field(&story, "table")?, "resource")?)?.join("\n")
                }
            };
            let table = table_of(&rows(&text)).map_err(usage)?;
            let s = subject.unwrap_or_else(|| "{S}".into());
            println!("# {}: the law on player {s}'s cell; fields {}", table.title,
                player_fields(&table).iter().enumerate().map(|(i, f)| format!("{i} {f}")).collect::<Vec<_>>().join(", "));
            for (i, c) in player_clauses(&table, &s).iter().enumerate() {
                println!("# clause {i}: {}", c.name);
                println!("{}{}", render(&c.predicate), if i + 1 < player_clauses(&table, &s).len() { ";" } else { "" });
            }
            Ok(())
        }
        Line::Look => look(session),
        Line::Go(w) => mv(session, Move::Go(w)),
        Line::Take(i) => mv(session, Move::Take(i)),
        Line::Act(v) => mv(session, Move::Act(v)),
        Line::Narrate(t) => narrate(session, &t),
    }
}

fn create(session: &Session, name: &str, storage: &str, law: &Value, room: &str) -> Result<Value, Done> {
    crate::chat::create_cell(session, name, storage, law, Some(room), None)
}

fn install(session: &Session, name: &str, law: &Value) -> Result<(), Done> {
    propose_submit(
        session,
        "law",
        &json!({"type":"minidregg-workspace-proposal-v1","action":"install-policy","name":name,"predicate":law}),
    )
    .map(|_| ())
}

fn story_new(session: &Session, name: &str, from: &str, gm: Option<String>) -> Result<(), Done> {
    if record_path(session, name).exists() {
        return Err(usage(format!("this session already has a story {name}")));
    }
    let text = source(session, from)?;
    let table = table_of(&rows(&text)).map_err(|e| usage(format!("the table refuses: {e}")))?;
    let author = me(session)?;
    let (code, _) = crate::shell::line(session, &format!("room new {name} --template story"));
    if code != EXIT_OK {
        return Err((code, format!("story {name}: the room template stopped; nothing after it was done\n")));
    }
    let gm = gm.unwrap_or_else(|| author.clone());
    if gm != author {
        install(session, &format!("{name}/scenes"), &scenes_law(&gm))?;
    }
    let table_ref = create(session, &format!("{name}/table"), "content", &table_open_law(&author), name)?;
    let actions: Vec<Value> = rows(&text).iter().map(|r| json!({"type":"append","text":r})).collect();
    propose_submit(
        session,
        "table",
        &json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
            "targets":[{"name":format!("{name}/table"),"payload":{"type":"document","actions":actions}}]}),
    )?;
    propose_submit(
        session,
        "map",
        &json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
            "targets":[{"name":format!("{name}/index"),"payload":{"type":"document",
                "actions":[{"type":"link","to":format!("{name}/table"),"relation":"0"}]}}]}),
    )?;
    let room = reference(session, name).map_err(error)?;
    let scenes = reference(session, &format!("{name}/scenes")).map_err(error)?;
    put_json(
        &record_path(session, name),
        &json!({"type":"mini-story-v1","story":name,"role":"author","author":author,"gm":gm,"grant":name,
            "room":member(&room,"target").map_err(error)?,
            "table":member(&table_ref,"target").map_err(error)?,
            "scenes":member(&scenes,"target").map_err(error)?}),
    )
    .map_err(error)?;
    set_current(session, name)?;
    println!(
        "story {name}: {} ({} scenes, {} ways, {} items); the table is {name}/table, only you write it until `story seal {name}`; the GM is {gm}",
        table.title,
        table.scenes.len(),
        table.ways.len(),
        table.items.len()
    );
    Ok(())
}

fn story_seal(session: &Session, name: &str) -> Result<(), Done> {
    let story = load(session, name)?;
    if story["role"] != "author" {
        return Err(usage(format!("only the author of {name} seals it")));
    }
    let target = field(&story, "table")?;
    let rows = table_rows(&read(session, &story, "table", target, "resource")?)?;
    let table = table_of(&rows).map_err(|e| usage(format!("the table refuses: {e}")))?;
    install(session, &format!("{name}/table"), &table_sealed_law())?;
    let clauses = player_clauses(&table, "{S}");
    println!("story {name} sealed: the table cannot be edited or re-lawed by anyone. Each player's cell will carry:");
    for (i, c) in clauses.iter().enumerate() {
        println!("  {i:>2} {:<28} {}", c.name, render(&explained(&c.predicate)));
    }
    Ok(())
}

fn grant(session: &Session, room: &str, recipient: &str, verbs: &[&str]) -> Result<Value, Done> {
    let done = propose_submit(
        session,
        "grant",
        &json!({"type":"minidregg-workspace-proposal-v1","action":"delegate","name":room,
            "recipient":recipient,"verbs":verbs,"maxCost":"50000","room":true}),
    )?;
    let id = done["id"].as_str().unwrap_or_default().to_owned();
    let ws = &session.workspace;
    client(
        "workspace",
        &[("action", os("publish-delegation")), ("dir", os(ws)), ("proposal-id", os(&id)), ("attempt", os(ws.join("attempts").join(&id)))],
    )?;
    get_json(&ws.join("proposals").join(&id).join("recipient-reference.json"))
        .ok_or_else(|| error("the published delegation left no recipient-reference.json"))
}

fn story_invite(session: &Session, name: &str, subject: &str, as_gm: bool) -> Result<(), Done> {
    let story = load(session, name)?;
    if story["role"] != "author" {
        return Err(usage(format!("only the author of {name} invites")));
    }
    let table = sealed_table(session, &story)?;
    let mut invitation = json!({"type":"mini-story-invitation-v1","story":name,
        "author":story["author"],"gm":story["gm"],"table":story["table"],"scenes":story["scenes"]});
    if as_gm {
        if story["gm"].as_str() != Some(subject) {
            return Err(usage(format!("{subject} is not {name}'s GM (story new {name} --gm SUBJECT names it)")));
        }
        invitation["role"] = json!("gm");
        invitation["grant"] = grant(session, name, subject, &["observe", "append"])?;
    } else {
        let cell = format!("{name}/p-{subject}");
        let author = field(&story, "author")?.to_owned();
        // THE field list: born, then written, in `player_fields` order.
        let fields = player_fields(&table);
        let declared = format!("0-{}", fields.len() - 1);
        let born = crate::chat::create_cell_with_fields(session, &cell, "declared",
            &staging_law(&author), Some(name), None, Some(&declared))?;
        let target = member(&born, "target").map_err(error)?.to_owned();
        // A declared cell is born holding some fields (field 1, today): each
        // start value is a create where the field is absent and a write from
        // what the birth left where it is present.
        let held = fields_of(&read(session, &story, "born", &target, "resource")?);
        let actions: Vec<Value> = (0..fields.len() as u64)
            .filter_map(|f| {
                let value = if f == 0 { table.start } else { 0 };
                let key = json!({"type":"object","field":f.to_string()});
                match held.get(&f) {
                    None => Some(json!({"type":"create","key":key,"value":value.to_string()})),
                    Some(v) if *v == value => None,
                    Some(v) => Some(json!({"type":"write","key":key,"value":value.to_string(),"expected":v.to_string()})),
                }
            })
            .collect();
        propose_submit(
            session,
            "start",
            &json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
                "targets":[{"name":cell,"payload":{"type":"scalar","actions":actions}}]}),
        )?;
        install(session, &cell, &player_law(&table, subject))?;
        invitation["role"] = json!("player");
        invitation["cell"] = json!(target);
        invitation["grant"] = grant(session, name, subject, &["observe", "mutate", "append"])?;
    }
    let path = story_dir(session).join("invites").join(format!("{name}-{subject}.json"));
    put_json(&path, &invitation).map_err(error)?;
    println!(
        "invited {subject} to {name} as {}{}; give them this line:",
        invitation["role"].as_str().unwrap_or("?"),
        invitation.get("cell").and_then(Value::as_str).map(|c| format!(" (their cell {c}, at scene {}, under the sealed law)", table.start)).unwrap_or_default()
    );
    println!("story join {name} {}", serde_json::to_string(&invitation).expect("JSON"));
    Ok(())
}

fn story_join(session: &Session, name: &str, invitation: &str) -> Result<(), Done> {
    let value: Value = if let Some(file) = invitation.strip_prefix('@') {
        if file.is_empty() || file.contains('/') || file.starts_with('.') {
            return Err(usage("@FILE is a plain file name in HOME/requests"));
        }
        let p = session.home.join("requests").join(file);
        serde_json::from_slice(&fs::read(&p).map_err(|e| error(format!("cannot read {}: {e}", p.display())))?)
            .map_err(|e| usage(format!("the invitation is not JSON: {e}")))?
    } else {
        serde_json::from_str(invitation).map_err(|e| usage(format!("the invitation is not JSON: {e}")))?
    };
    let me = me(session)?;
    if value["type"] != "mini-story-invitation-v1" || value["story"].as_str() != Some(name) {
        return Err(usage(format!("this is not an invitation to {name}")));
    }
    if value.pointer("/grant/recipient").and_then(Value::as_str) != Some(me.as_str()) {
        return Err(usage(format!("this invitation is not addressed to you ({me})")));
    }
    import_from(session, name, &value["grant"])?;
    let grant = reference(session, name).map_err(error)?;
    let capability = member(&grant, "observeCapability").map_err(error)?.to_owned();
    let s = |k: &str| value.get(k).and_then(Value::as_str).map(str::to_owned).ok_or_else(|| usage(format!("the invitation lacks {k}")));
    import_stream(session, &format!("{name}/scenes"), &s("scenes")?, &capability)?;
    let mut record = json!({"type":"mini-story-v1","story":name,"role":s("role")?,"author":s("author")?,"gm":s("gm")?,
        "grant":name,"table":s("table")?,"scenes":s("scenes")?});
    if value["role"] == "player" {
        import_stream(session, &format!("{name}/me"), &s("cell")?, &capability)?;
        record["cell"] = json!(s("cell")?);
    }
    put_json(&record_path(session, name), &record).map_err(error)?;
    set_current(session, name)?;
    println!("joined {name} as {}; it is your current story (look)", record["role"].as_str().unwrap_or("?"));
    Ok(())
}

/// My cell, read and checked: its law is the one the table generates for me,
/// and a cell nobody has moved stands at the start.
fn my_cell(session: &Session, story: &Value, table: &Table) -> Result<BTreeMap<u64, i64>, Done> {
    let me = me(session)?;
    let cell = field(story, "cell")?;
    let policy = read(session, story, "cell-law", cell, "policy")?;
    if !carries_unconditional_local_law(&policy, &player_law(table, &me)) {
        return Err(error(format!(
            "your cell {cell} does not carry the unconditional law the sealed table gives you; do not play it (story law {} {me} prints that law)",
            field(story, "story")?
        )));
    }
    let fields = fields_of(&read(session, story, "cell", cell, "resource")?);
    let n = player_fields(table).len() as u64;
    if (0..n).any(|f| !fields.contains_key(&f)) {
        return Err(error(format!("your cell {cell} lacks a field the table declares")));
    }
    if fields[&1] == 0 && (fields[&0] != table.start || (2..n).any(|f| fields[&f] != 0)) {
        return Err(error(format!("your cell {cell} was not born at the start (turn 0 at scene {})", fields[&0])));
    }
    Ok(fields)
}

fn print_scene(table: &Table, fields: &BTreeMap<u64, i64>) {
    let at = fields[&0];
    let Some(scene) = table.scene(at) else {
        println!("you are at scene {at}, which the table does not have");
        return;
    };
    println!("{} — {} (scene {at}, turn {})", table.title, scene.title, fields[&1]);
    println!("{}", scene.text);
    let carried: Vec<&String> = table.items.keys().filter(|i| table.item_field(i).is_some_and(|f| fields.get(&f) == Some(&1))).collect();
    let here: Vec<&String> = table.items.iter().filter(|(i, s)| **s == at && !carried.contains(i)).map(|(i, _)| i).collect();
    if !here.is_empty() {
        println!("here: {}", here.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", "));
    }
    for w in table.ways.iter().filter(|w| w.from == at) {
        let title = table.scene(w.to).map(|s| s.title.as_str()).unwrap_or("?");
        let needs = w.needs.as_ref().map(|i| format!(" (needs {i})")).unwrap_or_default();
        println!("  {} {:<10} {title}{needs}", if w.act { "act" } else { "go " }, w.word);
    }
    if !carried.is_empty() {
        println!("you carry: {}", carried.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", "));
    }
    if table.ends.contains(&at) {
        println!("THE END. (This is one of the story's endings; the table has no way on.)");
    }
}

fn narration(session: &Session, story: &Value) -> Vec<String> {
    let Ok(target) = field(story, "scenes") else { return vec![] };
    let ws = match workspace_record(session) {
        Ok(w) => w,
        Err(_) => return vec![],
    };
    let Ok(grant) = reference(session, story["grant"].as_str().unwrap_or("")) else { return vec![] };
    let synthetic = json!({"kind":"object","target":target,"observeCapability":grant.get("observeCapability")});
    let room = format!("story-{}", story["story"].as_str().unwrap_or(""));
    let Ok(view) = signed_read(session, &ws, &room, "scenes", &synthetic, "tail", &[("start", "1".into()), ("count", "256".into())]) else {
        return vec![];
    };
    entries_of(&view, target, story["gm"].as_str().unwrap_or(""))
        .into_iter()
        .filter_map(|e| match e.payload {
            Payload::Verified(t) => serde_json::from_str::<Value>(&t).ok()?.get("text")?.as_str().map(|s| format!("h{} {}", e.height, s)),
            _ => None,
        })
        .collect()
}

fn look(session: &Session) -> Result<(), Done> {
    let story = current(session)?;
    let table = sealed_table(session, &story)?;
    if story["role"] == "player" {
        let fields = my_cell(session, &story, &table)?;
        print_scene(&table, &fields);
    } else {
        println!("{} — you are its {}; {} scenes, start {}", table.title, story["role"].as_str().unwrap_or("?"), table.scenes.len(), table.start);
        for s in &table.scenes {
            println!("  scene {} {}{}", s.n, s.title, if table.ends.contains(&s.n) { " (an end)" } else { "" });
        }
    }
    let said = narration(session, &story);
    for line in said.iter().skip(said.len().saturating_sub(3)) {
        println!("the GM: {line}");
    }
    Ok(())
}

enum Move {
    Go(String),
    Take(String),
    Act(String),
}

fn mv(session: &Session, m: Move) -> Result<(), Done> {
    let story = current(session)?;
    if story["role"] != "player" {
        return Err(usage("you have no cell in this story (you are not a player)"));
    }
    let table = sealed_table(session, &story)?;
    let fields = my_cell(session, &story, &table)?;
    let (at, turn) = (fields[&0], fields[&1]);
    let w = |f: u64, value: i64, expected: i64| {
        json!({"type":"write","key":{"type":"object","field":f.to_string()},"value":value.to_string(),"expected":expected.to_string()})
    };
    let (what, action) = match &m {
        Move::Go(word) | Move::Act(word) => {
            let act = matches!(m, Move::Act(_));
            let way = table.ways.iter().find(|w| w.from == at && w.act == act && &w.word == word);
            let to = match way {
                Some(w) => w.to,
                // Not a way from here: a scene by number goes to the law as
                // asked (and the law decides); anything else is not a move.
                None => match word.parse::<i64>() {
                    Ok(n) if !act => n,
                    _ => return Err(usage(format!("no {} {word} from {}", if act { "act" } else { "exit" }, table.scene(at).map(|s| s.title.as_str()).unwrap_or("here")))),
                },
            };
            (format!("{} {word}", if act { "act" } else { "go" }), w(0, to, at))
        }
        Move::Take(item) => {
            let f = table.item_field(item).ok_or_else(|| usage(format!("the table has no item {item}")))?;
            (format!("take {item}"), w(f, 1, fields[&f]))
        }
    };
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":[{"name":format!("{}/me", field(&story, "story")?),"payload":{"type":"scalar",
            "actions":[action, w(1, turn + 1, turn)]}}]});
    match propose_submit(session, "move", &request) {
        Ok(_) => {
            println!("{what}: admitted");
            let fields = my_cell(session, &story, &table)?;
            print_scene(&table, &fields);
            Ok(())
        }
        Err((code, text)) if code == EXIT_REFUSED => {
            let me = me(session)?;
            let clauses = player_clauses(&table, &me);
            let named = clause_named(&clauses, &text)
                .map(|(i, c)| format!("  the table's clause {i}: {}\n", c.name))
                .unwrap_or_default();
            Err((code, format!("{text}{named}")))
        }
        Err(done) => Err(done),
    }
}

fn narrate(session: &Session, text: &str) -> Result<(), Done> {
    let story = current(session)?;
    let name = field(&story, "story")?;
    let payload = serde_json::to_string(&json!({"type":"say","text":text})).expect("JSON");
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":[{"name":format!("{name}/scenes"),"payload":{"type":"append","topic":"","text":payload}}]});
    propose_submit(session, "narrate", &request)?;
    println!("narrated in {name}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tale() -> Table {
        table_of(&rows(TALE)).expect("the tale parses")
    }

    #[test]
    fn sealed_law_recognition_rejects_selector_bypasses() {
        let expected = table_sealed_law();
        let mut policy = json!({"predicate": expected.clone(), "localSelector": {
            "physicalKinds": null, "requestKinds": null, "verbs": null}});
        assert!(carries_unconditional_local_law(&policy, &expected));
        for field in ["physicalKinds", "requestKinds", "verbs"] {
            policy["localSelector"][field] = json!(["1", "2"]);
            assert!(!carries_unconditional_local_law(&policy, &expected));
            policy["localSelector"][field] = json!([]);
            assert!(!carries_unconditional_local_law(&policy, &expected));
            policy["localSelector"][field] = Value::Null;
        }
        policy.as_object_mut().unwrap().remove("localSelector");
        assert!(!carries_unconditional_local_law(&policy, &expected));
    }

    #[test]
    fn sealed_law_recognition_keeps_additional_inherited_restrictions() {
        let expected = player_law(&tale(), "7");
        let policy = json!({"predicate": expected.clone(), "localSelector": {
            "physicalKinds": null, "requestKinds": null, "verbs": null},
            "parents": [{"policyId": "99", "facet": "descendants",
                "selection": {"type": "head"}}],
            "descendants": {"selector": {}, "predicate": {"type": "any", "predicates": []},
                "parents": []}});
        assert!(carries_unconditional_local_law(&policy, &expected));
        assert!(!carries_unconditional_local_law(&policy, &table_sealed_law()));
    }

    #[test]
    fn the_tale_parses_into_its_table() {
        let t = tale();
        assert_eq!(t.scenes.len(), 5);
        assert_eq!(t.start, 0);
        assert_eq!(t.ends, BTreeSet::from([2, 4]));
        assert_eq!(player_fields(&t), vec!["scene", "turn", "carries/key"]);
        let edges: Vec<(i64, i64, bool)> = t.ways.iter().map(|w| (w.from, w.to, w.needs.is_some())).collect();
        assert_eq!(edges, vec![(0, 1, false), (1, 2, false), (1, 3, true), (3, 4, false)]);
    }

    #[test]
    fn a_bad_table_is_refused_naming_its_row() {
        let base = rows(TALE);
        let with = |extra: &str| {
            let mut r = base.clone();
            r.push(extra.to_owned());
            table_of(&r)
        };
        assert!(with("exit 2 back 0").unwrap_err().contains("is an end"));
        assert!(with("exit 0 west 9").unwrap_err().contains("scene 9"));
        assert!(with("exit 3 down 1 needs lamp").unwrap_err().contains("needs lamp"));
        assert!(with("act 0 north 2").is_ok());
        assert!(with("exit 0 up 1").unwrap_err().contains("one way per pair"));
        assert!(with("castle").unwrap_err().contains("not a table row"));
        assert!(with("scene 7 Lost | nowhere").unwrap_err().contains("cannot be reached"));
    }

    /// The generated law's grammar text is what the shell's parser reads back
    /// to the same JSON: the text a friend sees is the law installed.
    #[test]
    fn story_law_grammar_is_its_json() {
        let t = tale();
        let clauses = player_clauses(&t, "7");
        assert_eq!(crate::shell::law::parse(&grammar(&clauses)).unwrap(), player_law(&t, "7"));
        assert_eq!(crate::shell::law::parse(&render(&table_sealed_law())).unwrap(), table_sealed_law());
        assert_eq!(clauses.len(), 8);
        assert_eq!(render(&explained(&clauses[3].predicate)),
            "any [ field 0 delta == 0, all [ field 0 before == 0, field 0 == 1 ], all [ field 0 before == 1, field 0 == 2 ], all [ field 0 before == 1, field 0 == 3 ], all [ field 0 before == 3, field 0 == 4 ] ]");
    }

    #[test]
    fn a_refusal_is_named_by_its_clause() {
        let clauses = player_clauses(&tale(), "7");
        let said = "refused: law-denied: field 1 delta == 1 (value -1) (Host refused prepare, reply byte 255)";
        assert_eq!(clause_named(&clauses, said).map(|(i, c)| (i, c.name.as_str())), Some((2, "turn")));
        let said = "refused: law-denied: any [ not (all [ field 0 before == 1, field 0 == 3 ]), field 2 before == 1 ] (Host refused prepare, reply byte 255)";
        assert_eq!(clause_named(&clauses, said).map(|(i, _)| i), Some(4));
        assert_eq!(render(&explained(&guard(vec![any(vec![])]))), "sealed");
    }

    #[test]
    fn story_lines_plan() {
        assert_eq!(plan("look").unwrap().unwrap(), Line::Look);
        assert_eq!(plan("go north").unwrap().unwrap(), Line::Go("north".into()));
        assert_eq!(plan("narrate 'the door groans'").unwrap().unwrap(), Line::Narrate("the door groans".into()));
        assert_eq!(plan("story new tale --from tale --gm 42").unwrap().unwrap(),
            Line::New { name: "tale".into(), from: "tale".into(), gm: Some("42".into()) });
        assert_eq!(plan("story join tale {\"a\": 1}").unwrap().unwrap(),
            Line::Join { name: "tale".into(), invitation: "{\"a\": 1}".into() });
        assert!(plan("go").unwrap().is_err());
        assert!(plan("story invite tale bob").unwrap().is_err());
        assert!(plan("say hi").is_none());
    }
}
