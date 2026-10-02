//! The one document renderer: `render(view) -> Rendered`, with a text backend
//! (`doc show`, `doc outline`, `doc backlinks`) and an HTML backend (`mini web`).
//!
//! Input is what the kernel already decided: the Host's `inspect view-document`
//! (the tree's pre-order walk, each row's live marks with the Host's `fresh`,
//! each transclusion rendered over the reader's own source reads), the host
//! cell's signed entries (annotations, atom kinds), and this workspace's
//! reference names.  Nothing here re-derives order, freshness or readability.
//!
//! The notation is lossy by design: `**two**` in a rendering does not say
//! whether the line holds one bold mark or fifty, nor which is stale beside a
//! fresh one, and a body that itself contains `**` reads the same as a mark.
//! There is no parser back from the notation.  `--format raw` is the byte-exact
//! form: the document's own live atoms, one per line.

pub mod history;
pub mod html;
pub mod text;

use serde_json::{json, Value};
use std::collections::BTreeMap;

/// What the renderer reads.  All of it comes from signed reads this workspace
/// made, or from its own reference hints.
pub struct View<'a> {
    /// `inspect view-document` output, with each `transclusions[]` item's
    /// `render` already re-read `at` its opening height when it had `moved`.
    pub document: &'a Value,
    /// The host cell's signed `entries` (annotations, atoms with their kind).
    pub entries: &'a [Value],
    /// Cell or document id -> the name this workspace knows it by.
    pub names: &'a BTreeMap<String, String>,
    /// Source cell -> (atom id -> its live line number in this reader's own
    /// current read of that source).  Absent when the reader holds no read.
    pub sources: &'a BTreeMap<String, BTreeMap<String, usize>>,
    /// This workspace's subject: its own annotations read as `you`.
    pub me: &'a str,
}

/// One mark kind on a line, as it renders: each kind once (a link: once per
/// target), struck only when every mark of it is stale.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Deco {
    Code { stale: bool },
    Italic { stale: bool },
    Bold { stale: bool },
    /// `target` is the reader's name for it, else `doc:<id>`; `None` = dead.
    Link { target: Option<String>, stale: bool },
    Heading { level: usize, stale: bool },
}

#[derive(Clone, Debug)]
pub enum Body {
    /// A text atom.  `bytes` are its exact payload.
    Text { bytes: Vec<u8>, struck: bool },
    /// An atom that is not UTF-8 text: shown by kind and size.
    Object { label: String, bytes: Vec<u8>, struck: bool },
    Transclusion(Transcluded),
    Section,
}

#[derive(Clone, Debug)]
pub struct Transcluded {
    pub id: String,
    pub source: String,
    pub source_name: String,
    /// `snapshot` or `live`, as the transclusion record names it.
    pub mode: String,
    /// `snapshot`, `live`, `unavailable`, `moved`, `invalidated`, `unresolved`.
    pub view: String,
    pub header: String,
    /// The transcluded lines (UTF-8, lossy); empty when not readable.
    pub lines: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct Annotation {
    pub id: String,
    pub author: String,
    pub fresh: bool,
    pub body: String,
}

#[derive(Clone, Debug)]
pub struct RenderedLine {
    pub row: Value,
    /// Live-line number; `None` for a struck atom or a section.
    pub line: Option<usize>,
    pub depth: usize,
    pub body: Body,
    pub decos: Vec<Deco>,
    pub annotations: Vec<Annotation>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OutlineEntry {
    pub line: usize,
    pub level: usize,
    pub text: String,
}

#[derive(Clone, Debug)]
pub struct Backlink {
    pub source: String,
    pub link: String,
    pub line: Option<usize>,
    pub rendered: Option<String>,
}

#[derive(Clone, Debug)]
pub struct Rendered {
    pub root: Value,
    pub root_revision: Value,
    pub lines: Vec<RenderedLine>,
    /// Annotations anchored on the document itself, not a line.
    pub document_annotations: Vec<Annotation>,
    pub outline: Vec<OutlineEntry>,
    pub backlinks: Vec<Backlink>,
}

/// The name this reader knows cell/document `id` by, else `doc:<id>`.
pub fn name_of(names: &BTreeMap<String, String>, id: &str) -> String {
    names.get(id).cloned().unwrap_or_else(|| format!("doc:{id}"))
}

fn link_target(names: &BTreeMap<String, String>, mark: &Value) -> Option<String> {
    if mark["linkLive"] == false {
        return None;
    }
    let target = &mark["target"];
    let id = target["id"].as_str().or_else(|| target["document"].as_str())?;
    match target["type"].as_str() {
        Some("document") | Some("range") => Some(name_of(names, id)),
        Some(other) => Some(format!("{other}:{id}")),
        None => None,
    }
}

/// The decorations of one row's live marks, innermost first.
pub fn decos(names: &BTreeMap<String, String>, marks: &Value, depth: usize) -> Vec<Deco> {
    let Some(marks) = marks.as_array() else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for kind in ["code", "italic", "bold", "link", "heading"] {
        // target -> any fresh; a BTreeMap so the order is the same every run.
        let mut seen = BTreeMap::<Option<String>, bool>::new();
        for mark in marks.iter().filter(|mark| mark["kind"] == kind) {
            let target = if kind == "link" { link_target(names, mark) } else { None };
            *seen.entry(target).or_insert(false) |= mark["fresh"] == true;
        }
        for (target, fresh) in seen {
            let stale = !fresh;
            out.push(match kind {
                "code" => Deco::Code { stale },
                "italic" => Deco::Italic { stale },
                "bold" => Deco::Bold { stale },
                "link" => Deco::Link { target, stale },
                _ => Deco::Heading { level: depth.max(1), stale },
            });
        }
    }
    out
}

fn decode_hex(value: &str) -> Vec<u8> {
    if value.len() % 2 != 0 {
        return Vec::new();
    }
    (0..value.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&value[i..i + 2], 16))
        .collect::<Result<Vec<_>, _>>()
        .unwrap_or_default()
}

/// `12 B`, `3 KB`, `2 MB`: an embed's size, to the unit a reader thinks in.
pub fn size_text(bytes: usize) -> String {
    if bytes < 1024 {
        format!("{bytes} B")
    } else if bytes < 1024 * 1024 {
        format!("{} KB", (bytes + 512) / 1024)
    } else {
        format!("{} MB", (bytes + 512 * 1024) / (1024 * 1024))
    }
}

fn author_text(me: &str, author: &Value) -> String {
    match author["subject"].as_str() {
        Some(subject) if subject == me => "you".to_owned(),
        Some(subject) => format!("subject {subject}"),
        None => "?".to_owned(),
    }
}

fn annotation_of(view: &View, entry: &Value) -> Annotation {
    let body = &entry["body"];
    let body = match body["type"].as_str() {
        Some("inline") => {
            String::from_utf8_lossy(&decode_hex(body["bytes"].as_str().unwrap_or(""))).into_owned()
        }
        Some("reference") => format!("→ {}", name_of(view.names, body["document"].as_str().unwrap_or("?"))),
        _ => String::new(),
    };
    Annotation {
        id: entry["id"].as_str().unwrap_or("").to_owned(),
        author: author_text(view.me, &entry["author"]),
        fresh: entry["fresh"] == true,
        body,
    }
}

/// The one-line header and lines of one rendered transclusion item, or the
/// placeholder when this reader's own reads do not cover its source.
pub fn transcluded(
    names: &BTreeMap<String, String>,
    sources: &BTreeMap<String, BTreeMap<String, usize>>,
    item: &Value,
) -> Transcluded {
    let opening = &item["opening"];
    let source = opening["source"].as_str().unwrap_or("?").to_owned();
    let source_name = name_of(names, &source);
    let view = item["render"]["view"].as_str().unwrap_or("?").to_owned();
    let lines: Vec<String> = item["render"]["lines"]
        .as_array()
        .map(|lines| {
            lines
                .iter()
                .filter_map(Value::as_str)
                .map(|line| String::from_utf8_lossy(&decode_hex(line)).into_owned())
                .collect()
        })
        .unwrap_or_default();
    // Source line numbers, as this reader's current read of the source places
    // the range's endpoints: the pins for a snapshot, the endpoints' neighbours
    // for a live range.  `?` where that atom is no live line of the source now.
    let numbers = sources.get(&source);
    let place = |atom: Option<&str>| -> String {
        atom.and_then(|atom| numbers.and_then(|numbers| numbers.get(atom)))
            .map_or("?".to_owned(), |n| n.to_string())
    };
    let (first, last) = if item["mode"] == "live" {
        (
            opening["range"]["start"]["neighbor"].as_str(),
            opening["range"]["finish"]["neighbor"].as_str(),
        )
    } else {
        let pins = opening["pins"].as_array();
        (
            pins.and_then(|pins| pins.first()).and_then(|pin| pin["atom"].as_str()),
            pins.and_then(|pins| pins.last()).and_then(|pin| pin["atom"].as_str()),
        )
    };
    let height = opening["height"].as_str().unwrap_or("?");
    let header = match view.as_str() {
        "unavailable" => format!(
            "[transclusion: {} atoms of {source_name}, not readable by you]",
            opening["atoms"].as_str().unwrap_or("?")
        ),
        "snapshot" => format!("⟨from {source_name} lines {}..{}, snapshot@{height}⟩", place(first), place(last)),
        "live" if item["render"]["revised"] == true => {
            format!("⟨from {source_name} lines {}..{}, live, revised⟩", place(first), place(last))
        }
        "live" => format!("⟨from {source_name} lines {}..{}, live⟩", place(first), place(last)),
        // A snapshot whose pins moved, re-read `at` its opening height and
        // refused there `no-grant`: the reader is told the lines moved, not shown them.
        "moved" => match item["atRefused"].as_str() {
            Some(at) => format!(
                "[snapshot of {source_name}: its lines moved since height {at}, and your grant did not cover {source_name} then]"
            ),
            None => format!("⟨from {source_name}, moved⟩"),
        },
        other => format!("⟨from {source_name}, {other}⟩"),
    };
    Transcluded {
        id: item["id"].as_str().unwrap_or("").to_owned(),
        source,
        source_name,
        mode: item["mode"].as_str().unwrap_or("?").to_owned(),
        view,
        header,
        lines: if matches!(item["render"]["view"].as_str(), Some("snapshot" | "live")) {
            lines
        } else {
            Vec::new()
        },
    }
}

/// The document as this reader reads it.
pub fn render(view: &View) -> Result<Rendered, String> {
    let document = view.document;
    let order = document["order"].as_array().ok_or("document view has no order")?;
    let transclusions: Vec<&Value> = document["transclusions"].as_array().map_or(Vec::new(), |all| all.iter().collect());
    let atom_kinds: BTreeMap<&str, &Value> = view
        .entries
        .iter()
        .filter(|entry| entry["type"] == "atom")
        .filter_map(|entry| Some((entry["id"].as_str()?, &entry["kind"])))
        .collect();
    let mut by_atom = BTreeMap::<String, Vec<Annotation>>::new();
    let mut document_annotations = Vec::new();
    for entry in view.entries.iter().filter(|entry| entry["type"] == "annotation") {
        match entry["anchor"]["type"].as_str() {
            Some("atom") => {
                if let Some(atom) = entry["anchor"]["atom"].as_str() {
                    by_atom.entry(atom.to_owned()).or_default().push(annotation_of(view, entry));
                }
            }
            Some("document") => document_annotations.push(annotation_of(view, entry)),
            _ => {}
        }
    }
    let mut depth = BTreeMap::<String, usize>::new();
    if let Some(root) = document["root"].as_str() {
        depth.insert(root.to_owned(), 0);
    }
    let mut lines = Vec::new();
    let mut number = 0usize;
    for row in order {
        let element = row["element"].as_str().ok_or("order row lacks element")?.to_owned();
        let level = row["parent"].as_str().and_then(|parent| depth.get(parent)).map_or(1, |d| d + 1);
        depth.insert(element, level);
        let (line, body, annotations) = match row["kind"].as_str() {
            Some("atom") => {
                let bytes = decode_hex(row["payload"].as_str().unwrap_or(""));
                let struck = row["struck"] == true;
                let line = if struck {
                    None
                } else {
                    number += 1;
                    Some(number)
                };
                let atom = row["atom"].as_str().unwrap_or("");
                let kind = atom_kinds.get(atom).copied();
                let opened = view.entries.iter().find(|entry| entry["type"] == "atom" && entry["id"].as_str() == Some(atom));
                let private_bytes = opened.and_then(|entry| crate::workspace::private::opened_text(entry).ok().flatten());
                let body = if let Some(bytes) = private_bytes {
                    if std::str::from_utf8(&bytes).is_ok() { Body::Text { bytes, struck } }
                    else { Body::Object { label: format!("[private binary {}]", size_text(bytes.len())), bytes, struck } }
                } else { match kind.and_then(|kind| kind["type"].as_str()) {
                    Some("inlineObject") if kind.is_some_and(crate::workspace::private::is_private_kind) => Body::Object {
                        label: opened.and_then(|entry| entry["private"].as_str()).unwrap_or("[private: locked or unreadable]").to_owned(),
                        bytes,
                        struck,
                    },
                    Some("inlineObject") => Body::Object {
                        label: format!(
                            "[object {} {}]",
                            kind.and_then(|kind| kind["schema"].as_str()).unwrap_or("?"),
                            size_text(bytes.len())
                        ),
                        bytes,
                        struck,
                    },
                    _ if std::str::from_utf8(&bytes).is_err() => Body::Object {
                        label: format!("[binary {}]", size_text(bytes.len())),
                        bytes,
                        struck,
                    },
                    _ => Body::Text { bytes, struck },
                }};
                (line, body, by_atom.remove(atom).unwrap_or_default())
            }
            Some("embed") => {
                number += 1;
                let id = row["transclusion"].as_str().unwrap_or("");
                let body = match transclusions.iter().find(|item| item["id"].as_str() == Some(id)) {
                    Some(item) => Body::Transclusion(transcluded(view.names, view.sources, item)),
                    None => Body::Transclusion(Transcluded {
                        id: id.to_owned(),
                        source: String::new(),
                        source_name: "?".to_owned(),
                        mode: "?".to_owned(),
                        view: "absent".to_owned(),
                        header: "[transclusion: not rendered by the Host]".to_owned(),
                        lines: Vec::new(),
                    }),
                };
                (Some(number), body, Vec::new())
            }
            Some("container") => (None, Body::Section, Vec::new()),
            other => return Err(format!("document view row of unknown kind {other:?}")),
        };
        let decos = decos(view.names, &row["marks"], level);
        lines.push(RenderedLine { row: row.clone(), line, depth: level, body, decos, annotations });
    }
    let outline = lines
        .iter()
        .filter_map(|line| {
            let n = line.line?;
            let level = line.decos.iter().find_map(|deco| match deco {
                Deco::Heading { level, stale: false } => Some(*level),
                _ => None,
            })?;
            Some(OutlineEntry { line: n, level, text: line.plain() })
        })
        .collect();
    Ok(Rendered {
        root: document["root"].clone(),
        root_revision: document["rootRevision"].clone(),
        lines,
        document_annotations,
        outline,
        backlinks: Vec::new(),
    })
}

impl RenderedLine {
    /// The line's body without notation (an embed: its header).
    pub fn plain(&self) -> String {
        match &self.body {
            Body::Text { bytes, .. } => String::from_utf8_lossy(bytes).into_owned(),
            Body::Object { label, .. } => label.clone(),
            Body::Transclusion(t) => t.header.clone(),
            Body::Section => String::new(),
        }
    }

    pub fn struck(&self) -> bool {
        matches!(self.body, Body::Text { struck: true, .. } | Body::Object { struck: true, .. })
    }
}

fn annotation_json(annotation: &Annotation) -> Value {
    json!({"id":annotation.id,"author":annotation.author,"fresh":annotation.fresh,"body":annotation.body})
}

impl Rendered {
    /// `--format raw`: the document's own live atoms, byte-exact, each followed
    /// by one newline.  A transclusion is not this document's bytes (the host
    /// holds none of them) and a struck atom is no line; neither appears.
    pub fn raw(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for line in &self.lines {
            match &line.body {
                Body::Text { bytes, struck: false } | Body::Object { bytes, struck: false, .. } => {
                    out.extend_from_slice(bytes);
                    out.push(b'\n');
                }
                _ => {}
            }
        }
        out
    }

    /// `--format json`: every view row, plus `line`, `depth`, `text` (the raw
    /// body), `rendered` (the text notation), its annotations and transclusion.
    pub fn json(&self, host: &str) -> Value {
        let lines: Vec<Value> = self
            .lines
            .iter()
            .map(|line| {
                let mut row = line.row.clone();
                row["line"] = line.line.map_or(Value::Null, |n| json!(n));
                row["depth"] = json!(line.depth);
                row["text"] = json!(line.plain());
                row["rendered"] = json!(text::line_notation(line));
                row["annotations"] = Value::Array(line.annotations.iter().map(annotation_json).collect());
                if let Body::Transclusion(t) = &line.body {
                    row["transcluded"] = json!({"id":t.id,"source":t.source,"name":t.source_name,
                        "view":t.view,"header":t.header,"lines":t.lines});
                }
                row
            })
            .collect();
        json!({"type":"document","host":host,"root":self.root,"rootRevision":self.root_revision,
            "lines":lines,
            "documentAnnotations":self.document_annotations.iter().map(annotation_json).collect::<Vec<_>>(),
            "outline":self.outline.iter().map(|o| json!({"line":o.line,"level":o.level,"text":o.text})).collect::<Vec<_>>(),
            "backlinks":self.backlinks.iter().map(|b| json!({"source":b.source,"link":b.link,
                "line":b.line,"rendered":b.rendered})).collect::<Vec<_>>(),
            "text":self.text()})
    }

    pub fn text(&self) -> String {
        text::document(self)
    }

    pub fn html(&self, title: &str) -> String {
        html::document(self, title)
    }
}

/// Live line number -> atom, for a source document's own view: what places a
/// transclusion's endpoints in that source.
pub fn line_numbers(document: &Value) -> BTreeMap<String, usize> {
    let mut out = BTreeMap::new();
    let mut n = 0usize;
    for row in document["order"].as_array().into_iter().flatten() {
        match row["kind"].as_str() {
            Some("atom") if row["struck"] != true => {
                n += 1;
                if let Some(atom) = row["atom"].as_str() {
                    out.insert(atom.to_owned(), n);
                }
            }
            Some("embed") => n += 1,
            _ => {}
        }
    }
    out
}

#[cfg(test)]
mod tests;
