//! The HTML backend: the same structure as the text backend, as semantic HTML
//! with classes and no CSS (the web face styles it).  Every text and name is
//! escaped; a link carries the reader's name for its target in `data-target`
//! and no URL, since routes are the web face's.

use super::{Annotation, Body, Deco, Rendered, RenderedLine};
use serde_json::Value;

pub fn escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            _ => out.push(c),
        }
    }
    out
}

fn decorate(body: &str, decos: &[Deco]) -> String {
    let strike = |stale: bool, inner: String| {
        if stale {
            format!("<s class=\"stale\">{inner}</s>")
        } else {
            inner
        }
    };
    let mut html = escape(body);
    for deco in decos {
        html = match deco {
            Deco::Code { stale } => strike(*stale, format!("<code>{html}</code>")),
            Deco::Italic { stale } => strike(*stale, format!("<em>{html}</em>")),
            Deco::Bold { stale } => strike(*stale, format!("<strong>{html}</strong>")),
            Deco::Link { target: Some(target), stale } => strike(
                *stale,
                format!("<a class=\"link\" data-target=\"{}\">{html}</a>", escape(target)),
            ),
            Deco::Link { target: None, stale } => {
                strike(*stale, format!("<a class=\"link dead\">{html}</a>"))
            }
            Deco::Heading { level, stale } => format!(
                "<span class=\"heading{}\" role=\"heading\" aria-level=\"{level}\">{html}</span>",
                if *stale { " stale" } else { "" }
            ),
        };
    }
    html
}

fn annotation(a: &Annotation) -> String {
    format!(
        "<aside class=\"annotation {}\" data-annotation=\"{}\" data-fresh=\"{}\"><span class=\"author\">{}</span> <span class=\"body\">{}</span></aside>",
        if a.fresh { "fresh" } else { "stale" },
        escape(&a.id),
        a.fresh,
        escape(&a.author),
        escape(&a.body)
    )
}

/// A row's live marks as one attribute: each kind, `~` before a stale one.
fn marks_attr(row: &Value) -> String {
    let kinds: Vec<String> = row["marks"]
        .as_array()
        .map(|marks| {
            marks
                .iter()
                .map(|mark| {
                    format!(
                        "{}{}",
                        if mark["fresh"] == false { "~" } else { "" },
                        mark["kind"].as_str().unwrap_or("?")
                    )
                })
                .collect()
        })
        .unwrap_or_default();
    if kinds.is_empty() {
        String::new()
    } else {
        format!(" data-marks=\"{}\"", escape(&kinds.join(",")))
    }
}

/// The row's identity as attributes, in a fixed order: element, kind, live
/// line number (`-` for a struck atom, empty for a section), then per kind the
/// atom, its creator, revision, struck flag and marks, or the transclusion,
/// its mode and how it rendered for this reader.
fn row_attrs(line: &RenderedLine) -> String {
    let row = &line.row;
    let text = |value: &Value| escape(value.as_str().unwrap_or("?"));
    let number = match line.line {
        Some(n) => n.to_string(),
        None if line.struck() => "-".to_owned(),
        None => String::new(),
    };
    let mut attrs = format!(
        " data-element=\"{}\" data-kind=\"{}\" data-line=\"{number}\"",
        text(&row["element"]),
        text(&row["kind"])
    );
    match &line.body {
        Body::Text { struck, .. } | Body::Object { struck, .. } => attrs.push_str(&format!(
            " data-atom=\"{}\" data-creator=\"{}\" data-revision=\"{}\" data-struck=\"{struck}\"{}",
            text(&row["atom"]),
            text(&row["createdBy"]["subject"]),
            text(&row["revision"]),
            marks_attr(row)
        )),
        Body::Transclusion(t) => attrs.push_str(&format!(
            " data-transclusion=\"{}\" data-mode=\"{}\" data-render=\"{}\"{}",
            escape(&t.id),
            escape(&t.mode),
            escape(&t.view),
            marks_attr(row)
        )),
        Body::Section => attrs.push_str(&format!(" data-section=\"{}\"", text(&row["revision"]))),
    }
    attrs
}

pub fn document(rendered: &Rendered, title: &str) -> String {
    let mut out = vec![format!("<article class=\"doc\" data-name=\"{}\">", escape(title))];
    if !rendered.shared_names.is_empty() {
        out.push("<section class=\"shared-names\"><h2>Shared names</h2><dl>".to_owned());
        for binding in &rendered.shared_names {
            out.push(format!("<dt>{}</dt><dd>{}:{}</dd>",escape(&binding.name),
                escape(&binding.kind),escape(&binding.target)));
        }
        out.push("</dl></section>".to_owned());
    }
    for a in &rendered.document_annotations {
        out.push(annotation(a));
    }
    if !rendered.outline.is_empty() {
        out.push("<nav class=\"outline\"><ol>".to_owned());
        for entry in &rendered.outline {
            out.push(format!(
                "<li data-line=\"{}\" data-level=\"{}\">{}</li>",
                entry.line,
                entry.level,
                escape(&entry.text)
            ));
        }
        out.push("</ol></nav>".to_owned());
    }
    out.push("<ol class=\"lines\">".to_owned());
    for line in &rendered.lines {
        let mut classes = vec!["line"];
        let number = line.line.map_or(String::new(), |n| format!(" value=\"{n}\""));
        let content = match &line.body {
            Body::Text { struck, .. } | Body::Object { struck, .. } => {
                if matches!(line.body, Body::Object { .. }) {
                    classes.push("object");
                }
                let inner = decorate(&line.plain(), &line.decos);
                if *struck {
                    classes.push("struck");
                    format!("<del>{inner}</del>")
                } else {
                    inner
                }
            }
            Body::Section => {
                classes.push("section");
                decorate("", &line.decos)
            }
            Body::Transclusion(t) => {
                classes.push("transclusion");
                let mut block = format!(
                    "<blockquote class=\"transclusion {}\" data-source=\"{}\"><header>{}</header>",
                    escape(&t.view),
                    escape(&t.source_name),
                    decorate(&t.header, &line.decos)
                );
                for quoted in &t.lines {
                    block.push_str(&format!("<p class=\"quoted\">{}</p>", escape(quoted)));
                }
                block.push_str("</blockquote>");
                block
            }
        };
        let annotations: String = line.annotations.iter().map(|a| annotation(a)).collect();
        out.push(format!(
            "<li class=\"{}\"{number}{} data-depth=\"{}\">{content}{annotations}</li>",
            classes.join(" "),
            row_attrs(line),
            line.depth
        ));
    }
    out.push("</ol>".to_owned());
    if !rendered.backlinks.is_empty() {
        out.push("<section class=\"backlinks\"><ul>".to_owned());
        for b in &rendered.backlinks {
            out.push(format!(
                "<li><span class=\"source\">{}</span>{}</li>",
                escape(&b.source),
                b.rendered
                    .as_ref()
                    .map(|r| format!(" <span class=\"context\">{}</span>", escape(r)))
                    .unwrap_or_default()
            ));
        }
        out.push("</ul></section>".to_owned());
    }
    out.push("</article>".to_owned());
    let mut html = out.join("\n");
    html.push('\n');
    html
}
