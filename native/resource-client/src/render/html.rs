//! The HTML backend: the same structure as the text backend, as semantic HTML
//! with classes and no CSS (the web face styles it).  Every text and name is
//! escaped; a link carries the reader's name for its target in `data-target`
//! and no URL, since routes are the web face's.

use super::{Annotation, Body, Deco, Rendered, RenderedLine, SharedName};
use serde_json::Value;

/// THE escaper for every stranger-supplied string the web face renders, in text and in quoted
/// attribute values alike (there is no other in this crate; `web::escape` is this function).
/// Beyond the five HTML metacharacters it makes visible what a reader cannot see and a stranger
/// can use: C0/C1 controls (as their control pictures / `\u{..}`), the bidirectional embedding,
/// override and isolate controls (U+202A..U+202E, U+2066..U+2069: "Trojan Source" reordering of a
/// name, a line or a command), and the invisible separators U+200B, U+2060, U+FEFF (a name that
/// looks like another). ZWJ/ZWNJ and the LRM/RLM marks stay: scripts and emoji need them, and
/// they cannot reorder text. Newline, carriage return and tab stay (`<pre>` keeps lines; HTML reads CR as space).
pub fn escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            '\n' | '\r' | '\t' => out.push(c),
            '\u{7f}' => out.push('\u{2421}'),
            c if (c as u32) < 0x20 => out.push(char::from_u32(0x2400 + c as u32).unwrap_or('\u{fffd}')),
            '\u{80}'..='\u{9f}' | '\u{202a}'..='\u{202e}' | '\u{2066}'..='\u{2069}' | '\u{200b}' | '\u{2060}' | '\u{feff}' => {
                out.push_str(&format!("[U+{:04X}]", c as u32))
            }
            _ => out.push(c),
        }
    }
    out
}

/// A URL for an `href`, `src` or `action` attribute built from data (an origin a worker reported,
/// a link a page carries): a same-origin path (`/…`, never `//…` or `/\…`) or an absolute
/// `https://`/`http://` URL, escaped; anything else (`javascript:`, `data:`, `vbscript:`, a
/// relative path, a scheme hidden behind controls or whitespace) becomes `#refused-url`, so no
/// stranger-chosen scheme ever reaches a browser's URL parser from this face.
pub fn url(text: &str) -> String {
    let same_origin = text.starts_with('/') && !text.starts_with("//") && !text.starts_with("/\\");
    let lower = text.to_ascii_lowercase();
    let absolute = (lower.starts_with("https://") || lower.starts_with("http://")) && text.len() > "https://".len();
    let clean = !text.chars().any(|c| c.is_control() || c.is_whitespace() || c == '\\');
    if (same_origin || absolute) && clean {
        escape(text)
    } else {
        "#refused-url".to_owned()
    }
}

fn doc_href(base: Option<&str>, target: &str) -> Option<String> {
    let base = base?.trim_end_matches('/');
    crate::workspace::validate_ref_name(target).ok()?;
    let href = url(&format!("{base}/doc/{target}"));
    (href != "#refused-url").then_some(href)
}

fn decorate_html(mut html: String, decos: &[Deco], base: Option<&str>) -> String {
    let strike = |stale: bool, inner: String| {
        if stale {
            format!("<s class=\"stale\">{inner}</s>")
        } else {
            inner
        }
    };
    for deco in decos {
        html = match deco {
            Deco::Code { stale } => strike(*stale, format!("<code>{html}</code>")),
            Deco::Italic { stale } => strike(*stale, format!("<em>{html}</em>")),
            Deco::Bold { stale } => strike(*stale, format!("<strong>{html}</strong>")),
            Deco::Link {
                target: Some(target),
                stale,
            } => strike(
                *stale,
                match doc_href(base, target) {
                    Some(href) => format!(
                        "<a class=\"link\" href=\"{href}\" data-target=\"{}\">{html}</a>",
                        escape(target)
                    ),
                    None => format!(
                        "<a class=\"link\" data-target=\"{}\">{html}</a>",
                        escape(target)
                    ),
                },
            ),
            Deco::Link {
                target: None,
                stale,
            } => strike(*stale, format!("<a class=\"link dead\">{html}</a>")),
            Deco::Heading { level, stale } => format!(
                "<span class=\"heading{}\" role=\"heading\" aria-level=\"{level}\">{html}</span>",
                if *stale { " stale" } else { "" }
            ),
        };
    }
    html
}

fn decorate(body: &str, decos: &[Deco], base: Option<&str>) -> String {
    decorate_html(escape(body), decos, base)
}

fn annotation(a: &Annotation) -> String {
    format!(
        "<aside class=\"annotation {}\" data-annotation=\"{}\" data-fresh=\"{}\"><span class=\"author\">{}</span> <span class=\"body\">{}</span></aside>",
        if a.fresh { "fresh" } else { "stale" },
        escape(&a.id),
        a.fresh,
        escape(&a.author),
        format!("{}{}",escape(&a.body),a.key_wrapping.as_ref().map(|event|format!(" <small class=key-wrapping>{}</small>",escape(event))).unwrap_or_default())
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
    document_with_base(rendered, title, None)
}

pub fn document_linked(rendered: &Rendered, title: &str, base: &str) -> String {
    document_with_base(rendered, title, Some(base))
}

fn document_with_base(rendered: &Rendered, title: &str, base: Option<&str>) -> String {
    let mut out = vec![format!(
        "<article class=\"doc\" data-name=\"{}\">",
        escape(title)
    )];
    if !rendered.shared_names.is_empty() {
        out.push("<section class=\"shared-names\"><h2>Shared names</h2><dl>".to_owned());
        for name in &rendered.shared_names {
            out.push(match name {
                SharedName::Bound(binding) => format!(
                    "<dt>{}</dt><dd>{}:{}</dd>",
                    escape(&binding.name),
                    escape(&binding.kind),
                    escape(&binding.target)
                ),
                SharedName::Invalid { link, reason } => format!(
                    "<dt class=\"invalid\" data-invalid-name=\"{0}\">invalid link {0}</dt><dd>{1}</dd>",
                    escape(link),
                    escape(reason)
                ),
            });
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
        // Containers participate in the source tree, but an empty structural
        // row is not a displayed line and must not consume an HTML list marker.
        if matches!(line.body, Body::Section)
            && line.annotations.is_empty()
            && line.decos.is_empty()
        {
            continue;
        }
        let mut classes = vec!["line"];
        let number = line.line.map_or_else(
            || " style=\"list-style:none\"".to_owned(),
            |n| format!(" value=\"{n}\""),
        );
        let content = match &line.body {
            Body::Text { struck, .. } | Body::Object { struck, .. } => {
                if matches!(line.body, Body::Object { .. }) {
                    classes.push("object");
                }
                let inner = decorate(&line.plain(), &line.decos, base);
                if *struck {
                    classes.push("struck");
                    format!("<del>{inner}</del>")
                } else {
                    inner
                }
            }
            Body::Section => {
                classes.push("section");
                decorate("", &line.decos, base)
            }
            Body::Transclusion(t) => {
                classes.push("transclusion");
                let has_link_mark = line.decos.iter().any(|d| matches!(d, Deco::Link { .. }));
                let prefix = format!("⟨from {}", t.source_name);
                let header_html = match (
                    !has_link_mark,
                    t.header.strip_prefix(&prefix),
                    doc_href(base, &t.source_name),
                ) {
                    (true, Some(rest), Some(href)) => format!(
                        "⟨from <a href=\"{href}\">{}</a>{}",
                        escape(&t.source_name),
                        escape(rest)
                    ),
                    _ => escape(&t.header),
                };
                let mut block = format!(
                    "<blockquote class=\"transclusion {}\" data-source=\"{}\"><header>{}</header>",
                    escape(&t.view),
                    escape(&t.source_name),
                    decorate_html(header_html, &line.decos, base)
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
            let source_html = match doc_href(base, &b.source) {
                Some(href) => format!("<a class=\"source\" href=\"{href}\">{}</a>", escape(&b.source)),
                None => format!("<span class=\"source\">{}</span>", escape(&b.source)),
            };
            out.push(format!(
                "<li>{source_html}{}</li>",
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

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    fn row(body: Body, number: Option<usize>) -> RenderedLine {
        RenderedLine {
            row: json!({"element":"1","kind":"atom","atom":"9","revision":"2","createdBy":{"subject":"7"}}),
            line: number,
            depth: 1,
            body,
            decos: vec![],
            annotations: vec![],
        }
    }
    #[test]
    fn structural_rows_do_not_produce_blank_or_duplicate_line_numbers() {
        let mut note = row(Body::Section, None);
        note.annotations.push(Annotation {
            key_wrapping: None,
            id: "3".into(),
            author: "you".into(),
            fresh: true,
            body: "Section note".into(),
        });
        let rendered = Rendered {
            shared_names: vec![],
            root: json!("1"),
            root_revision: json!("2"),
            lines: vec![
                row(Body::Section, None),
                row(
                    Body::Text {
                        bytes: b"first current line".to_vec(),
                        struck: false,
                    },
                    Some(1),
                ),
                row(Body::Section, None),
                note,
                row(
                    Body::Text {
                        bytes: b"second current line".to_vec(),
                        struck: false,
                    },
                    Some(2),
                ),
            ],
            document_annotations: vec![],
            outline: vec![],
            backlinks: vec![],
        };
        let html = document(&rendered, "paper");
        assert_eq!(html.matches("<li ").count(), 3);
        assert_eq!(html.matches("value=\"1\"").count(), 1);
        assert_eq!(html.matches("value=\"2\"").count(), 1);
        assert!(html.contains("class=\"line section\" style=\"list-style:none\""));
        assert!(html.contains("Section note"));
        assert!(html.contains("first current line") && html.contains("second current line"));
        assert!(!html.contains("data-depth=\"1\"></li>"));
    }
}
