//! The text backend: the plain notation `doc show` prints.
//!
//! | what                 | notation                                   |
//! |----------------------|--------------------------------------------|
//! | bold / italic / code | `**t**` / `_t_` / `` `t` ``                 |
//! | heading              | `# t` (`#` per tree depth: `##` in a section) |
//! | link mark            | `[t](→ NAME)`, `[t](→ doc:ID)` unnamed, `[t](→ ?)` dead |
//! | stale mark           | that kind's decoration wrapped `~~…~~`     |
//! | live line            | `  N  text`                                |
//! | struck line          | `  -  ~~text~~`                            |
//! | section              | `  §`                                      |
//! | transclusion         | `  N  ⟨from DOC lines a..b, snapshot@H⟩` / `live`, then `     │ line` |
//! | not readable         | `  N  [transclusion: K atoms of DOC, not readable by you]` |
//! | object atom          | `[object SCHEMA 12 KB]`, `[binary 3 B]`     |
//! | annotation           | `     ↳ AUTHOR (fresh|stale): body`        |
//!
//! Marks apply innermost first: code, italic, bold, link, heading.

use super::{Annotation, Body, Deco, Rendered, RenderedLine};

/// A body may hold a newline; a rendered line may not.
fn one_line(text: &str) -> String {
    text.replace('\n', "␤").replace('\r', "␍")
}

pub fn decorate(body: &str, decos: &[Deco]) -> String {
    let strike = |stale: bool, decorated: String| if stale { format!("~~{decorated}~~") } else { decorated };
    let mut text = body.to_owned();
    for deco in decos {
        text = match deco {
            Deco::Code { stale } => strike(*stale, format!("`{text}`")),
            Deco::Italic { stale } => strike(*stale, format!("_{text}_")),
            Deco::Bold { stale } => strike(*stale, format!("**{text}**")),
            Deco::Link { target, stale } => {
                strike(*stale, format!("[{text}](→ {})", target.as_deref().unwrap_or("?")))
            }
            Deco::Heading { level, stale } => {
                let hashes = "#".repeat(*level);
                if text.is_empty() {
                    strike(*stale, hashes)
                } else {
                    format!("{} {text}", strike(*stale, hashes))
                }
            }
        };
    }
    text
}

/// One row's text with its marks (an embed: its header), no number, no
/// annotation: the `rendered` field of `--format json`.
pub fn line_notation(line: &RenderedLine) -> String {
    let decorated = decorate(&one_line(&line.plain()), &line.decos);
    if line.struck() {
        format!("~~{decorated}~~")
    } else {
        decorated
    }
}

fn annotation(indent: &str, a: &Annotation) -> String {
    format!(
        "{indent}     ↳ {} ({}): {}",
        a.author,
        if a.fresh { "fresh" } else { "stale" },
        one_line(&a.body)
    )
}

pub fn document(rendered: &Rendered) -> String {
    let mut out = Vec::new();
    for a in &rendered.document_annotations {
        out.push(annotation("", a).replacen("     ↳", "  ¶  ↳", 1));
    }
    for line in &rendered.lines {
        let indent = "  ".repeat(line.depth.saturating_sub(1));
        let notation = line_notation(line);
        let number = match (line.line, &line.body) {
            (Some(n), _) => format!("{n:>3}"),
            (None, Body::Section) => "  §".to_owned(),
            (None, _) => "  -".to_owned(),
        };
        out.push(if notation.is_empty() {
            format!("{indent}{number}")
        } else {
            format!("{indent}{number}  {notation}")
        });
        if let Body::Transclusion(t) = &line.body {
            for quoted in &t.lines {
                out.push(format!("{indent}     │ {}", one_line(quoted)));
            }
        }
        for a in &line.annotations {
            out.push(annotation(&indent, a));
        }
    }
    let mut text = out.join("\n");
    text.push('\n');
    text
}

/// `doc outline`: the heading lines, indented by depth, with their numbers.
pub fn outline(rendered: &Rendered) -> String {
    let mut text = String::new();
    for entry in &rendered.outline {
        text.push_str(&format!(
            "{}{:>3}  {}\n",
            "  ".repeat(entry.level.saturating_sub(1)),
            entry.line,
            one_line(&entry.text)
        ));
    }
    text
}
