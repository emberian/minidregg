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

/// Document data is never terminal control syntax. Keep controls visible,
/// including both ESC-prefixed sequences and single-codepoint C1 controls.
/// Line separators are supplied by the renderer, never by document content.
fn one_line(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for character in text.chars() {
        match character {
            '\n' => out.push('␤'),
            '\r' => out.push('␍'),
            c if c.is_ascii_control() => {
                out.push(if c == '\u{7f}' { '␡' } else {
                    char::from_u32(0x2400 + c as u32).expect("ASCII control picture")
                });
            }
            c if c.is_control() => out.extend(c.escape_unicode()),
            c => out.push(c),
        }
    }
    out
}

pub fn decorate(body: &str, decos: &[Deco]) -> String {
    let strike = |stale: bool, decorated: String| if stale { format!("~~{decorated}~~") } else { decorated };
    let mut text = one_line(body);
    for deco in decos {
        text = match deco {
            Deco::Code { stale } => strike(*stale, format!("`{text}`")),
            Deco::Italic { stale } => strike(*stale, format!("_{text}_")),
            Deco::Bold { stale } => strike(*stale, format!("**{text}**")),
            Deco::Link { target, stale } => {
                strike(*stale, format!("[{text}](→ {})", one_line(target.as_deref().unwrap_or("?"))))
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
    let decorated = decorate(&line.plain(), &line.decos);
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
        format!("{}{}",one_line(&a.body),a.key_wrapping.as_ref().map(|event|format!(" [{event}]")).unwrap_or_default())
    )
}

pub fn document(rendered: &Rendered) -> String {
    let mut out = Vec::new();
    for binding in &rendered.shared_names {
        out.push(format!("  {} → {}:{}", binding.name, binding.kind, binding.target));
    }
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
    // Apply the same boundary to metadata (shared names, annotation authors,
    // key-wrapping descriptions) as to payloads and transclusions.
    let mut text = out.iter().map(|line| one_line(line)).collect::<Vec<_>>().join("\n");
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

#[cfg(test)]
mod terminal_tests {
    use super::*;

    const ATTACK: &str = "\u{1b}]52;c;c2VjcmV0\u{7}\u{9b}2J\u{8}\t\r\n";

    #[test]
    fn every_unicode_control_is_visible_without_terminal_control_bytes() {
        let controls: String = (0..=0x10ffff).filter_map(char::from_u32)
            .filter(|c| c.is_control()).collect();
        let rendered = one_line(&controls);
        assert!(!rendered.chars().any(char::is_control));
        assert!(rendered.contains('␛'));
        assert!(rendered.contains("\\u{9b}"));
        assert_eq!(one_line("λ café 🐴\n\r"), "λ café 🐴␤␍");
        assert_eq!(one_line(&rendered), rendered);
    }

    #[test]
    fn decorations_cannot_restore_terminal_sequences_via_link_names() {
        let rendered = decorate(ATTACK, &[Deco::Link {
            target: Some(ATTACK.into()), stale: false,
        }, Deco::Bold { stale: false }]);
        assert!(!rendered.chars().any(char::is_control));
        assert!(rendered.contains("**[␛]52;"));
    }

    #[test]
    fn document_metadata_annotations_and_outline_are_terminal_safe() {
        use super::super::{OutlineEntry, Rendered};
        let annotation = Annotation {
            id: "1".into(), author: ATTACK.into(), fresh: true,
            body: ATTACK.into(), key_wrapping: Some(ATTACK.into()),
        };
        let rendered = Rendered {
            shared_names: Vec::new(), root: serde_json::Value::Null,
            root_revision: serde_json::Value::Null,
            lines: vec![RenderedLine {
                row: serde_json::Value::Null, line: Some(1), depth: 1,
                body: Body::Text { bytes: ATTACK.as_bytes().to_vec(), struck: false },
                decos: vec![Deco::Link { target: Some(ATTACK.into()), stale: false }],
                annotations: vec![annotation.clone()],
            }],
            document_annotations: vec![annotation],
            outline: vec![OutlineEntry { line: 1, level: 1, text: ATTACK.into() }],
            backlinks: Vec::new(),
        };
        for output in [document(&rendered), outline(&rendered)] {
            assert!(output.chars().all(|c| c == '\n' || !c.is_control()), "{output:?}");
        }
        assert_eq!(document(&rendered).lines().count(), 3);
        // Raw document bytes remain exact; this is a presentation boundary.
        assert_eq!(rendered.raw(), [ATTACK.as_bytes(), b"\n"].concat());
    }
}
