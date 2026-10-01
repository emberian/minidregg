//! The shell's `doc` lines for the element tree, marks and rendering: each
//! line is exactly one `mini workspace` action, spelled here as its flags
//! (without `--dir`, which the session supplies).  The spec is
//! `deploy/shell/DOC-VERBS.md`.
//!
//! On the k-marks tree there is no `mini shell` (it lives on `final`), so this
//! file is compiled from `main.rs` by path and nothing calls it.  Integrator:
//! add `mod doc_render;` to `shell.rs`, delete the `#[path]` line in
//! `main.rs`, and in the `"doc"` arm route `show outline mark unmark insert
//! move remove transclude transclusions follow links backlinks` through
//! `doc_flags`, passing the TEXT of `insert` through `text_argument` first
//! (so `@FILE` works) and wrapping the flags in `client("workspace", …)` with
//! `flag("dir", ws())` prepended.

/// The workspace flags for one `doc` line (`words[0] == "doc"`), or the usage
/// text when the line is malformed.  Nothing is sent from here.
pub(crate) fn doc_flags(words: &[String]) -> Result<Vec<(&'static str, String)>, String> {
    let w: Vec<&str> = words.iter().map(String::as_str).collect();
    let number = |value: &str, what: &str| -> Result<String, String> {
        if !value.is_empty() && value.bytes().all(|b| b.is_ascii_digit()) && value != "0" {
            Ok(value.to_owned())
        } else {
            Err(format!("{what} is a line number (1, 2, …), not {value:?}"))
        }
    };
    let decimal = |value: &str, what: &str| -> Result<String, String> {
        if !value.is_empty() && value.bytes().all(|b| b.is_ascii_digit()) {
            Ok(value.to_owned())
        } else {
            Err(format!("{what} is a decimal id, not {value:?}"))
        }
    };
    let usage = |line: &str| Err(format!("usage: {line}"));
    let flags = match w.as_slice() {
        ["doc", "show", name] => vec![("action", "doc-show".into()), ("name", (*name).into())],
        ["doc", "show", name, format @ ("--raw" | "--json" | "--html")] => vec![
            ("action", "doc-show".into()),
            ("name", (*name).into()),
            ("format", format.trim_start_matches("--").into()),
        ],
        ["doc", "show", ..] => return usage("doc show NAME [--raw|--json|--html]"),
        ["doc", "outline", name] => vec![("action", "doc-outline".into()), ("name", (*name).into())],
        ["doc", "outline", ..] => return usage("doc outline NAME"),
        ["doc", verb @ ("backlinks" | "links" | "transclusions"), name] => vec![
            ("action", if *verb == "transclusions" { "transclusions".into() } else { format!("doc-{verb}") }),
            ("name", (*name).into()),
        ],
        ["doc", "mark", name, line, kind] | ["doc", "mark", name, line, kind, _] => {
            if !matches!(*kind, "bold" | "italic" | "code" | "heading" | "link") {
                return Err(format!("unknownKind: {kind} (expected bold, italic, code, heading or link)"));
            }
            let mut flags = vec![
                ("action", "mark".into()),
                ("name", (*name).into()),
                ("line", number(line, "LINE")?),
                ("kind", (*kind).into()),
            ];
            match (w.get(5), *kind) {
                (Some(target), "link") => flags.push(("to", (*target).into())),
                (None, "link") => return usage("doc mark NAME LINE link TARGET"),
                (Some(_), _) => return usage("doc mark NAME LINE KIND (a TARGET is a link's only)"),
                (None, _) => {}
            }
            flags
        }
        ["doc", "mark", ..] => return usage("doc mark NAME LINE bold|italic|code|heading|link [TARGET]"),
        ["doc", "unmark", name, mark] => {
            vec![("action", "unmark".into()), ("name", (*name).into()), ("mark", decimal(mark, "MARK")?)]
        }
        ["doc", "unmark", name, line, kind] => vec![
            ("action", "unmark".into()),
            ("name", (*name).into()),
            ("line", number(line, "LINE")?),
            ("kind", (*kind).into()),
        ],
        ["doc", "unmark", ..] => return usage("doc unmark NAME MARK | doc unmark NAME LINE KIND"),
        ["doc", "insert", name, at, text] => vec![
            ("action", "doc-insert".into()),
            ("name", (*name).into()),
            ("at", number(at, "N")?),
            ("text", (*text).into()),
        ],
        ["doc", "insert", ..] => return usage("doc insert NAME N TEXT|@FILE"),
        ["doc", "move", name, from, to] => vec![
            ("action", "doc-move".into()),
            ("name", (*name).into()),
            ("from", number(from, "FROM")?),
            ("to", number(to, "TO")?),
        ],
        ["doc", "move", ..] => return usage("doc move NAME FROM TO"),
        ["doc", "remove", name, line] => {
            vec![("action", "doc-remove".into()), ("name", (*name).into()), ("line", number(line, "N")?)]
        }
        ["doc", "remove", ..] => return usage("doc remove NAME N"),
        ["doc", "transclude", name, source, from, to, rest @ ..] => {
            let mut flags = vec![
                ("action", "transclude".into()),
                ("name", (*name).into()),
                ("source", (*source).into()),
                ("from", decimal(from, "FROM atom")?),
                ("to", decimal(to, "TO atom")?),
            ];
            let mut rest = rest.iter();
            while let Some(word) = rest.next() {
                match *word {
                    "snapshot" | "live" => flags.push(("mode", (*word).into())),
                    "at" => match rest.next() {
                        Some(n) => flags.push(("at", number(n, "at N")?)),
                        None => return usage("doc transclude NAME SOURCE FROM TO [snapshot|live] [at N]"),
                    },
                    _ => return usage("doc transclude NAME SOURCE FROM TO [snapshot|live] [at N]"),
                }
            }
            flags
        }
        ["doc", "transclude", ..] => return usage("doc transclude NAME SOURCE FROM TO [snapshot|live] [at N]"),
        ["doc", "follow", name, transclusion] => vec![
            ("action", "follow".into()),
            ("name", (*name).into()),
            ("transclusion", decimal(transclusion, "TRANSCLUSION")?),
        ],
        ["doc", "follow", ..] => return usage("doc follow NAME TRANSCLUSION"),
        _ => return usage("doc show|outline|mark|unmark|insert|move|remove|transclude|transclusions|follow|links|backlinks …"),
    };
    Ok(flags)
}

#[cfg(test)]
mod tests {
    use super::doc_flags;

    fn flags(line: &str) -> Result<Vec<(&'static str, String)>, String> {
        doc_flags(&line.split(' ').map(str::to_owned).collect::<Vec<_>>())
    }

    #[test]
    fn each_doc_line_is_one_workspace_action() {
        let f = |pairs: &[(&'static str, &str)]| -> Vec<(&'static str, String)> {
            pairs.iter().map(|(k, v)| (*k, (*v).to_owned())).collect()
        };
        assert_eq!(flags("doc show paper").unwrap(), f(&[("action", "doc-show"), ("name", "paper")]));
        assert_eq!(
            flags("doc show paper --raw").unwrap(),
            f(&[("action", "doc-show"), ("name", "paper"), ("format", "raw")])
        );
        assert_eq!(flags("doc outline paper").unwrap(), f(&[("action", "doc-outline"), ("name", "paper")]));
        assert_eq!(
            flags("doc mark paper 5 link notes").unwrap(),
            f(&[("action", "mark"), ("name", "paper"), ("line", "5"), ("kind", "link"), ("to", "notes")])
        );
        assert_eq!(
            flags("doc unmark paper 8401").unwrap(),
            f(&[("action", "unmark"), ("name", "paper"), ("mark", "8401")])
        );
        assert_eq!(
            flags("doc insert paper 2 hello").unwrap(),
            f(&[("action", "doc-insert"), ("name", "paper"), ("at", "2"), ("text", "hello")])
        );
        assert_eq!(
            flags("doc move paper 5 1").unwrap(),
            f(&[("action", "doc-move"), ("name", "paper"), ("from", "5"), ("to", "1")])
        );
        assert_eq!(
            flags("doc transclude paper wall 1002 1004 live at 3").unwrap(),
            f(&[("action", "transclude"), ("name", "paper"), ("source", "wall"), ("from", "1002"),
                ("to", "1004"), ("mode", "live"), ("at", "3")])
        );
        assert_eq!(
            flags("doc follow paper 77").unwrap(),
            f(&[("action", "follow"), ("name", "paper"), ("transclusion", "77")])
        );
    }

    #[test]
    fn malformed_lines_are_refused_before_anything_is_sent() {
        for bad in ["doc", "doc show", "doc show p --pdf", "doc mark p 0 bold", "doc mark p 2 underline",
            "doc mark p 2 link", "doc mark p 2 bold extra", "doc unmark p x", "doc move p 1",
            "doc remove p two", "doc transclude p w 1 2 at", "doc follow p"] {
            assert!(flags(bad).is_err(), "{bad} should be refused");
        }
        assert!(flags("doc mark p 2 underline").unwrap_err().starts_with("unknownKind: underline"));
    }
}
