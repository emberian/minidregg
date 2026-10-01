//! The shell's `doc` lines for the element tree, marks and rendering: each
//! line is exactly one `mini workspace` action, spelled here as its flags
//! (without `--dir`, which the session supplies).  The spec is
//! `deploy/shell/DOC-VERBS.md`.
//!
//! `shell.rs`'s `"doc"` arm routes every verb but `new`, `append`, `edit`,
//! `link`, `annotate` and `push` (which spell a proposal request or name a
//! session file) through `doc_flags`, after passing `insert`'s TEXT through
//! `text_argument` (so `@FILE` works), and prepends `--dir`.

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
        ["doc", "show", name, rest @ ..] => {
            let mut flags = vec![("action", "doc-show"), ("name", *name)]
                .into_iter()
                .map(|(k, v)| (k, v.to_owned()))
                .collect::<Vec<_>>();
            let mut rest = rest.iter();
            let mut format = None;
            while let Some(word) = rest.next() {
                match *word {
                    "--at" | "at" => match (rest.next(), flags.iter().any(|(k, _)| *k == "at")) {
                        (Some(h), false) => flags.push(("at", decimal(h, "H")?)),
                        _ => return usage("doc show NAME [--at H] [--raw|--json|--html]"),
                    },
                    "--raw" | "--json" | "--html" if format.is_none() => format = Some(word.trim_start_matches("--")),
                    _ => return usage("doc show NAME [--at H] [--raw|--json|--html]"),
                }
            }
            if let Some(format) = format {
                flags.push(("format", format.to_owned()));
            }
            flags
        }
        ["doc", "show", ..] => return usage("doc show NAME [--at H] [--raw|--json|--html]"),
        ["doc", "history", name, rest @ ..] => {
            let mut flags = vec![("action", "doc-history"), ("name", *name)]
                .into_iter()
                .map(|(k, v)| (k, v.to_owned()))
                .collect::<Vec<_>>();
            match rest {
                [] => {}
                [format @ ("--json" | "--html")] => flags.push(("format", format.trim_start_matches("--").into())),
                _ => return usage("doc history NAME [--json|--html]"),
            }
            flags
        }
        ["doc", "history", ..] => return usage("doc history NAME [--json|--html]"),
        ["doc", "diff", name, from, to, rest @ ..] => {
            let mut flags = vec![
                ("action", "doc-diff"),
                ("name", *name),
            ]
            .into_iter()
            .map(|(k, v)| (k, v.to_owned()))
            .collect::<Vec<_>>();
            flags.push(("from", decimal(from, "H1")?));
            flags.push(("to", decimal(to, "H2")?));
            match rest {
                [] => {}
                [format @ ("--json" | "--html")] => flags.push(("format", format.trim_start_matches("--").into())),
                _ => return usage("doc diff NAME H1 H2 [--json|--html]"),
            }
            flags
        }
        ["doc", "diff", ..] => return usage("doc diff NAME H1 H2 [--json|--html]"),
        ["doc", "pull", name] => vec![("action", "doc-pull".into()), ("name", (*name).into())],
        ["doc", "pull", ..] => return usage("doc pull NAME"),
        ["doc", "range", name, from, to] => vec![
            ("action", "doc-range".into()),
            ("name", (*name).into()),
            ("from", number(from, "FROM")?),
            ("to", number(to, "TO")?),
        ],
        ["doc", "range", ..] => return usage("doc range NAME FROM TO"),
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
                ("from-line", number(from, "FROM")?),
                ("to-line", number(to, "TO")?),
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
        _ => return usage("doc show|outline|history|diff|pull|range|mark|unmark|insert|move|remove|transclude|transclusions|follow|links|backlinks …"),
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
            flags("doc transclude paper wall 2 4 live at 3").unwrap(),
            f(&[("action", "transclude"), ("name", "paper"), ("source", "wall"), ("from-line", "2"),
                ("to-line", "4"), ("mode", "live"), ("at", "3")])
        );
        assert_eq!(
            flags("doc show paper --at 77 --html").unwrap(),
            f(&[("action", "doc-show"), ("name", "paper"), ("at", "77"), ("format", "html")])
        );
        assert_eq!(flags("doc history paper").unwrap(), f(&[("action", "doc-history"), ("name", "paper")]));
        assert_eq!(
            flags("doc diff paper 77 81 --json").unwrap(),
            f(&[("action", "doc-diff"), ("name", "paper"), ("from", "77"), ("to", "81"), ("format", "json")])
        );
        assert_eq!(flags("doc pull paper").unwrap(), f(&[("action", "doc-pull"), ("name", "paper")]));
        assert_eq!(
            flags("doc range notes 2 3").unwrap(),
            f(&[("action", "doc-range"), ("name", "notes"), ("from", "2"), ("to", "3")])
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
            "doc remove p two", "doc transclude p w 1 2 at", "doc follow p", "doc show p --at",
            "doc show p --at x", "doc show p --raw --html", "doc diff p 1", "doc history p --raw", "doc range p 0 2",
            "doc pull"] {
            assert!(flags(bad).is_err(), "{bad} should be refused");
        }
        assert!(flags("doc mark p 2 underline").unwrap_err().starts_with("unknownKind: underline"));
    }
}
