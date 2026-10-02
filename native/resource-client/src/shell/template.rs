//! Room templates: files of shell lines (PLACE §4.9). A template is exactly
//! what a friend could type: `room new NAME --template T` binds `$ROOM` and
//! `$ME` (the founder's subject) and runs the lines in order as the founder;
//! `room welcome NAME SUBJECT --template T` runs the template's member lines
//! with `$MEMBER` bound too. Nothing here decides anything: every line is one
//! ordinary verb, and the Host judges each (the birth gate judges every
//! `--in $ROOM`).
//!
//! The built-in templates are the files under `deploy/shell/templates/room/`,
//! compiled in so a shell always has them; `room template show T` prints the
//! file byte for byte, and a friend's own copy is `--template @FILE` (from
//! HOME/requests). The files are the documentation.

use std::fs;
use std::io::Read;
use std::path::Path;

/// A built-in template: its name, its room lines, its member lines (if any).
struct Builtin {
    name: &'static str,
    room: &'static str,
    member: Option<&'static str>,
}

const BUILTINS: &[Builtin] = &[
    Builtin {
        name: "workroom",
        room: include_str!("../../../../deploy/shell/templates/room/workroom/template.shell"),
        member: None,
    },
    Builtin {
        name: "social",
        room: include_str!("../../../../deploy/shell/templates/room/social/template.shell"),
        member: Some(include_str!("../../../../deploy/shell/templates/room/social/member.shell")),
    },
    Builtin {
        name: "story",
        room: include_str!("../../../../deploy/shell/templates/room/story/template.shell"),
        member: None,
    },
];

/// Which lines of a template: the room's birth, or one member's welcome.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(super) enum Part {
    Room,
    Member,
}

impl Part {
    fn file(self) -> &'static str {
        match self {
            Part::Room => "template.shell",
            Part::Member => "member.shell",
        }
    }
}

/// The text of a template: a built-in name, or `@FILE` from HOME/requests.
/// Returns (label, text); the label is what refusals name.
pub(super) fn source(home: &Path, spec: &str, part: Part) -> Result<(String, String), String> {
    if let Some(file) = spec.strip_prefix('@') {
        return Ok((spec.to_owned(), session_text(home, file)?));
    }
    let builtin = BUILTINS
        .iter()
        .find(|builtin| builtin.name == spec)
        .ok_or_else(|| format!("no template {spec} (room template list; your own file is @FILE in HOME/requests)"))?;
    let text = match part {
        Part::Room => builtin.room,
        Part::Member => builtin
            .member
            .ok_or_else(|| format!("template {spec} has no member lines (only social does)"))?,
    };
    Ok((format!("{spec}/{}", part.file()), text.to_owned()))
}

fn session_text(home: &Path, file: &str) -> Result<String, String> {
    if file.is_empty()
        || file.len() > 64
        || file.starts_with('.')
        || !file.bytes().all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.'))
    {
        return Err("a template file must be a plain file name in HOME/requests (letters, digits, '-', '_', '.'; no leading dot)".into());
    }
    let path = home.join("requests").join(file);
    let mut bytes = Vec::new();
    fs::File::open(&path)
        .and_then(|f| f.take(1 << 16).read_to_end(&mut bytes))
        .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    String::from_utf8(bytes).map_err(|_| format!("{} is not UTF-8", path.display()))
}

/// The lines to run: every line that is not blank or a `#` comment, with each
/// `$NAME` placeholder replaced by its bound value, numbered as in the file.
/// A placeholder this template is not given refuses the whole template.
pub(super) fn bind(label: &str, text: &str, vars: &[(&str, &str)]) -> Result<Vec<(usize, String)>, String> {
    let mut out = Vec::new();
    for (index, raw) in text.lines().enumerate() {
        let number = index + 1;
        let trimmed = raw.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let mut line = String::with_capacity(trimmed.len());
        let mut rest = trimmed;
        while let Some(at) = rest.find('$') {
            line.push_str(&rest[..at]);
            let after = &rest[at + 1..];
            let end = after
                .find(|c: char| !c.is_ascii_uppercase())
                .unwrap_or(after.len());
            let name = &after[..end];
            let value = vars
                .iter()
                .find(|(var, _)| *var == name)
                .map(|(_, value)| *value)
                .ok_or_else(|| {
                    let given: Vec<String> = vars.iter().map(|(var, _)| format!("${var}")).collect();
                    format!(
                        "template {label} line {number}: unknown placeholder ${name} (this template binds {})",
                        given.join(", ")
                    )
                })?;
            line.push_str(value);
            rest = &after[end..];
        }
        line.push_str(rest);
        out.push((number, line));
    }
    Ok(out)
}

/// `room template list`: each built-in, what it is (its first comment line),
/// and whether it has member lines.
pub(super) fn list() -> String {
    let mut out = String::from("# room templates (deploy/shell/templates/room/); `room template show T` prints one\n");
    for builtin in BUILTINS {
        let about = builtin
            .room
            .lines()
            .find_map(|line| line.strip_prefix("# "))
            .unwrap_or("");
        out.push_str(&format!(
            "{}\t{}\t{}\n",
            builtin.name,
            about,
            if builtin.member.is_some() { "room welcome: yes" } else { "room welcome: no" }
        ));
    }
    out
}

/// `room template show T [member]`: the file, byte for byte.
pub(super) fn show(home: &Path, spec: &str, part: Part) -> Result<String, String> {
    source(home, spec, part).map(|(_, text)| text)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn placeholders_bind_and_unknown_ones_refuse() {
        let text = "# a comment\n\nroom new $ROOM --law open\n  doc new $ROOM/index 'subject == $ME' --in $ROOM  \n";
        let lines = bind("t", text, &[("ROOM", "lab"), ("ME", "7")]).unwrap();
        assert_eq!(
            lines,
            [
                (3, "room new lab --law open".to_owned()),
                (4, "doc new lab/index 'subject == 7' --in lab".to_owned())
            ]
        );
        let err = bind("t", "create $ROOM/s stream open --owner $MEMBER", &[("ROOM", "lab"), ("ME", "7")]).unwrap_err();
        assert!(err.contains("line 1") && err.contains("$MEMBER") && err.contains("$ROOM, $ME"), "{err}");
        // A `$` followed by no name is an empty placeholder, refused by name.
        assert!(bind("t", "doc append a b 'costs $5'", &[("ROOM", "lab")]).is_err());
    }

    #[test]
    fn builtins_are_the_files_and_member_lines_are_only_social() {
        let home = Path::new("/nonexistent");
        for builtin in BUILTINS {
            let (label, text) = source(home, builtin.name, Part::Room).unwrap();
            assert_eq!(label, format!("{}/template.shell", builtin.name));
            assert_eq!(text, builtin.room);
            // Every template births its room first, then an index in it.
            let lines = bind(&label, &text, &[("ROOM", "lab"), ("ME", "7")]).unwrap();
            assert_eq!(lines[0].1, "room new lab --law open");
            assert!(lines[1].1.starts_with("doc new lab/index "), "{}", lines[1].1);
            assert!(lines.iter().any(|(_, l)| l.starts_with("create lab/") && l.contains(" stream ")));
        }
        assert!(source(home, "social", Part::Member).is_ok());
        assert!(source(home, "workroom", Part::Member).unwrap_err().contains("no member lines"));
        assert!(source(home, "castle", Part::Room).unwrap_err().contains("room template list"));
        assert!(source(home, "@../etc/passwd", Part::Room).is_err());
        let listed = list();
        for name in ["workroom", "social", "story"] {
            assert!(listed.lines().any(|l| l.starts_with(&format!("{name}\t"))), "{listed}");
        }
        assert_eq!(show(home, "story", Part::Room).unwrap(), BUILTINS[2].room);
    }
}

#[cfg(test)]
mod plan_tests {
    use super::super::{plan, Plan, Session};
    use std::fs;
    use std::path::PathBuf;

    fn session(tag: &str) -> (PathBuf, Session) {
        let root = std::env::temp_dir().join(format!("mini-template-{tag}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("w")).unwrap();
        fs::create_dir_all(root.join("h").join("requests")).unwrap();
        fs::write(root.join("w").join("workspace.json"), br#"{"subject":"7"}"#).unwrap();
        let session = Session {
            workspace: root.join("w"),
            home: root.join("h"),
            host: PathBuf::from("/bin/host"),
            config: PathBuf::from("/c.json"),
        };
        (root, session)
    }

    fn lines(plan: Plan) -> (String, Vec<(usize, String)>) {
        match plan {
            Plan::Template { label, lines } => (label, lines),
            other => panic!("not a template plan: {other:?}"),
        }
    }

    #[test]
    fn room_new_with_a_template_is_its_lines_bound_and_planned() {
        let (root, s) = session("new");
        let (label, run) = lines(plan(&s, "room new lab --template workroom").unwrap());
        assert_eq!(label, "workroom/template.shell");
        let text: Vec<&str> = run.iter().map(|(_, l)| l.as_str()).collect();
        assert_eq!(text[0], "room new lab --law open");
        assert!(text[1].starts_with("doc new lab/index 'any [ not (verb == write), all [ subject == 7,"), "{}", text[1]);
        for born in ["create lab/wall stream open --in lab", "doc new lab/notes draft --in lab",
            "doc new lab/tasks note --in lab", "doc link lab-map-wall lab/index lab/wall", "submit lab-map-wall"] {
            assert!(text.contains(&born), "{born} missing from {text:?}");
        }
        // Line numbers are the file's.
        let file = super::source(&s.home, "workroom", super::Part::Room).unwrap().1;
        for (number, _) in &run {
            let raw = file.lines().nth(number - 1).unwrap();
            assert!(!raw.trim().is_empty() && !raw.trim_start().starts_with('#'));
        }
        let (_, run) = lines(plan(&s, "room welcome lab 12 --template social").unwrap());
        assert_eq!(run[0].1, "room invite lab-invite-12 lab 12 --verbs observe,place,append");
        assert_eq!(run.last().unwrap().1,
            "create lab/stream-12 stream 'any [ not (verb in {write, append}), subject == 12 ]' --in lab");
        for name in ["social", "story"] {
            let (_, run) = lines(plan(&s, &format!("room new r1 --template {name}")).unwrap());
            assert_eq!(run[0].1, "room new r1 --law open");
        }
        assert!(matches!(plan(&s, "room template list").unwrap(), Plan::Text(t) if t.contains("social\t")));
        assert!(matches!(plan(&s, "room template show social member").unwrap(), Plan::Text(t) if t.contains("subject == $MEMBER")));
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn a_bad_template_line_refuses_the_template_by_line_before_anything_runs() {
        let (root, s) = session("bad");
        let requests = s.home.join("requests");
        fs::write(requests.join("bad.shell"),
            "# mine\nroom new $ROOM --law open\ndoc new $ROOM/x castle --in $ROOM\ndoc new $ROOM/y draft --in $ROOM\n").unwrap();
        let err = plan(&s, "room new lab --template @bad.shell").unwrap_err();
        assert!(err.starts_with("template @bad.shell line 3: doc new lab/x castle --in lab"), "{err}");
        fs::write(requests.join("nest.shell"), "room new $ROOM --template workroom\n").unwrap();
        assert!(plan(&s, "room new lab --template @nest.shell").unwrap_err().contains("may not apply a template"));
        fs::write(requests.join("var.shell"), "room new $ROOM --law open\ncreate $ROOM/s stream open --owner $MEMBER\n").unwrap();
        assert!(plan(&s, "room new lab --template @var.shell").unwrap_err().contains("line 2: unknown placeholder $MEMBER"));
        fs::write(requests.join("empty.shell"), "# nothing\n").unwrap();
        assert!(plan(&s, "room new lab --template @empty.shell").unwrap_err().contains("no lines"));
        // A templated room is one segment: its lines name proposals after it.
        assert!(plan(&s, "room new lab/sub --template workroom").is_err());
        assert!(plan(&s, "room welcome lab 12 --template workroom").unwrap_err().contains("no member lines"));
        assert!(plan(&s, "room welcome lab 12").is_err());
        assert!(plan(&s, "room new lab --template workroom --x 1").is_err());
        let _ = fs::remove_dir_all(root);
    }
}
