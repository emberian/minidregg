//! What goes back to Discord: the shell's own output, or the shell's own ending line.
//!
//! `mini shell` ends every failed verb with one stderr line whose first word says who
//! decided (`error:` 1, `usage:` 2, `refused:` 3, `undecided:` 4). The entrance does not
//! reinterpret it: the first such line is returned verbatim. Output goes in a code block so
//! Discord markdown cannot restyle it, and is cut to Discord's 2000-character limit with a
//! note saying how much was shown.

/// Discord's message content limit, in characters.
pub const DISCORD_LIMIT: usize = 2000;

pub const ENDING_WORDS: [&str; 4] = ["error", "usage", "refused", "undecided"];

/// How a line ended, as the log and the reply name it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ending {
    /// `ok`, or one of [`ENDING_WORDS`].
    pub word: String,
    /// The ending line itself (empty for `ok`).
    pub line: String,
}

impl Ending {
    pub fn ok() -> Self {
        Ending { word: "ok".into(), line: String::new() }
    }

    /// An ending the entrance itself decided, before or instead of the shell.
    pub fn entrance(word: &str, text: &str) -> Self {
        debug_assert!(ENDING_WORDS.contains(&word));
        Ending { word: word.into(), line: format!("{word}: {text}") }
    }

    /// The shell's ending: exit 0 is `ok`; otherwise the first stderr line that starts with
    /// an ending word. A non-zero exit without one is reported as an `error:` that says so.
    pub fn of_shell(exit: Option<i32>, stderr: &str) -> Self {
        if exit == Some(0) {
            return Ending::ok();
        }
        for line in stderr.lines() {
            if let Some((word, _)) = line.split_once(':') {
                if ENDING_WORDS.contains(&word) {
                    return Ending { word: word.into(), line: line.to_string() };
                }
            }
        }
        let how = match exit {
            Some(code) => format!("exited {code}"),
            None => "was stopped by a signal".to_string(),
        };
        Ending::entrance("error", &format!("mini shell {how} without an ending line"))
    }
}

/// The reply for a line that ran.
pub fn render(stdout: &str, ending: &Ending) -> String {
    if ending.word == "ok" {
        if stdout.trim().is_empty() {
            return "done (no output)".to_string();
        }
        code_block(stdout.trim_end())
    } else {
        code_block(&ending.line)
    }
}

/// `body` in a code block, cut to [`DISCORD_LIMIT`] characters with a note when it is long.
pub fn code_block(body: &str) -> String {
    // A literal ``` inside would close the block early; a zero-width space breaks it.
    let body = body.replace("```", "``\u{200b}`");
    let total = body.chars().count();
    let full = format!("```\n{body}\n```");
    if full.chars().count() <= DISCORD_LIMIT {
        return full;
    }
    let note = |shown: usize| {
        format!("\n(truncated: {shown} of {total} characters shown; the whole output stays in the session)")
    };
    // `shown <= total`, so the note is at most as long as with `total`.
    let budget = DISCORD_LIMIT - "```\n\n```".chars().count() - note(total).chars().count();
    let shown: String = body.chars().take(budget).collect();
    let n = shown.chars().count();
    format!("```\n{shown}\n```{}", note(n))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ending_is_the_first_ending_line_verbatim() {
        let stderr = "workspace read attempt: /x\nrefused: no-grant: this key holds no grant (Host refused query, reply byte 255)\n  outcome …\nerror: later\n";
        let e = Ending::of_shell(Some(3), stderr);
        assert_eq!(e.word, "refused");
        assert_eq!(e.line, "refused: no-grant: this key holds no grant (Host refused query, reply byte 255)");
        assert_eq!(Ending::of_shell(Some(0), stderr), Ending::ok());
        let none = Ending::of_shell(Some(9), "boom\n");
        assert_eq!(none.word, "error");
        assert_eq!(none.line, "error: mini shell exited 9 without an ending line");
        assert_eq!(Ending::of_shell(None, "").line, "error: mini shell was stopped by a signal without an ending line");
        // prose containing the word later in a line is not an ending
        assert_eq!(Ending::of_shell(Some(1), "the host refused: no\n").word, "error");
    }

    #[test]
    fn render_ok_failure_and_empty() {
        assert_eq!(render("", &Ending::ok()), "done (no output)");
        assert_eq!(render("{\"a\":1}\n", &Ending::ok()), "```\n{\"a\":1}\n```");
        let e = Ending::of_shell(Some(2), "usage: read REF\n");
        assert_eq!(render("ignored", &e), "```\nusage: read REF\n```");
    }

    #[test]
    fn long_output_is_cut_to_the_limit_with_a_note() {
        let long = "x".repeat(5000);
        let out = code_block(&long);
        assert!(out.chars().count() <= DISCORD_LIMIT, "{}", out.chars().count());
        assert!(out.contains("of 5000 characters shown"));
        let exact = "y".repeat(DISCORD_LIMIT - 8);
        assert_eq!(code_block(&exact).chars().count(), DISCORD_LIMIT);
        assert!(!code_block(&exact).contains("truncated"));
        let wide = "é".repeat(3000);
        assert!(code_block(&wide).chars().count() <= DISCORD_LIMIT);
    }

    #[test]
    fn fences_inside_output_cannot_close_the_block() {
        let out = code_block("a```b");
        assert_eq!(out.matches("```").count(), 2);
    }
}
