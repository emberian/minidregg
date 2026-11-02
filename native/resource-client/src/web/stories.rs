//! `/story`: the stories this member plays and the invitations waiting for them. A story held is the
//! shell's own record (`HOME/story/NAME.json`, written by `story new` or `story join`); an
//! invitation is a `mini-story-invitation-v1` file in `HOME/requests` (where the door hands the
//! built-in tale's, and where `story join NAME @FILE` reads one). Joining, inviting and entering are
//! the derived `story` forms with what this page knows filled in; each answer is that leaf's one
//! outcome partial. Moves (`look`, `go`, `take`, `act`) are their own verbs and the tour's step 11.

use super::*;

pub(super) struct Invitation {
    pub file: String,
    pub story: String,
    pub role: String,
    pub author: String,
    pub recipient: String,
}

pub(super) struct Held {
    pub story: String,
    pub role: String,
    pub author: String,
    pub gm: String,
    pub current: bool,
}

fn home(site: &Site) -> Option<PathBuf> {
    site.shell.as_ref().map(|s| s.home.clone()).or_else(|| site.home.clone())
}

fn story_word(w: &str) -> bool {
    !w.is_empty() && w.len() <= 64 && w.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
}

/// The invitations in `HOME/requests`, bounded (64 files of at most 16 KiB are looked at).
pub(super) fn invitations(home: &std::path::Path) -> Vec<Invitation> {
    let mut out: Vec<Invitation> = fs::read_dir(home.join("requests"))
        .into_iter()
        .flatten()
        .flatten()
        .filter(|e| e.file_name().to_string_lossy().ends_with(".json"))
        .take(64)
        .filter_map(|e| {
            let file = e.file_name().to_string_lossy().into_owned();
            if file.starts_with('.') || file.contains('/') || e.metadata().ok()?.len() > 16 * 1024 {
                return None;
            }
            let v: Value = serde_json::from_slice(&fs::read(e.path()).ok()?).ok()?;
            if v["type"] != "mini-story-invitation-v1" {
                return None;
            }
            let s = |p: &str| v.pointer(p).and_then(Value::as_str).unwrap_or("").to_owned();
            let story = s("/story");
            story_word(&story).then(|| Invitation { file, role: s("/role"), author: s("/author"), recipient: s("/grant/recipient"), story })
        })
        .collect();
    out.sort_by(|a, b| (&a.story, &a.file).cmp(&(&b.story, &b.file)));
    out
}

/// The stories the shell holds a record of (`HOME/story/*.json`).
pub(super) fn held(home: &std::path::Path) -> Vec<Held> {
    let current = fs::read_to_string(home.join("story").join("current")).unwrap_or_default();
    let mut out: Vec<Held> = fs::read_dir(home.join("story"))
        .into_iter()
        .flatten()
        .flatten()
        .take(256)
        .filter_map(|e| {
            let name = e.file_name().to_string_lossy().strip_suffix(".json")?.to_owned();
            let v: Value = serde_json::from_slice(&fs::read(e.path()).ok()?).ok()?;
            let s = |k: &str| v[k].as_str().unwrap_or("").to_owned();
            Some(Held { current: current.trim() == name, role: s("role"), author: s("author"), gm: s("gm"), story: name })
        })
        .collect();
    out.sort_by(|a, b| a.story.cmp(&b.story));
    out
}

/// An invitation is still waiting unless the member already holds that story in that role (the
/// author who invites themself to play holds the story as `author` and joins as `player`).
fn pending(home: &std::path::Path) -> Vec<Invitation> {
    let have = held(home);
    invitations(home).into_iter().filter(|i| !have.iter().any(|h| h.story == i.story && h.role == i.role)).collect()
}

/// Invitations addressed to this member that still wait: what the front page and the door point at.
pub(super) fn waiting(site: &Site) -> Vec<Invitation> {
    let Some(home) = home(site) else { return Vec::new() };
    pending(&home).into_iter().filter(|i| i.recipient == site.subject).collect()
}

pub(super) fn page(site: &Site) -> Page {
    let Some(home) = home(site) else {
        return simple(200, "Stories", "this face has no home directory: stories are held by the shell's home");
    };
    let mine = held(&home);
    let mut body = String::from("<p class=\"eyebrow\">Sealed transition tables</p><p>Each player moves their own character cell; the story's sealed law checks every transition.</p><p class=note>Built-in tale invariant: Lean theorem <code>sealed_story_scene_monotone</code>.</p>\n");
    let pending = pending(&home);
    body.push_str("<section id=\"invitations\"><h2>Invitations waiting</h2>");
    if pending.is_empty() {
        body.push_str("<p class=\"empty\">No invitations waiting.</p>");
    }
    for inv in &pending {
        let to_me = inv.recipient == site.subject;
        body.push_str(&format!(
            "<article class=\"invitation\" data-story=\"{s}\" data-file=\"{f}\" data-to-me=\"{to_me}\"><h3>{s}</h3><p>From subject <code>{a}</code>, role <strong>{r}</strong> (<code>{f}</code> in requests).</p>",
            s = escape(&inv.story), f = escape(&inv.file), a = escape(&inv.author), r = escape(&inv.role)
        ));
        if to_me {
            if !site.front.read_only {
                let at = format!("@{}", inv.file);
                body.push_str(&super::verbs::form_for_filled("story", "story join", "/verb/story", "", &[("name", &inv.story), ("invitationfile", &at)]).unwrap_or_default());
            }
        } else {
            body.push_str(&format!(
                "<p class=note>Addressed to subject <code>{}</code>, not you (<code>{}</code>): the shell refuses to join it.</p>",
                escape(&inv.recipient), escape(&site.subject)
            ));
        }
        body.push_str("</article>");
    }
    body.push_str("</section>\n<section id=\"stories\"><h2>Your stories</h2>");
    if mine.is_empty() {
        body.push_str("<p>No stories held yet. Join an invitation above, or create one from the built-in tale:</p>");
        if !site.front.read_only {
            body.push_str(&super::verbs::form_for_filled("story", "story new", "/verb/story", "", &[("from", "tale")]).unwrap_or_default());
        }
    } else {
        body.push_str("<table><thead><tr><th>story</th><th>your role</th><th>author</th><th>GM</th></tr></thead><tbody>");
        for h in &mine {
            body.push_str(&format!(
                "<tr data-story=\"{s}\"><td><code>{s}</code>{}</td><td>{}</td><td><code>{}</code></td><td><code>{}</code></td></tr>",
                if h.current { " (current)" } else { "" }, escape(&h.role), escape(&h.author), escape(&h.gm), s = escape(&h.story)
            ));
        }
        body.push_str("</tbody></table>");
        if !site.front.read_only {
            for h in &mine {
                if !h.current {
                    body.push_str(&super::verbs::form_for_filled("story", "story enter", "/verb/story", "", &[("name", &h.story)]).unwrap_or_default());
                }
                // Only the author or the GM can grant a player cell; the law refuses anyone else.
                if h.author == site.subject || h.gm == site.subject {
                    body.push_str(&super::verbs::form_for_filled("story", "story invite", "/verb/story", "", &[("name", &h.story)]).unwrap_or_default());
                }
            }
        }
    }
    body.push_str("</section>\n");
    if !site.front.read_only {
        if let Some(cur) = mine.iter().find(|h| h.current) {
            body.push_str(&format!(
                "<section id=\"play\" data-current-story=\"{}\"><h2>Play <code>{}</code></h2><p class=\"note\">Inspect your current scene and exits with <code>look</code>, then move (`go`), pick up items (`take`), or act (`act`).</p>",
                escape(&cur.story), escape(&cur.story)
            ));
            for (v, leaf) in [("look", "look"), ("go", "go"), ("take", "take"), ("act", "act")] {
                body.push_str(&super::verbs::form_for_filled(v, leaf, &format!("/verb/{v}"), "", &[]).unwrap_or_default());
            }
            if cur.author == site.subject || cur.gm == site.subject {
                body.push_str(&super::verbs::form_for_filled("narrate", "narrate", "/verb/narrate", "", &[]).unwrap_or_default());
            }
            body.push_str("</section>\n");
        }
    }
    body.push_str("<p><a href=\"/tour#step-11\">Tour step 11: story moves</a> · <a href=\"/verb/look\">look</a> · <a href=\"/verb/go\">go</a> · <a href=\"/verb/story\">all story commands</a></p>");
    Page { status: 200, title: "Stories".into(), stamp: Stamp::None, body }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invitations_and_held_stories_are_read_from_the_shells_own_files() {
        let home = std::env::temp_dir().join(format!("stories-{}", std::process::id()));
        fs::create_dir_all(home.join("requests")).unwrap();
        fs::create_dir_all(home.join("story")).unwrap();
        let inv = |story: &str, to: &str| format!(r#"{{"type":"mini-story-invitation-v1","story":"{story}","role":"player","author":"7","gm":"7","grant":{{"recipient":"{to}"}}}}"#);
        fs::write(home.join("requests/tale-invite.json"), inv("tale", "42")).unwrap();
        fs::write(home.join("requests/odd-invite.json"), inv("odd", "43")).unwrap();
        fs::write(home.join("requests/bad.json"), inv("../x", "42")).unwrap();
        fs::write(home.join("requests/note.json"), r#"{"type":"something-else"}"#).unwrap();
        let found = invitations(&home);
        assert_eq!(found.iter().map(|i| (i.story.as_str(), i.recipient.as_str(), i.file.as_str())).collect::<Vec<_>>(),
            vec![("odd", "43", "odd-invite.json"), ("tale", "42", "tale-invite.json")], "a story name that is not a word is not an invitation");
        fs::write(home.join("story/tale.json"), r#"{"type":"mini-story-v1","story":"tale","role":"player","author":"7","gm":"7"}"#).unwrap();
        fs::write(home.join("story/current"), "tale\n").unwrap();
        let h = held(&home);
        assert_eq!((h.len(), h[0].story.as_str(), h[0].current, h[0].role.as_str()), (1, "tale", true, "player"));
        assert_eq!(pending(&home).iter().map(|i| i.story.as_str()).collect::<Vec<_>>(), vec!["odd"], "joined as player: tale no longer waits");
        fs::write(home.join("story/tale.json"), r#"{"type":"mini-story-v1","story":"tale","role":"author","author":"42","gm":"42"}"#).unwrap();
        assert_eq!(pending(&home).len(), 2, "the author invited to play still has the player's invitation waiting");
        fs::remove_dir_all(&home).unwrap();
    }
}
