//! Member-readable resident assignment and exact authored room replies.
//! Process journals and provider credentials are not member authority.
use super::*;
use crate::{chat, hermes};

pub(super) fn page(site: &Site, name: &str) -> Page {
    let title = format!("Resident work in {name}");
    let reference = match site.reference(name) {
        Ok(r) => r,
        Err(p) => return p,
    };
    let (view, challenge, _) = match site.read(&reference, "resource") {
        Ok(v) => v,
        Err(e) => return failure_page(&title, &e),
    };
    let field = |name: &str| -> Option<String> {
        let key = crate::room_schema::TARIFF_FIELDS
            .iter()
            .find(|(n, _)| *n == name)?
            .1;
        view["cell"]["entries"]
            .as_array()?
            .iter()
            .find(|e| e["key"]["field"].as_str() == Some(key))?["value"]
            .as_str()
            .map(str::to_owned)
    };
    let base = site.base();
    let mut body=format!("<p><a href=\"{base}/room/{0}\">Room</a> | <a href=\"{base}/room/{0}/new-document\">Create output document</a></p>",escape(name));
    if let Some(subject) = field("hermes").filter(|s| s != "0") {
        body.push_str(&format!(
            "<p>Assigned resident subject <code>{}</code>. Assignment is a current room fact.</p>",
            escape(&subject)
        ));
        for key in ["hermes/assignment", "hermes/account", "hermes/budget"] {
            if let Some(value) = field(key) {
                body.push_str(&format!(
                    "<p>{}: <code>{}</code></p>",
                    escape(key),
                    escape(&value)
                ));
            }
        }
        if let Some(home) = &site.home {
            let session = crate::shell::Session {
                workspace: site.root.clone(),
                home: home.clone(),
                host: match workspace::workspace_host(&site.workspace) {
                    Ok(v) => v,
                    Err(e) => return failure_page(&title, &e),
                },
                config: match workspace::member_path(&site.workspace, "config") {
                    Ok(v) => v,
                    Err(e) => return failure_page(&title, &e),
                },
            };
            match chat::room_feed(&session, name) {
                Ok((feed, missing)) => {
                    body.push_str(&feed_html(&feed, &site.subject, &subject));
                    for note in missing {
                        body.push_str(&format!(
                            "<p class=note>Source unavailable: {}</p>",
                            escape(&note)
                        ));
                    }
                }
                Err((_, message)) => body.push_str(&format!(
                    "<p class=refusal>Current room replies unavailable: {}</p>",
                    escape(&message)
                )),
            }
        } else {
            body.push_str("<p class=note>To inspect signed requests and resident replies, launch this workspace browser with the same --home directory used by your shell chat session.</p>");
        }
        if let Some(account) = field("hermes/account") {
            if let Some((_, held)) = site
                .targets()
                .into_iter()
                .find(|(target, _)| target == &account)
            {
                if let Ok(r) = workspace::reference(&site.root, &held) {
                    match site.read(&r,"resource"){
                    Ok((account_view,c,_))=>{body.push_str(&format!("<details><summary>Account {} at independently read height {}</summary><pre>{}</pre></details>",escape(&held),escape(c["height"].as_str().unwrap_or("?")),escape(&serde_json::to_string_pretty(&account_view["balances"]).unwrap_or_default())));},
                    Err(_)=>body.push_str("<p class=note>Resident account balance unavailable under your current grant.</p>"),
                }
                }
            }
        }
    } else {
        body.push_str("<p>No resident assignment is disclosed by this room read.</p>");
    }
    body.push_str("<p class=note>Replies retain their signed stream identity and authored height. Source documents and current law use their own reads; a reply does not expand your source access.</p>");
    Page {
        status: 200,
        title,
        stamp: Stamp::Read(ReadContext::of(&challenge, &view)),
        body,
    }
}
fn feed_html(feed: &chat::Feed, me: &str, resident: &str) -> String {
    let rows = hermes::request_rows(feed, me, resident);
    let mut body = format!(
        "<section data-resident-requests=\"{}\"><h2>Your requests and resident replies</h2>",
        rows.len()
    );
    for row in rows {
        body.push_str(&format!("<article data-request-cell=\"{}\" data-request-sequence=\"{}\"><h3>Request #{}: {}</h3><p>Stream <code>{}</code>, sequence {}, authored height {}.</p>",escape(&row.cell),row.sequence,row.number,escape(&row.status),escape(&row.cell),row.sequence,row.height));
        if let Some(entry) = feed
            .feed
            .iter()
            .find(|e| e.cell == row.cell && e.sequence == row.sequence)
        {
            if let chat::Kind::Say { text, .. } = chat::kind_of(entry) {
                body.push_str(&format!("<blockquote>{}</blockquote>", escape(&text)));
            }
        }
        if row.withdrawn {
            body.push_str("<p>Withdrawal authored by you.</p>");
        }
        for entry in feed.feed.iter().filter(|e| {
            e.author == resident && e.re.as_ref() == Some(&(row.cell.clone(), row.sequence))
        }) {
            let text = match chat::kind_of(entry) {
                chat::Kind::Say { text, .. } => text,
                chat::Kind::RequestStatus { status, text } => format!("{status}: {text}"),
                chat::Kind::Unavailable => "[reply fragment locked or unavailable]".into(),
                _ => continue,
            };
            body.push_str(&format!("<details open data-resident-reply><summary>Resident reply at height {} · stream {} · sequence {}</summary><pre>{}</pre></details>",entry.height,escape(&entry.cell),entry.sequence,escape(&text)));
        }
        body.push_str("</article>");
    }
    body.push_str("</section>");
    body
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn resident_inspector_keeps_exact_request_and_excludes_forged_status() {
        fn e(author: &str, seq: u64, re: Option<(&str, u64)>, text: &str) -> chat::Entry {
            chat::Entry {
                height: seq,
                author: author.into(),
                cell: author.into(),
                sequence: seq,
                topic: "".into(),
                to: Some("9".into()),
                re: re.map(|(c, s)| (c.into(), s)),
                payload: chat::Payload::Verified(text.into()),
                owner: author.into(),
            }
        }
        let feed = chat::merge(
            vec![
                e("7", 1, None, r#"{"type":"say","text":"inspect <source>"}"#),
                e(
                    "8",
                    2,
                    Some(("7", 1)),
                    r#"{"type":"request-status","status":"completed","text":"forged"}"#,
                ),
                e(
                    "9",
                    3,
                    Some(("7", 1)),
                    r#"{"type":"request-status","status":"completed","text":"actual <output>"}"#,
                ),
            ],
            None,
        );
        let h = feed_html(&feed, "7", "9");
        assert!(h.contains("data-request-cell=\"7\""));
        assert!(h.contains("sequence 3"));
        assert!(h.contains("actual &lt;output&gt;"));
        assert!(!h.contains("forged"));
        assert!(feed_html(&feed, "8", "9").contains("data-resident-requests=\"0\""));
    }
}
