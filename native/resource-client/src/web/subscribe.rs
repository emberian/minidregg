//! `/subscribe`: the subscriber tier (L4's `subscribers` room, deploy/hermes/README.md "The
//! subscriber tier"). What it buys is read from the box's provider table (the `zai-glm` row: its
//! model and each member's share of the spend ceiling, in calls); the price and period from the
//! room (`tariff subscribers`); the member's window from `room status subscribers`, its end height
//! said as a date at one height a minute. Subscribe is `pay subscribers week`; joining the room's
//! chat is `chat join subscribers` with the founder-signed invitation the concierge drops into
//! HOME/inbox. Every action is the member's own shell line through the one outcome partial.

use super::body::{act, answer_html, verb, Shell};
use super::*;

pub(super) const ROOM: &str = "subscribers";
const ROW: &str = "zai-glm";
const PROVIDERS: &str = "/etc/mini/providers.json";
/// ember's retention and provider sentence (one file, read by the door and this body alike).
pub(super) const RETENTION: &str = include_str!("../../../../deploy/policy/RETENTION.txt");

/// What the tier buys, from the provider table: (model, calls a day, calls until the weekly reset).
pub(super) fn offer(table: &Value) -> Option<(String, u64, u64)> {
    let row = table["providers"].as_array()?.iter().find(|r| r["name"] == ROW)?;
    let caps = &row["caps"];
    let n = |k: &str| caps[k].as_str().and_then(|v| v.parse::<u64>().ok());
    let call = n("callMicroUsd").filter(|c| *c > 0)?;
    Some((row["models"][0].as_str()?.to_owned(), n("memberDayMicroUsd")? / call, n("memberTotalMicroUsd")? / call))
}

/// The tier in two sentences, for the front page and this page; nothing when the box's provider
/// table has no such row.
pub(super) fn summary() -> Option<String> {
    let table: Value = serde_json::from_slice(&fs::read(PROVIDERS).ok()?).ok()?;
    let (model, day, total) = offer(&table)?;
    Some(format!(
        "A house Hermes on <code>{}</code> answers in the <code>{ROOM}</code> room. Each subscriber may spend up to <strong>{day} model calls a day</strong> (an ask is a few calls) and {total} until the plan's weekly reset; past either, the broker refuses by name (<code>member-day-ceiling</code>, <code>member-total-ceiling</code>).",
        escape(&model)
    ))
}

/// `room status` names the room's height and the member's window end: (height, notAfter).
pub(super) fn window(status: &str) -> (Option<u64>, Option<u64>) {
    let height = status.lines().find_map(|l| l.trim().strip_prefix(&format!("room {ROOM} ")).and_then(|r| r.split(" at height ").nth(1)).and_then(|h| h.trim().parse().ok()));
    let until = status.lines().find_map(|l| {
        let l = l.trim();
        l.strip_prefix("my window: member until height ").or_else(|| l.strip_prefix("my window: ENDED at height ")).and_then(|r| r.split_whitespace().next()).and_then(|h| h.parse().ok())
    });
    (height, until)
}

/// A UTC date for a unix time (days from the civil-from-days algorithm), to the minute.
pub(crate) fn utc(secs: u64) -> String {
    let days = (secs / 86_400) as i64;
    let (h, m) = ((secs % 86_400) / 3600, (secs % 3600) / 60);
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let mo = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + i64::from(mo <= 2);
    format!("{y:04}-{mo:02}-{d:02} {h:02}:{m:02} UTC")
}

fn now() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

pub(super) fn missing_room_ref(text: &str) -> bool {
    text.contains("unknown reference")
        || text.contains("No such file or directory")
        || text.contains("subscribers.json")
}

pub(super) fn page(site: &Site, said: Option<String>) -> Page {
    super::body::import_inbox(site);
    let mut body = String::new();
    body.push_str(&format!("<section><h2>What it buys</h2><p>{}</p>", summary().unwrap_or_else(|| "This box's provider table has no subscriber route.".to_owned())));
    body.push_str(&format!("<p class=\"policy\">{}</p></section>\n", escape(RETENTION.trim_end())));
    if let Some(said) = said {
        body.push_str(&said);
    }
    if let Some(ending) = verb(site, &[format!("tariff {ROOM}")]) {
        if ending.code == 0 {
            body.push_str(&format!("<section><h2>Price</h2>{}</section>\n", answer_html(&ending, &[])));
        } else if missing_room_ref(&ending.stderr) {
            body.push_str(&format!("<section><h2>Price</h2><p class=\"note\">This workspace does not hold the <code>{ROOM}</code> room reference yet.</p></section>\n"));
        } else {
            body.push_str(&format!("<section><h2>Price</h2>{}</section>\n", answer_html(&ending, &[])));
        }
    }
    body.push_str("<section data-load=\"/purse/meter\"><div class=\"fill\"><p class=\"note\"><a href=\"/purse\">your purse, as a meter</a></p></div></section>\n");
    if let Some(ending) = verb(site, &[format!("room status {ROOM}")]) {
        if ending.code != 0 && missing_room_ref(&ending.stderr) {
            body.push_str(&format!(
                "<section><h2>Your window</h2><p class=\"big\">Not a member yet.</p><p class=\"note\">No <code>{ROOM}</code> reference in this workspace yet.</p></section>\n"
            ));
        } else {
            let (height, until) = window(&ending.stdout);
            let when = match (height, until) {
                (Some(h), Some(a)) if a >= h => format!("<p class=\"big\">Member until height {a}: about <strong>{}</strong> (at one height a minute).</p>", utc(now() + (a - h) * 60)),
                (Some(h), Some(a)) => format!("<p class=\"big\">Your window ended at height {a}, about {} ago.</p>", minutes(h - a)),
                _ => "<p class=\"big\">Not a member yet.</p>".to_owned(),
            };
            body.push_str(&format!("<section><h2>Your window</h2>{when}{}</section>\n", answer_html(&ending, &[])));
        }
    }
    body.push_str(&format!(
        "<section><h2>Subscribe</h2><form method=\"post\" action=\"/subscribe/pay\"><p><code>pay {ROOM} week</code>: pays the room tariff from your purse for one week; paying again extends the window.</p><button>Subscribe</button></form>\
         <form method=\"post\" action=\"/subscribe/join\"><p>Join the room chat once with the invitation from your inbox (<code>chat join {ROOM}</code>).</p><button>Join the room</button></form></section>\n"
    ));
    Page { status: 200, title: "Subscribe".into(), stamp: Stamp::None, body }
}

fn minutes(n: u64) -> String {
    if n >= 1440 { format!("{} days", n / 1440) } else if n >= 60 { format!("{} hours", n / 60) } else { format!("{n} minutes") }
}

pub(super) fn pay(site: &Site) -> Page {
    super::body::import_inbox(site);
    if let Some(ending) = verb(site, &[format!("tariff {ROOM}")]) {
        if ending.code != 0 && missing_room_ref(&ending.stderr) {
            return page(site, Some(format!("<p class=\"note\">This workspace does not hold the <code>{ROOM}</code> room reference yet.</p>")));
        }
    }
    let mut page = act(site, "Subscribe", vec![format!("pay {ROOM} week")], "", &[("subscribe", "/subscribe")]);
    page.title = "Subscribe".into();
    page
}

/// The concierge's invitation: a delegated reference in HOME/inbox to this subject, a room grant
/// on the room's own target. The newest such file is the one to take.
fn invitation(shell: &Shell, me: &str, target: &str) -> Option<(String, Value)> {
    let mut found: Vec<(std::time::SystemTime, String, Value)> = Vec::new();
    for entry in fs::read_dir(shell.home.join("inbox")).ok()?.flatten() {
        let Ok(bytes) = fs::read(entry.path()) else { continue };
        let Ok(value) = serde_json::from_slice::<Value>(&bytes) else { continue };
        if value["type"] == "minidregg-delegated-reference-v1" && value["room"] == true && value["recipient"] == me && value["target"] == target {
            let at = entry.metadata().and_then(|m| m.modified()).unwrap_or(std::time::UNIX_EPOCH);
            found.push((at, entry.file_name().to_string_lossy().into_owned(), value));
        }
    }
    found.sort_by_key(|f| f.0);
    found.pop().map(|(_, name, value)| (name, value))
}

pub(super) fn join(site: &Site) -> Page {
    super::body::import_inbox(site);
    let Some(shell) = site.shell.as_ref() else { return page(site, Some("<p class=\"note\">This body has no shell paths.</p>".into())) };
    let target = verb(site, &[format!("room status {ROOM}")]).and_then(|e| {
        e.stdout.lines().find_map(|l| l.trim().strip_prefix(&format!("room {ROOM} (")).and_then(|r| r.split(')').next()).map(str::to_owned))
    });
    let Some(target) = target else {
        return page(site, Some(format!("<p class=\"note\">This workspace holds no <code>{ROOM}</code> room yet: subscribe first; the concierge delivers it within a minute.</p>")));
    };
    let Some((file, invitation)) = invitation(shell, &site.subject, &target) else {
        return page(site, Some("<p class=\"note\">No invitation from the room is in your inbox yet: the concierge delivers one within a minute of your payment. Reload, then press Join again.</p>".into()));
    };
    let json = serde_json::to_string(&invitation).unwrap_or_default();
    let mut page = act(site, "Join the subscribers room", vec![format!("chat join {ROOM} {json}")], "", &[("subscribe", "/subscribe"), ("the room", &format!("/room/{ROOM}"))]);
    page.body.insert_str(0, &format!("<p class=\"note\">The invitation: <code>inbox/{}</code>.</p>", escape(&file)));
    page
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    #[test]
    fn the_offer_is_read_from_the_provider_row() {
        let table = json!({"providers":[{"name":"zai-glm","models":["glm-5.3","glm-5.3-flash"],
            "caps":{"perCall":"4096","perDay":"140","ceilingMicroUsd":"70000","callMicroUsd":"500","memberDayMicroUsd":"10000","memberTotalMicroUsd":"35000"}}]});
        assert_eq!(super::offer(&table), Some(("glm-5.3".to_owned(), 20, 70)));
        assert_eq!(super::offer(&json!({"providers":[]})), None);
    }

    #[test]
    fn the_window_is_read_from_room_status_and_dated() {
        let status = "room subscribers (123) at height 1000\n  my window: member until height 44200 (43200 heights left; capability 9)\n";
        assert_eq!(super::window(status), (Some(1000), Some(44200)));
        assert_eq!(super::window("room subscribers (123) at height 1000\n  my window: none (guest; `pay subscribers week` buys one)\n"), (Some(1000), None));
        assert_eq!(super::utc(1_794_268_800), "2026-11-10 00:00 UTC");
        assert_eq!(super::utc(0), "1970-01-01 00:00 UTC");
    }

    #[test]
    fn missing_subscribers_ref_error_is_detected() {
        assert!(super::missing_room_ref("error: cannot read /var/lib/mini/members/uxprobe/home/workspace/refs/subscribers.json: No such file or directory (os error 2)"));
        assert!(super::missing_room_ref("error: unknown reference subscribers"));
        assert!(!super::missing_room_ref("error: permission denied"));
    }
}
