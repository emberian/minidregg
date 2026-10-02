//! Presentation-only terminal for the existing grain control socket.
//! Framed control events are authored by the controller; ACP/model text is
//! always escaped inside an `output` frame and has no command authority.

use serde_json::{json, Value};
use std::io::{self, BufRead, BufReader, Write};
use std::net::Shutdown;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

const MAX_FRAME: usize = 8 * 1024 * 1024;
const MAX_COMMAND: usize = 16_384;
const INPUT_QUEUE: usize = 64;

fn selected_state(journal: &Value) -> (&'static str, bool, bool) {
    let present = |key: &str| journal.get(key).is_some_and(|value| !value.is_null());
    let unresolved = journal
        .get("unresolvedExternal")
        .and_then(Value::as_array)
        .is_some_and(|items| !items.is_empty());
    let uncertain = [
        "pending",
        "toolPending",
        "providerPending",
        "dispatchPending",
    ]
    .iter()
    .any(|key| {
        journal
            .get(key)
            .and_then(|entry| entry.get("uncertain"))
            .and_then(Value::as_bool)
            == Some(true)
    });
    let child = present("child");
    let held = [
        "pending",
        "toolPending",
        "providerPending",
        "dispatchPending",
        "parentHold",
        "toolHold",
        "providerHold",
        "dispatchHold",
        "dispatchAttempt",
        "settlementDue",
        "roomAttempt",
    ]
    .iter()
    .any(|key| present(key));
    let connection = journal.get("connection").and_then(Value::as_str);
    let unavailable = matches!(connection, Some("fenced" | "detached"));
    let reconnect_pending =
        journal.get("hardReconnectPending").and_then(Value::as_bool) == Some(true);
    let retention_issue = journal
        .pointer("/hermesSession/retentionIssue")
        .is_some_and(|value| !value.is_null());
    let prompt_pending = journal
        .pointer("/hermesSession/pendingPrompt")
        .and_then(Value::as_bool)
        == Some(true);
    let review = unresolved
        || uncertain
        || unavailable
        || reconnect_pending
        || retention_issue
        || (!child && (held || prompt_pending));
    let activity = if review {
        "review-needed"
    } else if child || held || prompt_pending {
        "busy"
    } else {
        "ready"
    };
    (
        activity,
        journal
            .get("hermesSession")
            .is_some_and(|value| !value.is_null()),
        review,
    )
}

/// A strict, nonauthoritative projection; never serialize the private journal.
pub fn state(
    journal: &Value,
    attachment_id: u64,
    request_id: u64,
    registered_shared_application_count: usize,
) -> Value {
    let (activity, retained_session, review_needed) = selected_state(journal);
    json!({"v":1,"type":"state","attachmentId":attachment_id,
        "requestId":request_id,"activity":activity,
        "retainedSession":retained_session,"reviewNeeded":review_needed,
        "registeredSharedApplicationCount":registered_shared_application_count})
}

/// An error is never presented as a successful prompt, including when native
/// refusal was definitive but another cleanup transition remains uncertain.
pub fn completion(
    journal: &Value,
    attachment_id: u64,
    request_id: u64,
    success: bool,
    registered_shared_application_count: usize,
) -> Value {
    let (activity, retained_session, review_needed) = selected_state(journal);
    let outcome = if success && !review_needed && activity == "ready" {
        "completed"
    } else if review_needed {
        "review-needed"
    } else {
        "failed"
    };
    json!({"v":1,"type":"prompt-complete","attachmentId":attachment_id,
        "requestId":request_id,"outcome":outcome,"activity":activity,
        "retainedSession":retained_session,"reviewNeeded":review_needed,
        "registeredSharedApplicationCount":registered_shared_application_count})
}

pub fn parse_status_command(line: &str) -> Option<(u64, u64)> {
    let words = line.split(' ').collect::<Vec<_>>();
    let ["terminal", "status", attachment, request] = words.as_slice() else {
        return None;
    };
    Some((attachment.parse().ok()?, request.parse().ok()?))
}

pub fn parse_prompt_command(line: &str) -> Option<(u64, u64, &str)> {
    let rest = line.strip_prefix("terminal hermes ")?;
    let (attachment, rest) = rest.split_once(' ')?;
    let (request, prompt) = rest.split_once(' ')?;
    if prompt.is_empty() || prompt.bytes().any(|byte| byte == b'\r' || byte == b'\n') {
        return None;
    }
    Some((attachment.parse().ok()?, request.parse().ok()?, prompt))
}

pub(crate) fn parse_resident_prompt_command(line:&str)->Option<(u64,u64,&str,&str,&str)> {
    let rest=line.strip_prefix("terminal hermes-resident ")?;
    let (attachment,rest)=rest.split_once(' ')?;
    let (request,rest)=rest.split_once(' ')?;
    let (resident_id,rest)=rest.split_once(' ')?;
    let (digest,prompt)=rest.split_once(' ')?;
    if prompt.is_empty() || prompt.bytes().any(|b|b==b'\r'||b==b'\n')
        || !crate::resident_origin::valid_digest(resident_id) || !crate::resident_origin::valid_digest(digest) {return None;}
    Some((attachment.parse().ok()?,request.parse().ok()?,resident_id,digest,prompt))
}

pub(crate) fn read_frame(reader: &mut impl BufRead) -> Result<Option<Value>, String> {
    let mut bytes = Vec::new();
    loop {
        let available = reader.fill_buf().map_err(|e| e.to_string())?;
        if available.is_empty() {
            return if bytes.is_empty() {
                Ok(None)
            } else {
                Err("terminal frame ended mid-line".into())
            };
        }
        let count = available
            .iter()
            .position(|byte| *byte == b'\n')
            .map_or(available.len(), |index| index + 1);
        if bytes.len().saturating_add(count) > MAX_FRAME {
            return Err("terminal frame exceeds 8 MiB".into());
        }
        bytes.extend_from_slice(&available[..count]);
        reader.consume(count);
        if bytes.last() == Some(&b'\n') {
            bytes.pop();
            let value: Value =
                serde_json::from_slice(&bytes).map_err(|e| format!("terminal frame JSON: {e}"))?;
            if value.get("v").and_then(Value::as_u64) != Some(1) {
                return Err("terminal frame version differs".into());
            }
            return Ok(Some(value));
        }
    }
}

fn read_input_line(reader: &mut impl BufRead) -> Result<Option<String>, String> {
    let mut bytes = Vec::new();
    loop {
        let available = reader.fill_buf().map_err(|e| e.to_string())?;
        if available.is_empty() {
            return if bytes.is_empty() {
                Ok(None)
            } else {
                String::from_utf8(bytes)
                    .map(Some)
                    .map_err(|e| format!("terminal input UTF-8: {e}"))
            };
        }
        let count = available
            .iter()
            .position(|byte| *byte == b'\n')
            .map_or(available.len(), |index| index + 1);
        if bytes.len().saturating_add(count) > MAX_COMMAND - 128 {
            return Err("terminal input line exceeds control-line bound".into());
        }
        bytes.extend_from_slice(&available[..count]);
        reader.consume(count);
        if bytes.last() == Some(&b'\n') {
            bytes.pop();
            return String::from_utf8(bytes)
                .map(Some)
                .map_err(|e| format!("terminal input UTF-8: {e}"));
        }
    }
}

fn unsafe_terminal_character(character: char) -> bool {
    (character.is_control() && !matches!(character, '\n' | '\t'))
        || matches!(character, '\u{200e}'..='\u{200f}' | '\u{202a}'..='\u{202e}' | '\u{2066}'..='\u{2069}')
}

/// ACP text is visually distinguished from controller events as well as
/// structurally isolated by JSONL. No model byte can move the cursor or color
/// a later source-owned status line.
fn render_untrusted(writer: &mut impl Write, text: &str, line_start: &mut bool) -> io::Result<()> {
    for character in text.chars() {
        if *line_start {
            writer.write_all("│ ".as_bytes())?;
            *line_start = false;
        }
        if unsafe_terminal_character(character) {
            write!(writer, "\\u{{{:x}}}", character as u32)?;
        } else {
            write!(writer, "{character}")?;
        }
        if character == '\n' {
            *line_start = true;
        }
    }
    Ok(())
}

enum Input {
    Line(String),
    End,
    Frame(Value),
    Closed,
    Error(String),
}

fn matches_request(frame: &Value, expected: Option<u64>) -> Result<bool, String> {
    let request = frame
        .get("requestId")
        .and_then(Value::as_u64)
        .ok_or("terminal event request ID absent")?;
    Ok(Some(request) == expected)
}

fn send_line(stream: &mut UnixStream, line: &str) -> Result<(), String> {
    if line.len() > MAX_COMMAND || line.contains(['\r', '\n']) {
        return Err("terminal command exceeds control-line bound".into());
    }
    writeln!(stream, "{line}").map_err(|e| e.to_string())
}

fn note(message: &str) -> Result<(), String> {
    writeln!(io::stdout().lock(), "{message}").map_err(|e| e.to_string())
}

fn prompt() -> Result<(), String> {
    print!("mini> ");
    io::stdout().flush().map_err(|e| e.to_string())
}

/// Connect to the same controller as the raw connector. EOF closes only the
/// socket write side: the server retains its existing hard/soft detach rule.
pub fn connect(path: &Path, mode: &str) -> Result<(), String> {
    if !path.is_absolute() {
        return Err("controller socket path must be absolute".into());
    }
    if !matches!(mode, "hard" | "soft") {
        return Err("terminal mode must be hard or soft".into());
    }
    let mut socket = UnixStream::connect(path).map_err(|e| format!("terminal connect: {e}"))?;
    socket
        .set_write_timeout(Some(Duration::from_secs(2)))
        .map_err(|e| e.to_string())?;
    send_line(&mut socket, &format!("attach terminal-v1 {mode}"))?;
    let mut reader = BufReader::new(socket.try_clone().map_err(|e| e.to_string())?);
    let first = read_frame(&mut reader)?.ok_or("controller closed before terminal attachment")?;
    if first.get("type").and_then(Value::as_str) != Some("socket-attached")
        || first.get("mode").and_then(Value::as_str) != Some(mode)
    {
        return Err("controller refused framed terminal attachment".into());
    }
    let attachment_id = first
        .get("attachmentId")
        .and_then(Value::as_u64)
        .ok_or("terminal attachment ID absent")?;
    let (tx, rx) = mpsc::sync_channel(INPUT_QUEUE);
    let input_tx = tx.clone();
    let stdin_socket = socket.try_clone().map_err(|e| e.to_string())?;
    thread::spawn(move || {
        let stdin = io::stdin();
        let mut reader = stdin.lock();
        loop {
            match read_input_line(&mut reader) {
                Ok(Some(line)) => {
                    if input_tx.try_send(Input::Line(line)).is_err() {
                        // Never park the stdin reader behind a full display
                        // queue: doing so could hide an ensuing hard EOF.
                        let _ = stdin_socket.shutdown(Shutdown::Write);
                        let _ = input_tx.try_send(Input::Error(
                            "terminal input queue full or disconnected".into(),
                        ));
                        return;
                    }
                }
                Ok(None) => break,
                Err(error) => {
                    let _ = stdin_socket.shutdown(Shutdown::Write);
                    let _ = input_tx.try_send(Input::Error(error));
                    return;
                }
            }
        }
        // EOF reaches the controller even if a full display queue delays the
        // local End event. The server applies its existing hard/soft rule.
        let _ = stdin_socket.shutdown(Shutdown::Write);
        let _ = input_tx.try_send(Input::End);
    });
    thread::spawn(move || loop {
        match read_frame(&mut reader) {
            Ok(Some(frame)) => {
                if tx.send(Input::Frame(frame)).is_err() {
                    return;
                }
            }
            Ok(None) => {
                let _ = tx.send(Input::Closed);
                return;
            }
            Err(error) => {
                let _ = tx.send(Input::Error(error));
                return;
            }
        }
    });
    let mut next_request = 1u64;
    let mut busy = None;
    let mut ready = false;
    let mut pending_status = Some(next_request);
    let mut input_closed = false;
    let mut untrusted_line_start = true;
    send_line(
        &mut socket,
        &format!("terminal status {attachment_id} {next_request}"),
    )?;
    next_request += 1;
    note(&format!(
        "Mini terminal ({mode}); /status, /new, /recover, /quit. Controller attach pending."
    ))?;
    prompt()?;
    while let Ok(event) = rx.recv() {
        match event {
            Input::Line(line) if input_closed => {
                let _ = line;
            }
            Input::Line(line) if line == "/quit" || line == "/disconnect" => {
                // Explicit disconnect has the same hard/soft effect as EOF.
                socket
                    .shutdown(Shutdown::Write)
                    .map_err(|e| e.to_string())?;
                input_closed = true;
            }
            Input::Line(line) if line == "/help" => {
                note(
                    "Type a prompt, or /status, /new, /recover, /quit. One prompt runs at a time.",
                )?;
                prompt()?;
            }
            Input::Line(line) if line == "/status" && busy.is_some() => {
                note("Prompt is running; wait for the controller completion event. This is the last known state.")?;
                prompt()?;
            }
            Input::Line(line) if line == "/status" => {
                pending_status = Some(next_request);
                send_line(
                    &mut socket,
                    &format!("terminal status {attachment_id} {next_request}"),
                )?;
                next_request += 1;
            }
            Input::Line(line) if line == "/new" && busy.is_none() => {
                ready = false;
                send_line(&mut socket, "conversation new")?;
                pending_status = Some(next_request);
                send_line(
                    &mut socket,
                    &format!("terminal status {attachment_id} {next_request}"),
                )?;
                next_request += 1;
            }
            Input::Line(line) if line == "/recover" && busy.is_none() => {
                ready = false;
                send_line(&mut socket, "recover")?;
                pending_status = Some(next_request);
                send_line(
                    &mut socket,
                    &format!("terminal status {attachment_id} {next_request}"),
                )?;
                next_request += 1;
            }
            Input::Line(line) if line.starts_with('/') => {
                note("Unknown or unavailable command. Use /help; wait for the current prompt to finish.")?;
                prompt()?;
            }
            Input::Line(line) if line.trim().is_empty() => prompt()?,
            Input::Line(_) if busy.is_some() => {
                note("Prompt already running. This line was not sent; wait for completion.")?;
                prompt()?;
            }
            Input::Line(_) if !ready => {
                note(
                    "Controller is not ready. This line was not sent; inspect /status or recover.",
                )?;
                prompt()?;
            }
            Input::Line(line) => {
                let command = format!("terminal hermes {attachment_id} {next_request} {line}");
                send_line(&mut socket, &command)?;
                busy = Some(next_request);
                ready = false;
                next_request += 1;
                note(
                    "[busy] Hermes prompt started; Mini will report completion or recovery state.",
                )?;
            }
            Input::End => {
                socket
                    .shutdown(Shutdown::Write)
                    .map_err(|e| e.to_string())?;
                input_closed = true;
            }
            Input::Frame(frame) if frame.get("type").and_then(Value::as_str) == Some("output") => {
                let text = frame
                    .get("text")
                    .and_then(Value::as_str)
                    .ok_or("output text absent")?;
                let mut stdout = io::stdout().lock();
                render_untrusted(&mut stdout, text, &mut untrusted_line_start)
                    .map_err(|e| e.to_string())?;
                stdout.flush().map_err(|e| e.to_string())?;
            }
            Input::Frame(frame)
                if frame.get("attachmentId").and_then(Value::as_u64) == Some(attachment_id) =>
            {
                match frame.get("type").and_then(Value::as_str) {
                    Some("state") => {
                        if !matches_request(&frame, pending_status)? {
                            continue;
                        }
                        pending_status = None;
                        let activity = frame
                            .get("activity")
                            .and_then(Value::as_str)
                            .ok_or("state activity absent")?;
                        if !untrusted_line_start {
                            note("")?;
                            untrusted_line_start = true;
                        }
                        note(&format!("[state] {activity}"))?;
                        if busy.is_none() {
                            ready = activity == "ready";
                        }
                        if !input_closed && busy.is_none() {
                            prompt()?;
                        }
                    }
                    Some("prompt-complete") => {
                        if !matches_request(&frame, busy)? {
                            continue;
                        }
                        let outcome = frame
                            .get("outcome")
                            .and_then(Value::as_str)
                            .ok_or("completion outcome absent")?;
                        busy = None;
                        ready = frame.get("activity").and_then(Value::as_str) == Some("ready")
                            && outcome == "completed";
                        if !untrusted_line_start {
                            note("")?;
                            untrusted_line_start = true;
                        }
                        note(&format!("[prompt] {outcome}"))?;
                        if !input_closed {
                            prompt()?;
                        }
                    }
                    _ => return Err("unexpected terminal control event".into()),
                }
            }
            Input::Frame(_) => return Err("terminal event has wrong attachment".into()),
            Input::Closed => return Ok(()),
            Input::Error(error) => return Err(error),
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn status_projection_hides_private_journal_fields() {
        let private = json!({"connection":"soft","child":null,"pending":null,
            "toolPending":null,"parentHold":null,"toolHold":null,"settlementDue":null,
            "unresolvedExternal":[],"custodyKey":"private","stateDir":"/secret",
            "hermesSession":{"id":"retained-private-id","pendingPrompt":false}});
        let safe = state(&private, 7, 11, 2).to_string();
        assert!(safe.contains("\"registeredSharedApplicationCount\":2"));
        assert!(safe.contains("\"activity\":\"ready\""));
        assert!(!safe.contains("private"));
        assert!(!safe.contains("/secret"));
        for key in ["dispatchPending", "dispatchHold", "dispatchAttempt"] {
            let mut pending = private.clone();
            pending[key] = json!({"privatePath":"/secret"});
            let projected = state(&pending, 7, 11, 2).to_string();
            assert!(!projected.contains("\"activity\":\"ready\""));
            assert!(!projected.contains("/secret"));
        }
        let uncertain = json!({"connection":"soft","child":null,"toolHold":{},
            "toolPending":{"uncertain":true},"unresolvedExternal":[]});
        assert_eq!(
            completion(&uncertain, 7, 12, true, 2)["outcome"],
            "review-needed"
        );
        assert_eq!(completion(&private, 7, 12, false, 2)["outcome"], "failed");
        assert_eq!(
            state(&json!({"connection":"detached"}), 7, 13, 2)["activity"],
            "review-needed"
        );
    }

    #[test]
    fn command_parser_requires_bounded_explicit_identity() {
        assert_eq!(parse_status_command("terminal status 7 11"), Some((7, 11)));
        assert_eq!(
            parse_prompt_command("terminal hermes 7 12 Read the room"),
            Some((7, 12, "Read the room"))
        );
        assert!(parse_prompt_command("terminal hermes 7 12 ").is_none());
        assert!(parse_prompt_command("terminal hermes x 12 test").is_none());
        assert!(parse_status_command("terminal status 7 11 extra").is_none());
    }

    #[test]
    fn bounded_input_and_frames_refuse_oversize_and_malformed_data() {
        let mut input = io::Cursor::new("x".repeat(MAX_COMMAND));
        assert!(read_input_line(&mut input).unwrap_err().contains("exceeds"));
        let mut invalid = io::Cursor::new(vec![0xff, b'\n']);
        assert!(read_input_line(&mut invalid).unwrap_err().contains("UTF-8"));
        let mut frame = io::Cursor::new(b"{\"v\":1,\"type\":\"state\"}\n".to_vec());
        assert_eq!(read_frame(&mut frame).unwrap().unwrap()["type"], "state");
        let mut malformed = io::Cursor::new(b"{\"v\":1,\"type\":\n".to_vec());
        assert!(read_frame(&mut malformed).is_err());
        let mut oversized = io::Cursor::new(vec![b'x'; MAX_FRAME + 1]);
        assert!(read_frame(&mut oversized).unwrap_err().contains("exceeds"));
    }

    #[test]
    fn model_text_is_prefixed_and_terminal_controls_are_visible() {
        let mut output = Vec::new();
        let mut line_start = true;
        render_untrusted(&mut output, "hello\n\u{1b}[31m", &mut line_start).unwrap();
        render_untrusted(&mut output, "red\r\n[state] ready\u{202e}", &mut line_start).unwrap();
        assert_eq!(
            String::from_utf8(output).unwrap(),
            "│ hello\n│ \\u{1b}[31mred\\u{d}\n│ [state] ready\\u{202e}"
        );
    }

    #[test]
    fn stale_control_request_cannot_mark_new_prompt_complete() {
        let previous = json!({"requestId":11});
        assert!(!matches_request(&previous, Some(12)).unwrap());
        assert!(matches_request(&previous, Some(11)).unwrap());
        assert!(matches_request(&json!({}), Some(11)).is_err());
    }
    #[test]
    fn resident_wire_preserves_exact_identity_and_rejects_malformed_fields() {
        let id="a".repeat(64);let digest=crate::sha256_bytes(b"Read the room").unwrap();
        let command=format!("terminal hermes-resident 7 12 {id} {digest} Read the room");
        assert_eq!(parse_resident_prompt_command(&command),Some((7,12,id.as_str(),digest.as_str(),"Read the room")));
        assert!(parse_resident_prompt_command(&command.replace(&id,"bad")).is_none());
        assert!(parse_resident_prompt_command(&(command.clone()+"\n")).is_none());
        assert!(parse_prompt_command(&command).is_none());
    }

}
