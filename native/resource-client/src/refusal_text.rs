//! The Host's refusal text as the client shows it: the tail of the outcome
//! body on one line. The words are the Host's; nothing is renamed here.
pub(crate) fn render(body: &[u8]) -> String {
    String::from_utf8_lossy(&body[body.len().saturating_sub(600)..])
        .split_whitespace().collect::<Vec<_>>().join(" ")
}
