//! Bounded member search. No index, cached matches, or transclusion fanout.
//! Each result is derived from this request's signed current resource read.
use super::*;
use crate::render::{Body, Rendered};
use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

pub(crate) const PAGE_SIZE: usize = 4;
const MAX_COLLECTION: usize = 4096;
const MAX_HITS: usize = 100;

/// Scope is an explicit comma-separated held-reference collection or @held.
/// Enumeration reveals only the caller's existing local names, never a server inventory.
fn collection(root: &Path, scope: &str) -> Result<Vec<String>> {
    let mut names = BTreeSet::new();
    if scope == "@held" {
        for entry in fs::read_dir(root.join("refs")).map_err(|e| e.to_string())? {
            let entry = entry.map_err(|e| e.to_string())?;
            if let Some(name) = entry
                .file_name()
                .to_str()
                .and_then(|s| s.strip_suffix(".json"))
            {
                names.insert(ref_name_of_file(name));
            }
            if names.len() > MAX_COLLECTION {
                return Err(
                    "held collection exceeds 4096 references; select explicit names".into(),
                );
            }
        }
    } else {
        for name in scope.split(',') {
            // Same name parser as workspace references; no ambient room expansion.
            validate_ref_name(name)?;
            names.insert(name.to_owned());
            if names.len() > MAX_COLLECTION {
                return Err("collection exceeds 4096 references".into());
            }
        }
    }
    Ok(names.into_iter().collect())
}

/// Direct document projection shares the ordinary renderer and authenticated
/// opened_entries boundary. Empty sources deliberately leave transclusions unresolved.
fn direct(
    root: &Path,
    workspace: &Value,
    reference: &Value,
) -> Result<(Value, Value, Rendered, usize)> {
    let (view, challenge, signed) = signed_view(root, workspace, reference, "resource")?;
    let bin = fs::read(signed.with_file_name("view.bin")).map_err(|e| e.to_string())?;
    let (attempt, _) = new_attempt(root)?;
    make_private_dir(&attempt)?;
    let input = attempt.join("search-document-in.json");
    private_file(
        &input,
        &serde_json::to_vec(&json!({"host":hex(&bin),"sources":[]})).map_err(|e| e.to_string())?,
    )?;
    let document = inspect(
        &workspace_host(workspace)?,
        &member_path(workspace, "config")?,
        "view-document",
        &input,
        &attempt.join("search-document.json"),
    )?;
    let display = opened_entries(root, workspace, reference, &view)?;
    let rendered = crate::render::render(&crate::render::View {
        document: &document,
        entries: &display,
        names: &BTreeMap::new(),
        sources: &BTreeMap::new(),
        me: member(workspace, "subject")?,
    })?;
    let locked = locked_text_rows(&display, &rendered);
    Ok((view, challenge, rendered, locked))
}

/// Count only currently placed private atoms whose authenticated local opening
/// is unavailable. Detached history and ordinary binary objects are not locked text.
fn locked_text_rows(entries: &[Value], rendered: &Rendered) -> usize {
    let locked: BTreeSet<&str> = entries
        .iter()
        .filter(|entry| {
            entry["type"] == "atom"
                && private::is_private_kind(&entry["kind"])
                && private::opened_text(entry).ok().flatten().is_none()
        })
        .filter_map(|entry| entry["id"].as_str())
        .collect();
    rendered
        .lines
        .iter()
        .filter(|line| {
            line.line.is_some()
                && line.row["atom"]
                    .as_str()
                    .is_some_and(|atom| locked.contains(atom))
        })
        .count()
}

fn query_text(query: &str) -> Result<String> {
    if query.trim().is_empty() || query.len() > 256 || query.chars().any(char::is_control) {
        return Err(
            "search query must contain 1–256 bytes of text without control characters".into(),
        );
    }
    Ok(query.to_lowercase())
}

fn snippet(text: &str, query: &str) -> String {
    // Character boundaries survive Unicode lowercase expansion. Context around
    // the first matching original character, with a strict display bound.
    let chars: Vec<char> = text.chars().collect();
    let mut folded = String::new();
    let mut origins = Vec::new();
    for (i, c) in chars.iter().enumerate() {
        for lower in c.to_lowercase() {
            folded.push(lower);
            origins.extend(std::iter::repeat_n(i, lower.len_utf8()));
        }
    }
    let at = folded
        .find(query)
        .and_then(|offset| origins.get(offset))
        .copied()
        .unwrap_or(0);
    let begin = at.saturating_sub(48);
    let end = (begin + 200).min(chars.len());
    format!(
        "{}{}{}",
        if begin > 0 { "…" } else { "" },
        chars[begin..end].iter().collect::<String>(),
        if end < chars.len() { "…" } else { "" }
    )
}

fn matches(
    rendered: &Rendered,
    needle: &str,
    name: &str,
    target: &str,
    challenge: &Value,
) -> (Vec<Value>, usize, usize) {
    let mut hits = Vec::new();
    let mut matching = 0;
    let mut omitted = 0;
    for line in &rendered.lines {
        let Body::Text {
            bytes,
            struck: false,
        } = &line.body
        else {
            if matches!(
                line.body,
                Body::Object { struck: false, .. } | Body::Transclusion(_)
            ) {
                omitted += 1;
            }
            continue;
        };
        let Ok(text) = std::str::from_utf8(bytes) else {
            omitted += 1;
            continue;
        };
        if !text.to_lowercase().contains(needle) {
            continue;
        }
        matching += 1;
        if hits.len() < MAX_HITS {
            hits.push(json!({"name":name,"target":target,"atom":line.row["atom"],
                "revision":line.row["revision"],"element":line.row["element"],"line":line.line,
                "rootRevision":rendered.root_revision,"worldRoot":challenge["worldRoot"],
                "height":challenge["height"],"snippet":snippet(text,needle)}));
        }
    }
    (hits, matching, omitted)
}

pub(crate) fn search(
    root: &Path,
    workspace: &Value,
    query: &str,
    scope: &str,
    offset: usize,
    expected: Option<&str>,
) -> Result<Value> {
    let needle = query_text(query)?;
    let started = Instant::now();
    let names = collection(root, scope)?;
    let mut digest = Sha256::new();
    for name in &names {
        let reference = bounded_json(&root.join("refs").join(format!("{}.json", ref_file(name))));
        let bytes = serde_json::to_vec(&json!([name, reference.unwrap_or(Value::Null)]))
            .map_err(|e| e.to_string())?;
        digest.update((bytes.len() as u64).to_be_bytes());
        digest.update(bytes);
    }
    let fingerprint = hex(&digest.finalize());
    if offset > names.len() || (offset > 0 && expected != Some(fingerprint.as_str())) {
        return Err(
            "search collection changed or cursor is missing; restart from the first page".into(),
        );
    }
    let mut documents = Vec::new();
    let mut hits = Vec::new();
    let mut failures = 0;
    let mut truncated = false;
    let mut locked_total = 0;
    let end = (offset + PAGE_SIZE).min(names.len());
    for name in &names[offset..end] {
        let mut read = || -> Result<Value> {
            let reference = reference(root, name)?;
            let target = member(&reference, "target")?;
            let (_, challenge, rendered, locked) = direct(root, workspace, &reference)?;
            locked_total += locked;
            let (found, matching, omitted) = matches(&rendered, &needle, name, target, &challenge);
            let returned = found.len();
            truncated |= returned < matching;
            hits.extend(found);
            Ok(
                json!({"name":name,"target":target,"status":"read","matchingLines":matching,
                "returned":returned,"omittedNonTextOrTranscluded":omitted,"lockedTextRows":locked,
                "rootRevision":rendered.root_revision,"worldRoot":challenge["worldRoot"],"height":challenge["height"]}),
            )
        };
        match read() {
            Ok(value) => documents.push(value),
            Err(error) => {
                failures += 1;
                documents.push(json!({"name":name,"status":"unavailable","error":error}));
            }
        }
    }
    Ok(
        json!({"type":"mini-doc-search-v1","query":query,"scope":scope,
        "coverage":"current authorized direct live UTF-8 text; no annotations, objects, history or transcluded text",
        "consistency":"each document independently read at its reported current signed head",
        "collectionFingerprint":fingerprint,"heldReferences":names.len(),"offset":offset,"through":end,
        "nextOffset":if end < names.len() {Some(end)} else {None},
        "pageComplete":failures==0 && !truncated && locked_total==0,"lockedTextRows":locked_total,"hitsTruncated":truncated,"documents":documents,"hits":hits,
        "elapsedMs":started.elapsed().as_millis()}),
    )
}

pub(crate) fn follow(
    root: &Path,
    workspace: &Value,
    name: &str,
    target: &str,
    atom: &str,
    revision: &str,
) -> Result<Value> {
    decimal(target, "document")?;
    decimal(atom, "atom")?;
    field_decimal(revision, "revision")?;
    let reference = reference(root, name)?;
    if member(&reference, "target")? != target {
        return Err("reference now names a different document; search again".into());
    }
    let (_, challenge, rendered, _) = direct(root, workspace, &reference)?;
    let line = rendered
        .lines
        .iter()
        .find(|line| line.row["atom"] == atom)
        .ok_or("atom is no longer visible in this document")?;
    let Body::Text {
        bytes,
        struck: false,
    } = &line.body
    else {
        return Err("atom is no longer visible live text".into());
    };
    let text = std::str::from_utf8(bytes).map_err(|_| "atom is not UTF-8 text")?;
    Ok(
        json!({"type":"mini-doc-search-follow-v1","name":name,"target":target,"atom":atom,
        "searchedRevision":revision,"revision":line.row["revision"],"changed":line.row["revision"] != revision,
        "line":line.line,"text":text,"height":challenge["height"],"worldRoot":challenge["worldRoot"]}),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::render::RenderedLine;
    fn line(body: Body) -> RenderedLine {
        RenderedLine {
            row: json!({"atom":"9","revision":"3","element":"8"}),
            line: Some(1),
            depth: 0,
            body,
            decos: vec![],
            annotations: vec![],
        }
    }
    #[test]
    fn only_live_opened_text_is_searchable() {
        let rendered = Rendered {
            shared_names: vec![],
            root: json!("1"),
            root_revision: json!("2"),
            lines: vec![
                line(Body::Text {
                    bytes: b"hello EMBER".to_vec(),
                    struck: false,
                }),
                line(Body::Text {
                    bytes: b"secret ember".to_vec(),
                    struck: true,
                }),
                line(Body::Object {
                    label: "locked ember".into(),
                    bytes: b"cipher ember".to_vec(),
                    struck: false,
                }),
            ],
            document_annotations: vec![],
            outline: vec![],
            backlinks: vec![],
        };
        let (hits, count, omitted) =
            matches(&rendered, "ember", "paper", "7", &json!({"height":"11"}));
        assert_eq!(count, 1);
        assert_eq!(hits.len(), 1);
        assert_eq!(omitted, 1);
        assert_eq!(hits[0]["atom"], "9");
        assert_eq!(hits[0]["snippet"], "hello EMBER");
    }
    #[test]
    fn locked_coverage_excludes_detached_history_and_opened_private_text() {
        let mut rendered = Rendered {
            root: json!("1"),
            root_revision: json!("2"),
            lines: vec![line(Body::Object {
                label: "locked".into(),
                bytes: vec![],
                struck: false,
            })],
            document_annotations: vec![],
            outline: vec![],
            backlinks: vec![],
        };
        let kind = json!({"type":"inlineObject","schema":protected_document::schema()});
        let mut entries = vec![
            json!({"type":"atom","id":"9","kind":kind,"private":"locked"}),
            json!({"type":"atom","id":"10","kind":kind,"private":"locked"}),
        ];
        assert_eq!(locked_text_rows(&entries, &rendered), 1);
        entries[0]["private"] = json!({"text":"opened locally"});
        assert_eq!(locked_text_rows(&entries, &rendered), 0);
        entries[0]["private"] = json!("locked");
        rendered.lines[0].line = None;
        assert_eq!(locked_text_rows(&entries, &rendered), 0);
    }

    #[test]
    fn unicode_context_is_bounded_and_query_is_nonempty() {
        assert!(query_text(" ").is_err());
        assert!(query_text("a\nb").is_err());
        let text = format!("{}İstanbul{}", "🍄".repeat(300), "x".repeat(300));
        let result = snippet(&text, "i̇stanbul");
        assert!(result.contains("İstanbul"));
        assert!(result.chars().count() <= 202);
    }
}
