//! Fixtures are real `inspect view-document` outputs from journey runs on this
//! tree (`tests/fixtures/render/`): K12M's fifty marks, K12T's three
//! transclusions as a covering and a non-covering reader see them, K12E's 104
//! lines with nested sections, and J12R's whole document (the golden).

use super::*;
use serde_json::json;

fn fixture(name: &str) -> Value {
    let text = match name {
        "k12m" => include_str!("../../tests/fixtures/render/k12m-fifty-marks.view-document.json"),
        "k12t-unreadable" => include_str!("../../tests/fixtures/render/k12t-unreadable.view-document.json"),
        "k12t-readable" => include_str!("../../tests/fixtures/render/k12t-snapshot-live.view-document.json"),
        "k12e" => include_str!("../../tests/fixtures/render/k12e-sections.view-document.json"),
        _ => unreachable!(),
    };
    serde_json::from_str(text).expect("fixture is JSON")
}

fn render_with(document: &Value, entries: &[Value], names: &BTreeMap<String, String>) -> Rendered {
    let sources = BTreeMap::new();
    render(&View { document, entries, names, sources: &sources, me: "7" }).expect("renders")
}

#[test]
fn fifty_marks_render_once_per_kind_and_the_heading_is_the_outline() {
    let rendered = render_with(&fixture("k12m"), &[], &BTreeMap::new());
    let notation: Vec<String> = rendered.lines.iter().map(text::line_notation).collect();
    // Line 2: one stale and one fresh bold -> bold, unstruck (k-marks' rule).
    assert_eq!(notation, ["one", "**two'**", "three", "# **_`four`_**"]);
    assert_eq!(rendered.outline, [OutlineEntry { line: 4, level: 1, text: "four".into() }]);
    assert_eq!(text::outline(&rendered), "  4  four\n");
    assert_eq!(rendered.text(), "  1  one\n  2  **two'**\n  3  three\n  4  # **_`four`_**\n");
}

#[test]
fn raw_is_the_atoms_byte_exact() {
    let rendered = render_with(&fixture("k12m"), &[], &BTreeMap::new());
    assert_eq!(rendered.raw(), b"one\ntwo'\nthree\nfour\n");
    // A payload that is not UTF-8 renders by size and stays exact in raw.
    let mut document = fixture("k12m");
    document["order"][0]["payload"] = json!("ff00fe");
    let rendered = render_with(&document, &[], &BTreeMap::new());
    assert_eq!(text::line_notation(&rendered.lines[0]), "[binary 3 B]");
    assert_eq!(&rendered.raw()[..4], &[0xff, 0x00, 0xfe, b'\n']);
}

#[test]
fn unreadable_source_is_the_placeholder_named_by_the_readers_hint() {
    let document = fixture("k12t-unreadable");
    let source = document["transclusions"][0]["opening"]["source"].as_str().unwrap().to_owned();
    let named = BTreeMap::from([(source.clone(), "wall".to_owned())]);
    let rendered = render_with(&document, &[], &named);
    assert_eq!(rendered.lines.len(), 3);
    for line in &rendered.lines {
        assert_eq!(text::line_notation(line), "[transclusion: 3 atoms of wall, not readable by you]");
        let Body::Transclusion(t) = &line.body else { panic!("an embed row") };
        assert!(t.lines.is_empty(), "no source bytes for a reader without the source");
    }
    // No hint: the id, spelled as a document, never a bare number.
    let rendered = render_with(&document, &[], &BTreeMap::new());
    assert_eq!(
        text::line_notation(&rendered.lines[0]),
        format!("[transclusion: 3 atoms of doc:{source}, not readable by you]")
    );
    assert!(rendered.raw().is_empty(), "a transclusion is not the host's bytes");
}

#[test]
fn readable_transclusions_carry_header_and_lines() {
    let document = fixture("k12t-readable");
    let source = document["transclusions"][0]["opening"]["source"].as_str().unwrap().to_owned();
    let names = BTreeMap::from([(source.clone(), "wall".to_owned())]);
    // The reader's own read of wall: atoms 1001..1005 are its lines 1..5.
    let lines: BTreeMap<String, usize> = (1..=5).map(|n| (format!("100{n}"), n)).collect();
    let sources = BTreeMap::from([(source, lines)]);
    let rendered =
        render(&View { document: &document, entries: &[], names: &names, sources: &sources, me: "7" }).unwrap();
    let text = rendered.text();
    assert!(text.contains("  1  ⟨from wall lines 2..4, snapshot@40⟩\n     │ wall line 2\n     │ wall line 3\n     │ wall line 4\n"), "{text}");
    assert!(text.contains("⟨from wall lines 2..4, live⟩\n     │ wall line 2"), "{text}");
    // Without the source read, the endpoints are not placed: `?`, not a guess.
    let rendered = render_with(&document, &[], &names);
    assert!(rendered.text().contains("⟨from wall lines ?..?, snapshot@40⟩"));
}

#[test]
fn sections_nest_and_numbering_counts_live_lines_only() {
    let mut document = fixture("k12e");
    let rendered = render_with(&document, &[], &BTreeMap::new());
    let numbered = rendered.lines.iter().filter(|line| line.line.is_some()).count();
    assert_eq!(numbered, 105, "104 atoms and one transclusion");
    let sections: Vec<usize> =
        rendered.lines.iter().filter(|line| matches!(line.body, Body::Section)).map(|line| line.depth).collect();
    assert_eq!(sections, [1, 2]);
    assert!(rendered.text().ends_with("\n  §\n    §\n"));
    // A struck atom keeps its place and takes no number; the lines after it
    // shift up by one (P-DOC-WRITE's rule).
    document["order"][0]["struck"] = json!(true);
    let struck = render_with(&document, &[], &BTreeMap::new());
    assert!(struck.text().starts_with("  -  ~~p2~~\n  1  "), "{}", &struck.text()[..40]);
    assert_eq!(struck.lines.iter().filter(|line| line.line.is_some()).count(), 104);
    // A heading inside section 502 is an outline entry at depth 3.
    let order = document["order"].as_array_mut().unwrap();
    order.push(json!({"element":"9001","parent":"502","kind":"atom","atom":"9001","payload":"6465657020686561646572",
        "revision":"1","struck":false,"marks":[{"kind":"heading","fresh":true}]}));
    let rendered = render_with(&document, &[], &BTreeMap::new());
    let last = rendered.outline.last().unwrap();
    assert_eq!((last.level, last.text.as_str()), (3, "deep header"));
    assert!(rendered.text().ends_with("    §\n    105  ### deep header\n"), "{}", rendered.text());
    assert!(text::outline(&rendered).ends_with("    105  deep header\n"));
}

#[test]
fn annotations_sit_under_their_line_with_author_and_freshness() {
    let document = fixture("k12m");
    let atom = document["order"][1]["atom"].as_str().unwrap().to_owned();
    let entries = vec![
        json!({"type":"annotation","id":"1","anchor":{"type":"atom","atom":atom,"revision":"0"},
            "body":{"type":"inline","bytes":"636974652074686973"},"author":{"subject":"7"},"fresh":true}),
        json!({"type":"annotation","id":"2","anchor":{"type":"atom","atom":atom,"revision":"0"},
            "body":{"type":"reference","document":"77"},"author":{"subject":"8"},"fresh":false}),
        json!({"type":"annotation","id":"3","anchor":{"type":"atom","atom":"424242","revision":"0"},
            "body":{"type":"inline","bytes":"6f746865722064"},"author":{"subject":"7"},"fresh":true}),
    ];
    let names = BTreeMap::from([("77".to_owned(), "notes".to_owned())]);
    let rendered = render_with(&document, &entries, &names);
    assert!(rendered.text().contains(
        "  2  **two'**\n     ↳ you (fresh): cite this\n     ↳ subject 8 (stale): → notes\n  3  three\n"
    ));
    assert!(!rendered.text().contains("other d"), "an annotation of another document's atom is not this document's");
}

#[test]
fn a_dead_link_is_a_question_mark_and_html_escapes_everything() {
    let mut document = fixture("k12m");
    document["order"][0]["payload"] = json!("3c623e2026"); // "<b> &"
    document["order"][0]["marks"] = json!([
        {"kind":"link","fresh":true,"linkLive":false,"target":{"type":"document","id":"77"}},
        {"kind":"link","fresh":true,"linkLive":true,"target":{"type":"document","id":"78"}}]);
    let names = BTreeMap::from([("78".to_owned(), "a\"b".to_owned())]);
    let rendered = render_with(&document, &[], &names);
    // BTreeMap order: Some(name) after None, so the live link wraps the dead one.
    assert_eq!(text::line_notation(&rendered.lines[0]), "[[<b> &](→ ?)](→ a\"b)");
    let html = rendered.html("p<1>");
    assert!(html.starts_with("<article class=\"doc\" data-name=\"p&lt;1&gt;\">"));
    assert!(html.contains(
        "<a class=\"link\" data-target=\"a&quot;b\"><a class=\"link dead\">&lt;b&gt; &amp;</a></a>"
    ));
    // Each line names its row: element, kind, live line number, then the atom's
    // identity and marks (what the web face's rows and the journeys key on).
    let four = html.lines().find(|line| line.contains("value=\"4\"")).unwrap();
    assert!(four.starts_with("<li class=\"line\" value=\"4\" data-element=\""), "{four}");
    assert!(four.contains("data-kind=\"atom\" data-line=\"4\" data-atom=\""), "{four}");
    assert!(four.contains("data-marks=\""), "{four}");
    assert!(four.ends_with(" data-depth=\"1\"><span class=\"heading\" role=\"heading\" aria-level=\"1\"><strong><em><code>four</code></em></strong></span></li>"), "{four}");
    assert!(!html.contains("<b>"));
}

#[test]
fn a_kind_is_struck_only_when_every_mark_of_it_is_stale() {
    let names = BTreeMap::new();
    let one_stale = json!([{"kind":"bold","fresh":false}]);
    assert_eq!(text::decorate("t", &decos(&names, &one_stale, 1)), "~~**t**~~");
    let stale_and_fresh = json!([{"kind":"bold","fresh":false},{"kind":"bold","fresh":true}]);
    assert_eq!(text::decorate("t", &decos(&names, &stale_and_fresh, 1)), "**t**");
    let stale_heading = json!([{"kind":"heading","fresh":false}]);
    assert_eq!(text::decorate("t", &decos(&names, &stale_heading, 2)), "~~##~~ t");
}

#[test]
fn sizes_read_in_the_unit_a_reader_thinks_in() {
    assert_eq!(size_text(12), "12 B");
    assert_eq!(size_text(12 * 1024 + 100), "12 KB");
    assert_eq!(size_text(3 * 1024 * 1024), "3 MB");
}

/// J12R's document as A read it in run `run-pdr/q3` (view-document, the cell's
/// entries, rsrc's own view), rendered here to the journey's golden file.
#[test]
fn j12r_renders_to_the_journey_golden() {
    let fixture: Value =
        serde_json::from_str(include_str!("../../tests/fixtures/render/j12r-rpaper.json")).unwrap();
    let names: BTreeMap<String, String> = fixture["names"]
        .as_object()
        .unwrap()
        .iter()
        .map(|(id, name)| (id.clone(), name.as_str().unwrap().to_owned()))
        .collect();
    let source = fixture["document"]["transclusions"][0]["opening"]["source"].as_str().unwrap().to_owned();
    let sources = BTreeMap::from([(source, line_numbers(&fixture["sourceDocument"]))]);
    let entries = fixture["entries"].as_array().unwrap();
    let rendered = render(&View {
        document: &fixture["document"],
        entries,
        names: &names,
        sources: &sources,
        me: fixture["me"].as_str().unwrap(),
    })
    .unwrap();
    let golden = include_str!("../../journey.d/j12r.golden.txt")
        .replace("subject <R> ", "subject 14100043549062199830 ")
        .replace("snapshot@<H>", "snapshot@30");
    assert_eq!(rendered.text(), golden);
    assert_eq!(rendered.raw(), b"Docuverse\nbold words\nslanted\nmini serve\nsee the target\nchanged\n");
    assert_eq!(text::outline(&rendered), "  1  Docuverse\n");
}

#[test]
fn shared_name_bindings_render_as_internal_targets_not_external_urls() {
    let entry=json!({"type":"link","id":"9","source":null,"relation":"0","tombstonedAt":null,
        "target":crate::workspace::shared_names::target("board","object","42").unwrap()});
    let rendered=render_with(&fixture("k12m"),&[entry],&BTreeMap::new());
    assert!(rendered.text().contains("board → object:42"));
    assert!(rendered.html("lab/index").contains("<dt>board</dt><dd>object:42</dd>"));
    assert!(!rendered.html("lab/index").contains("mini-name:"));
    assert_eq!(rendered.json("7")["sharedNames"][0]["name"],"board");
    assert_eq!(rendered.raw(), b"one\ntwo'\nthree\nfour\n");
}

// These are explicit legacy-reference carriers, not fabricated range openings.
#[test]
fn legacy_reference_renders_current_authorized_bytes_without_inventing_height() {
    let item = json!({"id":"61","mode":"snapshot",
        "legacyReference":{"document":"42","atom":"255","revision":"17","mode":"snapshot"},
        "render":{"view":"snapshot","lines":["68656c6c6f"]}});
    let names = BTreeMap::from([("42".to_owned(), "notes".to_owned())]);
    let sources = BTreeMap::from([("42".to_owned(), BTreeMap::from([("255".to_owned(), 1)]))]);
    let rendered = transcluded(&names, &sources, &item);
    assert_eq!(rendered.source, "42");
    assert_eq!(rendered.lines, ["hello"]);
    assert_eq!(rendered.header, "⟨from notes line 1, retained revision 17⟩");
    assert!(!rendered.header.contains("snapshot@"));
}

#[test]
fn unreadable_legacy_reference_stays_a_meaningful_link_without_payload() {
    let item = json!({"id":"61","mode":"live",
        "legacyReference":{"document":"42","atom":"255","revision":"17","mode":"live"},
        "render":{"view":"unavailable"}});
    let rendered = transcluded(&BTreeMap::new(), &BTreeMap::new(), &item);
    assert_eq!(rendered.source, "42");
    assert!(rendered.lines.is_empty());
    assert!(rendered.header.contains("atom 255"));
    assert!(rendered.header.contains("not readable by you"));
}

#[test]
fn legacy_mark_is_visible_metadata_not_invented_formatting() {
    let document = json!({"root":null,"rootRevision":null,"order":[],"transclusions":[]});
    let entries = vec![json!({"type":"annotation","id":"70","anchor":{"type":"range"},
        "body":{"type":"inline","bytes":"626164206672616d696e67"},
        "author":{"subject":"7"},"fresh":false,
        "legacyMark":{"id":"3","kindDigest":"88","payload":"72656d656d626572",
            "range":{"start":"1","finish":"2"},"tombstoned":false}})];
    let rendered = render_with(&document, &entries, &BTreeMap::new());
    assert_eq!(rendered.document_annotations.len(), 1);
    assert!(rendered.document_annotations[0].body.contains("retained mark 88"));
    assert!(rendered.document_annotations[0].body.contains("remember"));
    assert!(!rendered.document_annotations[0].body.contains("bad framing"));
    assert!(rendered.lines.is_empty());
}
