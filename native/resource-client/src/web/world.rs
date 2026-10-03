//! Two useful faces of a member-defined kind or instance, over current signed reads.
use super::*;

pub(super) fn page(site: &Site, name: &str, behavior: bool) -> Page {
    let reference = match site.reference(name) {
        Ok(reference) => reference,
        Err(page) => return page,
    };
    match site.read(&reference, "resource") {
        Ok((view, challenge, _)) => match body(site, name, &view, behavior) {
            Some(mut body) => {
                if behavior {
                    body.push_str("<h2>Current law</h2>");
                    match site.read(&reference,"policy") {
                        Ok((law,head,_)) => body.push_str(&format!("<p>Law read at height {}.</p><details><summary>Disclosed law</summary><pre>{}</pre></details>",escape(head["height"].as_str().unwrap_or("?")),escape(&serde_json::to_string_pretty(&law).unwrap_or_default()))),
                        Err(error) => body.push_str(&format!("<p class=refusal>Law unavailable: {}</p>",escape(&refusal_text(&error).unwrap_or(error)))),
                    }
                }
                Page {
                    status: 200,
                    title: format!(
                        "{} · {}",
                        name,
                        if behavior { "behavior" } else { "fields" }
                    ),
                    stamp: Stamp::Read(ReadContext::of(&challenge, &view)),
                    body,
                }
            }
            None => simple(
                400,
                "No object view",
                "This resource has no member-defined kind or instance projection.",
            ),
        },
        Err(error) => failure_page(name, &error),
    }
}

pub(super) fn body(site: &Site, name: &str, view: &Value, behavior: bool) -> Option<String> {
    render(&site.base(), name, view, behavior)
}

fn render(base: &str, name: &str, view: &Value, behavior: bool) -> Option<String> {
    let cell = &view["cell"];
    let (object, is_kind) = if cell["worldInstance"].is_object() {
        (&cell["worldInstance"], false)
    } else if cell["worldKind"].is_object() {
        (&cell["worldKind"], true)
    } else {
        return None;
    };
    let n = escape(name);
    let descriptor = &object["descriptor"];
    let mut html = format!("<nav data-object-views><a href=\"{base}/object/{n}\">Fields</a> · \
        <a href=\"{base}/object/{n}/behavior\">Behavior and meaning</a></nav><p>{} · kind <code>{}</code> · revision <code>{}</code></p>",
        if is_kind {"Kind definition"} else {"Instance"},escape(descriptor["kind"].as_str().unwrap_or("?")),
        escape(descriptor["revision"].as_str().unwrap_or("?")));
    if let Some(root) = object["kindRoot"].as_str() {
        html.push_str(&format!(
            "<p data-pinned-kind>Instance meaning pinned to kind root <code>{}</code>.</p>",
            escape(root)
        ));
    }
    if !behavior {
        html.push_str(&fields(object));
    } else {
        html.push_str("<section data-object-behavior><h2>Methods</h2>");
        match object["methods"].as_array() {
            Some(methods) => {
                if methods.is_empty() {
                    html.push_str("<p>This definition has no named methods.</p>");
                }
                for method in methods {
                    html.push_str(&format!("<article><h3>{}</h3><p>Program <code>{}</code></p><table><tr><th>Output</th><th>Field</th><th>Key</th></tr>",
                        escape(method["name"].as_str().unwrap_or("?")),escape(method["program"].as_str().unwrap_or("?"))));
                    if let Some(outputs) = method["outputs"].as_array() {
                        for output in outputs {
                            html.push_str(&format!(
                                "<tr><td>{}</td><td>{}</td><td>{}</td></tr>",
                                escape(output["output"].as_str().unwrap_or("?")),
                                escape(output["field"].as_str().unwrap_or("?")),
                                escape(output["key"].as_str().unwrap_or("?"))
                            ));
                        }
                    }
                    html.push_str("</table></article>");
                }
            }
            None => html.push_str("<p>No method table was disclosed by this read.</p>"),
        }
        html.push_str("</section><h2>Field meanings</h2><table><tr><th>Name</th><th>Meaning</th><th>Codec</th><th>Updates</th></tr>");
        if let Some(fields) = descriptor["fields"].as_array() {
            for field in fields {
                html.push_str(&format!(
                    "<tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>",
                    escape(field["name"].as_str().unwrap_or("?")),
                    escape(field["meaning"].as_str().unwrap_or("?")),
                    escape(field["codec"].as_str().unwrap_or("?")),
                    escape(field["discipline"].as_str().unwrap_or("?"))
                ));
            }
        }
        html.push_str("</table>");
        for (key, label) in [
            ("sampleSlots", "Source sample slots"),
            ("definitionBytes", "Canonical definition"),
            ("construction", "Construction and parents"),
            ("trace", "Definition trace"),
        ] {
            if let Some(value) = object.get(key) {
                html.push_str(&format!(
                    "<details data-object-{key}><summary>{label}</summary><pre>{}</pre></details>",
                    escape(&serde_json::to_string_pretty(value).unwrap_or_default())
                ));
            }
        }
        html.push_str(&format!(
            "<details><summary>Full disclosed object record</summary><pre>{}</pre></details>",
            escape(&serde_json::to_string_pretty(object).unwrap_or_default())
        ));
    }
    Some(html)
}

fn fields(object: &Value) -> String {
    let mut html =
        String::from("<table data-object-fields><tr><th>Field</th><th>Key</th><th>Value</th></tr>");
    let entries = object["entries"]
        .as_array()
        .or_else(|| object["defaults"].as_array());
    if let Some(entries) = entries {
        for entry in entries {
            let id = entry["field"].as_str().unwrap_or("?");
            let field = object["descriptor"]["fields"]
                .as_array()
                .and_then(|fields| fields.iter().find(|f| f["id"].as_str() == Some(id)));
            let label = field.and_then(|f| f["name"].as_str()).unwrap_or(id);
            let value = entry["value"].as_str().unwrap_or("?");
            let shown = if field.is_some_and(|f| f["codec"] == "bytes") {
                crate::decode_hex(value)
                    .ok()
                    .and_then(|bytes| String::from_utf8(bytes).ok())
                    .filter(|text| {
                        !text
                            .chars()
                            .any(|c| c.is_control() && !matches!(c, '\n' | '\t'))
                    })
                    .unwrap_or_else(|| format!("hex: {value}"))
            } else {
                value.to_owned()
            };
            html.push_str(&format!("<tr><td>{} <small><code>{}</code></small></td><td>{}</td><td><pre>{}</pre></td></tr>",
                escape(label),escape(id),escape(entry["key"].as_str().unwrap_or("?")),escape(&shown)));
        }
    }
    html.push_str("</table>");
    html
}

#[cfg(test)]
mod tests {
    use super::*;
    fn object() -> Value {
        serde_json::json!({"cell":{"worldInstance":{"kindRoot":"901","descriptor":{"kind":"7","revision":"2",
        "fields":[{"id":"4","name":"Votes <yes>","meaning":"number of approvals","codec":"nat","discipline":"ram"}]},
        "entries":[{"field":"4","key":"0","value":"12"}],"methods":[{"name":"vote","program":"42","outputs":[{"output":"0","field":"4","key":"0"}]}],
        "sampleSlots":[["world/before/Votes","12"]]}}})
    }
    #[test]
    fn two_views_share_one_pinned_instance_and_escape_member_data() {
        let fields = render("/secret", "poll", &object(), false).unwrap();
        let behavior = render("/secret", "poll", &object(), true).unwrap();
        assert!(fields.contains("Votes &lt;yes&gt;"));
        assert!(fields.contains("12"));
        assert!(behavior.contains("number of approvals"));
        assert!(behavior.contains("vote"));
        assert!(behavior.contains("world/before/Votes"));
        for view in [fields, behavior] {
            assert!(view.contains("901"));
            assert!(view.contains("/object/poll/behavior"));
        }
        assert!(render(
            "/secret",
            "other",
            &serde_json::json!({"cell":{"entries":[]}}),
            false
        )
        .is_none());
    }
}
