//! The HTML backend: the same structure as the text backend, as semantic HTML
//! with classes and no CSS (the web face styles it).  Every text and name is
//! escaped; a link carries the reader's name for its target in `data-target`
//! and no URL, since routes are the web face's.

use super::{Annotation, Body, Deco, Rendered};

pub fn escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            _ => out.push(c),
        }
    }
    out
}

fn decorate(body: &str, decos: &[Deco]) -> String {
    let strike = |stale: bool, inner: String| {
        if stale {
            format!("<s class=\"stale\">{inner}</s>")
        } else {
            inner
        }
    };
    let mut html = escape(body);
    for deco in decos {
        html = match deco {
            Deco::Code { stale } => strike(*stale, format!("<code>{html}</code>")),
            Deco::Italic { stale } => strike(*stale, format!("<em>{html}</em>")),
            Deco::Bold { stale } => strike(*stale, format!("<strong>{html}</strong>")),
            Deco::Link { target: Some(target), stale } => strike(
                *stale,
                format!("<a class=\"link\" data-target=\"{}\">{html}</a>", escape(target)),
            ),
            Deco::Link { target: None, stale } => {
                strike(*stale, format!("<a class=\"link dead\">{html}</a>"))
            }
            Deco::Heading { level, stale } => format!(
                "<span class=\"heading{}\" role=\"heading\" aria-level=\"{level}\">{html}</span>",
                if *stale { " stale" } else { "" }
            ),
        };
    }
    html
}

fn annotation(a: &Annotation) -> String {
    format!(
        "<aside class=\"annotation {}\"><span class=\"author\">{}</span> <span class=\"body\">{}</span></aside>",
        if a.fresh { "fresh" } else { "stale" },
        escape(&a.author),
        escape(&a.body)
    )
}

pub fn document(rendered: &Rendered, title: &str) -> String {
    let mut out = vec![format!("<article class=\"doc\" data-name=\"{}\">", escape(title))];
    for a in &rendered.document_annotations {
        out.push(annotation(a));
    }
    if !rendered.outline.is_empty() {
        out.push("<nav class=\"outline\"><ol>".to_owned());
        for entry in &rendered.outline {
            out.push(format!(
                "<li data-line=\"{}\" data-level=\"{}\">{}</li>",
                entry.line,
                entry.level,
                escape(&entry.text)
            ));
        }
        out.push("</ol></nav>".to_owned());
    }
    out.push("<ol class=\"lines\">".to_owned());
    for line in &rendered.lines {
        let mut classes = vec!["line"];
        let number = line.line.map_or(String::new(), |n| format!(" value=\"{n}\" data-line=\"{n}\""));
        let content = match &line.body {
            Body::Text { struck, .. } | Body::Object { struck, .. } => {
                if matches!(line.body, Body::Object { .. }) {
                    classes.push("object");
                }
                let inner = decorate(&line.plain(), &line.decos);
                if *struck {
                    classes.push("struck");
                    format!("<del>{inner}</del>")
                } else {
                    inner
                }
            }
            Body::Section => {
                classes.push("section");
                decorate("", &line.decos)
            }
            Body::Transclusion(t) => {
                classes.push("transclusion");
                let mut block = format!(
                    "<blockquote class=\"transclusion {}\" data-source=\"{}\"><header>{}</header>",
                    escape(&t.view),
                    escape(&t.source_name),
                    decorate(&t.header, &line.decos)
                );
                for quoted in &t.lines {
                    block.push_str(&format!("<p class=\"quoted\">{}</p>", escape(quoted)));
                }
                block.push_str("</blockquote>");
                block
            }
        };
        let annotations: String = line.annotations.iter().map(|a| annotation(a)).collect();
        out.push(format!(
            "<li class=\"{}\"{number} data-depth=\"{}\">{content}{annotations}</li>",
            classes.join(" "),
            line.depth
        ));
    }
    out.push("</ol>".to_owned());
    if !rendered.backlinks.is_empty() {
        out.push("<section class=\"backlinks\"><ul>".to_owned());
        for b in &rendered.backlinks {
            out.push(format!(
                "<li><span class=\"source\">{}</span>{}</li>",
                escape(&b.source),
                b.rendered
                    .as_ref()
                    .map(|r| format!(" <span class=\"context\">{}</span>", escape(r)))
                    .unwrap_or_default()
            ));
        }
        out.push("</ul></section>".to_owned());
    }
    out.push("</article>".to_owned());
    let mut html = out.join("\n");
    html.push('\n');
    html
}
