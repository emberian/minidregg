#!/usr/bin/env python3
"""Generate website/status.html from the "Honest state" section of README.md.

    python3 website/gen-status.py           write website/status.html
    python3 website/gen-status.py --check   exit 1 if status.html is not what the README
                                            generates, or if a <pre data-source=PATH> block
                                            on any page is not text of PATH

The page's header and footer are copied from website/index.html, so the status page
cannot drift from the hand-written pages' navigation. Relative README links become
links into the repository on GitHub. The README is the only source: edit it, then
regenerate. A missing section or a malformed table refuses; nothing is guessed.

--check also runs two controls, so that a check that cannot go red does not read green:
a README with one table cell changed must render differently, and a source block with
one character changed must be refused.
"""
import difflib
import html
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SITE = ROOT / "website"
README = ROOT / "README.md"
OUT = SITE / "status.html"
BLOB = "https://github.com/emberian/minidregg/blob/main/"
TREE = "https://github.com/emberian/minidregg/tree/main/"
HEADINGS = ["Component", "Evidence", "Boundary"]


class Refuse(Exception):
    pass


def section(readme: str) -> list[str]:
    lines = readme.splitlines()
    try:
        start = lines.index("## Honest state")
    except ValueError:
        raise Refuse('README.md has no "## Honest state" heading')
    body = []
    for line in lines[start + 1:]:
        if line.startswith("## "):
            break
        body.append(line)
    return body


def href(target: str) -> str:
    if re.match(r"^[a-z]+:", target) or target.startswith("#"):
        return target
    path, _, frag = target.partition("#")
    base = TREE if path.endswith("/") else BLOB
    return base + path + ("#" + frag if frag else "")


def inline(text: str) -> str:
    """The inline Markdown the README uses: code spans, links, **strong**, *em*."""
    out, pos = [], 0
    for m in re.finditer(r"`([^`]+)`", text):
        out.append(prose(text[pos:m.start()]))
        out.append("<code>" + html.escape(m.group(1), quote=False) + "</code>")
        pos = m.end()
    out.append(prose(text[pos:]))
    return "".join(out)


def prose(text: str) -> str:
    text = html.escape(text, quote=False)
    text = re.sub(r"\[([^\]]+)\]\(([^)\s]+)\)",
                  lambda m: f'<a href="{html.escape(href(m.group(2)))}">{m.group(1)}</a>', text)
    text = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", text)
    text = re.sub(r"(?<![\w*])\*([^*]+)\*(?![\w*])", r"<em>\1</em>", text)
    return text


def cells(row: str) -> list[str]:
    row = row.strip()
    if not (row.startswith("|") and row.endswith("|")):
        raise Refuse(f"table row does not start and end with '|': {row[:60]}")
    if "\\|" in row:
        raise Refuse("escaped '|' in a table cell is not supported; rephrase the cell")
    return [c.strip() for c in row[1:-1].split("|")]


def render_body(readme: str) -> str:
    body = section(readme)
    blocks, para, table = [], [], []
    before, after = [], []
    for line in body + [""]:
        if line.startswith("|"):
            if para:
                (after if table else before).append(" ".join(para))
                para = []
            table.append(line)
        elif line.strip() == "":
            if para:
                (after if table else before).append(" ".join(para))
                para = []
        else:
            para.append(line.strip())
    if len(table) < 3:
        raise Refuse("the Honest state section has no table with at least one row")
    head = cells(table[0])
    if head != HEADINGS:
        raise Refuse(f"table headings are {head}, expected {HEADINGS}")
    if not all(re.fullmatch(r":?-{3,}:?", c) for c in cells(table[1])):
        raise Refuse("the second table line is not a separator row")
    rows = [cells(r) for r in table[2:]]
    for r in rows:
        if len(r) != len(HEADINGS):
            raise Refuse(f"row has {len(r)} cells, expected {len(HEADINGS)}: {r[0][:40]}")
    for p in before:
        blocks.append(f"<p>{inline(p)}</p>")
    blocks.append('<table class="stack status">')
    blocks.append("<thead><tr>" + "".join(f"<th>{h}</th>" for h in HEADINGS) + "</tr></thead>")
    blocks.append("<tbody>")
    for r in rows:
        tds = "".join(f'<td data-label="{h}">{inline(c)}</td>' for h, c in zip(HEADINGS, r))
        blocks.append(f"<tr>{tds}</tr>")
    blocks.append("</tbody>")
    blocks.append("</table>")
    for p in after:
        blocks.append(f"<p>{inline(p)}</p>")
    return "\n".join(blocks)


def render(readme: str, index: str) -> str:
    try:
        header = index[:index.index('<main id="main">')]
        footer = index[index.index("</main>"):]
    except ValueError:
        raise Refuse('website/index.html has no <main id="main"> ... </main>')
    header = header.replace(" aria-current=\"page\"", "")
    if '<a href="status.html">' not in header:
        raise Refuse("index.html navigation has no link to status.html")
    header = header.replace('<a href="status.html">', '<a href="status.html" aria-current="page">')
    header = re.sub(r"<title>[^<]*</title>", "<title>Status · Mini</title>", header)
    header = re.sub(r'<meta name="description" content="[^"]*">',
                    '<meta name="description" content="The state of each Mini component, by evidence class, '
                    'generated from the Honest state table of the repository README.">', header)
    intro = (
        "<h1>Status</h1>\n"
        "<p class=\"lede\">What each part of Mini has actually done, graded by the strongest "
        "evidence there is for it.</p>\n"
        "<p class=\"small muted\">This page is generated from the Honest state table of the "
        f"repository <a href=\"{BLOB}README.md#honest-state\">README</a> by "
        "<code>website/gen-status.py</code>, and a gate fails when it is stale. "
        "Edit the README, not this page.</p>\n"
    )
    main = '<main id="main">\n<div class="wrap wide">\n' + intro + render_body(readme) + "\n\n</div>\n"
    return header + main + footer


def source_errors(name: str, text: str) -> list[str]:
    """Each <pre data-source="PATH"><code>TEXT</code></pre> must be text of PATH."""
    errors = []
    for m in re.finditer(r'<pre data-source="([^"]+)"><code>(.*?)</code></pre>', text, re.S):
        path, shown = m.group(1), html.unescape(m.group(2))
        src = ROOT / path
        if not src.is_file():
            errors.append(f"{name}: data-source {path} does not exist")
        elif not shown.strip() or shown not in src.read_text():
            errors.append(f"{name}: a block marked data-source={path} is not text of that file")
    return errors


def check() -> int:
    readme, index = README.read_text(), (SITE / "index.html").read_text()
    want = render(readme, index)
    have = OUT.read_text() if OUT.exists() else ""
    red = 0
    if want != have:
        sys.stdout.writelines(difflib.unified_diff(
            have.splitlines(True), want.splitlines(True), "status.html (on disk)", "status.html (from README.md)", n=1))
        print("website: status.html is stale against README.md; run python3 website/gen-status.py")
        red += 1
    # Control 1: a changed table cell must change the page.
    lines = readme.splitlines()
    first_row = lines.index("## Honest state") + next(
        i for i, l in enumerate(section(readme)) if l.startswith("|")) + 3
    lines[first_row] = lines[first_row].replace(" |", " CONTROL-MUTATION |", 1)
    if "CONTROL-MUTATION" not in render("\n".join(lines), index):
        print("website: CONTROL FAILED: a mutated README row did not change the generated page")
        red += 1
    errors = [e for page in sorted(SITE.glob("*.html")) for e in source_errors(page.name, page.read_text())]
    for e in errors:
        print("website: " + e)
    red += bool(errors)
    # Control 2: a source block with one character changed must be refused.
    page = SITE / "language.html"
    text = page.read_text() if page.exists() else ""
    if 'data-source="' not in text:
        print("website: CONTROL FAILED: language.html has no data-source block to mutate")
        red += 1
    else:
        i = text.index("<code>", text.index('data-source="')) + len("<code>")
        mutated = text[:i] + ("Q" if text[i] != "Q" else "R") + text[i + 1:]
        if not source_errors("control", mutated):
            print("website: CONTROL FAILED: a mutated source block still matched its file")
            red += 1
    if red == 0:
        rows = sum(1 for l in section(readme) if l.startswith("|")) - 2
        blocks = sum(text.count('<pre data-source="') for text in (p.read_text() for p in SITE.glob("*.html")))
        print(f"website: PASS: status.html matches README.md ({rows} rows); {blocks} source blocks match; both controls refused")
    return 1 if red else 0


def main() -> int:
    try:
        if sys.argv[1:] == ["--check"]:
            return check()
        if sys.argv[1:]:
            print(__doc__.strip().splitlines()[2], file=sys.stderr)
            return 2
        OUT.write_text(render(README.read_text(), (SITE / "index.html").read_text()))
        print(f"wrote {OUT.relative_to(ROOT)}")
        return 0
    except Refuse as e:
        print(f"website: refused: {e}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
