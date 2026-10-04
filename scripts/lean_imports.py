"""The one reader of a Lean module header, shared by the gates that walk imports
(check-import-boundary.sh, check-host-closure.sh, check-build-closure.sh, lean-build-surfaces.py).

A gate that reads imports with `^import\\s+(\\S+)` sees only an `import` that starts a line.
Lean also accepts an indented import, several imports on one line, and the `public`, `meta`
and `private` import modifiers (and `import all`); each of those is a module the compiler
reads that such a gate cannot see (measured by W20-GATE-MUTATION, 2026-10-05). The header
is what Lean itself reads: comments and whitespace, an optional `module` or `prelude`, then
imports, up to the first token that is none of those. Text after the header (doc comments,
string literals that happen to start a line with `import`) is not an import.
"""
import re

_IMPORT = re.compile(r"(?:(?:public|meta|private)[ \t\r\n]+)*import(?:[ \t\r\n]+all)?[ \t\r\n]+([^\s]+)")
_KEYWORD = re.compile(r"(?:module|prelude)(?![\w.'!?])")


def _skip_blank(text, i):
    n = len(text)
    while i < n:
        c = text[i]
        if c in " \t\r\n":
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j + 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        else:
            break
    return i


def header_imports(text):
    """The modules a Lean source's header imports, in order."""
    out, i = [], 0
    while True:
        i = _skip_blank(text, i)
        kw = _KEYWORD.match(text, i)
        if kw:
            i = kw.end()
            continue
        m = _IMPORT.match(text, i)
        if not m:
            return out
        out.append(m.group(1))
        i = m.end()


def file_imports(path):
    with open(path, encoding="utf-8") as fh:
        return header_imports(fh.read())
