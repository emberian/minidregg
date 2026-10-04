"""What a native source calls, as code (W43-ORPHAN-GATES).

check-exports.sh asks "is this Lean export named by native code?". Naming it in a comment, or in a
`#[cfg(any())]` item that no build compiles, is not a call. `live_code(text)` returns the source with
comments blanked and every `#[cfg(any())]`-gated item blanked; string literals are KEPT, because the
real calls are dlsym("minidregg_...") string literals (native/resource-client/src/relay.rs).
Offsets and newlines are preserved. C and C++ headers use the same comment syntax.
"""
import re


def blank_comments(src):
    out, i, n = list(src), 0, len(src)

    def blank(a, b):
        for j in range(a, b):
            if out[j] != "\n":
                out[j] = " "
    while i < n:
        if src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif src.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            blank(i, j)
            i = j
        else:
            raw = re.compile(r'b?r(#*)"').match(src, i)
            if raw:
                end = src.find('"' + raw.group(1), raw.end())
                i = n if end < 0 else end + 1 + len(raw.group(1))
            elif src[i] == '"':
                i += 1
                while i < n and src[i] != '"':
                    i += 2 if src[i] == "\\" else 1
                i += 1
            elif src[i] == "'":
                ch = re.compile(r"'(?:[^'\\\n]|\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.))'").match(src, i)
                i = ch.end() if ch else i + 1
            else:
                i += 1
    return "".join(out)


_DEAD = re.compile(r"#\s*\[\s*cfg\s*\(\s*(?:any\s*\(\s*\)|not\s*\(\s*all\s*\(\s*\)\s*\))\s*\)\s*\]")


def blank_dead_cfg(code):
    out = list(code)
    for m in _DEAD.finditer(code):
        i, depth = m.end(), 0
        while i < len(code):
            c = code[i]
            if c in "([":
                depth += 1
            elif c in ")]":
                depth -= 1
            elif c == ";" and depth == 0:
                i += 1
                break
            elif c == "{" and depth == 0:
                d = 0
                while i < len(code):
                    d += (code[i] == "{") - (code[i] == "}")
                    i += 1
                    if d == 0:
                        break
                break
            i += 1
        for j in range(m.start(), min(i, len(code))):
            if out[j] != "\n":
                out[j] = " "
    return "".join(out)


def live_code(src):
    return blank_dead_cfg(blank_comments(src))
