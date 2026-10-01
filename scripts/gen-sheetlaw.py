#!/usr/bin/env python3
"""Assurance/SheetLaw.lean §2 is a mechanical embed of the MUD sheet law JSON; this script is that embed.

usage (from the repository root):
  scripts/gen-sheetlaw.py           rewrite §2 (`def management` .. `end Law`) from the JSON
  scripts/gen-sheetlaw.py --check   exit 1 if §2 differs from what the JSON generates

Sources: deploy/shell/templates/mud/law.management.json (clause 0) and
deploy/shell/templates/mud/sheet/law.sheet.json (an `all` of clauses 1..N). Placeholder `{X}`
becomes `p.X`; negative literals are parenthesised; nothing is re-sorted, dropped or simplified.
Changing the JSON without re-running this script leaves the theorems about a different law."""
import json, re, sys

T = "deploy/shell/templates/mud"
F = "Assurance/SheetLaw.lean"

def val(v):
    v = str(v)
    m = re.fullmatch(r"\{([A-Z_0-9]+)\}", v)
    if m:
        return "p." + m.group(1)
    n = int(v)
    return f"({n})" if n < 0 else str(n)

def q(s):
    return '"' + s + '"'

def render(n, ind):
    t = n["type"]
    if t in ("all", "any"):
        kids = [" " * (ind + 2) + render(c, ind + 2) for c in n["predicates"]]
        return f"Pred.{t} [\n" + ",\n".join(kids) + "]"
    if t == "not":
        return f".not ({render(n['predicate'], ind + 2)})"
    if t in ("eq", "le"):
        return f".{t} {q(n['slot'])} {val(n['value'])}"
    if t == "memberOf":
        return f".memberOf {q(n['slot'])} [" + ", ".join(val(v) for v in n["values"]) + "]"
    if t == "monotone":
        return f".monotone {q(n['slot'])}"
    if t in ("eqSlots", "leSlots"):
        return f".{t} {q(n['left'])} {q(n['right'])}"
    if t == "leSlotsOff":
        return f".leSlotsOff {q(n['left'])} {q(n['right'])} {val(n['offset'])}"
    sys.exit(f"gen-sheetlaw: no Lean rendering for atom type {t!r}")

def generate():
    mg = json.load(open(f"{T}/law.management.json"))
    sh = json.load(open(f"{T}/sheet/law.sheet.json"))
    if sh["type"] != "all":
        sys.exit("gen-sheetlaw: law.sheet.json is not an `all` of clauses")
    out = ["def management (p : Params) : Pred :=", "  " + render(mg, 2), ""]
    for i, c in enumerate(sh["predicates"], 1):
        out += [f"/-- clause {i} -/", f"def sheetClause{i} (p : Params) : Pred :=", "  " + render(c, 2), ""]
    return "\n".join(out) + "\n\n", len(sh["predicates"])

gen, n = generate()
s = open(F).read()
a, b = s.index("def management (p : Params) : Pred :="), s.index("end Law")
if "--check" in sys.argv[1:]:
    if s[a:b] != gen:
        sys.exit(f"gen-sheetlaw: {F} §2 is not the embed of {T}/sheet/law.sheet.json; run scripts/gen-sheetlaw.py")
    print(f"gen-sheetlaw: {F} §2 matches the JSON ({n} clauses)")
else:
    open(F, "w").write(s[:a] + gen + s[b:])
    print(f"gen-sheetlaw: wrote {F} §2 ({n} clauses); sheetClauses must list sheetClause1..{n}")
