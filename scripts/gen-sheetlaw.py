#!/usr/bin/env python3
"""§2 of Assurance/SheetLaw.lean, of Assurance/ItemLaw.lean and of Assurance/CitedLand.lean is a mechanical
embed of law JSON; this script is that embed.

usage (from the repository root):
  scripts/gen-sheetlaw.py           rewrite each §2 (its first generated line .. `end Law`) from the JSON
  scripts/gen-sheetlaw.py --check   exit 1 if a §2 differs from what the JSON generates

Sources (`EMBEDS`): for SheetLaw, native/resource-client/templates/mud/law.management.json (clause 0) and
native/resource-client/templates/mud/sheet/law.sheet.json (an `all` of clauses 1..N); for ItemLaw, the same
clause 0 and native/resource-client/templates/mud/item/law.item.json (clauses 1..N); for CitedLand,
native/resource-client/templates/fleet/verdict/law.verdict.json (clauses 0..) and
native/resource-client/templates/fleet/branch/law.branch.json (clauses 1..). Placeholder `{X}`
becomes `p.X`; negative literals are parenthesised; nothing is re-sorted, dropped or simplified.
Changing the JSON without re-running this script leaves the theorems about a different law."""
import json, re, sys

T = "native/resource-client/templates/mud"
FLEET = "native/resource-client/templates/fleet"

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
    if t in ("monotone", "writeOnce"):
        return f".{t} {q(n['slot'])}"
    if t in ("eqSlots", "leSlots"):
        return f".{t} {q(n['left'])} {q(n['right'])}"
    if t == "leSlotsOff":
        return f".leSlotsOff {q(n['left'])} {q(n['right'])} {val(n['offset'])}"
    sys.exit(f"gen-sheetlaw: no Lean rendering for atom type {t!r}")

# file -> (first generated line, [(json, def prefix, first clause number or None for one unnumbered def)])
EMBEDS = {
    "Assurance/SheetLaw.lean": ("def management (p : Params) : Pred :=", [
        (f"{T}/law.management.json", "management", None),
        (f"{T}/sheet/law.sheet.json", "sheetClause", 1)]),
    "Assurance/ItemLaw.lean": ("def management (p : Params) : Pred :=", [
        (f"{T}/law.management.json", "management", None),
        (f"{T}/item/law.item.json", "itemClause", 1)]),
    "Assurance/CitedLand.lean": ("/-- clause 0 -/\ndef verdictClause0 (p : Params) : Pred :=", [
        (f"{FLEET}/verdict/law.verdict.json", "verdictClause", 0),
        (f"{FLEET}/branch/law.branch.json", "branchClause", 1)]),
}

def generate(parts):
    out, counts = [], []
    for path, prefix, first in parts:
        law = json.load(open(path))
        if first is None:
            out += [f"def {prefix} (p : Params) : Pred :=", "  " + render(law, 2), ""]
            continue
        if law["type"] != "all":
            sys.exit(f"gen-sheetlaw: {path} is not an `all` of clauses")
        for i, c in enumerate(law["predicates"], first):
            out += [f"/-- clause {i} -/", f"def {prefix}{i} (p : Params) : Pred :=", "  " + render(c, 2), ""]
        counts.append(f"{prefix}{first}..{first + len(law['predicates']) - 1}")
    return "\n".join(out) + "\n\n", ", ".join(counts)

check, bad = "--check" in sys.argv[1:], []
for F, (start, parts) in EMBEDS.items():
    gen, n = generate(parts)
    s = open(F).read()
    a, b = s.index(start), s.index("end Law")
    if check:
        if s[a:b] != gen:
            bad.append(F)
        else:
            print(f"gen-sheetlaw: {F} §2 matches the JSON ({n})")
    else:
        open(F, "w").write(s[:a] + gen + s[b:])
        print(f"gen-sheetlaw: wrote {F} §2 ({n}); the clause lists must name each")
if bad:
    sys.exit(f"gen-sheetlaw: §2 is not the embed of its JSON in: {', '.join(bad)}; run scripts/gen-sheetlaw.py")
