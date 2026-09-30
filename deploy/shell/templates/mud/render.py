# Render the MUD law files (P-LAW grammar, extended below) to Pred JSON.
#
# A copy of planning/place/p-templates-render.py, extended with:
#   * `-- comment` to end of line, and a first-line directive `-- kind: KIND` naming the cell kind
#     whose fields.json resolves `field NAME` (numeric `field 3` still works);
#   * `field NAME VIEW <= v`                 -> le         (Pred/Core.lean `le`)
#   * `eqSlots A B` / `leSlots A B`           -> {"type":"eqSlots"|"leSlots","left","right"}
#                                               (k-sloteq 342d57d, Host/Json.lean shape per planning/place/k-sloteq.md)
#   * `leSlotsOff A B k`                      -> {"type":"leSlotsOff","left","right","offset"}
#                                               NOT LANDED: K-PRED-OFFSET; the JSON key names are ASSUMED
#   * `witnessed ID`                          -> {"type":"witnessed","identifier":ID}
#   * slot operands: `subject` `verb` `cost` (request/*), `clock now|day` (K-CLOCK, NOT LANDED),
#     `field NAME [VIEW]`, `joint I KIND NAME [VIEW]` -> joint/index/I/resource/field/N/VIEW
#     (K-JOINT-INDEX, NOT LANDED; I is the command's 0-based target index, as List.finRange at
#     c-c2:Kernel/DeclaredResourceController.lean:176-180), and `slot PATH` (a raw slot string).
# Every field reference resolves through */fields.json ("kinds" -> kind -> name -> number).
#
# usage: python3 render.py TEMPLATES_MUD_DIR LAWFILE...   (paths relative to TEMPLATES_MUD_DIR)
import json, re, sys, os, glob

T = sys.argv[1]
KINDS = {}
for f in sorted(glob.glob(os.path.join(T, "**", "fields.json"), recursive=True)):
    for k, m in json.load(open(f))["kinds"].items():
        assert k not in KINDS, f"kind {k} defined twice ({f})"
        KINDS[k] = m

TOK = re.compile(r"slot\s+\S+|\{[A-Z0-9_]+\}|<=|==|-?\d+|[A-Za-z][A-Za-z0-9_-]*|[\[\]\(\)\{\},;]")
VIEWS = ("before", "after", "delta")

def tok(s):
    s = "\n".join(line.split("--", 1)[0] for line in s.splitlines())
    out, i = [], 0
    for m in TOK.finditer(s):
        gap = s[i:m.start()]
        if gap.strip(): raise SystemExit(f"untokenizable {gap.strip()!r}")
        out.append(m.group(0)); i = m.end()
    if s[i:].strip(): raise SystemExit(f"untokenizable {s[i:].strip()!r}")
    return out

class P:
    def __init__(s, text, kind): s.t = tok(text); s.i = 0; s.kind = kind
    def peek(s, k=0): return s.t[s.i + k] if s.i + k < len(s.t) else None
    def eat(s, x=None):
        v = s.t[s.i]; s.i += 1
        if x is not None and v != x: raise SystemExit(f"expected {x} got {v} near {s.t[max(0,s.i-6):s.i+3]}")
        return v
    def law(s):
        cs = [s.pred()]
        while s.peek() == ';': s.eat(); cs.append(s.pred())
        if s.peek() is not None: raise SystemExit("trailing " + str(s.t[s.i:s.i+8]))
        return cs
    def lst(s):
        s.eat('['); xs = [s.pred()]
        while s.peek() == ',': s.eat(); xs.append(s.pred())
        s.eat(']'); return xs
    def val(s):
        v = s.eat()
        if not (re.fullmatch(r"-?\d+", v) or re.fullmatch(r"\{[A-Z0-9_]+\}", v)): raise SystemExit(f"bad value {v}")
        return v
    def setv(s):
        s.eat('{'); xs = [s.val()]
        while s.peek() == ',': s.eat(); xs.append(s.val())
        s.eat('}'); return xs
    def fnum(s, kind, name):
        if re.fullmatch(r"\d+", name): return name
        if kind not in KINDS: raise SystemExit(f"no fields.json for kind {kind}")
        if name not in KINDS[kind]: raise SystemExit(f"kind {kind} has no field {name}")
        return KINDS[kind][name]
    def view(s):
        return s.eat() if s.peek() in VIEWS else "after"
    def slot(s):
        w = s.eat()
        if w.startswith("slot"): return w.split(None, 1)[1], None
        if w in ("subject", "verb", "cost"): return "request/" + w, None
        if w == "clock":
            n = s.eat()
            assert n in ("now", "day"), n
            return "clock/" + n, None
        if w == "field":
            n = s.fnum(s.kind, s.eat()); v = s.view()
            return f"resource/field/{n}/{v}", v
        if w == "joint":
            i = s.eat(); assert re.fullmatch(r"\d+", i), i
            k = s.eat(); n = s.fnum(k, s.eat()); v = s.view()
            return f"joint/index/{i}/resource/field/{n}/{v}", v
        raise SystemExit("unknown slot word " + w)
    def pred(s):
        w = s.peek()
        if w == 'sealed': s.eat(); return {"type":"any","predicates":[]}
        if w == 'open': s.eat(); return {"type":"all","predicates":[]}
        if w in ('any','all'): s.eat(); return {"type":w,"predicates":s.lst()}
        if w == 'not':
            s.eat(); s.eat('('); p = s.pred(); s.eat(')'); return {"type":"not","predicate":p}
        if w == 'witnessed': s.eat(); return {"type":"witnessed","identifier":s.eat()}
        if w in ('eqSlots', 'leSlots'):
            s.eat(); a, _ = s.slot(); b, _ = s.slot()
            return {"type":w,"left":a,"right":b}
        if w == 'leSlotsOff':
            s.eat(); a, _ = s.slot(); b, _ = s.slot()
            return {"type":"leSlotsOff","left":a,"right":b,"offset":s.val()}
        slot, view = s.slot()
        op = s.eat()
        if op in ('monotone', 'writeOnce'):
            assert view == 'after', f"{op} on /{view} is vacuous (p-templates finding 1)"
            return {"type":op,"slot":slot}
        if op == '==': return {"type":"eq","slot":slot,"value":s.val()}
        if op == '<=': return {"type":"le","slot":slot,"value":s.val()}
        if op == 'in': return {"type":"memberOf","slot":slot,"values":s.setv()}
        raise SystemExit("unknown op " + op)

def kind_of(text):
    first = text.splitlines()[0]
    m = re.fullmatch(r"--\s*kind:\s*([a-z]+)\s*", first)
    if not m: raise SystemExit("first line must be `-- kind: KIND`")
    return m.group(1)

def render(path):
    text = open(path).read()
    cs = P(text, kind_of(text)).law()
    return cs[0] if len(cs) == 1 else {"type":"all","predicates":cs}

if __name__ == "__main__":
    for f in sys.argv[2:]:
        j = render(os.path.join(T, f))
        open(os.path.join(T, f + ".json"), "w").write(json.dumps(j, indent=2) + "\n")
        print("rendered", f)
