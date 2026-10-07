#!/usr/bin/env python3
"""objective-manifest.py -- the Objective contract manifests and their ratchet.

The scanner (Verify/ObjectiveManifest.lean, run by scripts/ObjectiveManifest.lean and
scripts/ObjectiveManifestMathlib.lean) writes, per run, the covered declarations (`R` lines), the
constant records of their closure (`C` lines) and the expression DAG those records point into
(node lines). This tool hashes them and ratchets the result against the pinned per-module
manifests, scripts/gates/objective-manifest/<Module>.tsv.

Hashes (SHA-256 throughout):
  node     H(tag, fields, child node hashes): a Merkle hash of the elaborated term, binder names
           and metadata excluded, universe parameters by name.
  self     H(kind, universe parameters, shape, root node hashes) of one constant: its type, plus
           its body for a definition, plus the shape and constructors of an inductive. A leaf of
           the cut (outside the repository, an axiom, an opaque) has its type only.
  closure  over the strongly connected components of the constant graph: a component hashes its
           members' (name, self) and its successor components' hashes; a constant's closure hash is
           H(name, its component's hash). It changes when anything the constant reaches changes.
  stmt     H(kind, universe parameters, type node hash): the elaborated statement.
  contract H(key, kind, stmt, closure, axioms): the row's identity in the ledger.

Manifest row (tab-separated): kind, key, contract, stmt, closure, self (first 16 hex), axioms,
statement text. The key is the shown name, `private <name> @<module>` for a private one. A row's
contract is recomputed on load: a hand-edited pin refuses to load.

The ratchet, per key:
  added       not pinned                                    passes; `pin` adds it
  removed     pinned, gone                                  RED unless the ledger admits it
  restated    kind or stmt hash changed                     RED unless the ledger admits it
  redefined   stmt same, closure hash changed               RED unless the ledger admits it
  axioms      stmt and closure same, axiom set changed      RED unless the ledger admits it
  rerendered  hashes and axioms same, text differs          passes; `pin` refreshes the text
The ledger, scripts/gates/objective-contract-changes.txt, one admitted change per line:
  name <TAB> old contract <TAB> new contract (`-` if removed) <TAB> kind <TAB> commit <TAB> reason
An entry admits exactly that (name, old, new, kind). `pin` writes nothing unless every change is
admitted; it adds rows, applies admitted changes and removals, refreshes text, and nothing else.

usage:
  objective-manifest.py check  --pins DIR --ledger FILE RUN...   ratchet; exit 1 on any red
  objective-manifest.py pin    --pins DIR --ledger FILE RUN...   ratchet, then write the pins
  objective-manifest.py draft  --pins DIR --ledger FILE RUN...   print ledger lines (reason TODO,
                                                                 which the ledger refuses) for review
  objective-manifest.py expect --pins DIR --ledger FILE RUN --changed KEY=KIND[:VIA]... [--plant KEY] [--against RUN0]
      a scratch run (a copy of one module, mutated): every public row it shows must match its pin
      except the named ones, which must classify as KIND (and, for `redefined`, name VIA among the
      changed definitions of their closure), and the ratchet must be red on them; --plant KEY: KEY
      must classify `added` and the ratchet must pass; --against RUN0: compare with RUN0's rows
      instead of the pins.
  objective-manifest.py selftest --pins DIR --ledger FILE RUN... the ratchet logic on synthetic
      removals, restatements, redefinitions, additions and ledger entries over the real rows.
"""
import argparse
import hashlib
import os
import re
import sys

KINDS = ("removed", "restated", "redefined", "axioms")
HEX64 = re.compile(r"^[0-9a-f]{64}$")


def H(*parts):
    h = hashlib.sha256()
    for p in parts:
        if isinstance(p, str):
            p = p.encode()
        h.update(len(p).to_bytes(4, "big"))
        h.update(p)
    return h.digest()


class Run:
    """One scanner output: rows with their hashes."""

    def __init__(self, path):
        self.path = path
        nodes = []
        self.consts = {}  # name -> [internal, kind, lps, extra, roots, deps]
        raw_rows = []
        failures = []
        with open(path, encoding="utf-8") as f:
            for line in f:
                line = line.rstrip("\n")
                t = line[:1]
                if t == "C":
                    p = line.split("\t")
                    roots = [int(r) for r in p[6].split()]
                    self.consts[p[1]] = [p[2] == "I", p[3], p[4], p[5], roots, p[7:]]
                elif t == "R":
                    raw_rows.append(line.split("\t", 6))
                elif t == "a":
                    _, i, j = line.split(" ")
                    nodes.append(H("a", nodes[int(i)], nodes[int(j)]))
                elif t in ("l", "f"):
                    _, bi, i, j = line.split(" ")
                    nodes.append(H(t, bi, nodes[int(i)], nodes[int(j)]))
                elif t == "t":
                    _, nd, i, j, k = line.split(" ")
                    nodes.append(H("t", nd, nodes[int(i)], nodes[int(j)], nodes[int(k)]))
                elif t == "p":
                    _, idx, j, s = line.split(" ", 3)
                    nodes.append(H("p", idx, s, nodes[int(j)]))
                elif t in ("b", "s", "c", "n", "x"):
                    nodes.append(H("leaf", line))
                elif t in ("F", "M"):
                    failures.append(f"instrument: a free variable or metavariable in a constant: {line}")
                    nodes.append(H("leaf", line))
                else:
                    failures.append(f"instrument: unparseable line in {path}: {line[:80]}")
        if failures:
            raise SystemExit("\n".join(failures[:20]))
        self.self_ = {}
        self.stmt = {}
        for name, (internal, kind, lps, extra, roots, _deps) in self.consts.items():
            self.self_[name] = H("C", kind, lps, extra, "I" if internal else "E",
                                 *[nodes[r] for r in roots])
            self.stmt[name] = H("S", kind, lps, nodes[roots[0]])
        self.closure = self._closures()
        self.rows = {}
        for _, name, shown, module, kind, axioms, text in raw_rows:
            key = f"{shown} @{module}" if shown.startswith("private ") else shown
            if name not in self.consts:
                raise SystemExit(f"instrument: row {name} has no constant record")
            row = Row(kind, key, self.stmt[name].hex(), self.closure[name].hex(),
                      self.self_[name].hex()[:16], axioms, text, module)
            row.name = name
            if key in self.rows:
                raise SystemExit(f"instrument: two rows with key {key}")
            self.rows[key] = row

    def deps(self, name):
        c = self.consts[name]
        return [d for d in c[5] if d in self.consts] if c[0] else []

    def _closures(self):
        # iterative Tarjan over the constant graph; components are emitted callees-first
        index, low, onstack, stack = {}, {}, set(), []
        comp_of, comp_hash = {}, []
        counter = 0
        for root in self.consts:
            if root in index:
                continue
            work = [(root, iter(self.deps(root)))]
            index[root] = low[root] = counter
            counter += 1
            stack.append(root)
            onstack.add(root)
            while work:
                v, it = work[-1]
                advanced = False
                for w in it:
                    if w not in index:
                        index[w] = low[w] = counter
                        counter += 1
                        stack.append(w)
                        onstack.add(w)
                        work.append((w, iter(self.deps(w))))
                        advanced = True
                        break
                    elif w in onstack:
                        low[v] = min(low[v], index[w])
                if advanced:
                    continue
                work.pop()
                if work:
                    u = work[-1][0]
                    low[u] = min(low[u], low[v])
                if low[v] == index[v]:
                    members = []
                    while True:
                        w = stack.pop()
                        onstack.discard(w)
                        members.append(w)
                        if w == v:
                            break
                    cid = len(comp_hash)
                    for m in members:
                        comp_of[m] = cid
                    succ = sorted({comp_hash[comp_of[d]] for m in members for d in self.deps(m)
                                   if comp_of.get(d, cid) != cid})
                    mem = sorted((m, self.self_[m]) for m in members)
                    comp_hash.append(H("K", *[x for m, s in mem for x in (m, s)], *succ))
        return {n: H("N", n, comp_hash[comp_of[n]]) for n in self.consts}

    def reach(self, name):
        seen, todo = set(), [name]
        while todo:
            n = todo.pop()
            if n in seen:
                continue
            seen.add(n)
            todo.extend(self.deps(n))
        return seen


class Row:
    def __init__(self, kind, key, stmt, closure, self16, axioms, text, module):
        self.kind, self.key, self.stmt, self.closure = kind, key, stmt, closure
        self.self16, self.axioms, self.text, self.module = self16, axioms, text, module
        self.contract = H("R", key, kind, stmt, closure, axioms).hex()
        self.name = None

    def line(self):
        return "\t".join([self.kind, self.key, self.contract, self.stmt, self.closure,
                          self.self16, self.axioms, self.text])


def load_pins(d):
    pins, problems = {}, []
    if not os.path.isdir(d):
        return pins, [f"no manifest directory {d}"]
    for fn in sorted(os.listdir(d)):
        if not fn.endswith(".tsv"):
            problems.append(f"{d}/{fn}: not a manifest (expected <Module>.tsv)")
            continue
        module = fn[:-4]
        for n, line in enumerate(open(os.path.join(d, fn), encoding="utf-8"), 1):
            line = line.rstrip("\n")
            if not line or line.startswith("#"):
                continue
            p = line.split("\t", 7)
            if len(p) != 8:
                problems.append(f"{fn}:{n}: malformed row")
                continue
            kind, key, contract, stmt, closure, self16, axioms, text = p
            row = Row(kind, key, stmt, closure, self16, axioms, text, module)
            if row.contract != contract:
                problems.append(f"{fn}:{n}: {key}: the contract hash does not match the row (hand-edited pin)")
            if key in pins:
                problems.append(f"{fn}:{n}: {key}: pinned twice")
            pins[key] = row
    return pins, problems


def load_ledger(path):
    admitted, problems = set(), []
    if not os.path.exists(path):
        return admitted, [f"no ledger {path}"]
    for n, line in enumerate(open(path, encoding="utf-8"), 1):
        line = line.rstrip("\n")
        if not line.strip() or line.startswith("#"):
            continue
        p = line.split("\t")
        if len(p) != 6:
            problems.append(f"ledger:{n}: expected 6 tab-separated fields (name, old, new, kind, commit, reason)")
            continue
        name, old, new, kind, commit, reason = p
        if kind not in KINDS:
            problems.append(f"ledger:{n}: kind {kind!r} is not one of {', '.join(KINDS)}")
        if not HEX64.match(old):
            problems.append(f"ledger:{n}: old contract is not a SHA-256 hex digest")
        if (kind == "removed") != (new == "-") or (new != "-" and not HEX64.match(new)):
            problems.append(f"ledger:{n}: new contract must be `-` exactly when the kind is removed")
        if not commit.strip() or not reason.strip() or reason.strip() == "TODO":
            problems.append(f"ledger:{n}: a commit and a reason are required")
        admitted.add((name, old, new, kind))
    return admitted, problems


def classify(p, f):
    if f is None:
        return "removed"
    if p is None:
        return "added"
    if p.kind != f.kind or p.stmt != f.stmt:
        return "restated"
    if p.closure != f.closure:
        return "redefined"
    if p.axioms != f.axioms:
        return "axioms"
    if p.text != f.text or p.module != f.module:
        return "rerendered"
    return "same"


def fresh_rows(runs):
    rows = {}
    for r in runs:
        for k, row in r.rows.items():
            if k in rows:
                raise SystemExit(f"instrument: {k} is covered by two runs (the partition overlaps)")
            rows[k] = (row, r)
    return rows


def via(run, row, pins):
    """The rows of `row`'s closure whose own content changed against the pins."""
    out = []
    for n in sorted(run.reach(row.name)):
        p = pins.get(n)  # a public constant's key is its name
        if p is not None and p.self16 != run.self_[n].hex()[:16]:
            out.append(n)
    return out


def ratchet(pins, fresh, admitted, partial=False):
    """[(kind, key, old, new, row, run, ok)] for every key that is not `same`."""
    out = []
    keys = set(fresh) if partial else set(pins) | set(fresh)
    for k in sorted(keys):
        p = pins.get(k)
        f, run = fresh.get(k, (None, None))
        kind = classify(p, f)
        if kind == "same":
            continue
        old = p.contract if p else "-"
        new = f.contract if f else "-"
        ok = kind in ("added", "rerendered") or (k, old, new, kind) in admitted
        out.append((kind, k, old, new, f, run, ok))
    return out


def report(changes, pins, label):
    red = 0
    counts = {}
    for kind, k, old, new, f, run, ok in changes:
        counts[kind] = counts.get(kind, 0) + 1
        if kind in ("added", "rerendered"):
            continue
        tag = "admitted" if ok else "RED"
        line = f"{label}: {tag} {kind} {k} old={old} new={new}"
        if kind == "redefined" and f is not None:
            v = via(run, f, pins)
            line += f" via {', '.join(v[:12]) + (' ...' if len(v) > 12 else '') if v else '(a generated or unpinned constant of its closure)'}"
        print(line)
        red += not ok
    added = [k for kind, k, *_ in changes if kind == "added"]
    for k in added[:20]:
        print(f"{label}: added {k} (unpinned until `--pin`)")
    if len(added) > 20:
        print(f"{label}: ... {len(added) - 20} more additions")
    summary = ", ".join(f"{n} {k}" for k, n in sorted(counts.items())) or "no changes"
    unpinned = len(added) + counts.get("rerendered", 0)
    print(f"{label}: {summary}; {red} unadmitted"
          + (f"; {unpinned} rows unpinned: `scripts/check-objective-proofs.sh proofs --pin` and commit" if unpinned else ""))
    return red


def write_pins(d, pins, fresh, changes):
    new = dict(pins)
    for kind, k, old, new_c, f, run, ok in changes:
        assert ok
        if kind == "removed":
            del new[k]
        else:
            new[k] = f
    by_module = {}
    for k, row in new.items():
        by_module.setdefault(row.module, []).append(row)
    os.makedirs(d, exist_ok=True)
    for fn in os.listdir(d):
        if fn.endswith(".tsv") and fn[:-4] not in by_module:
            os.remove(os.path.join(d, fn))
    for module, rows in by_module.items():
        if module == "<local>":
            raise SystemExit("pin: refusing to pin a scratch run's rows")
        with open(os.path.join(d, module + ".tsv"), "w", encoding="utf-8") as f:
            f.write(f"# {module}: Objective contract manifest. Written by `scripts/check-objective-proofs.sh proofs --pin`;\n"
                    f"# a removed or changed row needs a line in scripts/gates/objective-contract-changes.txt.\n")
            for row in sorted(rows, key=lambda r: r.key):
                f.write(row.line() + "\n")


def cmd_expect(a, pins, admitted):
    run = Run(a.runs[0])
    if a.against:
        # compare with another run of the same tree instead of the pins (the planted-theorem
        # self-test: the plant run must be the run plus the plant, whatever the tree changed)
        pins = Run(a.against).rows
    fresh = {k: (r, run) for k, r in run.rows.items() if not k.startswith("private ")}
    changes = {c[1]: c for c in ratchet(pins, fresh, admitted, partial=True)}
    want = {}
    for spec in a.changed:
        key, kind = spec.rsplit("=", 1)
        kind, _, v = kind.partition(":")
        want[key] = (kind, v)
    failures = []
    for key, (kind, v) in want.items():
        c = changes.get(key)
        if c is None:
            failures.append(f"{key}: unchanged against its pin (expected {kind})")
            continue
        if c[0] != kind:
            failures.append(f"{key}: classified {c[0]} (expected {kind})")
        if c[6]:
            failures.append(f"{key}: the ratchet admitted it (expected RED)")
        if kind == "redefined":
            p = pins[key]
            if p.text != c[4].text:
                failures.append(f"{key}: the statement text changed (the plant must keep it identical)")
            names = via(run, c[4], pins)
            if v and v not in names:
                failures.append(f"{key}: the report does not name {v} (named: {names[:12]})")
        print(f"expect: {key}: {c[0]} old={c[2]} new={c[3]} {'admitted' if c[6] else 'RED'}"
              + (f" via {', '.join(via(run, c[4], pins)[:6])}" if c[0] == "redefined" else ""))
    if a.plant:
        c = changes.get(a.plant)
        if c is None or c[0] != "added" or not c[6]:
            failures.append(f"{a.plant}: expected an admitted addition, got {c[0] if c else 'nothing'}")
    unexpected = [c for k, c in changes.items() if k not in want and k != a.plant and c[0] not in ("rerendered",)
                  and not (a.allow_downstream and c[0] == "redefined")]
    for c in unexpected[:10]:
        failures.append(f"{c[1]}: unexpected {c[0]}")
    compared = len(fresh)
    if compared < a.floor:
        failures.append(f"only {compared} rows compared (floor {a.floor})")
    for f in failures:
        print(f"expect: FAIL {f}")
    print(f"expect: {compared} rows compared, {len(changes)} differ, {len(failures)} failure(s)")
    return 1 if failures else 0


def cmd_selftest(pins, fresh, admitted):
    """The ratchet's own logic on synthetic changes of the real rows."""
    failures = []
    thm = next(k for k, (r, _) in sorted(fresh.items()) if r.kind == "theorem" and k in pins)
    base = dict(fresh)

    def red_on(mut, kind, key):
        ch = [c for c in ratchet(pins, mut, admitted) if c[1] == key]
        return ch and ch[0][0] == kind and not ch[0][6], ch

    def verdict(mut, adm, key):
        return [c[6] for c in ratchet(pins, mut, adm) if c[1] == key]

    def with_entry(mut, key):
        # only `key`'s verdict: the tree itself may carry other (real) changes
        ch = [c for c in ratchet(pins, mut, admitted) if c[1] == key][0]
        adm = admitted | {(key, ch[2], ch[3], ch[0])}
        good = verdict(mut, adm, key) == [True]
        bad = True
        if ch[3] != "-":
            wrong = admitted | {(key, ch[2], "0" * 64, ch[0])}
            bad = verdict(mut, wrong, key) == [False]
        other = "restated" if ch[0] != "restated" else "redefined"
        bad = bad and verdict(mut, admitted | {(key, ch[2], ch[3], other)}, key) == [False]
        return good, bad

    def mutated(field, value):
        r, run = base[thm]
        r2 = Row(r.kind, r.key, r.stmt, r.closure, r.self16, r.axioms, r.text, r.module)
        setattr(r2, field, value)
        r2.contract = H("R", r2.key, r2.kind, r2.stmt, r2.closure, r2.axioms).hex()
        r2.name = r.name
        m = dict(base)
        m[thm] = (r2, run)
        return m

    cases = [("removed", {k: v for k, v in base.items() if k != thm}),
             ("restated", mutated("stmt", "1" * 64)),
             ("redefined", mutated("closure", "2" * 64)),
             ("axioms", mutated("axioms", "sorryAx"))]
    for kind, m in cases:
        ok, ch = red_on(m, kind, thm)
        if not ok:
            failures.append(f"{kind} of {thm}: not RED as {kind} ({ch})")
            continue
        good, bad = with_entry(m, thm)
        if not good:
            failures.append(f"{kind} of {thm}: the exact ledger entry did not admit it")
        if not bad:
            failures.append(f"{kind} of {thm}: a ledger entry with the wrong new hash or kind admitted it")
    r, run = base[thm]
    plant = Row("theorem", "Minidregg.ObjectiveManifest.Plant.selftest", r.stmt, r.closure, r.self16,
                r.axioms, r.text, r.module)
    m = dict(base)
    m[plant.key] = (plant, run)
    if verdict(m, admitted, plant.key) != [True]:
        failures.append("an added row is not an admitted addition")
    for f in failures:
        print(f"selftest: FAIL {f}")
    print(f"selftest: removed/restated/redefined/axioms of {thm} RED, admitted by their exact ledger entry only "
          f"(not a wrong new hash, not a wrong kind); an addition passes: {'PASS' if not failures else 'FAIL'}")
    return 1 if failures else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("command", choices=["check", "pin", "draft", "expect", "selftest"])
    ap.add_argument("--pins", required=True)
    ap.add_argument("--ledger", required=True)
    ap.add_argument("--label", default="objective-manifest")
    ap.add_argument("--changed", action="append", default=[])
    ap.add_argument("--plant")
    ap.add_argument("--against", help="expect: compare with this run's rows instead of the pins")
    ap.add_argument("--floor", type=int, default=1)
    ap.add_argument("--allow-downstream", action="store_true",
                    help="expect: other rows of the scratch module may be `redefined` (they reach the plant)")
    ap.add_argument("runs", nargs="+")
    a = ap.parse_args()
    pins, problems = load_pins(a.pins)
    admitted, lproblems = load_ledger(a.ledger)
    problems += lproblems
    for p in problems:
        print(f"{a.label}: {p}")
    if problems:
        return 1
    if a.command == "expect":
        return cmd_expect(a, pins, admitted)
    fresh = fresh_rows([Run(p) for p in a.runs])
    if a.command == "selftest":
        return cmd_selftest(pins, fresh, admitted)
    changes = ratchet(pins, fresh, admitted)
    if a.command == "draft":
        for kind, k, old, new, f, run, ok in changes:
            if not ok:
                if kind == "redefined":
                    print(f"# {k}: via {', '.join(via(run, f, pins)) or '(a generated or unpinned constant)'}")
                print("\t".join([k, old, new, kind, "COMMIT", "TODO"]))
        return 0
    red = report(changes, pins, a.label)
    if a.command == "pin":
        if red:
            print(f"{a.label}: pin REFUSED: {red} unadmitted change(s); nothing written")
            return 1
        write_pins(a.pins, pins, fresh, changes)
        print(f"{a.label}: pinned {len(fresh)} rows into {a.pins}")
    return 1 if red else 0


if __name__ == "__main__":
    sys.exit(main())
