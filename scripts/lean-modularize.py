#!/usr/bin/env python3
"""scripts/lean-modularize.py -- move Lean files onto Lean 4.30's module system, mechanically.

    scripts/lean-modularize.py [--check] FILE.lean...
    scripts/lean-modularize.py --batches ROOT...     print the import-closed conversion batches of ROOT's closure

Why (docs/COORDINATION-2026-10-27.md §3, the lane loop): a non-`module` .olean carries every proof
body, so a one-line proof edit changes the olean and Lake rebuilds every transitive dependent. A
`module`'s public .olean carries statements and exposed definitions only; theorem bodies live in
.olean.private, and Lake's output-hash cutoff stops at a module whose public .olean did not change.
Measured on Lake 4.30 (scratch toy, 2026-10-27): a proof edit under `module` rebuilds no dependent
unless it changes the theorem's exported axiom set or adds a public auxiliary declaration (e.g. the
first `simp [f]` that generates `f.eq_1`); a NON-module importer still rebuilds (it loads the private
parts), and a `module` may import only modules, so conversion runs bottom-up in import-closed batches.

The transform, statement-preserving (no declaration text changes):
  * `module` before the first import;
  * every `import X` becomes `public import X` (keeps today's transitive visibility);
  * a file that evaluates code at elaboration (`native_decide`, `#eval`, `#guard <term>`, `decide +native`)
    also gets `meta import X` for each import (meta imports load the compiled IR, transitively);
  * `@[expose] public section` right after the header: definitions stay unfoldable downstream
    (`decide`, `rfl`, `simp [f]`), theorems are opaque as they always were in the kernel's sense.
  The package-wide `backward.privateInPublic` (lakefile.toml leanOptions) lets a module's OWN private
  names appear in its public statements and exposed bodies; another module still cannot name them,
  so the private-constructor token discipline (TokenCensus) is unchanged.
--check exits 1 if any FILE is not yet a module (no rewrite).
"""
import os, re, subprocess, sys, collections
sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
from lean_imports import header_layout, file_imports

# A file runs code at elaboration when it evaluates (`native_decide`, `#eval`, `#guard` term) or defines an
# elaborator/macro whose body calls imported definitions: each import then needs a `meta import`.
EVAL = re.compile(r"native_decide|^\s*#eval\b|^\s*#guard\s(?!_msgs)|^\s*#guard_expr\b|decide\s*\+\s*native|^\s*#reduce\b"
                  r"|^\s*(?:@\[[^\]]*\]\s*)?(?:elab|elab_rules|macro|macro_rules)\b", re.M)


# Header lines a converted file needs beyond its own imports (all statement-preserving; the home
# modules never change under a build, so `import all` of them costs no rebuild):
#  * `import all`: bodies the home module does not expose to a module importer. Kernel reduction
#    (`decide`) through core: `toString`/`s!` of Nat and List (Nat.toDigits), Array.map, Array.zip, the
#    UTF-8 encoder. Mathlib's derive handlers, whose generated instances `cases` on the handler's own
#    private types (`deriving Encodable`: Mathlib.Deriving.Encodable.S).
#  * `meta import`: a module whose `initialize` registers an attribute or extension; under the module
#    system its initializers run in an importer's elaboration only through a meta import.
#  * `public import`: a module a non-module file reached through a PRIVATE import of core or Mathlib
#    (non-public imports do not propagate under the module system).
# RULES fire on a pattern in the file's body; PER_FILE names what no pattern can see, as printed by
# scripts/module-hidden-bodies.sh FILE on a box (never by guessing). An `import all` of one of OUR modules
# (derived Repr/DecidableEq bodies are not exposed) re-links that one file to the module's private olean.
CORE_REDUCE = ["Init.Data.Repr", "Init.Data.ToString.Basic", "Init.Data.ToString.Extra", "Init.Data.Array.Basic",
               "Init.Data.ByteArray.Basic", "Init.Data.String.Decode", "Init.Data.String.Defs",
               "Init.Control.Except", "Init.Data.List.Basic", "Init.Data.Nat.Bitwise.Basic",
               "Init.Data.String.Bootstrap", "Init.Data.Format.Basic", "Init.Data.List.Scan.Basic"]
RULES = [
    (re.compile(r"\bdecide\b|\brfl\b"), ["import all " + m for m in CORE_REDUCE]),
    # Mathlib's Encodable handler cases on its private `S`; Theory.DeriveEncodable is that handler with
    # `S` public (same encoding), registered after Mathlib's so it is the one that runs
    (re.compile(r"deriving\b[^\n]*\bEncodable\b"), ["public import Theory.DeriveEncodable"]),
    (re.compile(r"deriving\b[^\n]*\bCountable\b"), ["import all Mathlib.Tactic.DeriveCountable"]),
    (re.compile(r"deriving\b[^\n]*\bFintype\b"), ["import all Mathlib.Tactic.DeriveFintype"]),
    (re.compile(r"persisted_codec_tag|make_persisted_codec_manifest"), ["meta import Compiler.PersistedCodecTagRegistry"]),
    # `rfl` through IO/EIO binds unfolds EST.bind/EST.pure
    (re.compile(r"\A(?=[\s\S]*\brfl\b)(?=[\s\S]*\b(?:IO|EIO|BaseIO)\b)"), ["import all Init.System.ST", "import all Init.System.IO"]),
]
# lines an earlier rule set wrote and the current one replaces
RETIRED = {"import all Mathlib.Tactic.DeriveEncodable"}
# Files that stay non-modules, with the reason. A non-module sees every imported body; a module may not
# import one, so every importer of a kept file is kept too (the list is closed under importers).
KEEP = set()
PER_FILE = {
    "Compiler/Mersenne127.lean": ["import all Mathlib.NumberTheory.LucasLehmer"],
    "Kernel/GenericSimplex.lean": ["import all Init.Util"],
    "Compiler/CredentialAuthorityDomainReceiver.lean": ["import all Init.Util"],
    "Host/CapacityJson.lean": ["import all Lean.Data.Json.Basic", "import all Init.Data.Nat.Bitwise.Basic",
                               "import all Init.Data.String.Search", "import all Init.Prelude",
                               "import Std.Data.TreeMap.Raw.Lemmas", "import Std.Data.String.ToNat"],
    "Kernel/WorldRoot.lean": ["import all Init.Data.Format.Basic", "import all Init.Data.Nat.Bitwise.Basic",
                              "import all Init.Data.String.Bootstrap", "import all Mathlib.Data.List.Sort"],
    "Kernel/Seat.lean": ["import all Init.Data.Format.Basic", "import all Init.Data.Nat.Bitwise.Basic",
                         "import all Init.Data.String.Bootstrap", "import all Mathlib.Data.List.Sort",
                         "import all Kernel.Invitation", "import all Theory.TypedAuthorization"],
    "Compiler/ObjectiveBendPublication.lean": ["import all Init.Data.String.Defs"],
    "Kernel/LawView.lean": ["import Std.Data.String.ToNat"],
    # `String.startsWith` reduces through the whole string-slice pattern family
    "Host/FnArchivePublisher.lean": ["import all Init.Data.String.*", "import all Init.Prelude"],
    "Host/Json.lean": ["import all Init.Data.Int.Repr", "import all Init.Data.List.Sort.Basic",
                       "import all Init.Data.Range.Basic", "import all Init.Data.String.Legacy",
                       "import all Init.Data.String.Pattern.String", "import all Init.Data.String.Search",
                       "import all Init.Data.String.Slice", "import all Init.Data.String.TakeDrop",
                       "import all Init.Prelude", "import all Lean.Data.Json.Basic",
                       "import all Lean.Data.Json.FromToJson.Basic", "import all Lean.Data.Json.Parser",
                       "import all Lean.Data.Json.Printer", "import all Std.Data.DHashMap.Basic"],
    "Kernel/ObjectiveActivityReceiver.lean": ["import all Init.System.ST", "import all Init.System.IO"],
    "Compiler/ObjectiveBendTermWire.lean": ["import all Lean.Data.Json.Basic", "import all Lean.Data.Json.FromToJson.Basic",
                                            "public import Std.Data.TreeMap.Raw.Lemmas"],
}
CORE_NOTE = "-- Bodies this file reduces or derives through, not exposed by their modules (module system).\n"
SECTION = "@[expose] public section\n"
CORE_BLOCK = re.compile(r"\n-- (?:`decide` reduces these core definitions|Bodies this file reduces)[^\n]*\n(?:(?:import all|meta import|public import|import) [^\n]*\n)+")


_CORE_FAMILY = {}


def expand(line):
    """`import all Init.Data.String.*`: every toolchain module under that prefix (from `lean --print-prefix`)."""
    if not line.endswith(".*"):
        return [line]
    head, prefix = line[:-2].rsplit(" ", 1)
    if prefix not in _CORE_FAMILY:
        root = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
        src = os.path.join(root, "src", "lean", *prefix.split("."))
        mods = []
        for d, _, fs in os.walk(src):
            for f in fs:
                if f.endswith(".lean"):
                    rel = os.path.relpath(os.path.join(d, f), os.path.join(root, "src", "lean"))
                    mods.append(rel[:-5].replace(os.sep, "."))
        _CORE_FAMILY[prefix] = sorted(mods)
    return [f"{head} {m}" for m in _CORE_FAMILY[prefix]]


def wanted(body, path):
    lines = [l for rx, ls in RULES if rx.search(body) for l in ls] + PER_FILE.get(path, [])
    return list(dict.fromkeys(x for l in lines for x in expand(l)))


def convert(text, path=""):
    """The module form of text, or None when text is already in it."""
    first, imports, end, keywords = header_layout(text)
    if "prelude" in keywords:
        raise SystemExit("prelude files are not converted")
    body = text[end:]
    m = CORE_BLOCK.search(text)
    have = [l for l in m.group(0).strip().split("\n")[1:]] if m else []
    have = [l for l in have if l not in RETIRED]
    me = path.removesuffix(".lean").replace("/", ".")
    lines = [l for l in dict.fromkeys(have + wanted(body, path)) if l.split()[-1] != me]
    block = (CORE_NOTE + "".join(l + "\n" for l in lines) + "\n") if lines else ""
    if "module" in keywords:
        if EVAL.search(body):
            # every public import of a file that runs code at elaboration also needs its meta import
            pub = [mo for (s, e, _, mo) in imports if text[s:e].split()[0] == "public" and text[s:e].split()[1] != "meta"]
            have_meta = {mo for (s, e, _, mo) in imports if "meta" in text[s:e].split()[:2]}
            add = [mo for mo in pub if mo not in have_meta]
            if add:
                last = max(e for (s, e, _, mo) in imports if text[s:e].split()[0] == "public")
                text = text[:last] + "".join(f"\nmeta import {mo}" for mo in add) + text[last:]
        stripped = CORE_BLOCK.sub("\n", text)
        stripped = re.sub(r"\n\n+(?=" + re.escape(SECTION) + ")", "\n\n", stripped)
        i = stripped.find("\n" + SECTION)
        if i < 0:
            raise SystemExit(f"{path}: a module without `@[expose] public section` after its header: convert it by hand")
        new = stripped[:i + 1] + block + stripped[i + 1:]
        return None if new == text else new
    mods = [mo for (_, _, _, mo) in imports]
    evals = bool(EVAL.search(body))
    head = "module\n\n"
    head += "".join(f"public import {mo}\n" for mo in mods)
    if evals:
        head += "".join(f"meta import {mo}\n" for mo in mods)
    head += ("\n" + block if block else "\n") + SECTION
    # with no imports, the file may open with a `/-!` module doc, which is a command: `module` goes first
    if not mods:
        return head + "\n" + text.lstrip("\n")
    return text[:first] + head + "\n" + text[end:].lstrip("\n")


def batches(roots):
    files = [f for f in subprocess.check_output(["git", "ls-files", "*.lean"]).decode().split("\n") if f]
    mods = {f[:-5].replace("/", "."): f for f in files}
    imp = {}
    seen, stack = set(), list(roots)
    while stack:
        m = stack.pop()
        if m in seen or m not in mods:
            continue
        seen.add(m)
        imp[m] = [d for d in file_imports(mods[m]) if d in mods]
        stack += imp[m]
    depth = {}
    sys.setrecursionlimit(20000)
    def d(m):
        if m not in depth:
            depth[m] = 0
            depth[m] = 1 + max([d(x) for x in imp[m]] or [0])
        return depth[m]
    for m in seen:
        d(m)
    return mods, depth


def main(argv):
    if argv[:1] == ["--batches"]:
        mods, depth = batches(argv[1:])
        lay = collections.defaultdict(list)
        for m, k in depth.items():
            lay[k].append(m)
        for k in sorted(lay):
            print(k, len(lay[k]), " ".join(sorted(mods[m] for m in lay[k])))
        return 0
    check = argv[:1] == ["--check"]
    files = argv[1:] if check else argv
    bad = 0
    for f in files:
        if f in KEEP:
            continue
        text = open(f, encoding="utf-8").read()
        new = convert(text, f)
        while new is not None and (again := convert(new, f)) is not None:
            new = again
        if new is None:
            continue
        if check:
            if "module" in header_layout(text)[3]:
                continue
            print(f"not a module: {f}")
            bad = 1
        else:
            open(f, "w", encoding="utf-8").write(new)
    return bad


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
