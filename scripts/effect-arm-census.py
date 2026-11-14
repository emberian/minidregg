#!/usr/bin/env python3
"""The hand-arm census of the declared-resource payload (docs/EFFECTS-REVIVAL.md §1a).

    scripts/effect-arm-census.py [ROOT]          a table: per payload kind, hand arms and files
    scripts/effect-arm-census.py --sites [ROOT]  also every counted arm, file:line

A HAND ARM is a match arm, in any Lean file under Kernel/ Compiler/ Host/ Assurance/, of a match
over a `DeclaredResourceController.Payload`, that names a payload constructor. The constructors
are read from the `Payload` inductive in Kernel/ResourceTransaction.lean, so the census follows
the type. A match over a payload is found by its head: `cases payload`, `match … payload … with`,
`cases … : ….payload with`, or a declaration whose signature names `Payload` (a definition by
cases, a structure instance whose fields are given by cases as a codec's `encode`, or a decoder
that returns one). Inside such a declaration an arm on a STRING equal to a constructor's name
(`| "scalar" =>`, the JSON `type` a request decoder dispatches on) is a hand arm too, counted in
its own column.

`registered` is the open constructor: its arms are the registry's (each reads the declaration
`effectAt code`), counted on their own line and never as a kind's hand arms. A kind with no
constructor (a declared effect, as the cited read) has no hand arm by construction; the table
lists the registry's codes with zero.
"""
import os, re, sys

args = [a for a in sys.argv[1:] if not a.startswith("--")]
root = args[0] if args else os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
sites = "--sites" in sys.argv

src = open(os.path.join(root, "Kernel/ResourceTransaction.lean")).read()
m = re.search(r"^inductive Payload where\n(.*?)^\s*deriving", src, re.S | re.M)
ctors = re.findall(r"^\s*\|\s*(\w+)", m.group(1), re.M)

head = re.compile(r"(\bcases\b[^\n]*\bpayload\b)|(\bmatch\b[^\n]*\bpayload\b[^\n]*\bwith\b)|(:\s*\(?[^\n]*\bPayload\b\s*→)|(→\s*Payload\s*→)|(\bPayload\b\s*(:=|where)\s*(do)?\s*$)")
arm = re.compile(r"^\s*\|")
decl = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(?:def|theorem|instance|abbrev|structure|inductive|lemma|example)\b")

counts = {c: [] for c in ctors}
strings = {c: [] for c in ctors}
for top in ("Kernel", "Compiler", "Host", "Assurance"):
    for dirpath, _, names in os.walk(os.path.join(root, top)):
        for name in names:
            if not name.endswith(".lean"):
                continue
            path = os.path.join(dirpath, name)
            lines = open(path, errors="replace").read().split("\n")
            rel = os.path.relpath(path, root)
            i = 0
            while i < len(lines):
                line = lines[i]
                if lines[i].lstrip().startswith("inductive Payload"):
                    i += 1
                    while i < len(lines) and not lines[i].lstrip().startswith("deriving"):
                        i += 1
                    continue
                if not head.search(line):
                    i += 1
                    continue
                # `cases payload <;> tac` splits without naming a constructor
                j = i + 1 if not arm.match(line) else i
                while j < len(lines):
                    text = lines[j]
                    if decl.match(text) or text.startswith("/-") or text.startswith("end ") or text.startswith("namespace "):
                        break
                    if head.search(text) and j != i:
                        break
                    if arm.match(text):
                        pattern = text.split("=>")[0]
                        for c in ctors:
                            if re.search(r'^\s*\|\s*"' + c + r'"\s*$', pattern):
                                strings[c].append((rel, j + 1))
                            elif re.search(r"(?<![\w.\"])\.?" + c + r"\b(?!\s*:=)(?!\")", pattern):
                                counts[c].append((rel, j + 1))
                    j += 1
                i = max(j, i + 1)

legacy = [c for c in ctors if c != "registered"]
print(f"{'payload kind':<16}{'hand arms':>10}{'string arms':>12}{'files':>7}")
for c in legacy:
    files = {f for f, _ in counts[c]} | {f for f, _ in strings[c]}
    print(f"{c:<16}{len(counts[c]):>10}{len(strings[c]):>12}{len(files):>7}")
total = sum(len(counts[c]) for c in legacy)
stotal = sum(len(strings[c]) for c in legacy)
allfiles = {f for c in legacy for f, _ in counts[c]} | {f for c in legacy for f, _ in strings[c]}
print(f"{'TOTAL (hand)':<16}{total:>10}{stotal:>12}{len(allfiles):>7}")
if "registered" in counts:
    r = counts["registered"]
    print(f"{'registered':<16}{len(r):>10}{'':>12}{len({f for f, _ in r}):>7}   (the registry's arms: each reads `effectAt code`)")
    reg = os.path.join(root, "Kernel/ResourceEffectRegistry.lean")
    if os.path.exists(reg):
        bound = re.search(r"def liveEffects[^\n]*:=\s*\[(.*?)\]", open(reg).read(), re.S)
        for code, decl_name in re.findall(r"\((\d+),\s*(\w+)\)", bound.group(1) if bound else ""):
            print(f"{'code ' + code:<16}{0:>10}{0:>12}{0:>7}   (declared: {decl_name}; no constructor, no hand arm)")
if sites:
    for c in ctors:
        for f, n in counts[c]:
            print(f"{c}\t{f}:{n}")
        for f, n in strings[c]:
            print(f'"{c}"\t{f}:{n}')
