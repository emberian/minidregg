#!/usr/bin/env python3
"""rust-rows.py REPO FROM TO OUT.sh
Write OUT.sh = scripts/check-rust-tests.sh of REPO with only the rows whose crate is
touched by FROM..TO (a changed file under native/<crate>/, or a path dependency of one,
transitively: a change to mini-sdk selects every row of a crate that depends on it).
Prints the selected crates and row names. If no row is selected, OUT.sh runs nothing
and prints 'rust-tests: no touched rows'. Rows: t / exact / known_red / sudo_exact."""
import os, re, subprocess, sys
repo, frm, to, out = sys.argv[1:5]
def git(*a): return subprocess.check_output(["git", "-C", repo, *a], text=True)
changed = git("diff", "--name-only", f"{frm}..{to}").split()
native = os.path.join(repo, "native")
crates = sorted(d for d in os.listdir(native) if os.path.isfile(os.path.join(native, d, "Cargo.toml")))
deps = {}
for c in crates:
    toml = open(os.path.join(native, c, "Cargo.toml")).read()
    deps[c] = set()
    for p in re.findall(r'path\s*=\s*"([^"]+)"', toml):
        tgt = os.path.normpath(os.path.join(native, c, p))
        if os.path.dirname(tgt) == native and os.path.basename(tgt) in crates:
            deps[c].add(os.path.basename(tgt))
def rusty(f):
    # what a cargo build or test of the crate reads: Rust sources, manifests, and files under
    # src/ tests/ benches/ examples/ (fixtures, include_bytes!); a script beside the crate is not
    parts = f.split("/")
    # golden/ and fixtures/ are read by tests through CARGO_MANIFEST_DIR (mini-sdk golden vectors)
    return (f.endswith(".rs") or parts[-1] in ("Cargo.toml", "Cargo.lock", "build.rs")
            or (len(parts) > 3 and parts[2] in ("src", "tests", "benches", "examples", "golden", "fixtures", "testdata")))
def balanced(text, i):
    depth = 0
    for j in range(i, len(text)):
        depth += (text[j] == "(") - (text[j] == ")")
        if depth == 0:
            return j
    return len(text)
def embedded(crate):
    """Repo-relative files (a trailing / names a directory) a crate's sources include_str!/include_bytes!,
    including files outside native/ (deploy/shell/templates/..., Kernel/*.lean) and in-crate files outside
    src/ (journey.d/*.golden.txt). A change to one is a change to the crate's tests; a selector that looks
    only under native/<crate>/src would never run the rows that read it."""
    out, cdir = set(), os.path.join(native, crate)
    for dirpath, dirnames, filenames in os.walk(cdir):
        dirnames[:] = [d for d in dirnames if d not in ("target", ".git")]
        for fn in filenames:
            if not fn.endswith(".rs"):
                continue
            path = os.path.join(dirpath, fn)
            text = open(path, encoding="utf-8", errors="replace").read()
            for m in re.finditer(r"include_(?:str|bytes)!\s*\(", text):
                arg = text[m.end():balanced(text, m.end() - 1)]
                lits = "".join(re.findall(r'"((?:[^"\\]|\\.)*)"', arg))
                if not lits:
                    continue
                base = cdir if "CARGO_MANIFEST_DIR" in arg else dirpath
                rel = os.path.relpath(os.path.normpath(os.path.join(base, lits.lstrip("/") if base == cdir else lits)), repo)
                out.add(rel + ("/" if lits.endswith("/") else ""))
    return out
embeds = {c: embedded(c) for c in crates}
def reads(c, f):
    return any(f == e or (e.endswith("/") and f.startswith(e)) or f.startswith(e + "/") for e in embeds[c])
touched = {f.split("/")[1] for f in changed if f.startswith("native/") and f.count("/") >= 2
           and f.split("/")[1] in crates and rusty(f)}
touched |= {c for c in crates for f in changed if reads(c, f)}
# anything outside native/ that a Rust build reads directly (lockfile/toolchain) selects all rows
if any(f in ("rust-toolchain.toml", "scripts/check-rust-tests.sh") for f in changed):
    touched = set(crates)
sel = set(touched)
grew = True
while grew:
    grew = False
    for c in crates:
        if c not in sel and deps[c] & sel:
            sel.add(c); grew = True
src = open(os.path.join(repo, "scripts/check-rust-tests.sh")).read()
lines = src.split("\n")
# join continuations
logical, buf = [], ""
for ln in lines:
    if buf:
        buf += "\n" + ln
    else:
        buf = ln
    if not ln.endswith("\\"):
        logical.append(buf); buf = ""
if buf: logical.append(buf)
crate_idx = {"t": 3, "exact": 2, "known_red": 3, "sudo_exact": 2}
outl, rows = [], []
for l in logical:
    toks = l.split()
    if toks and toks[0] in crate_idx and not l.lstrip().startswith(("t()", "exact()", "known_red()", "sudo_exact()")) and l == l.lstrip():
        crate = toks[crate_idx[toks[0]]]
        if crate in sel:
            outl.append(l); rows.append(f"{toks[1]}({crate})")
        continue
    outl.append(l)
body = "\n".join(outl)
body = body.replace('root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)', f'root={repo}', 1)
if not rows:
    body = "#!/usr/bin/env bash\necho 'rust-tests: no touched rows'\nexit 0\n"
open(out, "w").write(body)
os.chmod(out, 0o755)
print("touched crates:", " ".join(sorted(touched)) or "-")
print("selected crates (with dependents):", " ".join(sorted(sel)) or "-")
print("rows:", " ".join(rows) or "-")
