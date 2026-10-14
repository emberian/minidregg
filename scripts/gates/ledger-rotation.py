#!/usr/bin/env python3
"""ledger-rotation.py -- the Objective contract ledger is rotated at each pin, never truncated.

The pins (scripts/gates/objective-manifest/) are the state; the ledger
(scripts/gates/objective-contract-changes.txt) is the history of admitted changes. At each
`check-objective-proofs.sh proofs --pin` the live segment's entries are archived byte-exact to
scripts/gates/ledger-archive/<UTC yyyymmddTHHMMSS>-<HEAD sha8>.txt.zst and the live file keeps
only its documentation header (everything up to and including the MARKER line). The ratchet reads
only the live segment: a pinned change needs no line any more.

  rotate LEDGER ARCHIVE_DIR HEAD   archive the live entries (if any) and empty the segment
  check  FROM..TO                  the gate: RED when the entries live at FROM are gone at TO
                                   and no archive ADDED in FROM..TO holds them as a prefix, or
                                   when an archive is modified or deleted in FROM..TO
  selftest                         the check against planted histories in a scratch repository

Entries = the lines load_ledger reads (non-blank, not `#`).
"""
import os, subprocess, sys, tempfile, time

LEDGER = "scripts/gates/objective-contract-changes.txt"
ARCHIVE = "scripts/gates/ledger-archive"
MARKER = "# ---- live segment: entries below; archived at each --pin (scripts/gates/ledger-rotation.py) ----"


def entries(text):
    return [l for l in text.splitlines() if l.strip() and not l.startswith("#")]


def zstd(data, decompress=False):
    args = ["zstd", "-q", "-c"] + (["-d"] if decompress else ["-19", "-T0"])
    return subprocess.run(args, input=data, stdout=subprocess.PIPE, check=True).stdout


def rotate(ledger, archive_dir, head):
    text = open(ledger, encoding="utf-8").read()
    lines = text.splitlines(keepends=True)
    if not any(l.rstrip("\n") == MARKER for l in lines):
        sys.exit(f"ledger-rotation: REFUSED: {ledger} has no marker line; add it below the header")
    cut = next(i for i, l in enumerate(lines) if l.rstrip("\n") == MARKER) + 1
    if not entries(text):
        print("ledger-rotation: live segment empty; nothing archived")
        return
    os.makedirs(archive_dir, exist_ok=True)
    name = f"{time.strftime('%Y%m%dT%H%M%S', time.gmtime())}-{head[:8]}.txt.zst"
    path = os.path.join(archive_dir, name)
    if os.path.exists(path):
        sys.exit(f"ledger-rotation: REFUSED: {path} exists")
    blob = text.encode("utf-8")
    packed = zstd(blob)
    if zstd(packed, decompress=True) != blob:
        sys.exit("ledger-rotation: REFUSED: archive does not round-trip")
    open(path, "wb").write(packed)
    open(ledger, "w", encoding="utf-8").write("".join(lines[:cut]))
    print(f"ledger-rotation: archived {len(entries(text))} entries ({len(blob)} bytes -> {len(packed)}) to {path}; segment emptied")


def git(*args, cwd=None, binary=False):
    r = subprocess.run(["git", *args], cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    if r.returncode != 0:
        return None
    return r.stdout if binary else r.stdout.decode("utf-8")


def check(rng, cwd=None):
    """Return a list of problems (empty = PASS)."""
    frm, to = rng.split("..")
    problems = []
    status = git("diff", "--name-status", "--no-renames", frm, to, "--", ARCHIVE, cwd=cwd) or ""
    added = []
    for row in status.splitlines():
        st, path = row.split("\t", 1)
        if st == "A":
            added.append(path)
        else:
            problems.append(f"archive {path} is {st} in {rng}: archives are add-only")
    old = git("show", f"{frm}:{LEDGER}", cwd=cwd)
    new = git("show", f"{to}:{LEDGER}", cwd=cwd)
    if old is None:
        return problems
    if new is None:
        return problems + [f"{LEDGER} deleted in {rng}"]
    e_old, e_new = entries(old), entries(new)
    if e_new[:len(e_old)] == e_old:
        return problems
    archived = []
    for path in sorted(added):
        blob = git("show", f"{to}:{path}", cwd=cwd, binary=True)
        try:
            archived += entries(zstd(blob, decompress=True).decode("utf-8"))
        except Exception as e:
            problems.append(f"archive {path} does not decompress: {e}")
    if not added:
        problems.append(f"un-archived rotation: {len(e_old)} ledger entries live at {frm[:8]} are gone at {to[:8]} and no archive was added")
    elif archived[:len(e_old)] != e_old:
        miss = next((i for i, (a, b) in enumerate(zip(archived, e_old)) if a != b), min(len(archived), len(e_old)))
        problems.append(f"rotation does not archive the live segment: archives added in {rng} hold {len(archived)} entries, "
                        f"the segment at {frm[:8]} held {len(e_old)}; first difference at entry {miss + 1}")
    return problems


def selftest():
    failed = 0
    with tempfile.TemporaryDirectory() as d:
        run = lambda *a: subprocess.run(a, cwd=d, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        run("git", "init", "-q"); run("git", "config", "user.email", "t@t"); run("git", "config", "user.name", "t")
        os.makedirs(os.path.join(d, os.path.dirname(LEDGER)))
        L = os.path.join(d, LEDGER)
        def commit(msg):
            run("git", "add", "-A"); run("git", "commit", "-q", "--allow-empty", "-m", msg)
            return git("rev-parse", "HEAD", cwd=d).strip()
        head = "# doc\n" + MARKER + "\n"
        e = lambda n: f"N{n}\t{'a'*64}\t{'b'*64}\tredefined\tc\treason {n}\n"
        open(L, "w").write(head + e(1) + e(2)); c0 = commit("base")
        open(L, "a").write(e(3)); c1 = commit("append")
        cases = []
        cases.append(("append-only", f"{c0}..{c1}", True))
        open(L, "w").write(head + e(9)); c2 = commit("truncate without archive")
        cases.append(("truncation without an archive", f"{c1}..{c2}", False))
        run("git", "reset", "-q", "--hard", c1)
        rotate(L, os.path.join(d, ARCHIVE), c1); open(L, "a").write(e(4)); c3 = commit("rotate")
        cases.append(("rotation with its archive", f"{c1}..{c3}", True))
        cases.append(("rotation, range from before the last append", f"{c0}..{c3}", True))
        arch = os.path.join(d, ARCHIVE, os.listdir(os.path.join(d, ARCHIVE))[0])
        open(arch, "wb").write(zstd((head + e(2) + e(3)).encode())); c4 = commit("archive edited")
        cases.append(("an archive edited after it was added", f"{c3}..{c4}", False))
        run("git", "reset", "-q", "--hard", c1)
        os.makedirs(os.path.join(d, ARCHIVE), exist_ok=True)
        open(os.path.join(d, ARCHIVE, "x.txt.zst"), "wb").write(zstd((head + e(2) + e(3)).encode()))
        open(L, "w").write(head); c5 = commit("rotate, archive missing entry 1")
        cases.append(("rotation whose archive drops an entry", f"{c1}..{c5}", False))
        for name, rng, ok in cases:
            p = check(rng, cwd=d)
            good = (not p) == ok
            failed |= not good
            print(f"ledger-rotation self-test {name}: {'PASS' if good else 'FAIL'} ({'green' if not p else 'red: ' + p[0]})")
    return failed


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else ""
    if cmd == "rotate" and len(sys.argv) == 5:
        rotate(*sys.argv[2:])
    elif cmd == "check" and len(sys.argv) == 3:
        if selftest():
            sys.exit("ledger-rotation: self-test FAILED; instrument not trusted")
        p = check(sys.argv[2])
        for x in p:
            print("ledger-rotation: RED " + x)
        print(f"ledger-rotation: {'PASS' if not p else 'RED'} over {sys.argv[2]}")
        sys.exit(1 if p else 0)
    elif cmd == "selftest":
        sys.exit(selftest())
    else:
        sys.exit(__doc__)
