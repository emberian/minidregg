#!/usr/bin/env python3
"""Read-only phase check for a private protected-document fixture.

Run only after the private workflow owner hands over its stable phase. This makes
fresh signed reads and local read-attempt files, but performs no document writes,
key imports, membership changes, service restarts, or build. Put --out outside the
workspace: it deliberately retains plaintext response evidence with mode 0600.
"""
import argparse
import html
import json
import os
from pathlib import Path
import re
import subprocess
import time
import urllib.error
import urllib.parse
import urllib.request

parser = argparse.ArgumentParser(description=__doc__)
for field in ("mini", "workspace", "needle-file", "out"):
    parser.add_argument("--" + field, type=Path, required=True)
parser.add_argument("--name", required=True)
parser.add_argument("--expect", choices=("present", "locked", "refused"), required=True)
parser.add_argument("--refusal-pattern", default="revok|no-grant|not authorized|refused|denied")
parser.add_argument("--prior-hit", type=Path)
parser.add_argument("--browser", action="store_true")
parser.add_argument("--retain-browser", action="store_true")
args = parser.parse_args()
os.umask(0o077)
args.out.mkdir(mode=0o700)
needle = args.needle_file.read_text().strip()
assert 12 <= len(needle.encode()) <= 256, "use a distinctive 12–256 byte fixture marker"
assert not args.out.resolve().is_relative_to(args.workspace.resolve()), "keep plaintext test evidence outside the workspace"
patterns = (needle.encode(), needle.encode().hex().encode())
rows = []
web = None
completed = False

def fingerprint():
    files = {}
    for sub in ("attempts", "sources"):
        directory = args.workspace / sub
        if directory.exists():
            for file in directory.rglob("*"):
                if file.is_file() and not file.is_symlink():
                    stat = file.stat()
                    files[str(file)] = (stat.st_ino, stat.st_size, stat.st_mtime_ns)
    return files
before = fingerprint()

def record(name, passed, **evidence):
    rows.append(dict(name=name, passed=bool(passed), **evidence))
    (args.out / "results.json").write_text(json.dumps(rows, indent=2))
    print(name, bool(passed), evidence, flush=True)
    assert passed, name

def call(label, action, success=True):
    start = time.monotonic()
    result = subprocess.run([str(args.mini), "workspace", "--dir", str(args.workspace)] + action,
                            capture_output=True, timeout=240)
    (args.out / (label + ".out")).write_bytes(result.stdout)
    (args.out / (label + ".err")).write_bytes(result.stderr)
    if success and result.returncode:
        raise RuntimeError(label + ": " + result.stderr.decode(errors="replace")[-1200:])
    return result, round(time.monotonic() - start, 3)

def follow(hit, success=True, label="follow"):
    return call(label, ["--action", "doc-search-follow", "--name", hit["name"], "--target", hit["target"],
                           "--atom", hit["atom"], "--revision", hit["revision"]], success)

try:
    result, seconds = call("search", ["--action", "doc-search", "--text", needle, "--scope", args.name])
    search = json.loads(result.stdout)
    docs = search["documents"]
    record("explicit-single-document-scope", len(docs) == 1 and search["through"] == 1)
    if args.expect == "present":
        record("current-authorized-opened-text", search["pageComplete"] and len(search["hits"]) > 0 and docs[0]["status"] == "read", seconds=seconds)
        hit = search["hits"][0]
        (args.out / "hit.json").write_text(json.dumps(hit, indent=2))
        result, elapsed = follow(hit)
        current = json.loads(result.stdout)
        record("fresh-protected-hit-follow", needle.lower() in current["text"].lower(), seconds=elapsed,
               height=current["height"])
    elif args.expect == "locked":
        record("authorized-view-has-no-opened-match", not search["hits"] and docs[0]["status"] == "read" and docs[0]["omittedNonTextOrTranscluded"] > 0, seconds=seconds)
    else:
        error = docs[0].get("error", "")
        record("current-authority-refuses-text", not search["hits"] and not search["pageComplete"] and docs[0]["status"] == "unavailable" and re.search(args.refusal_pattern, error, re.I), seconds=seconds)
    if args.prior_hit:
        prior = json.loads(args.prior_hit.read_text())
        result, seconds = follow(prior, success=args.expect == "present", label="retained-hit-follow")
        if args.expect == "present":
            record("retained-hit-currently-readable", needle.lower() in json.loads(result.stdout)["text"].lower(), seconds=seconds)
        else:
            record("retained-hit-does-not-reveal-text", result.returncode != 0 and needle.encode() not in result.stdout, seconds=seconds)

    if args.browser:
        web = subprocess.Popen([str(args.mini), "web", "--dir", str(args.workspace), "--listen", "127.0.0.1:0"],
                               stdin=subprocess.DEVNULL, stdout=open(args.out / "web.out", "wb"),
                               stderr=open(args.out / "web.err", "wb"), start_new_session=True)
        for _ in range(100):
            urls = re.findall(r"http://127\.0\.0\.1:([0-9]+)/([0-9a-f]+)/", (args.out / "web.out").read_text())
            if urls:
                break
            assert web.poll() is None, "web exited before listening"
            time.sleep(.1)
        port, token = urls[0]
        base = f"http://127.0.0.1:{port}/{token}/"
        (args.out / "browser-private.json").write_text(json.dumps(dict(url=base + "search", remote_port=int(port), web_pid=web.pid, workspace=str(args.workspace)), indent=2))
        def get(path):
            try:
                with urllib.request.urlopen(base + path, timeout=240) as reply:
                    return reply.status, reply.read().decode()
            except urllib.error.HTTPError as reply:
                return reply.code, reply.read().decode()
        status, page = get("search?" + urllib.parse.urlencode(dict(query=needle, scope=args.name)))
        (args.out / "search.html").write_text(page)
        # The query form necessarily echoes the needle. Inspect snippets/hit links,
        # not arbitrary occurrence of the submitted query in the response.
        links = re.findall(r'href="[^\"]*/(search-hit/[^\"]+)"', page)
        snippets = re.findall(r"<blockquote>(.*?)</blockquote>", page, re.S)
        if args.expect == "present":
            record("browser-protected-search", status == 200 and bool(links) and any(needle.lower() in html.unescape(s).lower() for s in snippets))
            status, page = get(links[0])
            (args.out / "hit.html").write_text(page)
            record("browser-protected-hit", status == 200 and needle.lower() in html.unescape(page).lower())
        else:
            record("browser-no-protected-results", status == 200 and not links and not snippets)
    after = fingerprint()
    changed = [Path(path) for path, digest in after.items() if before.get(path) != digest]
    challenges = [path for path in changed if path.name == "challenge.json"]
    record("fresh-read-attempts-created", bool(challenges), challenges=len(challenges))
    leaks = [str(path.relative_to(args.workspace)) for path in changed
             if any(pattern in path.read_bytes() for pattern in patterns)]
    record("read-attempts-retain-no-plaintext-marker", not leaks, files_checked=len(changed), unexpected_paths=leaks)
    completed = True
    print("Protected search phase passed", args.expect, len(rows), flush=True)
finally:
    if web is not None and (not args.retain_browser or not completed):
        web.terminate()
        try:
            web.wait(timeout=10)
        except subprocess.TimeoutExpired:
            web.kill()
            web.wait()
