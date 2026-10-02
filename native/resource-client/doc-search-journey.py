#!/usr/bin/env python3
"""Receiving test against a PRIVATE disposable Mini fixture, never a live member Store.

Provide initialized owner + reader workspaces on the same Host. The owner needs a
funded factory reference. Creates a fresh document, delegates/revokes it, tests
native shell and actual HTTP search, and retains all deciding outputs. Does not
build Lean or start/stop the Store. Uses the workspace's pinned Host and socket.
"""
import argparse
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import time
import urllib.error
import urllib.parse
import urllib.request

parser = argparse.ArgumentParser(description=__doc__)
for field in ("mini", "owner", "reader", "out"):
    parser.add_argument("--" + field, type=Path, required=True)
parser.add_argument("--name", default="search-paper")
args = parser.parse_args()
args.out.mkdir(mode=0o700)
os.umask(0o077)
rows = []
subject = json.loads((args.reader / "workspace.json").read_text())["subject"]
name = args.name
web = None

def record(label, condition, **detail):
    rows.append(dict(name=label, passed=bool(condition), **detail))
    (args.out / "results.json").write_text(json.dumps(rows, indent=2))
    print(label, bool(condition), detail, flush=True)
    assert condition, label

def run(label, command, success=True):
    start = time.monotonic()
    result = subprocess.run([str(args.mini)] + command, capture_output=True)
    (args.out / (label + ".out")).write_bytes(result.stdout)
    (args.out / (label + ".err")).write_bytes(result.stderr)
    if success and result.returncode:
        raise RuntimeError(label + ": " + result.stderr.decode(errors="replace")[-1500:])
    return result, round(time.monotonic() - start, 3)

def work(label, command, workspace=None, success=True):
    return run(label, ["workspace", "--dir", str(workspace or args.owner)] + command, success)

def shell(label, command):
    return run(label, ["shell", "--workspace", str(args.owner), "--home", str(args.out / "home"), "--line", command])

def search(label, query, workspace=None, scope=None):
    result, seconds = work(label, ["--action", "doc-search", "--text", query, "--scope", scope or name], workspace)
    return json.loads(result.stdout), seconds

def proposal(label, body):
    request = args.out / (label + ".json")
    request.write_text(json.dumps({"type": "minidregg-workspace-proposal-v1", **body}))
    work(label + "-propose", ["--action", "propose", "--request", str(request), "--proposal-id", label])
    work(label + "-submit", ["--action", "submit", "--intent", str(args.owner / "proposals" / label / "intent.json"), "--attempt", str(args.owner / "attempts" / label)])

def grant(label, fields=None):
    body = dict(action="delegate", name=name, recipient=subject, verbs=["observe"], maxCost="50000")
    if fields is not None:
        body["fields"] = fields
    proposal(label, body)
    work(label + "-publish", ["--action", "publish-delegation", "--proposal-id", label, "--attempt", str(args.owner / "attempts" / label)])
    work(label + "-import", ["--action", "import", "--name", label, "--from-ref", str(args.owner / "proposals" / label / "recipient-reference.json")], args.reader)
    return label

def follow(label, hit, workspace=None, success=True):
    return work(label, ["--action", "doc-search-follow", "--name", hit["name"], "--target", hit["target"], "--atom", hit["atom"], "--revision", hit["revision"]], workspace, success)

try:
    shell("new", "doc new " + shlex.quote(name))
    for i, text in enumerate(["The amber compass.", "A quiet quartz garden."]):
        label = f"{name}-seed-{i}"
        shell(label, f"doc append {label} {name} " + shlex.quote(text))
        shell(label + "-submit", "submit " + label)
    first, seconds = search("before", "amber")
    record("fresh-current-text-search", len(first["hits"]) == 1, seconds=seconds)
    hit = first["hits"][0]
    result, seconds = follow("follow", hit)
    record("stable-hit-follow", not json.loads(result.stdout)["changed"], seconds=seconds)
    result, seconds = shell("shell-search", f"doc search amber {name}")
    record("shell-search-connected", len(json.loads(result.stdout)["hits"]) == 1, seconds=seconds)

    web = subprocess.Popen([str(args.mini), "web", "--dir", str(args.owner), "--listen", "127.0.0.1:0"], stdin=subprocess.DEVNULL, stdout=open(args.out / "web.out", "wb"), stderr=open(args.out / "web.err", "wb"))
    for _ in range(100):
        urls = re.findall(r"http://127\.0\.0\.1:[0-9]+/[0-9a-f]+/", (args.out / "web.out").read_text())
        if urls:
            break
        if web.poll() is not None:
            raise RuntimeError("web exited before listening")
        time.sleep(.1)
    base = urls[0]
    def get(path, origin=None):
        request = urllib.request.Request(base + path, headers={} if origin is None else {"Origin": origin})
        try:
            with urllib.request.urlopen(request, timeout=180) as reply:
                return reply.status, reply.read().decode()
        except urllib.error.HTTPError as reply:
            return reply.code, reply.read().decode()
    status, html = get("search?" + urllib.parse.urlencode(dict(query="amber", scope=name)))
    (args.out / "web-search.html").write_text(html)
    record("web-search-connected", status == 200 and "The amber compass." in html)
    link = re.search(r'href="[^\"]*/(search-hit/[^\"]+)"', html).group(1)
    status, html = get(link)
    record("web-stable-hit-follow", status == 200 and "The amber compass." in html)
    status, _ = get("search?query=amber&scope=" + name, "https://foreign.example")
    record("foreign-origin-refused", status == 403)

    shell("fresh-before-edit", "doc show " + name)
    label = name + "-edit"
    shell(label, f'doc edit {label} {name} 1 "Silver replaces the old needle."')
    shell(label + "-submit", "submit " + label)
    current, seconds = search("after-edit", "amber")
    record("changed-text-disappears", not current["hits"] and current["pageComplete"], seconds=seconds)
    result, _ = follow("follow-changed", hit)
    current = json.loads(result.stdout)
    record("old-hit-follows-current-revision", current["changed"] and current["text"] == "Silver replaces the old needle.")

    shared = grant(name + "-reader")
    current, seconds = search("reader-before-revoke", "Silver", args.reader, shared)
    record("recipient-sees-shared-text", len(current["hits"]) == 1, seconds=seconds)
    reader_hit = current["hits"][0]
    proposal(name + "-revoke", dict(action="revoke", name=name, recipient=subject))
    current, seconds = search("reader-revoked", "Silver", args.reader, shared)
    record("revoked-results-disappear", not current["hits"] and not current["pageComplete"] and current["documents"][0]["status"] == "unavailable", seconds=seconds)
    result, _ = follow("reader-revoked-follow", reader_hit, args.reader, False)
    record("revoked-hit-follow-refused", result.returncode != 0 and b"Silver" not in result.stdout)
    narrowed = grant(name + "-narrow", ["annotations"])
    current, seconds = search("reader-narrowed", "Silver", args.reader, narrowed)
    record("narrowed-view-no-cached-text", not current["hits"], seconds=seconds, status=current["documents"][0]["status"])
    restored = grant(name + "-again")
    current, seconds = search("reader-restored", "Silver", args.reader, restored)
    record("authorized-navigation-resumes", len(current["hits"]) == 1, seconds=seconds)
    current, _ = search("missing-reference", "Silver", scope="missing-" + name + "," + name)
    record("failed-reference-not-no-results", len(current["hits"]) == 1 and not current["pageComplete"])
    wrong = {**hit, "target": "0"}
    result, _ = follow("wrong-target", wrong, success=False)
    record("retargeted-name-refused", result.returncode != 0 and b"different document" in result.stderr)
    print("All receiving checks passed", len(rows), flush=True)
finally:
    if web is not None:
        web.terminate()
        try:
            web.wait(timeout=10)
        except subprocess.TimeoutExpired:
            web.kill()
            web.wait()
