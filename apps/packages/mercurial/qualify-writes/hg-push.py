#!/usr/bin/env python3
"""hg-push.py ROUTE_DIR FILENAME TEXT [REPO]: push one changeset over Mercurial's HTTP wire protocol.

Mercurial 7.2.4 (apps/packages/mercurial/runner.py) serves an hgwebdir collection whose hgrc sets
allow_push = * and push_ssl = False; REPO is the repository's URL name under it. No hg client is
assumed: this builds the HG10UN changegroup by hand (changelog, manifest and one filelog, each a single
revision whose parents are the null revision, so the delta is a whole-file insert against the empty
text) and POSTs it to /REPO?cmd=unbundle with heads=force over the owner route (http.sock, session
cookie, Origin).
Prints one JSON line {"ok": true, "node": HEX, "reply": FIRST_LINE}; exit 0 only on a pushed changeset.
"""
import hashlib, http.client, json, os, socket, struct, sys

COOKIE = "__Host-mini_spk_session"
NULL = b"\0" * 20


class Conn(http.client.HTTPConnection):
    def __init__(self, route):
        super().__init__("grain.test", timeout=120)
        self.route = route
        self.token = open(os.path.join(route, "browser.token")).read().strip()

    def connect(self):
        self.sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.sock.settimeout(120)
        self.sock.connect(os.path.join(self.route, "http.sock"))

    def call(self, method, path, body=None, ctype=None):
        h = {"Cookie": "%s=%s" % (COOKIE, self.token), "Origin": "https://grain.test"}
        if ctype:
            h["Content-Type"] = ctype
        self.request(method, path, body=body, headers=h)
        r = self.getresponse()
        return r.status, r.read()


def node(p1, p2, text):
    a, b = sorted((p1, p2))
    return hashlib.sha1(a + b + text).digest()


def chunk(data):
    return struct.pack(">l", len(data) + 4) + data


def delta_chunk(n, p1, p2, link, text):
    # cg1 delta header: node p1 p2 linknode; the first revision's base is p1 (null), so one patch
    # hunk (start 0, end 0, length) replaces the empty text with the whole text.
    return chunk(n + p1 + p2 + link + struct.pack(">lll", 0, 0, len(text)) + text)


def bundle(fname, content, user, when, desc):
    fnode = node(NULL, NULL, content)
    manifest = fname.encode() + b"\0" + fnode.hex().encode() + b"\n"
    mnode = node(NULL, NULL, manifest)
    clog = (mnode.hex() + "\n" + user + "\n" + "%d 0" % when + "\n" + fname + "\n\n" + desc).encode()
    cnode = node(NULL, NULL, clog)
    out = b"HG10UN"
    out += delta_chunk(cnode, NULL, NULL, cnode, clog) + b"\0\0\0\0"        # changelog group
    out += delta_chunk(mnode, NULL, NULL, cnode, manifest) + b"\0\0\0\0"    # manifest group
    out += chunk(fname.encode()) + delta_chunk(fnode, NULL, NULL, cnode, content) + b"\0\0\0\0"  # filelog
    out += b"\0\0\0\0"                                                       # end of files
    return cnode.hex(), out


def main():
    route, fname, text, base = sys.argv[1:5]
    c = Conn(route)
    st, caps = c.call("GET", "/" + base + "?cmd=capabilities")
    if st != 200 or b"unbundle" not in caps:
        print(json.dumps({"ok": False, "why": "capabilities %d: %r" % (st, caps[:120])})); return 1
    cnode, data = bundle(fname, text.encode(), "resident <resident@mini>", 1793000000, "written by a resident over the wire protocol")
    st, rep = c.call("POST", "/" + base + "?cmd=unbundle&heads=" + b"force".hex(), data, "application/mercurial-0.1")
    first = rep.split(b"\n", 1)[0].decode("latin1")
    if st != 200 or not first.isdigit() or int(first) < 1:
        print(json.dumps({"ok": False, "why": "unbundle %d: %r" % (st, rep[:200])})); return 1
    print(json.dumps({"ok": True, "node": cnode, "reply": first})); return 0


sys.exit(main())
