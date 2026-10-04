#!/usr/bin/env python3
"""FN-DIRECT native acceptance: Mini's fn archive against an isolated fn owner.

  fn_archive_acceptance.py RUN_ROOT HOST CONFIG FN_WRAPPER OPENSSL_PREFIX FIRST_TX FIRST_EVENT

RUN_ROOT is fresh. HOST is the lane's minidregg-host; CONFIG the pinned config of
a Mini world whose service is stopped (its Store has >= 3*k committed heights);
FN_WRAPPER runs `fn --fn VERB`; FIRST_TX/FIRST_EVENT name one accepted Mini
transaction used as archive-funding evidence. The fn owner is started here,
in RUN_ROOT/fn, on a fresh Store (never /tank/fn). Every step writes its
command, stdout, stderr and exit code under RUN_ROOT/steps/; the verdict table
is RUN_ROOT/acceptance.json. Exit 0 iff every check passes.
"""
import json, os, socket, subprocess, sys, time
from pathlib import Path

root, host, config, fnw, ossl_prefix, tx, ev = sys.argv[1:8]
R = Path(root); R.mkdir(parents=True, exist_ok=False)
steps = R / "steps"; steps.mkdir()
OSSL = ossl_prefix + "/bin/openssl"
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE",
           LD_LIBRARY_PATH=ossl_prefix + "/lib64:" + ossl_prefix + "/lib")
results = []
counter = [0]

def run(label, argv, expect=None, timeout=600):
    counter[0] += 1
    stem = steps / ("%02d-%s" % (counter[0], label))
    started = time.time()
    p = subprocess.run([str(a) for a in argv], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       env=env, timeout=timeout)
    stem.with_suffix(".cmd").write_text(" ".join(str(a) for a in argv) + "\n")
    stem.with_suffix(".out").write_bytes(p.stdout)
    stem.with_suffix(".err").write_bytes(p.stderr)
    stem.with_suffix(".rc").write_text("%d %.2fs\n" % (p.returncode, time.time() - started))
    if expect is not None and p.returncode != expect:
        raise SystemExit("%s exited %d (expected %d): %s" % (label, p.returncode, expect,
                         p.stderr.decode(errors="replace")[-800:]))
    return p

def check(cid, ok, detail):
    results.append({"check": cid, "status": "PASS" if ok else "FAIL", "detail": detail})
    (R / "acceptance.json").write_text(json.dumps(results, indent=2) + "\n")
    print(("PASS " if ok else "FAIL ") + cid + ": " + detail, flush=True)

def jload(path):
    return json.loads(Path(path).read_text())

# ---- the isolated fn owner -------------------------------------------------
F = R / "fn"; F.mkdir()
def free_port():
    s = socket.socket(); s.bind(("127.0.0.1", 0)); port = s.getsockname()[1]; s.close(); return port
PORT = free_port()
run("fn-store-init", [fnw, "--fn", "store", F / "store", "init", "mini.archive", "control.cancel"], 0)
(F / "fn.toml").write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                           '[control]\npath = "%s"\n[log]\npath = "%s"\n'
                           % (F / "store", PORT, F / "control.sock", F / "service.log"))
owner = [None]
def start_owner():
    log = open(F / ("owner-%d.out" % counter[0]), "wb")
    err = open(F / ("owner-%d.err" % counter[0]), "wb")
    proc = subprocess.Popen([fnw, "--fn", "operator", str(F / "fn.toml"), "run"],
                            stdout=log, stderr=err, env=env)
    for _ in range(240):
        if b"LISTENING" in Path(log.name).read_bytes():
            break
        time.sleep(0.5)
    else:
        raise SystemExit("fn owner did not start")
    owner[0] = proc
def stop_owner():
    proc = owner[0]
    if proc is None: return
    proc.terminate()
    try: proc.wait(60)
    except subprocess.TimeoutExpired: proc.kill(); proc.wait()
    owner[0] = None

# ---- keys (devnet test material, generated here, never copied anywhere) ---
K = R / "keys"; K.mkdir()
(K / "principal.bin").write_bytes(os.urandom(32))
run("ed-gen", [OSSL, "genpkey", "-algorithm", "ed25519", "-out", K / "ed.pem"], 0)
ed_priv = run("ed-priv", [OSSL, "pkey", "-in", K / "ed.pem", "-outform", "DER"], 0).stdout[-32:]
ed_pub = run("ed-pub", [OSSL, "pkey", "-in", K / "ed.pem", "-pubout", "-outform", "DER"], 0).stdout[-32:]
(K / "ed-public.bin").write_bytes(ed_pub); (K / "ed-secret.bin").write_bytes(ed_priv + ed_pub)
run("ml-gen", [OSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", K / "ml-private.pem"], 0)
run("ml-pub", [OSSL, "pkey", "-in", K / "ml-private.pem", "-pubout", "-out", K / "ml-public.pem"], 0)
ml_raw = run("ml-raw", [OSSL, "pkey", "-in", K / "ml-private.pem", "-pubout", "-outform", "DER"], 0).stdout[-1952:]
keys = {"principal": str(K / "principal.bin"), "edPublic": str(K / "ed-public.bin"),
        "edSecret": str(K / "ed-secret.bin"), "mlPublic": str(K / "ml-public.pem"),
        "mlSecret": str(K / "ml-private.pem")}
(R / "keys.json").write_text(json.dumps(keys))
pin = {"fnBinary": fnw, "mlPublicKey": str(K / "ml-public.pem"),
       "principal": (K / "principal.bin").read_bytes().hex(), "edPublicKey": ed_pub.hex(),
       "mlPublicKeyHex": ml_raw.hex()}
(R / "fn-pin.json").write_text(json.dumps(pin))
K_BUNDLE = int(os.environ.get("ARCHIVE_K", "2"))
archive = {
  "profile": {"fromMailbox": "mini-archive@archive.example.invalid", "newsgroup": "mini.archive",
              "messageIdDomain": "archive.example.invalid", "date": "Thu, 01 Oct 2026 00:00:00 +0000",
              "k": K_BUNDLE, "maxBlockOctets": int(os.environ.get("ARCHIVE_MAX_BLOCK", "60000")),
              "articleBound": 16 * 1024 * 1024},
  "fn": {"control": str(F / "control.sock"), "generation": 1, "mlPublicPem": str(K / "ml-public.pem"),
         "nntpPort": PORT, "pin": "d5b0b9100762f5f03b55f489efaaebc41024d0ce"},
  "fee": {"perOctet": 1, "perTransaction": 1000, "recipient": "archive-fee-recipient-qe6-test"}}
(R / "archive.json").write_text(json.dumps(archive, indent=1))
A = R / "archive.json"
def mini(label, *args, expect=None):
    return run(label, [host, config, "fn-archive", R / "fn-pin.json", *args], expect)

def nntp(cmds):
    s = socket.create_connection(("127.0.0.1", PORT), timeout=30); f = s.makefile("rb")
    f.readline(); out = []
    for c in cmds:
        s.sendall(c.encode() + b"\r\n"); out.append(f.readline().decode().strip())
        if out[-1].startswith("220 ") or out[-1].startswith("211 ") and c.startswith("LISTGROUP"):
            body = []
            while True:
                l = f.readline()
                if l == b".\r\n": break
                body.append(l)
            out.append(b"".join(body))
    s.close(); return out

def sign_and_author(stem, source):
    (R / (stem + ".eml")).write_bytes(source)
    sig = run("sign-" + stem, [fnw, "--fn", "hybrid-sign", K / "principal.bin", K / "ed-public.bin",
               K / "ed-secret.bin", K / "ml-public.pem", K / "ml-private.pem", R / (stem + ".eml")], 0)
    parts = dict(l.split() for l in sig.stdout.decode().splitlines())
    (R / (stem + ".ed")).write_bytes(bytes.fromhex(parts["ed25519"]))
    (R / (stem + ".ml")).write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
    return run("author-" + stem, [fnw, "--fn", "hybrid-author", F / "control.sock", "1",
               R / (stem + ".eml"), R / (stem + ".ed"), R / (stem + ".ml"), K / "ml-public.pem"])

def group_count():
    line = nntp(["GROUP mini.archive"])[0]
    return int(line.split()[1]) if line.startswith("211 ") else -1

start_owner()
run("fn-enroll", [fnw, "--fn", "hybrid-enroll", F / "control.sock", "1", K / "principal.bin",
                  K / "ed-public.bin", K / "ml-public.pem"], 0)

# ---- the fee gate ------------------------------------------------------------
p = mini("publish-unfunded", "publish", A, "1", "-", R / "keys.json", R / "r-unfunded.json")
check("fee:unfunded-refused-before-signing", p.returncode != 0 and b"refused before posting" in p.stderr
      and group_count() == 0, p.stderr.decode(errors="replace").strip()[-200:])
mini("fund", "fund", A, "100000000", tx, ev, R / "r-fund.json", expect=0)

# ---- check 1: one bundle of k finalized blocks posted once ----------------
mini("publish-1", "publish", A, "1", "-", R / "keys.json", R / "r-pub1.json", expect=0)
r1 = jload(R / "r-pub1.json"); M1 = r1["messageId"]
check("1:posted-once", r1["outcome"] == "acknowledged" and not r1["resend"] and group_count() == 1,
      "%s heights %d..%d %d octets fee %d, fn group count %d" % (M1, r1["identity"]["first"],
      r1["identity"]["last"], r1["sourceOctets"], r1["fee"], group_count()))

# ---- check 2: identical resend -> :duplicate, exit 0, one record ----------
p = mini("resend-1", "resend", A, M1, R / "r-resend1.json")
rr = jload(R / "r-resend1.json")
check("2:duplicate", p.returncode == 0 and rr["exit"] == 0 and rr["word"] == "DUPLICATE" and group_count() == 1,
      "resend of persisted bytes (no keys read): exit %d word %s; fn group count %d" % (rr["exit"], rr["word"], group_count()))

# ---- check 4: fetch back by Message-ID, extract, digest matches ------------
p = mini("lookup-1", "lookup", A, M1, R / "r-look1.json")
l1 = jload(R / "r-look1.json")
check("4:read-back-verified", p.returncode == 0 and l1["readBack"] == "verified",
      "ARTICLE %s -> %s (%s); bundle digest %s" % (M1, l1["readBack"], l1["recorded"], l1["identity"]["bundleDigest"][:24]))

# ---- check 3 + adapter (a): a changed source under a Mini Message-ID ------
# bundle 2: Mini persists its signed article while the owner is down (not-connected),
# then a substitute signed by the same author lands first under that Message-ID.
first2 = 1 + K_BUNDLE
stop_owner()
p = mini("publish-2-owner-down", "publish", A, str(first2), "-", R / "keys.json", R / "r-pub2a.json")
r2a = jload(R / "r-pub2a.json"); M2 = r2a["messageId"]
start_owner()
mini("reconcile-pending", "reconcile", A, R / "r-rec0.json", expect=0)
pend = [row["messageId"] for row in jload(R / "r-rec0.json")["pending"]]
check("6a:owner-down-leaves-pending", M2 in pend and r2a["outcome"].startswith(("transient", "unknown")),
      "owner down: exit %d %s; %s pending (Unknown) in the journal" % (r2a["exit"], r2a["outcome"], M2))
# The substitute: Mini's headers under M2, a different (still base64) body, signed by the same author.
sub = ("From: mini-archive@archive.example.invalid\r\nDate: Thu, 01 Oct 2026 00:00:00 +0000\r\n"
       "Newsgroups: mini.archive\r\nSubject: Mini archive\r\nMessage-ID: %s\r\nMini-Archive: v1\r\n\r\n"
       "Zm9yZ2Vk\r\n" % M2).encode()
a = sign_and_author("substitute-2", sub)
p = mini("resend-2-after-substitute", "resend", A, M2, R / "r-resend2.json")
rs2 = jload(R / "r-resend2.json")
art = nntp(["ARTICLE " + M2])
check("3:conflict-stores-nothing", a.returncode == 0 and rs2["exit"] == 1 and rs2["word"] == "CONFLICT"
      and art[0].startswith("220 ") and art[1].endswith(sub),
      "substitute accepted first (exit %d); Mini's persisted bytes answered exit %d %s; fn still serves the substitute only"
      % (a.returncode, rs2["exit"], rs2["word"]))
p = mini("lookup-2-substitute", "lookup", A, M2, R / "r-look2.json")
l2 = jload(R / "r-look2.json")
check("a:substitute-refused-by-name", p.returncode != 0 and l2["readBack"].startswith("refused"),
      "%s -> %s" % (M2, l2["readBack"]))

# ---- check 5: a cancelled archive article reads back withdrawn ------------
first3 = 1 + 2 * K_BUNDLE
mini("publish-3", "publish", A, str(first3), "-", R / "keys.json", R / "r-pub3.json", expect=0)
M3 = jload(R / "r-pub3.json")["messageId"]
cancel = ("From: mini-archive@archive.example.invalid\r\nDate: Thu, 01 Oct 2026 00:00:01 +0000\r\n"
          "Newsgroups: mini.archive\r\nSubject: cmsg cancel %s\r\nMessage-ID: <cancel-3@archive.example.invalid>\r\n"
          "Control: cancel %s\r\n\r\ncancel\r\n" % (M3, M3)).encode()
c = sign_and_author("cancel-3", cancel)
time.sleep(2)
p = mini("lookup-3-withdrawn", "lookup", A, M3, R / "r-look3.json")
l3 = jload(R / "r-look3.json")
p_abs = nntp(["ARTICLE <never-posted@archive.example.invalid>"])
check("5:withdrawn-not-absent", c.returncode == 0 and l3["readBack"].startswith("withdrawn"),
      "cancel exit %d; %s -> %s; a never-posted id answers %r" % (c.returncode, M3, l3["readBack"], p_abs[0]))

# ---- adapter (b): the cursor holds at an omitted object -------------------
(R / "cursor").write_text("1\n")
p = mini("follow-1", "follow", A, R / "cursor", R / "r-f1.json")
f1 = jload(R / "r-f1.json")
(R / "cursor").write_text("%d\n" % first3)
p3 = mini("follow-3-withdrawn", "follow", A, R / "cursor", R / "r-f3.json")
f3 = jload(R / "r-f3.json")
check("b:cursor-holds-on-omission", p.returncode == 0 and f1["cursorAfter"] == first2 and
      p3.returncode != 0 and f3["cursorAfter"] == first3 and "withdrawn" in f3["outcome"],
      "follow 1 -> %d (%s); follow %d -> %d (%s)" % (f1["cursorAfter"], f1["outcome"], first3,
      f3["cursorAfter"], f3["outcome"]))

# ---- check 6: a post across an fn owner restart --------------------------
first4 = 1 + 3 * K_BUNDLE
stop_owner()
p = mini("publish-4-owner-down", "publish", A, str(first4), "-", R / "keys.json", R / "r-pub4a.json")
r4a = jload(R / "r-pub4a.json"); M4 = r4a["messageId"]
start_owner()
p2 = mini("publish-4-after-restart", "publish", A, str(first4), "-", "-", R / "r-pub4b.json")
r4b = jload(R / "r-pub4b.json")
check("6:restart-resolves-same-identity", r4a["outcome"].startswith(("transient", "unknown"))
      and p2.returncode == 0 and r4b["messageId"] == M4 and r4b["resend"] and r4b["outcome"].startswith("acknowledged"),
      "owner down: exit %d %s; after restart, no keys given: %s %s, same Message-ID %s"
      % (r4a["exit"], r4a["outcome"], r4b["word"], r4b["outcome"], M4))

# ---- adapter (c): every acknowledged identity is listed after restart ----
stop_owner(); start_owner()
p = mini("reconcile", "reconcile", A, R / "r-rec.json", "lookup", expect=0)
rec = jload(R / "r-rec.json")
listed = {row["messageId"]: row["readBack"] for row in rec["acknowledged"]}
check("c:acknowledged-listed-after-restart", set(listed) >= {M1, M3, M4} and listed[M1] == "verified"
      and listed[M4] == "verified" and listed[M3].startswith("withdrawn"),
      json.dumps(listed))
stop_owner()
sys.exit(0 if all(r["status"] == "PASS" for r in results) else 1)
