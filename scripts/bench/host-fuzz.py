#!/usr/bin/env python3
"""BURN-BENCH Host fuzz harness (stdio frame level).

  fuzz.py run  WORKER NWORKERS SECONDS     fuzz loop (one worker of NWORKERS)
  fuzz.py repro FINDING_DIR                re-run a finding's minimized request on its snapshot
  fuzz.py corpus                           print the corpus op histogram

Corpus: tee2/<driver>/{req,rep}-N.bin + req-N.meta + cfg-H.json + snap-H-HEIGHT.sqlite3 recorded by
host-tee while the real acceptance drivers ran. Each batch restores one snapshot into a private store,
starts the REAL minidregg-host in stdio mode on it, and sends (a) random bytes, (b) single-field
mutations of recorded requests, (c) replays, truncations, one-byte flips; then the untouched recorded
requests as controls. Property per mutated input: a named refusal (or a normal read result), never a
crash/hang(>30s)/unnamed error/memory blowup, and the store head never moves.
"""
import os, sys, json, glob, random, struct, subprocess, time, select, shutil, hashlib, re, sqlite3, signal, copy, traceback

os.umask(0o077)
B = '/srv/lanes/bench-store'
HOST = B + '/set/bin/minidregg-host'
TEE = B + '/tee2'
FZ = B + '/fz'
TAG = b'DREGG/NATIVE-HOST/OUTCOME/v4'
HANG_S = 30
RSS_LIMIT_KB = 6 * 1024 * 1024
CRASH_RE = re.compile(rb'(panic|Segmentation|segfault|uncaught exception|out of memory|stack overflow|core dumped|INTERNAL PANIC|Lean internal|unreachable code|assertion|SIGSEGV|SIGABRT|Aborted)', re.I)
SUBMIT_OPS = {2,20,22,26,28,34,38,40,46,54,60,62,72,76,84,88,94,98,105,110,115,119,125,128,142,162,172,185,189,208,212,217}
ACTIVE_OPS = list(range(0, 256))

# ---------------------------------------------------------------- corpus
def load_corpus():
    items = []
    for meta in sorted(glob.glob(TEE + '/*/req-*.meta')):
        d = os.path.dirname(meta); seq = os.path.basename(meta)[4:10]
        try:
            m = json.load(open(meta))
            if not m.get('snap'): continue
            req = open('%s/req-%s.bin' % (d, seq), 'rb').read()
            rep = open('%s/rep-%s.bin' % (d, seq), 'rb').read()
        except Exception: continue
        if not req: continue
        items.append({'dir': d, 'seq': seq, 'op': req[0], 'req': req, 'rep': rep, 'cfg': '%s/cfg-%s.json' % (d, m['cfg']),
                      'snap': '%s/%s' % (d, m['snap']), 'headAfter': m.get('headAfter')})
    groups = {}
    for it in items: groups.setdefault((it['cfg'], it['snap']), []).append(it)
    return items, groups

# ---------------------------------------------------------------- host session
class HostSession:
    def __init__(self, work, cfgfile, snapfile):
        shutil.rmtree(work, ignore_errors=True)
        self.work = work; os.makedirs(work + '/store', mode=0o700)
        self.db = work + '/store/forward-link.sqlite3'
        shutil.copyfile(snapfile, self.db); os.chmod(self.db, 0o600)
        if os.path.exists(snapfile + '.anchor'):
            shutil.copyfile(snapfile + '.anchor', work + '/store.head-anchor'); os.chmod(work + '/store.head-anchor', 0o600)
        cfg = json.load(open(cfgfile)); cfg['storageRoot'] = work + '/store'
        self.cfgpath = work + '/config.json'; json.dump(cfg, open(self.cfgpath, 'w'))
        self.errpath = work + '/stderr.log'; self.err = open(self.errpath, 'wb')
        self.p = subprocess.Popen([HOST, self.cfgpath, 'stdio'], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=self.err, start_new_session=True)
        self.errpos = 0
    def head(self):
        c = sqlite3.connect('file:%s?mode=ro' % self.db, uri=True, timeout=10)
        try: return c.execute('select max(height) from durable_log').fetchone()[0] or 0
        finally: c.close()
    def rss_kb(self):
        try:
            for l in open('/proc/%d/status' % self.p.pid):
                if l.startswith('VmRSS:'): return int(l.split()[1])
        except Exception: pass
        return 0
    def _read(self, n, deadline):
        fd = self.p.stdout.fileno(); buf = b''
        while len(buf) < n:
            left = deadline - time.time()
            if left <= 0: return None, 'timeout'
            r, _, _ = select.select([fd], [], [], min(left, 1.0))
            if not r:
                if self.p.poll() is not None: return None, 'exit'
                continue
            c = os.read(fd, n - len(buf))
            if not c: return None, 'eof'
            buf += c
        return buf, None
    def call(self, body):
        """-> (status, reply): status in ok|timeout|eof|exit|oversize|write-fail"""
        deadline = time.time() + HANG_S
        try:
            self.p.stdin.write(struct.pack('<I', len(body)) + body); self.p.stdin.flush()
        except Exception:
            return 'write-fail', None
        h, why = self._read(4, deadline)
        if h is None: return why, None
        n = struct.unpack('<I', h)[0]
        if n > (1 << 28): return 'oversize', None
        r, why = self._read(n, deadline)
        if r is None: return why, None
        return 'ok', r
    def new_stderr(self):
        self.err.flush()
        with open(self.errpath, 'rb') as f:
            f.seek(self.errpos); data = f.read(); self.errpos += len(data)
        return data
    def exit_info(self):
        rc = self.p.poll()
        return rc
    def close(self):
        try:
            self.p.stdin.close()
        except Exception: pass
        try: os.killpg(self.p.pid, signal.SIGKILL)
        except Exception: pass
        try: self.p.wait(timeout=5)
        except Exception: pass
        try: self.err.close()
        except Exception: pass

# ---------------------------------------------------------------- mutation
INTERESTING = [0, 1, 2, 0x7f, 0x80, 0xfe, 0xff]
def u32_positions(b):
    out = []
    for i in range(1, len(b) - 3):
        v = struct.unpack_from('<I', b, i)[0]
        if 0 < v <= len(b) - i - 4 + 16: out.append(i)
    return out
def mutate_json(payload, rng):
    try: doc = json.loads(payload.decode())
    except Exception: return None
    leaves = []
    def walk(v, path):
        if isinstance(v, dict):
            for k, x in v.items(): walk(x, path + [k])
        elif isinstance(v, list):
            for i, x in enumerate(v): walk(x, path + [i])
        leaves.append(path)
    walk(doc, [])
    path = rng.choice(leaves)
    def get(d, p):
        for k in p: d = d[k]
        return d
    if not path: return None
    parent = get(doc, path[:-1]); key = path[-1]
    cur = parent[key]
    big = ['0', '-1', '4294967296', '18446744073709551616', '340282366920938463463374607431768211456',
           '', 'x' * 70000, '9' * 400, '00', '+1', '1e9', None, True, [], {}, 'ff' * 5000]
    kind = rng.randrange(6)
    if kind == 0 and isinstance(parent, dict): del parent[key]
    elif kind == 1 and isinstance(cur, str) and re.fullmatch(r'[0-9a-fA-F]*', cur) and cur:
        i = rng.randrange(len(cur)); c = rng.choice('0123456789abcdef'); parent[key] = cur[:i] + c + cur[i+1:]
    elif kind == 2 and isinstance(cur, str) and cur:
        i = rng.randrange(len(cur)); parent[key] = cur[:i] + rng.choice(['\x00', '\xff', '"', '\\', 'é', '\u202e']) + cur[i+1:]
    else: parent[key] = rng.choice(big)
    try: return json.dumps(doc).encode()
    except Exception: return None
def mutate(body, rng, others):
    """-> (kind, newbody)"""
    op, pl = body[0], body[1:]
    kinds = ['flip', 'set', 'trunc', 'extend', 'delete', 'insert', 'dup', 'len', 'sig', 'json', 'opswap', 'randpl', 'swap', 'zero', 'emptypl']
    k = rng.choice(kinds)
    if not pl and k not in ('extend', 'opswap', 'randpl', 'insert'): k = 'randpl'
    b = bytearray(pl)
    if k == 'flip':
        i = rng.randrange(len(b)); b[i] ^= 1 << rng.randrange(8)
    elif k == 'set':
        i = rng.randrange(len(b)); b[i] = rng.choice(INTERESTING + [rng.randrange(256)])
    elif k == 'trunc':
        b = b[:rng.randrange(len(b))]
    elif k == 'extend':
        b += bytes(rng.randrange(256) for _ in range(rng.choice([1, 2, 7, 33, 300])))
    elif k == 'delete':
        i = rng.randrange(len(b)); j = min(len(b), i + rng.choice([1, 2, 4, 32, 64])); del b[i:j]
    elif k == 'insert':
        i = rng.randrange(len(b) + 1); b[i:i] = bytes(rng.randrange(256) for _ in range(rng.choice([1, 4, 32, 65])))
    elif k == 'dup':
        i = rng.randrange(len(b)); j = min(len(b), i + rng.choice([4, 32, 64, 200])); b[j:j] = b[i:j]
    elif k == 'len':
        ps = u32_positions(body)
        if not ps: return mutate(body, rng, others)
        i = rng.choice(ps) - 1; v = struct.unpack_from('<I', b, i)[0]
        nv = rng.choice([0, v + 1, max(0, v - 1), 0xffffffff, 0x80000000, len(b) + 1, v * 2])
        struct.pack_into('<I', b, i, nv & 0xffffffff)
    elif k == 'sig':
        lo = max(0, len(b) - 200); i = rng.randrange(lo, len(b)); b[i] ^= 1 << rng.randrange(8)
    elif k == 'json':
        if pl[:1] in (b'{', b'['):
            r = mutate_json(pl, rng)
            if r is None: return mutate(body, rng, others)
            b = bytearray(r)
        else: return mutate(body, rng, others)
    elif k == 'opswap':
        return k, bytes([rng.choice(sorted(SUBMIT_OPS) if rng.random() < .6 else ACTIVE_OPS)]) + pl
    elif k == 'randpl':
        return k, bytes([op]) + bytes(rng.randrange(256) for _ in range(rng.choice([0, 1, 3, 17, 64, 500, 4096])))
    elif k == 'swap' and others:
        o = rng.choice(others)[1:]
        i = rng.randrange(len(b) + 1); j = min(len(o), i + rng.choice([8, 32, 100]))
        b[i:i+ (j - i)] = o[i:j]
    elif k == 'zero':
        i = rng.randrange(len(b)); j = min(len(b), i + rng.choice([1, 8, 64])); b[i:j] = bytes(j - i)
    elif k == 'emptypl':
        b = bytearray()
    return k, bytes([op]) + bytes(b)
def random_request(rng):
    op = rng.choice(ACTIVE_OPS if rng.random() < .5 else sorted(SUBMIT_OPS | {0, 1, 4, 5, 7, 8, 9, 10, 11}))
    n = rng.choice([0, 1, 2, 4, 8, 33, 100, 1000, 20000])
    mode = rng.randrange(3)
    if mode == 0: pl = bytes(rng.randrange(256) for _ in range(n))
    elif mode == 1: pl = struct.pack('<I', rng.choice([0, 1, 5, 0xffffffff, n])) + bytes(rng.randrange(256) for _ in range(n))
    else: pl = (b'{"' + bytes(rng.randrange(97, 123) for _ in range(5)) + b'":"' + b'9' * rng.choice([1, 40, 500]) + b'"}')
    return 'random', bytes([op]) + pl

# ---------------------------------------------------------------- oracle
def printable_runs(b, n=3):
    return re.findall(rb'[\x20-\x7e]{%d,}' % n, b)
def judge(op, mutated, status, reply, stderr, head0, head1, rss):
    """-> list of (class, detail)"""
    v = []
    if status != 'ok':
        v.append(('crash-or-hang' if status in ('eof', 'exit', 'timeout', 'write-fail', 'oversize') else status, status))
    if rss > RSS_LIMIT_KB: v.append(('memory', 'rss %d MB' % (rss // 1024)))
    if CRASH_RE.search(stderr or b''): v.append(('stderr-crash', CRASH_RE.search(stderr).group(0).decode('latin1')))
    if status == 'ok':
        if reply and reply[0] == 255:
            body = reply[1:]
            if not body.startswith(TAG): v.append(('unnamed-error', 'op255 body without outcome tag: %r' % body[:60]))
            else:
                runs = printable_runs(body[len(TAG):], 2)
                text = b' '.join(runs)
                if not runs or text.strip() in (b'', b'op %d' % op): v.append(('unnamed-error', 'refusal without detail: %r' % body[len(TAG):][:80]))
                elif CRASH_RE.search(text) or re.search(rb'(IO\.Error|user error|exception|index out of|Option\.get|failed to|unexpected)', text, re.I):
                    v.append(('leaky-error', text[:160].decode('latin1')))
        elif reply is not None and len(reply) == 0:
            v.append(('unnamed-error', 'empty reply frame'))
    if mutated and head1 is not None and head0 is not None and head1 != head0:
        v.append(('mutated-commit', 'head %d -> %d' % (head0, head1)))
    return v
def sig_of(op, cls, detail):
    d = re.sub(r'[0-9]+', 'N', detail)[:80]
    return hashlib.sha1(('%d|%s|%s' % (op, cls, d)).encode()).hexdigest()[:12]

# ---------------------------------------------------------------- run a request on a fresh session
def try_once(work, cfg, snap, prior, body):
    """fresh host on snap, send `prior` bodies (ignore result), then body; -> violations"""
    s = HostSession(work, cfg, snap)
    try:
        for p in prior: s.call(p)
        h0 = s.head(); s.new_stderr()
        st, rep = s.call(body)
        time.sleep(0.02)
        err = s.new_stderr(); h1 = s.head()
        v = judge(body[0] if body else -1, True, st, rep, err, h0, h1, s.rss_kb())
        return v, st, rep, err
    finally:
        s.close()
def minimize(work, cfg, snap, prior, body, cls, budget=150):
    """ddmin on bytes keeping the violation class."""
    def bad(b):
        try: v, *_ = try_once(work, cfg, snap, prior, b)
        except Exception: return False
        return any(c == cls for c, _ in v)
    cur = body; n = 2; used = 0
    while len(cur) >= 2 and used < budget:
        chunk = max(1, len(cur) // n); i = 1; shrunk = False
        while i < len(cur) and used < budget:
            cand = cur[:i] + cur[i + chunk:]
            used += 1
            if cand and bad(cand): cur = cand; shrunk = True; n = max(n - 1, 2)
            else: i += chunk
        if not shrunk:
            if chunk == 1: break
            n = min(len(cur), n * 2)
    return cur

# ---------------------------------------------------------------- worker loop
def record(finding_dir, info, files):
    os.makedirs(finding_dir, exist_ok=True)
    for name, data in files.items(): open(os.path.join(finding_dir, name), 'wb').write(data)
    json.dump(info, open(os.path.join(finding_dir, 'info.json'), 'w'), indent=1)
def worker(wid, nw, seconds):
    items, groups = load_corpus()
    keys = sorted(groups)
    if not keys: sys.exit('empty corpus')
    mine = [k for i, k in enumerate(keys) if i % nw == wid] or keys
    # weight groups holding submit ops higher
    weights = [3 if any(it['op'] in SUBMIT_OPS for it in groups[k]) else 1 for k in mine]
    work = '%s/work/w%d' % (FZ, wid); os.makedirs(FZ + '/findings', exist_ok=True); os.makedirs(FZ + '/stats', exist_ok=True)
    stats = {'batches': 0, 'inputs': 0, 'by_kind': {}, 'violations': 0, 'controls': 0, 'control_diff': 0, 'control_fail': 0, 'replay_commit': 0, 'startups': 0}
    seen = set(); t_end = time.time() + seconds; seed0 = int(time.time()) * 1000 + wid
    log = open('%s/stats/w%d.log' % (FZ, wid), 'a')
    while time.time() < t_end:
        key = random.Random(seed0 + stats['batches']).choices(mine, weights)[0]
        cfg, snap = key; grp = groups[key]
        rng = random.Random(seed0 * 7 + stats['batches']); stats['batches'] += 1
        try: s = HostSession(work, cfg, snap)
        except Exception as e:
            log.write('startup fail %r\n' % e); log.flush(); continue
        stats['startups'] += 1
        try:
            bodies = [it['req'] for it in grp]
            plan = []
            for _ in range(rng.choice([15, 30, 60])):
                if rng.random() < 0.15: plan.append(random_request(rng))
                else:
                    base = rng.choice(grp)['req']
                    plan.append(mutate(base, rng, bodies))
            for kind, body in plan:
                if s.exit_info() is not None or s.p.poll() is not None:
                    s.close(); s = HostSession(work, cfg, snap); stats['startups'] += 1
                h0 = s.head(); s.new_stderr()
                st, rep = s.call(body)
                err = s.new_stderr(); rss = s.rss_kb()
                h1 = s.head()
                stats['inputs'] += 1; stats['by_kind'][kind] = stats['by_kind'].get(kind, 0) + 1
                v = judge(body[0] if body else -1, True, st, rep, err, h0, h1, rss)
                if st != 'ok' or h1 != h0 or rss > RSS_LIMIT_KB:
                    s.close(); s = HostSession(work, cfg, snap); stats['startups'] += 1
                for cls, detail in v:
                    sg = sig_of(body[0] if body else -1, cls, detail)
                    stats['violations'] += 1
                    if sg in seen: continue
                    seen.add(sg)
                    fdir = '%s/findings/%s-%s' % (FZ, cls, sg)
                    if os.path.exists(fdir): continue
                    rd = '%s/work/m%d' % (FZ, wid)
                    mini = minimize(rd, cfg, snap, [], body, cls) if (cls != 'mutated-commit' or True) else body
                    record(fdir, {'class': cls, 'detail': detail, 'op': body[0] if body else None, 'mutation': kind, 'cfg': cfg, 'snap': snap,
                                  'prior': [], 'len': len(body), 'minlen': len(mini), 'worker': wid, 'seed': seed0 * 7 + stats['batches'] - 1},
                           {'request.bin': body, 'minimized.bin': mini, 'reply.bin': rep or b'', 'stderr.tail': (err or b'')[-4000:]})
                    shutil.copyfile(snap, fdir + '/snap.sqlite3'); shutil.copyfile(cfg, fdir + '/config.json')
            # controls: the recorded requests, in order, on the very same snapshot
            s.close(); s = HostSession(work, cfg, snap); stats['startups'] += 1
            for it in grp:
                st, rep = s.call(it['req']); stats['controls'] += 1
                if st != 'ok': stats['control_fail'] += 1; continue
                if rep != it['rep']: stats['control_diff'] += 1
                if it['op'] in SUBMIT_OPS:
                    h0 = s.head(); st2, rep2 = s.call(it['req']); h1 = s.head()   # replay
                    if h1 != h0:
                        stats['replay_commit'] += 1
                        sg = sig_of(it['op'], 'replay-commit', '')
                        fdir = '%s/findings/replay-commit-%s' % (FZ, sg)
                        if sg not in seen and not os.path.exists(fdir):
                            seen.add(sg)
                            record(fdir, {'class': 'replay-commit', 'op': it['op'], 'cfg': cfg, 'snap': snap, 'detail': 'exact replay advanced head %d -> %d' % (h0, h1)},
                                   {'request.bin': it['req'], 'minimized.bin': it['req'], 'reply.bin': rep2 or b''})
                            shutil.copyfile(snap, fdir + '/snap.sqlite3'); shutil.copyfile(cfg, fdir + '/config.json')
        except Exception:
            log.write('batch exception %s\n' % traceback.format_exc()); log.flush()
        finally:
            s.close()
        if stats['batches'] % 5 == 0:
            log.write(json.dumps(dict(stats, t=int(time.time()))) + '\n'); log.flush()
    log.write(json.dumps(dict(stats, t=int(time.time()), done=True)) + '\n'); log.close()

def repro(fdir):
    info = json.load(open(fdir + '/info.json'))
    body = open(fdir + '/minimized.bin', 'rb').read()
    v, st, rep, err = try_once(FZ + '/work/repro', fdir + '/config.json', fdir + '/snap.sqlite3', [], body)
    print('class', info['class'], 'op', info['op'], 'len', len(body)); print('status', st, 'violations', v)
    print('reply', (rep or b'')[:200]); print('stderr', err[-300:])

if __name__ == '__main__':
    if sys.argv[1] == 'run': worker(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    elif sys.argv[1] == 'repro': repro(sys.argv[2])
    elif sys.argv[1] == 'corpus':
        items, groups = load_corpus(); import collections
        c = collections.Counter(it['op'] for it in items); print(len(items), 'requests', len(groups), 'groups'); print(sorted(c.items()))
