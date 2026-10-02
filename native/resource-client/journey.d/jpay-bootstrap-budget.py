#!/usr/bin/env python3
"""Measure cold-entry HTTP against a stopped, isolated jpay-e4 fixture.

Requires Linux user systemd, the matched Host/client, and no running fixture
server. Never point this at a deployment store. The optional journal-growth
mode uses only two local synthetic RPC directories and the real verified
observer path; it preserves every cursor, attempt, and tick archive. Reuse
--growth-label and --growth-base-tip with a later --start-tip after interruption
to recover the same deposit origins rather than manufacture replacement ones.

This measures a finite real journal, not an unbounded scalability guarantee.
V1 full-view scans remain capped; v2 uses source-owned exact status operations.
"""
import argparse, concurrent.futures, hashlib, http.client, json, os, re, signal, subprocess, time
from pathlib import Path
p = argparse.ArgumentParser()
p.add_argument('--fixture', required=True)
p.add_argument('--output', required=True)
p.add_argument('--mini', required=True)
p.add_argument('--host', required=True)
p.add_argument('--grow-count', type=int, default=0)
p.add_argument('--source')
p.add_argument('--watcher')
p.add_argument('--growth-label')
p.add_argument('--growth-base-tip', type=int)
p.add_argument('--start-tip', type=int)
a = p.parse_args()
f = Path(a.fixture)
out = Path(a.output)
out.mkdir()
os.chmod(out, 448)
config = f / 'deployment/pinned-config.json'
private = f / 'operator/mini.sock'
public = f / 'public/mini.sock'
unit = 'mini-pay-budget-' + str(os.getpid())
children = []

def run(args, **kw):
    return subprocess.run(list(map(str, args)), capture_output=True, text=True, timeout=60, **kw)

def launch(args, log):
    q = subprocess.Popen(list(map(str, args)), stdout=(out / log).open('wb'), stderr=subprocess.STDOUT, start_new_session=True)
    children.append(q)
    return q

def wait_for(test, q, label):
    for _ in range(1200):
        if q.poll() is not None:
            raise RuntimeError(label + ' exited')
        if test():
            return
        time.sleep(0.1)
    raise RuntimeError(label + ' timeout')

def stop():
    run(['systemctl', '--user', 'stop', unit])
    for q in reversed(children):
        if q.poll() is None:
            os.killpg(q.pid, signal.SIGTERM)
            try:
                q.wait(timeout=20)
            except subprocess.TimeoutExpired:
                os.killpg(q.pid, signal.SIGKILL)
                q.wait(timeout=10)
try:
    q = launch([a.mini, 'serve-operator', '--host', a.host, '--config', config, '--socket', private], 'operator.log')
    wait_for(lambda: 'mini: serving ' + str(private) in (out / 'operator.log').read_text() and private.exists(), q, 'operator')
    q = launch([a.mini, 'serve-public-proxy', '--socket', public, '--upstream', private, '--config', config], 'relay.log')
    wait_for(lambda: 'mini: serving public proxy ' + str(public) in (out / 'relay.log').read_text() and public.exists(), q, 'relay')
    if a.grow_count:
        import sys
        assert a.source and a.watcher and (0 < a.grow_count <= 256)
        sys.dont_write_bytecode = True
        sys.path.insert(0, str(Path(a.source) / 'native/pay-watcher/fixtures'))
        import generate as gen
        tip = a.start_tip or 50000 + a.grow_count
        origin_tip = a.growth_base_tip or tip
        ep = gen.Endpoint()
        ep.put('getSlot/finalized.json', gen.envelope(tip))
        ep.put(f'getBlockTime/{tip}.json', gen.envelope(gen.block_time(tip)))
        for owner, acct in [(gen.ENROL, gen.ENROL_TA), (gen.BOOK0, gen.ATA0)]:
            ep.put(f'getTokenAccountsByOwner/{owner}.{gen.MINT}.json', gen.envelope({'context': {'slot': tip}, 'value': [gen.token_account_entry(acct, owner=owner)]}))
        for i in range(2, 8):
            owner = gen.b58(gen.key(f'book {i}'))
            ep.put(f'getTokenAccountsByOwner/{owner}.{gen.MINT}.json', gen.envelope({'context': {'slot': tip}, 'value': []}))
        history = []
        for i in range(a.grow_count):
            sig = gen.sig(f'bootstrap-budget-{a.growth_label or out.name}-{i}')
            slot = origin_tip - 1 - i
            history.append((sig, slot))
            ep.tx(sig, gen.enrol_tx(sig, slot, 1000000, memos=[]))
        for until in [None] + [sig for sig, _ in history]:
            rows = history if until is None else history[:[sig for sig, _ in history].index(until)]
            suffix = f'.until.{gen.b58(until)}' if until else ''
            ep.put(f'getSignaturesForAddress/{gen.ENROL_TA}{suffix}.json', gen.envelope(gen.listing(*[(sig, slot, None) for sig, slot in rows])))
            if rows:
                ep.put(f'getSignaturesForAddress/{gen.ENROL_TA}.before.{gen.b58(rows[-1][0])}{suffix}.json', gen.envelope([]))
        cursor = json.loads((f / 'ws/30/pay/enrol-cursor.json').read_text())
        for value in cursor['cursors'].values():
            ep.put(f'getSignaturesForAddress/{gen.ENROL_TA}.until.{gen.b58(bytes.fromhex(value))}.json', gen.envelope(gen.listing(*[(sig, slot, None) for sig, slot in history])))
            ep.put(f'getSignaturesForAddress/{gen.ENROL_TA}.before.{gen.b58(history[-1][0])}.until.{gen.b58(bytes.fromhex(value))}.json', gen.envelope([]))
        ep.sigs(gen.ATA0, [])
        dirs = []
        for side in ['a', 'b']:
            d = out / side
            dirs.append(str(d))
            for rel, body in ep.files.items():
                gen.dump(str(d / rel), body)
        env = dict(os.environ, MINI=a.mini, PAY_WATCHER=a.watcher, PAY_STATE=str(out / 'watcher-state'), PAY_OBSERVER_WS=str(f / 'ws/30'), PAY_OBSERVER_CAPABILITY='4030', PAY_ENROL_INDEX='0', PAY_JOURNAL_FLOOR='1000000', PAY_ENROL_CAPABILITY='4032', PAY_OPERATOR_SOCKET=str(private), PAY_RPC_FIXTURES=' '.join(dirs))
        env.pop('PAY_RPC_ENDPOINTS', None)
        baseline = run([a.mini, 'enrollment-view', '--socket', public])
        baseline.check_returncode()
        before = len(json.loads(baseline.stdout)['journal'])
        expected_signatures = {sig.hex() for sig, _ in history}
        (out / 'growth-origin.json').write_text(json.dumps({'signatures': sorted(expected_signatures), 'baselineRows': before, 'originTip': origin_tip, 'startTip': tip}))
        env['PAY_ENROL_ROUNDS'] = '1'
        for round in range(a.grow_count * 2 + 1):
            current = tip + round * 2
            for d in dirs:
                gen.dump(str(Path(d) / 'getSlot/finalized.json'), gen.envelope(current))
                gen.dump(str(Path(d) / f'getBlockTime/{current}.json'), gen.envelope(gen.block_time(current)))
            with (out / 'growth.log').open('a') as log:
                growth = subprocess.run(['sh', str(Path(a.source) / 'deploy/pay/mini-pay-watcher')], env=env, stdout=log, stderr=subprocess.STDOUT, timeout=300)
            if growth.returncode:
                raise RuntimeError('growth tick failed; see growth.log')
            after = run([a.mini, 'enrollment-view', '--socket', public])
            after.check_returncode()
            matched = {j['signature'] for j in json.loads(after.stdout)['journal']} & expected_signatures
            if len(matched) == a.grow_count:
                break
        else:
            raise RuntimeError('verified growth tick did not journal every fixture payment; see growth.log')
    meta = out / 'metadata.json'
    meta.write_text(json.dumps({'sshLogin': 'mini@box.example', 'clientBundleUrl': 'https://box.example/fixture-mini', 'clientBundleSha256': hashlib.sha256(Path(a.mini).read_bytes()).hexdigest()}))
    q = launch(['systemd-run', '--user', '--pipe', '--wait', '--unit', unit, '--property', 'MemoryMax=128M', '--property', 'TasksMax=16', a.mini, 'enrollment-bootstrap', '--host', a.host, '--config', f / 'public/mini.config', '--socket', public, '--listen', '127.0.0.1:0', '--trusted-proxy', '127.0.0.1', '--metadata', meta], 'bootstrap.log')

    def port():
        m = re.search('listening on 127\\.0\\.0\\.1:(\\d+)', (out / 'bootstrap.log').read_text())
        return int(m.group(1)) if m else None
    wait_for(port, q, 'bootstrap')
    n = port()
    key = json.loads((f / 'join/alice/join.json').read_text())['miniKey']
    view = run([a.mini, 'enrollment-view', '--socket', public])
    view.check_returncode()
    v = json.loads(view.stdout)

    def request(i, kind):
        c = http.client.HTTPConnection('127.0.0.1', n, timeout=6)
        t = time.monotonic()
        route = '/mini/v1/enrollment/' + key if kind == 'status' else '/mini/v1/quote' if kind == 'quote' else '/mini/v1/metadata'
        body = json.dumps({'miniKey': key, 'mode': 'renew', 'weeks': '1', 'starterCredit': '0'}) if kind == 'quote' else None
        try:
            c.request('POST' if body else 'GET', route, body, {'X-Real-IP': '192.0.2.' + str(i + 1), 'Content-Type': 'application/json'})
            r = c.getresponse()
            raw = r.read(16385)
            return {'kind': kind, 'status': r.status, 'seconds': time.monotonic() - t, 'bytes': len(raw), 'body': json.loads(raw)}
        except Exception as e:
            return {'kind': kind, 'error': str(e), 'seconds': time.monotonic() - t}
        finally:
            c.close()
    rows = []
    for phase, plan in [('sequential', ['status', 'quote']), ('concurrent', ['status', 'quote', 'metadata'] * 8)]:
        if phase == 'sequential':
            result = [request(i, k) for i, k in enumerate(plan)]
        else:
            with concurrent.futures.ThreadPoolExecutor(max_workers=16) as pool:
                result = list(pool.map(lambda pair: request(*pair), enumerate(plan)))
        rows.append({'phase': phase, 'requests': result})
    metrics = run(['systemctl', '--user', 'show', unit, '--property', 'MemoryPeak,MemoryMax,TasksCurrent,TasksMax,Result']).stdout
    summary = {'journalRows': len(v['journal']), 'enrolledRows': len(v['entries']), 'metrics': metrics, 'phases': rows, 'hostSha256': hashlib.sha256(Path(a.host).read_bytes()).hexdigest(), 'miniSha256': hashlib.sha256(Path(a.mini).read_bytes()).hexdigest(), 'configSha256': hashlib.sha256(config.read_bytes()).hexdigest(), 'fixture': str(f), 'argv': vars(a)}
    if a.grow_count:
        counts = {sig: sum((row['signature'] == sig for row in v['journal'])) for sig in expected_signatures}
        assert all((count == 1 for count in counts.values())), counts
        summary['growth'] = {'exactOrigins': len(counts), 'eachJournalledExactlyOnce': True, 'baselineRows': before, 'originTip': origin_tip, 'currentTip': current}
    (out / 'enrollment-view.json').write_text(json.dumps(v, indent=2))
    (out / 'results.json').write_text(json.dumps(summary, indent=2))
    assert all(('error' not in r and r['seconds'] < 6 and (r['bytes'] <= 16384) for row in rows for r in row['requests'])), summary
    assert all((r['status'] == 200 for r in rows[0]['requests'])), summary
    assert all((r['status'] in [200, 429, 503] for r in rows[1]['requests'])), summary
    assert 'MemoryMax=134217728' in metrics and 'TasksMax=16' in metrics, metrics
    print(json.dumps({'result': 'PASS', 'journalRows': summary['journalRows'], 'metrics': metrics, 'maxSeconds': max((r['seconds'] for row in rows for r in row['requests']))}))
finally:
    stop()
