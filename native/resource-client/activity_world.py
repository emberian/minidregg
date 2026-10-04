"""A scratch NATIVE world for the kernel activity, and the helpers every activity journey shares.

  from activity_world import World

One `World` is a fresh private one-sponsor Store (newparticipant-acceptance.sh) whose genesis pins this
checkout's Objective invocation policy (its maximum envelope, tariff and source bound are the activity
kernel's configuration) and enrolls a second subject (40: its own key and Book account). Never a live
or common world. Every activity turn is `mini activity --action submit` (Host op 7 author, op 210 plan,
the workspace key signs the header, op 211 assemble, op 212 submit); every refusal is the Host's, by
name; the public view (op 214) reads the cells back. ROOT/transcript holds every command's exact
output.

A journey records its rows through `World.turn` / `World.check` and groups them with `World.group`
(one group = one row of the journey table). `World.finish` writes ROOT/results.json and
ROOT/groups.tsv (ID, STATUS, WALL_S, DETAIL: the journey runner's sub-row format) and returns the
process exit code (1 on any red row).
"""
import contextlib, json, os, pathlib, subprocess, sys, time, traceback

MAXIMUM = {'typeFuel': 16384, 'sourceTicks': 200000, 'heap': 200000, 'stack': 200000, 'outputNodes': 20000,
           'outputBytes': 200000, 'inputBytes': 200000, 'scalarBits': 512, 'memoryTouches': 2000000,
           'proofWork': 900000, 'feeDebit': 1000000, 'turnBytes': 4000000, 'witnessBytes': 4000000,
           'storageBytes': 4000000, 'sideEffectCount': 16, 'networkBytes': 0, 'leaseByteBlocks': 0,
           'incidences': 16}
TARIFF = {'version': '1', 'base': '1', 'typeFuel': '0', 'sourceTicks': '1', 'heap': '0', 'stack': '0',
          'outputNodes': '0', 'outputBytes': '0', 'inputBytes': '0'}
PERMIT_ALL = {'type': 'all', 'predicates': []}

# A declared envelope of TICKS source ticks is priced base + ticks (TARIFF); an await escrows one
# resume envelope and one timeout envelope, the activity's purse must hold the pair.
TICKS = 3000
PRICE = 1 + TICKS
PAIR = 2 * PRICE


def nat(n):
    return {'tag': 'natural', 'value': str(n)}


def record(**fields):
    return {'tag': 'record', 'fields': [{'name': k, 'value': v} for k, v in fields.items()]}


def variant(label, payload):
    return {'tag': 'variant', 'label': label, 'payload': payload}


def cap(ticks, full=True):
    """A declared envelope (Capacity): `ticks` source ticks; a full one also declares the kernel's fixed
    heap, stack, type fuel and Plan budget (Config.covers), priced at 0."""
    c = {k: '0' for k in MAXIMUM}
    if full:
        for k in ['heap', 'stack', 'typeFuel', 'outputNodes', 'outputBytes']:
            c[k] = str(MAXIMUM[k])
    c['sourceTicks'] = str(ticks)
    return c


def eq(slot, value):
    return {'type': 'eq', 'slot': slot, 'value': str(value)}


def le(slot, value):
    return {'type': 'le', 'slot': slot, 'value': str(value)}


def monotone(slot):
    return {'type': 'monotone', 'slot': slot}


def all_of(*predicates):
    return {'type': 'all', 'predicates': list(predicates)}


def any_of(*predicates):
    return {'type': 'any', 'predicates': list(predicates)}


def unhex(text):
    try:
        return bytes.fromhex(text).decode(errors='replace')
    except (ValueError, TypeError):
        return str(text)


class World:
    def __init__(self, bin_dir, root, repo, second_subject='40'):
        os.umask(0o077)
        self.repo = pathlib.Path(repo).resolve()
        self.root = pathlib.Path(root).resolve()
        if self.root.exists():
            raise SystemExit('root must be new')
        self.root.mkdir(mode=0o700)
        self.T = self.root / 'transcript'
        self.T.mkdir()
        binary = pathlib.Path(bin_dir).resolve()
        self.host, self.mini, self.store, self.verifier = [
            binary / n for n in ['minidregg-host', 'mini', 'minidregg-link-sqlite-store',
                                 'minidregg-credential-signature-verifier']]
        self.counter = 0
        self.results = []
        self.groups = []
        self.current = None
        self.totals = []
        self.SECOND = second_subject
        self.attempts = self.root / 'attempts'
        self.attempts.mkdir()
        self.objects = {}

    # --- commands -------------------------------------------------------------------
    def sh(self, label, *cmd, ok=(0,), env=None):
        self.counter += 1
        tag = f'{self.counter:03d}-{label}'
        e = dict(os.environ)
        e.update(env or {})
        r = subprocess.run([str(c) for c in cmd], stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=e)
        (self.T / f'{tag}.cmd').write_text(' '.join(str(c) for c in cmd) + '\n')
        (self.T / f'{tag}.out').write_bytes(r.stdout)
        (self.T / f'{tag}.err').write_bytes(r.stderr)
        (self.T / f'{tag}.rc').write_text(f'{r.returncode}\n')
        if r.returncode not in ok:
            raise RuntimeError(f'FAILED {tag} rc={r.returncode}: {r.stderr.decode(errors="replace")[-1500:]}')
        return r

    @staticmethod
    def last_json(r):
        text = r.stdout.decode(errors='replace').strip()
        if not text:
            return {'error': r.stderr.decode(errors='replace').strip()[-800:]}
        try:
            return json.loads(text.splitlines()[-1])
        except json.JSONDecodeError:
            return {'unparsed': text[-800:]}

    # --- the world -------------------------------------------------------------------
    def bring_up(self, object_names, sponsor_balance='1000000'):
        """Genesis with the Objective policy and a second enrolled subject, then one native resource
        (object cell + operation capability) per name, none of them an object yet (no record)."""
        root = self.root
        constants = json.loads(self.sh('constants', self.host, '/dev/null', 'objective-constants').stdout)
        policy = {'schema': 'dregg.objective-bend.policy.v1', 'sourceBytes': '4194304',
                  'maximum': {k: str(v) for k, v in MAXIMUM.items()}, 'outputs': [constants['genericCodec']],
                  'clearAudience': '01ff', 'frontEnd': constants['frontEnd'], 'tariff': TARIFF}
        (root / 'policy.json').write_text(json.dumps(policy, indent=1))
        self.sh('policy', self.host, '/dev/null', 'author', 'objective-policy', root / 'policy.json',
                root / 'policy.hex')
        self.sh('keygen-second', self.mini, 'keygen', '--secret', root / 'second.key', '--public',
                root / 'second.pub')
        public = (root / 'second.pub').read_bytes().hex()
        enrollment = [{'key': {'keyId': '4000', 'keyEpoch': '2', 'algorithm': '1', 'subject': self.SECOND,
                               'publicKey': public, 'activeFrom': '0', 'activeUntil': '1000000',
                               'nextKeyDigest': None},
                       'accountId': self.SECOND, 'spendCapabilityId': '4002', 'controlCapabilityId': '4003',
                       'factoryObserveCapabilityId': '4004', 'initialBalance': '100000',
                       'accountPredicate': {'type': 'all', 'predicates': []}}]
        (root / 'enrollment-second.json').write_text(json.dumps(enrollment))
        self.W = root / 'w'
        self.sock = self.W / 'public' / 'mini.sock'
        self.sh('genesis', 'sh', self.repo / 'native/resource-client/newparticipant-acceptance.sh', self.host,
                self.mini, self.store, self.verifier, self.W, self.sock,
                env={'OBJECTIVE_INVOCATION_POLICY': (root / 'policy.hex').read_text().strip(),
                     'EXTRA_GENESIS_ENROLLMENTS': str(root / 'enrollment-second.json'),
                     'NEWPARTICIPANT_SPONSOR_BALANCE': sponsor_balance})
        self.config = self.W / 'deployment' / 'pinned-config.json'
        self.sponsor = self.W / 'sponsor'
        self.second = root / 'second'
        self.second.mkdir(mode=0o700)
        (self.second / 'workspace.json').write_text(json.dumps({
            'type': 'minidregg-participant-workspace-v1', 'host': str(self.host), 'socket': str(self.sock),
            'config': str(self.config), 'key': str(root / 'second.key'), 'subject': self.SECOND}))
        params = json.loads((self.W / 'genesis-params.json').read_text())
        self.SPONSOR = str(params['sponsor']['subject'])
        self.SPONSOR_ACCOUNT = str(params['sponsor']['accountId'])
        self.SPONSOR_SPEND = str(params['sponsor']['spendCapabilityId'])
        self.COLLECTOR = str(params['collector'])
        (root / 'permit-all.json').write_text('{"type":"all","predicates":[]}\n')
        for name in object_names:
            self.sh(f'resource-{name}', self.mini, 'workspace', '--action', 'create', '--dir', self.sponsor,
                    '--name', name, '--storage', 'content', '--predicate', root / 'permit-all.json')
            ref = json.loads((self.sponsor / 'refs' / f'{name}.json').read_text())
            self.objects[name] = {'object': ref['target'], 'capability': ref['operationCapability']}
        (root / 'objects.json').write_text(json.dumps(self.objects, indent=1))

    def stop(self):
        try:
            pid = int((self.W / 'public' / 'server.pid').read_text())
            os.kill(pid, 15)
        except (FileNotFoundError, ValueError, ProcessLookupError):
            pass

    # --- turns and views ---------------------------------------------------------------
    def view(self, label, request):
        r = self.sh(f'view-{label}', self.mini, 'activity', '--action', 'view', '--workspace', self.sponsor,
                    '--request', json.dumps(request))
        return self.last_json(r)

    def watched(self, label):
        v = self.view(label, {'accounts': [self.SPONSOR_ACCOUNT, self.SECOND, self.COLLECTOR]})
        self.totals.append({'after': label, 'height': v.get('height'), 'total': v.get('total')})
        return v

    def turn(self, label, workspace, body, expect, detail=None, prepare=False):
        """One signed command. `expect`: installed | replayed | refused | conflict | prepared. A refusal
        may name its reason in `detail` (a substring, or a list of substrings, of the Host's refusal text)."""
        out = self.attempts / label
        command = self.root / f'{label}.turn.json'
        command.write_text(json.dumps(body))
        args = ['activity', '--action', 'submit', '--workspace', workspace, '--command', command, '--out', out]
        if prepare:
            args += ['--prepare-only', 'true']
        r = self.sh(label, self.mini, *args, ok=(0, 1, 2))
        return self.judge(label, self.last_json(r), expect, detail)

    def resubmit(self, label, ingress, expect, detail=None):
        r = self.sh(label, self.mini, 'activity', '--action', 'resubmit', '--workspace', self.sponsor,
                    '--ingress', ingress, ok=(0, 1, 2))
        return self.judge(label, self.last_json(r), expect, detail)

    def judge(self, label, value, expect, detail):
        kind = value.get('type')
        reason = value.get('reason', '')
        text = unhex(value.get('detail', '')) if 'detail' in value else value.get('error', '')
        text = ' '.join(str(text).split())  # the Host prints refusals pretty-wrapped
        if expect == 'installed':
            ok = kind == 'confirmed' and value.get('confirmation') == 'installed'
        elif expect == 'replayed':
            ok = kind == 'confirmed' and value.get('confirmation') == 'replayed'
        elif expect == 'prepared':
            ok = kind == 'prepared'
        elif expect == 'conflict':
            ok = kind == 'refused' and reason == 'conflict'
        else:
            ok = kind == 'refused' or 'refused' in str(value.get('error', ''))
        if ok and detail is not None:  # one substring, or a list of them: every one must be in the refusal text
            ok = all(d in text for d in ([detail] if isinstance(detail, str) else detail))
        self._row({'step': label, 'expect': expect, 'detailExpected': detail, 'type': kind, 'reason': reason,
                   'detail': text[-300:], 'ok': ok})
        print(f'{label:44} {expect:9} {kind} {reason} {text[-120:]}', flush=True)
        return value

    def check(self, label, condition, observed):
        self._row({'step': label, 'expect': 'check', 'ok': bool(condition), 'observed': observed})
        print(f'{label:44} check     {"ok" if condition else "MISMATCH"} {json.dumps(observed)[:160]}', flush=True)

    def _row(self, row):
        row['group'] = self.current
        self.results.append(row)

    @contextlib.contextmanager
    def group(self, name):
        """One row of the journey table: PASS when every row recorded inside is ok and nothing raised."""
        self.current = name
        start = time.time()
        first = len(self.results)
        error = None
        try:
            yield
        except Exception as e:  # a step that cannot run is a red group, not a dead journey
            error = f'{type(e).__name__}: {e}'
            traceback.print_exc()
            self.results.append({'step': f'{name}-raised', 'expect': 'no exception', 'ok': False,
                                 'observed': error[-300:], 'group': name})
        rows = self.results[first:]
        bad = [r['step'] for r in rows if not r['ok']]
        detail = (f'{len(rows)} rows ok' if not bad else f'{len(bad)} of {len(rows)} rows red: ' + ', '.join(bad[:6]))
        self.groups.append({'id': name, 'status': 'PASS' if not bad and rows else 'FAIL',
                            'wall': int(time.time() - start), 'detail': detail})
        self.current = None

    def finish(self, extra=None):
        failed = [r['step'] for r in self.results if not r['ok']]
        (self.root / 'results.json').write_text(json.dumps(dict(
            rows=self.results, totals=self.totals, objects=self.objects, allPass=not failed, **(extra or {})),
            indent=1) + '\n')
        (self.root / 'groups.tsv').write_text(''.join(
            f"{g['id']}\t{g['status']}\t{g['wall']}\t{g['detail']}\n" for g in self.groups))
        print(json.dumps({'rows': len(self.results), 'failed': failed}))
        return 1 if failed else 0

    # --- reading cells --------------------------------------------------------------------
    @staticmethod
    def cell_of(v, cell):
        return next((c for c in v.get('cells', []) if c.get('cell') == cell), {})

    @staticmethod
    def balance(v, account):
        return int(next(b['balance'] for b in v['balances'] if b['account'] == account))

    def publication(self, label, modules, entry_module, entry):
        """Capture and lower a package with the Host's own front end into an activity artifact."""
        pub = self.root / label
        pub.mkdir()
        spec = {'schema': 'dregg.objective-bend.package-input.v1', 'edition': 'objective-bend-1',
                'modules': modules, 'entryModule': entry_module, 'entryDefinition': entry}
        (pub / 'spec.json').write_text(json.dumps(spec))
        out = self.last_json(self.sh(label, self.host, self.config, 'objective-publication', pub / 'spec.json',
                                     'activity', pub / 'out'))
        return out['artifactId'], {'artifact': (pub / 'out' / 'artifact.bin').read_bytes().hex(),
                                   'package': (pub / 'out' / 'package.bin').read_bytes().hex()}

    def create(self, label, workspace, name, law, expect, detail=None, pin=None, payer=None, payer_cap=None,
               object_cap=None):
        o = self.objects[name]
        return self.turn(label, workspace, {
            'kind': 'create', 'object': o['object'], 'objectCapability': object_cap or o['capability'],
            'pin': pin or self.PIN, 'law': law, 'upgrade': {'frozen': {}}, 'payer': payer or self.SPONSOR_ACCOUNT,
            'payerCapability': payer_cap or self.SPONSOR_SPEND}, expect, detail)

    def birth(self, label, workspace, name, deposit, expect, detail=None, init=None, decider=None, ticks=TICKS,
              pin=None):
        o = self.objects[name]
        body = {'kind': 'birth', 'object': o['object'], 'objectCapability': o['capability'],
                'account': self.SPONSOR_ACCOUNT, 'accountCapability': self.SPONSOR_SPEND, 'pin': pin or self.PIN,
                'input': record(init=init or variant('set', nat(0)), decider=nat(int(decider or self.SECOND))),
                'envelope': cap(ticks), 'resume': cap(ticks), 'timeout': cap(ticks), 'deposit': str(deposit)}
        return self.turn(label, workspace, body, expect, detail).get('transaction')

    def state(self, name, label, transaction=None):
        """The object's record, declared state and (when a birth is named) the activity's record and purse."""
        o = self.objects[name]['object']
        request = {'objects': [o], 'accounts': [self.SPONSOR_ACCOUNT, self.SECOND, self.COLLECTOR]}
        if transaction:
            request['births'] = [{'object': o, 'transaction': transaction}]
        v = self.view(label, request)
        st = self.cell_of(v, v['objects'][0]['stateCell'])
        v['objectRecord'] = self.cell_of(v, v['objects'][0]['objectCell'])
        v['state'] = st.get('value')
        v['stateKind'] = st.get('kind')
        v['stateVersion'] = st.get('version')
        if transaction:
            rec_cell = v['births'][0]['record']
            rec = self.cell_of(v, rec_cell)
            v['record'] = rec.get('record', {})
            v['recordKind'] = rec.get('kind')
            v['recordCell'] = rec_cell
            v['purse'] = self.balance(self.view(label + '-purse', {'accounts': [rec_cell]}), rec_cell)
        self.totals.append({'after': label, 'height': v.get('height'), 'total': v.get('total')})
        return v

    @staticmethod
    def await_of(v):
        return v['record'].get('phase', {}).get('await', {})

    @staticmethod
    def total_of(v):
        s = v.get('state') or {}
        if s.get('tag') != 'record':
            return None
        total = next((f['value'] for f in s.get('fields', []) if f.get('name') == 'total'), {})
        return int(total.get('value', '-1')) if total.get('tag') == 'natural' else None
