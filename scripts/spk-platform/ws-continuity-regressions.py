#!/usr/bin/env python3
"""Real isolated Mini replay and interrupted-seal adapters; never retries a write."""
import argparse
import concurrent.futures
import hashlib
import http.client
import re
import secrets
import importlib.util
import json
import os
from pathlib import Path
import socket
import stat
import struct
import sys
import time

spec = importlib.util.spec_from_file_location("continuity_fixture", Path(__file__).with_name("ws-continuity-fixture.py"))
fixture = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fixture)
load, save, sha, require = fixture.load, fixture.save, fixture.sha, fixture.require
MAX_FRAME = 12_102_760
PERMIT = b"DREGG/APPLICATION/DISPATCH-COMMITTED-PERMIT/v1"


def private_exchange(path, config, host_hash, opcode, payload, evidence, timeout=120):
    """One actual pinned private-v2 Mini call; raw frames retained, no resend."""
    info = path.lstat()
    require(stat.S_ISSOCK(info.st_mode) and info.st_uid == os.getuid() and not info.st_mode & 0o077,
            "operator socket must be private and owned by this operator")
    fixture.protected_parent(path.parent)
    require(0 < len(config) <= 65536 and 0 < len(payload) < MAX_FRAME, "private request size refused")
    body = b'\x02' + struct.pack('<I',len(config)) + config + bytes.fromhex(host_hash) + bytes([opcode]) + payload
    require(len(body) <= MAX_FRAME and len(bytes.fromhex(host_hash)) == 32, "private envelope invalid")
    frame = struct.pack('<I',len(body)) + body
    with open(evidence/'request-frame.bin','xb') as out:
        out.write(frame)
    deadline = time.monotonic()+timeout
    def remaining(sock):
        seconds = deadline-time.monotonic()
        require(seconds > 0, "uncertain private call deadline; no automatic retry")
        sock.settimeout(seconds)
    def exact(sock, count):
        parts = bytearray()
        while len(parts) < count:
            remaining(sock)
            part = sock.recv(count-len(parts))
            require(part, "uncertain private response EOF; no automatic retry")
            parts.extend(part)
        return bytes(parts)
    with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as sock:
        remaining(sock)
        sock.connect(str(path))
        require(hasattr(socket,'SO_PEERCRED'), "Linux peer credentials required")
        _,uid,_ = struct.unpack('3i',sock.getsockopt(socket.SOL_SOCKET,socket.SO_PEERCRED,12))
        require(uid == os.getuid(), "operator peer UID differs")
        remaining(sock)
        sock.sendall(frame)
        prefix = exact(sock,4)
        size = struct.unpack('<I',prefix)[0]
        require(2 <= size <= MAX_FRAME, "private response size refused")
        reply = exact(sock,size)
    with open(evidence/'response-frame.bin','xb') as out:
        out.write(prefix+reply)
    return reply[0],reply[1:]


def equal_no_write(before, after):
    for key in ('storeHeight','worldRoot','dispatchCount','payerBalances'):
        require(before[key] == after[key], 'replay changed '+key)


def checked_historical(outcome, receipt, confirmations=("replayed",)):
    require(outcome.get('type') == 'confirmed' and outcome.get('confirmation') in confirmations,
            'exact replay did not return historical confirmation')
    require(all(outcome.get(k) == receipt[k] for k in ('transactionId','eventId','acceptedCount','worldRoot')),
            'historical reply differs from original receipt')


def select_delivered(candidates, journal, app, generation):
    tombstones = [(p,load(p)) for p in journal.glob('dispatch-op-*.json')]
    eligible, observations = [], []
    for path in sorted(candidates,key=lambda p:int(p.parent.name.removeprefix('dispatch-op-'))):
        data = load(path)
        operation = data['request']['operationId']
        matched = [(p,v) for p,v in tombstones if v.get('identity',{}).get('operation_id') == operation]
        require(len(matched) == 1, 'ambiguous or absent A physical journal')
        physical,value = matched[0]
        identity = value['identity']
        require(identity.get('dispatch_transaction') == data['receipt']['transactionId']
                and identity.get('dispatch_event') == data['receipt']['eventId']
                and identity.get('app') == int(app) and identity.get('app_generation') == int(generation),
                'A physical journal receipt or generation differs')
        phase = value.get('phase')
        require(phase in ('delivered','deliveryRequested','uncertain'), 'unknown A physical journal state')
        observations.append({'inspection':str(path),'deliveryJournal':str(physical),'phase':phase})
        if phase == 'delivered':
            eligible.append((path,physical))
    require(eligible, 'no delivered A ingress retained')
    return *eligible[0],observations


class Regressions:
    def __init__(self, path):
        self.f = fixture.Fixture(path)

    def snapshot(self):
        return fixture.Fixture(self.f.path).snapshot()

    def journal(self):
        return self.f.state / f"apps/{self.f.app}/g{self.f.f['generation']}"

    def result(self, action, **fields):
        path = self.f.opdir/'checked-action.json'
        value = dict(schema='spk-ws-continuity-action-v1',action=action,confirmed=True,artifact=str(path),**fields)
        save(path,value)
        return value

    def replay(self):
        f = self.f
        d = f.f['delegates']['a']
        require(d.get('revoked') is True, 'exact A replay requires owner-revoked A ticket')
        before = self.snapshot()
        candidates = []
        for path in self.journal().glob('dispatch-op-*/inspection.json'):
            data = load(path)
            if (data.get('session',{}).get('subject') == d['subject'] and
                data.get('session',{}).get('resource') == d['session'] and
                data.get('ticketResource') == d['ticket'] and
                data.get('app',{}).get('resource') == f.app):
                require(data['app'].get('generation') == f.f['generation'], 'accepted A candidate belongs to another generation')
                operation = data.get('request',{}).get('operationId','')
                require(isinstance(operation,str) and re.fullmatch('[1-9][0-9]*',operation) is not None
                        and path.parent.name == 'dispatch-op-'+operation, 'ambiguous A dispatch journal operation')
                candidates.append(path)
        require(candidates, 'no original accepted A dispatch retained')
        selected,physical,observations = select_delivered(candidates,self.journal(),f.app,f.f['generation'])
        attempt = selected.parent
        original = f.fresh('original-dispatch-inspected.json')
        f.run([f.m['host']['path'],f.config,'inspect','application-dispatch-committed',attempt/'committed-payload.bin',original])
        inspected = load(original)
        require(inspected == load(selected), 'retained dispatch differs from source decoder')
        save(f.opdir/'replay-selection.json',{'inspection':str(selected),'candidates':observations,
                                           'deliveryJournal':str(physical),'receipt':inspected['receipt']})
        ingress = (attempt/'ingress.bin').read_bytes()
        evidence = f.fresh('exact-replay')
        evidence.mkdir(mode=0o700)
        code,payload = private_exchange(f.osock,f.config.read_bytes(),f.m['host']['sha256'],34,ingress,evidence)
        require(code == 34 and not payload.startswith(PERMIT), 'replay minted a permit or returned nonhistorical opcode')
        raw = evidence/'outcome.bin'
        with open(raw,'xb') as out:
            out.write(payload)
        decoded = evidence/'outcome.json'
        f.run([f.m['host']['path'],f.config,'inspect','outcome',raw,decoded])
        checked_historical(load(decoded),inspected['receipt'])
        after = self.snapshot()
        equal_no_write(before,after)
        return self.result('replayAcceptedA',originalInspection=str(original),replayOutcome=str(decoded),
            originalIngressSha256=sha(attempt/'ingress.bin'),historicalReceiptOnly=True,
            physicalDelivery='No permit returned or forwarded; resident dispatch journal unchanged. Independent application delivery census unavailable.',
            before=before,after=after)

    def race(self):
        f = self.f
        require(f.f.get('enableSameIngressRace') is True and
                'integration-qualification' in load(f.root/'manifest.json').get('spkHostFeatures',[]),
                'race needs explicitly pinned integration-qualification resident')
        journal = self.journal()
        for name in ('trigger','claimed','ready','result'):
            require(not (journal/('dispatch-race-'+name+'.json')).exists(), 'race is already armed or attempted')
        before = self.snapshot()
        counter = journal/'dispatch-next-id'
        info = counter.lstat()
        require(stat.S_ISREG(info.st_mode) and info.st_uid == os.getuid() and stat.S_IMODE(info.st_mode) == 0o600
                and info.st_nlink == 1, 'next dispatch counter identity differs')
        operation = counter.read_text()
        require(re.fullmatch(r'[1-9][0-9]*\n',operation) is not None, 'next dispatch counter is not canonical')
        operation = operation[:-1]
        d = f.f['delegates']['b']
        require(not d.get('revoked',False), 'race B must remain authorized')
        room = os.environ.get('SPK_CONTINUITY_ROOM','')
        require(re.fullmatch(r'[A-Za-z0-9_-]{8,}',room) is not None, 'traffic harness unique sheet required')
        target = '/'+room
        nonce = secrets.token_hex(32)
        trigger = dict(protocol='mini-spk-dispatch-race-trigger-v1',nonceHex=nonce,app=f.app,
            session=d['session'],subject=d['subject'],ticketResource=d['ticket'],sessionKind='web',
            operationId=operation,method='GET',pathAndQuery=target,signedApiPath=None)
        save(journal/'dispatch-race-trigger.json',trigger)
        endpoint = d['endpoint']
        token = Path(endpoint['token']).read_text().strip()
        require(token and all(32 < ord(c) < 127 and c != ';' for c in token), 'unsafe browser token')
        host=endpoint['host']
        require(re.fullmatch(r'[A-Za-z0-9.-]+(?::[0-9]{1,5})?',host) is not None, 'fixture browser Host unsafe')
        def request():
            with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as sock:
                sock.settimeout(150)
                sock.connect(endpoint['unix_socket'])
                text = (f'GET {target} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\n'
                        'Sec-Fetch-Site: same-origin\r\nSec-Fetch-Mode: navigate\r\nSec-Fetch-Dest: document\r\n'
                        f'Origin: https://{host}\r\nCookie: __Host-mini_spk_session={token}\r\n\r\n')
                sock.sendall(text.encode())
                response = http.client.HTTPResponse(sock)
                response.begin()
                body = response.read(16*1024*1024+1)
                require(len(body) <= 16*1024*1024, 'race HTTP body too large')
                with open(f.opdir/'race-http-body.bin','xb') as out:
                    out.write(body)
                # No credentials/headers in the output artifact.
                result = dict(status=response.status,bodySha256=hashlib.sha256(body).hexdigest(),bodyBytes=len(body))
                save(f.opdir/'race-http-response.json',result)
                return result
        def wait_json(path, seconds=60):
            deadline = time.monotonic()+seconds
            while True:
                try:
                    require(not path.is_symlink(), 'race evidence cannot be a symlink')
                    return load(path)
                except (FileNotFoundError,json.JSONDecodeError):
                    require(time.monotonic() < deadline, 'race evidence did not complete; no automatic retry')
                    time.sleep(.02)
        with concurrent.futures.ThreadPoolExecutor(max_workers=1) as pool:
            pending_http = pool.submit(request)
            ready = wait_json(journal/'dispatch-race-ready.json')
            attempt = journal/('dispatch-op-'+operation)
            require(ready.get('protocol') == 'mini-spk-dispatch-race-ready-v1' and ready.get('nonceHex') == nonce
                    and ready.get('operationId') == operation and ready.get('attemptDirectory') == str(attempt)
                    and ready.get('ingressSha256') == sha(attempt/'ingress.bin') and ready.get('opcode') in (34,164),
                    'ready barrier differs from source-authored ingress')
            require(re.fullmatch('[0-9a-f]{64}',ready.get('submissionSha256','')) is not None, 'invalid submission hash')
            save(attempt/'race-go.json',dict(protocol='mini-spk-dispatch-race-go-v1',nonceHex=nonce,
                                          submissionSha256=ready['submissionSha256']))
            http_result = pending_http.result(timeout=160)
        require(http_result['status'] == 200 and http_result['bodyBytes'] > 0, 'race did not return app page')
        result_path = journal/'dispatch-race-result.json'
        result = wait_json(result_path)
        require(result.get('protocol') == 'mini-spk-dispatch-race-result-v1' and result.get('nonceHex') == nonce
                and result.get('operationId') == operation and result.get('attemptDirectory') == str(attempt)
                and result.get('result',{}).get('status') == 'winner-forwarded-to-resident', 'race did not select one fresh winner')
        selected = result['result']['selection']
        require(selected.get('protocol') == 'mini-spk-dispatch-race-selection-v1' and selected.get('operationId') == operation
                and selected.get('nonceHex') == nonce and type(selected.get('winnerIndex')) is int
                and type(selected.get('historicalIndex')) is int and {selected['winnerIndex'],selected['historicalIndex']} == {0,1},
                'race selection identity differs')
        inspection_path = f.fresh('race-dispatch-inspected.json')
        f.run([f.m['host']['path'],f.config,'inspect','application-dispatch-committed',attempt/'committed-payload.bin',inspection_path])
        inspection = load(inspection_path)
        checked_historical(selected['receipt'],inspection['receipt'],('installed','replayed','recoveredAfterUncertainResponse'))
        require(inspection['request']['operationId'] == operation and inspection['session']['subject'] == d['subject']
                and inspection['session']['resource'] == d['session'] and inspection['ticketResource'] == d['ticket'],
                'delivered dispatch identity differs')
        delivery = wait_json(attempt/'race-delivery-result.json')
        require(delivery.get('status') == 'app-response-received' and delivery.get('physicalDeliveries') == 1,
                'race physical delivery was not acknowledged')
        tombstones = [(p,load(p)) for p in journal.glob('dispatch-op-*.json')]
        matching = [(p,v) for p,v in tombstones if v.get('identity',{}).get('operation_id') == operation]
        require(len(matching) == 1 and matching[0][1].get('phase') == 'delivered', 'normal physical delivery journal missing or ambiguous')
        identity = matching[0][1]['identity']
        require(identity.get('dispatch_transaction') == inspection['receipt']['transactionId']
                and identity.get('dispatch_event') == inspection['receipt']['eventId']
                and identity.get('app') == int(f.app) and identity.get('app_generation') == int(f.f['generation']),
                'physical journal receipt differs from source receipt')
        after = self.snapshot()
        require(after['storeHeight'] == before['storeHeight']+1 and after['dispatchCount'] == before['dispatchCount']+1,
                'same-ingress race committed or delivered more than one new record')
        return self.result('sameIngressRace',sourceRaceResult=str(result_path),deliveryEvidence=str(attempt/'race-delivery-result.json'),
            normalDeliveryJournal=str(matching[0][0]),sourceInspection=str(inspection_path),httpResponse=str(f.opdir/'race-http-response.json'),
            oneAcceptedRecord=True,onePhysicalDelivery=True,before=before,after=after,
            billingEvidence='One authenticated Store record, exact receipt-only loser; independent classified billing-event counter remains unavailable.')

    def unit_properties(self, unit):
        require(isinstance(unit,str) and unit.endswith('.service') and '/' not in unit, 'invalid exact resident unit')
        _,out,_ = self.f.run(['systemctl','show',unit,'--property=OnFailure,Restart,ActiveState,ExecStart'])
        return dict(line.split('=',1) for line in out.read_text().splitlines() if '=' in line),str(out)

    def seal_recovery(self):
        f = self.f
        setup = f.f.get('sealSupervisor')
        if setup is None:
            return self.seal_recovery_body()
        require(set(setup) == {'brokerConfig','brokerConfigSha256'}, 'supervisor setup pins required')
        resident = self.journal()/'resident.json'
        config = load(resident)
        args = ['--fixture',str(f.path),'--expected-app',f.app,'--expected-unit',config['unit'],
                '--expected-resident-sha256',sha(resident),'--broker-config',setup['brokerConfig'],
                '--broker-config-sha256',setup['brokerConfigSha256']]
        helper = Path(__file__).with_name('ws-continuity-supervision.py')
        save(f.opdir/'root-supervisor-request.json',{'protocol':'mini-spk-fixture-supervisor-request-v1','arguments':args})
        command = ['/usr/bin/sudo','-n','/usr/bin/python3',str(helper)]
        failure = None
        try:
            f.run([*command,'install',*args])
            return self.seal_recovery_body()
        except BaseException as error:
            failure = error
            raise
        finally:
            # Only our exact root-recorded drop-in is removed. Retain command
            # evidence if the root helper cannot restore it.
            try:
                f.run([*command,'restore',*args])
            except Exception as cleanup_error:
                if failure is None:
                    raise
                save(f.opdir/'supervisor-restore-error.json',{'originalError':str(failure),'restoreError':str(cleanup_error)})

    def seal_recovery_body(self):
        f = self.f
        require(f.f.get('enableSealRecovery') is True, 'seal failure injection was not enabled for this fresh fixture')
        old = f.f['generation']
        journal = self.journal()
        resident = journal/'resident.json'
        config = load(resident)
        require(config['journalDir'] == str(journal), 'resident configuration names another generation')
        props,properties = self.unit_properties(config['unit'])
        require(props.get('OnFailure') == '' and props.get('Restart') == 'no' and props.get('ActiveState') == 'active',
                'root must prearrange isolated resident OnFailure empty, Restart=no, active; adapter never changes unit supervision')
        d = f.f['delegates']['b']
        require(not d.get('revoked',False), 'B must remain authorized')
        request_path = f.registration_request(d)
        request = load(request_path)
        seal_dir = journal/'route-seals'
        fixture.protected_parent(seal_dir)
        retained = {}
        for prior in seal_dir.iterdir():
            require(prior.is_file() and not prior.is_symlink() and not prior.name.startswith('.pending-'),
                    'preexisting interrupted/unknown seal prevents deterministic injection')
            record = load(prior)
            require(record.get('protocol') == 'mini-spk-resident-route-seal-v1' and
                    record.get('reply',{}).get('session') != d['session'], 'B route already sealed or unknown retained record')
            retained[str(prior)] = sha(prior)
        final = seal_dir/(request['registrationNonceHex']+'.json')
        pending = seal_dir/('.pending-'+request['registrationNonceHex']+'.json')
        require(not final.exists() and not final.is_symlink() and not pending.exists() and not pending.is_symlink(), 'selected seal path already exists')
        # This is a diagnostic fault, not fabricated authority. create_new preserves all custody.
        save(final,{'protocol':'mini-spk-test-seal-collision-v1','request':str(request_path),'fixture':str(f.path)})
        with open(final,'rb') as fd:
            os.fsync(fd.fileno())
        directory_fd = os.open(seal_dir,os.O_RDONLY|os.O_DIRECTORY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
        collider_hash = sha(final)
        rc,_,error = f.run([f.m['spkHost']['path'],'grain','register-route','--socket',journal/'route-control.sock','--request',request_path],okay=False)
        require(rc != 0, 'collision unexpectedly registered route')
        require(pending.is_file() and not pending.is_symlink(), 'native publisher did not leave interrupted seal evidence')
        seal = load(pending)
        require(seal.get('protocol') == 'mini-spk-resident-route-seal-v1' and seal.get('request') == request,
                'pending seal does not retain exact native request')
        fixture.check_registration(seal['reply'],request,d)
        binding = seal['binding']
        require(all(binding[k] == seal['reply'][k] for k in ('app','appGeneration','session','sessionGeneration','subject','ticketResource','sessionFingerprintHex')),
                'pending seal binding differs from admitted reply')
        pending_hash = sha(pending)
        deadline = time.monotonic()+30
        while True:
            current,_ = self.unit_properties(config['unit'])
            if current.get('ActiveState') not in ('active','activating','deactivating'):
                break
            require(time.monotonic() < deadline, 'resident remained alive after publication failure')
            time.sleep(.2)
        # Preserve the exact invocation/config, including the original systemd command evidence.
        argv = [f.m['spkHost']['path'],'resident-run',str(resident)]
        env_fields = {'MINI_SPK_APP_UID':str(config['appUid']),'MINI_SPK_APP_GID':str(config['appGid']),
                      'MINI_SPK_GRAINS_ROOT':config['grainsRoot'],'MINI_SPK_STORE':config['store']}
        save(f.opdir/'same-generation-invocation.json',{'argv':argv,'environment':env_fields,'residentConfigSha256':sha(resident),'originalSystemdProperties':properties})
        before = self.snapshot()
        rc,_,stderr = f.run(argv,okay=False,env=dict(os.environ,**env_fields),timeout=15)
        require(rc != 0 and 'retained route seal requires lifecycle STOP and a new generation' in stderr.read_text(),
                'same-generation startup did not fail at retained-seal guard')
        after = self.snapshot()
        equal_no_write(before,after)
        for endpoint in (v['endpoint'] for v in f.f['delegates'].values()):
            with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as sock:
                sock.settimeout(.5)
                try:
                    sock.connect(endpoint['unix_socket'])
                except (FileNotFoundError,ConnectionRefusedError):
                    pass
                else:
                    raise RuntimeError('same-generation listener remained connectable')
        f.run([f.m['spkHost']['path'],'grain','stop',f.profile,f.app])
        stopped = f.query(8,f.app,f.appcap)
        require(fixture.entries(stopped['view'])['1'] == '2', 'recovery STOP did not reach source phase2')
        f.run([f.m['spkHost']['path'],'grain','start',f.profile,f.app])
        started = f.query(8,f.app,f.appcap)
        fields = fixture.entries(started['view'])
        require(fields['1'] == '4' and int(fields['0']) > int(old), 'recovery did not start newer source generation')
        f.f['generation'] = fields['0']
        for delegate in f.f['delegates'].values():
            if not delegate.get('revoked',False):
                f.close_session(delegate)
                f.enroll(delegate)
        f.write_state()
        require(sha(final) == collider_hash and sha(pending) == pending_hash and all(sha(p)==h for p,h in retained.items()), 'old interrupted evidence changed during lifecycle recovery')
        return self.result('sealRecovery',oldGeneration=old,newGeneration=f.f['generation'],
            endpoint=d['endpoint'],sameGenerationRefused=True,pendingSeal=str(pending),collisionDiagnostic=str(final),
            refusal=str(stderr),registrationFailure=str(error),after=self.snapshot(),
            applicationData='Traffic harness must reopen B and independently check persisted sentinel.')

    def run(self, action):
        f = self.f
        marker = f.root/('action-'+action+'-started.json')
        save(marker,{'action':action,'evidence':str(f.opdir)})
        return {'replayAcceptedA':self.replay,'sealRecovery':self.seal_recovery,'sameIngressRace':self.race}[action]()


def main():
    os.umask(0o077)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action',choices=['replayAcceptedA','sealRecovery','sameIngressRace'])
    parser.add_argument('fixture')
    args = parser.parse_args()
    print(json.dumps(Regressions(args.fixture).run(args.action)))


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print('continuity regression: '+str(error),file=sys.stderr)
        raise SystemExit(1)
