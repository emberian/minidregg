#!/usr/bin/env python3
"""Actual source-owned commitment adoption -> existing rotation in a disposable fixture.

Prerequisite: caller supplies an already carried, continuity-protected legacy
workspace whose current key has no next commitment, served by an adoption-capable
Host. This harness neither creates KeyRecords nor modifies a Store directly.
Only Python's standard library and the openssl CLI are used for fixture custody.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import secrets
import socket
import struct
import subprocess

MAX_FRAME = 12_102_760

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixture-root', type=Path, required=True)
    parser.add_argument('--workspace', type=Path, required=True)
    parser.add_argument('--next-key', type=Path, required=True)
    parser.add_argument('--mini', type=Path, required=True)
    args = parser.parse_args()
    os.umask(0o077)
    root = args.fixture_root.resolve(strict=True)
    assert (root / 'KEY-ADOPTION-DISPOSABLE').is_file(), 'create the fixture ownership marker first'
    assert root.stat().st_uid == os.geteuid() and root.stat().st_mode & 0o077 == 0
    def owned(path):
        path = path.resolve(strict=True)
        assert path.is_relative_to(root), f'fixture path is outside disposable root: {path}'
        return path
    workspace = owned(args.workspace)
    next_key = owned(args.next_key)
    mini = args.mini.resolve(strict=True)
    manifest_path = workspace / 'workspace.json'
    manifest = json.loads(manifest_path.read_bytes())
    assert manifest.get('prerotation') in (None, False)
    assert 'nextPublicKey' not in manifest, 'fixture must be a legacy/uncommitted identity'
    assert manifest.get('receiptContinuity') == 'minidregg-continuity-v1'
    assert (workspace / 'receipt-continuity' / 'anchor.json').is_file()
    daily = owned(Path(manifest['key']))
    config = owned(Path(manifest['config']))
    address = manifest['socket']
    assert not address.startswith('ssh:'), 'native fixture harness currently uses a private Unix socket'
    endpoint = owned(Path(address))
    assert manifest['host'] is not None, 'harness needs the actual local Host image digest'
    host = Path(manifest['host']).resolve(strict=True)
    evidence = root / 'key-adoption-evidence'
    evidence.mkdir(mode=0o700)  # new evidence only; never overwrite another run
    rows = []
    def save(name, body):
        target = evidence / name
        with target.open('xb') as output:
            output.write(body)
            output.flush()
            os.fsync(output.fileno())
    def save_json(name, value):
        save(name, (json.dumps(value, indent=2) + '\n').encode())
    def passed(name):
        rows.append({'check': name, 'status': 'PASS'})
        print(f'PASS {name}', flush=True)
        with (evidence / 'rows.json').open('w') as output:
            json.dump(rows, output, indent=2)
            output.flush()
            os.fsync(output.fileno())
    def cli(name, *arguments, success=True):
        result = subprocess.run([str(mini), *map(str, arguments)], capture_output=True)
        save(name + '.stdout', result.stdout)
        save(name + '.stderr', result.stderr)
        assert (result.returncode == 0) == success, (name, result.returncode, result.stderr.decode(errors='replace'))
        return json.loads(result.stdout) if success else None
    def exact_read(stream, length):
        chunks = bytearray()
        while len(chunks) < length:
            part = stream.recv(length-len(chunks))
            assert part, 'native fixture returned an incomplete frame'
            chunks.extend(part)
        return bytes(chunks)
    config_bytes = config.read_bytes()
    host_digest = hashlib.sha256(host.read_bytes()).digest()
    def call(name, opcode, payload):
        frame = b'\x02' + struct.pack('<I', len(config_bytes)) + config_bytes + host_digest + bytes([opcode]) + payload
        assert len(payload) < MAX_FRAME
        with socket.socket(socket.AF_UNIX) as stream:
            stream.settimeout(120)
            stream.connect(str(endpoint))
            stream.sendall(struct.pack('<I', len(frame)) + frame)
            length = struct.unpack('<I', exact_read(stream,4))[0]
            assert 0 < length <= MAX_FRAME
            reply = exact_read(stream,length)
        save(name + '.request', bytes([opcode]) + payload)
        save(name + '.frame', reply)
        return reply
    def accepted_body(frame, opcode):
        assert frame[0] == opcode and len(frame)>1, (opcode, frame[:80])
        return frame[1:]
    def inspect(name, kind, body):
        encoded = kind.encode()
        frame = call(name,8,struct.pack('<H',len(encoded))+encoded+body)
        value = json.loads(accepted_body(frame,8))
        save_json(name+'.json',value)
        return value
    def pair(left,right):
        return struct.pack('<I',len(left))+left+right
    def sign(name,key_path,header):
        # Standard Ed25519 PKCS#8 wrapper, used only by this fixture signer.
        seed=key_path.read_bytes()
        assert len(seed)==32
        temporary=evidence/(name+'.private-der')
        temporary.write_bytes(bytes.fromhex('302e020100300506032b657004220420')+seed)
        message=evidence/(name+'.header')
        message.write_bytes(header)
        try:
            result=subprocess.run(['openssl','pkeyutl','-sign','-rawin','-inkey',str(temporary),'-in',str(message)],capture_output=True,check=True)
        finally:
            temporary.unlink()  # only this harness's transient private wrapper
        assert len(result.stdout)==64
        save(name+'.sig',result.stdout)
        return result.stdout
    def refused(name,frame,opcode):
        assert frame[0] in (255,opcode), (name,frame[:80])
        view=inspect(name+'-outcome','outcome',frame[1:])
        assert view['type'] != 'confirmed', (name,view)
        passed(name)
    save_json('provenance.json', {'mini':str(mini),'miniSha256':hashlib.sha256(mini.read_bytes()).hexdigest(),
        'host':str(host),'hostSha256':host_digest.hex(),'workspace':str(workspace),
        'configSha256':hashlib.sha256(config_bytes).hexdigest(),
        'scope':'actual native source; prerequisite legacy carried workspace supplied by caller'})
    save('workspace-before.json',manifest_path.read_bytes())
    daily_before=daily.read_bytes()
    next_before=next_key.read_bytes()
    status=cli('initial-status','key-status','--workspace',workspace)
    assert status['isCurrent'] and not status['currentRevoked'] and not status['prerotated']
    attempt='adoption-journey'
    cli('prepare','adopt-next-key','--workspace',workspace,'--next-key',next_key,'--attempt',attempt,'--action','prepare')
    custody=workspace/'attempts'/attempt
    pin=json.loads((custody/'attempt.json').read_bytes())
    plan=json.loads((custody/'plan.json').read_bytes())
    plan_bytes=(custody/'plan.bin').read_bytes()
    original=(custody/'ingress.bin').read_bytes()
    current_signature=(custody/'current.sig').read_bytes()
    next_signature=(custody/'next.sig').read_bytes()
    assert plan['command']['expectedCurrent']['nextKeyDigest'] is None
    assert manifest_path.read_bytes()==(evidence/'workspace-before.json').read_bytes()
    passed('prepare-preserves-legacy-workspace-and-current-key')
    alternate=evidence/'alternate.key'
    # keygen prints human text; retain it without trying to decode JSON.
    result=subprocess.run([str(mini),'keygen','--secret',str(alternate),'--public',str(evidence/'alternate.pub'),'--no-prerotation'],capture_output=True)
    save('alternate-key.stdout',result.stdout);save('alternate-key.stderr',result.stderr)
    assert result.returncode==0,result.stderr
    alternate_public=(evidence/'alternate.pub').read_bytes().hex()
    wrong=dict(pin['request'], currentPublicKey=alternate_public)
    frame=call('wrong-current-request',187,json.dumps(wrong).encode())
    assert frame[0]==255,frame[:80]
    passed('wrong-current-request-refused')
    stale_request=dict(pin['request'],nonce=str(secrets.randbits(128)),nextPublicKey=alternate_public)
    stale_plan=accepted_body(call('stale-plan',187,json.dumps(stale_request).encode()),187)
    stale_view=inspect('stale-plan-inspection','subject-key-adoption-plan',stale_plan)
    stale_current=sign('stale-current',daily,bytes.fromhex(stale_view['currentAuthorizationHeader']))
    stale_next=sign('stale-next',alternate,bytes.fromhex(stale_view['nextPossessionHeader']))
    stale_ingress=accepted_body(call('stale-assembly',188,pair(stale_plan,pair(stale_current,stale_next))),188)
    # Actual distinct-key signatures, rather than edited Lean command bytes.
    wrong_current=sign('wrong-current-signature',alternate,bytes.fromhex(plan['currentAuthorizationHeader']))
    wrong_next=sign('wrong-next-possession',alternate,bytes.fromhex(plan['nextPossessionHeader']))
    for name,first,second in [('wrong-current-signature',wrong_current,next_signature),('wrong-next-possession',current_signature,wrong_next)]:
        frame=call(name+'-assembly',188,pair(plan_bytes,pair(first,second)))
        if frame[0]==255:
            refused(name,frame,188)
        else:
            refused(name,call(name+'-submit',189,accepted_body(frame,188)),189)
    missing=call('missing-next-possession',188,pair(plan_bytes,pair(current_signature,b'')))
    assert missing[0] in (254,255),missing[:80]
    passed('missing-next-possession-refused')
    cli('wrong-next-cli','adopt-next-key','--workspace',workspace,'--attempt',attempt,'--next-key',alternate,success=False)
    assert (custody/'ingress.bin').read_bytes()==original
    passed('conflicting-next-cannot-replace-sealed-attempt')
    adopted=cli('adopt','adopt-next-key','--workspace',workspace,'--attempt',attempt)
    after=json.loads(manifest_path.read_bytes())
    assert after['prerotation'] and after['nextPublicKey']==pin['request']['nextPublicKey']
    for name,value in manifest.items():
        if name not in ('prerotation','nextPublicKey'): assert after[name]==value,name
    assert daily.read_bytes()==daily_before and next_key.read_bytes()==next_before
    assert adopted['keyEpoch']==status['keyEpoch'] and adopted['keyId']==status['keyId']
    passed('adoption-changes-only-next-commitment')
    refused('independently-signed-stale-plan',call('stale-submit',189,stale_ingress),189)
    # Completed exact lookup needs neither original signing secret.
    moved_daily=daily.with_name(daily.name+'.journey-held')
    moved_next=next_key.with_name(next_key.name+'.journey-held')
    assert not moved_daily.exists() and not moved_next.exists()
    daily.rename(moved_daily);next_key.rename(moved_next)
    try:
        cli('no-secrets-lookup','adopt-next-key','--workspace',workspace,'--attempt',attempt,'--action','lookup')
    finally:
        moved_daily.rename(daily);moved_next.rename(next_key)
    passed('exact-lookup-without-signing-secrets')
    rotated=cli('rotate','rotate-key','--workspace',workspace,'--next-key',next_key)
    assert rotated['keyEpoch']==str(int(status['keyEpoch'])+1)
    assert rotated['publicKey']==pin['request']['nextPublicKey']
    rotation_manifest=manifest_path.read_bytes()
    rotated_key=daily.read_bytes()
    key_status=cli('rotated-status','key-status','--workspace',workspace)
    assert key_status['isCurrent'] and key_status['prerotated'] and key_status['nextKeyMatchesCommitment']
    passed('existing-rotation-uses-adopted-commitment')
    replay=cli('post-rotation-adoption-lookup','adopt-next-key','--workspace',workspace,'--attempt',attempt,'--action','lookup')
    assert replay==adopted
    assert manifest_path.read_bytes()==rotation_manifest and daily.read_bytes()==rotated_key
    assert (custody/'ingress.bin').read_bytes()==original
    passed('old-adoption-replay-does-not-reset-new-commitment')
    save_json('result.json',{'status':'PASS','checks':len(rows),'rows':rows,'adoption':adopted,'rotation':rotated,
        'pending':'cross-domain native fixture is not claimed by this journey'})
    print(evidence,flush=True)

if __name__=='__main__':
    main()
