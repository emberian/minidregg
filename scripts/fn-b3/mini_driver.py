from pathlib import Path
import json
import hashlib
import os
import subprocess
import time

base = Path(os.environ['FN_B3_OUTPUT'])
assert base.is_absolute()
base.mkdir(exist_ok=False)
handoff = os.environ['FN_B3_HANDOFF']
mini_host = Path(os.environ['FN_B3_MINI_HOST'])
mini_config = Path(os.environ['FN_B3_MINI_CONFIG'])
mini_transaction = os.environ['FN_B3_MINI_TRANSACTION']
shim = Path(__file__).with_name('fn_bridge.sh')
timings = {}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run(label, argv, expected=0):
    print(label, flush=True)
    started = time.monotonic()
    with (base / (label + '.stdout')).open('wb') as out, (base / (label + '.stderr')).open('wb') as err:
        result = subprocess.run([str(a) for a in argv], stdout=out, stderr=err)
    timings[label] = {'seconds': round(time.monotonic() - started, 3),
                      'exit_code': result.returncode}
    (base / 'timings.json').write_text(json.dumps(timings, sort_keys=True, indent=2) + '\n')
    if result.returncode != expected:
        raise RuntimeError(f'{label} exited {result.returncode}; expected {expected}: ' +
            (base / (label + '.stderr')).read_text(errors='replace')[-500:])

ready_started = time.monotonic()
for _ in range(240):
    if subprocess.run(['ssh', 'hbox', f'test -f {handoff}/ready.json'],
                      stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0:
        break
    time.sleep(1)
else:
    raise RuntimeError('B3 native handoff did not become ready')
timings['wait-ready'] = {'seconds': round(time.monotonic() - ready_started, 3),
                         'exit_code': 0}
run('ready', ['scp', '-q', f'hbox:{handoff}/ready.json', base/'ready.json'])
ready = json.loads((base/'ready.json').read_text())
assert ready['generation'] == 1
for remote, local in [('principal','principal.bin'), ('ed_public','ed-public.bin'),
                      ('ml_public','ml-public.pem'), ('ml_public_raw','ml-public.raw')]:
    run('fetch-'+local, ['scp','-q',f'hbox:{ready[remote]}',base/local])
assert len((base/'principal.bin').read_bytes()) == 32
assert len((base/'ed-public.bin').read_bytes()) == 32
assert len((base/'ml-public.raw').read_bytes()) == 1952

assert ready['image'].startswith('/tank/fn/gates/')
os.environ['FN_B3_IMAGE'] = ready['image']

signer = {
    'principal': (base/'principal.bin').read_bytes().hex(),
    'edPublicKey': (base/'ed-public.bin').read_bytes().hex(),
    'mlPublicKeyHex': (base/'ml-public.raw').read_bytes().hex(),
}
(base/'signer.json').write_text(json.dumps(signer, sort_keys=True) + '\n')
fn_pin = dict(signer, fnBinary=str(shim), mlPublicKey=str(base/'ml-public.pem'))
(base/'fn-pin.json').write_text(json.dumps(fn_pin, sort_keys=True) + '\n')

run('prepare', [mini_host, mini_config, 'consumer-stage-reply-plan',
    base/'signer.json', mini_transaction, base/'prepared-store',
    base/'prepared-candidate.bin', base/'prepared-readback.bin',
    base/'prepared.source', base/'prepared.json'])
prepared_result = json.loads((base/'prepared.json').read_text())
assert prepared_result['stage'] == 'durable-accepted'
assert (base/'prepared-candidate.bin').read_bytes() == (base/'prepared-readback.bin').read_bytes()
assert (base/'prepared.source').read_bytes().count(
    ('Message-ID: ' + prepared_result['messageId'] + '\r\n').encode('ascii')) == 1

run('sign-stage', [mini_host, mini_config, 'consumer-stage-reply-sign',
    base/'fn-pin.json', base/'principal.bin', base/'ed-public.bin',
    ready['ed_secret'], ready['ml_private'], mini_transaction,
    base/'prepared-store', base/'signed-store', base/'plan-readback.bin',
    base/'reply.source', base/'preflight-carrier.eml',
    base/'signed-candidate.bin', base/'signed-readback.bin',
    base/'ed.sig', base/'ml.sig', base/'signed.json'])
signed_result = json.loads((base/'signed.json').read_text())
assert signed_result['stage'] == 'durable-accepted'
assert signed_result['messageId'] == prepared_result['messageId']
assert len(bytes.fromhex(signed_result['sourceIdentity'])) == 48
assert (base/'signed-candidate.bin').read_bytes() == (base/'signed-readback.bin').read_bytes()
assert (base/'prepared.source').read_bytes() == (base/'reply.source').read_bytes()
assert len((base/'ed.sig').read_bytes()) == 64
assert len((base/'ml.sig').read_bytes()) == 3309

# A reopened signed slot must supply the exact tuple without any signer call.
# Deliberately nonexistent private-key paths make accidental re-signing fail.
run('sign-repeat', [mini_host, mini_config, 'consumer-stage-reply-sign',
    base/'fn-pin.json', base/'principal.bin', base/'ed-public.bin',
    '/no-retry-ed-secret', '/no-retry-ml-secret', mini_transaction,
    base/'prepared-store', base/'signed-store', base/'repeat-plan.bin',
    base/'repeat.source', base/'repeat-carrier.eml',
    base/'repeat-signed-candidate.bin', base/'repeat-signed-readback.bin',
    base/'repeat-ed.sig', base/'repeat-ml.sig', base/'repeat-signed.json'])
repeat_result = json.loads((base/'repeat-signed.json').read_text())
assert repeat_result['stage'] == 'durable-accepted'
assert repeat_result['messageId'] == signed_result['messageId']
assert repeat_result['sourceIdentity'] == signed_result['sourceIdentity']
assert not (base/'repeat-carrier.eml').exists()
assert (base/'repeat.source').read_bytes() == (base/'reply.source').read_bytes()
assert (base/'repeat-ed.sig').read_bytes() == (base/'ed.sig').read_bytes()
assert (base/'repeat-ml.sig').read_bytes() == (base/'ml.sig').read_bytes()
assert (base/'repeat-signed-readback.bin').read_bytes() == (base/'signed-readback.bin').read_bytes()

run('fn-author', [shim, '--fn', 'hybrid-author', ready['control'],
    str(ready['generation']), base/'reply.source', base/'ed.sig',
    base/'ml.sig', base/'ml-public.pem'])

message_id = signed_result['messageId']
run('post-source', ['scp', '-q', base/'reply.source', f'hbox:{handoff}/posted.source'])
(base/'mini-finished.json').write_text(json.dumps({
    'message_id': message_id, 'result': 'accepted',
    'mini_transaction': mini_transaction,
    'source_identity': signed_result['sourceIdentity']}, sort_keys=True) + '\n')
run('post-marker-temp', ['scp','-q',base/'mini-finished.json',f'hbox:{handoff}/mini-finished.json.tmp'])
run('post-marker', ['ssh','hbox',f'mv {handoff}/mini-finished.json.tmp {handoff}/mini-finished.json'])
print('B3 POST ACCEPTED', message_id, flush=True)
(base/'evidence.json').write_text(json.dumps({
    'mini_source_revision': os.environ['FN_B3_MINI_REVISION'],
    'mini_binary_sha256': digest(mini_host),
    'fn_image': ready['image'],
    'fn_source_revision': os.environ['FN_B3_FN_REVISION'],
    'prepared_sha256': digest(base/'prepared-readback.bin'),
    'signed_sha256': digest(base/'signed-readback.bin'),
    'preflight_carrier_sha256': digest(base/'preflight-carrier.eml'),
    'source_sha256': digest(base/'reply.source'),
    'ed_signature_sha256': digest(base/'ed.sig'),
    'ml_signature_sha256': digest(base/'ml.sig'),
    'message_id': message_id,
    'source_identity': signed_result['sourceIdentity'],
}, sort_keys=True, indent=2) + '\n')
