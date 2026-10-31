#!/usr/bin/env python3
"""Run the same declared operations that emit Hermes schemas, on a member grain route.

Only a qualification driver; never install in the Hermes sandbox or operator daemon.
No HTML, app-specific executable branches, direct database access, or shell recipes.
"""
import argparse
import base64
import http.client
import http.cookiejar
import urllib.request
from http.cookies import SimpleCookie
import json
import os
from pathlib import Path
import socket
import sys
import time
import uuid

from binding import Engine, Refusal, Uncertain, digest, load, resolve, require_write_readback, run_scenario, tools
from ddp import DDP


class UnixHTTP(http.client.HTTPConnection):
    def __init__(self, route, seconds):
        super().__init__('grain.test', timeout=seconds)
        self.route = route

    def connect(self):
        self.sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.sock.settimeout(self.timeout)
        self.sock.connect(str(self.route / 'http.sock'))


class MemberCookiePolicy(http.cookiejar.DefaultCookiePolicy):
    def set_ok(self, cookie, request):
        return (cookie.name != '__Host-mini_spk_session' and
                cookie.domain.lstrip('.') == 'grain.test' and super().set_ok(cookie, request))


class Route:
    def __init__(self, route, d, journal):
        self.route, self.d, self.journal = route, d, journal
        self.cookies = http.cookiejar.CookieJar(MemberCookiePolicy())
        self.retain_app_cookies = d.get('auth', {}).get('appCookies', 'omit') == 'retain'
        self.cookie = (route / 'browser.token').read_text().strip()
        if not self.cookie or any(ord(c) < 33 or ord(c) > 126 or c in ';,' for c in self.cookie):
            raise Refusal('route-token-invalid')

    def retain(self, request):
        # Private diagnostics exclude credentials/prepared bodies; NOT a Mini permit journal.
        self.journal.write(json.dumps(request, separators=(',', ':')) + '\n')
        self.journal.flush()

    def cookie_values(self, path=''):
        if not self.retain_app_cookies:
            return {}
        request = urllib.request.Request('https://grain.test/' + path.lstrip('/'))
        self.cookies.add_cookie_header(request)
        parsed = SimpleCookie()
        parsed.load(request.get_header('Cookie', ''))
        return {name: morsel.value for name, morsel in parsed.items()}

    def http(self, request):
        body = request['body']
        secret = request.get('redact', False) or request['path'] in {
            self.d.get('auth', {}).get(key, '').lstrip('/') for key in ('postPath', 'credentialsPath')}
        if not secret:
            self.retain({'http': {**request, 'body': base64.b64encode(body).decode()}})
        path = '/' + request['path'] + ('?' + request['query'] if request['query'] else '')
        cookie_request = urllib.request.Request('https://grain.test' + path)
        if self.retain_app_cookies:
            self.cookies.add_cookie_header(cookie_request)
        app_cookie = cookie_request.get_header('Cookie', '')
        headers = {**request['headers'], 'Cookie': '__Host-mini_spk_session=' + self.cookie +
                   ('; ' + app_cookie if app_cookie else ''), 'Origin': 'https://grain.test'}
        conn = UnixHTTP(self.route, self.d['limits']['seconds'])
        try:
            try:
                conn.request(request['method'], path, body=body, headers=headers)
                response = conn.getresponse()
                data = response.read(self.d['limits']['replyBytes'] + 1)
            except http.client.HTTPException as e:
                # The request may already have reached the grain. Engine decides
                # read failure versus an uncertain write; it must not retry.
                raise EOFError('invalid HTTP response') from e
            if len(data) > self.d['limits']['replyBytes']:
                raise Refusal('reply-over-bound')
            if self.retain_app_cookies:
                self.cookies.extract_cookies(response, cookie_request)
            if not secret:
                self.retain({'response': {'status': response.status,
                             'contentType': response.getheader('content-type', ''),
                             'bodyBase64': base64.b64encode(data).decode()}})
            return response.status, dict((k.lower(), v) for k, v in response.getheaders()), data
        finally:
            conn.close()

    def ddp(self, binding, args, context, write=False):
        import websocket
        auth = self.d['auth']
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.settimeout(self.d['limits']['seconds'])
        s.connect(str(self.route / 'http.sock'))
        ws = None
        mutation = False
        try:
            # Library verifies Sec-WebSocket-Accept, masking, control frames and fragmentation.
            ws = websocket.create_connection('ws://grain.test' + auth['websocket'], socket=s,
                    origin='https://grain.test', cookie='__Host-mini_spk_session=' + self.cookie,
                    timeout=self.d['limits']['seconds'])
            ddp = DDP(ws, self.d['limits']['snapshotDocuments'], self.d['limits']['seconds'], diagnostic=self.retain)
            ddp.connect()
            uid = ddp.authenticate(auth, self.http)
            local = {**context, 'userId': uid, 'nowMs': int(time.time() * 1000), 'operationId': uuid.uuid4().hex}
            if binding['kind'] == 'snapshot':
                return ddp.snapshot(binding, args, local)
            params = resolve(binding['params'], args, local)
            self.retain({'ddp': {'method': binding['method'], 'params': params, 'id': local['operationId']}})
            mutation = write
            mid = ddp.begin(binding['method'], params, local['operationId'])
            result = ddp.finish(mid, mutation=write)
            if binding['result'] == 'json':
                return result
            if binding['result'] != 'insert-id' or result != local['operationId']:
                raise Uncertain('reply-uninterpretable', 'insert id differs')
            return {'id': result}
        except websocket.WebSocketException as e:
            if mutation:
                raise Uncertain('dispatch-uncertain', 'websocket closed') from e
            raise Refusal('websocket-unavailable') from e
        finally:
            if ws is not None:
                ws.close()
            else:
                s.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['tools', 'qualify', 'call'])
    parser.add_argument('app', help='package-pinned declaration name under apps/interfaces')
    parser.add_argument('--route', type=Path, help='member route directory holding http.sock and browser.token')
    parser.add_argument('--package-id', help='installed package identity from verified lifecycle evidence')
    parser.add_argument('--out', type=Path, help='new private run directory (never reused)')
    parser.add_argument('--operation', help='declared operation for call')
    parser.add_argument('--args', type=json.loads, help='JSON object for call')
    options = parser.parse_args()
    d = load(options.app)
    if options.command == 'tools':
        print(json.dumps({'tools': tools(d)}, indent=2)); return 0
    if not options.route or not options.out or not options.package_id:
        parser.error('qualify/call requires --route, --package-id and --out')
    if options.command == 'call' and (not options.operation or options.args is None):
        parser.error('call requires --operation and --args')
    if options.package_id != d['packageId']:
        raise Refusal('package-version-mismatch')
    if options.command == 'qualify':
        require_write_readback(d)
    options.out.mkdir(mode=0o700, parents=False, exist_ok=False)
    (options.out / 'row.pid').write_text(str(os.getpid()))
    context = {'runId': 'ai-' + uuid.uuid4().hex[:20]}
    with (options.out / 'requests.jsonl').open('x') as journal:
        os.chmod(journal.name, 0o600)
        summary = {'app': d['name'], 'packageId': d['packageId'], 'interfaceDigest': digest(d),
                   'runId': context['runId'], 'transport': 'member-browser-route', 'hermes': 'NOT_RUN'}
        try:
            engine = Engine(d, Route(options.route, d, journal), context)
            if options.command == 'qualify':
                result = run_scenario(engine)
            else:
                result = engine.tool_call('mini_' + d['name'] + '_' + options.operation.replace('.', '_'), options.args)
            (options.out / 'responses.json').write_text(json.dumps(result, indent=2) + '\n')
            os.chmod(options.out / 'responses.json', 0o600)
            summary.update(status='PASS', row='typed-write-readback' if options.command == 'qualify' else 'typed-call')
            code = 0
        except Refusal as e:
            summary.update(status='UNCERTAIN' if isinstance(e, Uncertain) else 'FAIL', reason=e.name, detail=e.detail)
            code = 3 if isinstance(e, Uncertain) else 1
        except (OSError, EOFError) as e:
            summary.update(status='FAIL', reason='transport-unavailable', detail=type(e).__name__)
            code = 1
        (options.out / 'result.json').write_text(json.dumps(summary, indent=2) + '\n')
        print(json.dumps(summary))
        return code


if __name__ == '__main__':
    try:
        sys.exit(main())
    except Refusal as e:
        print(json.dumps({'status': 'FAIL', 'reason': e.name, 'detail': e.detail})); sys.exit(1)
