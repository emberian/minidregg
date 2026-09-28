#!/usr/bin/env python3
"""Private one-request ACP/Chat-Completions measurement; fake loopback model only."""
import hashlib
import http.server
import json
import os
import select
import subprocess
import threading
import time
from pathlib import Path

ROOT = Path('/workspace')
HOME = ROOT / '.hermes'
HOME.mkdir(mode=0o700, exist_ok=True)
for rel in ('.cache', '.config', '.local', '.local/share'):
    (ROOT / rel).mkdir(parents=True, exist_ok=True)
(HOME / 'config.yaml').write_text('''model:\n  provider: custom\n  default: bonsai2-27b-ptq1\n  context_length: 7168\n  base_url: http://127.0.0.1:18777/v1\n  api_key: synthetic-no-send-token\n  api_mode: chat_completions\nmcp_servers: {}\nmemory:\n  memory_enabled: false\n  user_profile_enabled: false\nauxiliary:\n  title_generation:\n    enabled: false\nagent:\n  max_iterations: 1\ntools:\n  tool_search:\n    enabled: false\n''')
captured = threading.Event()
class Sink(http.server.BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass
    def do_GET(self):
        self.send_response(404); self.end_headers()
    def do_POST(self):
        n = int(self.headers.get('Content-Length', '0'))
        if n > 2_000_000:
            self.send_response(413); self.end_headers(); return
        body = self.rfile.read(n)
        (ROOT / 'first-request.json').write_bytes(body)
        (ROOT / 'request-path.txt').write_text(self.path + '\n')
        captured.set()
        self.send_response(503); self.end_headers()
        self.wfile.write(b'{"error":"measurement sink only"}')
httpd = http.server.ThreadingHTTPServer(('127.0.0.1', 18777), Sink)
threading.Thread(target=httpd.serve_forever, daemon=True).start()
proc = subprocess.Popen(['/agent/hermes-acp'], cwd='/workspace', stdin=subprocess.PIPE,
                        stdout=subprocess.PIPE, stderr=(ROOT/'acp-stderr.log').open('wb'),
                        text=True, bufsize=1)
def send(i, method, params):
    proc.stdin.write(json.dumps({'jsonrpc':'2.0','id':i,'method':method,'params':params})+'\n')
    proc.stdin.flush()
def recv(i, seconds):
    deadline=time.monotonic()+seconds
    while time.monotonic()<deadline:
        ready,_,_=select.select([proc.stdout],[],[],min(1,deadline-time.monotonic()))
        if ready:
            line=proc.stdout.readline()
            if not line: raise RuntimeError('ACP EOF')
            obj=json.loads(line)
            if obj.get('id')==i: return obj
    raise TimeoutError(f'ACP response {i} timeout')
try:
    send(1,'initialize',{'protocolVersion':1,'clientCapabilities':{'fs':{'readTextFile':False,'writeTextFile':False}},'clientInfo':{'name':'mini-no-send-measurement','version':'0.1'}})
    init=recv(1,90)
    if 'result' not in init: raise RuntimeError(f'initialize: {str(init)[:300]}')
    send(2,'session/new',{'cwd':'/workspace','mcpServers':[]})
    session=recv(2,90)
    sid=(session.get('result') or {}).get('sessionId')
    if not sid: raise RuntimeError(f'session/new: {str(session)[:300]}')
    send(3,'session/prompt',{'sessionId':sid,'prompt':[{'type':'text','text':'Say hello.'}]})
    if not captured.wait(90):
        raise TimeoutError('no Chat Completions POST observed')
    body=(ROOT/'first-request.json').read_bytes()
    parsed=json.loads(body)
    summary={'scope':'upstream ACP built-in tools only; no Mini MCP server',
             'httpPath':(ROOT/'request-path.txt').read_text().strip(),
             'requestBytes':len(body),'requestSha256':hashlib.sha256(body).hexdigest(),
             'model':parsed.get('model'),'messageCount':len(parsed.get('messages',[])),
             'toolCount':len(parsed.get('tools',[])),
             'toolNames':[x.get('function',{}).get('name') for x in parsed.get('tools',[])],
             'messageChars':[len(json.dumps(x,ensure_ascii=False)) for x in parsed.get('messages',[])]}
    (ROOT/'summary.json').write_text(json.dumps(summary,sort_keys=True,indent=2)+'\n')
    print(json.dumps(summary,sort_keys=True), flush=True)
finally:
    proc.terminate()
    try: proc.wait(timeout=3)
    except subprocess.TimeoutExpired: proc.kill(); proc.wait()
    httpd.shutdown()
