#!/usr/bin/env python3
"""Scripted no-paid SSE fixture; summarizes the actual native document read.

The listening port is an explicit input so a restart of this separately managed
unit keeps the endpoint already published in the root-copied provider table.
"""
import argparse,hashlib,http.server,json,os,pathlib,threading,unicodedata
p=argparse.ArgumentParser();p.add_argument('--state',required=True);p.add_argument('--port',type=int,required=True);a=p.parse_args()
if not 1024<a.port<65536:raise SystemExit('fixture provider needs an explicit unprivileged port')
os.umask(0o077);state=pathlib.Path(a.state);lock=threading.Lock()
def write(name,value):
    destination=state/name;temporary=state/(name+'.tmp')
    with open(temporary,'w') as stream:
        json.dump(value,stream,indent=2);stream.write('\n');stream.flush();os.fsync(stream.fileno())
    os.replace(temporary,destination)
    fd=os.open(state,os.O_RDONLY|os.O_DIRECTORY);os.fsync(fd);os.close(fd)
def summary(body):
    reads=[row for row in body.get('messages',[]) if row.get('role')=='tool' and row.get('tool_call_id')=='captured-input-read']
    if len(reads)!=1:raise ValueError('one actual captured input read required')
    result=json.loads(reads[0]['content'])
    if result.get('isError'):raise ValueError('native input read refused')
    content=result.get('content',[])
    if len(content)!=1 or content[0].get('type')!='text':raise ValueError('native read result shape differs')
    read=json.loads(content[0]['text']);doc=read['doc'];text=read['text']
    if not isinstance(doc,str) or not isinstance(text,str) or not text.strip():raise ValueError('native document input absent')
    excerpt=''.join(c if c=='\n' or unicodedata.category(c)!='Cc' else ' ' for c in text).encode()[:2000].decode('utf-8','ignore')
    reply='Verified current captured input '+doc+'.\n'+excerpt
    return reply,hashlib.sha256(text.encode()).hexdigest()
class Endpoint(http.server.BaseHTTPRequestHandler):
    def do_POST(self):
        if self.path!='/v1/chat/completions':self.send_error(404);return
        length=int(self.headers.get('Content-Length','0'))
        if not 0<length<=1048576:self.send_error(413);return
        raw=self.rfile.read(length)
        try:body=json.loads(raw);reply,read_sha=summary(body)
        except (ValueError,KeyError,TypeError) as error:self.send_error(400,str(error));return
        with lock:
            destination=state/'provider-received.json'
            received=json.loads(destination.read_text()) if destination.exists() else []
            received.append({'body':body,'sha256':hashlib.sha256(raw).hexdigest(),'reply':reply,'nativeInputTextSha256':read_sha})
            write('provider-received.json',received)
        chunks=[{'id':'completion-cut','object':'chat.completion.chunk','created':1,'model':'mini-hermes-completion-cut','choices':[{'index':0,'delta':{'role':'assistant','content':reply},'finish_reason':'stop'}]},
            {'id':'completion-cut','object':'chat.completion.chunk','created':1,'model':'mini-hermes-completion-cut','choices':[],'usage':{'prompt_tokens':1,'completion_tokens':2,'total_tokens':3}}]
        data=(''.join('data: '+json.dumps(value)+'\n\n' for value in chunks)+'data: [DONE]\n\n').encode()
        self.send_response(200);self.send_header('Content-Type','text/event-stream');self.send_header('Content-Length',str(len(data)));self.end_headers();self.wfile.write(data)
    def log_message(self,*args):pass
server=http.server.ThreadingHTTPServer(('127.0.0.1',a.port),Endpoint)
write('provider-ready.json',{'protocol':'mini-resident-fixture-provider-ready-v1','pid':os.getpid(),'endpoint':f'http://127.0.0.1:{server.server_port}/v1/chat/completions','sourceSha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()})
server.serve_forever()
