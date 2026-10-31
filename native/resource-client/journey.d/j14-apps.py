#!/usr/bin/env python3
"""J14 for hosted apps through Hermes: one Store, one controller, typed app tools (Davros).

Derives from the J14_ORACLE driver (the native phases are shared). The differences:
  * the app is a repackaged Davros whose package declares an api interface;
  * the controller config carries a typed attachment (toolTask.typedApplications) instead of
    an Oracle service profile;
  * the provider route is the operator's pool row (OpenRouter) by default, the real model, with
    the key read from J14_APPS_POOL_KEY (a private file; never printed or logged);
  * the probe is one Hermes task: refused without the room's apps grant, then put and get.

J14_APPS_UNTIL names the last phase to run (world, prepare_platform, prepare_application,
worker, room, attach, probe). Extra env: J14_APPS_DECLARATION (apps/interfaces/davros.json),
J14_APPS_MODEL, J14_APPS_POOL_KEY.

Native qualification of any declaration (conversation protocols included): J14_APPS_ALIAS names the
attachment (default dav), J14_APPS_ROLE the permission role the route's ticket holds (default 1, Davros's
editor), and J14_APPS_UNTIL=qualify runs the phase after attach: the operator-foreground hidden tool
mini_app_<alias>_qualify through the controller (the same fixed `controller-tool` IPC as `mini app-interface
--action qualify`), with the declaration digest the attachment pins and a fresh runId. The qualification
scenario's write and read-back each cross Mini admission and settlement; the result and the controller's
exported application evidence are retained under the step directory. No LLM turn is made.
"""
import base64, hashlib, http.client, importlib.util, json, os, shutil, socket, sys, time
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('j14_oracle',HERE/'j14-oracle.py')
m=importlib.util.module_from_spec(spec);sys.modules['j14_oracle']=m;spec.loader.exec_module(m)
read,write,sha=m.read,m.write,m.sha
ORDER=['world','prepare_platform','prepare_application','worker','room','attach','probe','qualify']
POOL='pool'

def declaration_digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()

class Apps(m.Journey):
    PROVIDER_FIXTURE=False
    DATA_PUBLICATION=False
    MODEL=os.environ.get('J14_APPS_MODEL','anthropic/claude-sonnet-4.5')
    MAX_INPUT=65536
    MAX_OUTPUT=2048

    def __init__(self):
        super().__init__()
        self.declaration_path=Path(os.environ['J14_APPS_DECLARATION']).resolve(strict=True)
        self.declaration=read(self.declaration_path)
        self.alias=os.environ.get('J14_APPS_ALIAS','dav')
        self.c['sizeClass']='M'
        self.c['expectedHost']=self.alias+'-j14.localhost'

    def run(self,label,args,**kwargs):
        if label=='world':args=['flock','-o','/tank/lanes/world-up.lock',*args]
        return super().run(label,args,**kwargs)

    def fixed(self,verb,*args,**kwargs):
        if verb=='controller-export' and not args:args=('application',)
        return super().fixed(verb,*args,**kwargs)

    def application_input(self):
        value=super().application_input()
        human=dict(value['delegates']['bootstrap'])
        for key in human:
            if key not in ('subject','sessionKind','expectedHost'):
                human[key]=str(int(human[key])+1000)
        human['sessionKind']='web'
        value['delegates']['human']=human
        return value

    def room(self):
        super().room()
        # The founder's signed program is editable independently of the room
        # grants. This resident serves app requests, not librarian maintenance.
        program='''# Hosted application assistant

Handle the addressed request in this assignment using the available Mini tools.
The assignment includes the current signed room and program context. For a hosted
application request, call the named application tools in the requested order.
Report the actual result, including the exact refusal name when a tool refuses.
Never retry an uncertain call. Do not change grants, provider, or your program.
Use one final text response to answer the requesting member; Mini delivers it.
Do not call mini_say or perform unrelated index, digest, or document maintenance.
'''
        path=self.homes/'alice/requests/apps-program.md';path.write_text(program)
        self.shell('alice','doc show lab-hermes-librarian')
        self.shell('alice','doc edit apps-program lab-hermes-librarian 1 @apps-program.md')
        self.shell('alice','submit apps-program')
        shown=self.shell('alice','doc show lab-hermes-librarian').read_text()
        if program.rstrip('\n').replace('\n','␤') not in shown:
            raise ValueError('the signed app-assistant program was not verified after publication')

    def capture_failure(self):
        if not self.controller:return
        errors=[]
        for verb in ('controller-service-logs','controller-export'):
            try:self.fixed(verb)
            except Exception as error:errors.append({'command':verb,'error':str(error)})
        if errors:write(self.root/'failure-evidence-errors.json',errors)

    def cleanup(self):
        # Stop our controller and public listener before removing the world;
        # the shared driver then closes its remaining child processes.
        try:
            recoveries=list(self.root.glob('broker-*/recovery.json'))
            if recoveries:
                if self.controller:self.fixed('controller-stop',timeout=120)
                for daemon in self.daemons:
                    if 'serve-public-proxy' in daemon['argv']:
                        for process in self.processes:
                            if process.pid==daemon['pid'] and process.poll() is None:
                                process.terminate();process.wait(timeout=30)
                teardown=self.root/'teardown';(teardown/'broker-setup').mkdir(parents=True,exist_ok=True)
                if len(recoveries)!=1:raise ValueError('expected one world recovery locator')
                shutil.copyfile(recoveries[0],teardown/'broker-setup/recovery.json')
                self.run('world-down',[m.REPO/'scripts/spk-platform/world-down.sh',teardown])
                self.controller=False
        finally:super().cleanup()

    def human_read(self,marker):
        spec=importlib.util.spec_from_file_location('apps_fixture',m.REPO/'scripts/spk-platform/ws-continuity-fixture.py')
        fixture=importlib.util.module_from_spec(spec);spec.loader.exec_module(fixture)
        x=fixture.Fixture(read(self.c['preparedApplication'])['fixture'])
        human=x.f['delegates']['human']
        x.step('member:human:enrollment',lambda:x.enroll(human))
        endpoint=human['endpoint']
        connection=http.client.HTTPConnection(endpoint['host'],timeout=120)
        connection.sock=socket.socket(socket.AF_UNIX,socket.SOCK_STREAM)
        connection.sock.settimeout(120);connection.sock.connect(endpoint['unix_socket'])
        try:
            connection.request('GET','/dav/notes.txt',headers={
                'Host':endpoint['host'],'Origin':'https://'+endpoint['host'],
                'Cookie':'__Host-mini_spk_session='+Path(endpoint['token']).read_text().strip()})
            response=connection.getresponse();body=response.read(1048577)
            if response.status!=200 or body!=marker.encode():
                raise ValueError('human web route did not read the exact agent-written file (HTTP %s)'%response.status)
        finally:connection.close()
        evidence={'status':response.status,'bodySha256':hashlib.sha256(body).hexdigest(),
                  'session':human['session'],'subject':human['subject'],'app':x.app,'path':'/dav/notes.txt'}
        write(self.root/'human-read.json',evidence)
        return evidence

    # ---- provider: the operator's pool row, the real model -------------------------------------
    def start_provider(self,port):
        write(self.table,{'type':'mini-provider-table-v2','providers':[{'name':POOL,'kind':'openai-compatible',
            'endpoint':'https://openrouter.ai/api/v1/chat/completions','models':[self.MODEL],'credential':'pool',
            'caps':{'perCall':str(self.MAX_OUTPUT),'perDay':'200','ceilingMicroUsd':'12000000','callMicroUsd':'250000',
                    'memberDayMicroUsd':'12000000','memberTotalMicroUsd':'12000000'}}]})

    def gateway_config(self,port,base):
        reserve=7+(self.MAX_INPUT*100000+self.MAX_OUTPUT*200000+999999)//1000000
        return {'providers':str(base/'worker/runtime-root/providers.json'),'credentialBroker':str(base/'worker/runtime-root/keys-client.json'),
            'gatewayBind':f'127.0.0.1:{m.available_port()}','model':self.MODEL,'provider':POOL,
            'reserve':str(reserve+1000),'maxInputTokens':self.MAX_INPUT,'maxOutputTokens':self.MAX_OUTPUT,
            'maxRequestBytes':1048576,'maxResponseBytes':8388608,'timeoutSeconds':600,'localFixtureHostNetwork':False}

    def set_provider_keys(self,keyclient):
        source=Path(os.environ['J14_APPS_POOL_KEY'])
        info=source.stat()
        if info.st_mode&0o077 or source.is_symlink():raise ValueError('pool key file must be private')
        secret=self.root/'pool-key.secret';secret.write_bytes(source.read_bytes());secret.chmod(0o600)
        try:
            self.run('pool-key',[self.mini,'key','--action','set','--pool','true','--provider',POOL,'--secret',secret,'--broker',keyclient])
        finally:secret.unlink()

    # ---- attachment: Davros, the api route, a typed attachment ---------------------------------
    def attach(self):
        d=self.declaration
        a=self.alias
        self.c['expectedHost']=a+'-j14.localhost'
        self.c['attachmentExtras']={
            # Davros's signed schema: role 0 is viewer; role 1 grants view/edit.
            'roleId':os.environ.get('J14_APPS_ROLE','1'),
            'names':{'application':a+'-app','family':a+'-session','route':a+'-agent-v1','display':d['name']+' agent',
                     'handle':a+'-agent','serviceProtocol':None,'applicationFamily':'oracle'},
            'typed':{'alias':self.alias,'declarationSource':str(self.declaration_path),
                     'declarationSha256':declaration_digest(d),'packageId':d['packageId']}}
        super().attach()

    # ---- native qualification: the declaration's own scenario through the controller -----------
    def qualify(self):
        import secrets
        d=self.declaration
        request=secrets.token_hex(16)
        args=self.root/'qualify-arguments.json'
        write(args,{'context':{'runId':'q'+secrets.token_hex(8)},'_miniInterfaceDigest':declaration_digest(d)})
        write(self.root/'qualify-request.json',{'requestId':request,'tool':'mini_app_'+self.alias+'_qualify','arguments':str(args)})
        done=self.fixed('controller-tool',request,'mini_app_'+self.alias+'_qualify',args)
        value=read(done)
        result=value.get('result',{})
        text=result.get('text','')
        try:detail=json.loads(text)
        except ValueError:detail={'raw':text[:400]}
        verdict={'passed':value.get('type')=='tool-complete' and value.get('isError') is False and result.get('isError') is False,
                 'requestId':request,'alias':self.alias,'packageId':d['packageId'],'detail':detail}
        write(self.root/'qualify-result.json',verdict)
        self.fixed('controller-tool-ack',request)
        if not verdict['passed']:raise ValueError('native qualification failed: '+json.dumps(detail)[:500])
        write(self.root/'result.json',{'passed':True,'rows':['typed-attachment','native-qualification-'+self.alias],'receipts':len(detail.get('nativeReceipts',[]))})

    # ---- probe -----------------------------------------------------------------------------
    def transcript(self):
        path=self.shell('alice','tail --in lab --json -n 200')
        return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]

    def replies_to(self,rows):
        return [r for r in rows if r.get('author')==self.subjects['hermes'] and r.get('to')==self.subjects['bob'] and r.get('kind')=='say']

    def task_turn(self,label,text):
        """One ask, one resident invocation; returns the new Hermes replies to bob."""
        exported=read(self.fixed('controller-export'))
        completed=self.completed_prompts(exported)
        known={(r['cell'],r['sequence']) for r in self.replies_to(self.transcript())}
        before=self.paid()
        self.shell('bob','ask lab '+text)
        self.resident(label,completed)
        new=[r for r in self.replies_to(self.transcript()) if (r['cell'],r['sequence']) not in known]
        if not new:raise ValueError('Hermes sent no reply to the ask: '+label)
        if self.paid()<=before:raise ValueError('the reply was not a paid turn: '+label)
        return new

    def application_attempts(self):
        journal=read(self.fixed('controller-journal'))
        history=journal.get('applicationApiHistory') or []
        return [a for a in history if a.get('routeName')=='dav-app' or a.get('route_name')=='dav-app']

    def provider_tool_results(self,exported):
        results={}
        for path,record in exported['files'].items():
            if not path.endswith('.controller-request'):continue
            data=base64.b64decode(record['base64'],validate=True)
            if hashlib.sha256(data).hexdigest()!=record['sha256']:raise ValueError('provider evidence digest differs')
            request=json.loads(data);calls={}
            for message in request.get('messages',[]):
                for call in message.get('tool_calls',[]):
                    calls[call['id']]=call['function']
                if message.get('role')=='tool' and message.get('tool_call_id') in calls:
                    call=calls[message['tool_call_id']]
                    if 'mini_app_dav_' in call.get('name',''):
                        results[message['tool_call_id']]={'providerRequest':path,'requestSha256':record['sha256'],
                            'call':call,'content':message.get('content')}
        return list(results.values())

    def dispatch_evidence(self,attempts,exported):
        state=Path(self.c['controllerRoot'])/'state';observed=set()
        for attempt in attempts:
            if attempt.get('phase')!='definite' or not attempt.get('lifetimeCommittedReceipt') or not attempt.get('lifetimeSettlement'):
                raise ValueError('Davros call lacks definite admission and settlement receipts')
            documents=[]
            for field in ('request','reply'):
                path=str(Path(attempt[field+'Path']).relative_to(state));record=exported['files'][path]
                payload=base64.b64decode(record['base64'],validate=True)
                if hashlib.sha256(payload).hexdigest()!=attempt[field+'Sha256']:raise ValueError('dispatch evidence digest differs')
                documents.append(json.loads(payload))
            request,reply=documents
            if reply.get('protocol')!='mini-spk-agent-api-v3' or reply.get('type')!='http-v3' or reply.get('status') not in (200,201,204):
                raise ValueError('Davros dispatch did not complete with a successful HTTP receipt')
            if (str(attempt['operationId'])!=reply.get('operationId') or
                request.get('operationId')!=reply.get('operationId') or
                request.get('bindingSha256')!=reply.get('bindingSha256') or
                any(not isinstance(reply.get(field),str) or len(reply[field])!=64 or
                    any(c not in '0123456789abcdef' for c in reply[field])
                    for field in ('bindingSha256','operationFingerprint','responseSha256')) or
                any(attempt.get(field)!=reply.get(field) for field in ('bindingSha256','operationFingerprint')) or
                attempt['lifetimeCommittedReceipt']!=reply.get('committedReceipt') or
                attempt.get('lifetimeSettledResponseSha256')!=reply.get('responseSha256') or
                attempt['lifetimeSettlement'].get('forwardOperationId')!=attempt['operationId'] or
                attempt['lifetimeSettlement'].get('settlement',{}).get('operation')!='dispatch settle'):
                raise ValueError('Davros admission, reply, and settlement do not join the same call')
            observed.add((request.get('method'),request.get('path')))
        if not {('PUT','dav/notes.txt'),('GET','dav/notes.txt')}<=observed:
            raise ValueError('receipts do not contain both the requested put and get: '+repr(observed))

    def probe(self):
        marker='Hermes was here %s'%self.broker['store']
        refused=self.task_turn('refused','Use your hosted Davros tool mini_app_dav_file_put_text to save the text "x" at path refused.txt, '
            'then tell me the exact outcome you received, including any refusal name.')
        write(self.root/'refused-replies.json',refused)
        if not any('typed-apps-not-granted' in r.get('text','') for r in refused):
            raise ValueError('the ungranted task did not meet the named refusal typed-apps-not-granted')
        exported=read(self.fixed('controller-export'))
        results=self.provider_tool_results(exported)
        write(self.root/'refused-tool-results.json',results)
        if not any('mini_app_dav_file_put_text' in r['call']['name'] and
                   'typed-apps-not-granted' in json.dumps(r['content']) for r in results):
            raise ValueError('no actual refused Davros tool result was returned to the provider')
        if self.application_attempts():raise ValueError('a refused task reached the application API')
        self.shell('alice','tariff lab set hermes/tools 16')
        done=self.task_turn('granted','Use your hosted Davros tools in this one task. First call mini_app_dav_file_put_text to save the text "%s" '
            'at path notes.txt, then call mini_app_dav_file_get_text for notes.txt and tell me the exact content you read back.'%marker)
        write(self.root/'granted-replies.json',done)
        self.fixed('controller-service-logs')
        exported=read(self.fixed('controller-export'))
        write(self.root/'granted-tool-results.json',self.provider_tool_results(exported))
        attempts=self.application_attempts()
        write(self.root/'application-attempts.json',attempts)
        if not any(marker in r.get('text','') for r in done):raise ValueError('the reply does not carry the read-back content')
        if len(attempts)<2:raise ValueError('expected a put and a get dispatch on the Davros route, saw %d'%len(attempts))
        self.dispatch_evidence(attempts,exported)
        human=self.human_read(marker)
        write(self.root/'result.json',{'protocol':'mini-j14-apps-result-v1','passed':True,'marker':marker,'store':self.broker['store'],
            'rows':['same-store-provision','typed-attachment','room-refusal-by-name','put-and-get-through-mini','human-read-same-grain'],
            'browserRead':human})
        print(self.root/'result.json')

def main():
    until=os.environ.get('J14_APPS_UNTIL','probe')
    if until not in ORDER:raise SystemExit('J14_APPS_UNTIL must be one of '+','.join(ORDER))
    j=Apps();phase='init'
    try:
        for phase in ORDER[:ORDER.index(until)+1]:
            getattr(j,phase)()
            write(j.root/('context-after-'+phase+'.json'),j.c)
            print('phase done',phase,flush=True)
    except Exception as error:
        write(j.root/'failure.json',{'phase':phase,'error':str(error),'passed':False,'lastCommand':j.counter})
        j.capture_failure()
        raise
    finally:j.cleanup()

if __name__=='__main__':main()
