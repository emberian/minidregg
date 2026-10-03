#!/usr/bin/env python3
"""Actual native context/current-base receiving on an existing participant.
Creates only this run's ordinary source/output/summary documents in the supplied
room. No world seed, provider calls, new history store, semantic Python model,
deployment, process kills or deletion. Native outcomes remain the authority.
"""
import argparse, hashlib, json, os, pathlib, shlex, subprocess

def main():
    p=argparse.ArgumentParser()
    for key in ('mini','host','config','socket','workspace','home','room','prefix','output'):
        p.add_argument('--'+key,required=True)
    p.add_argument('--timeout',type=int,default=180)
    p.add_argument('--handoff-prepared',action='store_true',help='Stop after actual signed native prepare; agreement receiver owns landing/recovery')
    p.add_argument('--support-document',action='append',default=[],help='Additional current authorized source reference to cite without mutating it')
    a=p.parse_args()
    if not a.prefix.replace('-','').isalnum():raise SystemExit('prefix must be a unique simple source name')
    if len(a.support_document)>8 or len(set(a.support_document))!=len(a.support_document):raise SystemExit('support documents require up to8 distinct existing references')
    out=pathlib.Path(a.output);out.mkdir(parents=True,exist_ok=True)
    os.chmod(out,0o700)
    home=pathlib.Path(a.home);requests=home/'requests'
    if not requests.is_dir():raise SystemExit('existing participant HOME/requests is required')
    state_path=out/'receiving.json'
    state=json.loads(state_path.read_text()) if state_path.exists() else {'type':'mini-context-review-receiving-v1','steps':{}}
    def retain():
        temp=out/'receiving.next.json'
        fd=os.open(temp,os.O_WRONLY|os.O_CREAT|os.O_TRUNC,0o600)
        try:os.write(fd,json.dumps(state,indent=2).encode());os.fsync(fd)
        finally:os.close(fd)
        os.replace(temp,state_path)
        fd=os.open(out,os.O_RDONLY|os.O_DIRECTORY)
        try:os.fsync(fd)
        finally:os.close(fd)
    def run_argv(label,argv,effect=False,refusal=False,native_refusal=False):
        prior=state['steps'].get(label)
        if prior and prior['phase']=='done':return prior['stdout']
        if prior:raise RuntimeError('uncertain prior '+label+' retained; inspect/recover exact native attempt before resuming')
        state['steps'][label]={'phase':'started','command':argv,'effect':effect};retain()
        try:r=subprocess.run(argv,capture_output=True,text=True,timeout=a.timeout,stdin=subprocess.DEVNULL)
        except subprocess.TimeoutExpired:raise RuntimeError('native outcome unknown at '+label+'; do not repeat')
        (out/(label+'.stdout')).write_text(r.stdout)
        (out/(label+'.stderr')).write_text(r.stderr)
        state['steps'][label].update(returncode=r.returncode,stdout=r.stdout,
            stdoutSHA256=hashlib.sha256(r.stdout.encode()).hexdigest())
        if native_refusal:
            # This proposal was authored while its base was current. Require
            # actual post-authoring native rejection, not the earlier client gate.
            try:outcome=json.loads(r.stdout)
            except json.JSONDecodeError:raise RuntimeError('native refusal omitted retained outcome JSON')
            if r.returncode!=3 or outcome.get('type')!='refused':
                raise RuntimeError('expected typed native current-base refusal, got '+str(r.returncode))
            if outcome.get('reason') not in ('operation-rejected','stale-root'):
                raise RuntimeError('native refusal did not identify expected guarded-source failure: '+str(outcome))
            state['steps'][label]['refusalBoundary']='typed-native-post-authoring'
        elif refusal:
            # A pinned-current-base check may refuse before proposal authoring
            # (client error1); typed native refusal3 is separately recognizable.
            early='the pinned document changed before proposal authoring' in (r.stdout+r.stderr)
            if r.returncode!=3 and not (r.returncode==1 and early):
                raise RuntimeError('expected exact current-base refusal; actual code '+str(r.returncode))
            state['steps'][label]['refusalBoundary']='before-proposal-authoring' if early else 'typed-native-refusal'
        elif r.returncode:
            raise RuntimeError('native '+label+' ended '+str(r.returncode)+'; exact attempt retained')
        state['steps'][label]['phase']='done';retain();return r.stdout
    def shell(label,line,effect=False,refusal=False,native_refusal=False):
        argv=[a.mini,'shell','--socket',a.socket,'--host',a.host,'--config',a.config,
              '--workspace',a.workspace,'--home',a.home,'--line',line]
        return run_argv(label,argv,effect,refusal,native_refusal)
    def prepared_write(label,line,proposal):
        planned=json.loads(shell(label+'-prepare',line))
        if planned.get('effect')!='none':raise RuntimeError('ordinary document prepare incorrectly claims installation')
        shell(label+'-submit','submit '+proposal,effect=True)
    def command_file(name,value):
        target=requests/(a.prefix+'-'+name+'.json')
        encoded=json.dumps(value,separators=(',',':')).encode()
        if target.exists():
            if target.read_bytes()!=encoded:raise RuntimeError('authored receiving file changed: '+str(target))
        else:
            fd=os.open(target,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
            try:os.write(fd,encoded);os.fsync(fd)
            finally:os.close(fd)
        return target.name
    def context(label,name):
        return json.loads(shell(label,'doc context '+shlex.quote(name)+' 64 8192'))
    def bundle(*sources):return {'type':'mini-context-bundle-v1','sources':list(sources)}
    def summary(pin):
        return {'type':'mini-context-summary-v1','text':'The authored source says initial-evidence.',
            'support':[{'name':source,'source':pin['source'],'root':pin['sourceRoot'],'capability':pin['readCapability']}]}
    source=a.prefix+'-source';target=a.prefix+'-output';memory=a.prefix+'-summary'
    for label,name in [('source',source),('target',target),('summary',memory)]:
        shell('birth-'+label,'doc new '+name+' note --in '+shlex.quote(a.room),effect=True)
    prepared_write('initial-source','doc append '+a.prefix+'-seed-source '+source+' initial-evidence',a.prefix+'-seed-source')
    prepared_write('initial-target','doc append '+a.prefix+'-seed-output '+target+' review-output',a.prefix+'-seed-output')
    first=context('first-source',source)
    initial=context('first-output',target)
    summary_file=command_file('summary-initial',summary(first))
    prepared_write('initial-summary','doc append '+a.prefix+'-seed-summary '+memory+' @'+summary_file,a.prefix+'-seed-summary')
    derived=context('summary-current',memory)
    rows=derived['rows']
    if not any(r.get('summary',{}).get('status')=='current' and r.get('text')=='The authored source says initial-evidence.' for r in rows):
        raise RuntimeError('current derived summary not received')
    external=[context('external-initial-'+str(i),name) for i,name in enumerate(a.support_document)]
    old=command_file('context-old',bundle(first,initial,derived,*external))
    request=command_file('proposal',{'type':'minidregg-workspace-proposal-v1','action':'invoke',
        'targets':[{'name':target,'payload':{'type':'document','actions':[{'type':'append','text':'review-landed'}]}}]})
    # Author a separate exact proposal before any source change. This tests
    # the native guard at landing, beyond the client pre-authoring stale gate.
    race_request=command_file('proposal-race',{'type':'minidregg-workspace-proposal-v1','action':'invoke',
        'targets':[{'name':target,'payload':{'type':'document','actions':[{'type':'append','text':'stale-race-must-not-land'}]}}]})
    race_proposal=a.prefix+'-race'
    race_plan=json.loads(shell('review-before-race','doc review '+race_proposal+' @'+old+' @'+race_request))
    if race_plan.get('effect')!='none':raise RuntimeError('prepared race incorrectly claims effect landing')
    # Actual admitted source edit, then structural reorder, each with signed reads.
    shell('source-seen','doc show '+source)
    prepared_write('source-edit','doc edit '+a.prefix+'-edit '+source+' 1 changed-evidence',a.prefix+'-edit')
    prepared_write('source-second','doc append '+a.prefix+'-second '+source+' additional-evidence',a.prefix+'-second')
    shell('source-move','doc move '+source+' 2 1',effect=True)
    after=context('source-after-move',source)
    if after['sourceRoot']==first['sourceRoot']:raise RuntimeError('source edit/move failed to change context dependency')
    texts=[row.get('text') for row in after['rows']]
    if texts!=['additional-evidence','changed-evidence']:
        raise RuntimeError('native document placement did not govern selected inference order: '+str(texts))
    if after['rows'][0].get('predecessor') is not None:
        raise RuntimeError('first projected row has an invented predecessor')
    if after['rows'][1].get('predecessor')!=after['rows'][0]['element']:
        raise RuntimeError('projected placement dependency differs from actual selected order')
    shell('submit-stale-race','submit '+race_proposal,effect=True,native_refusal=True)
    refused_readback=shell('readback-refused-race','doc show '+target)
    if 'stale-race-must-not-land' in refused_readback:
        raise RuntimeError('stale support proposal landed an output')
    invalid=context('summary-invalidated',memory)
    if not any(r.get('summary',{}).get('status')=='invalidated' and 'text' not in r for r in invalid['rows']):
        raise RuntimeError('stale derived memory entered inference context')
    shell('stale-review','doc review '+a.prefix+'-stale @'+old+' @'+request,refusal=True)
    # Explicit new authored memory/base; no retargeting of the previous proposal.
    fresh_summary=summary(after);fresh_summary['text']='The current source says changed-evidence.'
    fresh_file=command_file('summary-fresh',fresh_summary)
    shell('summary-seen','doc show '+memory)
    prepared_write('summary-revise','doc edit '+a.prefix+'-summary-revise '+memory+' 1 @'+fresh_file,a.prefix+'-summary-revise')
    current_summary=context('summary-rebased',memory)
    current_target=context('output-current',target)
    external=[context('external-current-'+str(i),name) for i,name in enumerate(a.support_document)]
    selected=command_file('context-fresh',bundle(after,current_target,current_summary,*external))
    proposal=a.prefix+'-land'
    planned=json.loads(shell('review-current','doc review '+proposal+' @'+selected+' @'+request))
    if planned.get('effect')!='none':raise RuntimeError('proposal creation incorrectly claims effect landing')
    if a.handoff_prepared:
        workspace=pathlib.Path(a.workspace)
        proposal_dir=workspace/'proposals'/proposal
        attempt=workspace/'attempts'/proposal
        run_argv('native-prepared-ingress',[a.mini,'workspace','--action','submit',
            '--dir',a.workspace,'--intent',str(proposal_dir/'intent.json'),
            '--attempt',str(attempt),'--prepare-only','true','--socket',a.socket])
        # Only actual retained public native inputs are handed to the receiver.
        # No controller journal, provider secret or signing key is included.
        retained={}
        for label,path in {'call':attempt/'call.bin','plan':attempt/'plan.bin',
            'planJson':attempt/'plan.json','preparedIntent':attempt/'intent.json',
            'config':attempt/'config.json','manifest':attempt/'attempt.json',
            'authoredIntent':proposal_dir/'intent.json','request':proposal_dir/'request.json',
            'proposal':proposal_dir/'proposal.json','selectedContext':requests/selected}.items():
            data=path.read_bytes()
            retained[label]={'path':str(path),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
        ws=json.loads((workspace/'workspace.json').read_text())
        actual_manifest=json.loads((attempt/'attempt.json').read_text())
        declared_host_sha=hashlib.sha256(pathlib.Path(a.host).read_bytes()).hexdigest()
        effective_host=actual_manifest.get('host')
        if effective_host:
            if hashlib.sha256(pathlib.Path(effective_host).read_bytes()).hexdigest()!=declared_host_sha:
                raise RuntimeError('actual prepared attempt Host differs from supplied matched Host')
        elif actual_manifest.get('hostSha256')!=declared_host_sha:
            raise RuntimeError('actual remote prepared Host pin differs from supplied matched Host')
        if (attempt/'config.json').read_bytes()!=pathlib.Path(a.config).read_bytes():
            raise RuntimeError('actual prepared config differs from selected receiving config')
        packet={'type':'mini-context-reviewed-native-ingress-v1','status':'PREPARED-NOT-LANDED',
            'participant':ws.get('subject'),'workspace':a.workspace,'home':a.home,
            'room':a.room,'sourceDocument':source,'outputDocument':target,
            'additionalSupportDocuments':a.support_document,'proposalId':proposal,
            'attempt':str(attempt),'socket':a.socket,'host':a.host,'mini':a.mini,
            'hostSha256':declared_host_sha,'actualNativeAttempt':actual_manifest,
            'miniSha256':hashlib.sha256(pathlib.Path(a.mini).read_bytes()).hexdigest(),
            'files':retained,
            'preparedPlan':json.loads((attempt/'plan.json').read_text()),
            'selectedSupport':json.loads((requests/selected).read_text()),
            'expectedWrite':'review-landed','sourceAuthority':'current signed participant reads and actual native prepare/assemble',
            'requires':'Receiver pre-state/config must match this exact prepared native admission prefix; no source bytes rename or re-sign/replan',
            'notClaimed':['agreement','effect-landing','lost-response-recovery','four-replica-readback','Bend-execution']}
        packet_path=out/'reviewed-native-ingress.json'
        encoded=json.dumps(packet,indent=2).encode()
        if packet_path.exists():
            if packet_path.read_bytes()!=encoded:raise RuntimeError('prepared native ingress changed')
        else:
            fd=os.open(packet_path,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
            try:os.write(fd,encoded);os.fsync(fd)
            finally:os.close(fd)
        state['result']={'status':'PREPARED-NOT-LANDED','ingress':str(packet_path),
            'ingressSha256':hashlib.sha256(encoded).hexdigest(),'callSha256':retained['call']['sha256']}
        retain();print(json.dumps(state['result']));return
    shell('submit','submit '+proposal,effect=True)
    shell('lookup','lookup '+proposal)
    readback=shell('readback','doc show '+target)
    if readback.count('review-landed')!=1:raise RuntimeError('source output not installed exactly once')
    shell('lookup-again','lookup '+proposal)
    again=shell('readback-again','doc show '+target)
    if again.count('review-landed')!=1:raise RuntimeError('exact recovery duplicated source output')
    # New participant process/read: semantic context ignores observation churn.
    cold=context('cold-projection',source)
    def semantic(v):return {k:x for k,x in v.items() if k not in ('observedHeight','readAuthorityRoot')}
    if semantic(cold)!=semantic(after):raise RuntimeError('same signed source yielded different semantic projection')
    state['result']={'status':'PASS','scope':'actual-native-document-context-summary-edit-placement-preauthoring-and-native-landing-refusal-review-submit-recover-readback',
        'residentStartedRecovery':'not exercised; existing request custody tests remain separate',
        'crossRoomMove':'not exercised','BendAuthoredSelector':'not exercised'}
    retain()
    print(json.dumps(state['result']))
if __name__=='__main__':main()
