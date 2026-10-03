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
    a=p.parse_args()
    if not a.prefix.replace('-','').isalnum():raise SystemExit('prefix must be a unique simple source name')
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
    def shell(label,line,effect=False,refusal=False):
        prior=state['steps'].get(label)
        if prior and prior['phase']=='done':return prior['stdout']
        if prior:raise RuntimeError('uncertain prior '+label+' retained; inspect/recover exact native attempt before resuming')
        argv=[a.mini,'shell','--socket',a.socket,'--host',a.host,'--config',a.config,
              '--workspace',a.workspace,'--home',a.home,'--line',line]
        state['steps'][label]={'phase':'started','command':argv,'effect':effect};retain()
        try:r=subprocess.run(argv,capture_output=True,text=True,timeout=a.timeout,stdin=subprocess.DEVNULL)
        except subprocess.TimeoutExpired:raise RuntimeError('native outcome unknown at '+label+'; do not repeat')
        (out/(label+'.stdout')).write_text(r.stdout)
        (out/(label+'.stderr')).write_text(r.stderr)
        state['steps'][label].update(returncode=r.returncode,stdout=r.stdout,
            stdoutSHA256=hashlib.sha256(r.stdout.encode()).hexdigest())
        if refusal:
            # A pinned-current-base check may refuse before proposal authoring
            # (client error1); typed native refusal3 is separately recognizable.
            early='the pinned document changed before proposal authoring' in (r.stdout+r.stderr)
            if r.returncode!=3 and not (r.returncode==1 and early):
                raise RuntimeError('expected exact current-base refusal; actual code '+str(r.returncode))
            state['steps'][label]['refusalBoundary']='before-proposal-authoring' if early else 'typed-native-refusal'
        elif r.returncode:
            raise RuntimeError('native '+label+' ended '+str(r.returncode)+'; exact attempt retained')
        state['steps'][label]['phase']='done';retain();return r.stdout
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
            'support':[{'name':source,'source':pin['source'],'root':pin['sourceRoot']}]}
    source=a.prefix+'-source';target=a.prefix+'-output';memory=a.prefix+'-summary'
    for label,name in [('source',source),('target',target),('summary',memory)]:
        shell('birth-'+label,'doc new '+name+' note --in '+shlex.quote(a.room),effect=True)
    shell('initial-source','doc append '+a.prefix+'-seed-source '+source+' initial-evidence',effect=True)
    shell('initial-target','doc append '+a.prefix+'-seed-output '+target+' review-output',effect=True)
    first=context('first-source',source)
    initial=context('first-output',target)
    summary_file=command_file('summary-initial',summary(first))
    shell('initial-summary','doc append '+a.prefix+'-seed-summary '+memory+' @'+summary_file,effect=True)
    derived=context('summary-current',memory)
    rows=derived['rows']
    if not any(r.get('summary',{}).get('status')=='current' and r.get('text')=='The authored source says initial-evidence.' for r in rows):
        raise RuntimeError('current derived summary not received')
    old=command_file('context-old',bundle(first,initial,derived))
    request=command_file('proposal',{'type':'minidregg-workspace-proposal-v1','action':'invoke',
        'targets':[{'name':target,'payload':{'type':'document','actions':[{'type':'append','text':'review-landed'}]}}]})
    # Actual admitted source edit, then structural reorder, each with signed reads.
    shell('source-seen','doc show '+source)
    shell('source-edit','doc edit '+a.prefix+'-edit '+source+' 1 changed-evidence',effect=True)
    shell('source-second','doc append '+a.prefix+'-second '+source+' additional-evidence',effect=True)
    shell('source-move','doc move '+source+' 2 1',effect=True)
    after=context('source-after-move',source)
    if after['sourceRoot']==first['sourceRoot']:raise RuntimeError('source edit/move failed to change context dependency')
    invalid=context('summary-invalidated',memory)
    if not any(r.get('summary',{}).get('status')=='invalidated' and 'text' not in r for r in invalid['rows']):
        raise RuntimeError('stale derived memory entered inference context')
    shell('stale-review','doc review '+a.prefix+'-stale @'+old+' @'+request,refusal=True)
    # Explicit new authored memory/base; no retargeting of the previous proposal.
    fresh_summary=summary(after);fresh_summary['text']='The current source says changed-evidence.'
    fresh_file=command_file('summary-fresh',fresh_summary)
    shell('summary-seen','doc show '+memory)
    shell('summary-revise','doc edit '+a.prefix+'-summary-revise '+memory+' 1 @'+fresh_file,effect=True)
    current_summary=context('summary-rebased',memory)
    current_target=context('output-current',target)
    selected=command_file('context-fresh',bundle(after,current_target,current_summary))
    proposal=a.prefix+'-land'
    planned=json.loads(shell('review-current','doc review '+proposal+' @'+selected+' @'+request))
    if planned.get('effect')!='none':raise RuntimeError('proposal creation incorrectly claims effect landing')
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
    state['result']={'status':'PASS','scope':'actual-native-document-context-summary-edit-placement-current-base-review-submit-recover-readback',
        'residentStartedRecovery':'not exercised; existing request custody tests remain separate',
        'crossRoomMove':'not exercised','BendAuthoredSelector':'not exercised'}
    retain()
    print(json.dumps(state['result']))
if __name__=='__main__':main()
