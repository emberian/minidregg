#!/usr/bin/env python3
"""Native boundary checks on the exact supplied joined Store/member inventory."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

here=Path(__file__).resolve().parent
module=importlib.util.spec_from_file_location('joined',here/'joined-member-journey.py')
j=importlib.util.module_from_spec(module);module.loader.exec_module(j)


def foreign_reference(refs, target):
    matches=[row for row in refs['references'] if str(row.get('target'))==str(target) and row.get('observeCapability')]
    j.require(matches, 'owner has no native reference for the exact supplied document')
    return matches[0]


def native_refusal(result):
    """Decode the CLI's retained Host outcome, never an rc-only refusal."""
    j.require(result.returncode == 3, 'boundary read did not return native refusal rc3')
    stdout = result.stdout.decode(errors='replace').strip()
    if stdout:
        outcome = json.loads(stdout)
    else:
        matches = re.findall(r'^  outcome \(decoded by the Host\): (\{[^\n]*\})$',
                             result.stderr.decode(errors='replace'), re.MULTILINE)
        j.require(len(matches) == 1, 'boundary refusal lacks one exact Host-decoded outcome')
        outcome = json.loads(matches[0])
    j.require(outcome.get('type') == 'refused' and outcome.get('reason') == 'no-grant'
              and outcome.get('phase') == 'observation'.encode().hex(),
              'boundary read did not receive the source observation no-grant refusal')
    return outcome


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--state',required=True);parser.add_argument('--request',required=True);parser.add_argument('--result',required=True)
    a=parser.parse_args()
    state=j.read(j.absolute(a.state));spec=j.read(j.absolute(state['journey']))
    request=j.read(j.absolute(a.request));identity=j.validate(spec)
    j.require(identity==state['identity']==request['identity'],'boundary request belongs to another Store')
    j.require(request['role']=='group-boundary' and request['phase']=='run','unknown native boundary role/phase')
    outsider=request['boundaryActor'];owner=request['owner']
    j.require(outsider in spec['members'] and owner in request['subjects'] and outsider not in request['subjects'], 'boundary actor must be an actual uninvited member')
    j.require(request['subjects'][owner]==spec['members'][owner]['subject'],'owner inventory changed')
    label='boundary-'+hashlib.sha256(Path(a.request).name.encode()).hexdigest()[:16]
    evidence=j.absolute(request['evidenceDirectory'])/(label+'.json')
    j.require(not evidence.exists(),'native boundary evidence already exists')
    records=[]
    def run(argv):
        j.require(j.validate(spec)==identity,'Store pins changed during native boundary check')
        argv=[str(v) for v in argv]
        result=subprocess.run(argv,stdin=subprocess.DEVNULL,capture_output=True,timeout=spec.get('timeoutSeconds',300))
        records.append({'argv':argv,'rc':result.returncode,'stdout':result.stdout.decode(errors='replace'),'stderr':result.stderr.decode(errors='replace')})
        return result
    def shell(member,line):
        ssh=spec['members'][member]['ssh']
        return run(['/usr/bin/ssh','-F','/dev/null','-T','-o','BatchMode=yes','-o','IdentitiesOnly=yes','-o','StrictHostKeyChecking=yes','-o','ClearAllForwardings=yes','-o','UserKnownHostsFile='+ssh['knownHostsFile'],'-i',ssh['identityFile'],'-p',ssh['port'],ssh['destination'],line])
    observed=shell(owner,'refs')
    j.require(observed.returncode==0,'native owner reference observation failed')
    reference=foreign_reference(json.loads(observed.stdout),request['documentTarget'])
    alias='foreign-'+hashlib.sha256(str(request['documentTarget']).encode()).hexdigest()[:16]
    manifest=j.read(j.absolute(spec['manifest']))
    imported=run([manifest['mini'],'workspace','--action','import','--dir',spec['members'][outsider]['workspace'],'--name',alias,'--kind','object','--target',request['documentTarget'],'--observe-capability',reference['observeCapability']])
    j.require(imported.returncode==0,'local foreign discovery hint could not be installed')
    # Importing another holder's real capability ID is only a local hint. The
    # outsider must receive a source signed refusal on this exact document.
    refused=shell(outsider,'read '+alias)
    j.save(evidence,{'identity':identity,'roomTarget':request['roomTarget'],'documentTarget':request['documentTarget'],
                     'owner':spec['members'][owner]['subject'],'outsider':spec['members'][outsider]['subject'],
                     'foreignCapability':reference['observeCapability'],'commands':records})
    outcome=native_refusal(refused)
    j.save(Path(a.result),{'type':'mini-joined-member-hook-result-v1','role':request['role'],'phase':request['phase'],'status':'pass',
                          'identity':identity,'refused':True,'refusedSubject':spec['members'][outsider]['subject'],
                          'roomTarget':request['roomTarget'],'documentTarget':request['documentTarget'],
                          'outcome':outcome,
                          'artifacts':[{'path':str(evidence),'sha256':j.digest(evidence)}]})

if __name__=='__main__':main()
