#!/usr/bin/env python3
"""Joined inventory hook: actual arbitrary-member EtherCalc writes/readback.
The attach input supplies source-authorized keys/caps; this script creates no world.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import sys
import time
import uuid
HERE=Path(__file__).resolve().parent

def module(name,file):
    spec=importlib.util.spec_from_file_location(name,HERE/file);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m
app=module('same_store_app','same-store-app.py');f=app.f
ws=module('joined_spk_ws','jspk10-ws.py')

def exercise(fixture, phase):
    x=f.Fixture(fixture);root=x.root;retained=root/'joined-sheet.json';sockets=[]
    try:
        if phase=='before-restart':
            f.require(not retained.exists(),'joined sheet write already attempted; inspect evidence')
            state={'sheet':'mini-shared-'+uuid.uuid4().hex,'markers':{}}
            f.save(retained,state)
        else: state=f.load(retained)
        for label,d in x.f['delegates'].items():
            sock=ws.WS(None,'/socket.io/?EIO=3&transport=websocket',timeout=120,endpoint=ws.Endpoint(**d['endpoint']))
            sock.start(keepalive='2',every=20);sockets.append((label,sock))
            opened=sock.get(time.monotonic()+10);f.require(isinstance(opened,str) and opened.startswith('0'),'Engine.IO opening absent')
            ws.wait_for(sock,lambda message:isinstance(message,str) and message.startswith('40'),time.monotonic()+10)
        def read(sock,label):
            sock.send('42'+json.dumps(['data',{'type':'ask.log','room':state['sheet'],'user':label}]))
            result,_=ws.wait_for(sock,lambda message:(ws.sio_data(message) or {}).get('type')=='log',time.monotonic()+10)
            return json.dumps(ws.sio_data(result),sort_keys=True)
        if phase=='before-restart':
            for index,(label,sock) in enumerate(sockets):
                marker='member-'+label+'-'+uuid.uuid4().hex
                state['markers'][label]=marker
                # Retain exact intended writes before sending; no automatic retry.
                write=root/('joined-write-'+label+'.json');f.save(write,{'sheet':state['sheet'],'marker':marker})
                number=index+1;column=''
                while number: number,remainder=divmod(number-1,26);column=chr(65+remainder)+column
                command={'type':'execute','room':state['sheet'],'user':label,'cmdstr':f'set {column}1 text t {marker}','saveundo':False}
                sock.send('42'+json.dumps(['data',command]))
                observer=sockets[(index+1)%len(sockets)][1]
                if observer is not sock:
                    ws.wait_for(observer,lambda message:(ws.sio_data(message) or {}).get('cmdstr')==command['cmdstr'],time.monotonic()+10)
                f.require(marker in read(observer,sockets[(index+1)%len(sockets)][0]),'another member did not independently observe write')
            # Keep initial one-shot write plan; completion has its own immutable artifact.
            f.save(root/'joined-sheet-complete.json',state)
        else:
            state=f.load(root/'joined-sheet-complete.json')
            for label,sock in sockets:
                log=read(sock,label)
                f.require(all(marker in log for marker in state['markers'].values()),'persisted member data absent after restart')
        snapshot=x.snapshot();evidence=x.opdir/('joined-'+phase+'.json')
        f.save(evidence,{'phase':phase,'app':x.app,'generation':x.f['generation'],'sheet':state,'snapshot':snapshot})
        return x,evidence
    finally:
        for _,sock in sockets: sock.close()

def run(request_path,result_path):
    request=f.load(request_path);f.require(request['type']=='mini-joined-member-hook-request-v1' and request['role']=='spk','wrong hook contract')
    phase=request['phase'];f.require(phase in ['before-restart','after-restart'],'unsupported hook phase')
    c=f.load(request['instance']['attach']['inputPath'])
    f.require(c['miniConfigSha256']==request['identity']['configSha256'] and f.sha(c['manifest'])==request['identity']['manifestSha256'],'hook candidate or Store config differs')
    f.require(c['miniConfig']==request['deployment']['config'] and c['publicSocket']==request['deployment']['socket'],'hook supplied another Store endpoint')
    f.require(c['room']['target']==request['roomTarget'],'app attach is for another room')
    f.require(c['authority']['owner']==request['subjects'][request['owner']],'app owner differs from room owner')
    f.require({label:d['subject'] for label,d in c['delegates'].items()}==request['subjects'],'delegate inventory differs from scoped members')
    root=f.absolute(c['root']);fixture=root/'fixture.json'
    if phase=='before-restart': app.attach(request['instance']['attach']['inputPath'])
    else: f.require(request['appId']==c['application']['app'],'restart hook app identity differs')
    x,evidence=exercise(fixture,phase)
    value={'type':'mini-joined-member-hook-result-v1','identity':request['identity'],'role':'spk','phase':phase,'status':'pass',
        'roomTarget':request['roomTarget'],'subjects':request['subjects'],'instanceId':request['instanceId'],'appId':x.app,
        'artifacts':[{'path':str(evidence),'sha256':f.sha(evidence)}]}
    if phase=='before-restart':value.update(writeRead=True,shared=len(x.f['delegates'])>1)
    else:value.update(retainedData=True)
    f.save(result_path,value)

def main():
    os.umask(0o077);p=argparse.ArgumentParser(description=__doc__);p.add_argument('--request',required=True);p.add_argument('--result',required=True);args=p.parse_args();run(args.request,args.result)
if __name__=='__main__':main()
