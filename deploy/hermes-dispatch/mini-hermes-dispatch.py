#!/usr/bin/env python3
"""Registered Hermes delivery pump. File discovery is advisory; Mini admits every delivery."""
import argparse, collections, concurrent.futures, hashlib, itertools, json, os, pathlib, stat, subprocess, sys, time
MAX_BYTES=4*1024*1024
MAX_MEMBERS=4096
MAX_ASSIGNMENTS_PER_MEMBER=512

def read(path, trusted=False):
    path=pathlib.Path(path)
    descriptor=os.open(path,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK)
    try:
        metadata=os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode) or metadata.st_size>MAX_BYTES: raise ValueError('bounded regular JSON file required')
        if trusted and (metadata.st_uid not in (0,os.geteuid()) or metadata.st_mode&0o022): raise ValueError('operator-owned immutable registration required')
        data=os.read(descriptor,MAX_BYTES+1)
        if len(data)>MAX_BYTES: raise ValueError('JSON input exceeds bound')
        def pairs(items):
            result={}
            for key,value in items:
                if key in result:raise ValueError('duplicate JSON key')
                result[key]=value
            return result
        return json.loads(data,object_pairs_hook=pairs),hashlib.sha256(data).hexdigest()
    finally:os.close(descriptor)

def config(path):
    value,_=read(path,True)
    if set(value)!={'type','mini','socket','registrationsDir','memberHomes'} or value['type']!='mini-hermes-dispatch-service-v1':raise ValueError('invalid dispatcher service config')
    for key in ('mini','socket','registrationsDir'):
        if not isinstance(value[key],str) or not pathlib.Path(value[key]).is_absolute():raise ValueError('dispatcher paths must be absolute')
    homes=value['memberHomes']
    if not isinstance(homes,list) or len(homes)>MAX_MEMBERS or len(set(homes))!=len(homes) or any(not isinstance(h,str) or not pathlib.Path(h).is_absolute() for h in homes):raise ValueError('invalid bounded member inventory')
    return value

def registrations(directory):
    index={}
    for path in sorted(pathlib.Path(directory).glob('*.json')):
        r,_=read(path,True)
        if r.get('type')!='mini-hermes-dispatch-registration-v1':raise ValueError('invalid dispatcher registration')
        identity=(r['subject'],r['roomCell'],r['task'])
        if identity in index:raise ValueError('ambiguous registered resident identity')
        index[identity]=path
    return index

def member_files(home):
    # Keep iterators between polls: retained history is paged, never a lifetime
    # admission limit. A pathological member cannot stop the other inventories.
    return (p for p in pathlib.Path(home).glob('outbox/*/room-*/assignment-*/*.json') if p.name in ('handoff.json','dismissal.json'))

def jobs(c,index,cursors,offset):
    homes=c['memberHomes'];selected=homes[offset:]+homes[:offset];visits=0;exhausted=set()
    # One hint per member per round, bounded BEFORE success-cache filtering.
    for _ in range(16):
        for home in selected:
            if home in exhausted:continue
            if visits>=128:return
            visits+=1;cursor=cursors.setdefault(home,member_files(home))
            try:path=next(cursor)
            except (StopIteration,OSError):
                cursors[home]=member_files(home);exhausted.add(home);continue
            try:
                bundle,digest=read(path)
                payload=json.loads(bytes.fromhex(bundle['payloadHex']))
                identity=(payload['recipient'],payload['roomCell'],payload['task'])
                registration=index.get(identity)
                if registration:yield path,registration,digest
            except (OSError,ValueError,KeyError,TypeError):pass

def dispatch(c,job):
    path,registration,digest=job
    try:
        result=subprocess.run([c['mini'],'hermes-handoff','--socket',c['socket'],'--action','dispatch','--registration',str(registration),'--bundle',str(path)],capture_output=True,text=True,timeout=60)
        if result.returncode:
            return path,digest,False,result.stderr[-2048:].strip()
        return path,digest,True,'delivered'
    except (OSError,subprocess.TimeoutExpired) as error:return path,digest,False,str(error)

def pump(path,once=False):
    completed=collections.OrderedDict();reported=collections.OrderedDict();cursors={};offset=0
    while True:
        c=config(path);index=registrations(c['registrationsDir'])
        candidates=list(itertools.islice((j for j in jobs(c,index,cursors,offset) if completed.get(str(j[0]))!=j[2]),32))
        offset=(offset+32)%max(1,len(c['memberHomes']))
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
            futures=[pool.submit(dispatch,c,j) for j in candidates]
            for future in concurrent.futures.as_completed(futures):
                file,digest,ok,detail=future.result();key=str(file)
                if ok:
                    completed[key]=digest;completed.move_to_end(key)
                    while len(completed)>65536:completed.popitem(last=False)
                state=(digest,ok,detail)
                if reported.get(key)!=state:
                    print(json.dumps({'type':'mini-hermes-dispatch-event-v1','bundle':key,'delivered':ok,'detail':detail}),flush=True);reported[key]=state;reported.move_to_end(key)
                    while len(reported)>65536:reported.popitem(last=False)
        # Advisory bounded caches may evict. Native origin and durable ready
        # still establish exact retry; eviction never changes source authority.
        if once:return
        time.sleep(2)

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--config',required=True);parser.add_argument('--once',action='store_true');args=parser.parse_args()
    pump(args.config,args.once)
if __name__=='__main__':
    try:main()
    except (OSError,ValueError,KeyError,TypeError) as error:print(f'hermes dispatcher refused: {error}',file=sys.stderr);sys.exit(1)
