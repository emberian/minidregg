#!/usr/bin/env python3
"""Author source-backed constructor Nock and expected bytes; contains no evaluator."""
import argparse,json,sys
sys.setrecursionlimit(30000)
from pathlib import Path
# Reuse the proven authoring grammar/jam rather than introduce another encoding.
ns={}
helper=Path(__file__).with_name('jworld-prototype.py')
exec(helper.read_text().split('parser=argparse.ArgumentParser()')[0],ns)
p=argparse.ArgumentParser()
p.add_argument('--parent',type=Path,required=True)
p.add_argument('--target',type=ns['decimal'],required=True)
p.add_argument('--revision',type=int,required=True)
p.add_argument('--out',type=Path,required=True)
p.add_argument('--definition-bytes',type=Path)
a=p.parse_args()
if a.revision<0: p.error("revision must be nonnegative")
data=json.loads(a.parent.read_text())
source=data.get('value',data.get('cell',{}).get('worldKind',data))
raw=bytes.fromhex(source['definitionBytes'])
# Compiler.StreamCodec.nat: canonical base255 digits with255 terminator.
def nat_bytes(value):
    digits=[]
    while value:
        digits.append(value%255);value//=255
    return bytes(digits+[255])
old=nat_bytes(int(source['descriptor']['kind']))+nat_bytes(int(source['descriptor']['revision']))
assert raw.startswith(old),'signed canonical definition prefix differs from source descriptor'
retarget={'descriptor':dict(source['descriptor']),'defaults':source['defaults']}
retarget['descriptor']['kind']=a.target
retarget['descriptor']['revision']=str(a.revision)
a.out.mkdir(parents=True,exist_ok=True)
(a.out/'retarget.json').write_text(json.dumps(retarget,indent=2)+'\n')
# Retargeting also changes the inner StoreCodec layout digest. The actual Host
# worldDefinition encoder supplies it; this authoring helper contains no hash,
# definition encoder, or evaluator implementation.
if a.definition_bytes is None: sys.exit(0)
newraw=a.definition_bytes.read_bytes()
newheader=nat_bytes(int(a.target))+nat_bytes(a.revision)
assert newraw.startswith(newheader),'actual Host retarget descriptor prefix differs'
shared=0
while shared<min(len(raw),len(newraw)) and raw[-shared-1]==newraw[-shared-1]: shared+=1
assert shared>0,'retargeting must preserve an actual parent defaults payload'
oldprefix=len(raw)-shared
new=newraw[:-shared]
assert oldprefix>=len(old),'retargeting unexpectedly preserved outer source descriptor prefix'
# Existing Nock gate: source sample contains target0,target1,parent; parent noun
# is axis221 inside the slammed gate (previous two-target layout is not assumed).
slot=ns['slot'];quote=ns['quote'];select=ns['select'];equal=ns['equal'];choose=ns['choose']
parent=slot(221)
def tail(noun,count):
    for unused in range(count): noun=select(noun,3)
    return noun
# Native slot traverses the exact source prefix in one authored axis.
body=slot((221<<oldprefix)|((1<<oldprefix)-1))
for byte in reversed(new): body=(quote(byte),body)
for index,byte in reversed(list(enumerate(old))):
    body=choose(equal(select(tail(parent,index),2),quote(byte)),body,slot(0))
output=(((quote(ns['cord']('definition')),body)),quote(0))
# Same native core convention as jworld-method: [[1 gate]0].
core=((1,(output,(0,0))),0)
abi={'evaluator':'nock','version':'5','context':'pinned','arm':'2','fuel':'1000000',
    'libraries':[],
    'sample':[{'target':'1','slot':'kind/definition/noun','key':'parent','type':'noun'}],
    'outputs':[{'key':'definition','target':'0','field':'0','type':'noun'}]}
a.out.mkdir(parents=True,exist_ok=True)
(a.out/'constructor.json').write_text(json.dumps({'jam':ns['jam'](core),'abi':abi},indent=2)+'\n')
(a.out/'expected.json').write_text(json.dumps({'definitionBytes':newraw.hex(),
    'target':a.target,'revision':str(a.revision),'parentPrefix':old.hex(),
    'replacedPrefixBytes':str(oldprefix),'retainedParentBytes':str(shared),
    'source':'source-authenticated parent defaults payload with actual Host retarget codec prefix; native execution pending'},indent=2)+'\n')
