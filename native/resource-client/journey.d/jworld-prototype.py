#!/usr/bin/env python3
"""Noun/formula authoring and canonical jam only. This contains NO evaluator."""
import argparse, json
from pathlib import Path

def cell(a,b): return (a,b)
def quote(noun): return (1,noun)
def slot(axis): return (0,axis)
def evaluate(subject,formula): return (2,(subject,formula))
def kick(arm,core): return (9,(arm,core))
def edit_sample(sample,gate): return (10,((6,sample),gate))
def equal(a,b): return (5,(a,b))
def choose(test,yes,no): return (6,(test,(yes,no)))
def push(value,body): return (8,(value,body))
def cord(text): return int.from_bytes(text.encode(),"little")
def noun_list(values):
    result=0
    for value in reversed(values): result=(value,result)
    return result
def formula_list(values):
    result=quote(0)
    for value in reversed(values): result=(value,result)
    return result
def axis_at(parent,child):
    suffix=bin(child)[3:]
    return int(bin(parent)[2:]+suffix,2)
def select(value,axis): return evaluate(value,quote(slot(axis)))
def effect(key,value): return (quote(cord(key)),value)

# Every running implementation receives [B_i [S [C i]]].
# C is the same final bundle (axis14), i the implementation index (axis15).
SELF=slot(14)
SAMPLE=slot(6)
CURRENT=slot(15)
ARMS=[8,9,10,11]
# Bundle C = [[[A0 A1] [A2 A3]] [dispatch implementations]].
# dispatch = [2 3]: tally resolves to derived implementation2, close to3.
# implementations = ~[[8 none] [9 none] [10 some0] [11 some1]].
DISPATCH=(2,3)
IMPLEMENTATIONS=noun_list([(8,0),(9,0),(10,(0,0)),(11,(0,1))])

def implementation(index):
    # Finite source-generated switch, reading actual metadata from C.
    # The branch list uses indices only; arm and predecessor come from C.
    result=slot(0) # unknown index crashes, never defaults to another method
    entry_axis=2
    paths=[]
    for unused in ARMS:
        paths.append(axis_at(axis_at(14,7),entry_axis))
        entry_axis=axis_at(3,entry_axis)
    for i,path in reversed(list(enumerate(paths))):
        result=choose(equal(index,quote(i)),slot(path),result)
    return result

def invoke(index):
    arm=select(implementation(index),2)
    # Construct the existing Nock [9 arm 0 1] formula as a noun, then run it
    # over the same C. Its constructor yields a gate with C retained.
    kick_formula=(quote(9),(arm,quote(slot(1))))
    gate=evaluate(SELF,kick_formula)
    return kick(2,edit_sample(SAMPLE,gate))

def inherited():
    predecessor=select(implementation(CURRENT),3)
    # none is atom0; selecting axis3 of it crashes. some i is [0 i].
    return invoke(select(predecessor,3))

# Actual vote count is the sole source sample slot. With one target and one
# ABI slot, its value is axis109 in the installed gate (same as jworld-method).
base_tally=(slot(109),quote(0))
# Base close must use the shared final dispatch table, not direct base_tally.
self_tally=select(SELF,axis_at(6,2))
base_close=push(invoke(self_tally),formula_list([
    effect("open",quote(0)),
    effect("tally",slot(4)),      # result.head from pushed [result oldGate]
    effect("dispatch",slot(5)),  # result.tail proves final-self customization
]))
# Sibling override preserves inherited count, changes observable dispatch mark.
derived_tally=(select(inherited(),2),quote(1))
# Derived close calls inherited base close, retaining final self all the way.
derived_close=(effect("derived",quote(1)),inherited())
BODIES=[base_tally,base_close,derived_tally,derived_close]

def constructor(body,index):
    # Over C, this yields [body [0 [C index]]]. slam replaces only axis6.
    return (quote(body),(quote(0),(slot(1),quote(index))))

constructors=[constructor(body,i) for i,body in enumerate(BODIES)]
BUNDLE=(((constructors[0],constructors[1]),(constructors[2],constructors[3])),
        (DISPATCH,IMPLEMENTATIONS))

# Canonical jam authoring copied from the existing jworld-method fixture.
def mat(n):
    if n==0: return [1]
    b=n.bit_length(); c=b.bit_length()
    return [0]*c+[1]+[(b>>i)&1 for i in range(c-1)]+[(n>>i)&1 for i in range(b)]
def jam(noun):
    out,table=[],{}
    def go(n):
        key=("a",n) if isinstance(n,int) else ("c",n)
        if key in table:
            p=table[key]
            if isinstance(n,int) and n.bit_length()<=p.bit_length(): out.extend([0]+mat(n))
            else: out.extend([1,1]+mat(p))
            return
        table[key]=len(out)
        if isinstance(n,int): out.extend([0]+mat(n))
        else: out.extend([1,0]); go(n[0]); go(n[1])
    go(noun)
    atom=sum(bit<<i for i,bit in enumerate(out))
    return atom.to_bytes((atom.bit_length()+7)//8,"little").hex()

def abi(arm, libraries, outputs, sample=True):
    return {"evaluator":"nock","version":"5","context":"pinned","arm":str(arm),
      "fuel":"1000000","libraries":libraries,
      "sample":[{"target":"0","slot":"world/resource/field/3/count/before","key":"votes","type":"nat"}] if sample else [],
      "outputs":[{"key":key,"target":"0","field":str(field),"type":"nat"} for key,field in outputs]}
BASE_OUTPUTS=[("open",90),("tally",91),("dispatch",92)]
CLOSE_OUTPUTS=BASE_OUTPUTS+[("derived",93)]
def decimal(text):
    if not text.isascii() or not text.isdecimal() or str(int(text))!=text:
        raise argparse.ArgumentTypeError("source program ID must be canonical decimal")
    return text
parser=argparse.ArgumentParser()
parser.add_argument("--out",type=Path,required=True)
parser.add_argument("--library-id",type=decimal)
parser.add_argument("--base-program-id",type=decimal)
parser.add_argument("--close-program-id",type=decimal)
parser.add_argument("--instance-target",type=decimal)
args=parser.parse_args()
args.out.mkdir(parents=True,exist_ok=True)
def emit(name,value):
    (args.out/name).write_text(json.dumps(value,indent=2)+"\n")
emit("bundle-program.json",{"jam":jam(BUNDLE),"abi":abi(8,[],[],sample=False)})
emit("bundle.noun.json",BUNDLE)
emit("expected.json",{
 "status":"expected native receiving results; generator authors nouns only",
 "dispatch":{"tally":2,"close":3},
 "implementations":[{"index":i,"arm":arm,"super":sup} for i,arm,sup in [(0,8,None),(1,9,None),(2,10,0),(3,11,1)]],
 "sample":{"context":[0,0,0],"targets":["ACTUAL_INSTANCE_TARGET"],
           "slots":[["votes",2]],"sourceSlot":"world/resource/field/3/count/before"},
 "baseClose":{"open":0,"tally":2,"dispatch":1,"derivedUnchanged":0},
 "close":{"derived":1,"open":0,"tally":2,"dispatch":1},
 "effectBindings":{"90":[2,0],"91":[4,0],"92":[6,0],"93":[7,0]},
 "registrationOrder":["bundle-program.json","base-program.json","close-program.json","poll-kind.json"],
 "programIds":"all IDs come from actual Host registration; no invented digests",
 "expectedStepCounts":"must be obtained from the actual source evaluator; not predicted here"})
if args.library_id:
    emit("base-program.json",{"jam":jam(slot(1)),"abi":abi(9,[args.library_id],BASE_OUTPUTS)})
    emit("close-program.json",{"jam":jam(slot(1)),"abi":abi(11,[args.library_id],CLOSE_OUTPUTS)})
if bool(args.base_program_id)!=bool(args.close_program_id):
    parser.error("both leaf IDs are required to author the world kind")
if args.base_program_id:
    if args.base_program_id==args.close_program_id: parser.error("distinct method entries need distinct leaf IDs")
    def field(i,name,meaning,codec="nat",discipline="ram"):
        return {"id":str(i),"name":name,"meaning":meaning,"codec":codec,"discipline":discipline}
    def binding(output,field): return {"output":str(output),"field":str(field),"key":"0"}
    base_bindings=[binding(90,2),binding(91,4),binding(92,6)]
    methods=[{"name":"base-close","program":args.base_program_id,"outputs":base_bindings},
             {"name":"close","program":args.close_program_id,"outputs":base_bindings+[binding(93,7)]}]
    emit("poll-kind.json",{"descriptor":{"revision":"1","fields":[
      field(2,"open","poll accepts votes"),field(3,"votes","one vote per key",discipline="append"),
      field(4,"tally","votes counted at closure"),
      field(5,"methods","dregg/world/method-table/v1","bytes","rom"),
      field(6,"dispatch","final-self customization observed"),
      field(7,"derived","derived close wrapper completed")]},
      "defaults":[{"field":str(f),"key":"0","value":str(v)} for f,v in [(2,1),(4,0),(6,0),(7,0)]]
        +[{"field":"5","key":"0","value":methods}]})

if args.instance_target:
    sample=((0,(0,0)),noun_list([(cord("target/0"),int(args.instance_target)),(cord("votes"),2)]))
    base_output=noun_list([(cord("open"),0),(cord("tally"),2),(cord("dispatch"),1)])
    close_output=((cord("derived"),1),base_output)
    emit("expected-bytes.json",{"instanceTarget":args.instance_target,
      "sample":jam(sample),"baseOutput":jam(base_output),"closeOutput":jam(close_output),
      "sampleNoun":sample,"baseOutputNoun":base_output,"closeOutputNoun":close_output})
