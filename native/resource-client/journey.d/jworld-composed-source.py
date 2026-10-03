#!/usr/bin/env python3
"""Member source authoring for inherited final-self/super variants; no evaluator."""
import argparse,json
from pathlib import Path
ns={}
exec(Path(__file__).with_name('jworld-prototype.py').read_text().split('parser=argparse.ArgumentParser()')[0],ns)
p=argparse.ArgumentParser()
p.add_argument('--out',type=Path,required=True)
p.add_argument('--mark',type=int,default=1)
p.add_argument('--revision',type=int,default=1)
p.add_argument('--kind')
p.add_argument('--library-id')
p.add_argument('--base-program-id')
p.add_argument('--close-program-id')
a=p.parse_args();a.out.mkdir(parents=True,exist_ok=True)
quote=ns['quote'];select=ns['select'];inherited=ns['inherited'];effect=ns['effect']
ns['BODIES'][2]=(select(inherited(),2),quote(a.mark))
ns['BODIES'][3]=(effect('derived',quote(a.mark)),inherited())
cs=[ns['constructor'](body,index) for index,body in enumerate(ns['BODIES'])]
bundle=(((cs[0],cs[1]),(cs[2],cs[3])),(ns['DISPATCH'],ns['IMPLEMENTATIONS']))
def emit(name,value): (a.out/name).write_text(json.dumps(value,indent=2)+'\n')
emit('bundle.json',{'jam':ns['jam'](bundle),'abi':ns['abi'](8,[],[],False)})
if a.library_id:
    emit('base.json',{'jam':ns['jam'](ns['slot'](1)),'abi':ns['abi'](9,[a.library_id],ns['BASE_OUTPUTS'])})
    emit('close.json',{'jam':ns['jam'](ns['slot'](1)),'abi':ns['abi'](11,[a.library_id],ns['CLOSE_OUTPUTS'])})
if a.base_program_id and a.close_program_id:
    def field(i,name,meaning,codec='nat',discipline='ram'):
        return {'id':str(i),'name':name,'meaning':meaning,'codec':codec,'discipline':discipline}
    def binding(out,field): return {'output':str(out),'field':str(field),'key':'0'}
    common=[binding(90,2),binding(91,4),binding(92,6)]
    descriptor={'revision':str(a.revision),'fields':[
        field(2,'open','poll accepts votes'),field(3,'votes','one vote per key',discipline='append'),
        field(4,'tally','votes counted at closure'),field(5,'methods','dregg/world/method-table/v1','bytes','rom'),
        field(6,'dispatch','final-self customization observed'),field(7,'derived','derived close wrapper completed')]}
    if a.kind: descriptor['kind']=a.kind
    emit('kind.json',{'descriptor':descriptor,'defaults':[
        {'field':str(f),'key':'0','value':str(v)} for f,v in [(2,1),(4,0),(6,0),(7,0)]]+[
        {'field':'5','key':'0','value':[
            {'name':'base-close','program':a.base_program_id,'outputs':common},
            {'name':'close','program':a.close_program_id,'outputs':common+[binding(93,7)]}]}]})
