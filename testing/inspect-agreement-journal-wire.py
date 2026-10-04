#!/usr/bin/env python3
# Diagnostic wire metadata only. Does not restore an engine state or validate authority.
import sys,json,hashlib,collections
from pathlib import Path
class Reader:
 def __init__(self,b):self.b=b;self.p=0
 def nat(self):
  n=0;k=1
  while True:
   d=self.b[self.p];self.p+=1
   if d==255:return n
   n+=d*k;k*=255
 def blob(self):
  n=self.nat();p=self.p;self.p+=n
  if self.p>len(self.b):raise ValueError('truncated blob')
  return self.b[p:self.p]
 def block(self):return [self.blob() for _ in range(self.nat())]
 def context(self):
  self.blob();self.nat();self.blob();c=[self.nat() for _ in range(4)];keys=[len(self.blob()) for _ in range(self.nat())];return c,keys
 def message(self):
  sender=self.nat();view=self.nat();kind=self.nat();tag=self.b[self.p];self.p+=1
  if tag not in (0,1):raise ValueError('argument tag')
  block=None if tag==0 else self.block()
  return sender,view,kind,block
 def end(self):
  if self.p!=len(self.b):raise ValueError('trailing bytes')
def summary(block):return [dict(length=len(b),sha256=hashlib.sha256(b).hexdigest()) for b in block if b]
for path in sys.argv[1:]:
 b=Path(path).read_bytes();r=Reader(b);config,keys=r.context();party=r.nat();initial=r.nat();events=[]
 for _ in range(r.nat()):events.append((r.nat(),r.blob()))
 witnesses=[]
 for _ in range(r.nat()):
  view=r.nat();block=r.block();signer=r.nat();sig=r.blob();witnesses.append(dict(view=view,signer=signer,blockLength=len(block),application=summary(block)))
 r.end();checked=[];offers=[];deliveries=[];ticks=[]
 for i,(tag,payload) in enumerate(events):
  e=Reader(payload)
  if tag==1:ticks.append(e.nat());e.end()
  elif tag==2:checked.append(dict(index=i,application=summary(e.block())));e.end()
  elif tag==3:offers.append(dict(index=i,length=len(payload),sha256=hashlib.sha256(payload).hexdigest()))
  elif tag in (0,5):
   t=e.nat() if tag==5 else None
   sender,view,kind,block=e.message();e.end();deliveries.append(dict(index=i,time=t,sender=sender,view=view,kind=kind,blockLength=None if block is None else len(block),application=None if block is None else summary(block)))
  elif tag!=4:raise ValueError('event tag')
 print(json.dumps(dict(party=party,bytes=len(b),events=len(events),eventTags=dict(collections.Counter(t for t,_ in events)),lastTick=ticks[-1:] or None,offers=offers,checked=checked,maxDeliveredView=max([d["view"] for d in deliveries],default=0),highestDeliveries=[d for d in deliveries if d["view"]>=6][-12:],latestDeliveries=deliveries[-12:],witnesses=witnesses),sort_keys=True),flush=True)
