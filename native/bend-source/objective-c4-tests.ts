// C4 linearization: pommette.scm's published vectors, its refusals, and the
// ordered-presentation invariance property over enumerated small DAGs.
import {c4Linearize,C4Inconsistency} from "./objective-c4.ts";
const supers:Record<string,string[]>={};
for(const row of `O|A O|B O|C O|D O|E O|K1 A B C|K2 D B E|K3 D A|Z K1 K2 K3|J1 C A B|J2 B D E|J3 A D|Y J1 J3 J2|DB B|WB B|EL DB|SM DB|PWB EL WB|SC SM|P PWB SC|GL O|HG GL|VG GL|HVG HG VG|VHG VG HG|HH|GG HH|II GG|FF HH|EE HH|DD FF|CC EE FF GG|BB|AA BB CC DD|o O|a o|b a|c b o|d D c|M A B b a|N C c|L M N|k D L|j E k A|I N M|x1|x2 x1|x3 x2|x4 x3|x5 x4 x1|SBA|SBB|SBS SBA|sBs SBA|SBC SBS SBB`.split("|")){
 const [x,...ps]=row.split(" ");supers[x]=ps;
}
const isStruct=(x:string)=>x[0]>="a"&&x[0]<="z";
const memo=(get:(x:string)=>string[])=>{const cache=new Map<string,string[]>();const pl=(x:string):string[]=>{
 if(!cache.has(x))cache.set(x,c4Linearize([x],[get(x)],pl,isStruct).list);return cache.get(x)!;};return pl;};
const pl=memo(x=>supers[x]??[]);
const expected=`O|A O|B O|C O|D O|E O|K1 A B C O|K2 D B E O|K3 D A O|Z K1 K2 K3 D A B C E O|J1 C A B O|J2 B D E O|J3 A D O|Y J1 C J3 A J2 B D E O|DB B O|WB B O|EL DB B O|SM DB B O|PWB EL DB WB B O|SC SM DB B O|P PWB EL SC SM DB WB B O|GL O|HG GL O|VG GL O|HVG HG VG GL O|VHG VG HG GL O|HH|GG HH|II GG HH|FF HH|EE HH|DD FF HH|CC EE FF GG HH|BB|AA BB CC EE DD FF GG HH|o O|a o O|b a o O|c b a o O|d D c b a o O|M A B b a o O|N C c b a o O|L M A B N C c b a o O|k D L M A B N C c b a o O|j E k D L M A B N C c b a o O|I N C M A B c b a o O|x1|x2 x1|x3 x2 x1|x4 x3 x2 x1|x5 x4 x3 x2 x1|SBA|SBB|SBS SBA|sBs SBA|SBC SBS SBA SBB`.split("|");
for(const line of expected){const x=line.split(" ")[0];if(pl(x).join(" ")!==line)throw Error("C4 vector "+x+": "+pl(x).join(" ")+" expected "+line);}
const refuses=(f:()=>unknown,what:string)=>{try{f();}catch(e){if(e instanceof C4Inconsistency)return;throw e;}throw Error("accepted "+what);};
refuses(()=>memo(x=>x==="CG"?["HVG","VHG"]:supers[x]??[])("CG"),"CG inconsistent local orders");
refuses(()=>memo(x=>x==="SBc"?["sBs","SBB"]:supers[x]??[])("SBc"),"SBc incompatible suffix parents");
const dag=(order:string[][])=>c4Linearize([],order,pl,isStruct).list.join(" ");
for(const [order,want] of [[[["A"],["B"],["C"]],"A B C O"],[[["A","B"],["C","A"]],"C A B O"],[[["C","A"],["C","B"]],"C A B O"],[[["C","B"],["C","A"]],"C B A O"]] as const)
 if(dag(order as any)!==want)throw Error("DAG local order "+JSON.stringify(order)+": "+dag(order as any));
refuses(()=>dag([["A","B"],["B","C"],["C","A"]]),"cyclic local order");
console.log("C4 VECTORS PASS: "+expected.length+" pommette precedence lists, CG/SBc/cyclic refusals, 4 DAG local orders");

// Ordered-presentation invariance (scholar §5, proposed theorem): for every
// small DAG with ordered parent lists and suffix marks, renaming the nodes by
// any bijection renames the result (or the refusal) and changes nothing else;
// every accepted result satisfies inheritance order, local order, monotonicity
// and the suffix property.
type Graph={parents:number[][],suffix:boolean[]};
const run=(g:Graph,names:string[])=>{
 const key=new Map(names.map((n,i)=>[n,i]));const cache=new Map<string,string[]>();
 const pre=(x:string):string[]=>{if(!cache.has(x))cache.set(x,c4Linearize([x],[g.parents[key.get(x)!].map(i=>names[i])],pre,y=>g.suffix[key.get(y)!]).list);return cache.get(x)!;};
 return names.map(n=>{try{return pre(n);}catch(e){if(e instanceof C4Inconsistency)return null;throw e;}});
};
const isSubsequence=(sub:string[],list:string[])=>{let i=0;for(const x of list)if(x===sub[i])i++;return i===sub.length;};
let graphs=0,accepted=0,refused=0;let seed=20261004;
const random=()=>{seed=(seed*1103515245+12345)%2147483648;return seed/2147483648;};
for(let trial=0;trial<4000;trial++){
 const n=2+Math.floor(random()*6);
 const g:Graph={parents:[],suffix:[]};
 for(let i=0;i<n;i++){
  const pool=[...Array(i).keys()].filter(()=>random()<0.45);
  for(let j=pool.length-1;j>0;j--){const k=Math.floor(random()*(j+1));[pool[j],pool[k]]=[pool[k],pool[j]];}
  g.parents.push(pool);g.suffix.push(random()<0.25);
 }
 graphs++;
 const base=[...Array(n).keys()].map(i=>"n"+i),perm=[...Array(n).keys()].sort(()=>random()-0.5),renamed=perm.map(i=>"r"+i);
 const a=run(g,base),b=run(g,renamed);
 for(let i=0;i<n;i++){
  const want=a[i]?.map(x=>renamed[base.indexOf(x)])??null;
  if(JSON.stringify(want)!==JSON.stringify(b[i]))throw Error("ordered presentation not invariant under renaming: "+JSON.stringify(g));
  const p=a[i];if(!p){refused++;continue;}accepted++;
  if(p[0]!==base[i]||new Set(p).size!==p.length)throw Error("precedence list must start with the node and repeat nothing");
  for(const parent of g.parents[i]){
   const pp=a[parent];if(!pp)throw Error("accepted a node whose parent is inconsistent");
   if(!isSubsequence(pp,p))throw Error("monotonicity violated at n"+i+": "+JSON.stringify(g));
   if(p.indexOf(base[parent])<1)throw Error("inheritance order violated");
  }
  const ps=g.parents[i].map(j=>base[j]);if(!isSubsequence(ps,p))throw Error("local order violated at n"+i+": "+JSON.stringify(g));
  for(const x of p.slice(1)){const j=base.indexOf(x);if(g.suffix[j]){const sp=a[j]!;if(p.slice(p.length-sp.length).join()!==sp.join())throw Error("suffix property violated at n"+i+": "+JSON.stringify(g));}}
 }
}
console.log("C4 ORDERED-PRESENTATION INVARIANCE PASS: "+graphs+" random DAGs (seeded), "+accepted+" precedence lists satisfy inheritance/local order/monotonicity/suffix, "+refused+" refusals rename identically");
