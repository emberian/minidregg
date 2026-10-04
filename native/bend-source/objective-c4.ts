// C4 linearization (ltuo §7.4.4): C3 plus the suffix property. A port of
// pommette.scm `c4-linearize` (metareflection/poof, sha256 3403e04a…).
// Specifications are identified by declaration identity (generative, static):
// the caller passes keys, so a diamond's shared ancestor appears once while
// compose(E, E) still applies E twice.
export class C4Inconsistency extends Error{}

export type C4Result<T>={list:T[],suffix:T|null};

/** head: prefix to prepend (usually [x]); parents: local precedence chains
 * (each a total order; together a DAG); precedence(x) starts with x itself. */
export function c4Linearize<T>(head:T[],parentsIn:T[][],precedence:(x:T)=>T[],isSuffix:(x:T)=>boolean,name:(x:T)=>string=String):C4Result<T>{
 const parents=parentsIn.filter(p=>p.length>0);
 const superSuffix=(x:T):T|null=>precedence(x).slice(1).find(isSuffix)??null;
 if(parents.length===0)return {list:[...head],suffix:null};
 if(parents.length===1&&parents[0].length===1){
  const parent=parents[0][0];return {list:[...head,...precedence(parent)],suffix:isSuffix(parent)?parent:superSuffix(parent)};
 }
 let rcandidates:T[][]=[];let ss:T|null=null;let ssTail:T[]=[];
 const err=(...detail:string[]):never=>{throw new C4Inconsistency("inconsistent precedence graph at "+head.map(name).join(",")+": "+detail.join(" "));};
 const isSuperSuffix=(s1:T|null,s2:T|null):boolean=>{if(s2===null)return true;for(let s=s1;s!==null;s=superSuffix(s))if(s===s2)return true;return false;};
 const mergeSuffix=(s1:T|null,s2:T|null):T|null=>{
  if(s2===null)return s1;if(s1===null)return s2;
  for(let t1:T|null=s1,t2:T|null=s2;;t1=superSuffix(t1!),t2=superSuffix(t2!)){
   if(t1===s2)return s1;if(t2===s1)return s2;
   if(t1===null)return isSuperSuffix(t2,s1)?s2:err("suffix incompatibility",name(s1),name(s2));
   if(t2===null)return isSuperSuffix(t1,s2)?s1:err("suffix incompatibility",name(s1),name(s2));
  }
 };
 const counts=new Map<T,number>();
 const count=(c:T)=>counts.get(c)??0;const inc=(c:T)=>counts.set(c,count(c)+1);const dec=(c:T)=>counts.set(c,count(c)-1);
 for(const chain of parents)for(const parent of chain){
  if(count(parent)!==0)continue;
  let r:T[]=[];
  for(const al of [precedence(parent)]){
   let i=0;
   for(;i<al.length;i++){
    if(isSuffix(al[i])){
     const merged=mergeSuffix(al[i],ss);
     if(merged!==ss){for(const t of al.slice(i)){if(t===ss)break;inc(t);}ss=merged;ssTail=al.slice(i);}
     break;
    }
    inc(al[i]);r=[al[i],...r];
   }
   if(r.length)rcandidates=[r,...rcandidates];
  }
 }
 const tailIndex=new Map<T,number>();ssTail.forEach((t,j)=>tailIndex.set(t,ssTail.length-j));
 const rLocalOrder=parents.filter(chain=>chain.length>1).map(chain=>[...chain].reverse());
 for(const chain of rLocalOrder)for(const c of chain)inc(c);
 rcandidates=[...rLocalOrder,...rcandidates];
 // Re-reverse each reversed candidate list, removing suffix-tail elements, which
 // must appear in increasing tail-index order.
 const removeSuffixTailAndReverse=(rcl:T[]):T[]=>{
  let suffixPos=-1;
  for(let i=0;i<rcl.length;i++){
   const p=tailIndex.get(rcl[i]);
   if(p===undefined){
    let j=i+1;const h:T[]=[rcl[i]];
    while(j<rcl.length&&!tailIndex.has(rcl[j])){h.unshift(rcl[j]);j++;}
    if(j<rcl.length)err("ancestor out of order versus suffix tail",name(rcl[j]));
    return h;
   }
   if(p>suffixPos)suffixPos=p;else err("ancestor out of order versus suffix tail",name(rcl[i]));
  }
  return [];
 };
 const candidates=rcandidates.map(removeSuffixTailAndReverse).filter(l=>l.length>0).reverse();
 for(const cl of candidates)dec(cl[0]);
 const out:T[]=[...head];let tails=candidates;
 while(true){
  if(tails.length===0)return {list:[...out,...ssTail],suffix:ss};
  if(tails.length===1)return {list:[...out,...tails[0],...ssTail],suffix:ss};
  const winner=tails.find(t=>count(t[0])===0);
  if(!winner)return err("no C3 candidate",tails.map(t=>t.map(name).join(" ")).join(" | "));
  const next=winner[0];out.push(next);
  tails=tails.map(t=>{if(t[0]!==next)return t;if(t.length>1)dec(t[1]);return t.slice(1);}).filter(t=>t.length>0);
 }
}
