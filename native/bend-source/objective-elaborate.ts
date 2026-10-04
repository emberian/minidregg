// Objective Bend source elaboration, edition 1. Produces the actual Core4 Term
// consumed by ObjectiveBendDemandMachine and, separately, a proposal of lambda
// annotations for the proof-producing checker. Annotations are proposals: only
// the Lean checker's Checked result types a term. Laws stay retained closures.
import {readFile,writeFile} from "node:fs/promises";
import {createHash} from "node:crypto";
import {parseObjective} from "./objective-parser.ts";
import {c4Linearize,C4Inconsistency} from "./objective-c4.ts";
type Core={tag:string,[key:string]:any};
type Ty={tag:string,[key:string]:any};
const term=(tag:string,fields:any={}):Core=>({tag,...fields});
const nat=(n:string|number)=>term("nat",{value:String(n)});
const label=(value:string)=>term("label",{value});
const app=(fn:Core,arg:Core)=>term("app",{fn,arg});
const record=(fields:{name:string,value:Core}[])=>term("record",{fields});
const get=(target:Core,name:string)=>term("get",{target,name});
const bound=(index:number)=>term("bound",{index});
const sha=(bytes:Uint8Array|string)=>createHash("sha256").update(bytes).digest("hex");
const failure=(node:any,message:string):never=>{throw {schema:"dregg.bend.compiler-diagnostic.v1",stage:"objective-core-elaboration",message,span:node?.span??null};};
const duplicate=(names:string[])=>new Set(names).size!==names.length;

// ---- types (the Lean `Ty` JSON wire of Theory.ObjectiveBendTyping.typeJson) ----
const T={
 natural:{tag:"natural"} as Ty,boolean:{tag:"boolean"} as Ty,label:{tag:"label"} as Ty,emptyRow:{tag:"emptyRow"} as Ty,
 variable:(index:number):Ty=>({tag:"variable",index:String(index)}),
 arrow:(domain:Ty,codomain:Ty,parameter="unrestricted",reuse="reusable"):Ty=>({tag:"arrow",reuse,parameter,domain,codomain}),
 spec:(metadata:Ty,extension:Ty):Ty=>({tag:"specification",metadata,extension}),
 row:(fields:{name:string,type:Ty}[],tail:Ty={tag:"emptyRow"}):Ty=>fields.reduceRight((rest,f)=>({tag:"field",name:f.name,member:f.type,tail:rest}),tail),
};
const extensionTy=(target:Ty)=>T.arrow(target,T.arrow(target,target));
const callable=(t:Ty|null):Ty|null=>t&&t.tag==="specification"?callable(t.extension):t;
const lookupRow=(t:Ty|null,name:string):Ty|null=>{while(t&&t.tag==="field"){if(t.name===name)return t.member;t=t.tail;}return null;};
const sameTy=(a:Ty|null,b:Ty|null)=>a!==null&&b!==null&&canonicalJson(canonicalTy(a))===canonicalJson(canonicalTy(b));
const canonicalJson=(v:any):string=>JSON.stringify(v&&typeof v==="object"?Array.isArray(v)?v.map(x=>JSON.parse(canonicalJson(x))):Object.fromEntries(Object.keys(v).sort().map(k=>[k,JSON.parse(canonicalJson(v[k]))])):v);
// Mirrors Ty.canonical: rows sorted by name with first-field shadowing.
const canonicalTy=(t:Ty):Ty=>{
 if(t.tag==="arrow")return {...t,domain:canonicalTy(t.domain),codomain:canonicalTy(t.codomain)};
 if(t.tag==="specification")return {...t,metadata:canonicalTy(t.metadata),extension:canonicalTy(t.extension)};
 if(t.tag==="prototype")return {...t,spec:canonicalTy(t.spec),target:canonicalTy(t.target)};
 if(t.tag==="variant")return {...t,row:canonicalTy(t.row)};
 if(t.tag==="computation")return {...t,plan:canonicalTy(t.plan),response:canonicalTy(t.response),result:canonicalTy(t.result)};
 if(t.tag==="field"){
  const insert=(row:Ty,name:string,member:Ty):Ty=>row.tag!=="field"?{tag:"field",name,member,tail:row}:
   name===row.name?{tag:"field",name,member,tail:row.tail}:name<row.name?{tag:"field",name,member,tail:row}:{...row,tail:insert(row.tail,name,member)};
  return insert(canonicalTy(t.tail),t.name,canonicalTy(t.member));
 }
 return t;
};
// A lambda proposal: domain/codomain may be null (unresolved); literalAnnotations
// then refuses with the recorded reason instead of guessing a type.
type LamProposal={domain:Ty|null,codomain:Ty|null,parameter:string,reuse:string,reason?:string};
const proposals=new WeakMap<Core,LamProposal>();
const lam=(body:Core,proposal?:LamProposal)=>{const t=term("lam",{body});if(proposal)proposals.set(t,proposal);return t;};
// Injection proposals: each `inject` is annotated at its own path in the
// ordinary annotations list as the constructor-function type
// payload -> variant (SUMS-DESIGN §11).
const injections=new WeakMap<Core,{type:Ty|null,reason?:string}>();
// Activities (EVENTS-DESIGN A4): `perform` and the elaborator-inserted `done`
// carry the enclosing activity's Plan and Response types at their own path.
const effects=new WeakMap<Core,{plan:Ty,response:Ty}>();
const isComputation=(t:Ty|null)=>t?.tag==="computation";

// Source quantity -> checker quantity. `default`/`copy` are unrestricted.
export const quantityOf=(p:any):string=>{
 switch(p.quantity??"default"){
  case "default":case "copy":return "unrestricted";
  case "dead":return "erased";
  case "affine":return "affine";
  case "linear":return "linear";
  default:return failure(p,"unsupported source quantity "+p.quantity);
 }
};
const restricted=(q:string)=>q==="affine"||q==="linear";

// Operators the parser accepts whose core constructor does not exist yet.
// Each refusal names the constructor it waits for.
const awaiting:Record<string,string>={
 "<":"`<` needs a Nat order primitive (Primitive.less) in Core4; none exists",
 ">":"`>` needs a Nat order primitive (Primitive.less) in Core4; none exists",
 "<=":"`<=` needs a Nat order primitive (Primitive.less) in Core4; none exists",
 ">=":"`>=` needs a Nat order primitive (Primitive.less) in Core4; none exists",
 "-":"`-` needs a truncated-subtraction primitive (Primitive.subtract) in Core4; none exists",
 "/":"`/` needs a division primitive (Primitive.divide, with a stated zero-divisor meaning) in Core4; none exists",
};
const primitives:Record<string,{primitive:string,input:Ty,output:Ty}>={
 "+":{primitive:"add",input:T.natural,output:T.natural},"*":{primitive:"multiply",input:T.natural,output:T.natural},
 "==":{primitive:"equal",input:T.natural,output:T.boolean},"&&":{primitive:"conjunction",input:T.boolean,output:T.boolean},
};

type Binding={name:string,ty:Ty|null,quantity:string};
const declName=(d:any)=>d.name??d.signature.name;

export function elaborate(modules:any[],entryModule:number,entryDefinition:string,args:any,mode:"application"|"definition"="application"){
 const declarations=new Map<string,{d:any,m:any}>();
 for(const m of modules)for(const d of m.ast.declarations)if(d.kind!=="record"&&d.kind!=="sum"){
  const key=m.name+"."+declName(d);if(declarations.has(key))failure(d,"duplicate declaration "+key);declarations.set(key,{d,m});
 }
 const records=new Map<string,any>();
 const sums=new Map<string,any>();
 for(const m of modules)for(const d of m.ast.declarations){
  if(d.kind==="record"||d.kind==="sum"){const key=m.name+"."+d.name;if(records.has(key)||sums.has(key))failure(d,"duplicate type "+key);
   (d.kind==="record"?records:sums).set(key,d);}
 }
 // Recursive sums are rigid variables (index ≥ 1) bounded by their variant row;
 // each is a shareability premise (SUMS-DESIGN §5, §9).
 const sumVariables=new Map<string,number>();const sumBounds=new Map<number,Ty>();
 const resolveTypeKey=(name:string,moduleName:string):{key:string,moduleName:string}|null=>{
  const qualified=/^([A-Za-z_]\w*)\.([A-Za-z_]\w*)$/.exec(name);
  if(!qualified)return {key:moduleName+"."+name,moduleName};
  const m=modules.find(x=>x.name===moduleName);const imported=m&&importOf(m,qualified[1]);
  return imported?{key:imported.moduleName+"."+qualified[2],moduleName:imported.moduleName}:null;
 };
 const importOf=(m:any,alias:string)=>m.imports.find((i:any)=>i.alias===alias);

 // ---- source types ----
 const splitTop=(text:string,sep:string):string[]=>{
  const parts:string[]=[];let depth=0,start=0;
  for(let i=0;i<text.length;i++){const c=text[i];if("<({".includes(c))depth++;else if(">)}".includes(c)&&!(c===">"&&text[i-1]==="-"))depth--;
   else if(depth===0&&text.startsWith(sep,i)){parts.push(text.slice(start,i));start=i+sep.length;i+=sep.length-1;}}
  parts.push(text.slice(start));return parts.map(p=>p.trim());
 };
 const typeErrors:string[]=[];
 const sourceType=(name:string,moduleName:string,seen:string[]=[]):Ty|null=>{
  name=name.trim();
  if(name==="_"||name==="")return null;
  const arrows=splitTop(name,"->");
  if(arrows.length>1){let t=sourceType(arrows[arrows.length-1],moduleName,seen);
   for(let i=arrows.length-2;i>=0;i--){const d=sourceType(arrows[i],moduleName,seen);t=d&&t?T.arrow(d,t):null;}return t;}
  if(name.startsWith("(")&&name.endsWith(")"))return sourceType(name.slice(1,-1),moduleName,seen);
  if(name.startsWith("{")&&name.endsWith("}")){const inner=name.slice(1,-1).trim();if(!inner)return T.emptyRow;
   const fs=splitTop(inner,",").map(f=>{const m=/^([A-Za-z_]\w*)\s*:\s*(.+)$/.exec(f);return m?{name:m[1],type:sourceType(m[2],moduleName,seen)}:null;});
   return fs.every(f=>f&&f.type)?T.row(fs as {name:string,type:Ty}[]):null;}
  if(name==="Nat")return T.natural;if(name==="Bool")return T.boolean;if(name==="String")return T.label;
  const activity=/^Activity<(.+)>$/.exec(name);
  if(activity){const parts=splitTop(activity[1],",");if(parts.length!==3){typeErrors.push("Activity<Plan, Response, Result> takes three types");return null;}
   const [plan,response,result]=parts.map(x=>sourceType(x,moduleName,seen));
   return plan&&response&&result?{tag:"computation",plan,response,result}:null;}
  const generic=/^(Extension|Specification)<(.+)>$/.exec(name);
  if(generic){const target=sourceType(generic[2],moduleName,seen);if(!target)return null;
   return generic[1]==="Extension"?extensionTy(target):T.spec(specMetadataTy(T.emptyRow),extensionTy(target));}
  const qualified=/^([A-Za-z_]\w*)\.([A-Za-z_]\w*)$/.exec(name);
  if(qualified){const m=modules.find(x=>x.name===moduleName);const imported=m&&importOf(m,qualified[1]);
   if(!imported){typeErrors.push("unresolved source type import "+name);return null;}
   return sourceType(qualified[2],imported.moduleName,seen);}
  const key=moduleName+"."+name;
  const sum=sums.get(key);
  if(sum){
   if(seen.includes(key)){if(!sumVariables.has(key))sumVariables.set(key,sumVariables.size+1);return T.variable(sumVariables.get(key)!);}
   if(sumVariables.has(key)&&sumBounds.has(sumVariables.get(key)!))return T.variable(sumVariables.get(key)!);
   const cases=sum.cases.map((c:any)=>({name:c.label,type:sourceType(c.type,moduleName,[...seen,key])}));
   if(cases.some((c:any)=>!c.type))return null;
   const variant:Ty={tag:"variant",row:T.row(cases)};
   if(sumVariables.has(key)){const k=sumVariables.get(key)!;sumBounds.set(k,variant);return T.variable(k);}
   return variant;
  }
  if(seen.includes(key)){typeErrors.push("recursive row annotation requires explicit future-row binder: "+key);return null;}
  const d=records.get(key);if(!d){typeErrors.push("unsupported source type "+name);return null;}
  const fields=[...d.fields.map((f:any)=>({name:f.name,type:sourceType(f.type,moduleName,[...seen,key])})),
   ...d.methods.map((f:any)=>({name:f.name,type:signatureTy(f.parameters,f.resultType,moduleName,[...seen,key])}))];
  if(fields.some((f:any)=>!f.type))return null;
  return T.row(fields as {name:string,type:Ty}[]);
 };
 // Curried arrows. Once an affine/linear parameter is bound, every later closure
 // captures it and is one-shot; the arrow type records that.
 const signatureTy=(ps:any[],result:string|Ty|null,moduleName:string,seen:string[]=[]):Ty|null=>{
  let t:Ty|null=typeof result==="string"?sourceType(result,moduleName,seen):result;
  for(let i=ps.length-1;i>=0;i--){
   const d=sourceType(ps[i].type,moduleName,seen);if(!d||!t)return null;
   const once=ps.slice(0,i).some((p:any)=>restricted(quantityOf(p)));
   t=T.arrow(d,t,quantityOf(ps[i]),once?"once":"reusable");
  }return t;
 };
 const specMetadataTy=(laws:Ty)=>T.row([{name:"name",type:T.label},{name:"interface",type:T.label},{name:"laws",type:laws}]);

 // ---- declaration types (the global row members) ----
 const globalTypes=new Map<string,Ty|null>();const inferring=new Set<string>();
 const globalType=(key:string):Ty|null=>{
  if(globalTypes.has(key))return globalTypes.get(key)!;
  if(inferring.has(key)){typeErrors.push("result inference cycle through "+key+"; annotate its result type");return null;}
  const entry=declarations.get(key);if(!entry)return null;
  inferring.add(key);const {d,m}=entry;let t:Ty|null=null;
  if(d.kind==="function"){
   let result:Ty|null=sourceType(d.signature.resultType,m.name);
   if(d.signature.resultType==="_"){
    const env:Binding[]=[...d.signature.parameters].reverse().map((p:any)=>({name:p.name,ty:sourceType(p.type,m.name),quantity:quantityOf(p)}));
    result=synthBody(d.body,env,m);
    if(!result)typeErrors.push("result inference requires an annotation for "+key);
   }
   t=signatureTy(d.signature.parameters,result,m.name);
  }else if(d.kind==="extension")t=signatureTy(d.parameters,d.targetType,m.name);
  else if(d.kind==="spec"){
   const target=sourceType(d.targetType,m.name);
   const laws=d.laws.map((law:any)=>({name:law.name,type:signatureTy([{name:"self",type:d.targetType},{name:"super",type:d.targetType},...law.parameters],T.boolean,m.name)}));
   t=target&&laws.every((l:any)=>l.type)?T.spec(specMetadataTy(T.row(laws)),extensionTy(target)):null;
  }
  inferring.delete(key);globalTypes.set(key,t);return t;
 };
 const lookupGlobal=(name:string,m:any):string|null=>{const key=m.name+"."+name;return declarations.has(key)?key:null;};

 // ---- type synthesis over source expressions (for result inference and compose sharing) ----
 const composeTy=(left:Ty|null,right:Ty|null):Ty|null=>{
  const l=callable(left),r=callable(right);
  if(!left||!right||l?.tag!=="arrow"||r?.tag!=="arrow"||l.codomain.tag!=="arrow"||r.codomain.tag!=="arrow")return null;
  const meta=T.row([{name:"operator",type:T.label},{name:"inherited",type:left},{name:"wrapping",type:right}]);
  return T.spec(meta,T.arrow(l.domain,T.arrow(l.codomain.domain,r.codomain.codomain)));
 };
 // `Sum.label(payload)` / `Alias.Sum.label(payload)`: the callee names a sum case.
 const sumCase=(callee:any,env:Binding[],m:any):{key:string,moduleName:string,sum:any,label:string}|null=>{
  if(callee.kind!=="member")return null;
  let typeName:string|null=null;
  if(callee.target.kind==="var"&&!env.some(b=>b.name===callee.target.name))typeName=callee.target.name;
  else if(callee.target.kind==="member"&&callee.target.target.kind==="var"&&!env.some(b=>b.name===callee.target.target.name)&&importOf(m,callee.target.target.name))
   typeName=callee.target.target.name+"."+callee.target.name;
  if(!typeName)return null;
  const resolved=resolveTypeKey(typeName,m.name);if(!resolved)return null;
  const sum=sums.get(resolved.key);if(!sum)return null;
  return {key:resolved.key,moduleName:resolved.moduleName,sum,label:callee.name};
 };
 const sumTypeOf=(c:{key:string,moduleName:string,sum:any})=>sourceType(c.sum.name,c.moduleName);
 const variantRow=(t:Ty|null):Ty|null=>{if(t?.tag==="computation")return variantRow(t.result);if(t?.tag==="variable"){const b=sumBounds.get(Number(t.index));return b?.tag==="variant"?b.row:null;}return t?.tag==="variant"?t.row:null;};
 // The Plan/Response of the definition being lowered (null outside an activity).
 let currentEffect:{plan:Ty,response:Ty}|null=null;
 const isPerform=(e:any,env:Binding[],m:any)=>e.kind==="call"&&e.callee.kind==="var"&&e.callee.name==="perform"&&!env.some(b=>b.name==="perform")&&!lookupGlobal("perform",m);
 const synth=(e:any,env:Binding[],m:any):Ty|null=>{
  switch(e.kind){
   case "nat":return T.natural;case "bool":return T.boolean;case "string":return T.label;case "unit":return T.emptyRow;
   case "var":{const b=env.find(x=>x.name===e.name);if(b)return b.ty;const key=lookupGlobal(e.name,m);return key?globalType(key):null;}
   case "member":{
    if(e.target.kind==="var"&&!env.some(x=>x.name===e.target.name)){const imported=importOf(m,e.target.name);
     if(imported)return globalType(imported.moduleName+"."+e.name);}
    return lookupRow(synth(e.target,env,m),e.name);
   }
   case "record":{const fs=e.fields.map((f:any)=>({name:f.name,type:synth(f.value,env,m)}));return fs.every((f:any)=>f.type)?T.row(fs):null;}
   case "binary":{
    if(e.op==="!="||e.op==="==")return T.boolean;
    if(e.op==="||")return sameTy(synth(e.left,env,m),T.boolean)&&sameTy(synth(e.right,env,m),T.boolean)?T.boolean:null;
    const p=primitives[e.op];if(!p)return null;
    return sameTy(synth(e.left,env,m),p.input)&&sameTy(synth(e.right,env,m),p.input)?p.output:null;}
   case "if":{const a=synth(e.whenTrue,env,m),b=synth(e.whenFalse,env,m);return a&&b&&sameTy(a,b)?a:null;}
   case "compose":{let t=synth(e.specifications[0],env,m);for(const next of e.specifications.slice(1))t=composeTy(t,synth(next,env,m));return t;}
   case "fix":{const s=callable(synth(e.specification,env,m));return s?.tag==="arrow"?s.domain:null;}
   case "lambda":case "extension-value":return signatureTy(e.parameters,e.targetType??e.resultType,m.name);
   case "call":{
    if(isPerform(e,env,m))return currentEffect?{tag:"computation",plan:currentEffect.plan,response:currentEffect.response,result:currentEffect.response}:null;
    {const c=sumCase(e.callee,env,m);if(c)return sumTypeOf(c);}
    if(e.callee.kind==="var"&&["reflect","metadata","targetOf","prototype"].includes(e.callee.name)&&!env.some(x=>x.name===e.callee.name))return null;
    let t=synth(e.callee,env,m);for(const _ of e.args){t=callable(t);if(t?.tag!=="arrow")return null;t=t.codomain;}return t;
   }
   default:return null;
  }
 };
 const synthBody=(b:any,env:Binding[],m:any):Ty|null=>{
  if(b.kind==="expression")return synth(b.expression,env,m);
  if(b.branches.some((x:any)=>x.pattern.kind==="constructor"||x.pattern.kind==="bool")){
   const scrutineeTy=synth(b.scrutinee,env,m);const row=variantRow(scrutineeTy);
   let types=b.branches.map((x:any)=>synthBody(x.body,x.pattern.kind==="constructor"?[{name:x.pattern.binder,ty:lookupRow(row,x.pattern.label),quantity:"unrestricted"},...env]:env,m));
   // An activity scrutinee makes the whole match an activity; pure arms are lifted.
   if(isComputation(scrutineeTy)||types.some(isComputation))types=types.map((t:Ty|null)=>!t||isComputation(t)||!currentEffect?t:{tag:"computation",plan:currentEffect.plan,response:currentEffect.response,result:t});
   return types.every((t:Ty|null)=>t&&sameTy(t,types[0]))?types[0]:null;
  }
  const zero=b.branches.find((x:any)=>x.pattern.kind==="zero"),succ=b.branches.find((x:any)=>x.pattern.kind==="succ");
  if(!zero||!succ)return null;
  const z=synthBody(zero.body,env,m),s=synthBody(succ.body,[{name:succ.pattern.binder,ty:T.natural,quantity:"unrestricted"},...env],m);
  return z&&s&&sameTy(z,s)?z:null;
 };

 // ---- term elaboration ----
 const globalsIndex=(env:Binding[])=>env.findIndex(b=>b.name==="$globals");
 const lookup=(name:string,env:Binding[],m:any,node:any):Core=>{
  const index=env.findIndex(b=>b.name===name);if(index>=0)return bound(index);
  const key=lookupGlobal(name,m);if(key)return get(bound(globalsIndex(env)),key);
  return failure(node,"unbound source variable "+name);
 };
 // Curried lambdas; each carries its checker proposal. Reuse is `once` when any
 // visible lexical binding (outer or earlier parameter) is affine or linear.
 const abstract=(parameters:any[],env:Binding[],lower:(next:Binding[])=>Core,node:any,resultType:string|Ty|null,moduleName:string):Core=>{
  if(duplicate(parameters.map(p=>p.name)))failure(node,"duplicate lexical parameter");
  const bindings:Binding[]=parameters.map(p=>({name:p.name,ty:typeof p.ty==="object"&&p.ty?p.ty:sourceType(p.type??"_",moduleName),quantity:quantityOf(p)}));
  const inner=[...bindings].reverse().concat(env);
  let codomain:Ty|null=typeof resultType==="string"?sourceType(resultType,moduleName):resultType;
  // A body whose declared result is an Activity is lowered in effect mode.
  const saved=currentEffect;currentEffect=codomain?.tag==="computation"?{plan:codomain.plan,response:codomain.response}:null;
  let value:Core;try{value=lower(inner);}finally{currentEffect=saved;}
  for(let i=parameters.length-1;i>=0;i--){
   const visible=[...bindings.slice(0,i),...env];
   const reuse=visible.some(b=>restricted(b.quantity))?"once":"reusable";
   const reason=bindings[i].ty===null?"parameter "+parameters[i].name+" has no resolvable type":codomain===null?"result type of "+(node?.name??node?.signature?.name??node?.kind)+" is not resolvable":undefined;
   value=lam(value,{domain:bindings[i].ty,codomain,parameter:bindings[i].quantity,reuse,reason});
   codomain=bindings[i].ty&&codomain?T.arrow(bindings[i].ty!,codomain,bindings[i].quantity,reuse):null;
  }return value;
 };
 // Named refusals: an activity never occupies a shared (suspended) position.
 const noActivity=(e:any,env:Binding[],m:any,rule:string,why:string)=>{
  // Outside an activity only a literal perform is checked here (the checker refuses the rest), so
  // packages without activities elaborate exactly as before; inside one, synthesis names the rule.
  if(isPerform(e,env,m)||(currentEffect&&isComputation(synth(e,env,m))))failure(e,"refused ("+rule+"): an Activity cannot be used here; "+why+", so its effect would be cached and shared. Match on it first.");
 };
 // A tail position of an activity body: pure results are lifted with `done`.
 const tail=(e:any,env:Binding[],m:any):Core=>{
  if(!currentEffect)return expression(e,env,m);
  if(e.kind==="if")return term("ifBool",{condition:expression(e.condition,env,m),whenTrue:tail(e.whenTrue,env,m),whenFalse:tail(e.whenFalse,env,m)});
  if(isPerform(e,env,m)||isComputation(synth(e,env,m)))return expression(e,env,m);
  const t=term("done",{value:expression(e,env,m)});effects.set(t,currentEffect);return t;
 };
 const expression=(e:any,env:Binding[],m:any):Core=>{
  switch(e.kind){
   case "var":return lookup(e.name,env,m,e);
   case "nat":return nat(e.value);
   case "bool":return term("boolean",{value:e.value});
   case "string":return label(e.value);
   case "unit":return record([]);
   case "member":{
    if(e.target.kind==="var"&&!env.some(b=>b.name===e.target.name)){
     const imported=importOf(m,e.target.name);
     if(imported){const key=imported.moduleName+"."+e.name;if(!declarations.has(key))failure(e,"missing imported declaration "+key);
      return get(bound(globalsIndex(env)),key);}
    }
    return get(expression(e.target,env,m),e.name);
   }
   case "record":if(duplicate(e.fields.map((f:any)=>f.name)))failure(e,"duplicate record field");
    for(const f of e.fields)noActivity(f.value,env,m,"effect-in-field","a record field is a shared lazy cell");
    return record(e.fields.map((f:any)=>({name:f.name,value:expression(f.value,env,m)})));
   case "extend":if(duplicate(e.fields.map((f:any)=>f.name)))failure(e,"duplicate provided field");
    for(const f of e.fields)noActivity(f.value,env,m,"effect-in-field","an extended field is a shared lazy cell");
    return term("extend",{inherited:expression(e.inherited,env,m),fields:e.fields.map((f:any)=>({name:f.name,value:expression(f.value,env,m)}))});
   case "lambda":case "extension-value":return abstract(e.parameters,env,next=>expression(e.body,next,m),e,e.targetType??e.resultType,m.name);
   case "binary":{
    if(e.op==="=="||e.op==="!="){
     // Nat operands keep `equal`; String operands lower to `labelEqual`; unknown types are refused.
     const l=synth(e.left,env,m),r=synth(e.right,env,m);
     const not=(x:Core)=>term("ifBool",{condition:x,whenTrue:term("boolean",{value:false}),whenFalse:term("boolean",{value:true})});
     if(sameTy(l,T.boolean)&&sameTy(r,T.boolean)){
      // Bool equality: (λr. if a then r else not r) b. The right operand is
      // bound once (no term duplication); `a` is elaborated under the binder.
      const right=expression(e.right,env,m);
      const left=expression(e.left,[{name:"$right",ty:T.boolean,quantity:"unrestricted"},...env],m);
      const eq=app(lam(term("ifBool",{condition:left,whenTrue:bound(0),whenFalse:not(bound(0))}),
       {domain:T.boolean,codomain:T.boolean,parameter:"unrestricted",reuse:env.some(b=>restricted(b.quantity))?"once":"reusable"}),right);
      return e.op==="=="?eq:not(eq);
     }
     const primitive=sameTy(l,T.natural)&&sameTy(r,T.natural)?"equal":sameTy(l,T.label)&&sameTy(r,T.label)?"labelEqual":null;
     if(!primitive)failure(e,e.op+" needs both operands' types resolved to Nat, String or Bool (annotate the parameters)");
     const eq=term("binary",{primitive,left:expression(e.left,env,m),right:expression(e.right,env,m)});
     return e.op==="=="?eq:not(eq);
    }
    if(e.op==="||")return term("ifBool",{condition:expression(e.left,env,m),whenTrue:term("boolean",{value:true}),whenFalse:expression(e.right,env,m)});
    const p=primitives[e.op];
    if(!p)return failure(e,"operator "+e.op+" is not yet a core constructor: "+(awaiting[e.op]??"unknown operator"));
    return term("binary",{primitive:p.primitive,left:expression(e.left,env,m),right:expression(e.right,env,m)});
   }
   case "if":return term("ifBool",{condition:expression(e.condition,env,m),whenTrue:expression(e.whenTrue,env,m),whenFalse:expression(e.whenFalse,env,m)});
   case "compose":{
    // compose(a,b) = (λl. λr. specification({operator, inherited: l, wrapping: r}, mix l r)) a b.
    // The inherited composite is bound ONCE and shared by metadata and mix:
    // term size is linear in the number of composed specifications.
    if(!e.specifications.length)failure(e,"empty composition requires an explicit identity extension");
    let value=expression(e.specifications[0],env,m);let valueTy=synth(e.specifications[0],env,m);
    for(const next of e.specifications.slice(1)){
     const right=expression(next,env,m),rightTy=synth(next,env,m),composite=composeTy(valueTy,rightTy);
     const reason=composite?undefined:"composition operand types are not resolvable as extensions";
     const body=term("specification",{metadata:record([{name:"operator",value:label("compose")},
       {name:"inherited",value:bound(1)},{name:"wrapping",value:bound(0)}]),extension:term("mix",{lower:bound(1),upper:bound(0)})});
     const inner=lam(body,{domain:rightTy,codomain:composite,parameter:"unrestricted",reuse:"reusable",reason});
     const outer=lam(inner,{domain:valueTy,codomain:rightTy&&composite?T.arrow(rightTy,composite):null,parameter:"unrestricted",reuse:"reusable",reason});
     value=app(app(outer,value),right);valueTy=composite;
    }return value;
   }
   case "fix":return term("fix",{spec:expression(e.specification,env,m),seed:expression(e.inherited,env,m)});
   case "call":{
    if(isPerform(e,env,m)){
     if(!currentEffect)failure(e,"refused (perform-outside-activity): perform needs an enclosing definition whose result type is Activity<Plan, Response, Result>");
     if(e.args.length!==1)failure(e,"perform takes exactly one Plan");
     noActivity(e.args[0],env,m,"effect-in-plan","a Plan is data");
     const t=term("perform",{plan:expression(e.args[0],env,m)});effects.set(t,currentEffect!);return t;
    }
    const c=sumCase(e.callee,env,m);
    if(c){
     if(!c.sum.cases.some((x:any)=>x.label===c.label))failure(e,"sum "+c.key+" has no case "+c.label);
     if(e.args.length>1)failure(e,"a sum case carries one payload; use a record");
     if(e.args.length)noActivity(e.args[0],env,m,"effect-in-payload","a sum payload is a shared lazy cell");
     const t=term("inject",{label:c.label,payload:e.args.length?expression(e.args[0],env,m):record([])});
     const type=sumTypeOf(c);injections.set(t,{type,reason:type?undefined:"sum "+c.key+" type unresolved"});return t;
    }
    if(e.callee.kind==="var"&&!env.some(b=>b.name===e.callee.name)&&!lookupGlobal(e.callee.name,m)){
     const name=e.callee.name;
     if(["reflect","metadata","targetOf"].includes(name)){
      if(e.args.length!==1)failure(e,name+" expects one argument");
      return term(name==="targetOf"?"project":name,{value:expression(e.args[0],env,m)});
     }
     if(name==="prototype"){
      if(e.args.length!==2)failure(e,"prototype expects spec and lazy target");
      return term("prototype",{spec:expression(e.args[0],env,m),target:expression(e.args[1],env,m)});
     }
    }
    for(const arg of e.args)noActivity(arg,env,m,"effect-as-argument","an argument is a shared lazy thunk");
    let fn=expression(e.callee,env,m);for(const arg of e.args)fn=app(fn,expression(arg,env,m));return fn;
   }
   default:return failure(e,"unsupported Objective expression "+e.kind);
  }
 };
 const body=(b:any,env:Binding[],m:any):Core=>{
  if(b.kind==="expression")return tail(b.expression,env,m);
  if(b.kind!=="match")failure(b,"unsupported body "+b.kind);
  if(b.branches.some((x:any)=>x.pattern.kind==="bool")){
   const t=b.branches.find((x:any)=>x.pattern.kind==="bool"&&x.pattern.value),f=b.branches.find((x:any)=>x.pattern.kind==="bool"&&!x.pattern.value);
   if(b.branches.length!==2||!t||!f)failure(b,"Bool match requires exactly true and false branches");
   return term("ifBool",{condition:expression(b.scrutinee,env,m),whenTrue:body(t.body,env,m),whenFalse:body(f.body,env,m)});
  }
  if(b.branches.some((x:any)=>x.pattern.kind==="constructor")){
   if(!b.branches.every((x:any)=>x.pattern.kind==="constructor"))failure(b,"a sum match takes only label(binder) cases; wildcards are refused (no default arm)");
   if(duplicate(b.branches.map((x:any)=>x.pattern.label)))failure(b,"duplicate sum case");
   const row=variantRow(synth(b.scrutinee,env,m));
   if(row){const labels:string[]=[];for(let r=row;r.tag==="field";r=r.tail)labels.push(r.name);
    const missing=labels.filter(l=>!b.branches.some((x:any)=>x.pattern.label===l)),extra=b.branches.filter((x:any)=>!labels.includes(x.pattern.label)).map((x:any)=>x.pattern.label);
    if(missing.length||extra.length)failure(b,"sum match is not exhaustive: missing ["+missing.join(", ")+"], unknown ["+extra.join(", ")+"]");}
   return term("case",{scrutinee:expression(b.scrutinee,env,m),arms:b.branches.map((x:any)=>({label:x.pattern.label,
    body:body(x.body,[{name:x.pattern.binder,ty:lookupRow(row,x.pattern.label),quantity:"unrestricted"},...env],m)}))});
  }
  const zero=b.branches.find((x:any)=>x.pattern.kind==="zero");
  const succ=b.branches.find((x:any)=>x.pattern.kind==="succ");
  // Edition 1 lowering refuses ambiguous match patterns instead of silently
  // discarding wildcards, duplicate cases or source-order semantics.
  if(b.branches.length!==2||!zero||!succ)failure(b,"Nat match currently requires exactly zero and successor branches");
  return term("ifZero",{value:expression(b.scrutinee,env,m),zero:body(zero.body,env,m),
   successor:body(succ.body,[{name:succ.pattern.binder,ty:T.natural,quantity:"unrestricted"},...env],m)});
 };
 const outer:Binding[]=[{name:"$seed",ty:T.emptyRow,quantity:"unrestricted"},{name:"$globals",ty:T.variable(0),quantity:"unrestricted"}];
 function resultOf(t:Ty|null,arity:number):Ty|null{for(let i=0;i<arity;i++){if(t?.tag!=="arrow")return null;t=t.codomain;}return t;}
 // ---- specifications, declared ancestry and method combination ----
 // Identity is static and generative: the qualified declaration key. A spec's
 // precedence list is the C4 linearization of its declared parents; its
 // effective extension is the mix chain of its ancestors' own layers, least
 // specific lowest: init layers for simple combinations, then primary layers,
 // then around layers (standard method combination, ltuo §9.2.5).
 const specKey=(name:string,m:any,node:any):string=>{
  const q=/^([A-Za-z_]\w*)\.([A-Za-z_]\w*)$/.exec(name);
  let key=m.name+"."+name;
  if(q){const imported=importOf(m,q[1]);if(!imported)failure(node,"unknown import alias in spec parent "+name);key=imported.moduleName+"."+q[2];}
  if(declarations.get(key)?.d.kind!=="spec")failure(node,"spec parent "+name+" is not a spec declaration");
  return key;
 };
 const precedenceMemo=new Map<string,string[]>();const linearizing=new Set<string>();
 const precedence=(key:string):string[]=>{
  if(precedenceMemo.has(key))return precedenceMemo.get(key)!;
  const {d,m}=declarations.get(key)!;
  if(linearizing.has(key))failure(d,"spec ancestry cycle through "+key);
  linearizing.add(key);
  let list:string[]=[];
  try{list=c4Linearize([key],[d.parents.map((p:string)=>specKey(p,m,d))],precedence,(k:string)=>declarations.get(k)!.d.suffix===true).list;}
  catch(e){if(e instanceof C4Inconsistency)failure(d,"C4 linearization of "+key+" refused: "+e.message);throw e;}
  linearizing.delete(key);precedenceMemo.set(key,list);return list;
 };
 const combinations:Record<string,{primitive:string,zero:Core}>={
  "+":{primitive:"add",zero:nat(0)},"*":{primitive:"multiply",zero:nat(1)},"and":{primitive:"conjunction",zero:term("boolean",{value:true})},
 };
 const qualifierGroup=(q:string)=>q==="around"?"around":"primary";
 const checkSpecMethods=(d:any)=>{
  for(const method of d.methods)if(method.qualifier==="before"||method.qualifier==="after")
   failure(method,method.qualifier+" methods run for their effects and discard their result; Objective Bend core has no effect constructor yet (perform/yield, scout A move 2), so a pure "+method.qualifier+" method would be silently discarded");
  for(const group of ["primary","around"]){const names=d.methods.filter((x:any)=>qualifierGroup(x.qualifier??"primary")===group).map((x:any)=>x.name);
   if(duplicate(names))failure(d,"duplicate "+group+" method");}
 };
 const hasLayer=(d:any,group:string)=>d.methods.some((x:any)=>qualifierGroup(x.qualifier??"primary")===group);
 const plain=(d:any)=>!d.parents.length&&!hasLayer(d,"around")&&d.methods.every((x:any)=>(x.qualifier??"primary")==="primary");
 const selfSuperOf=(target:Ty|null):Binding[]=>[{name:"super",ty:target,quantity:"unrestricted"},{name:"self",ty:target,quantity:"unrestricted"},...outer];
 const layer=(d:any,m:any,group:string):Core=>{
  const selfSuper=selfSuperOf(sourceType(d.targetType,m.name));
  const methods=d.methods.filter((x:any)=>qualifierGroup(x.qualifier??"primary")===group).map((method:any)=>{
   const q=method.qualifier??"primary",combination=combinations[q];
   return {name:method.name,value:abstract(method.parameters,selfSuper,inner=>{
    const own=body(method.body,inner,m);if(!combination)return own;
    // A simple-combination method: own result op the next method's result.
    let next=get(bound(method.parameters.length),method.name);
    for(let i=0;i<method.parameters.length;i++)next=app(next,bound(method.parameters.length-1-i));
    return term("binary",{primitive:combination.primitive,left:own,right:next});
   },method,method.resultType,m.name)};
  });
  return abstract([{name:"self",type:d.targetType},{name:"super",type:d.targetType}],outer,
   ()=>term("extend",{inherited:bound(0),fields:methods}),d,d.targetType,m.name);
 };
 const layerRef=(key:string,group:string):Core=>{
  const {d}=declarations.get(key)!;
  return get(bound(globalsIndex(outer)),plain(d)&&group==="primary"?key:key+"#"+group);
 };
 const hidden:{name:string,value:Core,type:Ty|null}[]=[];
 function specification(d:any,m:any):Core{
  checkSpecMethods(d);
  const key=m.name+"."+d.name,target=sourceType(d.targetType,m.name);
  const list=precedence(key);
  let extension:Core;
  if(plain(d))extension=layer(d,m,"primary");
  else{
   for(const ancestor of list){const a=declarations.get(ancestor)!;
    if(target&&!sameTy(sourceType(a.d.targetType,a.m.name),target))failure(d,"ancestor "+ancestor+" targets "+a.d.targetType+"; declared ancestry composes one target type ("+d.targetType+")");}
   for(const group of ["primary","around"])if(hasLayer(d,group))
    hidden.push({name:key+"#"+group,value:layer(d,m,group),type:target?extensionTy(target):null});
   // Simple combinations: every primary-group method of one name across the
   // precedence list must share one qualifier; the combination's identity is
   // the bottom layer.
   const qualifiers=new Map<string,{q:string,method:any,moduleName:string}>();
   for(const ancestor of list)for(const method of declarations.get(ancestor)!.d.methods){
    const q=method.qualifier??"primary";if(qualifierGroup(q)!=="primary")continue;
    const prior=qualifiers.get(method.name);
    if(prior&&prior.q!==q)failure(d,"method "+method.name+" is "+prior.q+" in one ancestor and "+q+" in another of "+key);
    if(!prior)qualifiers.set(method.name,{q,method,moduleName:declarations.get(ancestor)!.m.name});
   }
   const layers:Core[]=[];
   for(const [name,{q,method,moduleName}] of qualifiers){const combination=combinations[q];if(!combination)continue;
    // The identity method is typed in the module that declared the signature.
    const init=abstract(method.parameters,selfSuperOf(target),()=>combination.zero,method,method.resultType,moduleName);
    layers.push(abstract([{name:"self",type:d.targetType},{name:"super",type:d.targetType}],outer,
     ()=>term("extend",{inherited:bound(0),fields:[{name,value:init}]}),d,d.targetType,m.name));
   }
   const reversed=[...list].reverse();
   for(const group of ["primary","around"])for(const ancestor of reversed)
    if(hasLayer(declarations.get(ancestor)!.d,group))layers.push(layerRef(ancestor,group));
   if(!layers.length)failure(d,"spec "+key+" and its ancestors provide no methods");
   if(layers.length===1)extension=abstract([{name:"self",type:d.targetType},{name:"super",type:d.targetType}],outer,
     ()=>app(app(shift(layers[0],2),bound(1)),bound(0)),d,d.targetType,m.name);
   else extension=layers.slice(1).reduce((lower,upper)=>term("mix",{lower,upper}),layers[0]);
  }
  // Reflection retains actual law bodies as callable values and complete
  // authored interfaces as immutable labels. Retention is not proof discharge.
  const laws=d.laws.map((law:any)=>({name:law.name,value:abstract([{name:"self",type:d.targetType},{name:"super",type:d.targetType},...law.parameters],outer,
     inner=>expression(law.body,inner,m),law,"Bool",m.name)}));
  return term("specification",{metadata:record([{name:"name",value:label(key)},
     {name:"interface",value:label(canonicalJson({targetType:d.targetType,suffix:d.suffix,parents:d.parents,precedence:list,requirements:d.requirements,
         methods:d.methods.map(({body,...signature}:any)=>signature)}))},{name:"laws",value:record(laws)}]),extension});
 }
 // Free de Bruijn indices of a closed-over-outer reference shift under binders.
 function shift(t:Core,by:number):Core{
  if(t.tag==="get"&&t.target.tag==="bound")return get(bound(t.target.index+by),t.name);
  return failure(null,"internal: only global references are shifted");
 }
 const fields:{name:string,value:Core}[]=[];
 for(const m of modules)for(const d of m.ast.declarations){
  let value:Core;
  if(d.kind==="record"||d.kind==="sum")continue;
  const key=m.name+"."+declName(d);
  if(d.kind==="function"&&!d.signature.parameters.length&&/^Activity</.test(d.signature.resultType.trim()))
   failure(d,"refused (nullary-activity): "+key+" has no parameters, so it is a shared lazy value; an Activity needs a parameter, e.g. (start: {})");
  if(d.kind==="function")value=abstract(d.signature.parameters,outer,next=>body(d.body,next,m),d,
   d.signature.resultType==="_"?((globalType(key) as any)?.tag?resultOf(globalType(key),d.signature.parameters.length):null):d.signature.resultType,m.name);
  else if(d.kind==="extension")value=abstract(d.parameters,outer,next=>body(d.body,next,m),d,d.targetType,m.name);
  else if(d.kind==="spec")value=specification(d,m);
  else failure(d,"unsupported declaration "+d.kind);
  fields.push({name:key,value:value!});
  for(const h of hidden.splice(0)){fields.push({name:h.name,value:h.value});globalTypes.set(h.name,h.type);}
 }
 // The global knot: fix(spec(meta, λ$globals. λ$seed. extend $seed {M.decl: …}), {}). $globals is the
 // rigid row variable 0, bounded by the row of every declaration's type.
 const globalRowFields=fields.map(f=>({name:f.name,type:globalType(f.name)}));
 const globalRow=globalRowFields.every(f=>f.type)?T.row(globalRowFields as {name:string,type:Ty}[]):null;
 const knotReason=globalRow?undefined:"declaration types unresolved: "+globalRowFields.filter(f=>!f.type).map(f=>f.name).join(", ");
 // The package root is itself a specification: its extension overlays the
 // declarations on the inherited row (super), so a package is a first-class
 // extensible value, not a closed record (scout A finding 4).
 const rootExtension=lam(lam(term("extend",{inherited:bound(0),fields}),{domain:T.emptyRow,codomain:T.variable(0),parameter:"unrestricted",reuse:"reusable",reason:knotReason}),
  {domain:T.variable(0),codomain:T.arrow(T.emptyRow,T.variable(0)),parameter:"unrestricted",reuse:"reusable",reason:knotReason});
 const rootSpecification=term("specification",{metadata:record([{name:"package",value:label(canonicalJson(modules.map(m=>m.name)))}]),extension:rootExtension});
 const root=term("fix",{spec:rootSpecification,seed:record([])});
 const entry=modules[entryModule];if(!entry||!declarations.has(entry.name+"."+entryDefinition))failure(null,"missing selected entry");
 let selected=get(root,entry.name+"."+entryDefinition);
 const argument=(a:any):Core=>{
  if(typeof a==="string"&&/^(0|[1-9][0-9]*)$/.test(a))return nat(a);
  if(typeof a==="boolean")return term("boolean",{value:a});
  if(a&&typeof a==="object"&&!Array.isArray(a))return record(Object.keys(a).sort().map(name=>({name,value:argument(a[name])})));
  return failure(null,"runtime arguments are canonical decimal Nat strings, Bool or records");
 };
 const exactKeys=(value:any,expected:string[])=>value&&typeof value==="object"&&!Array.isArray(value)&&
   Object.keys(value).sort().join("\0")===expected.slice().sort().join("\0");
 const typedArgument=(a:any):Core=>{
  if(a?.tag==="natural"&&exactKeys(a,["tag","value"])&&typeof a.value==="string"&&/^(0|[1-9][0-9]*)$/.test(a.value))return nat(a.value);
  if(a?.tag==="boolean"&&exactKeys(a,["tag","value"])&&typeof a.value==="boolean")return term("boolean",{value:a.value});
  if(a?.tag==="label"&&exactKeys(a,["tag","value"])&&typeof a.value==="string")return label(a.value);
  if(a?.tag==="record"&&exactKeys(a,["tag","fields"])&&Array.isArray(a.fields)){
   if(a.fields.some((f:any)=>!exactKeys(f,["name","value"])||typeof f.name!=="string")||duplicate(a.fields.map((f:any)=>f.name)))
    failure(null,"typed record arguments require exact distinct named fields");
   return record(a.fields.map((f:any)=>({name:f.name,value:typedArgument(f.value)})));
  }
  return failure(null,"malformed typed argument value; no implicit Nat/String coercion");
 };
 let argumentCodec:string;
 if(mode==="definition"){
  if(!Array.isArray(args)||args.length!==0)failure(null,"definition mode forbids invocation arguments");
  argumentCodec="unapplied-definition";
 }else if(Array.isArray(args)){
  argumentCodec="legacy-canonical-nat-bool-record";
  for(const arg of args)selected=app(selected,argument(arg));
 }else if(exactKeys(args,["schema","values"])&&args.schema==="dregg.objective-bend.argument-values.v1"&&Array.isArray(args.values)){
  argumentCodec="dregg.objective-bend.argument-values.v1";
  for(const arg of args.values)selected=app(selected,typedArgument(arg));
 }else failure(null,"arguments must select a supported complete value envelope");
 const output:any={schema:"dregg.objective-bend.core.v2",edition:"objective-bend-1",term:selected,
   sourceEntry:entry.name+"."+entryDefinition,argumentCodec,selectionMode:mode,sourceModules:modules.map(m=>({name:m.name,sourceSha256:m.sha256,astSha256:m.astSha256,imports:m.imports})),
   declarationASTs:modules.map(m=>m.ast),status:"elaborated executable term; new typing and demand adequacy unqualified"};
 // Non-enumerable: the typing proposal travels with the in-process output only.
 Object.defineProperty(output,"typing",{value:{globalRow,typeErrors,sumBounds},enumerable:false});
 return output;
}

// ---- the shared type table of a typing proposal ----
// A proposal names types through a table: every composite type (arrow, field,
// specification, prototype, variant, computation) is ONE table entry whose
// children are either inline leaves or `{tag:"ref",index}` to an earlier entry,
// and identical entries are stored once. A fully expanded type of a record whose
// fields are records of records is exponential in its depth; the table is linear
// in the number of DISTINCT types. The order is part of the contract (the Lean
// elaborator reproduces it for translation validation): entries are created in
// post-order (children before parent, children in the fixed order listed in
// `typeChildren`), walking the annotations in order (domain, then codomain),
// then the bounds, then the context.
const typeChildren:Record<string,string[]>={arrow:["domain","codomain"],field:["member","tail"],specification:["metadata","extension"],
 prototype:["spec","target"],variant:["row"],computation:["plan","response","result"]};
const isLeafTy=(t:Ty)=>["natural","boolean","label","emptyRow","variable","custody"].includes(t.tag);
export function typeTable(){
 const table:any[]=[];const seen=new Map<string,number>();const memo=new Map<object,any>();
 const intern=(t:Ty):any=>{
  if(isLeafTy(t))return t;
  const hit=memo.get(t);if(hit)return hit;
  const children=typeChildren[t.tag];if(!children)throw Error("unknown type constructor "+t.tag);
  const node:any={...t};for(const key of children)node[key]=intern(t[key]);
  const key=canonicalJson(node);let index=seen.get(key);
  if(index===undefined){index=table.length;table.push(node);seen.set(key,index);}
  const ref={tag:"ref",index:String(index)};memo.set(t,ref);return ref;
 };
 return {table,intern};
}
// Inverse of typeTable for tests and tools: every `ref` replaced by the entry it names.
// The result can be exponentially larger than the packet; never call it on a large proposal.
export function expandTypes(packet:any):any{
 const expand=(t:any):any=>{
  if(t.tag==="ref")return expand(packet.types[Number(t.index)]);
  const children=typeChildren[t.tag];if(!children)return t;
  const node:any={...t};for(const key of children)node[key]=expand(t[key]);return node;
 };
 const {types,...rest}=packet;
 return {...rest,annotations:packet.annotations.map((a:any)=>({...a,domain:expand(a.domain),codomain:expand(a.codomain)})),
  bounds:packet.bounds.map((b:any)=>({...b,type:expand(b.type)})),context:packet.context.map((c:any)=>({...c,type:expand(c.type)}))};
}

// Source annotations are proposals. The Lean checker must construct a derivation
// for the exact emitted term; this never mints a typing receipt.
export function literalAnnotations(output:any){
 try{
  const typing=output.typing;if(!typing)throw Error("typing proposal requires the in-process elaboration output");
  const annotations:any[]=[];const {table,intern}=typeTable();
  const visit=(t:Core,path:number[])=>{
   if(t.tag==="lam"){
    const p=proposals.get(t);
    if(!p)throw Error("lambda at "+path.join(".")+" has no proposal");
    if(!p.domain||!p.codomain)throw Error(p.reason??(typing.typeErrors[0]??"unresolved lambda type at "+path.join(".")));
    annotations.push({path:path.map(String),domain:intern(p.domain),codomain:intern(p.codomain),parameter:p.parameter,reuse:p.reuse});
    visit(t.body,[...path,0]);return;
   }
   const sub=(name:string,index:number)=>visit(t[name],[...path,index]);
   if(t.tag==="app"){sub("fn",0);sub("arg",1);}else if(t.tag==="fix"){sub("spec",0);sub("seed",1);}
   else if(t.tag==="mix"){sub("lower",0);sub("upper",1);}else if(t.tag==="binary"){sub("left",0);sub("right",1);}
   else if(t.tag==="prototype"){sub("spec",0);sub("target",1);}else if(t.tag==="specification"){sub("metadata",0);sub("extension",1);}
   else if(["reflect","metadata","project"].includes(t.tag))sub("value",0);
   else if(t.tag==="get")sub("target",0);
   else if(t.tag==="ifZero"){sub("value",0);sub("zero",1);sub("successor",2);}
   else if(t.tag==="ifBool"){sub("condition",0);sub("whenTrue",1);sub("whenFalse",2);}
   else if(t.tag==="inject"){
    const p=injections.get(t);if(!p?.type)throw Error(p?.reason??"injection at "+path.join(".")+" has no declared sum type");
    const variant=p.type.tag==="variable"?typing.sumBounds.get(Number(p.type.index)):p.type;
    const payload=variant?.tag==="variant"?lookupRow(variant.row,t.label):null;
    if(!payload)throw Error("injection label "+t.label+" absent from its declared sum");
    // The codomain is the DECLARED sum type: a recursive sum stays its bounded variable.
    annotations.push({path:path.map(String),domain:intern(payload),codomain:intern(p.type),parameter:"unrestricted",reuse:"reusable"});sub("payload",0);
   }
   else if(t.tag==="perform"||t.tag==="done"){
    const e=effects.get(t);if(!e)throw Error(t.tag+" at "+path.join(".")+" has no activity signature");
    annotations.push({path:path.map(String),domain:intern(e.plan),codomain:intern(e.response),parameter:"unrestricted",reuse:"reusable"});
    sub(t.tag==="perform"?"plan":"value",0);
   }
   else if(t.tag==="case"){sub("scrutinee",0);t.arms.forEach((a:any,i:number)=>visit(a.body,[...path,1,i]));}
   else if(t.tag==="record")t.fields.forEach((f:any,i:number)=>visit(f.value,[...path,i]));
   else if(t.tag==="extend"){sub("inherited",0);t.fields.forEach((f:any,i:number)=>visit(f.value,[...path,1,i]));}
  };
  visit(output.term,[]);
  if(!typing.globalRow)throw Error(typing.typeErrors[0]??"global row unresolved");
  const globalBound={index:"0",type:intern(typing.globalRow)};
  const sumBounds=[...typing.sumBounds.entries()].sort((a:any,b:any)=>a[0]-b[0]).map(([k,type]:any)=>({index:String(k),type:intern(type)}));
  const bounds=[globalBound,...sumBounds];
  return {schema:"dregg.objective-bend.typed-core.v3",term:output.term,types:table,annotations,
   bounds,shareableVariables:["0",...sumBounds.map((b:any)=>b.index)],fuel:output.limits?.typeFuel??"4096",context:[],
   sourceEntry:output.sourceEntry,sourceModules:output.sourceModules,
   status:"exact core annotation proposal; actual checker must return Checked; no law proof or effect authority"};
 }catch(e){return {status:"unsupported",message:e instanceof Error?e.message:String(e)};}
}

if(import.meta.main){
 try{
  const [capturePath,outPrefix,argsRaw="[]",projectionRaw="[]",limitsRaw='{"heap":"100000","stack":"100000","ticks":"100000"}',mode="application"]=process.argv.slice(2);
  if(!capturePath||!outPrefix)throw Error("usage: objective-elaborate CAPTURE_JSON OUTPUT_PREFIX [ARGUMENTS_JSON] [PROJECTIONS_JSON] [LIMITS_JSON] [application|definition]");
  if(mode!=="application"&&mode!=="definition")throw Error("selection mode must be application or definition");
  if(mode==="definition"&&(!Array.isArray(JSON.parse(projectionRaw))||JSON.parse(projectionRaw).length!==0))throw Error("definition mode forbids result projections");
  const limits=JSON.parse(limitsRaw);
  for(const key of ["heap","stack","ticks"])if(typeof limits[key]!=="string"||!/^[1-9][0-9]*$/.test(limits[key])||BigInt(limits[key])>1000000n)throw Error("preview limits must be canonical positive decimal strings ≤1000000");
  // The checker fuel travels in the proposal itself (its `fuel` field), so the packet the elaborator writes is exactly the packet the checker reads.
  if(limits.typeFuel!==undefined&&(typeof limits.typeFuel!=="string"||!/^[1-9][0-9]*$/.test(limits.typeFuel)||BigInt(limits.typeFuel)>16384n))throw Error("typeFuel must be a canonical positive decimal string ≤16384");
  const capture=JSON.parse(await readFile(capturePath,"utf8"));
  if(!Array.isArray(capture.modules)||capture.modules.length>64)throw Error("preview module capacity refused");
  if(capture.schema!=="dregg.objective-bend.captured-package.v1"||capture.edition!=="objective-bend-1")throw Error("unsupported captured edition");
  if(capture.parserSourceSha256&&sha(await readFile(new URL("./objective-parser.ts",import.meta.url)))!==capture.parserSourceSha256)throw Error("parser snapshot differs from captured parser");
  const modules=[];
  for(const [index,m] of capture.modules.entries()){
   const source=await readFile(m.sourcePath);const astBytes=await readFile(m.astPath);
   if(source.length>2097152||astBytes.length>4194304)throw Error("preview source/AST capacity refused");
   const sourceText=new TextDecoder("utf-8",{fatal:true}).decode(source);
   if(sha(source)!==m.sha256||sha(astBytes)!==m.astSha256)throw Error("captured source/AST hash mismatch "+m.name);
   const ast=JSON.parse(astBytes.toString());if(JSON.stringify(parseObjective(sourceText))!==JSON.stringify(ast))throw Error("source reparse mismatch "+m.name);
   if(JSON.stringify(m.imports.map(({path,alias,span}:any)=>({path,alias,span})))!==JSON.stringify(ast.imports))throw Error("import transcript differs from parsed imports");
   for(const i of m.imports)if(!/^(0|[1-9][0-9]*)$/.test(i.module)||Number(i.module)>=index||
     capture.modules[Number(i.module)].name!==i.moduleName||capture.modules[Number(i.module)].sha256!==i.sha256)throw Error("invalid locked import");
   modules.push({...m,ast});
  }
  const output=elaborate(modules,Number(capture.entryModule),capture.entryDefinition,JSON.parse(argsRaw),mode as any);
  output.limits=limits;
  for(const projection of JSON.parse(projectionRaw)){
   if(projection.field)output.term=get(output.term,projection.field);
   if(projection.argument!==undefined){if(!/^(0|[1-9][0-9]*)$/.test(projection.argument))throw Error("projection argument must be canonical Nat");output.term=app(output.term,nat(projection.argument));}
  }
  await writeFile(outPrefix+".typed.json",JSON.stringify(literalAnnotations(output),null,2)+"\n");
  await writeFile(outPrefix+".core.json",JSON.stringify(output,null,2)+"\n");
  console.log(JSON.stringify({schema:output.schema,sourceEntry:output.sourceEntry,outputPrefix:outPrefix,coreSha256:sha(JSON.stringify(output)),status:output.status}));
 }catch(e){console.error(JSON.stringify(e instanceof Error?{message:e.message}:e));process.exitCode=1;}
}
