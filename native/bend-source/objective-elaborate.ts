// Objective Bend source elaboration, edition 1. This produces the actual Term
// consumed by ObjectiveBendDemandMachine.run. It does not claim typing/adequacy
// or authorize effects. The full source AST, annotations and laws stay retained.
import {readFile,writeFile} from "node:fs/promises";
import {createHash} from "node:crypto";
import {parseObjective} from "./objective-parser.ts";
type Core={tag:string,[key:string]:any};
const term=(tag:string,fields:any={}):Core=>({tag,...fields});
const nat=(n:string|number)=>term("nat",{value:String(n)});
const label=(value:string)=>term("label",{value});
const app=(fn:Core,arg:Core)=>term("app",{fn,arg});
const lam=(body:Core)=>term("lam",{body});
const record=(fields:{name:string,value:Core}[])=>term("record",{fields});
const get=(target:Core,name:string)=>term("get",{target,name});
const sha=(bytes:Uint8Array|string)=>createHash("sha256").update(bytes).digest("hex");
const failure=(node:any,message:string):never=>{throw {schema:"dregg.bend.compiler-diagnostic.v1",stage:"objective-core-elaboration",message,span:node?.span??null};};
const duplicate=(names:string[])=>new Set(names).size!==names.length;
export function elaborate(modules:any[],entryModule:number,entryDefinition:string,args:any[]){
 const globals=new Set<string>();
 for(const m of modules)for(const d of m.ast.declarations)if(d.kind!=="record"){
  const key=m.name+"."+(d.name??d.signature.name);if(globals.has(key))failure(d,"duplicate declaration "+key);globals.add(key);
 }
 const lookup=(name:string,env:string[],m:any,node:any):Core=>{
  const index=env.indexOf(name);if(index>=0)return term("bound",{index});
  const key=m.name+"."+name;if(globals.has(key))return get(term("bound",{index:env.indexOf("$globals")}),key);
  return failure(node,"unbound source variable "+name);
 };
 const abstract=(parameters:any[],env:string[],lower:(next:string[])=>Core,node:any):Core=>{
  if(duplicate(parameters.map(p=>p.name)))failure(node,"duplicate lexical parameter");
  let value=lower([...parameters.map(p=>p.name).reverse(),...env]);
  for(let i=parameters.length-1;i>=0;i--)value=lam(value);return value;
 };
 const expression=(e:any,env:string[],m:any):Core=>{
  switch(e.kind){
   case "var":return lookup(e.name,env,m,e);
   case "nat":return nat(e.value);
   case "bool":return label(e.value?"true":"false");
   case "string":return label(e.value);
   case "unit":return record([]);
   case "member":{
    if(e.target.kind==="var"&&!env.includes(e.target.name)){
     const imported=m.imports.find((i:any)=>i.alias===e.target.name);
     if(imported){const key=imported.moduleName+"."+e.name;if(!globals.has(key))failure(e,"missing imported declaration "+key);
      return get(term("bound",{index:env.indexOf("$globals")}),key);}
    }
    return get(expression(e.target,env,m),e.name);
   }
   case "record":if(duplicate(e.fields.map((f:any)=>f.name)))failure(e,"duplicate record field");
    return record(e.fields.map((f:any)=>({name:f.name,value:expression(f.value,env,m)})));
   case "extend":if(duplicate(e.fields.map((f:any)=>f.name)))failure(e,"duplicate provided field");
    return term("extend",{inherited:expression(e.inherited,env,m),fields:e.fields.map((f:any)=>({name:f.name,value:expression(f.value,env,m)}))});
   case "lambda":case "extension-value":return abstract(e.parameters,env,next=>expression(e.body,next,m),e);
   case "binary":{
    const primitive={"+":"add","*":"multiply","==":"equal","&&":"conjunction"}[e.op];
    if(!primitive)failure(e,"unsupported primitive "+e.op);
    return term("binary",{primitive,left:expression(e.left,env,m),right:expression(e.right,env,m)});
   }
   case "compose":{
    if(!e.specifications.length)failure(e,"empty composition requires an explicit identity extension");
    let value=expression(e.specifications[0],env,m);
    for(const next of e.specifications.slice(1)){
     const right=expression(next,env,m);
     value=term("specification",{metadata:record([{name:"operator",value:label("compose")},
       {name:"inherited",value},{name:"wrapping",value:right}]),
       extension:term("mix",{lower:value,upper:right})});
    }return value;
   }
   case "fix":return term("fix",{spec:expression(e.specification,env,m),seed:expression(e.inherited,env,m)});
   case "call":{
    if(e.callee.kind==="var"){
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
    let fn=expression(e.callee,env,m);for(const arg of e.args)fn=app(fn,expression(arg,env,m));return fn;
   }
   default:return failure(e,"unsupported Objective expression "+e.kind);
  }
 };
 const body=(b:any,env:string[],m:any):Core=>{
  if(b.kind==="expression")return expression(b.expression,env,m);
  if(b.kind!=="match")failure(b,"unsupported body "+b.kind);
  const zero=b.branches.find((x:any)=>x.pattern.kind==="zero");
  const succ=b.branches.find((x:any)=>x.pattern.kind==="succ");
  // Edition 1 lowering refuses ambiguous match patterns instead of silently
  // discarding wildcards, duplicate cases or source-order semantics.
  if(b.branches.length!==2||!zero||!succ)failure(b,"Nat match currently requires exactly zero and successor branches");
  return term("ifZero",{value:expression(b.scrutinee,env,m),zero:body(zero.body,env,m),
   successor:body(succ.body,[succ.pattern.binder,...env],m)});
 };
 const fields:{name:string,value:Core}[]=[];
 for(const m of modules)for(const d of m.ast.declarations){
  const outer=["$seed","$globals"];let value:Core;
  if(d.kind==="record")continue;
  if(d.kind==="function")value=abstract(d.signature.parameters,outer,next=>body(d.body,next,m),d);
  else if(d.kind==="extension")value=abstract(d.parameters,outer,next=>body(d.body,next,m),d);
  else if(d.kind==="spec"){
   if(duplicate(d.methods.map((x:any)=>x.name)))failure(d,"duplicate provided method");
   const next=["super","self",...outer];
   const methods=d.methods.map((method:any)=>({name:method.name,value:abstract(method.parameters,next,
      inner=>body(method.body,inner,m),method)}));
   const extension=lam(lam(term("extend",{inherited:term("bound",{index:0}),fields:methods})));
   // Reflection retains actual law bodies as callable values and complete
   // authored interfaces as immutable labels. Retention is not proof discharge.
   const laws=d.laws.map((law:any)=>({name:law.name,value:abstract([{name:"self"},{name:"super"},...law.parameters],outer,
      inner=>expression(law.body,inner,m),law)}));
   value=term("specification",{metadata:record([{name:"name",value:label(m.name+"."+d.name)},
      {name:"interface",value:label(JSON.stringify({targetType:d.targetType,requirements:d.requirements,
          methods:d.methods.map(({body,...signature}:any)=>signature)}))},{name:"laws",value:record(laws)}]),extension});
  }else failure(d,"unsupported declaration "+d.kind);
  fields.push({name:m.name+"."+(d.name??d.signature.name),value});
 }
 const root=term("fix",{spec:lam(lam(record(fields))),seed:record([])});
 const entry=modules[entryModule];if(!entry||!globals.has(entry.name+"."+entryDefinition))failure(null,"missing selected entry");
 let selected=get(root,entry.name+"."+entryDefinition);
 const argument=(a:any):Core=>{
  if(typeof a==="string"&&/^(0|[1-9][0-9]*)$/.test(a))return nat(a);
  if(typeof a==="boolean")return label(a?"true":"false");
  if(a&&typeof a==="object"&&!Array.isArray(a))return record(Object.entries(a).map(([name,value])=>({name,value:argument(value)})));
  return failure(null,"runtime arguments are canonical decimal Nat strings, Bool or records");
 };
 for(const arg of args)selected=app(selected,argument(arg));
 return {schema:"dregg.objective-bend.core.v1",edition:"objective-bend-1",term:selected,
   sourceEntry:entry.name+"."+entryDefinition,sourceModules:modules.map(m=>({name:m.name,sourceSha256:m.sha256,astSha256:m.astSha256})),
   declarationASTs:modules.map(m=>m.ast),status:"elaborated executable term; new typing and demand adequacy unqualified"};
}
// First connected annotation cut: exact literal declarations (including source
// inference holes) plus the generated shared global knot. Other bodies return
// an explicit unsupported typing diagnostic; their executable core stays retained.
export function literalAnnotations(output:any){
 const fields:any[]=[];
 for(const [index,ast] of output.declarationASTs.entries())for(const d of ast.declarations){
  if(d.kind==="record")continue;
  if(d.kind!=="function"||d.signature.parameters.length||d.body.kind!=="expression")
   return {status:"unsupported",message:"typing bridge currently covers zero-argument literal declarations"};
  const e=d.body.expression;
  const type=e.kind==="nat"?{tag:"natural"}:e.kind==="bool"?{tag:"boolean"}:e.kind==="string"?{tag:"label"}:null;
  if(!type)return {status:"unsupported",message:"nonliteral declaration requires further source annotation inference"};
  const declared=d.signature.resultType;
  if(declared!=="_"&&declared!==(e.kind==="nat"?"Nat":e.kind==="bool"?"Bool":"String"))
   return {status:"refused",message:"literal result differs from authored result type",span:d.signature.span};
  fields.push({name:output.sourceModules[index].name+"."+d.signature.name,type});
 }
 let global:any={tag:"emptyRow"};for(const field of fields.slice().reverse())global={tag:"field",name:field.name,member:field.type,tail:global};
 const variable={tag:"variable",index:"0"},empty={tag:"emptyRow"};
 let cursor=output.term,path:number[]=[];
 while(cursor.tag==="app"){cursor=cursor.fn;path.push(0);}
 if(cursor.tag!=="get"||cursor.target.tag!=="fix")return {status:"unsupported",message:"typing bridge expects exact generated entry projection"};
 path.push(0,0);
 const annotation=(path:number[],domain:any,codomain:any)=>({path:path.map(String),domain,codomain,parameter:"unrestricted",reuse:"reusable"});
 const arrow={tag:"arrow",reuse:"reusable",parameter:"unrestricted",domain:empty,codomain:variable};
 return {schema:"dregg.objective-bend.typed-core.v1",term:output.term,annotations:[annotation(path,variable,arrow),annotation([...path,0],empty,variable)],
  bounds:[{index:"0",type:global}],shareableVariables:["0"],fuel:"4096",context:[],
  sourceEntry:output.sourceEntry,sourceModules:output.sourceModules,
  status:"exact core annotation proposal; actual checker must return Checked; no law proof or effect authority"};
}

export function lean(t:Core):string{
 const go=lean,q=JSON.stringify,fields=(fs:any[])=>`[${fs.map(f=>`(${q(f.name)}, ${go(f.value)})`).join(", ")}]`;
 switch(t.tag){
 case "bound":return `(Term.bound ${t.index})`;case "nat":return `(Term.nat ${t.value})`;case "label":return `(Term.label ${q(t.value)})`;
 case "lam":return `(Term.lam ${go(t.body)})`;case "app":return `(Term.app ${go(t.fn)} ${go(t.arg)})`;
 case "fix":return `(Term.fix ${go(t.spec)} ${go(t.seed)})`;case "mix":return `(Term.mix ${go(t.lower)} ${go(t.upper)})`;
 case "specification":return `(Term.specification ${go(t.metadata)} ${go(t.extension)})`;
 case "prototype":return `(Term.prototype ${go(t.spec)} ${go(t.target)})`;
 case "reflect":case "metadata":case "project":return `(Term.${t.tag} ${go(t.value)})`;
 case "record":return `(Term.record ${fields(t.fields)})`;case "extend":return `(Term.extend ${go(t.inherited)} ${fields(t.fields)})`;
 case "get":return `(Term.get ${go(t.target)} ${q(t.name)})`;
 case "binary":return `(Term.binary Primitive.${t.primitive} ${go(t.left)} ${go(t.right)})`;
 case "ifZero":return `(Term.ifZero ${go(t.value)} ${go(t.zero)} ${go(t.successor)})`;
 default:throw Error("internal unsupported core constructor "+t.tag);
 }
}
if(import.meta.main){
 try{
  const [capturePath,outPath,argsRaw="[]",projectionRaw="[]",limitsRaw='{"heap":"100000","stack":"100000","ticks":"100000"}']=process.argv.slice(2);
  if(!capturePath||!outPath)throw Error("usage: objective-elaborate CAPTURE_JSON OUTPUT_LEAN [ARGUMENTS_JSON] [PROJECTIONS_JSON] [LIMITS_JSON]");
  const limits=JSON.parse(limitsRaw);
  for(const key of ["heap","stack","ticks"])if(typeof limits[key]!=="string"||!/^[1-9][0-9]*$/.test(limits[key])||BigInt(limits[key])>1000000n)throw Error("preview limits must be canonical positive decimal strings ≤1000000");
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
  const output=elaborate(modules,Number(capture.entryModule),capture.entryDefinition,JSON.parse(argsRaw));
  output.limits=limits;
  for(const projection of JSON.parse(projectionRaw)){
   if(projection.field)output.term=get(output.term,projection.field);
   if(projection.argument!==undefined){if(!/^(0|[1-9][0-9]*)$/.test(projection.argument))throw Error("projection argument must be canonical Nat");output.term=app(output.term,nat(projection.argument));}
  }
  await writeFile(outPath+".typed.json",JSON.stringify(literalAnnotations(output),null,2)+"\n");
  await writeFile(outPath+".core.json",JSON.stringify(output,null,2)+"\n");
  await writeFile(outPath,`import Theory.ObjectiveBendDemandMachine
open Lean (Json toJson)
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
def authoredTerm : Term := ${lean(output.term)}
def previewLimits : Limits := ⟨${limits.heap},${limits.stack}⟩
def measured : Nat → State → List Nat → Outcome × List Nat
  | 0,state,entered => (runBounded previewLimits 0 state,entered)
  | ticks+1,state,entered =>
    let entered := match state.control with
      | .enter address => match state.heap[address]? with
        | some (.suspended _) => address::entered
        | _ => entered
      | _ => entered
    match step previewLimits state with
    | .suspended .ticks next => measured ticks next entered
    | other => (other,entered)
def resultJson : RuntimeValue → Json
  | .natural value => Json.mkObj [("tag",toJson "natural"),("value",toJson (toString value))]
  | .label value => Json.mkObj [("tag",toJson "label"),("value",toJson value)]
  | .closure _ _ => Json.mkObj [("tag",toJson "closure"),("status",toJson "unforced body")]
  | .record fields => Json.mkObj [("tag",toJson "record"),("fields",toJson (fields.map Prod.fst))]
  | .specification _ _ => Json.mkObj [("tag",toJson "specification"),("status",toJson "unforced extension")]
  | .prototype _ _ => Json.mkObj [("tag",toJson "prototype"),("status",toJson "unforced target")]
def main : IO Unit := do
  let (outcome,entered) := measured ${limits.ticks} (initial authoredTerm) []
  let state : State := match outcome with
    | .finished _ state | .suspended _ state | .divergent _ state | .refused _ state => state
  let (status,value,diagnostic) := match outcome with
    | .finished value _ => ("finished",resultJson value,Json.null)
    | .suspended reason _ => ("suspended",Json.null,toJson (reprStr reason))
    | .divergent _ _ => ("divergent",Json.null,toJson "blackhole; no catchable source exception")
    | .refused reason _ => ("refused",Json.null,toJson (reprStr reason))
  let addresses := state.heap.toList.foldl (fun (prior : List Nat) (cell : Cell) => match cell with
    | .cached _ (.record fields) => match fields.find? (fun field => field.1 == "costly") with
      | some (_,address) => if prior.contains address then prior else address::prior
      | none => prior
    | _ => prior) ([] : List Nat)
  let demands := addresses.map fun address => Json.mkObj
    [("address",toJson (toString address)),("firstEntries",toJson (toString ((entered.filter (· == address)).length)))]
  IO.println ((Json.mkObj [("schema",toJson "dregg.objective-bend.reference-result.v1"),
    ("sourceEntry",toJson ${JSON.stringify(output.sourceEntry)}),("edition",toJson "objective-bend-1"),
    ("status",toJson status),("result",value),("diagnostic",diagnostic),
    ("heap",toJson (toString state.heap.size)),("stack",toJson (toString state.stack.length)),
    ("sharingProbe",Json.arr demands.toArray),("authority",toJson "none; clear source preview")]).compress)
`);
  console.log(JSON.stringify({schema:output.schema,sourceEntry:output.sourceEntry,outputPath:outPath,coreSha256:sha(JSON.stringify(output)),status:output.status}));
 }catch(e){console.error(JSON.stringify(e instanceof Error?{message:e.message}:e));process.exitCode=1;}
}
