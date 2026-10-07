// Elaboration cohort, through the Lean front end (Compiler/ObjectiveBendElaborate via the
// front end's batch command). Every scenario is a .obend source run in ONE batch; the
// assertions below read the core term, the typing proposal packet and the front end's own
// check result. Successor of the TypeScript elaborator's test suite, same assertions.
// usage: bun tests/objective-bend-source/check-elaborate.ts   (env LEAN, LEAN_PATH: see front.ts)
import {readFileSync,readdirSync,writeFileSync,mkdtempSync} from "node:fs";
import {join} from "node:path";
import {tmpdir} from "node:os";
import {batch} from "./front.ts";

// ---- the scenarios ----
const jobs:any[]=[];
const job=(name:string,source:string,entry:string,args:any=[],mode="application")=>{
 jobs.push({name,modules:[{name:"Probe",source,imports:[]}],entryModule:0,entryDefinition:entry,arguments:args,mode});return name;};
const parseJob=(name:string,source:string)=>{jobs.push({name,parse:source});return name;};
const E="edition ObjectiveBend 1\n";
const runSrc=(body:string,type:string)=>`${E}def value() -> ${type}:\n  ${body}\n`;
const run=(key:string,body:string,type:string)=>job(key,runSrc(body,type),"value");
run("bool","true","Bool");run("label",'"ordinary text"',"String");
for(const w of ["true","false"])run("reserved-"+w,JSON.stringify(w),"String");
run("unknown","7n","Unknown");
job("inferred",E+"def value(x: Nat):\n  return x + 1n\n","value",["7"]);
const identitySource=E+"def identity(x: String) -> String:\n  return x\n";
const typed=(values:any[])=>({schema:"dregg.objective-bend.argument-values.v1",values});
const identityValues:[string,any][]=[["label",{tag:"label",value:"7"}],["natural",{tag:"natural",value:"7"}],["boolean",{tag:"boolean",value:true}],
 ["nested",{tag:"record",fields:[{name:"root",value:{tag:"label",value:"00ab"}}]}]];
for(const [k,v] of identityValues)job("identity-"+k,identitySource,"identity",typed([v]));
const badValues=[{tag:"natural",value:"07"},{tag:"natural",value:"-1"},{tag:"label",value:"7",extra:true},{tag:"boolean",value:"true"},{tag:"record",fields:[{name:"x",value:{tag:"natural",value:"0"}},{name:"x",value:{tag:"natural",value:"1"}}]}];
badValues.forEach((v,i)=>job("identity-bad-"+i,identitySource,"identity",typed([v])));
job("identity-extra",identitySource,"identity",{...typed([]),extra:true});
const repeated=(k:number)=>job("repeated-"+k,`${E}extension AddOne(self: Nat, super: Nat) -> Nat:\n  super + 1n\ndef repeated(seed: Nat) -> Nat:\n  fix(compose(${Array(k).fill("AddOne").join(", ")}), seed)\n`,"repeated");
for(const k of [2,3,8,16,32])repeated(k);
const evenOdd=`${E}record Parity:\n  even(n: Nat) -> Bool\n  odd(n: Nat) -> Bool\nspec Even for Parity:\n  requires odd(n: Nat) -> Bool\n  def even(n: Nat) -> Bool:\n    match n:\n      case 0n: true\n      case 1n+pred: self.odd(pred)\nspec Odd for Parity:\n  requires even(n: Nat) -> Bool\n  def odd(n: Nat) -> Bool:\n    match n:\n      case 0n: false\n      case 1n+pred: self.even(pred)\n  claim total(n: Nat): self.odd(n) == self.odd(n)\ndef four() -> Nat:\n  4n\n`;
job("evenodd",evenOdd,"four");
job("affine",E+"def keep(affine x: Nat, linear y: Nat, -z: Nat, +w: Nat) -> Nat:\n  x + y\n","keep");
parseJob("double-quantity",E+"def bad(affine +x: Nat) -> Nat:\n  x\n");
const depth=18;let deep=E+"record R0:\n  a: Nat\n  b: Nat\n";
for(let i=1;i<=depth;i++)deep+=`record R${i}:\n  l: R${i-1}\n  r: R${i-1}\n`;
deep+=`def pass(x: R${depth}) -> R${depth}:\n  x\n`;job("deep",deep,"pass",[],"definition");
job("small-table",E+"record A:\n  a: Nat\nrecord B:\n  l: A\n  r: A\ndef pass(x: B) -> B:\n    x\n","pass",[],"definition");
// [operator, result type, Core4 primitive, lowered as the negation of that primitive]
const ops:[string,string,string,boolean][]=[["<","Bool","less",false],[">","Bool","lessEqual",true],["<=","Bool","lessEqual",false],[">=","Bool","less",true],["-","Nat","subtract",false],["/","Nat","divide",false],["%","Nat","modulo",false]];
ops.forEach(([op,type],i)=>run("op-"+i,"7n "+op+" 2n",type));
run("minus","4n - 1n","Nat");
job("let",E+"def f(x: Nat) -> Nat:\n  let y = x + 1n\n  let x: Nat = y * y\n  x + x\n","f",[],"definition");
job("let-unresolved",E+"def g(p: Nat) -> Nat:\n  let y = metadata(p)\n  1n\n","g",[],"definition");
job("let-inline",E+"def h(x: Nat) -> Nat:\n  let a: Nat = x in a + a\n","h",[],"definition");
parseJob("let-misplaced",E+"def f() -> Nat:\n  let y = 1n\n    y\n");
const shapes=`${E}sum Shape:\n  circle: Nat\n  square: {side: Nat}\n  none: {}\nsum List:\n  nil: {}\n  cons: {head: Nat, tail: List}\ndef area(s: Shape) -> Nat:\n  match s:\n    case circle(r): r * 3n\n    case square(q): q.side * q.side\n    case none(_): 0n\ndef pick(b: Bool) -> Nat:\n  if b then 1n else 2n\ndef same(a: String, b: String) -> Bool:\n  a == b\ndef differ(a: Nat, b: Nat) -> Bool:\n  a != b\ndef either(a: Bool, b: Bool) -> Bool:\n  a || b\ndef one() -> List:\n  List.cons({head: 1n, tail: List.nil()})\ndef main() -> Nat:\n  area(Shape.square({side: 4n}))\n`;
job("sums",shapes,"main");run("sum-free","7n","Nat");
job("nonexhaustive",shapes.replace("    case none(_): 0n\n",""),"main");
job("unknown-case",shapes.replace("Shape.square({side: 4n})","Shape.triangle(4n)"),"main");
job("untyped-eq",E+"def eq(a, b) -> Bool:\n  a == b\n","eq");
parseJob("gen1",E+'import Prior from "./Base.bend"\n');
const ancestrySource=(specs:string)=>`${E}record R:\n  v(n: Nat) -> Nat\n${specs}def blank() -> R:\n  {v: fn(n: Nat) -> Nat: n}\n`;
const spec=(name:string,head:string,body="    super.v(n) + 1n")=>`${head.replace("NAME",name)}\n  def v(n: Nat) -> Nat:\n${body}\n`;
job("diamond",ancestrySource(spec("O","spec NAME for R:","    n")+spec("A","spec NAME extends O for R:")+spec("B","spec NAME extends O for R:")+spec("D","spec NAME extends A, B for R:")),"blank");
const refusals:[string,string,RegExp][]=[
 ["inconsistent",spec("O","spec NAME for R:","    n")+spec("H","spec NAME extends O for R:")+spec("V","spec NAME extends O for R:")+spec("HV","spec NAME extends H, V for R:")+spec("VH","spec NAME extends V, H for R:")+spec("X","spec NAME extends HV, VH for R:"),/C4 linearization of Probe\.X refused/],
 ["suffix",spec("S","suffix spec NAME for R:","    n")+spec("T","suffix spec NAME for R:","    n")+spec("X","spec NAME extends S, T for R:"),/suffix incompatibility/],
 ["cycle",spec("A","spec NAME extends B for R:")+spec("B","spec NAME extends A for R:"),/ancestry cycle/],
 ["before",spec("O","spec NAME for R:","    n")+"spec B extends O for R:\n  before v(n: Nat) -> Nat:\n    n\n",/no effect constructor yet/],
 ["mixed",spec("O","spec NAME for R:","    n")+"spec P extends O for R:\n  combine + v(n: Nat) -> Nat:\n    n\n",/method v is \+ in one ancestor and primary in another/],
 ["unknown-parent",spec("O","spec NAME for R:","    n")+spec("X","spec NAME extends Missing for R:"),/not a spec declaration/]];
for(const [k,specs] of refusals)job("ancestry-"+k,ancestrySource(specs),"blank");
const testDir=import.meta.dirname;
const sources=readdirSync(testDir).filter(f=>f.endsWith(".obend")).sort();
// Both import forms: `import A from "./B.obend"` and `import ./B.obend as A`.
const parsedImports=(src:string)=>[...src.matchAll(/^import\s+(?:([A-Za-z_]\w*)\s+from\s+"\.\/([A-Za-z_]\w*)\.obend"|\.\/([A-Za-z_]\w*)\.obend(?:\s+as\s+([A-Za-z_]\w*))?)$/gm)]
 .map(m=>m[1]?{alias:m[1],base:m[2]}:{alias:m[4]??"",base:m[3]});
const lastDecl=(src:string)=>[...src.matchAll(/^(?:def|spec|suffix spec|extension)\s+([A-Za-z_]\w*)/gm)].map(m=>m[1]).at(-1)!;
for(const f of sources){
 const src=readFileSync(join(testDir,f),"utf8");const imps=parsedImports(src);
 const modules=[...imps.map(i=>({name:i.base,source:readFileSync(join(testDir,i.base+".obend"),"utf8"),imports:[]})),
  {name:f.replace(".obend",""),source:src,imports:imps.map((i,j)=>({alias:i.alias,module:String(j)}))}];
 jobs.push({name:"every:"+f,modules,entryModule:modules.length-1,entryDefinition:lastDecl(src),arguments:[],mode:"definition"});
}

// ---- one Lean process ----
const work=mkdtempSync(join(tmpdir(),"obend-elaborate-"));writeFileSync(join(work,"jobs.json"),JSON.stringify(jobs));
const results=new Map<string,any>(batch(join(work,"jobs.json"),join(work,"results.json")).map((r:any)=>[r.name,r]));
const out=(k:string)=>{const r=results.get(k);if(!r?.ok)throw Error("refused unexpectedly: "+k+" "+JSON.stringify(r?.diagnostic));return r.output.core;};
const rawProposal=(k:string)=>{out(k);return results.get(k).output.packet;};
const typeChildren:Record<string,string[]>={arrow:["domain","codomain"],field:["member","tail"],specification:["metadata","extension"],prototype:["spec","target"],variant:["row"],computation:["plan","response","result"]};
const expandTypes=(p:any)=>{const ex=(t:any):any=>{if(t.tag==="ref")return ex(p.types[Number(t.index)]);const c=typeChildren[t.tag];if(!c)return t;const n:any={...t};for(const k of c)n[k]=ex(t[k]);return n;};
 const {types,...rest}=p;return {...rest,annotations:p.annotations.map((a:any)=>({...a,domain:ex(a.domain),codomain:ex(a.codomain)})),bounds:p.bounds.map((b:any)=>({...b,type:ex(b.type)})),context:p.context.map((c:any)=>({...c,type:ex(c.type)}))};};
const literal=(k:string)=>{const p=rawProposal(k);return p.schema?expandTypes(p):p;};
const refusedWith=(k:string,pattern:RegExp,what:string)=>{const r=results.get(k);const m=r?.ok?"":String(r?.diagnostic?.message??"");
 if(r?.ok||!pattern.test(m))throw Error(what+": expected refusal matching "+pattern+", got "+JSON.stringify(r?.ok?"accepted":m));};

// ---- the assertions ----
if(literal("bool").schema!=="dregg.objective-bend.typed-core.v3"||literal("bool").bounds[0].type.member.tag!=="boolean")throw Error("Bool source annotation lost");
if(literal("label").bounds[0].type.member.tag!=="label")throw Error("String source annotation lost");
for(const w of ["true","false"])if(literal("reserved-"+w).bounds[0].type.member.tag!=="label")throw Error("String content reclassified as Boolean");
if(literal("unknown").status!=="unsupported")throw Error("unsupported authored type silently replaced");
if(literal("inferred").bounds[0].type.member.codomain.tag!=="natural")throw Error("ordinary result hole did not infer actual primitive body");
console.log("OBJECTIVE ELABORATION DIAGNOSTICS PASS: Bool/String distinction, formerly reserved String acceptance, unknown type refusal");
if(out("identity-label").term.arg.tag!=="label"||out("identity-natural").term.arg.tag!=="nat"||out("identity-boolean").term.arg.tag!=="boolean"||out("identity-nested").term.arg.fields[0].value.tag!=="label")throw Error("typed argument reclassified");
badValues.forEach((_,i)=>{if(results.get("identity-bad-"+i)?.ok)throw Error("malformed tagged value accepted");});
if(results.get("identity-extra")?.ok)throw Error("ignored argument envelope field");
console.log("TAGGED ARGUMENT VALUES PASS: exact Nat/Boolean/String/record and malformed-value refusals");
const size=(t:any)=>JSON.stringify(t).length;
const findTag=(t:any,tag:string):any=>{if(!t||typeof t!=="object")return null;if(t.tag===tag)return t;for(const v of Object.values(t)){const r=Array.isArray(v)?v.map(x=>findTag(x,tag)).find(Boolean):findTag(v,tag);if(r)return r;}return null;};
const findAll=(t:any,pred:(x:any)=>boolean,acc:any[]=[]):any[]=>{if(t&&typeof t==="object"){if(pred(t))acc.push(t);for(const v of Object.values(t))findAll(v,pred,acc);}return acc;};
const s8=size(out("repeated-8").term),s16=size(out("repeated-16").term),s32=size(out("repeated-32").term);
if(s32-s16!==2*(s16-s8))throw Error("compose term growth is not linear: "+[s8,s16,s32]);
// compose's metadata is SpecMeta.composed{inherited, wrapping}: a specification operand
// contributes metadata(<its binder>), a bare extension SpecMeta.extension{}. In
// compose(compose(AddOne, AddOne), AddOne) the outer step's inherited operand is the inner
// composite: its provenance and the mix's lower must read the SAME binder (no copy).
const composedMeta=(x:any)=>x.tag==="specification"&&x.metadata.tag==="inject"&&x.metadata.label==="composed";
const shared=findAll(out("repeated-3").term,(x:any)=>composedMeta(x)&&x.metadata.payload.fields[0].value.tag==="metadata")[0];
if(!shared)throw Error("no composed SpecMeta with a specification operand");
const inheritedMeta=shared.metadata.payload.fields[0].value.value;
if(inheritedMeta.tag!=="bound"||inheritedMeta.index!==1||shared.extension.lower.tag!=="bound"||shared.extension.lower.index!==1)
 throw Error("metadata inherited and mix lower do not reference one shared binder");
const bare=findAll(out("repeated-2").term,composedMeta)[0];
if(bare?.metadata.payload.fields[0].value.tag!=="inject"||bare.metadata.payload.fields[0].value.label!=="extension")
 throw Error("a bare extension operand did not record SpecMeta.extension");
if(literal("repeated-3").schema!=="dregg.objective-bend.typed-core.v3")throw Error("shared composition lost its typing proposal");
console.log("COMPOSE SHARING PASS: k=8/16/32 sizes "+[s8,s16,s32].join("/")+" (linear); SpecMeta.composed inherited and mix.lower are bound 1 of one redex");
const specTyped=literal("evenodd");
if(specTyped.schema!=="dregg.objective-bend.typed-core.v3")throw Error("spec-declaring package refused: "+specTyped.message);
// Both specs have the ONE metadata type (the SpecMeta variable), claim or no claim; the claim
// is its own knot field Probe.Odd#claim#total : (self, super, n) -> Bool.
const specRow=specTyped.bounds[0].type;const rowField=(row:any,name:string):any=>row?.tag==="field"?(row.name===name?row.member:rowField(row.tail,name)):null;
const evenTy=rowField(specRow,"Probe.Even"),oddTy=rowField(specRow,"Probe.Odd"),claimTy=rowField(specRow,"Probe.Odd#claim#total");
if(evenTy?.tag!=="specification"||oddTy?.tag!=="specification"||evenTy.metadata.tag!=="variable"||JSON.stringify(evenTy.metadata)!==JSON.stringify(oddTy.metadata))
 throw Error("spec global types do not share the one SpecMeta metadata type");
if(claimTy?.codomain?.codomain?.codomain?.tag!=="boolean")throw Error("claim field type lost: "+JSON.stringify(claimTy));
if(specTyped.annotations.length<8)throw Error("spec method lambdas lack binder hints");
if(results.get("evenodd").output.check.accepted!==true)throw Error("the checker refused the front end's own packet: "+JSON.stringify(results.get("evenodd").output.check));
console.log("SPEC TYPING PASS: spec-declaring package yields typed-core.v3; spec, claim and method lambdas annotated; the front end's packet checks");
const affine=literal("affine");
const quantities=affine.annotations.slice(-4).map((a:any)=>a.parameter+"/"+a.reuse).join(",");
if(quantities!=="affine/reusable,linear/once,erased/once,unrestricted/once")throw Error("quantities lost: "+quantities);
if(affine.bounds[0].type.member.codomain.reuse!=="once")throw Error("closure after an affine parameter not one-shot in the declared type");
if(results.get("double-quantity")?.ok!==false||!/two quantity markers/.test(results.get("double-quantity").diagnostic.message))throw Error("double quantity accepted");
console.log("QUANTITY SURFACE PASS: affine/linear/dead/copy reach annotations; later closures one-shot");
{
 const big=rawProposal("deep");const nodes=new Map<number,number>();
 const count=(t:any):number=>t.tag==="ref"?(nodes.get(Number(t.index))??(()=>{const n=count(big.types[Number(t.index)]);nodes.set(Number(t.index),n);return n;})()):1+["member","tail","domain","codomain","row"].reduce((a,k)=>a+(t[k]?count(t[k]):0),0);
 const expanded=big.annotations.reduce((a:number,x:any)=>a+count(x.domain)+count(x.codomain),0);
 if(big.schema!=="dregg.objective-bend.typed-core.v3"||JSON.stringify(big).length>60000||expanded<1000000)throw Error("type table did not share: "+JSON.stringify(big).length+" bytes, expansion "+expanded+" nodes");
 const seen=new Set<string>();
 for(const [k,entry] of big.types.entries()){
  const sorted=(v:any):any=>v&&typeof v==="object"?Object.fromEntries(Object.keys(v).sort().map(k=>[k,sorted(v[k])])):v;const key=JSON.stringify(sorted(entry));if(seen.has(key))throw Error("duplicate type table entry "+k);seen.add(key);
  for(const v of Object.values(entry as any))if((v as any)?.tag==="ref"&&Number((v as any).index)>=k)throw Error("type table entry "+k+" refers forward");
 }
 const dom=literal("small-table").annotations.find((a:any)=>a.domain.tag==="field")?.domain;
 if(!dom||dom.name!=="l"||dom.member.tag!=="field"||dom.member.name!=="a"||dom.tail.name!=="r"||dom.tail.member.name!=="a")throw Error("table expansion lost structure");
 console.log("TYPE TABLE PASS: depth-"+depth+" nested records: proposal "+JSON.stringify(big).length+" bytes, "+big.types.length+" table entries, expansion would be "+expanded+" type nodes");
}
ops.forEach(([op,,primitive,negated],i)=>{
 const fields=findTag(out("op-"+i).term,"fix").spec.extension.body.body.fields;
 if(fields.map((f:any)=>f.name).join()!=="Probe.value")throw Error("operator "+op+" added package fields: "+fields.map((f:any)=>f.name));
 const value=fields[0].value;
 const bin=negated?value.condition:value;
 if(negated&&(value.tag!=="ifBool"||value.whenTrue.tag!=="boolean"||value.whenTrue.value!==false||value.whenFalse.tag!=="boolean"||value.whenFalse.value!==true))throw Error("operator "+op+" is not the negation of "+primitive);
 if(bin?.tag!=="binary"||bin.primitive!==primitive||bin.left.value!=="7"||bin.right.value!=="2")throw Error("operator "+op+" did not lower to binary "+primitive+" with the operands in source order: "+JSON.stringify(value));
 const typedOp=literal("op-"+i);if(typedOp.schema!=="dregg.objective-bend.typed-core.v3")throw Error("operator "+op+" lost its typing proposal");
 const row:string[]=[];for(let r=typedOp.bounds[0].type;r.tag==="field";r=r.tail)row.push(r.name);
 if(row.join()!=="Probe.value")throw Error("global row for "+op+" is not exactly the package's own: "+row);
});
if(JSON.parse(findTag(out("minus").term,"fix").spec.metadata.fields[0].value.value).join()!=="Probe")throw Error("package label names a module the source does not have");
if(out("minus").sourceModules.length!==1)throw Error("captured source modules changed");
console.log("OPERATOR LOWERING PASS: - / % < <= are Core4 binary subtract/divide/modulo/less/lessEqual; > >= are their negations, operands in source order; no package fields added");
const fBody=findTag(out("let").term,"fix").spec.extension.body.body.fields.find((f:any)=>f.name==="Probe.f").value.body;
if(fBody.tag!=="app"||fBody.fn.tag!=="lam"||fBody.arg.tag!=="binary"||fBody.arg.primitive!=="add"||fBody.arg.left.tag!=="bound"||fBody.arg.left.index!==0)
 throw Error("let did not lower to an application of a lambda whose argument is the value, elaborated outside the binder");
const inner=fBody.fn.body;
if(inner.tag!=="app"||inner.arg.primitive!=="multiply"||inner.arg.left.index!==0||inner.arg.right.index!==0||inner.fn.body.primitive!=="add"||inner.fn.body.left.index!==0)
 throw Error("nested let / shadowing lowered wrongly: "+JSON.stringify(inner).slice(0,300));
if(findAll(out("let").term,(x:any)=>x.tag==="binary"&&x.primitive==="multiply").length!==1)throw Error("let duplicated its value");
if(literal("let").annotations.filter((a:any)=>a.domain.tag==="natural"&&a.codomain.tag==="natural").length<3)throw Error("let lambdas lost their annotations");
const unresolved=literal("let-unresolved");
if(unresolved.status!=="unsupported"||!/parameter y has no resolvable type/.test(unresolved.message))throw Error("an unresolvable let type was guessed: "+JSON.stringify(unresolved).slice(0,200));
if(findAll(out("let-inline").term,(x:any)=>x.tag==="app"&&x.fn.tag==="lam").length!==1)throw Error("expression let did not lower to a redex");
if(results.get("let-misplaced")?.ok!==false||!/same indent/.test(results.get("let-misplaced").diagnostic.message))throw Error("misplaced let body accepted");
console.log("LET PASS: let lowers to one redex, value shared and outside the binder, shadowing, unresolved type refused by the proposal, statement and expression forms");
const g=(name:string)=>findTag(out("sums").term,"fix").spec.extension.body.body.fields.find((f:any)=>f.name==="Probe."+name).value;
if(findTag(g("area"),"case")?.arms.map((a:any)=>a.label).join()!=="circle,square,none")throw Error("sum match did not lower to case");
if(findTag(g("pick"),"ifBool")===null||findTag(g("same"),"binary").primitive!=="labelEqual"||findTag(g("differ"),"ifBool").condition.primitive!=="equal"||findTag(g("either"),"ifBool").whenTrue.value!==true)throw Error("Bool/label lowering lost");
const sumsTyped=literal("sums");
const injectAnnotations=sumsTyped.annotations?.filter((a:any)=>a.codomain.tag==="variant"||(a.codomain.tag==="variable"&&a.codomain.index!=="0"))??[];
if(injectAnnotations.filter((a:any)=>a.codomain.tag==="variable").length!==2)throw Error("recursive-sum injections do not carry the declared sum variable");
if(sumsTyped.schema!=="dregg.objective-bend.typed-core.v3"||injectAnnotations.length!==3||"injections" in sumsTyped)throw Error("injection annotations lost");
if(!injectAnnotations.some((a:any)=>a.domain.tag==="field"&&a.domain.name==="side"))throw Error("injection domain is not the payload type");
if(!sumsTyped.bounds.some((b:any)=>b.index==="1"&&b.type.tag==="variant")||!sumsTyped.shareableVariables.includes("1"))throw Error("recursive sum not a bounded shareable variable");
if(JSON.stringify(Object.keys(rawProposal("sum-free")).sort())!==JSON.stringify(["annotations","bounds","context","fuel","schema","shareableVariables","sourceEntry","sourceModules","status","term","types"]))throw Error("sum-free packet shape changed");
refusedWith("nonexhaustive",/not exhaustive: missing \[none\]/,"non-exhaustive match");
refusedWith("unknown-case",/has no case triangle/,"unknown sum case");
refusedWith("untyped-eq",/operands' types resolved/,"untyped ==");
console.log("SUMS SURFACE PASS: inject/case/ifBool/labelEqual, != and || via ifBool, recursive sum bound, exhaustiveness, sum-free packets unchanged");
if(results.get("gen1")?.ok!==false||!/Gen-1 \.\/NAME\.bend imports are retired/.test(results.get("gen1").diagnostic.message))throw Error("Gen-1 import accepted");
console.log("GEN-1 IMPORT REFUSAL PASS");
const anc=out("diamond");
const dSpec=findAll(anc.term,(x:any)=>x.tag==="specification"&&x.metadata.tag==="inject"&&x.metadata.label==="declared"&&x.metadata.payload.fields[0]?.value?.value==="Probe.D")[0];
const iface=JSON.parse(dSpec.metadata.payload.fields[1].value.value);
if(iface.precedence.join()!=="Probe.D,Probe.A,Probe.B,Probe.O")throw Error("C4 precedence list wrong: "+iface.precedence);
const chain:string[]=[];for(let x=dSpec.extension;x.tag==="mix";x=x.lower)chain.unshift(x.upper.name);
const bottom=(()=>{let x=dSpec.extension;while(x.tag==="mix")x=x.lower;return x.name;})();
if([bottom,...chain].join()!=="Probe.O,Probe.B#primary,Probe.A#primary,Probe.D#primary")throw Error("mix chain order wrong: "+[bottom,...chain]);
if(literal("diamond").schema!=="dregg.objective-bend.typed-core.v3")throw Error("ancestry package lost typing");
for(const [k,,pattern] of refusals)refusedWith("ancestry-"+k,pattern,k);
console.log("ANCESTRY PASS: diamond D,A,B,O; mix chain O<B#primary<A#primary<D#primary; inconsistent / suffix / cycle / before / mixed-qualifier / unknown-parent refusals");
const rootFix=findTag(out("sum-free").term,"fix");
if(rootFix.spec.tag!=="specification"||rootFix.spec.extension.body.body.tag!=="extend")throw Error("package root is not an extensible specification");
console.log("PACKAGE ROOT PASS: fix(specification(package, λself λsuper. extend super {...}), {})");
for(const f of sources)out("every:"+f);
console.log("EVERY OBEND ELABORATES: "+sources.length+" files");
