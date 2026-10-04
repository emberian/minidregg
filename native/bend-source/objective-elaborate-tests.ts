import {parseObjective} from './objective-parser.ts';
import {elaborate,literalAnnotations as rawProposal,expandTypes} from './objective-elaborate.ts';
// Most checks below read types inline; the packet itself names them through its shared type table.
const literalAnnotations=(output:any)=>{const p=rawProposal(output);return p.schema?expandTypes(p):p;};
const moduleFor=(source:string)=>({name:'Probe',sha256:'test-only',astSha256:'test-only',imports:[],ast:parseObjective(source)});
const run=(body:string,type:string)=>elaborate([moduleFor(`edition ObjectiveBend 1\ndef value() -> ${type}:\n  ${body}\n`)],0,'value',[]);
const bool=literalAnnotations(run('true','Bool'));
if(bool.schema!=='dregg.objective-bend.typed-core.v3'||bool.bounds[0].type.member.tag!=='boolean')throw Error('Bool source annotation lost');
const label=literalAnnotations(run('"ordinary text"','String'));
if(label.schema!=='dregg.objective-bend.typed-core.v3'||label.bounds[0].type.member.tag!=='label')throw Error('String source annotation lost');
for(const formerlyReserved of ['true','false']){
 const strings=literalAnnotations(run(JSON.stringify(formerlyReserved),'String'));
 if(strings.schema!=='dregg.objective-bend.typed-core.v3'||strings.bounds[0].type.member.tag!=='label')throw Error('String content reclassified as Boolean');
}
const unknown=literalAnnotations(run('7n','Unknown'));
if(unknown.status!=='unsupported')throw Error('unsupported authored type silently replaced');
const inferred=elaborate([moduleFor('edition ObjectiveBend 1\ndef value(x: Nat):\n  return x + 1n\n')],0,'value',['7']);
const proposal=literalAnnotations(inferred);
if(proposal.schema!=='dregg.objective-bend.typed-core.v3'||proposal.bounds[0].type.member.codomain.tag!=='natural')throw Error('ordinary result hole did not infer actual primitive body');
console.log('OBJECTIVE ELABORATION DIAGNOSTICS PASS: Bool/String distinction, formerly reserved String acceptance, unknown type refusal');

const identityModule=moduleFor('edition ObjectiveBend 1\ndef identity(x: String) -> String:\n  return x\n');
const typed=(values:any[])=>({schema:'dregg.objective-bend.argument-values.v1',values});
const identity=(value:any)=>elaborate([identityModule],0,'identity',typed([value]));
if(identity({tag:'label',value:'7'}).term.arg.tag!=='label')throw Error('typed String coerced to Nat');
if(identity({tag:'natural',value:'7'}).term.arg.tag!=='nat')throw Error('typed Nat reclassified');
if(identity({tag:'boolean',value:true}).term.arg.tag!=='boolean')throw Error('typed Boolean reclassified');
const nested=identity({tag:'record',fields:[{name:'root',value:{tag:'label',value:'00ab'}}]});
if(nested.term.arg.fields[0].value.tag!=='label')throw Error('nested String lost');
for(const bad of [{tag:'natural',value:'07'},{tag:'natural',value:'-1'},{tag:'label',value:'7',extra:true},{tag:'boolean',value:'true'},{tag:'record',fields:[{name:'x',value:{tag:'natural',value:'0'}},{name:'x',value:{tag:'natural',value:'1'}}]}]){
 let refused=false;try{identity(bad)}catch{refused=true}if(!refused)throw Error('malformed tagged value accepted');
}
let extraRefused=false;try{elaborate([identityModule],0,'identity',{...typed([]),extra:true})}catch{extraRefused=true}
if(!extraRefused)throw Error('ignored argument envelope field');
console.log('TAGGED ARGUMENT VALUES PASS: exact Nat/Boolean/String/record and malformed-value refusals');

// ---- W1.5 front-end repairs ----
const expectThrow=(f:()=>unknown,pattern:RegExp,what:string)=>{
 let message="";try{f();}catch(e:any){message=e?.message??String(e);}
 if(!pattern.test(message))throw Error(what+": expected refusal matching "+pattern+", got "+JSON.stringify(message));
};
const size=(t:any)=>JSON.stringify(t).length;
// (a) compose shares the inherited composite: linear growth, one binder for metadata and mix.
const repeated=(k:number)=>elaborate([moduleFor(`edition ObjectiveBend 1\nextension AddOne(self: Nat, super: Nat) -> Nat:\n  super + 1n\ndef repeated(seed: Nat) -> Nat:\n  fix(compose(${Array(k).fill('AddOne').join(', ')}), seed)\n`)],0,'repeated',[]);
const s8=size(repeated(8).term),s16=size(repeated(16).term),s32=size(repeated(32).term);
if(s32-s16!==2*(s16-s8))throw Error('compose term growth is not linear: '+[s8,s16,s32]);
const findTag=(t:any,tag:string):any=>{if(!t||typeof t!=='object')return null;if(t.tag===tag)return t;for(const v of Object.values(t)){const r=Array.isArray(v)?v.map(x=>findTag(x,tag)).find(Boolean):findTag(v,tag);if(r)return r;}return null;};
const findAll=(t:any,pred:(x:any)=>boolean,out:any[]=[]):any[]=>{if(t&&typeof t==='object'){if(pred(t))out.push(t);for(const v of Object.values(t))findAll(v,pred,out);}return out;};
const shared=findAll(repeated(2).term,(x:any)=>x.tag==='specification'&&x.metadata.fields[0]?.name==='operator')[0];
if(shared.metadata.fields[1].value.tag!=='bound'||shared.metadata.fields[1].value.index!==1||shared.extension.lower.tag!=='bound'||shared.extension.lower.index!==1)
 throw Error('metadata inherited and mix lower do not reference one shared binder');
const typedCompose=literalAnnotations(repeated(3));
if(typedCompose.schema!=='dregg.objective-bend.typed-core.v3')throw Error('shared composition lost its typing proposal: '+typedCompose.message);
console.log('COMPOSE SHARING PASS: k=8/16/32 sizes '+[s8,s16,s32].join('/')+' (linear); metadata.inherited and mix.lower are bound 1 of one redex');
// (b) a package that declares specifications yields a typed packet; spec method lambdas carry binder hints.
const evenOdd=`edition ObjectiveBend 1\nrecord Parity:\n  even(n: Nat) -> Bool\n  odd(n: Nat) -> Bool\nspec Even for Parity:\n  requires odd(n: Nat) -> Bool\n  def even(n: Nat) -> Bool:\n    match n:\n      case 0n: true\n      case 1n+pred: self.odd(pred)\nspec Odd for Parity:\n  requires even(n: Nat) -> Bool\n  def odd(n: Nat) -> Bool:\n    match n:\n      case 0n: false\n      case 1n+pred: self.even(pred)\n  law total(n: Nat): self.odd(n) == self.odd(n)\ndef four() -> Nat:\n  4n\n`;
const specTyped=literalAnnotations(elaborate([moduleFor(evenOdd)],0,'four',[]));
if(specTyped.schema!=='dregg.objective-bend.typed-core.v3')throw Error('spec-declaring package refused: '+specTyped.message);
const specRow=specTyped.bounds[0].type;if(specRow.member.tag!=='specification'||specRow.tail.member.metadata.tail.tail.member.member.codomain.codomain.codomain.tag!=='boolean')throw Error('spec global type or law type lost');
if(specTyped.annotations.length<8)throw Error('spec method lambdas lack binder hints');
console.log('SPEC TYPING PASS: spec-declaring package yields typed-core.v3; spec, law and method lambdas annotated');
// (c) affine/linear are reachable from the surface and reach the checker proposal.
const affine=literalAnnotations(elaborate([moduleFor('edition ObjectiveBend 1\ndef keep(affine x: Nat, linear y: Nat, -z: Nat, +w: Nat) -> Nat:\n  x + y\n')],0,'keep',[]));
const quantities=affine.annotations.slice(-4).map((a:any)=>a.parameter+'/'+a.reuse).join(',');
if(quantities!=='affine/reusable,linear/once,erased/once,unrestricted/once')throw Error('quantities lost: '+quantities);
if(affine.bounds[0].type.member.codomain.reuse!=='once')throw Error('closure after an affine parameter not one-shot in the declared type');
expectThrow(()=>moduleFor('edition ObjectiveBend 1\ndef bad(affine +x: Nat) -> Nat:\n  x\n'),/two quantity markers/,'double quantity');
console.log('QUANTITY SURFACE PASS: affine/linear/dead/copy reach annotations; later closures one-shot');
// (c') the proposal names types through a shared table: a type whose expansion is exponential stays linear.
{
 const depth=18;
 let src='edition ObjectiveBend 1\nrecord R0:\n  a: Nat\n  b: Nat\n';
 for(let i=1;i<=depth;i++)src+=`record R${i}:\n  l: R${i-1}\n  r: R${i-1}\n`;
 src+=`def pass(x: R${depth}) -> R${depth}:\n  x\n`;
 const big=rawProposal(elaborate([moduleFor(src)],0,'pass',[],'definition'));
 const nodes=new Map<number,number>();
 const count=(t:any):number=>t.tag==='ref'?(nodes.get(Number(t.index))??(()=>{const n=count(big.types[Number(t.index)]);nodes.set(Number(t.index),n);return n;})()):1+['member','tail','domain','codomain','row'].reduce((a,k)=>a+(t[k]?count(t[k]):0),0);
 const expanded=big.annotations.reduce((a:number,x:any)=>a+count(x.domain)+count(x.codomain),0);
 if(big.schema!=='dregg.objective-bend.typed-core.v3'||JSON.stringify(big).length>60000||expanded<1000000)throw Error('type table did not share: '+JSON.stringify(big).length+' bytes, expansion '+expanded+' nodes');
 // Entries are unique, and a ref only ever names an EARLIER entry (so every type is a finite tree).
 const seen=new Set<string>();
 for(const [k,entry] of big.types.entries()){
  const sorted=(v:any):any=>v&&typeof v==='object'?Object.fromEntries(Object.keys(v).sort().map(k=>[k,sorted(v[k])])):v;const key=JSON.stringify(sorted(entry));if(seen.has(key))throw Error('duplicate type table entry '+k);seen.add(key);
  for(const v of Object.values(entry as any))if((v as any)?.tag==='ref'&&Number((v as any).index)>=k)throw Error('type table entry '+k+' refers forward');
 }
 // Expansion inverts the table: depth 2 expands to the nested row it names.
 const small=expandTypes(rawProposal(elaborate([moduleFor('edition ObjectiveBend 1\nrecord A:\n  a: Nat\nrecord B:\n  l: A\n  r: A\ndef pass(x: B) -> B:\n    x\n')],0,'pass',[],'definition')));
 const dom=small.annotations.find((a:any)=>a.domain.tag==='field')?.domain;
 if(!dom||dom.tag!=='field'||dom.name!=='l'||dom.member.tag!=='field'||dom.member.name!=='a'||dom.tail.name!=='r'||dom.tail.member.name!=='a')throw Error('table expansion lost structure');
 console.log('TYPE TABLE PASS: depth-'+depth+' nested records: proposal '+JSON.stringify(big).length+' bytes, '+big.types.length+' table entries, expansion would be '+expanded+' type nodes');
}
// (d) operators without a core primitive lower to the package prelude: a call of one global of the knot.
const preludeKeys=(out:any)=>findTag(out.term,'fix').spec.extension.body.body.fields.map((f:any)=>f.name).filter((n:string)=>n.startsWith('$prelude.'));
for(const [op,type,definitions] of [['<','Bool',['lt']],['>','Bool',['lt']],['<=','Bool',['le']],['>=','Bool',['le']],['-','Nat',['sub']],['/','Nat',['sub','lt','quotient','divide']]] as [string,string,string[]][]){
 const out=run('7n '+op+' 2n',type);
 const keys=preludeKeys(out).map((n:string)=>n.slice('$prelude.'.length)).sort().join();
 if(keys!==[...definitions].sort().join())throw Error('operator '+op+' pulled prelude definitions '+keys+' wanted '+definitions);
 const typedOp=literalAnnotations(out);
 if(typedOp.schema!=='dregg.objective-bend.typed-core.v3'||!typedOp.bounds[0].type)throw Error('operator '+op+' lost its typing proposal: '+typedOp.message);
 const row:string[]=[];for(let r=typedOp.bounds[0].type;r.tag==='field';r=r.tail)row.push(r.name);
 if(!definitions.every(d=>row.includes('$prelude.'+d))||row.includes('Probe.value')===false)throw Error('prelude definitions missing from the global row for '+op);
}
// `>` and `>=` swap the operands of `<` and `<=`; neither operand is duplicated.
const lt32=findAll(run('3n < 2n','Bool').term,(x:any)=>x.tag==='app'&&x.fn.tag==='app'&&x.fn.fn.name==='$prelude.lt')[0];
const gt32=findAll(run('3n > 2n','Bool').term,(x:any)=>x.tag==='app'&&x.fn.tag==='app'&&x.fn.fn.name==='$prelude.lt')[0];
if(lt32.fn.arg.value!=='3'||lt32.arg.value!=='2'||gt32.fn.arg.value!=='2'||gt32.arg.value!=='3')throw Error('> did not lower to < with swapped operands');
if(preludeKeys(run('1n + 2n','Nat')).length||preludeKeys(run('1n == 2n','Bool')).length)throw Error('a package without these operators gained prelude definitions');
if(JSON.parse(findTag(run('4n - 1n','Nat').term,'fix').spec.metadata.fields[0].value.value).join()!=='Probe,$prelude')throw Error('package label does not name the prelude module');
if(JSON.parse(findTag(run('4n + 1n','Nat').term,'fix').spec.metadata.fields[0].value.value).join()!=='Probe')throw Error('package label of an operator-free package changed');
if(run('4n - 1n','Nat').sourceModules.length!==1||run('4n - 1n','Nat').declarationASTs.length!==1)throw Error('prelude leaked into the captured source modules');
console.log('OPERATOR LOWERING PASS: - / < <= > >= call $prelude.sub/divide/lt/le; only needed definitions added; > >= swap; operator-free packages unchanged');
// `let`: (lambda x. body) value, ONE value subterm however often x is used; the value is outside the binder.
const letOut=elaborate([moduleFor('edition ObjectiveBend 1\ndef f(x: Nat) -> Nat:\n  let y = x + 1n\n  let x: Nat = y * y\n  x + x\n')],0,'f',[],'definition');
const fBody=findTag(letOut.term,'fix').spec.extension.body.body.fields.find((f:any)=>f.name==='Probe.f').value.body;
if(fBody.tag!=='app'||fBody.fn.tag!=='lam'||fBody.arg.tag!=='binary'||fBody.arg.primitive!=='add'||fBody.arg.left.tag!=='bound'||fBody.arg.left.index!==0)
 throw Error('let did not lower to an application of a lambda whose argument is the value, elaborated outside the binder');
const inner=fBody.fn.body;
if(inner.tag!=='app'||inner.arg.primitive!=='multiply'||inner.arg.left.index!==0||inner.arg.right.index!==0||inner.fn.body.primitive!=='add'||inner.fn.body.left.index!==0)
 throw Error('nested let / shadowing lowered wrongly: '+JSON.stringify(inner).slice(0,300));
if(findAll(letOut.term,(x:any)=>x.tag==='binary'&&x.primitive==='multiply').length!==1)throw Error('let duplicated its value');
const letTyped=literalAnnotations(letOut);
if(letTyped.schema!=='dregg.objective-bend.typed-core.v3'||letTyped.annotations.filter((a:any)=>a.domain.tag==='natural'&&a.codomain.tag==='natural').length<3)throw Error('let lambdas lost their annotations: '+letTyped.message);
const unresolved=literalAnnotations(elaborate([moduleFor('edition ObjectiveBend 1\ndef g(p: Nat) -> Nat:\n  let y = metadata(p)\n  1n\n')],0,'g',[],'definition'));
if(unresolved.status!=='unsupported'||!/parameter y has no resolvable type/.test(unresolved.message))throw Error('an unresolvable let type was guessed: '+JSON.stringify(unresolved).slice(0,200));
const inline=elaborate([moduleFor('edition ObjectiveBend 1\ndef h(x: Nat) -> Nat:\n  let a: Nat = x in a + a\n')],0,'h',[],'definition');
if(findAll(inline.term,(x:any)=>x.tag==='app'&&x.fn.tag==='lam').length!==1)throw Error('expression let did not lower to a redex');
expectThrow(()=>moduleFor('edition ObjectiveBend 1\ndef f() -> Nat:\n  let y = 1n\n    y\n'),/same indent/,'misplaced let body');
console.log('LET PASS: let lowers to one redex, value shared and outside the binder, shadowing, unresolved type refused by the proposal, statement and expression forms');
// Sums (SUMS-DESIGN §9): inject/case/ifBool/labelEqual, != and || via ifBool.
const shapes=`edition ObjectiveBend 1\nsum Shape:\n  circle: Nat\n  square: {side: Nat}\n  none: {}\nsum List:\n  nil: {}\n  cons: {head: Nat, tail: List}\ndef area(s: Shape) -> Nat:\n  match s:\n    case circle(r): r * 3n\n    case square(q): q.side * q.side\n    case none(_): 0n\ndef pick(b: Bool) -> Nat:\n  if b then 1n else 2n\ndef same(a: String, b: String) -> Bool:\n  a == b\ndef differ(a: Nat, b: Nat) -> Bool:\n  a != b\ndef either(a: Bool, b: Bool) -> Bool:\n  a || b\ndef one() -> List:\n  List.cons({head: 1n, tail: List.nil()})\ndef main() -> Nat:\n  area(Shape.square({side: 4n}))\n`;
const sumsOut=elaborate([moduleFor(shapes)],0,'main',[]);
const g=(name:string)=>findTag(sumsOut.term,'fix').spec.extension.body.body.fields.find((f:any)=>f.name==='Probe.'+name).value;
if(findTag(g('area'),'case')?.arms.map((a:any)=>a.label).join()!=='circle,square,none')throw Error('sum match did not lower to case');
if(findTag(g('pick'),'ifBool')===null||findTag(g('same'),'binary').primitive!=='labelEqual'||findTag(g('differ'),'ifBool').condition.primitive!=='equal'||findTag(g('either'),'ifBool').whenTrue.value!==true)throw Error('Bool/label lowering lost');
const sumsTyped=literalAnnotations(sumsOut);
// An injection's codomain is its declared sum: a variant, or a recursive sum's bounded variable (index >= 1).
const injectAnnotations=sumsTyped.annotations?.filter((a:any)=>a.codomain.tag==='variant'||(a.codomain.tag==='variable'&&a.codomain.index!=='0'))??[];
if(injectAnnotations.filter((a:any)=>a.codomain.tag==='variable').length!==2)throw Error('recursive-sum injections do not carry the declared sum variable');
if(sumsTyped.schema!=='dregg.objective-bend.typed-core.v3'||injectAnnotations.length!==3||'injections' in sumsTyped)throw Error('injection annotations lost: '+JSON.stringify(sumsTyped.message??injectAnnotations.length));
if(!injectAnnotations.some((a:any)=>a.domain.tag==='field'&&a.domain.name==='side'))throw Error('injection domain is not the payload type');
if(!sumsTyped.bounds.some((b:any)=>b.index==='1'&&b.type.tag==='variant')||!sumsTyped.shareableVariables.includes('1'))throw Error('recursive sum not a bounded shareable variable');
if(JSON.stringify(Object.keys(rawProposal(run('7n','Nat'))))!=='["schema","term","types","annotations","bounds","shareableVariables","fuel","context","sourceEntry","sourceModules","status"]')throw Error('sum-free packet shape changed');
expectThrow(()=>elaborate([moduleFor(shapes.replace('    case none(_): 0n\n',''))],0,'main',[]),/not exhaustive: missing \[none\]/,'non-exhaustive match');
expectThrow(()=>elaborate([moduleFor(shapes.replace('Shape.square({side: 4n})','Shape.triangle(4n)'))],0,'main',[]),/has no case triangle/,'unknown sum case');
expectThrow(()=>elaborate([moduleFor('edition ObjectiveBend 1\ndef eq(a, b) -> Bool:\n  a == b\n')],0,'eq',[]),/operands' types resolved/,'untyped ==');
console.log('SUMS SURFACE PASS: inject/case/ifBool/labelEqual, != and || via ifBool, recursive sum bound, exhaustiveness, sum-free packets unchanged');
// Gen-1 imports are refused by the parser.
expectThrow(()=>parseObjective('edition ObjectiveBend 1\nimport Prior from "./Base.bend"\n'),/Gen-1 \.\/NAME\.bend imports are retired/,'Gen-1 import');
console.log('GEN-1 IMPORT REFUSAL PASS');

// ---- declared ancestry (C4) and method combination ----
const ancestrySource=(specs:string)=>`edition ObjectiveBend 1\nrecord R:\n  v(n: Nat) -> Nat\n${specs}def blank() -> R:\n  {v: fn(n: Nat) -> Nat: n}\n`;
const spec=(name:string,head:string,body='    super.v(n) + 1n')=>`${head.replace('NAME',name)}\n  def v(n: Nat) -> Nat:\n${body}\n`;
const diamond=spec('O','spec NAME for R:','    n')+spec('A','spec NAME extends O for R:')+spec('B','spec NAME extends O for R:')+spec('D','spec NAME extends A, B for R:');
const anc=elaborate([moduleFor(ancestrySource(diamond))],0,'blank',[]);
const dSpec=findAll(anc.term,(x:any)=>x.tag==='specification'&&x.metadata.fields[0]?.value?.value==='Probe.D')[0];
const iface=JSON.parse(dSpec.metadata.fields[1].value.value);
if(iface.precedence.join()!=='Probe.D,Probe.A,Probe.B,Probe.O')throw Error('C4 precedence list wrong: '+iface.precedence);
const chain:string[]=[];for(let x=dSpec.extension;x.tag==='mix';x=x.lower)chain.unshift(x.upper.name);
const bottom=(()=>{let x=dSpec.extension;while(x.tag==='mix')x=x.lower;return x.name;})();
if([bottom,...chain].join()!=='Probe.O,Probe.B#primary,Probe.A#primary,Probe.D#primary')throw Error('mix chain order wrong: '+[bottom,...chain]);
if(literalAnnotations(anc).schema!=='dregg.objective-bend.typed-core.v3')throw Error('ancestry package lost typing');
expectThrow(()=>elaborate([moduleFor(ancestrySource(spec('O','spec NAME for R:','    n')+spec('H','spec NAME extends O for R:')+spec('V','spec NAME extends O for R:')+spec('HV','spec NAME extends H, V for R:')+spec('VH','spec NAME extends V, H for R:')+spec('X','spec NAME extends HV, VH for R:')))],0,'blank',[]),/C4 linearization of Probe\.X refused/,'inconsistent ancestry');
expectThrow(()=>elaborate([moduleFor(ancestrySource(spec('S','suffix spec NAME for R:','    n')+spec('T','suffix spec NAME for R:','    n')+spec('X','spec NAME extends S, T for R:')))],0,'blank',[]),/suffix incompatibility/,'incompatible suffix parents');
expectThrow(()=>elaborate([moduleFor(ancestrySource(spec('A','spec NAME extends B for R:')+spec('B','spec NAME extends A for R:')))],0,'blank',[]),/ancestry cycle/,'ancestry cycle');
expectThrow(()=>elaborate([moduleFor(ancestrySource(spec('O','spec NAME for R:','    n')+'spec B extends O for R:\n  before v(n: Nat) -> Nat:\n    n\n'))],0,'blank',[]),/no effect constructor yet/,'before method');
expectThrow(()=>elaborate([moduleFor(ancestrySource(spec('O','spec NAME for R:','    n')+'spec P extends O for R:\n  combine + v(n: Nat) -> Nat:\n    n\n'))],0,'blank',[]),/method v is \+ in one ancestor and primary in another/,'mixed qualifiers');
expectThrow(()=>elaborate([moduleFor(ancestrySource(spec('O','spec NAME for R:','    n')+spec('X','spec NAME extends Missing for R:')))],0,'blank',[]),/not a spec declaration/,'unknown parent');
console.log('ANCESTRY PASS: diamond D,A,B,O; mix chain O<B#primary<A#primary<D#primary; inconsistent / suffix / cycle / before / mixed-qualifier / unknown-parent refusals');
// The package root is a specification whose extension extends the inherited row.
const rootFix=findTag(run('7n','Nat').term,'fix');
if(rootFix.spec.tag!=='specification'||rootFix.spec.extension.body.body.tag!=='extend')throw Error('package root is not an extensible specification');
console.log('PACKAGE ROOT PASS: fix(specification(package, λself λsuper. extend super {...}), {})');

// Control: every in-repo .obend elaborates (definition mode, last declaration).
import {readdirSync,readFileSync} from 'node:fs';
const testDir=new URL('../../tests/objective-bend-source/',import.meta.url);
const sources=readdirSync(testDir).filter(f=>f.endsWith('.obend')).sort();
for(const f of sources){
 const name=f.replace('.obend',''),ast=parseObjective(readFileSync(new URL(f,testDir),'utf8'));
 const mods:any[]=ast.imports.map((i:any)=>{const base=i.path.slice(2).replace('.obend','');return {name:base,sha256:'t',astSha256:'t',imports:[],ast:parseObjective(readFileSync(new URL(base+'.obend',testDir),'utf8'))};});
 mods.push({name,sha256:'t',astSha256:'t',imports:ast.imports.map((i:any,j:number)=>({...i,module:String(j),moduleName:mods[j].name})),ast});
 const decls=ast.declarations.filter((d:any)=>d.kind!=='record'&&d.kind!=='sum'),last:any=decls[decls.length-1];
 elaborate(mods,mods.length-1,last.name??last.signature.name,[],'definition');
}
console.log('EVERY OBEND ELABORATES: '+sources.length+' files');
