import {parseObjective} from './objective-parser.ts';
import {elaborate,literalAnnotations} from './objective-elaborate.ts';
const moduleFor=(source:string)=>({name:'Probe',sha256:'test-only',astSha256:'test-only',imports:[],ast:parseObjective(source)});
const run=(body:string,type:string)=>elaborate([moduleFor(`edition ObjectiveBend 1\ndef value() -> ${type}:\n  ${body}\n`)],0,'value',[]);
const bool=literalAnnotations(run('true','Bool'));
if(bool.schema!=='dregg.objective-bend.typed-core.v2'||bool.bounds[0].type.member.tag!=='boolean')throw Error('Bool source annotation lost');
const label=literalAnnotations(run('"ordinary text"','String'));
if(label.schema!=='dregg.objective-bend.typed-core.v2'||label.bounds[0].type.member.tag!=='label')throw Error('String source annotation lost');
for(const formerlyReserved of ['true','false']){
 const strings=literalAnnotations(run(JSON.stringify(formerlyReserved),'String'));
 if(strings.schema!=='dregg.objective-bend.typed-core.v2'||strings.bounds[0].type.member.tag!=='label')throw Error('String content reclassified as Boolean');
}
const unknown=literalAnnotations(run('7n','Unknown'));
if(unknown.status!=='unsupported')throw Error('unsupported authored type silently replaced');
const inferred=elaborate([moduleFor('edition ObjectiveBend 1\ndef value(x: Nat):\n  return x + 1n\n')],0,'value',['7']);
const proposal=literalAnnotations(inferred);
if(proposal.schema!=='dregg.objective-bend.typed-core.v2'||proposal.bounds[0].type.member.codomain.tag!=='natural')throw Error('ordinary result hole did not infer actual primitive body');
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
if(typedCompose.schema!=='dregg.objective-bend.typed-core.v2')throw Error('shared composition lost its typing proposal: '+typedCompose.message);
console.log('COMPOSE SHARING PASS: k=8/16/32 sizes '+[s8,s16,s32].join('/')+' (linear); metadata.inherited and mix.lower are bound 1 of one redex');
// (b) a package that declares specifications yields a typed packet; spec method lambdas carry binder hints.
const evenOdd=`edition ObjectiveBend 1\nrecord Parity:\n  even(n: Nat) -> Bool\n  odd(n: Nat) -> Bool\nspec Even for Parity:\n  requires odd(n: Nat) -> Bool\n  def even(n: Nat) -> Bool:\n    match n:\n      case 0n: true\n      case 1n+pred: self.odd(pred)\nspec Odd for Parity:\n  requires even(n: Nat) -> Bool\n  def odd(n: Nat) -> Bool:\n    match n:\n      case 0n: false\n      case 1n+pred: self.even(pred)\n  law total(n: Nat): self.odd(n) == self.odd(n)\ndef four() -> Nat:\n  4n\n`;
const specTyped=literalAnnotations(elaborate([moduleFor(evenOdd)],0,'four',[]));
if(specTyped.schema!=='dregg.objective-bend.typed-core.v2')throw Error('spec-declaring package refused: '+specTyped.message);
const specRow=specTyped.bounds[0].type;if(specRow.member.tag!=='specification'||specRow.tail.member.metadata.tail.tail.member.member.codomain.codomain.codomain.tag!=='boolean')throw Error('spec global type or law type lost');
if(specTyped.annotations.length<8)throw Error('spec method lambdas lack binder hints');
console.log('SPEC TYPING PASS: spec-declaring package yields typed-core.v2; spec, law and method lambdas annotated');
// (c) affine/linear are reachable from the surface and reach the checker proposal.
const affine=literalAnnotations(elaborate([moduleFor('edition ObjectiveBend 1\ndef keep(affine x: Nat, linear y: Nat, -z: Nat, +w: Nat) -> Nat:\n  x + y\n')],0,'keep',[]));
const quantities=affine.annotations.slice(-4).map((a:any)=>a.parameter+'/'+a.reuse).join(',');
if(quantities!=='affine/reusable,linear/once,erased/once,unrestricted/once')throw Error('quantities lost: '+quantities);
if(affine.bounds[0].type.member.codomain.reuse!=='once')throw Error('closure after an affine parameter not one-shot in the declared type');
expectThrow(()=>moduleFor('edition ObjectiveBend 1\ndef bad(affine +x: Nat) -> Nat:\n  x\n'),/two quantity markers/,'double quantity');
console.log('QUANTITY SURFACE PASS: affine/linear/dead/copy reach annotations; later closures one-shot');
// (d) operators without a core constructor are refused with the constructor they wait for.
for(const [op,wait] of [['<','Primitive.less'],['>=','Primitive.less'],['-','Primitive.subtract'],['/','Primitive.divide']]){
 expectThrow(()=>run('1n '+op+' 2n','Nat'),new RegExp('operator '+op.replace(/[-/]/g,'\\$&')+' is not yet a core constructor.*'+wait.replace('.','\\.')),'operator '+op);
}
console.log('OPERATOR REFUSAL PASS: < >= - / name Primitive.less/subtract/divide');
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
if(sumsTyped.schema!=='dregg.objective-bend.typed-core.v2'||injectAnnotations.length!==3||'injections' in sumsTyped)throw Error('injection annotations lost: '+JSON.stringify(sumsTyped.message??injectAnnotations.length));
if(!injectAnnotations.some((a:any)=>a.domain.tag==='field'&&a.domain.name==='side'))throw Error('injection domain is not the payload type');
if(!sumsTyped.bounds.some((b:any)=>b.index==='1'&&b.type.tag==='variant')||!sumsTyped.shareableVariables.includes('1'))throw Error('recursive sum not a bounded shareable variable');
if(JSON.stringify(Object.keys(literalAnnotations(run('7n','Nat'))))!=='["schema","term","annotations","bounds","shareableVariables","fuel","context","sourceEntry","sourceModules","status"]')throw Error('sum-free packet shape changed');
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
if(literalAnnotations(anc).schema!=='dregg.objective-bend.typed-core.v2')throw Error('ancestry package lost typing');
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
