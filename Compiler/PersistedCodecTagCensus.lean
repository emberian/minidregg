/- Named build check: the canonical set of persisted codec tags/frames
reachable from elaborated codec/materializer/byte-encoder bodies must equal
Compiler.PersistedCodecTags' registry set, in both directions. Definitions are
traversed, not comments or theorem fixtures. Registry enumeration and the epoch
hash are excluded from discovery, so they cannot manufacture reverse coverage.
Inline receiving identities need no relocation or declaration exceptions. -/
import Kernel.NativeHostReplay
import Compiler.PersistedCodecTags
import Lean

namespace Minidregg.Compiler.PersistedCodecTagCensus
open Lean Elab Command Meta

partial def literals (e : Expr) : List String :=
  match e with
  | .lit (.strVal s) => if s.startsWith "DREGG" then [s] else []
  | .app f a => literals f ++ literals a
  | .lam _ _ b _ | .forallE _ _ b _ => literals b
  | .letE _ _ v b _ => literals v ++ literals b
  | .mdata _ b => literals b
  | .proj _ _ b => literals b
  | _ => []

partial def dependencies (e : Expr) : List Name :=
  match e with
  | .const n _ => [n]
  | .app f a => dependencies f ++ dependencies a
  | .lam _ _ b _ | .forallE _ _ b _ => dependencies b
  | .letE _ _ v b _ => dependencies v ++ dependencies b
  | .mdata _ b => dependencies b
  | .proj _ _ b => dependencies b
  | _ => []

/-- Static version suffixes and raw numeric byte frames, including those
embedded directly in a codec record. A descriptor's encoded data is not a tag. -/
partial def fixedFrames (e : Expr) : List Expr :=
  let args := e.getAppArgs
  let numericFrame := e.isAppOfArity ``List.cons 3 &&
    args[0]!.isConstOf ``UInt8 &&
    args[1]!.isAppOfArity ``OfNat.ofNat 3 &&
    args[1]!.getAppArgs[1]! == .lit (.natVal 68)
  let suffixedFrame := (e.isAppOfArity ``HAppend.hAppend 6 ||
      e.isAppOfArity ``List.append 3) &&
    args[args.size - 1]!.isAppOfArity ``List.cons 3 &&
    args[args.size - 1]!.getAppArgs[0]!.isConstOf ``UInt8
  let versionedPrefix := if (e.isAppOfArity ``HAppend.hAppend 6 ||
      e.isAppOfArity ``List.append 3) && args[args.size - 1]!.isAppOfArity ``List.cons 3 then
    let cons := args[args.size - 1]!.getAppArgs
    let framePrefix := args[args.size - 2]!
    let version := cons[1]!
    if cons[0]!.isConstOf ``UInt8 && !framePrefix.hasLooseBVars && !version.hasLooseBVars then
      [mkApp3 (mkConst ``List.append [.zero]) (mkConst ``UInt8) framePrefix
        (mkApp3 (mkConst ``List.cons [.zero]) (mkConst ``UInt8) version
          (mkApp (mkConst ``List.nil [.zero]) (mkConst ``UInt8)))]
    else []
  else []
  let here := (if !e.hasLooseBVars && (numericFrame || suffixedFrame) then [e] else []) ++ versionedPrefix
  here ++ match e with
    | .app f a => fixedFrames f ++ fixedFrames a
    | .lam _ _ b _ | .forallE _ _ b _ => fixedFrames b
    | .letE _ _ v b _ => fixedFrames v ++ fixedFrames b
    | .mdata _ b => fixedFrames b
    | .proj _ _ b => fixedFrames b
    | _ => []

def packageDeclaration (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => n.toString.startsWith "Minidregg."
  | some i =>
      match env.header.moduleNames[i.toNat]? with
      | some m => [ `Compiler, `Kernel, `Host ].contains m.getRoot
      | none => false

def codecRoot (n : Name) (info : ConstantInfo) : Bool :=
  let head := info.type.consumeMData.getForallBody.getAppFn.constName?
  let leaf := n.toString.splitOn "." |>.getLast!
  leaf.startsWith "encode" || leaf.startsWith "decode" || leaf.endsWith "Bytes" ||
    head == some ``Minidregg.Kernel.ProtectedCell.Spec ||
    head == some ``Minidregg.Compiler.DurableCheckpointCodec.Framed ||
    head == some ``Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec ||
    head == some ``Minidregg.Theory.IndexedProgram.LawfulCodec ||
    head == some ``Minidregg.Compiler.StoreCodec.Wire ||
    head == some ``Minidregg.Theory.CellState.Materializer

/-- Read a directly referenced registry identity, without following the
manifest or hash back into all entries. A codec's reference remains evidence;
the mere presence of an entry in the registry does not count as reachability. -/
def registeredIdentity (name : Name) (info : ConstantInfo) : TermElabM (List UInt8) := do
  let value := mkConst name
  if info.type.isConstOf ``String then
    return (← unsafe evalExpr String (mkConst ``String) value).toUTF8.toList
  else if info.type.isConstOf ``Nat then
    return (toString (← unsafe evalExpr Nat (mkConst ``Nat) value)).toUTF8.toList
  else
    unsafe evalExpr (List UInt8) (mkApp (mkConst ``List [.zero]) (mkConst ``UInt8)) value

elab "#assert_persisted_codec_tags" : command => do
  let env ← getEnv
  let mut queue : List Name := []
  for (name, info) in env.constants.toList do
    if packageDeclaration env name && codecRoot name info &&
        !name.toString.startsWith "Minidregg.Compiler.PersistedCodecTags." then
      queue := name :: queue
  let mut seen : NameSet := {}
  let mut observed : List (List UInt8) := []
  let mut unregistered : Array (Name × Name × String) := #[]
  let registered := Minidregg.Compiler.PersistedCodecTags.canonicalSet
    (Minidregg.Compiler.PersistedCodecTags.entries.map (·.bytes))
  while !queue.isEmpty do
    let name := queue.head!
    queue := queue.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if let some (.defnInfo info) := env.find? name then
      if name.toString.startsWith "Minidregg.Compiler.PersistedCodecTags." then
        if Minidregg.Compiler.PersistedCodecTags.tagAttribute.hasTag env name then
          observed := (← liftTermElabM <| registeredIdentity name (.defnInfo info)) :: observed
        continue
      let source := match env.getModuleIdxFor? name with
        | some i => env.header.moduleNames[i.toNat]!
        | none => env.mainModule
      let type := info.type.consumeMData
      let leaf := name.toString.splitOn "." |>.getLast!
      let constants := if type.isAppOfArity ``List 1 && type.appArg!.isConstOf ``UInt8 &&
          (leaf.endsWith "Frame" || leaf.endsWith "FrameName" || leaf == "frame" || leaf == "magic")
        then [mkConst name] else []
      for frame in constants ++ fixedFrames info.value do
        let bytes ← liftTermElabM <| unsafe evalExpr (List UInt8)
          (mkApp (mkConst ``List [.zero]) (mkConst ``UInt8)) frame
        if bytes.take 5 == [68,82,69,71,71] then
          observed := bytes :: observed
          unless registered.contains bytes do
            unregistered := unregistered.push (name, source, s!"complete frame {bytes}")
      for tag in literals info.value do
        let bytes := tag.toUTF8.toList
        observed := bytes :: observed
        unless registered.contains bytes do
          unregistered := unregistered.push (name, source, tag)
      queue := dependencies info.value ++ queue
  let reachable := Minidregg.Compiler.PersistedCodecTags.canonicalSet observed
  let registryOnly := Minidregg.Compiler.PersistedCodecTags.entries.filter
    (fun entry => !reachable.contains entry.bytes)
  unless reachable == registered do
    throwError m!"persisted codec tag set equality failed: reachable-only {unregistered.toList}; registry-only {registryOnly.map (·.name)}"
  logInfo m!"#assert_persisted_codec_tags: {seen.size} definitions reached; {reachable.length} canonical identities; reachable set = registry set (both directions)"

#assert_persisted_codec_tags
end Minidregg.Compiler.PersistedCodecTagCensus
