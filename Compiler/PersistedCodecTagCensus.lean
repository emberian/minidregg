/- Build-time completeness check for the source-owned persisted codec corpus.
The roots are discovered from actual StreamCodec/LawfulCodec/Wire/materializer
types plus byte encoders (which expose frames hidden behind opaque byte fields).
Dependency traversal reads definition bodies, never comments or theorem fixtures.
A new reachable DREGG literal outside PersistedCodecTags fails elaboration.
The temporary train-owned exceptions are exact declaration/value pairs, and each
is required to remain present; deleting/changing a codec cannot silently retain
an obsolete exception. No persistence decisions are delegated to a transport. -/
import Kernel.NativeHostReplay
import Theory.PersistedCodecTags
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
  let here := if !e.hasLooseBVars && (numericFrame || suffixedFrame) then [e] else []
  here ++ match e with
    | .app f a => fixedFrames f ++ fixedFrames a
    | .lam _ _ b _ | .forallE _ _ b _ => fixedFrames b
    | .letE _ _ v b _ => fixedFrames v ++ fixedFrames b
    | .mdata _ b => fixedFrames b
    | .proj _ _ b => fixedFrames b
    | _ => []

/-- Pending relocation by train kern only. Each value is the registry's own
entry, not a second tag spelling. The check verifies the actual source body. -/
def kernOwnedExceptions : List (Name × String) := [
  (`Minidregg.Kernel.ObjectiveActivityReceiver.commandFrame, Minidregg.Theory.PersistedCodecTags.objective_activity_command_v12),
  (`Minidregg.Kernel.ObjectiveActivityReceiver.contextAt, Minidregg.Theory.PersistedCodecTags.objective_activity_args_v1),
  (`Minidregg.Kernel.ObjectiveActivityReceiver.effectDigest, Minidregg.Theory.PersistedCodecTags.objective_activity_effect_v1),
  (`Minidregg.Kernel.ObjectiveActivityReceiver.event, Minidregg.Theory.PersistedCodecTags.objective_activity_event_v1),
  (`Minidregg.Kernel.ObjectiveActivityReceiver.ingressFrame, Minidregg.Theory.PersistedCodecTags.objective_activity_signed_v2),
  (`Minidregg.Kernel.ObjectiveActivityReceiver.marker, Minidregg.Theory.PersistedCodecTags.objective_activity_identity_v1),
  (`Minidregg.Kernel.ObjectiveActivityReceiver.outcomeDigest, Minidregg.Theory.PersistedCodecTags.objective_activity_outcome_v1),
  (`Minidregg.Kernel.ObjectiveActivityReceiver.recordedFailureCodec, Minidregg.Theory.PersistedCodecTags.objective_activity_recorded_failure_v1),
  (`Minidregg.Kernel.ObjectiveActivityReceiver.rejectCodec, Minidregg.Theory.PersistedCodecTags.objective_activity_reject_v1),
  (`Minidregg.Kernel.ObjectiveActivityReceiver.signingPlanCodec, Minidregg.Theory.PersistedCodecTags.objective_activity_plan_v4),
  (`Minidregg.Kernel.WorldKindInstance.frame, String.fromUTF8! (ByteArray.mk Minidregg.Theory.PersistedCodecTags.world_instance_byte_v1.dropLast.toArray)),
  (`Minidregg.Kernel.WorldRoot.logCustomization, Minidregg.Theory.PersistedCodecTags.log_v1),
  (`Minidregg.Kernel.WorldRoot.turnCustomization, Minidregg.Theory.PersistedCodecTags.turn_v1),
  (`Minidregg.Kernel.WorldRoot.worldCustomization, Minidregg.Theory.PersistedCodecTags.world_root_v1)]

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

elab "#assert_persisted_codec_tags" : command => do
  let env ← getEnv
  let mut queue : List Name := []
  for (name, info) in env.constants.toList do
    if packageDeclaration env name && codecRoot name info then queue := name :: queue
  let mut seen : NameSet := {}
  let mut observed : Array (Name × String) := #[]
  let mut offenders : Array (Name × Name × String) := #[]
  let registeredBytes := Minidregg.Theory.PersistedCodecTags.entries.map (·.bytes)
  while !queue.isEmpty do
    let name := queue.head!
    queue := queue.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if let some (.defnInfo info) := env.find? name then
      if name.toString.startsWith "Minidregg.Theory.PersistedCodecTags." then continue
      let source := match env.getModuleIdxFor? name with
        | some i => env.header.moduleNames[i.toNat]!
        | none => env.mainModule
      -- Check complete frame constants and static suffix expressions, including
      -- anonymous frames in StreamCodec definitions. Encoded descriptor data
      -- is traversed for its tags, rather than mistaken for a codec identity.
      let type := info.type.consumeMData
      let leaf := name.toString.splitOn "." |>.getLast!
      let constants := if type.isAppOfArity ``List 1 && type.appArg!.isConstOf ``UInt8 &&
          (leaf.endsWith "Frame" || leaf.endsWith "FrameName" || leaf == "frame" || leaf == "magic")
        then [mkConst name] else []
      for frame in constants ++ fixedFrames info.value do
        let bytes ← liftTermElabM <| unsafe evalExpr (List UInt8)
          (mkApp (mkConst ``List [.zero]) (mkConst ``UInt8)) frame
        if bytes.take 5 == [68,82,69,71,71] then
          unless registeredBytes.contains bytes do
            offenders := offenders.push (name, source, s!"complete frame {bytes}")
      for tag in literals info.value do
        observed := observed.push (name, tag)
        unless kernOwnedExceptions.contains (name, tag) do
          offenders := offenders.push (name, source, tag)
      queue := dependencies info.value ++ queue
  for exception in kernOwnedExceptions do
    unless observed.contains exception do
      throwError m!"persisted codec tag exception is stale: {exception.1}; actual definition must match its registered tag"
  unless offenders.isEmpty do
    throwError m!"persisted codec tag literals must be owned by Theory.PersistedCodecTags: {offenders.toList}"
  logInfo m!"#assert_persisted_codec_tags: {seen.size} definitions reached; {kernOwnedExceptions.length} exact kern-owned exceptions verified; no unregistered persisted DREGG literals"

#assert_persisted_codec_tags
end Minidregg.Compiler.PersistedCodecTagCensus
