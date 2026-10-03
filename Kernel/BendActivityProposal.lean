/- Generated native command for source-authored persistent computation.
Application libraries provide source code, not their own checkpoint journal.
The proposed command still needs the normal current signed native admission;
this client-side producer cannot manufacture a receiving token. -/
import Kernel.BendActivityIngress
namespace Minidregg.Kernel.BendActivityProposal
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

structure Proposed (source : BendActivityIngress.Source) where
  program : BendActivityProgram.Prepared source.program
  after : BendActivity.Record
  command : Command
  nonceBound : command.nonce = BendActivityIngress.actionNonce source

/-- Build the exact content operation to be signed, using only the actual source
compiler/start/run. No caller-selected post-state or callback code is accepted.
The native receiver repeats the same computation on its current prefix. -/
def propose (pin : ContentControlFrame.Pin) (capability : CapabilityId)
    (source : BendActivityIngress.Source) (preimage : List UInt8) :
    Option (Proposed source) := do
  let program ← BendActivityProgram.prepare source.program
  let (after, payload) ← if source.initialize then do
    if source.ordinal != 0 || source.ticks != 0 ||
        BendActivityControl.phase pin preimage != some .bare then none else do
      let .ok initial := BendActivity.start (BendActivityProgram.binding source.program)
        source.generation program.limits program.compiled.library program.compiled.entry | none
      some (initial, ContentResource.Command.mk
        [.createAtom pin.atom (.inlineObject pin.schema) (BendActivity.encode initial)])
    else do
      let before ← BendActivityControl.readRecord pin preimage
      if before.checkpoint.contextBytes != BendClosureContinuationCodec.encodeContext
          (BendClosureContinuationCodec.executionContext (BendActivityProgram.binding source.program)
            program.limits program.compiled.library) ||
          before.checkpoint.generation != source.generation || before.ordinal != source.ordinal then none else do
        let after ← BendActivity.advance program.limits program.compiled.library source.ticks before
        let payload ← ContentControlFrame.editPayload pin preimage (BendActivity.encode after)
        some (after,payload)
  let target : Target := {kind := .object, target := pin.cell.value, capability := capability, schemaVersion := 1, expectedTargetRoot := ResourceBirthCodec.rootBytes preimage, payload := .content payload}
  let command : Command := {subject := pin.owner, nonce := BendActivityIngress.actionNonce source, targets := [target]}
  some ⟨program,after,command,rfl⟩

/-- After the normal native signing flow, retain that exact original signature
in the source ingress. Signature validation remains at current native admission. -/
def seal (source : BendActivityIngress.Source) (domain semantics : Digest)
    (signed : SignedCommand) : Option BendActivityIngress.Source := do
  let command ← commandCodec.decode signed.commandBytes
  if command.nonce != BendActivityIngress.actionNonce source then none
  else some {source with signedBytes := signedBytes domain semantics signed}

@[simp] theorem signing_preserves_action (source : BendActivityIngress.Source)
    (bytes : List UInt8) :
    BendActivityIngress.actionNonce {source with signedBytes := bytes} =
      BendActivityIngress.actionNonce source := rfl

theorem signed_action_nonce {source : BendActivityIngress.Source} (proposal : Proposed source) :
    proposal.command.nonce = BendActivityIngress.actionNonce source := proposal.nonceBound

#assert_axioms propose
#assert_axioms signing_preserves_action
#assert_axioms signed_action_nonce
end Minidregg.Kernel.BendActivityProposal
