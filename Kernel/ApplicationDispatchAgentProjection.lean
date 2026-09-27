/-
Versioned physical projection for an agent-origin special dispatch. The v1
human permit has no task budget/fence, so a physical host must reject agent
origin in v1 and accept agent delivery only after a distinct v2 native route.
-/
import Kernel.ApplicationDispatchProjection

namespace Minidregg.Kernel.ApplicationDispatchAgentProjection

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationDispatchCodec

set_option autoImplicit false

/-- Exact reserved task state and both roots at the dispatch admission tip.
`innerRoot` is signed in the DRC target; `physicalRoot` is the complete-cell
CAS root. A process runner uses task/generation/status/budget as a fence, not
as a caller-chosen grant. -/
structure Parent where
  task : Nat
  generation : Int
  status : Int
  remaining : Int
  reserved : Int
  innerRoot : Digest
  physicalRoot : Digest
  deriving DecidableEq

def parentStream : StreamCodec Parent :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product DeclaredEffectPageMaterializer.intStream
        (StreamCodec.product DeclaredEffectPageMaterializer.intStream
          (StreamCodec.product DeclaredEffectPageMaterializer.intStream
            (StreamCodec.product DeclaredEffectPageMaterializer.intStream
              (StreamCodec.product digestStream digestStream))))))
    (fun parent => (parent.task, parent.generation, parent.status,
      parent.remaining, parent.reserved, parent.innerRoot, parent.physicalRoot))
    (fun (task, generation, status, remaining, reserved, innerRoot, physicalRoot) =>
      ⟨task, generation, status, remaining, reserved, innerRoot, physicalRoot⟩)
    (by intro parent; cases parent; rfl)

structure Candidate where
  base : ApplicationDispatchProjection.Candidate
  parent : Parent
  deriving DecidableEq

def candidateStream : StreamCodec Candidate :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationDispatchProjection.candidateStream parentStream)
    (fun candidate => (candidate.base, candidate.parent))
    (fun (base, parent) => ⟨base, parent⟩)
    (by intro candidate; cases candidate; rfl)

def codec : LawfulCodec Candidate :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-DISPATCH-CANDIDATE/v2".toUTF8.toList candidateStream

theorem decode_encode (candidate : Candidate) :
    codec.decode (codec.encode candidate) = some candidate :=
  codec.decode_encode candidate

/-- Native admission checks `parentMatches` and the exact second DRC target.
This projection additionally reads the same current physical cell so the
host can fence by the full-cell root and reserved budget. No caller-provided
parent state enters this function. -/
def ofDispatchAt {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : NativeHostReplay.DispatchAt config opened ingress) :
    Option Candidate := do
  let .agent task generation := ingress.dispatch.dispatch.session.origin
    | none
  let claimed ← ingress.parent
  if claimed.task != task || claimed.state.generation != generation ||
      !(claimed.state.status == 3 || claimed.state.status == 4) then none else
  let cell ← match opened.directory.directory.slots task with
    | .present cell => some cell
    | _ => none
  let ⟨.declaredObject, payload⟩ := cell
    | none
  let page ← DeclaredEffectPageMaterializer.pageAt payload.logical
  let state ← AgentGrain.readState task page
  if state != claimed.state || payload.root != claimed.root ||
      state.remaining < 0 || state.reserved < 0 then none else
  some ⟨ApplicationDispatchProjection.ofDispatchAt admitted,
    ⟨task, state.generation, state.status, state.remaining, state.reserved,
      payload.root, ResourceBirthCodec.physicalRoot (.live cell)⟩⟩

end Minidregg.Kernel.ApplicationDispatchAgentProjection
