/-
# `Effects/Revival/PrepareProofs.lean` — `PrepareFactors contentSpec`, PROVED

`Effects/Revival/Statements.lean` §8 (audited, pass 27): for a content target whose slot is
present, the deployed per-target preparation `ResourceTransaction.prepareTarget` (its post
packed, its refusals named) IS the registry dispatch of the content handler followed by
`genericChecks` (the final-post law, the policy source, the audience), which never sees the
payload.  Today this is a theorem about the hand arm; at the migration commit it is the shape
`prepareTarget` takes.
-/
module

public import Effects.Revival.ContentProofs
public import Theory.AssertAxioms

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Effects.Revival

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
theorem dispatch_content (ctx : HostCtx) (cell : HostCell) (command : ContentResource.Command) :
    dispatch [(1, contentHandlerOf contentSpec)] 1 (ContentResource.commandStream.encode command) ctx cell =
      (contentHandlerOf contentSpec).fire 1 ctx command cell := by
  simp only [dispatch, List.lookup, beq_self_eq_true]
  rw [show (contentHandlerOf contentSpec).spec.opStream = ContentResource.commandStream from rfl,
    decode_encode_op]

/-- `selectTarget` at a content target selects exactly a content cell under the role and the
cell law. -/
theorem select_some {deployment : DeclaredResourceController.Deployment} {ctx : LiveCtx}
    {command : ContentResource.Command} {version : Nat} {root : Digest}
    {observe : Option CapabilityId} {epoch : Option Nat} {roster : Option ObjectAudienceRoster.Roster}
    {before : HostCell} {pre : ContentResource.ContentCell}
    (selected : DeclaredResourceController.selectTarget deployment
      (contentTarget ctx version root command observe epoch roster) before = some pre) :
    ctx.kind = .object ∧ CanonicalCellRegistry.CellLaw deployment ctx.target before ∧
      before = ⟨.content, pre⟩ := by
  obtain ⟨kind, cell⟩ := before
  simp only [DeclaredResourceController.selectTarget, contentTarget] at selected
  split_ifs at selected with object law
  · refine ⟨object, law, ?_⟩
    split at selected
    · rename_i value same
      cases same
      cases selected
      rfl
    · cases selected

/-- When `selectTarget` refuses, the content header refuses `wrongRole`. -/
theorem header_of_select_none {deployment : DeclaredResourceController.Deployment} {ctx : LiveCtx}
    {command : ContentResource.Command} {version : Nat} {root : Digest}
    {observe : Option CapabilityId} {epoch : Option Nat} {roster : Option ObjectAudienceRoster.Roster}
    {before : HostCell}
    (refused : DeclaredResourceController.selectTarget deployment
      (contentTarget ctx version root command observe epoch roster) before = none) :
    contentHeader (hostCtxOf ctx deployment version root observe epoch roster) before =
      .error (.wrongRole 1) := by
  obtain ⟨kind, cell⟩ := before
  simp only [DeclaredResourceController.selectTarget, contentTarget] at refused
  unfold contentHeader
  by_cases object : ctx.kind = .object
  · by_cases law : CanonicalCellRegistry.CellLaw deployment ctx.target ⟨kind, cell⟩
    · rw [if_pos object, if_pos law] at refused
      have accepts : contentSpec.accepts ctx.kind = true := by simp [contentSpec, object]
      rw [if_neg (by simp only [hostCtxOf]; rintro (h | h) <;> simp_all)]
      split
      · rename_i value same
        cases same
        simp at refused
      · rfl
    · rw [if_pos (Or.inr (by simpa [hostCtxOf] using law))]
  · rw [if_pos (Or.inl (by simp [contentSpec, hostCtxOf, object]))]

theorem exec_comap {C C' : Type} {S : Substrate} {O R : Type} (f : C' → C) (E : EffectSpec C S O R)
    (code : Nat) (c : C') (op : O) (s : S.State) :
    (E.comap f).exec code c op s = E.exec code (f c) op s := rfl

theorem hostCtxOf_toLiveCtx (ctx : LiveCtx) (deployment : DeclaredResourceController.Deployment)
    (version : Nat) (root : Digest) (observe : Option CapabilityId) (epoch : Option Nat)
    (roster : Option ObjectAudienceRoster.Roster) :
    (hostCtxOf ctx deployment version root observe epoch roster).toLiveCtx = ctx := rfl

set_option backward.isDefEq.respectTransparency false in
theorem prepareFactors : PrepareFactors contentSpec := by
  intro deployment directory ctx command version root observe epoch roster before present
  rw [dispatch_content]
  unfold DeclaredResourceController.prepareTarget
  split
  · rename_i absent
    rw [present] at absent
    cases absent
  · rename_i slot found
    rw [present] at found
    cases found
    split
    · rename_i refused
      simp only [Handler.fire, Handler.admits, contentHandlerOf, header_of_select_none refused]
      rfl
    · rename_i pre selected
      obtain ⟨object, law, rfl⟩ := select_some selected
      have accepts : contentSpec.accepts ctx.kind = true := by simp [contentSpec, object]
      obtain ⟨-, wrongVersion, stale, live, -⟩ :=
        contentAgreement ctx command pre observe epoch roster
      by_cases sameVersion : version = contentSpec.version
      · subst sameVersion
        change ContentResource.ContentCell at pre
        have header : contentHeader (hostCtxOf ctx deployment contentSpec.version root observe epoch roster)
            (⟨.content, pre⟩ : HostCell) = .ok () := by
          unfold contentHeader
          rw [if_neg (by simp only [hostCtxOf]; rintro (h | h) <;> simp_all)]
          simp [hostCtxOf]
        by_cases fresh : root = pre.root ∨ contentSpec.commutes command = true
        · have admitted : (contentHandlerOf contentSpec).admits 1
              (hostCtxOf ctx deployment contentSpec.version root observe epoch roster) command
              (⟨.content, pre⟩ : HostCell) = .ok () := by
            simp only [Handler.admits, contentHandlerOf, header]
            rcases fresh with same | commuting
            · subst same
              dsimp only [contentFresh, hostCtxOf]
              rw [if_pos (by simp)]
            · simp [EffectSpec.comap, commuting]
          obtain ⟨accept, refuse, descriptor⟩ := live root accepts fresh
          unfold Handler.fire
          rw [admitted]
          dsimp only [contentHandlerOf]
          rw [exec_comap, hostCtxOf_toLiveCtx]
          cases executed : EffectSpec.exec contentSpec 1 ctx command pre.logical with
          | error e =>
            have refusedLive : ∃ r, DeclaredResourceController.computeTarget ctx.snapshot ctx.semantics
                ctx.ambient ctx.command (contentTarget ctx contentSpec.version root command observe epoch roster)
                pre = .error (.content r) := by
              rw [computeTarget_content_header ctx command pre observe epoch roster root object fresh]
              split
              · exact ⟨_, rfl⟩
              · rename_i prepared _
                exfalso
                have emitted : contentSpec.sem ctx command pre.logical = .ok prepared.progress.2 := by
                  simp [contentSpec, contentSem, prepared.nonempty, prepared.computed, Except.map]
                obtain ⟨s', admitted⟩ := exec_ok_of_complete (code := 1) contentComplete emitted
                rw [admitted] at executed
                cases executed
            obtain ⟨r, liveRefused⟩ := refusedLive
            have named := refuse r liveRefused
            rw [executed] at named
            cases named
            split
            · rename_i reason computed
              rw [liveRefused] at computed
              cases computed
              rfl
            · rename_i post computed
              rw [liveRefused] at computed
              cases computed
          | ok post =>
            obtain ⟨computedOk, valid⟩ := (accept post).1 executed
            obtain ⟨ps, emitted⟩ : ∃ ps, contentSpec.sem ctx command pre.logical = .ok ps := by
              unfold EffectSpec.exec at executed
              split at executed
              · cases executed
              · exact ⟨_, ‹_›⟩
            have patch := descriptor ps emitted
            have postRun : Patch.run pre.logical (DeclaredResourceController.targetPatch ctx.snapshot
                ctx.semantics ctx.ambient ctx.command
                (contentTarget ctx contentSpec.version root command observe epoch roster) pre) = post := by
              obtain ⟨inFrame, -⟩ := contentComplete ctx command pre.logical ps emitted
              unfold EffectSpec.exec at executed
              rw [emitted] at executed
              dsimp only at executed
              rw [if_pos inFrame] at executed
              split at executed
              · cases executed
              · rename_i s' ran
                cases executed
                rw [patch]
                exact ((store_run_iff (L := Hyperdocument.layout) _ _ _).1 ran).2
            split
            · rename_i reason computed
              rw [computedOk] at computed
              cases computed
            · rename_i post' computed
              rw [computedOk] at computed
              cases computed
              obtain ⟨validated, accepted⟩ := validate_accepts
                (contentTarget ctx contentSpec.version root command observe epoch roster).materializer
                pre pre.root _ rfl valid
              split
              · rename_i reason rejected
                have clash := rejected.symm.trans accepted
                cases clash
              · rename_i validated' _
                split
                · rename_i postExact
                  show _ = genericChecks deployment directory ctx.snapshot ctx.target epoch
                    (⟨.content, pre⟩ : HostCell)
                    ⟨.content, CellState.materialize HyperdocumentCell.contentMaterializer post⟩
                  unfold genericChecks
                  split
                  · rename_i postLaw
                    have postLaw' : CanonicalCellRegistry.FinalPostLaw deployment ctx.target
                        (⟨.content, pre⟩ : HostCell)
                        ⟨.content, CellState.materialize HyperdocumentCell.contentMaterializer post⟩ := by
                      rw [← postRun]
                      exact postLaw
                    rw [if_pos postLaw']
                    cases source : CanonicalCellRegistry.loadPolicySource ctx.snapshot.domain directory
                        (ctx.snapshot.authState.policyAddress ⟨ctx.target⟩
                          (ctx.snapshot.authState.policyRevision ⟨ctx.target⟩)) with
                    | none =>
                      simp only [DeclaredResourceController.requireSome]
                      rfl
                    | some loaded =>
                      dsimp only [DeclaredResourceController.requireSome, bind, Except.bind]
                      split
                      · rename_i reason fresh
                        rw [fresh]
                        rfl
                      · rename_i fresh
                        split
                        · rename_i reason other
                          rw [fresh] at other
                          cases other
                        · exact congrArg (fun s => (Except.ok ⟨.content,
                            CellState.materialize HyperdocumentCell.contentMaterializer s⟩ :
                              Except DispatchRefusal HostCell)) postRun
                  · rename_i noLaw
                    have noLaw' : ¬ CanonicalCellRegistry.FinalPostLaw deployment ctx.target
                        (⟨.content, pre⟩ : HostCell)
                        ⟨.content, CellState.materialize HyperdocumentCell.contentMaterializer post⟩ := by
                      rw [← postRun]
                      exact noLaw
                    rw [if_neg noLaw']
                    rfl
                · rename_i notExact
                  exact absurd postRun notExact
        · have sameRoot : root ≠ pre.root := fun same => fresh (Or.inl same)
          have commutes : contentSpec.commutes command = false := by
            cases commuting : contentSpec.commutes command
            · rfl
            · exact absurd (Or.inr commuting) fresh
          have admitted : (contentHandlerOf contentSpec).admits 1
              (hostCtxOf ctx deployment contentSpec.version root observe epoch roster) command
              (⟨.content, pre⟩ : HostCell) = .error (.staleTarget 1) := by
            have commutes' : (contentSpec.comap HostCtx.toLiveCtx).commutes command = false := commutes
            simp only [Handler.admits, contentHandlerOf, header]
            simp [contentFresh, hostCtxOf, commutes']
            exact sameRoot
          have computedStale := stale root accepts commutes sameRoot
          split
          · rename_i reason computed
            rw [computedStale] at computed
            cases computed
            unfold Handler.fire
            rw [admitted]
            rfl
          · rename_i post computed
            rw [computedStale] at computed
            cases computed
      · have header : contentHeader (hostCtxOf ctx deployment version root observe epoch roster)
            (⟨.content, pre⟩ : HostCell) = .error (.unsupportedVersion 1) := by
          unfold contentHeader
          rw [if_neg (by simp only [hostCtxOf]; rintro (h | h) <;> simp_all)]
          simp [hostCtxOf, sameVersion]
        have computedVersion := wrongVersion version root accepts sameVersion
        split
        · rename_i reason computed
          rw [computedVersion] at computed
          cases computed
          simp only [Handler.fire, Handler.admits, contentHandlerOf, header]
          rfl
        · rename_i post computed
          rw [computedVersion] at computed
          cases computed

#assert_axioms prepareFactors

end Minidregg.Effects.Revival
