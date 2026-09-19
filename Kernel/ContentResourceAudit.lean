/- Executed source-level poles for typed content mutation. No network, native
signature, or linked-host claim is implied by these kernel-evaluated cases. -/
import Kernel.ContentResource
import Compiler.CanonicalCellRegistry

namespace Minidregg.Kernel.ContentResource.Audit

open Minidregg.Compiler
open Minidregg.Compiler.HyperdocumentContentPageMaterializer
open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentOperations
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def domain : Digest := ⟨7100⟩
def author : PrincipalRef := ⟨⟨7⟩, .object, ⟨11⟩⟩
def operation : OperationId := ⟨⟨9001⟩⟩
def nextOperation : OperationId := ⟨⟨9002⟩⟩
def atom : AtomId := ⟨⟨101⟩⟩
def empty : Page := initialPage domain 100

def original : AtomRecord :=
  ⟨empty.document, .text, [0, 104, 105, 255], author, operation, none⟩
def created : Page := { empty with slot0 := some (.atom atom original) }
def create : Command := ⟨[.createAtom atom .text original.payload]⟩

def edit : EditAtomPayload :=
  ⟨atom, original, .inlineObject ⟨42⟩, [255, 0, 1, 2, 3], false⟩
def edited : Page :=
  { created with slot0 := some (.atom atom (editAtomRecord nextOperation edit)) }

def editCommand : Command := ⟨[.editAtom edit]⟩

theorem create_exact_bytes_and_provenance :
    run author operation empty create = .ok created := by decide

theorem edit_exact_bytes_and_provenance :
    run author nextOperation created editCommand = .ok edited := by decide

theorem edit_keeps_original_author :
    (editAtomRecord nextOperation edit).createdBy = author := rfl

theorem edit_keeps_original_creation :
    (editAtomRecord nextOperation edit).createdAt = operation := rfl

theorem typed_atom_projects_into_canonical_hyperdocument :
    Hyperdocument.lookup created.toCanonicalState .atoms atom = some original := by
  simp [Hyperdocument.lookup, Page.toCanonicalState, Page.entries, created, empty,
    initialPage, Entry.install, atom]
  rfl

/-- Same byte length is insufficient: the entire old atom record must match. -/
theorem stale_same_length_bytes_refused :
    run author nextOperation created
      ⟨[.editAtom { edit with before := { original with payload := [0, 104, 106, 255] } }]⟩ =
      .error .staleAtom := by decide

theorem duplicate_identity_refused :
    run author nextOperation created create = .error .duplicateAddress := by decide

theorem forged_old_document_refused :
    run author nextOperation created
      ⟨[.editAtom { edit with before := { original with document := ⟨⟨999⟩⟩ } }]⟩ =
      .error .wrongDocument := by decide

def tombstoned : AtomRecord := { original with tombstonedAt := some nextOperation }

theorem ordinary_edit_cannot_resurrect :
    (editAtomRecord operation { edit with before := tombstoned }).tombstonedAt =
      some nextOperation := rfl

def linkId : LinkId := ⟨⟨102⟩⟩
def remotePage : PageRef := ⟨⟨8000⟩, 4, ⟨8150⟩⟩
def forward : ForwardLink :=
  ⟨empty.document, none, .document remotePage ⟨⟨8001⟩⟩, ⟨55⟩,
    author, nextOperation, none⟩
def linked : Page := { created with slot1 := some (.link linkId forward) }

theorem typed_reference_created :
    run author nextOperation created
      ⟨[.link linkId none forward.target forward.relation]⟩ = .ok linked := by decide

theorem reference_preserves_expected_root :
    linked.routeForLink linkId = some remotePage := by decide

def full : Page :=
  { linked with
    slot2 := some (.atom ⟨⟨103⟩⟩ original)
    slot3 := some (.atom ⟨⟨104⟩⟩ original)
    overflow := (List.range 12).map fun n => .atom ⟨⟨200 + n⟩⟩ original }

theorem capacity_refusal_explicit :
    run author nextOperation full
      ⟨[.createAtom ⟨⟨105⟩⟩ .text [9]]⟩ = .error .full := by decide

/-- An earlier successful insertion is not returned when a later action fails. -/
theorem failed_batch_has_no_post :
    run author operation empty
      ⟨[.createAtom atom .text original.payload,
        .createAtom atom .text [99]]⟩ = .error .duplicateAddress := by decide

def deployment : CanonicalCellRegistry.Deployment := ⟨domain, 1, 2, 3⟩
def birth : CellRegistry.PackedCell CanonicalCellRegistry.registry :=
  ⟨.content, CellState.materialize HyperdocumentContentPageMaterializer.materializer
    (stateOfOption (some empty))⟩

theorem neutral_content_birth_admitted :
    CanonicalCellRegistry.UserInitial deployment 100 birth := by decide

theorem authored_history_cannot_be_injected_at_birth :
    ¬CanonicalCellRegistry.UserInitial deployment 100
      ⟨.content, CellState.materialize HyperdocumentContentPageMaterializer.materializer
        (stateOfOption (some created))⟩ := by decide

/-- Observing payload byte counts does not reinterpret bytes as field elements. -/
theorem policy_byte_counts_exact :
    contentPayloadBytes created = 4 ∧ contentPayloadBytes edited = 5 ∧
      contentBytes created < contentBytes edited := by decide

theorem policy_total_size_includes_typed_reference :
    contentBytes created < contentBytes linked := by decide

def runId : RunId := ⟨⟨103⟩⟩
def anchoredRange : StableRange :=
  ⟨⟨runId, some atom, .before, .keepTombstone⟩,
    ⟨runId, some atom, .after, .keepTombstone⟩⟩

def linkedDocument : Command :=
  ⟨[.createDocument ⟨⟨104⟩⟩ ⟨21⟩ (.runs [runId]),
    .createAtom atom .text original.payload,
    .createRun runId [atom],
    .link linkId (some anchoredRange) forward.target forward.relation]⟩

def linkedDocumentPage : Page :=
  { empty with
    slot0 := some (.document empty.document ⟨⟨⟨104⟩⟩, ⟨21⟩, author, operation⟩)
    slot1 := some (.element ⟨⟨104⟩⟩
      ⟨empty.document, none, .runs [runId], author, operation, none⟩)
    slot2 := some (.atom atom original)
    slot3 := some (.run runId ⟨empty.document, [atom], author, operation, none⟩)
    overflow := [.link linkId { forward with source := some anchoredRange, operation := operation }] }

theorem complete_linked_document_has_exact_post :
    run author operation empty linkedDocument = .ok linkedDocumentPage := by decide

theorem complete_linked_document_is_valid : linkedDocumentPage.Valid := by decide

theorem complete_linked_document_uses_fifth_entry :
    linkedDocumentPage.entries.length = 5 := by decide

theorem complete_link_source_has_canonical_membership :
    StoredRangeValidAt linkedDocumentPage.toCanonicalState
      linkedDocumentPage.document anchoredRange :=
  rangeCheck_sound _ _ (by decide)

theorem nonexistent_source_anchor_refused :
    run author operation created
      ⟨[.link linkId (some anchoredRange) forward.target forward.relation]⟩ =
      .error .invalidSourceRange := by decide

theorem run_cannot_name_absent_atom :
    run author operation empty ⟨[.createRun runId [atom]]⟩ = .error .invalidRun := by decide

theorem run_cannot_duplicate_atom :
    run author operation created ⟨[.createRun runId [atom, atom]]⟩ =
      .error .invalidRun := by decide

/-- info: 'Minidregg.Kernel.ContentResource.Audit.create_exact_bytes_and_provenance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms create_exact_bytes_and_provenance

end Minidregg.Kernel.ContentResource.Audit
