/- Executed source-level poles for typed content mutation on the one content
store cell. No network, native signature, or linked-host claim is implied by
these kernel-evaluated cases. -/
import Kernel.ContentResource
import Compiler.CanonicalCellRegistry

namespace Minidregg.Kernel.ContentResource.Audit

open Minidregg.Compiler
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
def document : DocumentId := documentOf 100
def empty : ContentStore := initialStore

/-- The post of an accepted run, or the empty store for a refusal. -/
def postOf : Except Reject Progress → ContentStore
  | .ok progress => progress.1
  | .error _ => initialStore

/-- The refusal of a run, if it refused. -/
def refusalOf : Except Reject Progress → Option Reject
  | .ok _ => none
  | .error reason => some reason

def original : AtomRecord := ⟨document, .text, [0, 104, 105, 255], author, operation, operation, none⟩
def create : Command := ⟨[.createAtom atom .text original.payload]⟩
def created : ContentStore := postOf (run author operation document empty create)

theorem create_accepted : refusalOf (run author operation document empty create) = none := by
  decide

theorem create_exact_bytes_and_provenance :
    Hyperdocument.lookup created .atoms atom = some original := by decide

def edit : EditAtomPayload :=
  ⟨atom, original, .inlineObject ⟨42⟩, [255, 0, 1, 2, 3], false⟩
def editCommand : Command := ⟨[.editAtom edit]⟩
def edited : ContentStore := postOf (run author nextOperation document created editCommand)

theorem edit_exact_bytes_and_provenance :
    refusalOf (run author nextOperation document created editCommand) = none ∧
      Hyperdocument.lookup edited .atoms atom = some (editAtomRecord nextOperation edit) := by
  decide

theorem edit_keeps_original_author :
    (editAtomRecord nextOperation edit).createdBy = author := rfl

theorem edit_keeps_original_creation :
    (editAtomRecord nextOperation edit).createdAt = operation := rfl

/-- Same byte length is insufficient: the entire old atom record must match. -/
theorem stale_same_length_bytes_refused :
    refusalOf (run author nextOperation document created
      ⟨[.editAtom { edit with before := { original with payload := [0, 104, 106, 255] } }]⟩) =
      some .staleAtom := by decide

theorem duplicate_identity_refused :
    refusalOf (run author nextOperation document created create) = some .duplicateAddress := by
  decide

theorem forged_old_document_refused :
    refusalOf (run author nextOperation document created
      ⟨[.editAtom { edit with before := { original with document := ⟨⟨999⟩⟩ } }]⟩) =
      some .wrongDocument := by decide

def tombstoned : AtomRecord := { original with tombstonedAt := some nextOperation }

theorem ordinary_edit_cannot_resurrect :
    (editAtomRecord operation { edit with before := tombstoned }).tombstonedAt =
      some nextOperation := rfl

def linkId : LinkId := ⟨⟨102⟩⟩
def remote : LinkTarget := .document ⟨⟨8001⟩⟩
def linked : ContentStore :=
  postOf (run author nextOperation document created ⟨[.link linkId none remote ⟨55⟩]⟩)

theorem typed_reference_created :
    Hyperdocument.lookup linked .links linkId =
      some ⟨document, none, remote, ⟨55⟩, author, nextOperation, none⟩ := by decide

/-- There is no capacity: seventeen further atoms in one command are accepted
(the retired four-slot page refused the fifth record without overflow, and its
sixteen-entry overflow refused the seventeenth). -/
def seventeenAtoms : Command :=
  ⟨(List.range 17).map fun n => .createAtom ⟨⟨200 + n⟩⟩ .text [9]⟩

theorem seventeen_atoms_accepted :
    refusalOf (run author nextOperation document created seventeenAtoms) = none ∧
      Hyperdocument.lookup (postOf (run author nextOperation document created seventeenAtoms))
        .atoms ⟨⟨216⟩⟩ = some ⟨document, .text, [9], author, nextOperation, nextOperation, none⟩ := by
  decide

/-- An earlier successful insertion is not returned when a later action fails. -/
theorem failed_batch_has_no_post :
    refusalOf (run author operation document empty
      ⟨[.createAtom atom .text original.payload,
        .createAtom atom .text [99]]⟩) = some .duplicateAddress := by decide

def deployment : CanonicalCellRegistry.Deployment := ⟨domain, 1, 2, 3⟩

def birth : CellRegistry.PackedCell CanonicalCellRegistry.registry :=
  ⟨.content, CellState.materialize HyperdocumentCell.contentMaterializer empty⟩

theorem neutral_content_birth_admitted :
    CanonicalCellRegistry.UserInitial deployment 100 birth := by
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · intro left member
    exact ((DFinsupp.mem_support_toFun _ _).mp member rfl).elim
  · rfl

theorem authored_history_cannot_be_injected_at_birth :
    ¬CanonicalCellRegistry.UserInitial deployment 100
      ⟨.content, CellState.materialize HyperdocumentCell.contentMaterializer created⟩ := by
  intro admitted
  have supported : (⟨.atoms, atom⟩ : Store.Address Hyperdocument.layout) ∈ created.support := by
    rw [DFinsupp.mem_support_iff]
    change Hyperdocument.lookup created .atoms atom ≠ none
    rw [create_exact_bytes_and_provenance]
    simp
  have shape : created.support = ∅ := admitted.2
  rw [shape] at supported
  exact Finset.notMem_empty _ supported

def runId : RunId := ⟨⟨103⟩⟩
def anchoredRange : StableRange :=
  ⟨⟨runId, some atom, .before, .keepTombstone⟩,
    ⟨runId, some atom, .after, .keepTombstone⟩⟩

def linkedDocument : Command :=
  ⟨[.createDocument ⟨⟨104⟩⟩ ⟨21⟩ (.runs [runId]),
    .createAtom atom .text original.payload,
    .createRun runId [atom],
    .link linkId (some anchoredRange) remote ⟨55⟩]⟩

def linkedDocumentStore : ContentStore := postOf (run author operation document empty linkedDocument)

theorem complete_linked_document_accepted :
    refusalOf (run author operation document empty linkedDocument) = none := by decide

theorem complete_linked_document_has_exact_post :
    Hyperdocument.lookup linkedDocumentStore .documents document =
        some ⟨⟨⟨104⟩⟩, ⟨21⟩, author, operation⟩ ∧
      Hyperdocument.lookup linkedDocumentStore .runs runId =
        some ⟨document, [atom], author, operation, none⟩ ∧
      Hyperdocument.lookup linkedDocumentStore .links linkId =
        some ⟨document, some anchoredRange, remote, ⟨55⟩, author, operation, none⟩ := by
  decide

theorem complete_link_source_has_canonical_membership :
    StoredRangeValidAt linkedDocumentStore document anchoredRange :=
  rangeCheck_sound _ _ _ (by decide)

theorem nonexistent_source_anchor_refused :
    refusalOf (run author operation document created
      ⟨[.link linkId (some anchoredRange) remote ⟨55⟩]⟩) = some .invalidSourceRange := by
  decide

theorem run_cannot_name_absent_atom :
    refusalOf (run author operation document empty ⟨[.createRun runId [atom]]⟩) =
      some .invalidRun := by decide

theorem run_cannot_duplicate_atom :
    refusalOf (run author operation document created ⟨[.createRun runId [atom, atom]]⟩) =
      some .invalidRun := by decide

/-- info: 'Minidregg.Kernel.ContentResource.Audit.create_exact_bytes_and_provenance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms create_exact_bytes_and_provenance
/-- info: 'Minidregg.Kernel.ContentResource.Audit.seventeen_atoms_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms seventeen_atoms_accepted
/-- info: 'Minidregg.Kernel.ContentResource.Audit.authored_history_cannot_be_injected_at_birth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authored_history_cannot_be_injected_at_birth

end Minidregg.Kernel.ContentResource.Audit
