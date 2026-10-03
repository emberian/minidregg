/- Narrow native declaration/refuser poles. These do not claim source execution
or signed settlement receiving; those require the joined current world fixture. -/
import Kernel.ResourceMoneyReceiver
import Theory.AssertAxioms

namespace Minidregg.Assurance.ResourceMoneyReceiverAudit
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Kernel.ResourceMoneyWire
open Minidregg.Kernel.ResourceMoneyReceiver
set_option autoImplicit false

def batch : ApplicationBatch :=
  ⟨⟨0⟩, [.transfer 1 2 7 4, .transfer 2 1 8 12,
    .transfer 1 3 7 3, .transfer 3 1 8 9]⟩

def entries : List Entry :=
  [⟨1, ⟨some batch, [0, 2], none⟩⟩,
   ⟨2, ⟨none, [1], none⟩⟩,
   ⟨3, ⟨none, [3], none⟩⟩]

theorem repeated_source_positions_are_covered : Covered entries batch := by decide

theorem wrong_account_position_refused :
    ¬ Covered [⟨1, ⟨some batch, [0, 1, 2], none⟩⟩,
      ⟨2, ⟨none, [], none⟩⟩, ⟨3, ⟨none, [3], none⟩⟩] batch := by decide

theorem duplicate_position_refused :
    ¬ Covered [⟨1, ⟨some batch, [0, 0, 2], none⟩⟩,
      ⟨2, ⟨none, [1], none⟩⟩, ⟨3, ⟨none, [3], none⟩⟩] batch := by decide

theorem out_of_range_position_refused :
    ¬ Covered [⟨1, ⟨some batch, [0, 2, 4], none⟩⟩,
      ⟨2, ⟨none, [1], none⟩⟩, ⟨3, ⟨none, [3], none⟩⟩] batch := by decide

theorem missing_destination_participant_refused :
    ¬ Covered [⟨1, ⟨some ⟨⟨0⟩, [.transfer 1 2 8 1]⟩, [0], none⟩⟩]
      ⟨⟨0⟩, [.transfer 1 2 8 1]⟩ := by decide

theorem duplicate_account_alias_refused :
    ¬ Covered [⟨1, ⟨some batch, [0], none⟩⟩, ⟨1, ⟨none, [2], none⟩⟩,
      ⟨2, ⟨none, [1], none⟩⟩, ⟨3, ⟨none, [3], none⟩⟩] batch := by decide

theorem incoming_credit_does_not_discount_consent :
    debit ⟨⟨0⟩, [.transfer 2 1 8 12, .transfer 1 2 8 12]⟩
      ⟨2, ⟨none, [0], none⟩⟩ 8 = 12 := by decide

theorem actual_operation_stream_roundtrip (value : ApplicationBatch) :
    batchStream.toLawful.decode (batchStream.encode value) = some value :=
  batchStream.toLawful.decode_encode value

theorem actual_consent_stream_roundtrip (value : Consent) :
    consentStream.toLawful.decode (consentStream.encode value) = some value :=
  consentStream.toLawful.decode_encode value

#assert_axioms repeated_source_positions_are_covered
#assert_axioms wrong_account_position_refused
#assert_axioms duplicate_position_refused
#assert_axioms out_of_range_position_refused
#assert_axioms missing_destination_participant_refused
#assert_axioms duplicate_account_alias_refused
#assert_axioms incoming_credit_does_not_discount_consent
#assert_axioms actual_operation_stream_roundtrip
#assert_axioms actual_consent_stream_roundtrip
#assert_axioms ResourceMoneyReceiver.Prepared.conserves
#assert_axioms ResourceMoneyReceiver.Prepared.exact_original_root
#assert_axioms ResourceMoneyReceiver.Prepared.one_batch
#assert_axioms ResourceMoneyReceiver.Prepared.no_duplicate_accounts

/-- Production payment verbs cannot authorize issuer-backed mint or burn. -/
theorem transfer_does_not_authorize_mint :
    ¬ Verb.AllowedBy .mintAsset ({.transfer} : Finset (Verb .account)) := by decide

theorem transfer_does_not_authorize_burn :
    ¬ Verb.AllowedBy .burnAsset ({.transfer} : Finset (Verb .account)) := by decide

#assert_axioms transfer_does_not_authorize_mint
#assert_axioms transfer_does_not_authorize_burn

end Minidregg.Assurance.ResourceMoneyReceiverAudit
