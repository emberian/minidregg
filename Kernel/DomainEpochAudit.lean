/-
# Kernel.DomainEpochAudit — the axiom pins of the channel epoch modules

Every theorem of `Kernel.DomainEpoch`, `Kernel.DomainEpochLaw` and `Kernel.DomainEpochExport` rests on
at most `propext`, `Classical.choice`, `Quot.sound`: no `sorryAx`, no compiler trust, no hash axiom
(binding is the `Collision` disjunct). The pins moved here from the end of each module (CH-CLIENT-1) so
the runtime closure (`Kernel.DomainEpochExport`, linked into `libminidregg-channel.so`) has no Mathlib.
Same lines, same order, same namespaces.

One theorem lives here rather than in a module: `topicBytesList_is_recordAppend` ties the topic export
(runtime) to the kernel's `recordAppend` (`Kernel.DomainEpochLaw`, which imports K-STREAM), and this is
the first module that sees both.
-/
import Kernel.DomainEpochExport
import Kernel.DomainEpochLaw
import Theory.Channel.Audit
import Theory.AssertAxioms

namespace Minidregg.Kernel.DomainEpoch

open Minidregg.Theory.Channel (Blob fit Profile U16 be16 rd16 rd16_be16 Header Cell Schedule FillPrf
  fillCell Submission Source profileOfId cell_encode_injective)
open Minidregg.Pred.HashEqDigest (be ofBE Collision utf8 length_be)
open Minidregg.Compiler.Sp800185Cshake256 (cshake256Bytes cshake256Bytes_length)

/-! ## `Kernel.DomainEpoch` and `Kernel.DomainEpochLaw` (one namespace) -/

#assert_axioms collision_of
#assert_axioms ofBE_append
#assert_axioms ofBE_be
#assert_axioms flat_injective
#assert_axioms flat_length
#assert_axioms chunks_flat
#assert_axioms epochRecord_size
#assert_axioms epochRecord_parse_encode
#assert_axioms epochRecord_decode_encode
#assert_axioms epochRecord_decode_canonical
#assert_axioms epochRecord_decode_eq_some_iff
#assert_axioms epochRecord_encode_injective
#assert_axioms epochRecord_decode_refuses_length
#assert_axioms bit_injective
#assert_axioms map_bit_injective
#assert_axioms absentOpening_encode_injective
#assert_axioms absentOpening_size
#assert_axioms absentOpening_decode_encode
#assert_axioms absentOpening_decode_canonical
#assert_axioms absentOpening_wrong_length_refused
#assert_axioms commitAbsent_val
#assert_axioms opening_binds_with
#assert_axioms opening_binds
#assert_axioms lengthHash_opening_binding_fails
#assert_axioms checkShape_ok_iff
#assert_axioms checkLink_ok_iff
#assert_axioms checkRecord_ok_iff
#assert_axioms next_record_admitted
#assert_axioms first_record_admitted
#assert_axioms shape_refusal_first
#assert_axioms gap_refused
#assert_axioms out_of_order_refused
#assert_axioms foreign_author_refused
#assert_axioms foreign_domain_refused
#assert_axioms root_count_refused
#assert_axioms topicMagic_length
#assert_axioms classifyTopic_channelTopic
#assert_axioms channelTopic_length
#assert_axioms admitAppend_record
#assert_axioms admitAppend_record_ok_iff
#assert_axioms empty_channel_lawful
#assert_axioms cell_binds
#assert_axioms tick_binds
#assert_axioms digests_bind
#assert_axioms committed_cells_agree
#assert_axioms committed_cells_agree_cells
#assert_axioms shaped_length
#assert_axioms shaped_header
#assert_axioms headerAt_injective
#assert_axioms shaped_mem
#assert_axioms own_omission_evident
#assert_axioms flatMap_congr_mem
#assert_axioms getElem?_flatMap_range
#assert_axioms absentMask_getElem?
#assert_axioms absentMask_length
#assert_axioms epochMask_getElem?
#assert_axioms epochMask_length
#assert_axioms assembleAt_fill
#assert_axioms assemble_getElem?
#assert_axioms sealEpoch_root
#assert_axioms assemble_shaped
#assert_axioms assembled_included
#assert_axioms absent_position_holds_fill
#assert_axioms omission_evident
#assert_axioms seal_depends_only_on_received
#assert_axioms openRecord_sound
#assert_axioms openRecord_wrong_length_refused
#assert_axioms openRecord_epochOpening
#assert_axioms relay_equivocation_transferable
#assert_axioms equivocation_check_sound
#assert_axioms equivocation_unsigned_refused
#assert_axioms equivocation_same_record_refused
#assert_axioms admitAppend_link
#assert_axioms admittedHistory_last
#assert_axioms historyLaw_tail
#assert_axioms admittedHistory_chain
#assert_axioms channel_epochs_from_head
#assert_axioms ordinary_after_channel_refused
#assert_axioms channel_after_ordinary_refused
#assert_axioms admittedHistory_count
#assert_axioms admittedHistory_head_lawful
#assert_axioms admittedHistory_one_record_per_epoch
#assert_axioms Example.cached_next_admitted
#assert_axioms Example.cached_gap_refused
#assert_axioms Example.cached_repeat_refused
#assert_axioms Example.cached_stranger_refused
#assert_axioms Example.cached_ordinary_refused
#assert_axioms Example.cached_foreign_domain_refused
#assert_axioms Example.cached_channel_after_ordinary_refused
#assert_axioms channel_epochs_advance
#assert_axioms one_record_per_epoch
#assert_axioms Example.first_admitted
#assert_axioms Example.next_admitted
#assert_axioms Example.gap_refused
#assert_axioms Example.out_of_order_refused
#assert_axioms Example.repeat_refused
#assert_axioms Example.short_refused
#assert_axioms Example.long_refused
#assert_axioms Example.stranger_refused
#assert_axioms Example.record_size
#assert_axioms Example.opening_wrong_length_refused
#assert_axioms Example.opening_long_refused
#assert_axioms Example.opening_byte_refused
#assert_axioms Example.silent_slot_marked
#assert_axioms Example.mine_not_fill
#assert_axioms Example.omission_evident_instance
#assert_axioms Example.theirs_included
#assert_axioms Example.forged_mask_marks_included
#assert_axioms Example.fill_included_at_absent
#assert_axioms Example.own_omission_evident_instance
#assert_axioms Example.unshaped_opens_both
#assert_axioms Example.committed_cells_agree_instance
#assert_axioms Example.different_records_different_vectors
#assert_axioms Example.silent_and_dropped_indistinguishable
#assert_axioms Example.seal_opens

end Minidregg.Kernel.DomainEpoch

namespace Minidregg.Kernel.DomainEpochExport

open Minidregg.Theory.Channel
open Minidregg.Kernel.DomainEpoch

set_option autoImplicit false

/-- **The topic export is the append's topic** for the record of that domain and epoch. -/
theorem topicBytesList_is_recordAppend (r : EpochRecord) :
    topicBytesList r.domain.val r.epoch.toNat = (recordAppend r).topic := by
  simp [topicBytesList, recordAppend, U16.ofNat_val, UInt64.ofNat_toNat]

/-! ## `Kernel.DomainEpochExport` -/

#assert_axioms slices_flatMap
#assert_axioms length_flatMap_const
#assert_axioms U16.ofNat_val
#assert_axioms profileBytesList_is_profile
#assert_axioms profileBytesList_refuses
#assert_axioms headerBytesList_is_headerAt
#assert_axioms rootOfCells_vector
#assert_axioms tickRootBytesList_is_vectorRoot
#assert_axioms tickRootBytesList_refuses_length
#assert_axioms tickOut_length
#assert_axioms tickRoot_of_assemble
#assert_axioms assembleBytesList_is_tickOut
#assert_axioms tickOut_prf_congr
#assert_axioms map_beq_one_bit
#assert_axioms all_bit_le_one
#assert_axioms sealBytesList_is_sealEpoch
#assert_axioms sealBytesList_length
#assert_axioms sealBytesList_refuses_length
#assert_axioms relay_pipeline_is_sealEpoch
#assert_axioms commitAbsentBytesList_is_commitAbsent
#assert_axioms openBytesList_is_openRecord
#assert_axioms sealed_opening_opens
#assert_axioms openBytesList_wrong_length
#assert_axioms recordRootsBytesList_encode
#assert_axioms recordRootsBytesList_refuses
#assert_axioms topicBytesList_is_recordAppend

end Minidregg.Kernel.DomainEpochExport
