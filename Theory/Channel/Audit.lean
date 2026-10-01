/-
# Theory.Channel.Audit — the axiom pins of `Theory.Channel` (CH-CELL's 120 theorems)

Each theorem of `Theory.Channel.{Cell,Lease,Trace}` rests on at most `propext`, `Classical.choice`,
`Quot.sound`: no `sorryAx`, no compiler trust. The pins moved here from the end of each module
(CH-CLIENT-1) so the modules themselves import nothing but `Init` and the channel library a member
loads carries no Mathlib (`Theory.AssertAxioms` imports `Mathlib.Tactic.Basic` and `Lean`). The pins
are the same lines, in the same order, in the same namespace.
-/
import Theory.Channel
import Theory.Channel.Envelope
import Theory.AssertAxioms

namespace Minidregg.Theory.Channel

/-! ## `Theory.Channel.Cell` -/

#assert_axioms Blob.ext
#assert_axioms fit_val_of_length
#assert_axioms fit_val_of_le
#assert_axioms Profile.C_ge
#assert_axioms Profile.sealedLen_eq
#assert_axioms Profile.dutySealedLen_eq
#assert_axioms Profile.bodyLen_eq
#assert_axioms tagLen_eq
#assert_axioms headerLen_eq
#assert_axioms P0_timed
#assert_axioms P1_timed
#assert_axioms P1phone_timed
#assert_axioms P2_timed
#assert_axioms P2phoneAtPhoneDelta_not_timed
#assert_axioms P1phone_differs_only_in_delta
#assert_axioms P1_layout
#assert_axioms P0_layout
#assert_axioms P2_layout
#assert_axioms U16.ofNat_val_of_lt
#assert_axioms rd16_be16
#assert_axioms be16_rd16
#assert_axioms Header.encode_length
#assert_axioms Header.decode_encode_append
#assert_axioms Header.decode_eq_some
#assert_axioms Body.encode_length
#assert_axioms Cell.ext
#assert_axioms cell_size_exact
#assert_axioms Cell.ofRaw_header
#assert_axioms Cell.bodyBlob_ofRaw
#assert_axioms Cell.ofRaw_bodyBlob
#assert_axioms Cell.encode_eq_header_append
#assert_axioms cell_decode_encode
#assert_axioms cell_decode_canonical
#assert_axioms cell_decode_eq_some_iff
#assert_axioms cell_encode_injective
#assert_axioms cell_decode_refuses_length
#assert_axioms cell_decode_total_on_length
#assert_axioms cell_header_bytes
#assert_axioms SealMode.overhead_le
#assert_axioms Plaintext.encode_length
#assert_axioms Plaintext.decode_encode
#assert_axioms Plaintext.decode_canonical
#assert_axioms Plaintext.encode_injective
#assert_axioms Plaintext.decode_refuses_length
#assert_axioms payload_capacities
#assert_axioms plaintext_fits
#assert_axioms decodeCellBytesList_accepts
#assert_axioms decodeCellBytesList_refuses
#assert_axioms Smoke.p1Cell_size
#assert_axioms Smoke.p2Cell_size
#assert_axioms Smoke.p1Cell_roundtrip
#assert_axioms Smoke.p2Cell_roundtrip
#assert_axioms Smoke.p1Cell_header_bytes
#assert_axioms Smoke.p1_short_refused
#assert_axioms Smoke.p1_long_refused
#assert_axioms Smoke.p1_bytes_refused_at_p2
#assert_axioms Smoke.p1_export_kind
#assert_axioms Smoke.p2_export_kind

/-! ## `Theory.Channel.Lease` -/

#assert_axioms Schedule.mem_slots
#assert_axioms Schedule.headerAt_slot
#assert_axioms fill_is_cell_shaped
#assert_axioms Schedule.assemble_length
#assert_axioms Schedule.assembleAt_header
#assert_axioms Schedule.assembleAt_holder
#assert_axioms Schedule.header_is_schedule
#assert_axioms Schedule.slot_rate_bounded
#assert_axioms Schedule.slot_positions_exact
#assert_axioms Schedule.no_lease_no_cell
#assert_axioms Schedule.holder_cell_assembled
#assert_axioms Schedule.nonholder_never_source
#assert_axioms fanout_independent_of_presence
#assert_axioms Example.class_mismatch_not_live
#assert_axioms Example.example_sources
#assert_axioms Example.example_mask
#assert_axioms Example.header_only_admits_nonholder
#assert_axioms Example.holder_filter_refuses_nonholder
#assert_axioms Example.fill_at_unleased_slot_assembled
#assert_axioms Example.rate_attained
#assert_axioms Example.fanoutConnected_depends_on_presence
#assert_axioms Example.fanout_same_order
#assert_axioms sum_map_const
#assert_axioms fanoutBytesList_length
#assert_axioms assembleBytesList_length
#assert_axioms Example.assembleBytes_smoke
#assert_axioms Example.fanoutBytes_smoke

/-! ## `Theory.Channel.Trace` -/

#assert_axioms designEmission_constant
#assert_axioms designPolicy_fills
#assert_axioms designPolicy_constantFanout
#assert_axioms Domain.emitted_header
#assert_axioms Domain.assembleAt_run
#assert_axioms Domain.cellObs_ofRaw
#assert_axioms Domain.posObs_run
#assert_axioms Domain.tagged_eq_map
#assert_axioms Domain.emittedObs_traffic_invariant
#assert_axioms Domain.posObs_traffic_invariant
#assert_axioms Domain.vector_traffic_invariant
#assert_axioms Domain.observable_trace_depends_only_on_membership
#assert_axioms Domain.emittedObs_holder
#assert_axioms Domain.mem_up
#assert_axioms Domain.wire_reveals_membership
#assert_axioms Domain.hdr_isDutyTick
#assert_axioms Domain.posObs_presence_invariant
#assert_axioms Domain.member_view_independent_of_presence
#assert_axioms Example.fit_take_one
#assert_axioms Example.toy_payloadHidden
#assert_axioms Example.toy_fillHidden
#assert_axioms Example.leaky_not_payloadHidden
#assert_axioms Example.toy_cells_differ
#assert_axioms Example.toy_traces_equal
#assert_axioms Example.onDemand_breaks_membership_theorem
#assert_axioms Example.leaky_breaks_membership_theorem
#assert_axioms Example.presence_visible_to_wire_relay_operator_witness
#assert_axioms Example.membership_visible_to_wire
#assert_axioms Example.relay_sees_presence_change
#assert_axioms Example.toy_duty_agree
#assert_axioms Example.member_blind_to_presence_change
#assert_axioms Example.readable_mask_reveals_presence
#assert_axioms Example.connected_fanout_reveals_presence
#assert_axioms Example.no_fill_reveals_presence
#assert_axioms Example.fill_distinguishable_at_duty_tick

/-! ## `Theory.Channel.Envelope` (CH-CLIENT-1) -/

#assert_axioms payloadCapAt_eq
#assert_axioms sealedLenAt_ge
#assert_axioms envelope_parts_length
#assert_axioms envelopeBody_length
#assert_axioms envelopeCell_encode
#assert_axioms envelopeCell_regular
#assert_axioms envelopeCell_duty
#assert_axioms cut_flatten
#assert_axioms P1_payloadCaps
#assert_axioms sealCellBytesList_is_envelopeCell
#assert_axioms sealCellBytesList_refuses_payload
#assert_axioms openCellBytesList_sealCell
#assert_axioms openCellBytesList_refuses_length

end Minidregg.Theory.Channel
