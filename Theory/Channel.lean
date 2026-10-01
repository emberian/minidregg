/-
# Theory.Channel — constant-rate ordered broadcast domains (CHANNELS.md §2, revision 2)

* `Theory.Channel.Cell` — the class `(C, r, E, δ, δ_relay, μ)`, P0/P1/P1-phone/P2; the fixed-size cell
  (regular `8 | C−24 | 16`, duty `8 | 96 | 32 | 32 | C−184 | 16`) and its canonical codec; the sealed
  plaintext `viewTag 1 | frag 4 | [epk 32] | payload`; `@[export]` codec entry points.
* `Theory.Channel.Lease` — `Lease`, `Schedule`, `fillCell`, `assemble` (with fills and the absent mask),
  `fanout`; `slot_rate_bounded`, `no_lease_no_cell`, `fill_is_cell_shaped`,
  `fanout_independent_of_presence`; `@[export]` of `assemble` and `fanout` on bytes.
* `Theory.Channel.Trace` — the observers (wire, relay, operator, witness, non-recipient member), the
  sealing hypotheses `PayloadHidden` / `FillHidden`, `observable_trace_depends_only_on_membership`,
  `member_view_independent_of_presence`, and every pole on a concrete instance.
-/
import Theory.Channel.Cell
import Theory.Channel.Lease
import Theory.Channel.Trace
