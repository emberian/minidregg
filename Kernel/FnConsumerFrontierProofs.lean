/- Shared ordering facts for the two special progress families. -/
module

public import Kernel.FnSelectedPollCoverage
public import Kernel.FnEmptyPollProgressV2

@[expose] public section

namespace Minidregg.Kernel.FnConsumerFrontierProofs

open Minidregg.Kernel

set_option autoImplicit false

/-- Competing selected and empty decisions at the same consumer tip spend the
same durable nullifier, even though their event codecs are distinct. -/
theorem same_tip_nullifier
    (selected : FnSelectedPollCoverage.Spec)
    (empty : FnEmptyPollProgressV2.Spec)
    (domain : selected.domain = empty.domain)
    (semantics : selected.semantics = empty.semantics)
    (key : selected.evidence.key = empty.evidence.key)
    (position : selected.evidence.fromPosition = empty.evidence.fromPosition)
    (predecessor : selected.evidence.predecessor = empty.evidence.predecessor) :
    FnSelectedPollCoverage.frontierNullifier selected =
      FnEmptyPollProgressV2.frontierNullifier empty := by
  simp [FnSelectedPollCoverage.frontierNullifier,
    FnEmptyPollProgressV2.frontierNullifier,
    domain, semantics, key, position, predecessor]

end Minidregg.Kernel.FnConsumerFrontierProofs
