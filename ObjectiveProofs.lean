/- Objective Bend Core4 metatheory: the proofs about the default-build definitions
(Theory.ObjectiveBend{Types,OpenRecursion,Typing,DemandMachine,DemandData,
DemandCapacity,Extensions}). A separate library so its build is its own gate:
`lake build ObjectiveProofs`. -/
import Theory.ObjectiveBendDemandInvariant
import Theory.ObjectiveBendDemandTyping
import Theory.ObjectiveBendDemandPreservation
import Theory.ObjectiveBendDemandAdequacy
import Theory.ObjectiveBendDemandCompleteness
import Theory.ObjectiveBendDemandDataSoundness
