/-
Focused negative probe for the new inner composite birth frame. The admitted
route is checked by the receiver; this only checks the strict wire boundary
and its separation from the pre-existing bare-birth frame.
-/
import Kernel.GrainResourceBirthPolicyController

open Minidregg.Kernel

def malformedGrainBirth : List UInt8 :=
  GrainResourceBirthPolicyController.ingressCodec.encode ⟨[], [], []⟩

def checkIngressBoundary : IO Unit := do
  let malformed := malformedGrainBirth
  unless (GrainResourceBirthPolicyController.decodeIngress malformed).isNone do
    throw <| IO.userError "malformed composite ingress was decoded"
  unless (GrainResourceBirthPolicyController.decodeIngress (malformed ++ [0])).isNone do
    throw <| IO.userError "trailing composite byte was decoded"
  unless (ResourceBirthPolicyController.Concrete.decodeIngress malformed).isNone do
    throw <| IO.userError "composite frame was decoded as bare birth"
  unless (ResourceBirthPolicyController.Concrete.decodeIngress
      (malformed ++ [0])).isNone do
    throw <| IO.userError "malformed composite frame was decoded as bare birth"
  IO.println "grain birth ingress boundary PASS"

#eval checkIngressBoundary
