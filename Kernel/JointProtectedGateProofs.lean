/- Total composition laws for actual NativeHost source gates. -/
import Kernel.NativeHostContext
import Theory.AssertAxioms
namespace Minidregg.Kernel.JointProtectedGateProofs
open Minidregg.Theory
open Minidregg.Compiler
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost
set_option autoImplicit false

theorem invalid_layout_refuses {rootBytes : List UInt8 → TypedAuthorization.Digest}
    (config : Config) (own : Option ControlFacet)
    (snapshot : DataSnapshot rootBytes) (intent : DataIntent rootBytes)
    (invalid : config.controlLayoutValid = false) :
    config.sourceGate own snapshot intent = .error (.durable .transactionConflict) := by
  simp [Config.sourceGate,invalid]; rfl

theorem joint_exception_retains_activity {rootBytes : List UInt8 → TypedAuthorization.Digest}
    (config : Config) (pin : ContentControlFrame.Pin)
    (snapshot : DataSnapshot rootBytes) (intent : DataIntent rootBytes)
    (pinned : config.activityControl = some pin)
    (admitted : config.otherFacetGate .joint snapshot intent = .ok ()) :
    ProtectedContentGate.ordinaryGate pin snapshot intent = .ok () := by
  cases layout : config.controlLayoutValid with
  | false =>
      change config.sourceGate (some .joint) snapshot intent = .ok () at admitted
      rw [invalid_layout_refuses config (some .joint) snapshot intent layout] at admitted
      cases admitted
  | true =>
      cases joint : config.jointControl <;>
        simpa [Config.otherFacetGate,Config.sourceGate,layout,joint,pinned] using admitted

theorem activity_exception_retains_joint {rootBytes : List UInt8 → TypedAuthorization.Digest}
    (config : Config) (pin : JointControlFrame.Pin)
    (snapshot : DataSnapshot rootBytes) (intent : DataIntent rootBytes)
    (pinned : config.jointControl = some pin)
    (admitted : config.otherFacetGate .activity snapshot intent = .ok ()) :
    JointControlFrame.ordinaryGate config.deployment.domain pin snapshot intent = .ok () := by
  cases layout : config.controlLayoutValid with
  | false =>
      change config.sourceGate (some .activity) snapshot intent = .ok () at admitted
      rw [invalid_layout_refuses config (some .activity) snapshot intent layout] at admitted
      cases admitted
  | true =>
      cases jointGate : JointControlFrame.ordinaryGate config.deployment.domain pin snapshot intent with
      | error reason =>
          simp [Config.otherFacetGate,Config.sourceGate,layout,pinned,jointGate,Except.bind] at admitted
          change (Except.error (.durable .transactionConflict) : Except RejectReason Unit) = .ok () at admitted
          cases admitted
      | ok value => cases value; rfl

#assert_axioms invalid_layout_refuses
#assert_axioms joint_exception_retains_activity
#assert_axioms activity_exception_retains_joint
end Minidregg.Kernel.JointProtectedGateProofs
