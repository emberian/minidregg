/- Durable event tags and Host request opcodes are separate namespaces.
These additive tags have one owner each; old admitted event bytes stay exact. -/
namespace Minidregg.Compiler.NativeDurableEventRegistry

def jointReservation : Nat := 60
def jointBootstrap : Nat := 61
def activity : Nat := 62
def privateParty : Nat := 63
def activityPending : Nat := 64
def portableHomeTransfer : Nat := 65
def failedStartRecovery : Nat := 66
-- Reserved source owner; activation requires its typed replay/profile join.
def roomRelease : Nat := 67

def additiveTags : List Nat := [jointReservation, jointBootstrap, activity,
  privateParty, activityPending, portableHomeTransfer, failedStartRecovery, roomRelease]

theorem additiveTags_distinct : additiveTags.Nodup := by decide

theorem additiveTags_fitByte : additiveTags.all (fun tag => decide (tag < 256)) = true := by decide

end Minidregg.Compiler.NativeDurableEventRegistry
