/-
# scripts/KernelTransportCensus.lean -- who may judge a write under the object kernel's facet

`domain_holds_forever` and every other invariant of the protected coordinates (activity records,
object records, state, slots, inboxes, domains) is stated over `Step`, whose kernel constructor is
a turn that `ActivitySeatEnd.finish` (or `SeatStore.checkInert`) produced. The deployment writes the
protected coordinates only through a transport judged under `ControlFacet.objectKernel`
(`Config.kernelTransport`); every other transport runs the ordinary gate, which refuses them
(`Config.transport_sourceGate`). So the theorems describe the deployment exactly as long as the only
code that hands out the kernel facet is the code that commits through `finish`:

* `NativeHost.activitySubmitLoaded` -- `ObjectiveActivityReceiver.receiveLoaded` (finish);
* `NativeHost.seatSubmitLoaded`     -- `SeatReceiver.receiveLoaded` (checkInert);
* `NativeHostReplay.Derived.transport` -- replay, only when the record re-derives a `KernelTurn`.

Nothing in the types enforces that list (a new route could pass `config.kernelTransport`, or build
`{ config.transport with sourceGate := config.sourceGate (some .objectKernel) }`, or call
`config.otherFacetGate .objectKernel`, or decode one with `ControlFacet.ofNat`, and write protected cells outside `Step`, silently). This
census is the enforcement: it scans every definition in the environment (theorems excluded: a
theorem cannot write) and refuses unless the definitions mentioning `Config.kernelTransport` and
`ControlFacet.objectKernel` are EXACTLY the rows below. A new caller is a red gate; adding a row is
a reviewed edit of this file, with the reason it commits only through `finish`/`checkInert`.
-/
import Kernel.NativeHost
import Kernel.NativeHostReplay

open Lean Elab Command

namespace KernelTransportCensus

/-- The constants whose use hands out the kernel facet, and the definitions allowed to use each. -/
def rows : List (Name × List Name) :=
  [(``Minidregg.Kernel.NativeHost.Config.kernelTransport,
      [``Minidregg.Kernel.NativeHost.activitySubmitLoaded,
       ``Minidregg.Kernel.NativeHost.seatSubmitLoaded,
       ``Minidregg.Kernel.NativeHostReplay.Derived.transport]),
   (``Minidregg.Kernel.NativeHost.ControlFacet.objectKernel,
      [``Minidregg.Kernel.NativeHost.Config.sourceGate,
       ``Minidregg.Kernel.NativeHost.Config.kernelTransport]),
   -- the enum's decoder: no code may mint a facet from a number
   (``Minidregg.Kernel.NativeHost.ControlFacet.ofNat, [])]

/-- The inductive's own generated machinery (`rec`, `casesOn`, `ofNat`, `ctorElim`, ...) mentions
every constructor; it is not a caller. -/
def ownMachinery (n : Name) : Bool := (``Minidregg.Kernel.NativeHost.ControlFacet).isPrefixOf n

/-- A compiler- or elaborator-generated auxiliary (`match_1`, `_lambda_2`, `proof_3`, `eq_1`, ...)
is attributed to the user definition it belongs to; a private name to its user name. -/
partial def owner (n : Name) : Name :=
  let n := (privateToUserName? n).getD n
  match n with
  | .num p _ => owner p
  | .str p s =>
    if s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_"
        || s.startsWith "lam_" || s.startsWith "spec_" || s == "eq_def" || s == "sizeOf_spec"
        || s.startsWith "_cstage" then owner p
    else n
  | .anonymous => n

def mentions (info : ConstantInfo) (target : Name) : Bool :=
  info.type.getUsedConstants.contains target ||
    match info.value? with
    | some v => v.getUsedConstants.contains target
    | none => false

/-- The census: for each row, the owners of every non-theorem constant that mentions it. -/
def census (env : Environment) : List (Name × List Name) :=
  rows.map fun (target, _) =>
    let users := env.constants.fold (init := ([] : List Name)) fun acc n info =>
      if info matches .thmInfo _ then acc
      else if !(`Minidregg).isPrefixOf (owner n) || ownMachinery (owner n) then acc
      else if n == target || owner n == target then acc
      else if mentions info target then
        let o := owner n
        if acc.contains o then acc else o :: acc
      else acc
    (target, users)

end KernelTransportCensus

open KernelTransportCensus in
run_cmd do
  let env ← getEnv
  let mut failures : Array String := #[]
  for (target, users) in census env do
    let allowed := (rows.lookup target).getD []
    logInfo m!"kernel-transport census: {target} used by {users.reverse}"
    for u in users do
      unless allowed.contains u do
        failures := failures.push s!"{u} uses {target}: not an allowed caller (it must commit only through finish/checkInert, and be added to the census with that reason)"
    for a in allowed do
      unless users.contains a do
        failures := failures.push s!"{a} is allowed to use {target} but does not: the census is stale (remove the row)"
  unless failures.isEmpty do
    for f in failures do logError f
    throwError s!"kernel-transport census: {failures.size} failure(s)"
