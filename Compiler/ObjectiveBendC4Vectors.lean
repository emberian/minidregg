/- C4 linearization (`Compiler.ObjectiveBendC4`, the linearizer the elaborator runs):
pommette.scm's published precedence vectors and refusals, four DAG local orders, and the
ordered-presentation invariance property (`OrderedPresentationInvariant`, stated, not
proved) checked on 4000 seeded random DAGs with suffix marks. Each is a compiled theorem
(`native_decide`, re-run and named by `#assert_compiled`). -/
import Compiler.ObjectiveBendC4
import Theory.AssertCompiled
namespace Minidregg.Compiler.ObjectiveBendC4Vectors
open Minidregg.Compiler.ObjectiveBendC4
set_option autoImplicit false

/-- Precedence lists of `x` and all its ancestors (an association list), computed bottom-up
with each node's own parents as its local order. Fuel bounds the ancestry depth. -/
def ancestry (supers : String → List String) (isSuffix : String → Bool) :
    Nat → String → Except String (List (String × List String))
  | 0, _ => .error "ancestry depth"
  | fuel + 1, x => do
    let mut known : List (String × List String) := []
    for p in supers x do
      for entry in ← ancestry supers isSuffix fuel p do
        if !(known.any (·.1 == entry.1)) then known := known ++ [entry]
    let graph : Graph := ⟨fun y => (known.lookup y).getD [], isSuffix⟩
    let (list, _) ← (linearize graph [x] [supers x]).mapError Refusal.message
    return known ++ [(x, list)]

def precedenceOf (supers : String → List String) (isSuffix : String → Bool) (x : String) : Option (List String) :=
  match ancestry supers isSuffix 64 x with
  | .ok known => known.lookup x
  | .error _ => none

/-! ## pommette's vectors -/

def table : List (String × List String) :=
  ("O|A O|B O|C O|D O|E O|K1 A B C|K2 D B E|K3 D A|Z K1 K2 K3|J1 C A B|J2 B D E|J3 A D|Y J1 J3 J2|DB B|WB B|" ++
   "EL DB|SM DB|PWB EL WB|SC SM|P PWB SC|GL O|HG GL|VG GL|HVG HG VG|VHG VG HG|HH|GG HH|II GG|FF HH|EE HH|" ++
   "DD FF|CC EE FF GG|BB|AA BB CC DD|o O|a o|b a|c b o|d D c|M A B b a|N C c|L M N|k D L|j E k A|I N M|x1|x2 x1|" ++
   "x3 x2|x4 x3|x5 x4 x1|SBA|SBB|SBS SBA|sBs SBA|SBC SBS SBB").splitOn "|" |>.map fun row =>
    match row.splitOn " " with
    | x :: ps => (x, ps)
    | [] => ("", [])

def supers (x : String) : List String := (table.lookup x).getD []
def isStruct (x : String) : Bool := match x.toList.head? with | some c => 'a' ≤ c && c ≤ 'z' | none => false

def expected : List String :=
  ("O|A O|B O|C O|D O|E O|K1 A B C O|K2 D B E O|K3 D A O|Z K1 K2 K3 D A B C E O|J1 C A B O|J2 B D E O|J3 A D O|" ++
   "Y J1 C J3 A J2 B D E O|DB B O|WB B O|EL DB B O|SM DB B O|PWB EL DB WB B O|SC SM DB B O|P PWB EL SC SM DB WB B O|" ++
   "GL O|HG GL O|VG GL O|HVG HG VG GL O|VHG VG HG GL O|HH|GG HH|II GG HH|FF HH|EE HH|DD FF HH|CC EE FF GG HH|BB|" ++
   "AA BB CC EE DD FF GG HH|o O|a o O|b a o O|c b a o O|d D c b a o O|M A B b a o O|N C c b a o O|" ++
   "L M A B N C c b a o O|k D L M A B N C c b a o O|j E k D L M A B N C c b a o O|I N C M A B c b a o O|x1|x2 x1|" ++
   "x3 x2 x1|x4 x3 x2 x1|x5 x4 x3 x2 x1|SBA|SBB|SBS SBA|sBs SBA|SBC SBS SBA SBB").splitOn "|"

def vectorsHold : Bool :=
  expected.all fun line =>
    let names := line.splitOn " "
    precedenceOf supers isStruct names.head! == some names

theorem pommette_vectors : vectorsHold = true := by native_decide

/-- CG (inconsistent local orders) and SBc (incompatible suffix parents) refuse. -/
theorem pommette_refusals :
    precedenceOf (fun x => if x == "CG" then ["HVG", "VHG"] else supers x) isStruct "CG" = none ∧
    precedenceOf (fun x => if x == "SBc" then ["sBs", "SBB"] else supers x) isStruct "SBc" = none := by
  native_decide

def precedenceGraph : Graph := ⟨fun x => (precedenceOf supers isStruct x).getD [], isStruct⟩

/-- **Fuel exhaustion is not inconsistency.** A cyclic local order (A before B before C before A)
is refused `inconsistent`; SBc's incompatible suffix parents are refused `inconsistent`; and a
suffix chain that cannot end within its derived fuel (a suffix oracle whose chain cycles,
`cyclicSuffix`) is refused `fuelExhausted`, never reported as an inconsistent graph. -/
def cyclicTable : List (String × List String) :=
  [("P", ["P", "S1"]), ("Q", ["Q", "S2"]), ("S1", ["S1", "U"]), ("U", ["U", "V"]), ("V", ["V", "U"]),
   ("S2", ["S2", "W"]), ("W", ["W", "X"]), ("X", ["X", "W"])]
def cyclicSuffix : Graph := ⟨fun x => (cyclicTable.lookup x).getD [x], fun x => x != "P" && x != "Q"⟩

def refusalKind : Except Refusal (List String × Option String) → String
  | .error (.inconsistent _ _) => "inconsistent"
  | .error (.fuelExhausted _ _) => "fuel"
  | .ok _ => "ok"

theorem fuel_is_not_inconsistency :
    refusalKind (linearize precedenceGraph [] [["A", "B"], ["B", "C"], ["C", "A"]]) = "inconsistent" ∧
    refusalKind (linearize (⟨fun x => if x == "SBc" then ["SBc", "sBs", "SBB"] else (precedenceOf supers isStruct x).getD [x],
      isStruct⟩ : Graph) ["SBc"] [["sBs", "SBB"]]) = "inconsistent" ∧
    refusalKind (linearize cyclicSuffix ["X"] [["P", "Q"]]) = "fuel" := by
  native_decide
def dag (order : List (List String)) : Option (List String) := (linearize precedenceGraph [] order).toOption.map (·.1)

theorem dag_local_orders :
    dag [["A"], ["B"], ["C"]] = some ["A", "B", "C", "O"] ∧ dag [["A", "B"], ["C", "A"]] = some ["C", "A", "B", "O"] ∧
    dag [["C", "A"], ["C", "B"]] = some ["C", "A", "B", "O"] ∧ dag [["C", "B"], ["C", "A"]] = some ["C", "B", "A", "O"] ∧
    dag [["A", "B"], ["B", "C"], ["C", "A"]] = none := by
  native_decide

/-! ## Ordered-presentation invariance on seeded random DAGs -/

structure Dag where
  parents : Array (List Nat)
  suffix : Array Bool

def lcg (seed : Nat) : Nat := (seed * 1103515245 + 12345) % 2147483648

/-- A seeded DAG on `n` nodes: node `i` draws each earlier node with probability ~0.45, in a
shuffled order, and is a suffix node with probability ~0.25; plus a random renaming. -/
def generate (seed : Nat) : Dag × Array Nat × Nat := Id.run do
  let mut s := lcg seed
  let n := 2 + s % 6
  let mut parents : Array (List Nat) := #[]
  let mut suffix : Array Bool := #[]
  for i in [0:n] do
    let mut pool : Array Nat := #[]
    for j in [0:i] do
      s := lcg s
      if s % 100 < 45 then pool := pool.push j
    for k in [0:pool.size] do
      let j := pool.size - 1 - k
      s := lcg s
      let r := s % (j + 1)
      pool := pool.swapIfInBounds j r
    parents := parents.push pool.toList
    s := lcg s
    suffix := suffix.push (s % 100 < 25)
  let mut perm : Array Nat := Array.range n
  for k in [0:n] do
    let j := n - 1 - k
    s := lcg s
    perm := perm.swapIfInBounds j (s % (j + 1))
  return (⟨parents, suffix⟩, perm, s)

def runDag (g : Dag) (names : Array String) : Array (Option (List String)) :=
  let index (x : String) : Nat := (names.findIdx? (· == x)).getD 0
  let supers (x : String) := (g.parents[index x]!).map (names[·]!)
  let isSuffix (x : String) := g.suffix[index x]!
  names.map (precedenceOf supers isSuffix)

def isSubsequence (sub list : List String) : Bool :=
  (list.foldl (fun rest x => match rest with | y :: more => if x == y then more else rest | [] => []) sub).isEmpty

/-- One DAG: renaming commutes with linearization (results and refusals), and every
accepted list satisfies inheritance order, local order, monotonicity and the suffix
property. Returns the accepted and refused counts, or `none` on a violation. -/
def checkDag (seed : Nat) : Option (Nat × Nat) := do
  let (g, perm, _) := generate seed
  let n := g.parents.size
  let base := (Array.range n).map (fun i => "n" ++ toString i)
  let renamed := perm.map (fun i => "r" ++ toString i)
  let a := runDag g base
  let b := runDag g renamed
  let rename (x : String) : String := renamed[(base.findIdx? (· == x)).getD 0]!
  let mut accepted := 0
  let mut refused := 0
  for i in [0:n] do
    if (a[i]!).map (·.map rename) != b[i]! then none
    match a[i]! with
    | none => refused := refused + 1
    | some p =>
      accepted := accepted + 1
      if p.head? != some base[i]! || p.eraseDups.length != p.length then none
      for parent in g.parents[i]! do
        let some pp := a[parent]! | none
        if !isSubsequence pp p || (p.idxOf base[parent]!) < 1 || !p.contains base[parent]! then none
      if !isSubsequence ((g.parents[i]!).map (base[·]!)) p then none
      for x in p.drop 1 do
        let j := (base.findIdx? (· == x)).getD 0
        if g.suffix[j]! then
          let some sp := a[j]! | none
          if p.drop (p.length - sp.length) != sp then none
  return (accepted, refused)

def trials : Nat := 4000

def invariance : Option (Nat × Nat) :=
  (List.range trials).foldlM (init := (0, 0)) fun (acc, ref) t => do
    let (a, r) ← checkDag (20261004 + 7919 * t)
    return (acc + a, ref + r)

/-- Every trial passes, and the family is not vacuous: it has both accepted and refused nodes. -/
theorem ordered_presentation_invariance_4000 :
    invariance.map (fun (accepted, refused) => decide (0 < accepted) && decide (0 < refused)) = some true := by
  native_decide

#assert_compiled pommette_vectors
#assert_compiled pommette_refusals
#assert_compiled dag_local_orders
#assert_compiled fuel_is_not_inconsistency
#assert_compiled ordered_presentation_invariance_4000

/-- The gate's marker line, computed from the same checks. -/
def summary : String :=
  match invariance with
  | some (accepted, refused) =>
    "C4 ORDERED-PRESENTATION INVARIANCE PASS: " ++ toString trials ++ " seeded random DAGs, " ++ toString accepted ++
      " precedence lists satisfy inheritance/local order/monotonicity/suffix, " ++ toString refused ++
      " refusals rename identically; " ++ toString expected.length ++ " pommette vectors"
  | none => "C4 INVARIANCE FAILED"

end Minidregg.Compiler.ObjectiveBendC4Vectors
