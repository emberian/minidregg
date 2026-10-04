/- C4 linearization (ltuo §7.4.4): C3 plus the suffix property. A port of
pommette.scm `c4-linearize`; its published vectors are compiled theorems in
`Compiler.ObjectiveBendC4Vectors`. Specifications are identified by declaration keys. -/
import Std.Data.HashMap
namespace Minidregg.Compiler.ObjectiveBendC4
set_option autoImplicit false

/-- A precedence oracle: `precedence x` starts with `x` itself. -/
structure Graph where
  precedence : String → List String
  isSuffix : String → Bool

def superSuffix (g : Graph) (x : String) : Option String :=
  ((g.precedence x).drop 1).find? g.isSuffix

/-- Is `s2` reachable from `s1` along the super-suffix chain (or absent)? -/
def isSuperSuffix (g : Graph) : Nat → Option String → Option String → Bool
  | _, _, none => true
  | 0, _, _ => false
  | _ + 1, none, some _ => false
  | fuel + 1, some s, some target => s == target || isSuperSuffix g fuel (superSuffix g s) (some target)

def mergeSuffixFrom (g : Graph) (a b : String) (fuel : Nat) :
    Nat → Option String → Option String → Except String (Option String)
  | 0, _, _ => .error "suffix chain fuel"
  | steps + 1, t1, t2 =>
    if t1 == some b then .ok (some a)
    else if t2 == some a then .ok (some b)
    else match t1, t2 with
      | none, _ => if isSuperSuffix g fuel t2 (some a) then .ok (some b)
          else .error ("suffix incompatibility " ++ a ++ " " ++ b)
      | _, none => if isSuperSuffix g fuel t1 (some b) then .ok (some a)
          else .error ("suffix incompatibility " ++ a ++ " " ++ b)
      | some x, some y => mergeSuffixFrom g a b fuel steps (superSuffix g x) (superSuffix g y)

def mergeSuffix (g : Graph) (fuel : Nat) : Option String → Option String → Except String (Option String)
  | s1, none => .ok s1
  | none, s2 => .ok s2
  | some a, some b => mergeSuffixFrom g a b fuel fuel (some a) (some b)

/-- Re-reverse a reversed candidate list, dropping suffix-tail members, which
must appear in increasing tail-index order. -/
def removeSuffixTailAndReverse (tailIndex : Std.HashMap String Nat) : List String → Int → Except String (List String)
  | [], _ => .ok []
  | c :: rest, suffixPos =>
    match tailIndex.get? c with
    | none =>
      let taken := rest.takeWhile (fun x => !tailIndex.contains x)
      let remaining := rest.drop taken.length
      match remaining with
      | [] => .ok (taken.reverse ++ [c])
      | x :: _ => .error ("ancestor out of order versus suffix tail " ++ x)
    | some p =>
      if (p : Int) > suffixPos then removeSuffixTailAndReverse tailIndex rest p
      else .error ("ancestor out of order versus suffix tail " ++ c)

def inconsistent {α : Type} (head : List String) (detail : String) : Except String α :=
  .error ("inconsistent precedence graph at " ++ String.intercalate "," head ++ ": " ++ detail)

/-- `head` is prepended (usually `[x]`); `parents` are local precedence chains. -/
def linearize (g : Graph) (head : List String) (parentsIn : List (List String)) :
    Except String (List String × Option String) := do
  let parents := parentsIn.filter (fun chain => !chain.isEmpty)
  match parents with
  | [] => return (head, none)
  | [[parent]] => return (head ++ g.precedence parent,
      if g.isSuffix parent then some parent else superSuffix g parent)
  | _ =>
  let fuel := 1000000
  let mut rcandidates : List (List String) := []
  let mut ss : Option String := none
  let mut ssTail : List String := []
  let mut counts : Std.HashMap String Int := {}
  for chain in parents do
    for parent in chain do
      if counts.getD parent 0 != 0 then continue
      let al := g.precedence parent
      let pre := al.takeWhile (fun x => !g.isSuffix x)
      let rest := al.drop pre.length
      for x in pre do counts := counts.insert x (counts.getD x 0 + 1)
      match rest with
      | [] => pure ()
      | s :: _ =>
        let merged ← match mergeSuffix g fuel (some s) ss with
          | .ok v => pure v
          | .error e => inconsistent head e
        if merged != ss then
          for t in (rest.takeWhile (fun t => some t != ss)) do
            counts := counts.insert t (counts.getD t 0 + 1)
          ss := merged
          ssTail := rest
      if !pre.isEmpty then rcandidates := pre.reverse :: rcandidates
  let mut tailIndex : Std.HashMap String Nat := {}
  let mut position := ssTail.length
  for t in ssTail do
    tailIndex := tailIndex.insert t position
    position := position - 1
  let rLocalOrder := (parents.filter (fun chain => chain.length > 1)).map List.reverse
  for chain in rLocalOrder do
    for c in chain do counts := counts.insert c (counts.getD c 0 + 1)
  rcandidates := rLocalOrder ++ rcandidates
  let mut cleaned : List (List String) := []
  for rcl in rcandidates do
    match removeSuffixTailAndReverse tailIndex rcl (-1) with
    | .ok l => if !l.isEmpty then cleaned := cleaned ++ [l]
    | .error e => inconsistent head e
  let candidates := cleaned.reverse
  for cl in candidates do
    match cl with
    | c :: _ => counts := counts.insert c (counts.getD c 0 - 1)
    | [] => pure ()
  let mut out := head
  let mut tails := candidates
  for _ in List.range fuel do
    match tails with
    | [] => return (out ++ ssTail, ss)
    | [only] => return (out ++ only ++ ssTail, ss)
    | _ =>
      let some winner := tails.find? (fun t => match t with | c :: _ => counts.getD c 0 == 0 | [] => false)
        | inconsistent head "no C3 candidate"
      let next := winner.head!
      out := out ++ [next]
      let mut updated : List (List String) := []
      for t in tails do
        match t with
        | c :: rest' =>
          if c == next then
            match rest' with
            | d :: _ => counts := counts.insert d (counts.getD d 0 - 1)
            | [] => pure ()
            if !rest'.isEmpty then updated := updated ++ [rest']
          else updated := updated ++ [t]
        | [] => pure ()
      tails := updated
  inconsistent head "linearization fuel"

/-- Renaming a graph along a bijection (`to`, with inverse `back`). -/
def Graph.rename (g : Graph) (to back : String → String) : Graph :=
  ⟨fun y => (g.precedence (back y)).map to, fun y => g.isSuffix (back y)⟩

/-- ORDERED-PRESENTATION INVARIANCE (scholar §5, proposed theorem), stated, not
yet proved. Linearization commutes with every renaming of specification
identities: the precedence list (and its most specific suffix) of the renamed
presentation is the renamed result, and a refusal stays a refusal. It is a
claim about the ORDERED presentation (local parent sequences and suffix
marks), not about a bare DAG: a bare symmetric poset admits no equivariant
strict order. Current evidence: `Compiler.ObjectiveBendC4Vectors.ordered_presentation_invariance_4000`
checks it (compiled) on 4000 seeded random DAGs with suffix marks. Its premises are
inhabited by the identity renaming. -/
def OrderedPresentationInvariant : Prop :=
  ∀ (g : Graph) (to back : String → String),
    (∀ x, back (to x) = x) → (∀ y, to (back y) = y) →
    ∀ (head : List String) (parents : List (List String)),
      (linearize (g.rename to back) (head.map to) (parents.map (·.map to))).toOption =
        (linearize g head parents).toOption.map (fun r => (r.1.map to, r.2.map to))

end Minidregg.Compiler.ObjectiveBendC4
