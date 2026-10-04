/-
# scripts/NativeTranscripts.lean -- every recorded verifier transcript in the tree

A `CredentialSignatureIO.Transcript` stands in for the native signature verifier
inside a Lean fixture that evaluates a real admission
(`Assurance.NativeAcceptedFixture`).  It is trusted exactly as far as the pinned
verifier still answers `verified` on each of its triples, so this file finds EVERY
transcript the research umbrella holds and prints its triples for
`scripts/check-native-transcripts.sh`, which re-submits them to the verifier.

Closed world: a constant whose value builds a transcript (`Transcript.mk`) must
itself be a named `Transcript` (it is printed); a `Transcript.mk` buried in any
other definition (a config, a helper) is refused here, so no transcript can escape
the re-verification.

Output, one line per triple: `TRIPLE<TAB>constant<TAB>index<TAB>key<TAB>frame<TAB>signature`
(lowercase hex), then `TRANSCRIPTS<TAB>n<TAB>triples<TAB>m`.

Run: `lake env lean scripts/NativeTranscripts.lean` (needs AxiomCensusResearch built).
-/
import AxiomCensusResearch

open Lean Meta

namespace Minidregg.NativeTranscripts

def hex (bytes : List UInt8) : String :=
  String.join (bytes.map fun b =>
    let s := String.ofList (Nat.toDigits 16 b.toNat)
    if s.length = 1 then "0" ++ s else s)

/-- Does `e` BUILD a transcript: `Transcript.mk` applied to a closed argument (a
recorded list), or `Transcript.mk` used as a value?  Its application to bound
variables -- the pattern in a `casesOn`, `noConfusion` or derived `DecidableEq` --
takes a transcript apart and builds none. -/
def builds (mk : Name) (e : Expr) : Bool :=
  -- both passes are cached traversals (`find?`, `replace`): environment terms are DAGs
  (e.find? fun x => x.isAppOfArity mk 1 && !x.appArg!.hasLooseBVars).isSome ||
    ((e.replace fun x => if x.isAppOfArity mk 1 then some (mkConst ``Unit) else none).find?
      (·.isConstOf mk)).isSome

def ours (n : Name) : Bool :=
  (`Minidregg).isPrefixOf n && !n.isInternalDetail

def run : MetaM Unit := do
  let env ← getEnv
  let ty := mkConst ``Minidregg.Compiler.CredentialSignatureIO.Transcript
  let mk := ``Minidregg.Compiler.CredentialSignatureIO.Transcript.mk
  let mut named : Array Name := #[]
  let mut escaped : Array Name := #[]
  for (n, info) in env.constants.toList do
    unless ours n do continue
    let some value := info.value? | continue
    let isTranscript ← try isDefEq info.type ty catch _ => pure false
    if isTranscript && info.levelParams.isEmpty then
      named := named.push n
    else if builds mk value then
      escaped := escaped.push n
  let mut triples := 0
  for n in named.qsort (·.toString < ·.toString) do
    let t ← unsafe evalExpr Minidregg.Compiler.CredentialSignatureIO.Transcript ty (mkConst n)
    let mut i := 0
    for (k, f, s) in t.verified do
      IO.println s!"TRIPLE\t{n}\t{i}\t{hex k}\t{hex f}\t{hex s}"
      i := i + 1
      triples := triples + 1
  IO.println s!"TRANSCRIPTS\t{named.size}\ttriples\t{triples}"
  unless escaped.isEmpty do
    throwError s!"native-transcripts: Transcript.mk inside a non-Transcript constant (re-verification would miss it): {escaped.toList}"

end Minidregg.NativeTranscripts

set_option maxHeartbeats 0 in
run_meta Minidregg.NativeTranscripts.run
