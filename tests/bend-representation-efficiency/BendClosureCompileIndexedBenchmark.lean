import Compiler.BendClosureCompileIndexed

open Minidregg.Theory BendTT BendClosureArena BendClosureMachine
open Minidregg.Compiler

/-- Exercise every source constructor and every quantity. Exact decoding also
retains arbitrary Q0 syntax and the live rewrite evidence/motive distinction. -/
def constructors : List Term :=
  [.Var 99, .Ref "missing", .Ann (.Lab "x") (.Enu ["x"]),
   .Let .Q0 (.Var 77) (.Var 0), .Let .Q1 (.Lab "x") (.Var 0),
   .Let .Q2 (.Lab "x") (.Var 0), .Typ .Q0, .Typ .Q1, .Typ .Q2,
   .All .Q2 (.Typ .Q1) (.Var 0), .Lam .Q1 (.Var 0),
   .App .Q0 (.Ref "call") (.Var 400), .Sig .Q1 (.Enu ["x"]) (.Var 0),
   .Tup .Q0 (.Var 500) (.Lab "x"), .Tup .Q1 (.Lab "x") (.Lab "x"),
   .Tup .Q2 (.Lab "x") (.Lab "x"), .Prj (.Lam .Q1 (.Var 0)),
   .Enu ["x", "y", "x"], .Lab "x", .Mat "x" (.Lab "x") (.Lab "y"),
   .Efq, .Eql (.Var 1) (.Var 2) (.Typ .Q1), .Rfl,
   .Rwt .Rfl (.Var 700) (.Lab "x")]

def validate (book : Book) (source : Term) : IO (Library × Nat) := do
  let (library, entry) := BendClosureCompileIndexed.build book source
  let ticks := library.program.code.size + 1
  if (BendClosureCompile.validateCode library.program ticks entry source).isNone then
    throw (IO.userError "optimized entry did not decode to the exact original source")
  if (BendClosureCompile.validateDefinitions library.program ticks library.definitions.toList book).isNone then
    throw (IO.userError "optimized definitions did not decode to the exact ordered Book")
  pure (library, entry)

def repeated (depth : Nat) : Term :=
  (List.range depth).foldl (fun term _ => .Tup .Q1 term term) (.Lab "x")

def bench (depth : Nat) : IO Unit := do
  let source := repeated depth
  let begin ← IO.monoMsNow
  let (original, _) := BendClosureCompile.build [] source
  IO.println s!"CODE-INTERN original_rows={original.program.code.size}"
  let middle ← IO.monoMsNow
  let (optimized, _) ← validate [] source
  IO.println s!"CODE-INTERN indexed_rows={optimized.program.code.size}"
  let finish ← IO.monoMsNow
  if optimized.program.code.size != depth + 1 then
    throw (IO.userError "identical immutable subtrees were not shared")
  IO.println s!"CODE-INTERN depth={depth} original_ms={middle-begin} indexed_validated_ms={finish-middle}"

def captured (path : String) : IO Unit := do
  let text ← IO.FS.readFile path
  let .ok book := Book.parse text | throw (IO.userError s!"actual Book parser refused {path}")
  let some definition := book.head? | throw (IO.userError "empty captured Book")
  let source := Term.Ref definition.k
  let (original, _) := BendClosureCompile.build book source
  let (optimized, _) ← validate book source
  let some _ := BendClosureCompileIndexed.compile book source
    | throw (IO.userError s!"actual captured Book.check/optimized compile refused {path}")
  IO.println s!"CAPTURED-CODE {path}: definitions={book.length} original_rows={original.program.code.size} indexed_rows={optimized.program.code.size} names={optimized.program.names.size}"

def main (args : List String) : IO Unit := do
  if !args.isEmpty then
    for path in args do captured path
    IO.println "BEND INDEXED CAPTURED COMPILATION PASS"
    return
  for source in constructors do
    let _ ← validate [] source
  let duplicatedNames : Book :=
    [{ k := "same", T := .Enu ["first"], v := .Lab "first", o := false },
     { k := "same", T := .Enu ["second"], v := .Lab "second", o := false }]
  let (library, _) ← validate duplicatedNames (.Ref "same")
  let some body := library.lookupName "same" | throw (IO.userError "first name missing")
  let some decoded := decodeCode library.program (library.program.code.size + 1) body
    | throw (IO.userError "first definition failed decode")
  if decoded.term != .Lab "first" then throw (IO.userError "first-definition wins changed")
  let book : Book := [{ k := "one", T := .Enu ["x"], v := .Lab "x", o := false }]
  let some compiled := BendClosureCompileIndexed.compile book (.Ref "one")
    | throw (IO.userError "actual checked optimized compilation refused")
  if compiled.library.lookupName "one" != some 0 then
    throw (IO.userError "actual compiled source missing")
  for depth in [8, 12, 16] do bench depth
  for path in args do captured path
  IO.println "BEND INDEXED CODE COMPILATION PASS"
