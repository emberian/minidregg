/- Authored Objective Bend surfaces select admitted observations and prepared
native intents. This module does not authenticate observations, run a program,
or grant authority. Those are obligations of the existing native receiver.

A flat, backwards-addressed tree keeps the wire format finite and renderer
independent. Text is author prose; observed values and mounts are references to
explicit admitted slots. An action has no author-controlled enabled Boolean.
-/
import Compiler.NockProgramCodec

namespace Minidregg.Compiler.BendWorldSurface
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

structure Intent where
  artifact : Digest
  exportName : String
  program : Digest
  instance : Nat
  expectedRoot : Digest
  arguments : List UInt8
  deriving DecidableEq, Repr

structure Node where
  /-- 0 prose, 1 observed value, 2 document/object mount, 3 action, 4 group. -/
  tag : Nat
  slot : Nat
  label : String
  /-- Child indices must precede this node. Shared children are permitted. -/
  children : List Nat
  deriving DecidableEq, Repr

structure Surface where
  artifact : Digest
  exportName : String
  nodes : List Node
  root : Nat
  intents : List Intent
  deriving DecidableEq, Repr

def intentStream : StreamCodec Intent :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream bytesStream)))))
    (fun i => (i.artifact, i.exportName, i.program, i.instance, i.expectedRoot, i.arguments))
    (fun i => ⟨i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2.1, i.2.2.2.2.2⟩)
    (by intro i; cases i; rfl)

def nodeStream : StreamCodec Node :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat
    (StreamCodec.product PolicyRecordCodec.stringStream (StreamCodec.list StreamCodec.nat))))
    (fun n => (n.tag, n.slot, n.label, n.children))
    (fun n => ⟨n.1, n.2.1, n.2.2.1, n.2.2.2⟩)
    (by intro n; cases n; rfl)

def surfaceStream : StreamCodec Surface :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product (StreamCodec.list nodeStream)
    (StreamCodec.product StreamCodec.nat (StreamCodec.list intentStream)))))
    (fun s => (s.artifact, s.exportName, s.nodes, s.root, s.intents))
    (fun s => ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2⟩)
    (by intro s; cases s; rfl)

def frame : List UInt8 := "DREGG/BEND/SURFACE/v1".toUTF8.toList
def encode (s : Surface) : List UInt8 := frame ++ surfaceStream.encode s
def decode (bytes : List UInt8) : Option Surface :=
  NockProgramCodec.framedDecode frame surfaceStream bytes

theorem roundtrip (s : Surface) : decode (encode s) = some s :=
  NockProgramCodec.framedDecode_encode frame surfaceStream s

theorem canonical {bytes : List UInt8} {s : Surface}
    (h : decode bytes = some s) : encode s = bytes :=
  NockProgramCodec.framedDecode_canonical h

/-- An admitted slot is already projected for this viewer. Locked/refused slots
carry only the status the native projection was authorized to disclose. There
is no world lookup or reference enumeration in surface evaluation. -/
structure Observation where
  resource : Nat
  revision : Digest
  /-- 0 opened, 1 locked, 2 refused, 3 unavailable. -/
  state : Nat
  kind : String
  value : List UInt8
  deriving DecidableEq, Repr

/-- Custody handle returned by actual native preparation. A method's source,
program, target, expected root and arguments must all match before display can
offer this handle. Native approval still rereads current law and roots. -/
structure Prepared where
  intent : Intent
  operation : Digest
  deriving DecidableEq, Repr

def originMatches (s : Surface) (artifact : Digest) (exportName : String) : Bool :=
  decide (s.artifact = artifact ∧ s.exportName = exportName)

theorem origin_exact {s : Surface} {artifact : Digest} {exportName : String}
    (h : originMatches s artifact exportName = true) :
    s.artifact = artifact ∧ s.exportName = exportName := by
  exact of_decide_eq_true h

def wellFormed (s : Surface) (observations : List Observation) : Bool :=
  decide (s.root < s.nodes.length) &&
  (List.finRange s.nodes.length).all fun index =>
    let n := s.nodes[index]
    decide (n.tag ≤ 4) && n.children.all (fun child => decide (child < index.val)) &&
    (if n.tag = 1 ∨ n.tag = 2 then decide (n.slot < observations.length)
     else if n.tag = 3 then decide (n.slot < s.intents.length) else true)

def observe (observations : List Observation) (node : Node) : Option Observation :=
  if node.tag = 1 ∨ node.tag = 2 then observations[node.slot]? else none

def action (s : Surface) (prepared : List Prepared) (node : Node) : Option Prepared :=
  if node.tag = 3 then
    match s.intents[node.slot]? with
    | none => none
    | some intent => prepared.find? (fun p => decide (p.intent = intent))
  else none

/-- Every observed output is the same admitted slot, including its exact source
revision and unavailable/locked state. Installation cannot manufacture one. -/
theorem observed_from_admitted {observations : List Observation} {node : Node}
    {value : Observation} (h : observe observations node = some value) :
    observations[node.slot]? = some value := by
  unfold observe at h
  split at h
  · exact h
  · contradiction

/-- Actions originate in the independently prepared native intent list. This
is a display refinement, not an authorization theorem for that preparation. -/
theorem action_from_prepared {s : Surface} {prepared : List Prepared} {node : Node}
    {value : Prepared} (h : action s prepared node = some value) :
    ∃ intent, s.intents[node.slot]? = some intent ∧
      prepared.find? (fun p => decide (p.intent = intent)) = some value := by
  unfold action at h
  split at h
  · split at h
    · contradiction
    · rename_i intent hi
      exact ⟨intent, hi, h⟩
  · contradiction

theorem action_binding_exact {s : Surface} {prepared : List Prepared} {node : Node}
    {value : Prepared} (h : action s prepared node = some value) :
    value ∈ prepared ∧ s.intents[node.slot]? = some value.intent := by
  obtain ⟨intent, hi, hf⟩ := action_from_prepared h
  have hb : value.intent = intent := by simpa using List.find?_some hf
  exact ⟨List.mem_of_find?_eq_some hf, by simpa [hb] using hi⟩

end Minidregg.Compiler.BendWorldSurface
