/-
# Host.FnOutcome — what an fn command's exit and answer line mean to Mini

fn ends every native command with one of seven outcome classes and one exit
code per class (fn `books/outcome-class.lisp` `*fn-outcome-codes*`, PRF-143):

| code | class | may fn have acted? |
| --- | --- | --- |
| 0 | accepted | yes, and it did |
| 1 | refused (reason word on the answer line; includes transient `busy`, `clock-unusable`, and a socket that took no request) | no |
| 3 | fenced: the outcome is unknown; settle with `consumer position` or a lookup | maybe |
| 4 | fault: the host could not finish; OS errors inside the publication window are `fenced`, every other fault is here, so a fault CAN follow a durable commit (fn `fn-fs-classify`) | maybe |
| 5 | usage: the invocation was malformed before any socket or Store | no |
| 6 | interrupted: a connection lost after it existed | maybe |
| 7 | not-connected: nothing left the node | no |

There is no exit 2. Before this module eight Mini ack sites read exit 2 as
"refused", so every real fn refusal (exit 1) was reported as a transport
fault and the covered-by-frontier recovery behind "refused" never ran; and
the consumer poll paths collapsed every nonzero exit into one
"refused or was uncertain" error. `classify` keeps the seven apart, and an
unknown code fails closed toward "may have acted", as fn's own
`fn-outcome-code` fails closed toward the fence.

Every consumer verb Mini runs (`status`, `position`, `ack`, `poll`) and `identity` is run with
`--frame` (fn `3f0309256`; poll since fn `6679dae0e`) and prints the reply frame as hex, which
`Compiler.FnWireConsumer` reads with the grammar interpreter at fn's exported families: an
acknowledgement is durable-accepted exactly when the exit is 0 AND the frame is an `accepted`
consumer reply (`ackStatus_durableAccepted_iff`), not when a text line spells it. Mini reads no
fn answer text line; the former `consumer STATUS[ DETAIL]` splitter (`answerLine`) is deleted.
-/
import Theory.AxiomPin
import Theory.AssertCompiled
import Compiler.FnWireConsumer

namespace Minidregg.Host.FnOutcome

set_option autoImplicit false

open Minidregg.Compiler

/-- fn's seven outcome classes. -/
inductive Class where
  | accepted | refused | fenced | fault | usage | interrupted | notConnected
  deriving DecidableEq, Repr

def Class.code : Class → Nat
  | .accepted => 0 | .refused => 1 | .fenced => 3 | .fault => 4
  | .usage => 5 | .interrupted => 6 | .notConnected => 7

/-- The class of an exit code; `none` for a code fn never emits. -/
def classify (code : Nat) : Option Class :=
  match code with
  | 0 => some .accepted | 1 => some .refused | 3 => some .fenced | 4 => some .fault
  | 5 => some .usage | 6 => some .interrupted | 7 => some .notConnected
  | _ => none

/-- Whether fn may have changed its Store. A refusal, a usage error and a
connection that never existed are the only answers that say "no". -/
def Class.mayHaveActed : Class → Bool
  | .refused | .usage | .notConnected => false
  | .accepted | .fenced | .fault | .interrupted => true

/-- An exit code fn never emits is read as "may have acted". -/
def mayHaveActed (code : Nat) : Bool :=
  match classify code with
  | some c => c.mayHaveActed
  | none => true

def Class.word : Class → String
  | .accepted => "accepted" | .refused => "refused" | .fenced => "uncertain"
  | .fault => "fault" | .usage => "usage" | .interrupted => "interrupted"
  | .notConnected => "not-connected"

theorem classify_code : ∀ c : Class, classify c.code = some c := by
  intro c; cases c <;> rfl

/-- Exit 2 belongs to no class; nothing may read it as a refusal. -/
theorem classify_two : classify 2 = none := rfl

theorem mayHaveActed_false_iff {code : Nat} :
    mayHaveActed code = false ↔
      classify code = some .refused ∨ classify code = some .usage ∨
        classify code = some .notConnected := by
  unfold mayHaveActed
  cases h : classify code with
  | none => simp
  | some c => cases c <;> simp [Class.mayHaveActed]

/-- Split on newlines, keeping empty lines. -/
def splitOnLf : List UInt8 → List (List UInt8)
  | [] => [[]]
  | b :: rest =>
      if b = 10 then [] :: splitOnLf rest
      else match splitOnLf rest with
        | w :: ws => (b :: w) :: ws
        | [] => [[b]]

/-- Split on single spaces, keeping empty words (as `String.splitOn " "`). -/
def splitOnSpace : List UInt8 → List (List UInt8)
  | [] => [[]]
  | b :: rest =>
      if b = 32 then [] :: splitOnSpace rest
      else match splitOnSpace rest with
        | w :: ws => (b :: w) :: ws
        | [] => [[b]]

/-- The reason of a `--frame` answer: the outcome word of its consumer or status reply, with
the reason word of a reasoned reply. -/
def frameReason (stdout : List UInt8) : String :=
  let reasoned := fun (status : String) (reason : List UInt8) =>
    status ++ " " ++ ((String.fromUTF8? reason.toByteArray).getD "non-UTF-8 reason")
  match FnWire.readConsumerReply stdout with
  | .ok (.accepted _) => "accepted"
  | .ok .refused => "refused"
  | .ok .uncertain => "uncertain"
  | .ok .fault => "fault"
  | .ok (.reasoned s r) => reasoned s r
  | .error _ =>
    match FnWire.readStatusReply stdout with
    | .ok (.accepted ..) => "accepted"
    | .ok .refused => "refused"
    | .ok .uncertain => "uncertain"
    | .ok .fault => "fault"
    | .ok (.reasoned s r) => reasoned s r
    | .error _ =>
      -- A poll that is not accepted prints an eight-zero-octet arm; a bound of 64 octets
      -- reads exactly those, and an accepted poll is never described as a refusal.
      match FnWire.readPollReply 64 stdout with
      | .ok (.accepted ..) => "accepted"
      | .ok .refused => "refused"
      | .ok .uncertain => "uncertain"
      | .ok .fault => "fault"
      | .error _ => "no readable frame"

/-- A diagnostic naming the class and fn's own reason word (`reason`: `frameReason` for the
`--frame` verbs). -/
def describe (verb : String) (code : Nat) (reason : String) : String :=
  match classify code with
  | some .refused => s!"fn {verb} refused ({reason}); fn did not act"
  | some .notConnected => s!"fn {verb} reached no fn owner; nothing was sent"
  | some .usage => s!"fn {verb} refused Mini's invocation as malformed (exit 5); a Mini defect"
  | some .fenced => s!"fn {verb} is uncertain ({reason}); fn may have acted, settle by lookup"
  | some .fault => s!"fn {verb} faulted (exit 4); fn may have acted, settle by lookup"
  | some .interrupted => s!"fn {verb} lost its connection (exit 6); fn may have acted"
  | some .accepted => s!"fn {verb} accepted but its answer was not the expected line ({reason})"
  | none => s!"fn {verb} exited {code}, which is no fn outcome class; treated as may-have-acted"

/-- `hybrid-author`'s answer: the last non-empty line fn writes to stderr,
`CLASS hybrid-author WORD` (fn `host/native/hybrid-control.lisp`
`fnn-command-hybrid-author`, the status word upper-cased). CLI text; it goes when M5 exports
the status words. -/
def authorAnswer (stderr : List UInt8) : Option (List UInt8 × List UInt8) :=
  let lines := (splitOnLf stderr).filter (· ≠ [])
  match lines.getLast? with
  | some line =>
      match splitOnSpace line with
      | [cls, verb, word] =>
          if verb = "hybrid-author".toUTF8.toList ∧ cls ≠ [] ∧ word ≠ [] then some (cls, word)
          else none
      | _ => none
  | none => none

theorem authorAnswer_samples :
    authorAnswer "accepted hybrid-author DUPLICATE\n".toUTF8.toList =
      some ("accepted".toUTF8.toList, "DUPLICATE".toUTF8.toList) ∧
    authorAnswer "note\nrefused hybrid-author CONFLICT\n".toUTF8.toList =
      some ("refused".toUTF8.toList, "CONFLICT".toUTF8.toList) ∧
    authorAnswer "refused hybrid-enroll CONFLICT\n".toUTF8.toList = none := by decide +kernel

/-- What an ack site records. `refused` is fn's exit 1 (or 7: no request
left the node) and nothing else; `uncertain` is the fence; every other answer
is a transport fault, which the caller settles with `consumer position`. -/
inductive AckStatus where
  | durableAccepted | refused | uncertain | transportFault
  deriving DecidableEq, Repr

def AckStatus.word : AckStatus → String
  | .durableAccepted => "durable-accepted" | .refused => "refused"
  | .uncertain => "uncertain" | .transportFault => "transport-fault"

/-- `stdout` is what `consumer --frame ack` printed: durable only when the exit is 0 and the
printed frame is an accepted consumer reply. -/
def ackStatus (code : Nat) (stdout : List UInt8) : AckStatus :=
  match classify code with
  | some .accepted =>
      match FnWire.readConsumerReply stdout with
      | .ok (.accepted _) => .durableAccepted
      | _ => .transportFault
  | some .refused | some .notConnected => .refused
  | some .fenced => .uncertain
  | _ => .transportFault

theorem ackStatus_refused_iff {code : Nat} {stdout : List UInt8} :
    ackStatus code stdout = .refused ↔
      classify code = some .refused ∨ classify code = some .notConnected := by
  unfold ackStatus
  cases h : classify code with
  | none => simp
  | some c => cases c <;> simp <;> split <;> simp

theorem ackStatus_uncertain_iff {code : Nat} {stdout : List UInt8} :
    ackStatus code stdout = .uncertain ↔ classify code = some .fenced := by
  unfold ackStatus
  cases h : classify code with
  | none => simp
  | some c => cases c <;> simp <;> split <;> simp

theorem classify_eq_some {code : Nat} {c : Class} (h : classify code = some c) :
    code = c.code := by
  unfold classify at h
  split at h <;> cases h <;> rfl

/-- An accepted ack is exactly exit 0 with an accepted consumer reply frame. -/
theorem ackStatus_durableAccepted_iff {code : Nat} {stdout : List UInt8} :
    ackStatus code stdout = .durableAccepted ↔
      code = 0 ∧ ∃ c, FnWire.readConsumerReply stdout = .ok (.accepted c) := by
  constructor
  · intro h
    unfold ackStatus at h
    cases hc : classify code with
    | none => rw [hc] at h; simp at h
    | some c =>
      have e := classify_eq_some hc
      rw [hc] at h
      cases c <;> simp only [reduceCtorEq] at h
      · refine ⟨e, ?_⟩
        cases hr : FnWire.readConsumerReply stdout with
        | error _ => rw [hr] at h; simp at h
        | ok r =>
          rw [hr] at h
          cases r with
          | accepted c => exact ⟨c, rfl⟩
          | _ => simp at h
  · rintro ⟨rfl, c, hc⟩
    simp [ackStatus, classify, hc]

/-! Inhabitants: fn's three ack answers, and its refusal line split. -/

/-- fn-rendered `fnct.consumer.reply` accept vector 1 of the pinned file (`accepted`, no cursor),
and its `refused` and `uncertain` siblings (vectors 2 and 3). -/
def lineOf (hex : String) : List UInt8 := (hex ++ "\n").toUTF8.toList

def acceptedFrame : String :=
  "464e435401050000000100b961207007462e3a5ac2cfa2ff965536f0bf7628dbf1426a7dbfca7bf60f26ca"
def refusedFrame : String :=
  "464e435401050000000101b12723a10100f1500fdb79c6dcda3d69fbc33cf8b08f59f149d74e6645021609"

theorem ackStatus_samples :
    ackStatus 0 (lineOf acceptedFrame) = .durableAccepted ∧
    ackStatus 1 (lineOf refusedFrame) = .refused ∧
    ackStatus 3 [] = .uncertain ∧
    ackStatus 2 [] = .transportFault ∧ ackStatus 4 [] = .transportFault := by native_decide

/-- Teeth: exit 0 with a refused frame, with a bare line, with the old text, and with no output
is no durable acknowledgement. -/
theorem ackStatus_refuses_unframed_acceptance :
    ackStatus 0 (lineOf refusedFrame) = .transportFault ∧
    ackStatus 0 "consumer accepted\n".toUTF8.toList = .transportFault ∧
    ackStatus 0 (acceptedFrame.toUTF8.toList) = .transportFault ∧
    ackStatus 0 [] = .transportFault := by native_decide

#assert_axioms classify_code classify_two mayHaveActed_false_iff
  ackStatus_refused_iff ackStatus_uncertain_iff classify_eq_some ackStatus_durableAccepted_iff
  authorAnswer_samples
#assert_compiled ackStatus_samples
#assert_compiled ackStatus_refuses_unframed_acceptance

end Minidregg.Host.FnOutcome
