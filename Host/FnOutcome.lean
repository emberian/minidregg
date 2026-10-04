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

The local consumer verbs print one text line, `consumer STATUS[ DETAIL]`
(fn `host/native/consumer-local.lisp` `fnn-consumer-say`); `answerLine`
splits it so a refusal keeps its reason word. This reads fn's CLI text, which
is a host format string; it goes when Mini decodes fn's FNCT reply frames from
fn's exported grammar (`MINI-FN-660-REQUIREMENTS` M5).
-/
import Theory.AxiomPin

namespace Minidregg.Host.FnOutcome

set_option autoImplicit false

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

/-- One answer line, `consumer STATUS[ DETAIL]` plus its newline, as bytes. -/
structure Answer where
  status : List UInt8
  detail : List UInt8
  deriving DecidableEq, Repr

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

/-- `consumer` -/
def consumerWord : List UInt8 := [99, 111, 110, 115, 117, 109, 101, 114]

/-- Split fn's answer line. Refuses anything that is not one printable-ASCII
line beginning `consumer ` and ending in one newline. -/
def answerLine (stdout : List UInt8) : Option Answer :=
  match stdout.reverse with
  | last :: lineRev =>
      let line := lineRev.reverse
      if last = 10 ∧ line.all (fun b => 32 ≤ b.toNat && b.toNat ≤ 126) then
        match splitOnSpace line with
        | word :: status :: detail =>
            if word = consumerWord ∧ status ≠ [] then
              some ⟨status, [32].intercalate detail⟩
            else none
        | _ => none
      else none
  | [] => none

def Answer.text (answer : Answer) : String :=
  let bytes := if answer.detail.isEmpty then answer.status
    else answer.status ++ 32 :: answer.detail
  (String.fromUTF8? bytes.toByteArray).getD "non-UTF-8 answer"

/-- A diagnostic naming the class and fn's own reason word. -/
def describe (verb : String) (code : Nat) (stdout : List UInt8) : String :=
  let reason := match answerLine stdout with
    | some answer => answer.text
    | none => "no answer line"
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
`fnn-command-hybrid-author`, the status word upper-cased). CLI text, as
`answerLine` is; it goes when M5 exports the status words. -/
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

def ackStatus (code : Nat) (stdout : List UInt8) : AckStatus :=
  match classify code with
  | some .accepted =>
      if stdout == "consumer accepted\n".toUTF8.toList then .durableAccepted
      else .transportFault
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

/-- An accepted ack is exactly exit 0 with the exact accepted line. -/
theorem ackStatus_durableAccepted_iff {code : Nat} {stdout : List UInt8} :
    ackStatus code stdout = .durableAccepted ↔
      code = 0 ∧ stdout = "consumer accepted\n".toUTF8.toList := by
  unfold ackStatus
  cases h : classify code with
  | none =>
      simp only [reduceCtorEq, false_iff, not_and]
      intro z
      subst z
      simp [classify] at h
  | some c =>
      have e := classify_eq_some h
      cases c <;> simp [Class.code] at e ⊢
      all_goals first | (intro _; rfl) | omega

/-! Inhabitants: fn's three ack answers, and its refusal line split. -/

theorem ackStatus_samples :
    ackStatus 0 "consumer accepted\n".toUTF8.toList = .durableAccepted ∧
    ackStatus 1 "consumer refused busy\n".toUTF8.toList = .refused ∧
    ackStatus 3 "consumer uncertain\n".toUTF8.toList = .uncertain ∧
    ackStatus 2 [] = .transportFault ∧ ackStatus 4 [] = .transportFault := by decide +kernel

theorem answerLine_refused_busy :
    answerLine "consumer refused busy\n".toUTF8.toList =
      some ⟨"refused".toUTF8.toList, "busy".toUTF8.toList⟩ := by decide +kernel

theorem answerLine_refuses_other_verbs :
    answerLine "operator refused busy\n".toUTF8.toList = none ∧
    answerLine "consumer refused busy".toUTF8.toList = none := by decide +kernel

#assert_axioms classify_code classify_two mayHaveActed_false_iff
  ackStatus_refused_iff ackStatus_uncertain_iff classify_eq_some ackStatus_durableAccepted_iff
  ackStatus_samples answerLine_refused_busy
  answerLine_refuses_other_verbs authorAnswer_samples

end Minidregg.Host.FnOutcome
