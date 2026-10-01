/-
# Kernel.TailBound — a node runs at most `L` heights past its last certified head

COMPUTE.md §5.2/§6: Mina's one idea worth keeping is the scan state's
backpressure — no new transactions unless the older work is done.  Here the
older work is the node's own checkpoint chain, and the obligation is the
sequencer's, not a purchase:

    a record at height `head` is admitted only if  head − certified ≤ L

where `certified` is the system cell's certified height (`Kernel.SystemCell`)
and `L` its tail bound.  The rule is the system law
`leSlotsOff head/height certified/height L` (`SystemCell.law`), evaluated by
`Pred.eval`, the same evaluator every policy uses.

**Where the check lives: the kernel's durable admission, one rule for every
record.**  `gate` is called by the durable receiving loop
(`DurableReceiverIO.receiveLoadedDetailedWithFresh`) on every new commit, and
by the replay walk (`NativeHostReplay.advance`) on every re-admitted record, so
the live path, a reopen and `audit` judge the same rule.  It is not a clause of
any user law (a user cannot drop it) and it is not per-receiver (no receiver can
forget it).  K-CLOCK's clock pin is per-invocation because only resource laws
read time; the tail bound is about the log itself, so it sits at the one place
every record passes.

**The one exemption is a certify record**, recognised by its footprint: an
intent that writes the system cell.  Such an intent is admitted only if it
writes exactly one post value, and that value is `certifyNext` of the current
value at the current head and log chain, strictly advancing — so a certify can
always follow a full tail (liveness), and nothing else can move `certified`.

`head` is the height the record will take (`accepted.length + 1`); a certify at
`head` certifies `head − 1`, the head before it, whose chain value the loop
holds.
-/
import Compiler.CanonicalCellRegistry
import Kernel.DurableDataIntent

namespace Minidregg.Kernel.TailBound

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalCellRegistry (registry)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.SystemCell (System certifyNext admitsHead admitsHead_iff)
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## The decision on decoded values -/

/-- Judge one record at height `head` over the current system value `pre` and
the log chain `chain` (the value after `head − 1` records).  `posts` is the
decoded post value of every write the record makes on the system cell. -/
def judge (pre : System) (head : Nat) (chain : Digest) :
    List (Option System) → Except RejectReason Unit
  | [] =>
      if admitsHead pre head then .ok ()
      else .error (.tailBound head pre.certifiedHeight pre.tailBound)
  | [some post] =>
      if post = certifyNext pre (head - 1) chain ∧ pre.certifiedHeight < head - 1 then .ok ()
      else .error .systemWriteRefused
  | _ => .error .systemWriteRefused

theorem judge_none_ok {pre : System} {head : Nat} {chain : Digest}
    (ok : judge pre head chain [] = .ok ()) : head ≤ pre.certifiedHeight + pre.tailBound := by
  simp only [judge] at ok
  by_cases admits : admitsHead pre head = true
  · exact (admitsHead_iff pre head).mp admits
  · rw [if_neg admits] at ok
    cases ok

theorem judge_write_ok {pre : System} {head : Nat} {chain : Digest} {posts : List (Option System)}
    (nonempty : posts ≠ []) (ok : judge pre head chain posts = .ok ()) :
    posts = [some (certifyNext pre (head - 1) chain)] ∧ pre.certifiedHeight < head - 1 := by
  match posts, ok with
  | [], _ => exact absurd rfl nonempty
  | [some post], ok =>
      simp only [judge] at ok
      by_cases both : post = certifyNext pre (head - 1) chain ∧ pre.certifiedHeight < head - 1
      · exact ⟨by rw [both.1], both.2⟩
      · rw [if_neg both] at ok
        cases ok
  | [none], ok => simp [judge] at ok
  | _ :: _ :: _, ok => simp [judge] at ok

/-! ## The gate on the wire -/

/-- Decode a live system cell; any other role, a retired or fresh image, and
non-canonical bytes are refused. -/
def decodeCell (bytes : List UInt8) : Option SystemCell.Cell :=
  match (ResourceBirthCodec.LifecycleImage.codec registry).decode bytes with
  | some (.live ⟨.system, payload⟩) => some payload
  | _ => none

/-- The system value a cell's bytes hold. -/
def valueOf (bytes : List UInt8) : Option System :=
  (decodeCell bytes).bind fun cell => SystemCell.systemOf cell.logical

/-- The decoded post values of the intent's writes on `systemId`. -/
def systemPosts {rootBytes : List UInt8 → Digest} (systemId : CellId)
    (intent : DataIntent rootBytes) : List (Option System) :=
  (intent.writes.filter fun write => write.cellId = systemId).map
    fun write => valueOf write.canonicalPostBytes

/-- **The kernel's tail rule.**  `head` is the height the record takes; `chain`
the log chain before it; `snapshot` the state it is judged on. -/
def gate {rootBytes : List UInt8 → Digest} (systemId : CellId) (head : Nat) (chain : Digest)
    (snapshot : DataSnapshot rootBytes) (intent : DataIntent rootBytes) :
    Except RejectReason Unit :=
  match valueOf (snapshot.canonicalBytes systemId) with
  | none => .error .systemUnavailable
  | some pre => judge pre head chain (systemPosts systemId intent)

theorem systemPosts_nil_iff {rootBytes : List UInt8 → Digest} (systemId : CellId)
    (intent : DataIntent rootBytes) :
    systemPosts systemId intent = [] ↔ ∀ write ∈ intent.writes, write.cellId ≠ systemId := by
  simp [systemPosts, List.filter_eq_nil_iff]

variable {rootBytes : List UInt8 → Digest} {systemId : CellId} {head : Nat} {chain : Digest}
  {snapshot : DataSnapshot rootBytes} {intent : DataIntent rootBytes}

/-- **`tail_bounded`.**  Every admitted record that is not a certify record —
it writes no system cell — sits at most `L` heights past the certified height
of the state it was judged on. -/
theorem tail_bounded (ok : gate systemId head chain snapshot intent = .ok ())
    (notCertify : ∀ write ∈ intent.writes, write.cellId ≠ systemId) :
    ∃ pre, valueOf (snapshot.canonicalBytes systemId) = some pre ∧
      head - pre.certifiedHeight ≤ pre.tailBound := by
  unfold gate at ok
  split at ok
  · cases ok
  · rename_i pre found
    rw [(systemPosts_nil_iff systemId intent).mpr notCertify] at ok
    have := judge_none_ok ok
    exact ⟨pre, found, by omega⟩

/-- **`certified_written_only_by_checkpoint`.**  If an admitted record writes
the system cell at all, it writes it exactly once, and the value it writes is
the certification of the current head (`head − 1`) at the current log chain,
with the tail bound unchanged.  No other shape of write to the system cell is
admitted, whatever receiver produced it. -/
theorem certified_written_only_by_checkpoint (ok : gate systemId head chain snapshot intent = .ok ())
    (write : DataWrite) (member : write ∈ intent.writes) (target : write.cellId = systemId) :
    ∃ pre, valueOf (snapshot.canonicalBytes systemId) = some pre ∧
      systemPosts systemId intent = [some (certifyNext pre (head - 1) chain)] ∧
      pre.certifiedHeight < head - 1 := by
  unfold gate at ok
  split at ok
  · cases ok
  · rename_i pre found
    have nonempty : systemPosts systemId intent ≠ [] := by
      intro empty
      exact (systemPosts_nil_iff systemId intent).mp empty write member target
    exact ⟨pre, found, judge_write_ok nonempty ok⟩

/-- **`certified_monotone`.**  A write to the system cell that the gate admits
installs a strictly greater certified height and the same tail bound. -/
theorem certified_monotone (ok : gate systemId head chain snapshot intent = .ok ())
    (write : DataWrite) (member : write ∈ intent.writes) (target : write.cellId = systemId)
    (post : System) (decoded : valueOf write.canonicalPostBytes = some post) :
    ∃ pre, valueOf (snapshot.canonicalBytes systemId) = some pre ∧
      pre.certifiedHeight < post.certifiedHeight ∧ post.tailBound = pre.tailBound := by
  obtain ⟨pre, found, posts, advancing⟩ :=
    certified_written_only_by_checkpoint ok write member target
  have inPosts : some post ∈ systemPosts systemId intent := by
    simp only [systemPosts, List.mem_map, List.mem_filter]
    exact ⟨write, ⟨member, by simp [target]⟩, decoded⟩
  rw [posts, List.mem_singleton] at inPosts
  cases Option.some.inj inPosts
  exact ⟨pre, found, advancing, rfl⟩

/-- A system cell that is missing or undecodable refuses every record. -/
theorem unavailable_refuses (missing : valueOf (snapshot.canonicalBytes systemId) = none) :
    gate systemId head chain snapshot intent = .error .systemUnavailable := by
  unfold gate
  rw [missing]

/-! ## The poles, on the decision -/

/-- **Refuting pole** (general): the first height past the bound is refused by
name. -/
theorem beyond_bound_refused (pre : System) (chain : Digest) :
    judge pre (pre.certifiedHeight + pre.tailBound + 1) chain [] =
      .error (.tailBound (pre.certifiedHeight + pre.tailBound + 1) pre.certifiedHeight pre.tailBound) := by
  have : admitsHead pre (pre.certifiedHeight + pre.tailBound + 1) = false := by
    cases h : admitsHead pre (pre.certifiedHeight + pre.tailBound + 1)
    · rfl
    · have := (admitsHead_iff _ _).mp h
      omega
  simp [judge, this]

/-- **Satisfiable pole** (general): the last height inside the bound is admitted. -/
theorem at_bound_admitted (pre : System) (chain : Digest) :
    judge pre (pre.certifiedHeight + pre.tailBound) chain [] = .ok () := by
  have : admitsHead pre (pre.certifiedHeight + pre.tailBound) = true :=
    (admitsHead_iff _ _).mpr (Nat.le_refl _)
  simp [judge, this]

/-- **Refuting pole** (concrete, by `decide`): certified at 64 with `L = 8`, a
record at height 73 is refused `tailBound 73 64 8`. -/
theorem tailBound_refuses_73 :
    judge ⟨64, ⟨7⟩, 8⟩ 73 ⟨9⟩ [] = .error (.tailBound 73 64 8) := by decide

/-- **Satisfiable pole** (concrete, by `decide`): the record at height 72 is
admitted. -/
theorem tailBound_admits_72 : judge ⟨64, ⟨7⟩, 8⟩ 72 ⟨9⟩ [] = .ok () := by decide

/-- A certify record is admitted at a full tail (concrete): at height 73 it
certifies 72 at chain 9. -/
theorem certify_admitted_at_full_tail :
    judge ⟨64, ⟨7⟩, 8⟩ 73 ⟨9⟩ [some ⟨72, ⟨9⟩, 8⟩] = .ok () := by decide

/-- A certify that changes the tail bound is refused (concrete). -/
theorem certify_cannot_move_bound :
    judge ⟨64, ⟨7⟩, 8⟩ 73 ⟨9⟩ [some ⟨72, ⟨9⟩, 1000⟩] = .error .systemWriteRefused := by decide

/-- A certify that names another chain value is refused (concrete). -/
theorem certify_wrong_chain_refused :
    judge ⟨64, ⟨7⟩, 8⟩ 73 ⟨9⟩ [some ⟨72, ⟨8⟩, 8⟩] = .error .systemWriteRefused := by decide

/-- **`checkpoint_restores_progress`.**  A certify record at height `n + 1`
(certifying `n`) is admitted whenever it advances, and after it every record at
the next `L` heights — `n + 1 … n + L` — passes the tail law. -/
theorem checkpoint_restores_progress (pre : System) (n : Nat) (chain : Digest)
    (advancing : pre.certifiedHeight < n) :
    judge pre (n + 1) chain [some (certifyNext pre n chain)] = .ok () ∧
      ∀ head, head ≤ n + pre.tailBound → ∀ later : Digest,
        judge (certifyNext pre n chain) head later [] = .ok () := by
  refine ⟨?_, ?_⟩
  · simp [judge, advancing]
  · intro head within later
    have : admitsHead (certifyNext pre n chain) head = true :=
      (admitsHead_iff _ _).mpr (by simpa [certifyNext] using within)
    simp [judge, this]

/-- info: 'Minidregg.Kernel.TailBound.tail_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tail_bounded
/-- info: 'Minidregg.Kernel.TailBound.certified_written_only_by_checkpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certified_written_only_by_checkpoint
/-- info: 'Minidregg.Kernel.TailBound.certified_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certified_monotone
/-- info: 'Minidregg.Kernel.TailBound.unavailable_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unavailable_refuses
/-- info: 'Minidregg.Kernel.TailBound.beyond_bound_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms beyond_bound_refused
/-- info: 'Minidregg.Kernel.TailBound.at_bound_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms at_bound_admitted
/-- info: 'Minidregg.Kernel.TailBound.tailBound_refuses_73' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms tailBound_refuses_73
/-- info: 'Minidregg.Kernel.TailBound.tailBound_admits_72' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms tailBound_admits_72
/-- info: 'Minidregg.Kernel.TailBound.certify_admitted_at_full_tail' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms certify_admitted_at_full_tail
/-- info: 'Minidregg.Kernel.TailBound.certify_cannot_move_bound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms certify_cannot_move_bound
/-- info: 'Minidregg.Kernel.TailBound.certify_wrong_chain_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms certify_wrong_chain_refused
/-- info: 'Minidregg.Kernel.TailBound.checkpoint_restores_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkpoint_restores_progress

end Minidregg.Kernel.TailBound
