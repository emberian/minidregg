/-
# Kernel.TailBound — a node runs at most `L` heights past its last certified head

docs/COMPUTE.md §5.2/§6: Mina's one idea worth keeping is the scan state's
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
value at a prefix the log's history holds with that chain value, strictly
advancing (`ChainHistory.certifiable`, the rule the certify receiver also
calls) — so a certify can always follow a full tail (liveness), a write landing
after the certifier's observation does not refuse it, and nothing else can move
`certified`.

The gate reads the log only through a `ChainHistory` (generic: the loaded
image's chain log, or the head alone on a state without history). The record
takes height `head history + 1`, so the tail law and the certify rule talk
about the same head.
-/
module

public import Compiler.CanonicalCellRegistry
public import Kernel.DurableDataIntent
public import Kernel.ChainHistory

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Kernel.TailBound

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalCellRegistry (registry)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.SystemCell (System certifyNext admitsHead admitsHead_iff)
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel (ChainHistory Prefixes)

set_option autoImplicit false

/-! ## The decision on decoded values -/

variable {H : Type} [ChainHistory H]

/-- The height a record judged over `history` takes. -/
def recordHeight (history : H) : Nat := ChainHistory.head history + 1

/-- Judge one record over the current system value `pre` and the log's history (the record
takes `recordHeight history`).  `posts` is the decoded post value of every write the record
makes on the system cell. -/
def judge (pre : System) (history : H) : List (Option System) → Except RejectReason Unit
  | [] =>
      if admitsHead pre (recordHeight history) then .ok ()
      else .error (.tailBound (recordHeight history) pre.certifiedHeight pre.tailBound)
  | [some post] =>
      match ChainHistory.certifiable pre.certifiedHeight history post.certifiedHeight
          post.certifiedDigest with
      | .ok () =>
          if post = certifyNext pre post.certifiedHeight post.certifiedDigest then .ok ()
          else .error .systemWriteRefused
      | .error _ => .error .systemWriteRefused
  | _ => .error .systemWriteRefused

theorem judge_none_ok {pre : System} {history : H} (ok : judge pre history [] = .ok ()) :
    recordHeight history ≤ pre.certifiedHeight + pre.tailBound := by
  simp only [judge] at ok
  by_cases admits : admitsHead pre (recordHeight history) = true
  · exact (admitsHead_iff pre _).mp admits
  · rw [if_neg admits] at ok
    cases ok

theorem judge_write_ok {pre : System} {history : H} {posts : List (Option System)}
    (nonempty : posts ≠ []) (ok : judge pre history posts = .ok ()) :
    ∃ height digest, posts = [some (certifyNext pre height digest)] ∧
      pre.certifiedHeight < height ∧ ChainHistory.chainAt history height = some digest := by
  match posts, ok with
  | [], _ => exact absurd rfl nonempty
  | [some post], ok =>
      simp only [judge] at ok
      split at ok
      · rename_i certified
        obtain ⟨advancing, held⟩ := (ChainHistory.certifiable_ok_iff _ _ _ _).mp certified
        by_cases shape : post = certifyNext pre post.certifiedHeight post.certifiedDigest
        · exact ⟨post.certifiedHeight, post.certifiedDigest, by rw [← shape], advancing, held⟩
        · rw [if_neg shape] at ok
          cases ok
      · cases ok
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

/-- **The kernel's tail rule.**  `history` is the log before the record (the record takes
`recordHeight history`); `snapshot` the state it is judged on. -/
def gate {rootBytes : List UInt8 → Digest} (systemId : CellId) (history : H)
    (snapshot : DataSnapshot rootBytes) (intent : DataIntent rootBytes) :
    Except RejectReason Unit :=
  match valueOf (snapshot.canonicalBytes systemId) with
  | none => .error .systemUnavailable
  | some pre => judge pre history (systemPosts systemId intent)

theorem systemPosts_nil_iff {rootBytes : List UInt8 → Digest} (systemId : CellId)
    (intent : DataIntent rootBytes) :
    systemPosts systemId intent = [] ↔ ∀ write ∈ intent.writes, write.cellId ≠ systemId := by
  simp [systemPosts, List.filter_eq_nil_iff]

variable {rootBytes : List UInt8 → Digest} {systemId : CellId} {history : H}
  {snapshot : DataSnapshot rootBytes} {intent : DataIntent rootBytes}

/-- **`tail_bounded`.**  Every admitted record that is not a certify record —
it writes no system cell — sits at most `L` heights past the certified height
of the state it was judged on. -/
theorem tail_bounded (ok : gate systemId history snapshot intent = .ok ())
    (notCertify : ∀ write ∈ intent.writes, write.cellId ≠ systemId) :
    ∃ pre, valueOf (snapshot.canonicalBytes systemId) = some pre ∧
      recordHeight history - pre.certifiedHeight ≤ pre.tailBound := by
  unfold gate at ok
  split at ok
  · cases ok
  · rename_i pre found
    rw [(systemPosts_nil_iff systemId intent).mpr notCertify] at ok
    have := judge_none_ok ok
    exact ⟨pre, found, by omega⟩

/-- **`certified_written_only_by_checkpoint`.**  If an admitted record writes
the system cell at all, it writes it exactly once, and the value it writes is
the certification of a prefix past the certified height that the history holds
at that chain value, with the tail bound unchanged.  No other shape of write to
the system cell is admitted, whatever receiver produced it. -/
theorem certified_written_only_by_checkpoint (ok : gate systemId history snapshot intent = .ok ())
    (write : DataWrite) (member : write ∈ intent.writes) (target : write.cellId = systemId) :
    ∃ pre, valueOf (snapshot.canonicalBytes systemId) = some pre ∧
      ∃ height digest, systemPosts systemId intent = [some (certifyNext pre height digest)] ∧
        pre.certifiedHeight < height ∧ ChainHistory.chainAt history height = some digest := by
  unfold gate at ok
  split at ok
  · cases ok
  · rename_i pre found
    have nonempty : systemPosts systemId intent ≠ [] := by
      intro empty
      exact (systemPosts_nil_iff systemId intent).mp empty write member target
    exact ⟨pre, found, judge_write_ok nonempty ok⟩

/-- **`certified_true`.**  Over a history faithful to the log, the certified value an
admitted record installs is a true prefix: at or below the head the gate judged at, with
the log's own chain value there. -/
theorem certified_true {truth : Nat → Digest} (faithful : ChainHistory.Faithful history truth)
    (ok : gate systemId history snapshot intent = .ok ())
    (write : DataWrite) (member : write ∈ intent.writes) (target : write.cellId = systemId) :
    ∃ pre, valueOf (snapshot.canonicalBytes systemId) = some pre ∧
      ∃ height, systemPosts systemId intent = [some (certifyNext pre height (truth height))] ∧
        pre.certifiedHeight < height ∧ height < recordHeight history := by
  obtain ⟨pre, found, height, digest, posts, advancing, held⟩ :=
    certified_written_only_by_checkpoint ok write member target
  have within := ChainHistory.chainAt_le_head history height digest held
  have true_ := faithful.sound height digest held
  subst true_
  exact ⟨pre, found, height, posts, advancing, by unfold recordHeight; omega⟩

/-- **`certified_monotone`.**  A write to the system cell that the gate admits
installs a strictly greater certified height and the same tail bound. -/
theorem certified_monotone (ok : gate systemId history snapshot intent = .ok ())
    (write : DataWrite) (member : write ∈ intent.writes) (target : write.cellId = systemId)
    (post : System) (decoded : valueOf write.canonicalPostBytes = some post) :
    ∃ pre, valueOf (snapshot.canonicalBytes systemId) = some pre ∧
      pre.certifiedHeight < post.certifiedHeight ∧ post.tailBound = pre.tailBound := by
  obtain ⟨pre, found, height, digest, posts, advancing, _⟩ :=
    certified_written_only_by_checkpoint ok write member target
  have inPosts : some post ∈ systemPosts systemId intent := by
    simp only [systemPosts, List.mem_map, List.mem_filter]
    exact ⟨write, ⟨member, by simp [target]⟩, decoded⟩
  rw [posts, List.mem_singleton] at inPosts
  cases Option.some.inj inPosts
  exact ⟨pre, found, advancing, rfl⟩

/-- A system cell that is missing or undecodable refuses every record. -/
theorem unavailable_refuses (missing : valueOf (snapshot.canonicalBytes systemId) = none) :
    gate systemId history snapshot intent = .error .systemUnavailable := by
  unfold gate
  rw [missing]

/-! ## The poles, on the decision -/

/-- **Refuting pole** (general): the first height past the bound is refused by
name. -/
theorem beyond_bound_refused (pre : System) (history : H)
    (past : recordHeight history = pre.certifiedHeight + pre.tailBound + 1) :
    judge pre history [] =
      .error (.tailBound (pre.certifiedHeight + pre.tailBound + 1) pre.certifiedHeight pre.tailBound) := by
  have : admitsHead pre (recordHeight history) = false := by
    cases h : admitsHead pre (recordHeight history)
    · rfl
    · have := (admitsHead_iff _ _).mp h
      omega
  simp only [judge, this, Bool.false_eq_true, if_false]
  rw [past]

/-- **Satisfiable pole** (general): the last height inside the bound is admitted. -/
theorem at_bound_admitted (pre : System) (history : H)
    (at_ : recordHeight history = pre.certifiedHeight + pre.tailBound) :
    judge pre history [] = .ok () := by
  have : admitsHead pre (recordHeight history) = true :=
    (admitsHead_iff _ _).mpr (by omega)
  simp [judge, this]

/-- **`checkpoint_restores_progress`.**  A certify of a prefix `n` the history holds at
`chain` is admitted whenever it advances, and after it every record whose height is at most
`n + L` passes the tail law. -/
theorem checkpoint_restores_progress (pre : System) (history : H) (n : Nat) (chain : Digest)
    (held : ChainHistory.chainAt history n = some chain) (advancing : pre.certifiedHeight < n) :
    judge pre history [some (certifyNext pre n chain)] = .ok () ∧
      ∀ {H' : Type} [ChainHistory H'] (later : H'), recordHeight later ≤ n + pre.tailBound →
        judge (certifyNext pre n chain) later [] = .ok () := by
  refine ⟨?_, ?_⟩
  · have certified : ChainHistory.certifiable pre.certifiedHeight history n chain = .ok () :=
      (ChainHistory.certifiable_ok_iff _ _ _ _).mpr ⟨advancing, held⟩
    simp [judge, certifyNext, certified]
  · intro H' _ later within
    have : admitsHead (certifyNext pre n chain) (recordHeight later) = true :=
      (admitsHead_iff _ _).mpr (by simpa [certifyNext] using within)
    simp [judge, this]

/-! ## Built witnesses -/

/-- Certified at 64 with `L = 8`; the log's head is 72 at chain 9, so a record takes 73. -/
private def tip72 : ChainHistory.Tip := ⟨72, ⟨9⟩⟩

/-- **Refuting pole** (concrete): the ordinary record at height 73 is refused `tailBound 73 64 8`. -/
theorem tailBound_refuses_73 : judge ⟨64, ⟨7⟩, 8⟩ tip72 [] = .error (.tailBound 73 64 8) := by decide

/-- **Satisfiable pole** (concrete): with the head at 71, the record at 72 is admitted. -/
theorem tailBound_admits_72 : judge ⟨64, ⟨7⟩, 8⟩ (⟨71, ⟨9⟩⟩ : ChainHistory.Tip) [] = .ok () := by decide

/-- A certify of the head is admitted at a full tail (concrete). -/
theorem certify_admitted_at_full_tail :
    judge ⟨64, ⟨7⟩, 8⟩ tip72 [some ⟨72, ⟨9⟩, 8⟩] = .ok () := by decide

/-- A certify that changes the tail bound is refused (concrete). -/
theorem certify_cannot_move_bound :
    judge ⟨64, ⟨7⟩, 8⟩ tip72 [some ⟨72, ⟨9⟩, 1000⟩] = .error .systemWriteRefused := by decide

/-- A certify that names another chain value is refused (concrete). -/
theorem certify_wrong_chain_refused :
    judge ⟨64, ⟨7⟩, 8⟩ tip72 [some ⟨72, ⟨8⟩, 8⟩] = .error .systemWriteRefused := by decide

/-- A log of six records, chain after `h` records `⟨h⟩`; certified at 4 with `L = 2`, so the
next ordinary record (height 7) is past the bound. -/
private def six : Prefixes := Prefixes.ofTruth (fun h => ⟨h⟩) 6

/-- **The new liveness, concrete**: at that full tail, the ordinary record is refused, a
certify of the prefix 5 (not the head) is admitted, and after it the record is admitted. -/
theorem prefix_certify_reopens_writes :
    judge ⟨4, ⟨4⟩, 2⟩ six [] = .error (.tailBound 7 4 2) ∧
      judge ⟨4, ⟨4⟩, 2⟩ six [some ⟨5, ⟨5⟩, 2⟩] = .ok () ∧
      judge ⟨5, ⟨5⟩, 2⟩ six [] = .ok () := ⟨rfl, rfl, rfl⟩

/-- A certify of a prefix at or below the certified height, or past the head, is refused. -/
theorem prefix_certify_teeth :
    judge ⟨4, ⟨4⟩, 2⟩ six [some ⟨4, ⟨4⟩, 2⟩] = .error .systemWriteRefused ∧
      judge ⟨4, ⟨4⟩, 2⟩ six [some ⟨7, ⟨7⟩, 2⟩] = .error .systemWriteRefused ∧
      judge ⟨4, ⟨4⟩, 2⟩ six [some ⟨5, ⟨6⟩, 2⟩] = .error .systemWriteRefused := ⟨rfl, rfl, rfl⟩

#assert_axioms judge_none_ok judge_write_ok tail_bounded certified_written_only_by_checkpoint
  certified_true certified_monotone unavailable_refuses beyond_bound_refused at_bound_admitted
  checkpoint_restores_progress tailBound_refuses_73 tailBound_admits_72 certify_admitted_at_full_tail
  certify_cannot_move_bound certify_wrong_chain_refused prefix_certify_reopens_writes
  prefix_certify_teeth

end Minidregg.Kernel.TailBound
