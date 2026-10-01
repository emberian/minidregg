/-
# Kernel.TurnCensus — every live admission is expressible as a `Turn` (T1)

SURPASS §2(b), lane T1.  The Host admits through the 33 constructors of
`NativeHostReplay.NativeAdmission` (31 on main, `realmWell` and `clockTick`
on this tip; `final-pay` adds three pay constructors).  T0's census
(`planning/surpass/t0-receiver-census.md`) lists, per constructor, the cells it
reads and writes, its nullifiers, its charge and its clock pin.  This module
writes each constructor's **shape** as a `Turn` over the real `World.admit`,
in a census registry whose kinds are the deployed registry's, coarsened
(authority, resource, policy, book, stream, ticket, lifecycle, gateway,
clock, well, content), and decides, for every constructor at once:

* `turn_expressible`: the representative turn is accepted;
* `turn_negation_refused`: its negation — the stranger, the stale guard, the
  replayed marker or transaction, the over-allowance charge, the clock
  outside the window, the unguarded spend, the rewritten append-only row —
  is refused, with the named reason.

What this is not: `Turn.ofConstructor` here builds from each receiver's
*inputs as the census names them* (cell ids, values, markers, charge), not from
its `Accepted` object.  Deriving the turn from the admitted object is T3's
`Turn.ofIntent`; the shapes here are the targets it must hit.

`step_conserves` (SURPASS T9): a Book leg whose patch is a list of postings
moves the total over any account set by exactly the postings' deltas into it;
a balanced posting conserves it.  Stated and proved for the census Book
layout (`total` over a finite account set).  The deployed Book cell
(`Theory.CanonicalResourceKernel`) has its own layout; instantiating this at
it is T9's.

## What T3 starts from (statement only; not proved here)

```lean
theorem host_submit_is_step
    (accepted : NativeHostReplay.NativeAdmission config opened intent)
    (turn : Turn.ofIntent w intent = .ok t)              -- t : Turn R TxId Ev Digest
    (represents : Represents loaded w) :                 -- Represents : Loaded → World R TxId Digest → Prop
    Host.submit loaded intent = .ok (loaded', receipt) →
      ∃ w', World.admit H w t = .ok w' ∧ Represents loaded' w' ∧
        receipt.worldRoot = rootOf w' ∧
        receipt.height = (w.head.map Prod.fst).getD 0 + 1
```

`H := WorldRoot.cshakeHistory encode logRoot0 legBytes` (T1 made `legBytes` an
explicit argument: stage F must say what a leg's bytes are), `Turn` carries
`nullifiers := intent.nullifiers` (as digests), `charge := intent.exactCharge`,
`subject := intent.subject`, and the read guards become read legs.
-/
import Kernel.World
import Theory.AssertAxioms

namespace Minidregg.Kernel.TurnCensus

open Minidregg.Theory.Store
open Minidregg.Kernel.World
open Minidregg.Theory.ResourceCost (Lane Charge)

set_option autoImplicit false

/-! ## The census registry -/

/-- The kinds the 33 receivers touch. -/
inductive Kind
  | authority | resource | policy | book | stream | ticket | lifecycle | gateway | clock
  | well | content
  deriving DecidableEq, Repr

/-- Every census cell has a RAM row namespace and an append-only log. -/
inductive Space
  | rows
  | log
  deriving DecidableEq, Repr

/-- Census layout: `Nat` keys, `Int` values (a Book row is a signed balance). -/
def layout : Layout.{0, 0, 0} where
  Namespace := Space
  Key := fun _ => Nat
  Value := fun _ => Int
  discipline
    | .rows => .ram
    | .log => .appendOnly

/-- The census registry: every kind over the census layout. -/
abbrev R : Registry where
  Kind := Kind
  layout := fun _ => layout

abbrev CWorld := World R Nat Nat
abbrev CTurn := Turn R Nat Unit Nat

def rd (k : Nat) (v : Option Int) : Op layout := .read Space.rows k v
def wr (k : Nat) (b a : Int) : Op layout := .write Space.rows k b a
def al (k : Nat) (v : Int) : Op layout := .allocate Space.rows k v
def lg (k : Nat) (v : Int) : Op layout := .allocate Space.log k v
/-- A rewrite of an append-only row (never enabled). -/
def rewriteLog (k : Nat) (b a : Int) : Op layout := .write Space.log k b a

def leg (c : CellId) (k : Kind) (p : Patch layout) : Leg R := ⟨c, k, p⟩

/-- The census history: a leg is charged 16 bytes per op that writes. -/
def censusH : History R Nat Unit Nat where
  turnDigest := fun t => t.txId
  chain := fun r d => r + d + 1
  logRoot0 := 0
  legBytes := fun l => 16 * (l.patch.filter fun op => !Op.isRead op).length

/-! ## The census world -/

/-- Cell ids. -/
def cAuth : CellId := 0
def cRes : CellId := 1
def cPolicy : CellId := 2
def cBook : CellId := 3
def cStream : CellId := 4
def cTicket : CellId := 5
def cLife : CellId := 6
def cGate : CellId := 7
def cClock : CellId := 8
def cWell : CellId := 9
def cContent : CellId := 10
def cRoom : CellId := 11

def cellOf (k : Kind) (rows : List (Nat × Int)) : Cell R :=
  ⟨k, rows.foldl (fun (s : Store layout) e => s.set ⟨Space.rows, e.1⟩ (some e.2)) 0⟩

def cells0 : Cells R :=
  ((((((((((((0 : Cells R).update cAuth (some (cellOf .authority [(1, 1)]))).update cRes
    (some (cellOf .resource [(0, 10)]))).update cPolicy (some (cellOf .policy [(0, 1)]))).update
    cBook (some (cellOf .book [(0, 100), (1, 0)]))).update cStream
    (some (cellOf .stream []))).update cTicket (some (cellOf .ticket []))).update cLife
    (some (cellOf .lifecycle [(0, 0)]))).update cGate (some (cellOf .gateway [(0, 1)]))).update
    cClock (some (cellOf .clock [(0, 1000)]))).update cWell (some (cellOf .well [(0, 50)]))).update
    cContent (some (cellOf .content []))).update cRoom (some (cellOf .resource []))

/-- The meter every lane starts with. -/
def budget : Nat := 10000

/-- The census system cell: the genesis head, nullifier 99 already spent,
transaction 7 already journaled, every lane funded with `budget`. -/
def system0 : Store (sysLayout Nat Nat) :=
  meterLanes.foldl
    (fun (s : Store (sysLayout Nat Nat)) l => s.set ⟨SysSpace.allowance, l⟩ (some budget))
    (((genesisSystem censusH).set ⟨SysSpace.spent, (99 : Nat)⟩ (some ())).set
      ⟨SysSpace.journal, (7 : Nat)⟩ (some ((0 : Nat), (0 : Nat))))

def w0 : CWorld := ⟨cells0, system0⟩

/-! ## Turn builder -/

/-- A census turn: the storage lane is the patch bytes unless `storage`
overrides it (the mis-charged negation); `fee` is the fee lane. -/
def mk (creates : List (CellId × Kind × Option CellId)) (legs : List (Leg R)) (ns : List Nat)
    (fee : Nat := 0) (x : Nat := 1) (notBefore : Nat := 0) (validUntil : Option Nat := none)
    (cap : Option Nat := none) (storage : Option Nat := none) : CTurn :=
  { txId := x, creates := creates, legs := legs, retires := [], event := (), nullifiers := ns,
    charge := fun l =>
      if l = .storageBytes then storage.getD (legs.map censusH.legBytes).sum
      else if l = .feeDebit then fee else 0,
    subject := some ⟨1⟩, keyEpoch := 0, capability := cap, notBefore := notBefore,
    validUntil := validUntil }

/-! ## The constructors -/

/-- The admission constructors on this tip (`NativeHostReplay.lean:679-`). -/
inductive Ctor
  | birth | grainBirth | invoke | install | delegate | revoke
  | participantKeyEnrollment | participantFactoryProvisioning | fleetTurn | payBook
  | payAssignment | realmWell | clockTick | selectiveRelease | applicationShareIssue
  | applicationGrainShareIssue | applicationSessionEnrollment
  | applicationAgentLifetimeGrantIssue | applicationDispatch | applicationAgentDispatch
  | applicationAgentLifetimeDispatch | selectedSourcePublication | applicationLifecycleBegin
  | applicationLifecycleClaim | applicationLifecycleBeginV2 | applicationLifecycleClaimV2
  | applicationLifecycleCompletion | applicationLifecycleBeginV3 | applicationLifecycleClaimV3
  | applicationLifecycleCompletionV2 | fnConsumerNamespace | fnSelectedPoll | fnEmptyPollV2
  deriving DecidableEq, Repr

def Ctor.all : List Ctor :=
  [.birth, .grainBirth, .invoke, .install, .delegate, .revoke, .participantKeyEnrollment,
    .participantFactoryProvisioning, .fleetTurn, .payBook, .payAssignment, .realmWell,
    .clockTick, .selectiveRelease, .applicationShareIssue, .applicationGrainShareIssue,
    .applicationSessionEnrollment, .applicationAgentLifetimeGrantIssue, .applicationDispatch,
    .applicationAgentDispatch, .applicationAgentLifetimeDispatch, .selectedSourcePublication,
    .applicationLifecycleBegin, .applicationLifecycleClaim, .applicationLifecycleBeginV2,
    .applicationLifecycleClaimV2, .applicationLifecycleCompletion, .applicationLifecycleBeginV3,
    .applicationLifecycleClaimV3, .applicationLifecycleCompletionV2, .fnConsumerNamespace,
    .fnSelectedPoll, .fnEmptyPollV2]

theorem Ctor.mem_all (c : Ctor) : c ∈ Ctor.all := by cases c <;> decide

theorem Ctor.all_length : Ctor.all.length = 33 := rfl

/-- The capability guard: the authority row the exercised capability lives at. -/
def capGuard : Leg R := leg cAuth .authority [rd 1 (some 1)]
/-- The fn gateway pin, read and not written. -/
def gateGuard : Leg R := leg cGate .gateway [rd 0 (some 1)]

/-- **`Turn.ofConstructor`**: each receiver's census shape, at representative
inputs. -/
def Ctor.turn : Ctor → CTurn
  -- birth: a resource cell born in a room, the birth record, its marker
  | .birth => mk [(20, .resource, some cRoom)]
      [leg cAuth .authority [rd 1 (some 1), lg 1 1], leg 20 .resource [al 0 0]] [101]
  -- grain birth: two grain targets, two markers
  | .grainBirth => mk [(21, .resource, none), (22, .resource, none)]
      [leg cAuth .authority [lg 2 1], leg 21 .resource [al 0 0], leg 22 .resource [al 0 0]]
      [102, 103]
  -- invoke: the capability guard, the target write, a validity height
  | .invoke => mk [] [capGuard, leg cRes .resource [wr 0 10 11]] [104]
      (validUntil := some 256) (cap := some 1)
  | .install => mk [] [capGuard, leg cPolicy .policy [wr 0 1 2]] [105]
  | .delegate => mk [] [leg cAuth .authority [rd 1 (some 1), lg 3 1]] [106] (cap := some 1)
  | .revoke => mk [] [leg cAuth .authority [lg 4 1]] [107]
  | .participantKeyEnrollment => mk [] [leg cAuth .authority [lg 5 1]] [108]
  | .participantFactoryProvisioning => mk [] [leg cAuth .authority [lg 6 1]] [109]
      (validUntil := some 10)
  -- fleet: the payer's fee debit, the topic cell created explicitly
  | .fleetTurn => mk [(23, .stream, none)]
      [leg cBook .book [wr 0 100 95], leg 23 .stream [lg 0 1]] [110] (fee := 5)
  -- pay book: a balanced posting
  | .payBook => mk [] [leg cBook .book [wr 0 100 90, wr 1 0 10]] [111]
  -- pay assignment: guarded on account A (the census found no guard deployed)
  | .payAssignment => mk [] [leg cBook .book [rd 0 (some 100), al 2 1]] [112]
  | .realmWell => mk [] [leg cWell .well [wr 0 50 40]] [113]
  | .clockTick => mk [] [leg cClock .clock [wr 0 1000 1001]] [114]
  | .selectiveRelease => mk [] [leg cContent .content [al 0 1]] [115]
  | .applicationShareIssue => mk [] [leg cTicket .ticket [al 0 1]] [116]
  | .applicationGrainShareIssue => mk [] [leg cTicket .ticket [al 1 1]] [117]
  | .applicationSessionEnrollment => mk [] [leg cTicket .ticket [al 2 1]] [118]
  | .applicationAgentLifetimeGrantIssue => mk [] [leg cTicket .ticket [al 3 1]] [119]
  | .applicationDispatch => mk [] [leg cTicket .ticket [al 4 1]] [120]
  -- agent dispatch: the reserve is a purse debit, so a stale purse is a guard
  | .applicationAgentDispatch => mk [] [leg cBook .book [wr 0 100 90], leg cTicket .ticket [al 5 1]]
      [121]
  | .applicationAgentLifetimeDispatch => mk []
      [leg cBook .book [wr 0 100 80], leg cTicket .ticket [al 6 1]] [122]
  -- no cell written: a nullifier-only turn pinned by its read guard
  | .selectedSourcePublication => mk [] [capGuard] [123]
  | .applicationLifecycleBegin => mk [] [leg cLife .lifecycle [wr 0 0 1]] [124]
  | .applicationLifecycleClaim => mk [] [leg cLife .lifecycle [rd 0 (some 0), al 1 1]] [125]
  | .applicationLifecycleBeginV2 => mk [] [leg cLife .lifecycle [al 2 1]] [126]
  | .applicationLifecycleClaimV2 => mk [] [leg cLife .lifecycle [al 3 1]] [127]
  | .applicationLifecycleCompletion => mk [] [leg cLife .lifecycle [al 4 1]] [128]
  | .applicationLifecycleBeginV3 => mk [] [leg cLife .lifecycle [al 5 1]] [129]
  -- claim V3: the whole-root pin becomes an address-level read
  | .applicationLifecycleClaimV3 => mk [] [leg cLife .lifecycle [rd 0 (some 0), al 6 1]] [130]
  | .applicationLifecycleCompletionV2 => mk [] [leg cLife .lifecycle [wr 0 0 2]] [131]
  | .fnConsumerNamespace => mk [] [gateGuard] [132]
  | .fnSelectedPoll => mk [] [gateGuard] [133]
  | .fnEmptyPollV2 => mk [] [gateGuard] [134]

/-- Each constructor's negation: the case its receiver must refuse. -/
def Ctor.negation : Ctor → CTurn
  -- a room that does not exist
  | .birth => mk [(20, .resource, some 55)] [leg 20 .resource [al 0 0]] [101]
  -- one of the two markers already spent
  | .grainBirth => mk [(21, .resource, none)] [leg 21 .resource [al 0 0]] [102, 99]
  -- the target moved under the signed guard
  | .invoke => mk [] [capGuard, leg cRes .resource [wr 0 9 11]] [104] (cap := some 1)
  | .install => mk [] [capGuard, leg cPolicy .policy [wr 0 1 2]] [99]
  -- a stranger: the authority cell named at the wrong kind
  | .delegate => mk [] [leg cAuth .resource [lg 3 1]] [106]
  | .revoke => mk [] [leg cAuth .authority [lg 4 1]] [107] (fee := budget + 1)
  | .participantKeyEnrollment => mk [] [leg cAuth .authority [lg 5 1]] [108] (notBefore := 5)
  | .participantFactoryProvisioning => mk [] [leg cAuth .authority [lg 6 1]] [109, 109]
  -- the topic cell written without being created
  | .fleetTurn => mk [] [leg cBook .book [wr 0 100 95], leg 23 .stream [lg 0 1]] [110] (fee := 5)
  | .payBook => mk [] [leg cBook .book [wr 0 100 90, wr 1 0 10]] [111] (storage := some 0)
  | .payAssignment => mk [] [leg cBook .book [rd 0 (some 99), al 2 1]] [112]
  | .realmWell => mk [] [leg cWell .book [wr 0 50 40]] [113]
  | .clockTick => mk [] [leg cClock .clock [wr 0 999 1001]] [114]
  | .selectiveRelease => mk [] [leg cContent .content [al 0 1]] [99]
  | .applicationShareIssue => mk [] [leg cTicket .ticket [al 0 1]] [116] (x := 7)
  | .applicationGrainShareIssue => mk [] [leg cTicket .ticket [al 1 1]] [117, 117]
  | .applicationSessionEnrollment => mk [] [leg cTicket .ticket [al 2 1]] [99]
  | .applicationAgentLifetimeGrantIssue => mk [] [leg cTicket .ticket [al 3 1]] [119]
      (fee := budget + 1)
  | .applicationDispatch => mk [] [leg cTicket .ticket [al 4 1]] [120] (notBefore := 1)
  | .applicationAgentDispatch => mk [] [leg cBook .book [wr 0 90 80], leg cTicket .ticket [al 5 1]]
      [121]
  | .applicationAgentLifetimeDispatch => mk []
      [leg cBook .book [wr 0 100 80], leg cTicket .ticket [al 6 1]] [122] (storage := some 16)
  -- the unguarded spend
  | .selectedSourcePublication => mk [] [] [123]
  | .applicationLifecycleBegin => mk [] [leg cLife .lifecycle [wr 0 0 1]] [99]
  | .applicationLifecycleClaim => mk [] [leg cLife .lifecycle [rd 0 (some 5), al 1 1]] [125]
  | .applicationLifecycleBeginV2 => mk [] [leg cLife .lifecycle [al 2 1]] [99]
  | .applicationLifecycleClaimV2 => mk [] [leg cLife .lifecycle [al 3 1]] [127, 127]
  | .applicationLifecycleCompletion => mk [] [leg cLife .lifecycle [al 4 1]] [128]
      (fee := budget + 1)
  | .applicationLifecycleBeginV3 => mk [] [leg cLife .lifecycle [al 5 1]] [129] (x := 7)
  | .applicationLifecycleClaimV3 => mk [] [leg cLife .lifecycle [rd 0 (some 3), al 6 1]] [130]
  -- an append-only row rewritten
  | .applicationLifecycleCompletionV2 => mk []
      [leg cLife .lifecycle [rewriteLog 0 0 2]] [131]
  | .fnConsumerNamespace => mk [] [] [132]
  | .fnSelectedPoll => mk [] [gateGuard] [99]
  | .fnEmptyPollV2 => mk [] [leg cGate .gateway [rd 0 (some 0)]] [134]

/-- The reason each negation is refused with. -/
def Ctor.refusal : Ctor → Reject
  | .birth => .missingParent 20 55
  | .grainBirth => .nullifierSpent
  | .invoke => .guardFailed cRes 0
  | .install => .nullifierSpent
  | .delegate => .kindMismatch cAuth
  | .revoke => .overAllowance
  | .participantKeyEnrollment => .outsideWindow
  | .participantFactoryProvisioning => .duplicateNullifier
  | .fleetTurn => .missingCell 23
  | .payBook => .chargeMismatch
  | .payAssignment => .guardFailed cBook 0
  | .realmWell => .kindMismatch cWell
  | .clockTick => .guardFailed cClock 0
  | .selectiveRelease => .nullifierSpent
  | .applicationShareIssue => .replayedTransaction
  | .applicationGrainShareIssue => .duplicateNullifier
  | .applicationSessionEnrollment => .nullifierSpent
  | .applicationAgentLifetimeGrantIssue => .overAllowance
  | .applicationDispatch => .outsideWindow
  | .applicationAgentDispatch => .guardFailed cBook 0
  | .applicationAgentLifetimeDispatch => .chargeMismatch
  | .selectedSourcePublication => .emptyTurn
  | .applicationLifecycleBegin => .nullifierSpent
  | .applicationLifecycleClaim => .guardFailed cLife 0
  | .applicationLifecycleBeginV2 => .nullifierSpent
  | .applicationLifecycleClaimV2 => .duplicateNullifier
  | .applicationLifecycleCompletion => .overAllowance
  | .applicationLifecycleBeginV3 => .replayedTransaction
  | .applicationLifecycleClaimV3 => .guardFailed cLife 0
  | .applicationLifecycleCompletionV2 => .guardFailed cLife 0
  | .fnConsumerNamespace => .emptyTurn
  | .fnSelectedPoll => .nullifierSpent
  | .fnEmptyPollV2 => .guardFailed cGate 0

/-! ## The poles -/

theorem turn_expressible_all :
    ∀ c ∈ Ctor.all, rejectOf (World.admit censusH w0 c.turn) = none := by
  decide +kernel

theorem turn_negation_refused_all :
    ∀ c ∈ Ctor.all, rejectOf (World.admit censusH w0 c.negation) = some c.refusal := by
  decide +kernel

/-- **Every constructor is expressible**: its turn is accepted by the one
transition. -/
theorem turn_expressible (c : Ctor) : rejectOf (World.admit censusH w0 c.turn) = none :=
  turn_expressible_all c (Ctor.mem_all c)

/-- **And its negation is refused**, for the named reason. -/
theorem turn_negation_refused (c : Ctor) :
    rejectOf (World.admit censusH w0 c.negation) = some c.refusal :=
  turn_negation_refused_all c (Ctor.mem_all c)

/-- The four constructors that write no cell are nullifier-only turns: no
create, no retire, every leg a pure read guard, one nullifier. -/
def NullifierOnly (t : CTurn) : Prop :=
  t.creates = [] ∧ t.retires = [] ∧ t.nullifiers ≠ [] ∧
    ∀ l ∈ t.legs, ∀ op ∈ l.patch, Op.isRead op = true

instance (t : CTurn) : Decidable (NullifierOnly t) := by
  unfold NullifierOnly; infer_instance

theorem no_cell_ctors_nullifier_only :
    ∀ c ∈ [Ctor.selectedSourcePublication, .fnConsumerNamespace, .fnSelectedPoll, .fnEmptyPollV2],
      NullifierOnly c.turn ∧ c.turn.legs ≠ [] := by
  decide

/-! ## `step_conserves`: a Book leg of postings conserves its totals (T9) -/

/-- A posting: one account's balance moved from `before` to `after`. -/
structure Posting where
  account : Nat
  before : Int
  after : Int

def Posting.op (p : Posting) : Op layout := .write Space.rows p.account p.before p.after
def Posting.delta (p : Posting) : Int := p.after - p.before

/-- The total over a finite account set. -/
def total (K : Finset Nat) (s : Store layout) : Int :=
  ∑ k ∈ K, Option.getD (α := Int) (s ⟨Space.rows, k⟩) 0

theorem total_set (K : Finset Nat) (s : Store layout) (a : Nat) (v : Int) :
    total K (s.set ⟨Space.rows, a⟩ (some v)) =
      total K s + (if a ∈ K then v - Option.getD (α := Int) (s ⟨Space.rows, a⟩) 0 else 0) := by
  unfold total
  have frame : ∀ k ∈ K.erase a, Option.getD (α := Int) ((s.set ⟨Space.rows, a⟩ (some v))
      ⟨Space.rows, k⟩) 0 = Option.getD (α := Int) (s ⟨Space.rows, k⟩) 0 := by
    intro k hk
    have hne : k ≠ a := (Finset.mem_erase.mp hk).1
    rw [Store.set_ne _ _ _ _ (fun e => hne (eq_of_heq (Sigma.mk.inj e).2))]
  by_cases ha : a ∈ K
  · rw [if_pos ha, ← Finset.add_sum_erase K _ ha, ← Finset.add_sum_erase K _ ha,
      Finset.sum_congr rfl (fun k hk => by rw [frame k hk])]
    have e : Option.getD (α := Int) ((s.set ⟨Space.rows, a⟩ (some v)) ⟨Space.rows, a⟩) 0 = v := by
      rw [Store.set_eq]; rfl
    rw [e]
    ring
  · rw [if_neg ha, add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hne : k ≠ a := fun e => ha (e ▸ hk)
    rw [Store.set_ne _ _ _ _ (fun e => hne (eq_of_heq (Sigma.mk.inj e).2))]

/-- **Postings move a total by exactly their deltas into it** — the total is a
homomorphism, conservation its kernel. -/
theorem run_postings_total (K : Finset Nat) :
    ∀ (s : Store layout) (ps : List Posting), Patch.ValidFrom s (ps.map Posting.op) →
      total K (Patch.run s (ps.map Posting.op)) =
        total K s + ((ps.filter fun p => decide (p.account ∈ K)).map Posting.delta).sum
  | s, [], _ => by simp
  | s, p :: rest, valid => by
      have pre : Option.getD (α := Int) (s ⟨Space.rows, p.account⟩) 0 = p.before := by
        have e : s ⟨Space.rows, p.account⟩ = some p.before := valid.1.2
        rw [e]; rfl
      have ih : total K (Patch.run (s.set ⟨Space.rows, p.account⟩ (some p.after))
          (rest.map Posting.op)) = total K (s.set ⟨Space.rows, p.account⟩ (some p.after)) +
            ((rest.filter fun p => decide (p.account ∈ K)).map Posting.delta).sum :=
        run_postings_total K _ rest valid.2
      show total K (Patch.run (s.set ⟨Space.rows, p.account⟩ (some p.after))
        (rest.map Posting.op)) = _
      rw [ih, total_set, pre]
      by_cases ha : p.account ∈ K
      · simp only [if_pos ha, List.filter_cons, decide_eq_true ha, if_true, List.map_cons,
          List.sum_cons, Posting.delta]
        ring
      · simp [ha]

/-- **`step_conserves`** (SURPASS T9's statement, at the census Book): if an
accepted turn's leg on an existing Book cell is a list of postings that
balances over an account set `K`, the Book's total over `K` is the same
after the turn as before. -/
theorem step_conserves {TxId D : Type} [DecidableEq TxId] [DecidableEq D]
    (H : History R TxId Unit D) {w w' : World R TxId D} {t : Turn R TxId Unit D}
    (h : World.step H w t = some w') (b : CellId) (ps : List Posting)
    (m : leg b .book (ps.map Posting.op) ∈ t.legs)
    (hc : b ∉ t.creates.map Prod.fst) (hr : b ∉ t.retires) (K : Finset Nat)
    (balanced : ((ps.filter fun p => decide (p.account ∈ K)).map Posting.delta).sum = 0) :
    ∃ pre post, (w.cells b).bind (·.storeAt Kind.book) = some pre ∧
      (w'.cells b).bind (·.storeAt Kind.book) = some post ∧ total K post = total K pre := by
  obtain ⟨pre, hpre, hv, hpost⟩ := step_leg H h _ m hc hr
  have hpost' : w'.cells b = some ⟨Kind.book, Patch.run pre (ps.map Posting.op)⟩ := hpost
  refine ⟨pre, Patch.run pre (ps.map Posting.op), hpre, ?_, ?_⟩
  · rw [hpost']
    exact Cell.storeAt_self (R := R) Kind.book _
  · rw [run_postings_total K pre ps hv, balanced, add_zero]

/-- The pay-book constructor's postings. -/
def payPostings : List Posting := [⟨0, 100, 90⟩, ⟨1, 0, 10⟩]

theorem payBook_legs : (Ctor.turn .payBook).legs = [leg cBook .book (payPostings.map Posting.op)] :=
  rfl

theorem payPostings_balanced :
    ((payPostings.filter fun p => decide (p.account ∈ ({0, 1} : Finset Nat))).map
      Posting.delta).sum = 0 := by
  decide

/-- **The pay-book turn conserves its Book**, at every world it is accepted at. -/
theorem payBook_conserves {w w' : CWorld} (h : World.step censusH w (Ctor.turn .payBook) = some w') :
    ∃ pre post, (w.cells cBook).bind (·.storeAt Kind.book) = some pre ∧
      (w'.cells cBook).bind (·.storeAt Kind.book) = some post ∧
      total {0, 1} post = total {0, 1} pre :=
  step_conserves censusH h cBook payPostings (by rw [payBook_legs]; exact List.mem_singleton_self _)
    (by decide) (by decide) {0, 1} payPostings_balanced

#assert_axioms Ctor.mem_all
#assert_axioms turn_expressible
#assert_axioms turn_negation_refused
#assert_axioms no_cell_ctors_nullifier_only
#assert_axioms total_set
#assert_axioms run_postings_total
#assert_axioms step_conserves
#assert_axioms payPostings_balanced
#assert_axioms payBook_conserves

end Minidregg.Kernel.TurnCensus
