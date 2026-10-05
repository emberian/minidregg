/- Certified clearing: a DrEX batch as seats, judged by a Cert-F certificate.

Each order is a seat (`Kernel.Seat`) of one market instance: a BID gives
currency and wants goods (`give [(currency, budget)]`, `want [(goods, qty)]`),
an ASK gives goods and wants currency (`give [(goods, qty)]`,
`want [(currency, reserve)]`). When the batch window closes, an UNTRUSTED
clearer proposes a uniform-price allocation: the seat-to-seat transfers that
realize it, and a Cert-F certificate `(price, π, s)`. The judgment here admits
it only if

* every transfer moves the market's two assets between order seats of the
  instance (`foreignAsset`, `notAnOrder`);
* every order trades at the one price: an order that received (bid) or
  delivered (ask) `k` goods paid or received exactly `price * k` currency
  (`notUniform`);
* the fills read off the transfers, with the clearer's dual, are a Cert-F
  certificate (`Theory.CertF.Certified`) for the volume-max circulation LP of
  this batch at this price (`lpOf`): conservation `Σ bid fills = Σ ask fills`,
  `0 ≤ fill ≤ capacity` where an order's capacity is its quantity when its limit
  crosses the price and `0` otherwise, dual feasibility, and duality gap
  `≤ ε` (`uncertified`);

and then the transfers are the instance's ordinary `reallocate` step, so every
seat they touch is judged by its own offer-safety law and the Book conserves
every asset (`Kernel.Seat.step`).

What the pieces guarantee, and why both are needed:
* Offer safety is all-or-nothing per seat (`want` met, or `give` refunded), so
  it refuses partial fills and fills outside an order's limit; it does NOT
  refuse an allocation that leaves crossed orders unfilled. The tooth
  `suboptimal_passes_offer_safety` shows such an allocation admitted by the
  seat kernel alone, and `suboptimal_refused` shows the certificate refusing it.
* The certificate bounds the volume of EVERY feasible fractional circulation by
  the cleared volume plus `ε` (`clear_epsilon_optimal`, from
  `certifies_epsilon_optimal`); integral all-or-nothing allocations are among
  them, so the bound holds against them too. The integrality gap is real: an
  all-or-nothing batch can be refused at `ε = 0` and admitted only at a larger
  `ε` (`integrality_gap_refused_at_zero`).
* The certificate's numbers are checked, never trusted: a claimed dual that is
  not dual-feasible is refused however small the gap it implies
  (`forged_dual_refused`).

The judgment reads the fills OFF the transfers; it does not compute an
allocation, and it is not a second transition function: the transfers are
posted by `Seats.step` and nothing else.

Native route: on `lane/seats-native` the instance acts only through the Plan its
own package method returns (ROOT ruling 10-05). The package
`world/drex/DrexBatch.obend` is that method for a DrEX instance: it routes the
clearer's fills into seat-to-seat moves and returns them with the certificate.
Wiring `clear` as the receiver's judgment of that Plan action is the native leg,
after SEATS-NATIVE lands. -/
import Kernel.Seat
import Theory.CertF

namespace Minidregg.Kernel.CertifiedClearing
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.CertF
open Minidregg.Kernel.Seats
open Minidregg.Kernel.Invitations (InstanceId)
open Matrix
set_option autoImplicit false

/-! ## Markets, orders and the batch LP -/

/-- A market instance's terms: the asset bids pay in, the asset asks sell, and
the accuracy target of every clearing. -/
structure Market where
  currency : AssetId
  goods : AssetId
  epsilon : Nat
  deriving DecidableEq, Repr

inductive Side where
  | bid
  | ask
  deriving DecidableEq, Repr

/-- An order read off a seat. `total` is a bid's budget (the most it pays for
`qty`) or an ask's reserve (the least it accepts for `qty`). -/
structure Order where
  account : AccountId
  side : Side
  qty : Nat
  total : Nat
  deriving DecidableEq, Repr

/-- A seat is an order when its proposal gives one market asset and wants the
other, a positive quantity of goods. Any other seat of the instance is not an
order: it is no edge of the LP, and no clearing transfer may touch it. -/
def orderOf (market : Market) (seat : Seat) : Option Order :=
  match seat.proposal.give, seat.proposal.want with
  | [(given, amount)], [(wanted, wantAmount)] =>
    if given = market.currency ∧ wanted = market.goods ∧ 0 < wantAmount then
      some ⟨seat.account, .bid, wantAmount, amount⟩
    else if given = market.goods ∧ wanted = market.currency ∧ 0 < amount then
      some ⟨seat.account, .ask, amount, wantAmount⟩
    else none
  | _, _ => none

def ordersOf (market : Market) (seats : List Seat) : List Order :=
  seats.filterMap (orderOf market)

/-- An order crosses the price when trading its whole quantity there respects
its limit. -/
def Order.crosses (price : Nat) (order : Order) : Bool :=
  match order.side with
  | .bid => decide (price * order.qty ≤ order.total)
  | .ask => decide (order.total ≤ price * order.qty)

/-- The column of an order in the two-node trade graph: a bid is an edge
`0 → 1`, an ask `1 → 0`, so `A f = 0` says the goods bids receive are the goods
asks deliver. -/
def Side.out : Side → Int
  | .bid => -1
  | .ask => 1

def incidence (orders : List Order) : Matrix (Fin 2) (Fin orders.length) Int :=
  fun node edge => if node = 0 then (orders.get edge).side.out else -(orders.get edge).side.out

/-- The volume-max circulation LP of a batch at a price: unit weights (the
objective is twice the traded quantity), capacity `qty` on a crossing order and
`0` on any other. -/
def lpOf (market : Market) (orders : List Order) (price : Nat) : FlowLP (Fin 2) (Fin orders.length) Int where
  A := incidence orders
  w := fun _ => 1
  c := fun edge => if (orders.get edge).crosses price then ((orders.get edge).qty : Int) else 0
  ε := (market.epsilon : Int)

/-! ## Reading an allocation off the transfers -/

/-- What `account` gains in `asset` over the transfers. -/
def netFlow (transfers : List Transfer) (account : AccountId) (asset : AssetId) : Int :=
  (transfers.map fun transfer =>
    (if transfer.destination = account ∧ transfer.asset = asset then (transfer.amount : Int) else 0) -
      (if transfer.source = account ∧ transfer.asset = asset then (transfer.amount : Int) else 0)).sum

/-- The goods an order traded: received (bid) or delivered (ask). -/
def Order.fill (market : Market) (transfers : List Transfer) (order : Order) : Int :=
  match order.side with
  | .bid => netFlow transfers order.account market.goods
  | .ask => -netFlow transfers order.account market.goods

/-- The currency an order paid (bid) or received (ask). -/
def Order.paid (market : Market) (transfers : List Transfer) (order : Order) : Int :=
  match order.side with
  | .bid => -netFlow transfers order.account market.currency
  | .ask => netFlow transfers order.account market.currency

def fills (market : Market) (orders : List Order) (transfers : List Transfer) : Fin orders.length → Int :=
  fun edge => (orders.get edge).fill market transfers

/-! ## The certificate -/

/-- The clearer's certificate: the uniform price, node potentials `π` and one
slack per order (in the order of `ordersOf`). -/
structure Certificate where
  price : Nat
  potentials : Int × Int
  slacks : List Int
  deriving DecidableEq, Repr

def Certificate.π (certificate : Certificate) : Fin 2 → Int :=
  ![certificate.potentials.1, certificate.potentials.2]

def Certificate.s (certificate : Certificate) (n : Nat) : Fin n → Int :=
  fun edge => certificate.slacks.getD edge 0

instance primalDecidable {n : Nat} (lp : FlowLP (Fin 2) (Fin n) Int) (f : Fin n → Int) :
    Decidable (PrimalFeasible lp f) :=
  decidable_of_iff (lp.A *ᵥ f = 0 ∧ (∀ edge, 0 ≤ f edge) ∧ ∀ edge, f edge ≤ lp.c edge) Iff.rfl

instance dualDecidable {n : Nat} (lp : FlowLP (Fin 2) (Fin n) Int) (π : Fin 2 → Int) (s : Fin n → Int) :
    Decidable (DualFeasible lp π s) :=
  decidable_of_iff ((∀ edge, 0 ≤ s edge) ∧ ∀ edge, lp.w edge ≤ (π ᵥ* lp.A) edge + s edge) Iff.rfl

instance certifiedDecidable {n : Nat} (lp : FlowLP (Fin 2) (Fin n) Int) (f : Fin n → Int)
    (π : Fin 2 → Int) (s : Fin n → Int) : Decidable (Certified lp f π s) :=
  inferInstanceAs (Decidable (PrimalFeasible lp f ∧ DualFeasible lp π s ∧ lp.c ⬝ᵥ s - lp.w ⬝ᵥ f ≤ lp.ε))

/-- The duality gap a certificate claims (reported in a refusal). -/
def gap {n : Nat} (lp : FlowLP (Fin 2) (Fin n) Int) (f s : Fin n → Int) : Int :=
  lp.c ⬝ᵥ s - lp.w ⬝ᵥ f

/-! ## The judgment and the clearing step -/

inductive Refusal where
  | marketMalformed
  | foreignAsset (transfer : Transfer)
  | notAnOrder (transfer : Transfer)
  | slackCount (orders slacks : Nat)
  | notUniform (account : AccountId)
  | uncertified (gap : Int) (epsilon : Nat)
  | seat (reason : Seats.Refusal)
  deriving DecidableEq, Repr

def isOrderAccount (orders : List Order) (account : AccountId) : Bool :=
  orders.any fun order => order.account == account

/-- The Cert-F judgment of a proposed clearing over the batch's orders. -/
def judge (market : Market) (orders : List Order) (transfers : List Transfer) (certificate : Certificate) :
    Except Refusal Unit :=
  if market.currency = market.goods then .error .marketMalformed
  else match transfers.find? (fun t => t.asset != market.currency && t.asset != market.goods) with
  | some transfer => .error (.foreignAsset transfer)
  | none =>
    match transfers.find? (fun t => !isOrderAccount orders t.source || !isOrderAccount orders t.destination) with
    | some transfer => .error (.notAnOrder transfer)
    | none =>
      if certificate.slacks.length ≠ orders.length then
        .error (.slackCount orders.length certificate.slacks.length)
      else
        match orders.find? (fun order =>
            order.paid market transfers != (certificate.price : Int) * order.fill market transfers) with
        | some order => .error (.notUniform order.account)
        | none =>
          if Certified (lpOf market orders certificate.price) (fills market orders transfers)
              certificate.π (certificate.s orders.length) then .ok ()
          else .error (.uncertified
            (gap (lpOf market orders certificate.price) (fills market orders transfers)
              (certificate.s orders.length)) market.epsilon)

/-- The batch's orders: the open order seats of the instance, by ascending seat
account (the order a contract method sees them in, and the order of the
certificate's slacks). Insertion sort: structural, so the kernel evaluates it. -/
def batchOrders (world : World) (inst : InstanceId) (market : Market) : List Order :=
  ordersOf market ((openSeatsOf world inst).insertionSort fun a b => a.account ≤ b.account)

/-- Clear a batch: the certificate judgment, then the instance's reallocation,
judged by every touched seat's offer-safety law. -/
def clear (world : World) (height : Nat) (inst : InstanceId) (market : Market)
    (transfers : List Transfer) (certificate : Certificate) : Except Refusal World :=
  match judge market (batchOrders world inst market) transfers certificate with
  | .error reason => .error reason
  | .ok () =>
    match step world height (.inst inst) (.reallocate inst transfers) with
    | .error reason => .error (.seat reason)
    | .ok (next, _) => .ok next

/-! ## What the judgment guarantees -/

theorem judge_spec {market : Market} {orders : List Order} {transfers : List Transfer}
    {certificate : Certificate} (judged : judge market orders transfers certificate = .ok ()) :
    (∀ order ∈ orders, order.paid market transfers = (certificate.price : Int) * order.fill market transfers) ∧
      (∀ transfer ∈ transfers, isOrderAccount orders transfer.source = true ∧
        isOrderAccount orders transfer.destination = true) ∧
      Certified (lpOf market orders certificate.price) (fills market orders transfers)
        certificate.π (certificate.s orders.length) := by
  unfold judge at judged
  split at judged
  · cases judged
  split at judged
  · cases judged
  split at judged
  · cases judged
  rename_i noneOutside
  split at judged
  · cases judged
  split at judged
  · cases judged
  rename_i noneUneven
  split at judged
  · rename_i certified
    refine ⟨fun order member => ?_, fun transfer member => ?_, certified⟩
    · have := List.find?_eq_none.mp noneUneven order member
      simpa using this
    · have := List.find?_eq_none.mp noneOutside transfer member
      simpa [Bool.or_eq_true, not_or] using this
  · cases judged

theorem clear_spec {world next : World} {height : Nat} {inst : InstanceId} {market : Market}
    {transfers : List Transfer} {certificate : Certificate}
    (cleared : clear world height inst market transfers certificate = .ok next) :
    judge market (batchOrders world inst market) transfers certificate = .ok () ∧
      ∃ batch, step world height (.inst inst) (.reallocate inst transfers) = .ok (next, batch) := by
  unfold clear at cleared
  split at cleared
  · cases cleared
  · rename_i judged
    split at cleared
    · cases cleared
    · rename_i stepped
      cases cleared
      exact ⟨judged, _, stepped⟩

/-- **A cleared batch carries a Cert-F certificate.** The fills read off the
admitted transfers, with the clearer's dual, certify the batch LP at the
clearing price within the market's `ε`. -/
theorem clear_certified {world next : World} {height : Nat} {inst : InstanceId} {market : Market}
    {transfers : List Transfer} {certificate : Certificate}
    (cleared : clear world height inst market transfers certificate = .ok next) :
    Certified (lpOf market (batchOrders world inst market) certificate.price)
      (fills market (batchOrders world inst market) transfers) certificate.π
      (certificate.s (batchOrders world inst market).length) :=
  (judge_spec (clear_spec cleared).1).2.2

/-- **ε-optimality.** No feasible allocation of the batch at the clearing price
(fractional or all-or-nothing) trades more than the cleared one plus `ε`. -/
theorem clear_epsilon_optimal {world next : World} {height : Nat} {inst : InstanceId} {market : Market}
    {transfers : List Transfer} {certificate : Certificate}
    (cleared : clear world height inst market transfers certificate = .ok next)
    {other : Fin (batchOrders world inst market).length → Int}
    (feasible : PrimalFeasible (lpOf market (batchOrders world inst market) certificate.price) other) :
    (lpOf market (batchOrders world inst market) certificate.price).w ⬝ᵥ other ≤
      (lpOf market (batchOrders world inst market) certificate.price).w ⬝ᵥ
        fills market (batchOrders world inst market) transfers + market.epsilon :=
  certifies_epsilon_optimal _ (clear_certified cleared) feasible

/-- **One price.** Every order of the batch paid or received exactly the
clearing price per unit of goods it traded. -/
theorem clear_uniform_price {world next : World} {height : Nat} {inst : InstanceId} {market : Market}
    {transfers : List Transfer} {certificate : Certificate}
    (cleared : clear world height inst market transfers certificate = .ok next) :
    ∀ order ∈ batchOrders world inst market,
      order.paid market transfers = (certificate.price : Int) * order.fill market transfers :=
  (judge_spec (clear_spec cleared).1).1

/-- **Only crossing orders trade, within their quantity.** An order that traded
any goods crosses the clearing price, and traded at most its quantity. -/
theorem clear_fills_cross {world next : World} {height : Nat} {inst : InstanceId} {market : Market}
    {transfers : List Transfer} {certificate : Certificate}
    (cleared : clear world height inst market transfers certificate = .ok next)
    (edge : Fin (batchOrders world inst market).length)
    (traded : 0 < fills market (batchOrders world inst market) transfers edge) :
    ((batchOrders world inst market).get edge).crosses certificate.price = true ∧
      fills market (batchOrders world inst market) transfers edge ≤
        (((batchOrders world inst market).get edge).qty : Int) := by
  have bound := (clear_certified cleared).1.2.2 edge
  simp only [lpOf] at bound
  split at bound
  · exact ⟨by assumption, bound⟩
  · exact absurd (lt_of_lt_of_le traded bound) (lt_irrefl _)

/-- **Offer safety.** A clearing of an invariant world keeps the invariant, so
every open seat (every order, filled or not) satisfies its offer-safety law in
the settled allocation. -/
theorem clear_inv {world next : World} {height : Nat} {inst : InstanceId} {market : Market}
    {transfers : List Transfer} {certificate : Certificate} (inv : Inv world)
    (cleared : clear world height inst market transfers certificate = .ok next) : Inv next :=
  step_inv inv (clear_spec cleared).2.choose_spec

theorem clear_offer_safe {genesis world next : World} {height : Nat} {inst : InstanceId}
    {market : Market} {transfers : List Transfer} {certificate : Certificate}
    (empty : genesis.seats = []) (reachable : Reachable genesis world)
    (cleared : clear world height inst market transfers certificate = .ok next) :
    ∀ seat ∈ next.seats, seat.isOpen = true → safeAt next.book seat.account seat.proposal = true :=
  seat_offer_safe_forever empty (Reachable.admit height _ _ reachable (clear_spec cleared).2.choose_spec)

/-- **Conservation.** A clearing conserves every asset of the Book. -/
theorem clear_conserves {world next : World} {height : Nat} {inst : InstanceId} {market : Market}
    {transfers : List Transfer} {certificate : Certificate}
    (cleared : clear world height inst market transfers certificate = .ok next) (asset : AssetId) :
    next.book.totalAsset asset = world.book.totalAsset asset :=
  seat_conserves (clear_spec cleared).2.choose_spec asset

/-- **Refusal.** A proposal whose fills and dual are not a Cert-F certificate of
the batch LP within `ε` is refused, whatever offer safety would say. -/
theorem uncertified_refused {world : World} {height : Nat} {inst : InstanceId} {market : Market}
    {transfers : List Transfer} {certificate : Certificate}
    (uncertified : ¬ Certified (lpOf market (batchOrders world inst market) certificate.price)
      (fills market (batchOrders world inst market) transfers) certificate.π
      (certificate.s (batchOrders world inst market).length)) :
    ∃ reason, clear world height inst market transfers certificate = .error reason := by
  cases h : clear world height inst market transfers certificate with
  | error reason => exact ⟨reason, rfl⟩
  | ok next => exact absurd (clear_certified h) uncertified

/-- In particular, a feasible primal and dual whose gap exceeds `ε` are refused. -/
theorem gap_exceeding_refused {world : World} {height : Nat} {inst : InstanceId} {market : Market}
    {transfers : List Transfer} {certificate : Certificate}
    (exceeds : market.epsilon < gap (lpOf market (batchOrders world inst market) certificate.price)
      (fills market (batchOrders world inst market) transfers)
      (certificate.s (batchOrders world inst market).length)) :
    ∃ reason, clear world height inst market transfers certificate = .error reason :=
  uncertified_refused fun certified => absurd certified.2.2 (not_le.mpr exceeds)

#assert_axioms judge_spec clear_spec clear_certified clear_epsilon_optimal clear_uniform_price
  clear_fills_cross clear_inv clear_offer_safe clear_conserves uncertified_refused gap_exceeding_refused

/-! ## Inhabitants and teeth

A two-sided batch at price 4. Bids: Alice wants 2 G for at most 10 C, Bob wants
3 G for at most 12 C. Asks: Carol sells 2 G for at least 6 C, Dave sells 3 G for
at least 12 C. Every order crosses at 4; the whole book clears: 5 G change
hands for 20 C. -/

namespace Example
open Minidregg.Kernel.Invitations
open Minidregg.Pred (Pred)
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)

def G : AssetId := 100
def C : AssetId := 200
def market : Market := ⟨C, G, 0⟩
def marketAt (epsilon : Nat) : Market := { market with epsilon := epsilon }

def alice : SubjectId := ⟨1⟩
def bob : SubjectId := ⟨2⟩
def carol : SubjectId := ⟨3⟩
def dave : SubjectId := ⟨4⟩
def aliceAccount : AccountId := 10
def bobAccount : AccountId := 20
def carolAccount : AccountId := 30
def daveAccount : AccountId := 40
def aliceSeat : AccountId := reservedBase + 51
def bobSeat : AccountId := reservedBase + 52
def carolSeat : AccountId := reservedBase + 53
def daveSeat : AccountId := reservedBase + 54
def package : Digest := ⟨88⟩

def genesisBook : Book where
  accounts := {aliceAccount, bobAccount, carolAccount, daveAccount}
  balances := DFinsupp.single (aliceAccount, C) 10 + DFinsupp.single (bobAccount, C) 12 +
    DFinsupp.single (carolAccount, G) 2 + DFinsupp.single (daveAccount, G) 3
  leaseRecords := 0

def genesis : World := ⟨genesisBook, ⟨[], [], [], []⟩, []⟩

def drex : Instance := ⟨1, package, Pred.all []⟩

def aliceBid : Proposal := ⟨[(C, 10)], [(G, 2)], .onDemand⟩
def bobBid : Proposal := ⟨[(C, 12)], [(G, 3)], .onDemand⟩
def carolAsk : Proposal := ⟨[(G, 2)], [(C, 6)], .onDemand⟩
def daveAsk : Proposal := ⟨[(G, 3)], [(C, 12)], .onDemand⟩

/-- The window: the instance, its method minting four invitations (ids 1-4,
`Seats.Example.mintIds`), four orders. -/
def window : List Seats.Example.Entry :=
  [ .signed 1 alice (.create drex),
    .method 1 drex [.mint "bid" [] alice, .mint "bid" [] bob, .mint "ask" [] carol, .mint "ask" [] dave],
    .signed 2 alice (.offer 1 ⟨1, package, "bid"⟩ aliceSeat aliceAccount aliceAccount aliceBid none),
    .signed 3 bob (.offer 2 ⟨1, package, "bid"⟩ bobSeat bobAccount bobAccount bobBid none),
    .signed 4 carol (.offer 3 ⟨1, package, "ask"⟩ carolSeat carolAccount carolAccount carolAsk none),
    .signed 5 dave (.offer 4 ⟨1, package, "ask"⟩ daveSeat daveAccount daveAccount daveAsk none) ]

def opened : World :=
  match Seats.Example.run genesis window with
  | .ok world => world
  | .error _ => genesis

/-- The batch's orders, by seat account. -/
def book : List Order :=
  [⟨aliceSeat, .bid, 2, 10⟩, ⟨bobSeat, .bid, 3, 12⟩, ⟨carolSeat, .ask, 2, 6⟩, ⟨daveSeat, .ask, 3, 12⟩]

theorem opened_orders : batchOrders opened 1 market = book := by
  decide +kernel

/-- The whole book at price 4: Carol's 2 G to Alice, Dave's 3 G to Bob, 8 C and
12 C back. These are exactly the moves `world/drex/DrexBatch.obend` routes from
the fills `(2, 3, 2, 3)` (its preview row `DrexRoutesFullBook`). -/
def fullClearing : List Transfer :=
  [⟨carolSeat, aliceSeat, G, 2⟩, ⟨aliceSeat, carolSeat, C, 8⟩,
   ⟨daveSeat, bobSeat, G, 3⟩, ⟨bobSeat, daveSeat, C, 12⟩]

/-- The dual: `π = (0, 1)`, slack 0 on each bid, 2 on each ask: `cᵀs = 10 = wᵀf`. -/
def honest : Certificate := ⟨4, (0, 1), [0, 0, 2, 2]⟩

def balances (world : World) : List Int :=
  [aliceAccount, bobAccount, carolAccount, daveAccount].flatMap fun account =>
    [world.book.balance account G, world.book.balance account C]

def clearThenExit (transfers : List Transfer) (certificate : Certificate) (epsilon : Nat) :
    Except Refusal (List Int) :=
  match clear opened 6 1 (marketAt epsilon) transfers certificate with
  | .error reason => .error reason
  | .ok cleared =>
    match Seats.Example.run cleared
        [.signed 7 alice (.exit aliceSeat), .signed 7 bob (.exit bobSeat),
         .signed 7 carol (.exit carolSeat), .signed 7 dave (.exit daveSeat)] with
    | .error reason => .error (.seat reason)
    | .ok closed => .ok (balances closed)

/-- **The two-sided batch settles.** Alice ends with 2 G and 2 C (her bid
cleared below its limit), Bob with 3 G, Carol with 8 C, Dave with 12 C. -/
theorem batch_settles : clearThenExit fullClearing honest 0 = .ok [2, 2, 3, 0, 0, 8, 0, 12] := by
  decide +kernel

theorem honest_certified :
    Certified (lpOf market book 4) (fills market book fullClearing) honest.π (honest.s book.length) := by
  decide +kernel

/-- Only Alice and Carol trade: crossed but suboptimal (2 G of a possible 5). -/
def partialClearing : List Transfer := [⟨carolSeat, aliceSeat, G, 2⟩, ⟨aliceSeat, carolSeat, C, 8⟩]

/-- **The tooth.** Offer safety alone admits the suboptimal allocation: both
touched seats are satisfied and the others untouched. -/
theorem suboptimal_passes_offer_safety :
    (step opened 6 (.inst 1) (.reallocate 1 partialClearing)).toBool = true := by
  decide +kernel

/-- **The certificate refuses it**: with the honest dual its gap is 6 > ε = 0. -/
theorem suboptimal_refused :
    (clear opened 6 1 market partialClearing honest).map balances = .error (.uncertified 6 0) := by
  decide +kernel

/-- And no dual at all certifies it at `ε = 0`: the full clearing is feasible and
trades 6 more. -/
theorem suboptimal_not_certifiable (π : Fin 2 → Int) (s : Fin book.length → Int) :
    ¬ Certified (lpOf market book 4) (fills market book partialClearing) π s := by
  intro certified
  have feasible : PrimalFeasible (lpOf market book 4) ![2, 3, 2, 3] := by
    decide +kernel
  have bound := certifies_epsilon_optimal _ certified feasible
  revert bound
  decide +kernel

/-- The boundary in the other polarity: at `ε = 6` the same proposal is a
certificate, and the partial batch settles. -/
theorem suboptimal_admitted_at_six :
    clearThenExit partialClearing honest 6 = .ok [2, 2, 0, 12, 0, 8, 3, 0] := by
  decide +kernel

/-- **A forged dual is refused.** Zero slacks claim a gap of `-10`, below any
`ε`, but are not dual-feasible. -/
theorem forged_dual_refused :
    (clear opened 6 1 market fullClearing ⟨4, (0, 0), [0, 0, 0, 0]⟩).map balances =
      .error (.uncertified (-10) 0) := by
  decide +kernel

/-- **One price.** Alice paying her whole budget (10 C for 2 G) is offer-safe
for both seats, and refused as not uniform at price 4. -/
def unevenClearing : List Transfer :=
  [⟨carolSeat, aliceSeat, G, 2⟩, ⟨aliceSeat, carolSeat, C, 10⟩,
   ⟨daveSeat, bobSeat, G, 3⟩, ⟨bobSeat, daveSeat, C, 12⟩]

theorem uneven_passes_offer_safety :
    (step opened 6 (.inst 1) (.reallocate 1 unevenClearing)).toBool = true := by
  decide +kernel

theorem uneven_refused :
    (clear opened 6 1 market unevenClearing honest).map balances = .error (.notUniform aliceSeat) := by
  decide +kernel

/-- **A price above a bid's limit.** At 5 Bob's bid does not cross (15 > 12):
his fill exceeds his capacity 0, and the certificate is refused before the Book
would refuse his unfunded payment. -/
theorem over_limit_refused :
    ((clear opened 6 1 market
      [⟨carolSeat, aliceSeat, G, 2⟩, ⟨aliceSeat, carolSeat, C, 10⟩,
       ⟨daveSeat, bobSeat, G, 3⟩, ⟨bobSeat, daveSeat, C, 15⟩] ⟨5, (0, 1), [0, 0, 2, 2]⟩).map balances).toBool =
      false := by
  decide +kernel

/-- **Abort returns the deposits.** When no certified clearing comes, every
order's offerer exits, and every Book account is back at genesis. -/
theorem abort_returns_deposits :
    (Seats.Example.run opened
      [.signed 7 alice (.exit aliceSeat), .signed 7 bob (.exit bobSeat),
       .signed 7 carol (.exit carolSeat), .signed 7 dave (.exit daveSeat)]).map balances =
      .ok (balances genesis) := by
  decide +kernel

theorem genesis_balances : balances genesis = [0, 10, 0, 12, 2, 0, 3, 0] := by decide +kernel

/-- **The integrality gap.** Bob alone (3 G) against Carol (2 G) cannot trade
all-or-nothing, while the LP relaxation trades 2: refused at `ε = 0` with the
honest dual; with no transfers at all the certificate holds at `ε = 4`. -/
def thinWindow : List Seats.Example.Entry :=
  [ .signed 1 alice (.create drex),
    .method 1 drex [.mint "bid" [] bob, .mint "ask" [] carol],
    .signed 3 bob (.offer 1 ⟨1, package, "bid"⟩ bobSeat bobAccount bobAccount bobBid none),
    .signed 4 carol (.offer 2 ⟨1, package, "ask"⟩ carolSeat carolAccount carolAccount carolAsk none) ]

def thin : World :=
  match Seats.Example.run genesis thinWindow with
  | .ok world => world
  | .error _ => genesis

theorem integrality_gap_refused_at_zero :
    (clear thin 6 1 market [] ⟨4, (0, 1), [0, 2]⟩).map balances = .error (.uncertified 4 0) := by
  decide +kernel

theorem integrality_gap_admitted_at_four :
    ((clear thin 6 1 (marketAt 4) [] ⟨4, (0, 1), [0, 2]⟩).map balances).toBool = true := by
  decide +kernel

theorem window_runs : (Seats.Example.run genesis window).toBool = true := by decide +kernel

/-- The premises of `clear_offer_safe` are inhabited: the window is reachable
from a seatless genesis, and the full clearing is admitted there. -/
theorem window_reachable : Reachable genesis opened := by
  unfold opened
  split
  · rename_i world ran
    exact Seats.Example.run_reachable Reachable.start ran
  · rename_i reason ran
    have runs := window_runs
    rw [ran] at runs
    simp [Except.toBool] at runs

theorem full_clearing_admitted : (clear opened 6 1 market fullClearing honest).toBool = true := by
  decide +kernel

theorem full_clearing_offer_safe {next : World} (cleared : clear opened 6 1 market fullClearing honest = .ok next) :
    ∀ seat ∈ next.seats, seat.isOpen = true → safeAt next.book seat.account seat.proposal = true :=
  clear_offer_safe rfl window_reachable cleared

#assert_axioms opened_orders batch_settles honest_certified suboptimal_passes_offer_safety
  suboptimal_refused suboptimal_not_certifiable suboptimal_admitted_at_six forged_dual_refused
  uneven_passes_offer_safety uneven_refused over_limit_refused abort_returns_deposits genesis_balances
  integrality_gap_refused_at_zero integrality_gap_admitted_at_four window_runs window_reachable
  full_clearing_admitted full_clearing_offer_safe

end Example

end Minidregg.Kernel.CertifiedClearing
