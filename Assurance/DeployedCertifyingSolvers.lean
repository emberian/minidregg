/-
# Assurance.DeployedCertifyingSolvers -- `CertifiedClearing` (`Cert-F`) & `Pred.hashEq` Certifying-Checker Assurance

This module establishes the end-to-end soundness and computable verification of Mini's two
deployed certifying checkers:

1. **`CertifiedClearing` (`Cert-F`) & `SeatStore.decodeAction` bridge**:
   - Proves that `SeatStore.decodeAction` on a `.variant "clear"` record — including both the
     explicit-market format and the inferred-market path when `"market"` is omitted (as in
     `world/drex/DrexBatch.obend` `Action.clear({moves, certificate})`) — produces a
     `PlanAction.clear` whose acceptance by `CertifiedClearing.judge` / `CertifiedClearing.clear`
     / `SeatStore.stepCertifiedPlan` implies:
     * **Exact asset conservation**: world-book total asset invariance across all accounts/seats
       (`next.book.totalAsset asset = world.book.totalAsset asset`) and LP net flow conservation
       (`(lpOf market orders cert.price).A *ᵥ fills market orders transfers = 0`),
     * **Uniform price & price improvement**: uniform execution pricing across all orders
       (`order.paid market transfers = cert.price * order.fill market transfers`), and limit-price
       respect (`order.crosses cert.price = true` and `fill ≤ qty` for every traded order),
     * **Dual feasibility**: `DualFeasible (lpOf market orders cert.price) cert.π (cert.s orders.length)`,
     * **Bounded complementary slackness (`ε`-optimality)**:
       `gap (lpOf market orders cert.price) (fills market orders transfers) (cert.s orders.length) ≤ market.epsilon`,
       establishing `ε`-optimality (`certifies_epsilon_optimal`) against every feasible clearing
       of the batch.

2. **`Pred.hashEq` with `Pred.HashEqDigest.deployed` (`cSHAKE256("DREGG.PRED.HASHEQ/v2")`)**:
   - Proves that `Pred.eval` on `Pred.hashEq fields saltField digestField` rejects (`= false`)
     any state write where the committed digest at `digestField` does not equal the
     `cSHAKE256("DREGG.PRED.HASHEQ/v2")` digest of `(objectId, fields, saltField, digestField,
     fieldValues, salt)`, and binds any two accepted reveals at the same digest to identical
     `(objectId, fieldValues, salt)` up to a concrete `cSHAKE256("DREGG.PRED.HASHEQ/v2")`
     collision.

3. **Computable Positive & Negative Audit (`checkCertifyingSolversAudit`)**:
   - Verifies `Cert-F` acceptance (explicit and inferred market), conservation violation
     rejection, complementary-slackness / dual violation rejection, `Pred.hashEq` valid opening
     acceptance, and forged reveal rejection.
-/
import Kernel.CertifiedClearing
import Kernel.SeatStore
import Pred.HashEq
import Pred.HashEqDigest
import Theory.AssertAxioms

namespace Minidregg.Assurance.DeployedCertifyingSolvers

open Minidregg.Theory
open Minidregg.Theory.CanonicalResourceKernel (Book Batch Operation AccountId AssetId)
open Minidregg.Theory.CertF
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Theory.HashBytes (ofBE be CollisionAmong)
open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Kernel
open Minidregg.Kernel.Invitations
open Minidregg.Kernel.Seats (Transfer World safeAt)
open Minidregg.Kernel.CertifiedClearing
open Minidregg.Kernel.SeatStore
open Minidregg.Pred
open Minidregg.Pred.HashEqDigest
open Matrix

set_option autoImplicit false

/-! ## §1. `SeatStore.decodeMarket` and `SeatStore.decodeAction` on `.variant "clear"` -/

/-- When `"market"` is omitted (`ObjectiveActivity.fieldOf fields "market" = none`) and top-level
`"currency"` is also omitted (`natField fields "currency" = none`, as in
`world/drex/DrexBatch.obend` `Action.clear({moves, certificate})`), `SeatStore.decodeMarket` on
`t1 :: t2 :: rest` infers `⟨t1.asset, t2.asset, (natField fields "epsilon").getD 0⟩`. -/
theorem decodeMarket_inferred
    (fields : List (String × Data))
    (t1 t2 : Transfer) (rest : List Transfer)
    (hNoMarket : ObjectiveActivity.fieldOf fields "market" = none)
    (hNoCurrency : natField fields "currency" = none) :
    decodeMarket fields (t1 :: t2 :: rest) =
      some ⟨t1.asset, t2.asset, (natField fields "epsilon").getD 0⟩ := by
  simp [decodeMarket, hNoMarket, hNoCurrency, Option.orElse]

/-- Explicit-market decoding: when `"market"` is a record carrying `"currency"` and `"goods"`,
`SeatStore.decodeMarket` produces `some ⟨currency, goods, (natField mfields "epsilon").getD 0⟩`. -/
theorem decodeMarket_explicit
    (fields mfields : List (String × Data))
    (moves : List Transfer) (currency goods : Nat)
    (hMarket : ObjectiveActivity.fieldOf fields "market" = some (.record mfields))
    (hCurrency : natField mfields "currency" = some currency)
    (hGoods : natField mfields "goods" = some goods) :
    decodeMarket fields moves =
      some ⟨currency, goods, (natField mfields "epsilon").getD 0⟩ := by
  simp [decodeMarket, hMarket, hCurrency, hGoods]

/-- Characterization of `SeatStore.decodeAction` on `.variant "clear" (.record fields)`. -/
theorem decodeAction_clear_iff
    (fuel : Nat) (fields : List (String × Data)) (action : SeatStore.PlanAction) :
    decodeAction fuel (.variant "clear" (.record fields)) = some action ↔
      ∃ movesData moves certData cert market,
        ObjectiveActivity.fieldOf fields "moves" = some movesData ∧
        decodeList decodeTransfer fuel movesData = some moves ∧
        ObjectiveActivity.fieldOf fields "certificate" = some certData ∧
        decodeCertificate fuel certData = some cert ∧
        decodeMarket fields moves = some market ∧
        action = .clear market moves cert := by
  simp only [decodeAction, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq]
  constructor
  · rintro ⟨movesData, h1, moves, h2, certData, h3, cert, h4, market, h5, rfl⟩
    exact ⟨movesData, moves, certData, cert, market, h1, h2, h3, h4, h5, rfl⟩
  · rintro ⟨movesData, moves, certData, cert, market, h1, h2, h3, h4, h5, rfl⟩
    exact ⟨movesData, h1, moves, h2, certData, h3, cert, h4, market, h5, rfl⟩

/-- On the inferred-market path (`ObjectiveActivity.fieldOf fields "market" = none` and
`natField fields "currency" = none`, as in `world/drex/DrexBatch.obend`), `SeatStore.decodeAction`
on `.variant "clear"` produces
`some (.clear ⟨t1.asset, t2.asset, (natField fields "epsilon").getD 0⟩ (t1 :: t2 :: rest) cert)`. -/
theorem decodeAction_clear_inferred
    (fuel : Nat) (fields : List (String × Data))
    (movesData certData : Data)
    (t1 t2 : Transfer) (rest : List Transfer)
    (cert : Certificate)
    (hMovesData : ObjectiveActivity.fieldOf fields "moves" = some movesData)
    (hMoves : decodeList decodeTransfer fuel movesData = some (t1 :: t2 :: rest))
    (hCertData : ObjectiveActivity.fieldOf fields "certificate" = some certData)
    (hCert : decodeCertificate fuel certData = some cert)
    (hNoMarket : ObjectiveActivity.fieldOf fields "market" = none)
    (hNoCurrency : natField fields "currency" = none) :
    decodeAction fuel (.variant "clear" (.record fields)) =
      some (.clear ⟨t1.asset, t2.asset, (natField fields "epsilon").getD 0⟩
        (t1 :: t2 :: rest) cert) := by
  rw [decodeAction_clear_iff]
  exact ⟨movesData, t1 :: t2 :: rest, certData, cert,
    ⟨t1.asset, t2.asset, (natField fields "epsilon").getD 0⟩,
    hMovesData, hMoves, hCertData, hCert,
    decodeMarket_inferred fields t1 t2 rest hNoMarket hNoCurrency, rfl⟩

/-! ## §2. `CertifiedClearing` (`Cert-F`) Soundness Bridge -/

/-- `verifyClearing` alias for the deterministic primal-dual clearing checker
`CertifiedClearing.judge`. -/
abbrev verifyClearing := CertifiedClearing.judge

/-- **Soundness of `CertifiedClearing.judge` (`verifyClearing`)**:
When `verifyClearing market orders transfers cert = .ok ()`, the clearing satisfies:
1. Uniform fill pricing (`order.paid market transfers = cert.price * order.fill market transfers`),
2. Order-book confinement (`isOrderAccount orders t.source ∧ isOrderAccount orders t.destination`),
3. Primal feasibility (`PrimalFeasible`), including exact LP flow conservation
   (`(lpOf market orders cert.price).A *ᵥ fills market orders transfers = 0`) and capacity bounds
   (`0 ≤ fills ≤ c`),
4. Dual feasibility (`DualFeasible (lpOf market orders cert.price) cert.π (cert.s orders.length)`),
5. Bounded complementary slackness (`gap ≤ market.epsilon`), and
6. `ε`-optimality against every primal-feasible fill vector `other`. -/
theorem verifyClearing_sound
    {market : Market} {orders : List Order} {transfers : List Transfer} {cert : Certificate}
    (h : verifyClearing market orders transfers cert = .ok ()) :
    let lp := lpOf market orders cert.price
    let f := fills market orders transfers
    let s := cert.s orders.length
    (∀ order ∈ orders, order.paid market transfers = (cert.price : Int) * order.fill market transfers) ∧
    (∀ transfer ∈ transfers,
      isOrderAccount orders transfer.source = true ∧
      isOrderAccount orders transfer.destination = true) ∧
    PrimalFeasible lp f ∧
    lp.A *ᵥ f = 0 ∧
    DualFeasible lp cert.π s ∧
    gap lp f s ≤ (market.epsilon : Int) ∧
    (∀ other, PrimalFeasible lp other → lp.w ⬝ᵥ other ≤ lp.w ⬝ᵥ f + (market.epsilon : Int)) := by
  obtain ⟨hunif, horders, hcert⟩ := judge_spec h
  exact ⟨hunif, horders, hcert.1, hcert.1.1, hcert.2.1, hcert.2.2,
    fun other hfeas => certifies_epsilon_optimal _ hcert hfeas⟩

/-- **End-to-end `SeatStore.decodeAction` + `stepCertifiedPlan` (`Cert-F`) soundness**:
Whenever a `.variant "clear"` record decodes via `SeatStore.decodeAction` to `action` and
`SeatStore.stepCertifiedPlan height inst mintId world index action = .ok (next, batch)`,
the action is a `.clear market transfers cert` and the transition guarantees:
1. **Exact asset conservation**: `∀ asset, next.book.totalAsset asset = world.book.totalAsset asset`
   and `Inv next` (when `Inv world`), plus LP flow conservation `A *ᵥ f = 0`,
2. **Uniform price & price improvement**:
   `∀ order ∈ batchOrders world inst.id market, order.paid market transfers = cert.price * order.fill market transfers`,
   and for every traded order (`0 < fills ... edge`), `(orders.get edge).crosses cert.price = true`
   and `fills ... edge ≤ (orders.get edge).qty`,
3. **Dual feasibility**: `DualFeasible (lpOf market orders cert.price) cert.π (cert.s orders.length)`, and
4. **Bounded complementary slackness (`gap ≤ ε`) & `ε`-optimality** over all feasible clearings
   of the batch. -/
theorem decoded_clear_action_sound
    {fuel height index : Nat} {fields : List (String × Data)}
    {action : SeatStore.PlanAction} {inst : Instance} {mintId : Nat → InvitationId}
    {world next : World} {batch : Batch}
    (hDecode : decodeAction fuel (.variant "clear" (.record fields)) = some action)
    (hStep : stepCertifiedPlan height inst mintId world index action = .ok (next, batch)) :
    ∃ market transfers cert,
      let orders := batchOrders world inst.id market
      let lp := lpOf market orders cert.price
      let f := fills market orders transfers
      let s := cert.s orders.length
      action = .clear market transfers cert ∧
      CertifiedClearing.clear world height inst.id market transfers cert = .ok next ∧
      (∀ asset, next.book.totalAsset asset = world.book.totalAsset asset) ∧
      (Seats.Inv world → Seats.Inv next) ∧
      (∀ order ∈ orders,
        order.paid market transfers = (cert.price : Int) * order.fill market transfers) ∧
      (∀ edge : Fin orders.length, 0 < f edge →
        (orders.get edge).crosses cert.price = true ∧ f edge ≤ ((orders.get edge).qty : Int)) ∧
      PrimalFeasible lp f ∧
      lp.A *ᵥ f = 0 ∧
      DualFeasible lp cert.π s ∧
      gap lp f s ≤ (market.epsilon : Int) ∧
      (∀ other, PrimalFeasible lp other → lp.w ⬝ᵥ other ≤ lp.w ⬝ᵥ f + (market.epsilon : Int)) := by
  obtain ⟨_, moves, _, cert, market, -, -, -, -, -, rfl⟩ :=
    (decodeAction_clear_iff fuel fields action).mp hDecode
  have hClear : CertifiedClearing.clear world height inst.id market moves cert = .ok next :=
    stepCertifiedPlan_clear hStep
  have hCert := clear_certified hClear
  exact ⟨market, moves, cert, rfl, hClear,
    clear_conserves hClear,
    fun hinv => clear_inv hinv hClear,
    clear_uniform_price hClear,
    fun edge hpos => clear_fills_cross hClear edge hpos,
    hCert.1,
    hCert.1.1,
    hCert.2.1,
    hCert.2.2,
    fun other hfeas => clear_epsilon_optimal hClear hfeas⟩

/-! ## §3. `Pred.hashEq` with `Pred.HashEqDigest.deployed` (`cSHAKE256("DREGG.PRED.HASHEQ/v2")`) -/

/-- `Pred.HashEqDigest.customization` is the UTF-8 byte list of `"DREGG.PRED.HASHEQ/v2"`. -/
theorem hashEq_customization_eq :
    Pred.HashEqDigest.customization = utf8 "DREGG.PRED.HASHEQ/v2" :=
  rfl

/-- `Pred.HashEqDigest.digestWith Pred.HashEqDigest.deployed o` computes the 256-bit big-endian
integer of `cSHAKE256("DREGG.PRED.HASHEQ/v2", o.preimage)`. -/
theorem hashEq_deployed_cshake256_image (o : Opening) :
    digestWith deployed o =
      (ofBE (cshake256Bytes Pred.HashEqDigest.customization o.preimage) : Int) := by
  unfold digestWith
  rw [deployed_eq_cshake256Bytes]

/-- **Certifying rejection of mismatched `cSHAKE256("DREGG.PRED.HASHEQ/v2")` digest**:
`Pred.eval` on `Pred.hashEq fields saltField digestField` rejects (`= false`) any state write
where the committed digest at `digestField` does not equal the `cSHAKE256("DREGG.PRED.HASHEQ/v2")`
digest of the state's opening `(objectId, fields, saltField, digestField, fieldValues, salt)`. -/
theorem hashEq_rejects_mismatched_digest
    (fields : List Pred.Slot) (saltField digestField : Pred.Slot)
    (old new : Pred.State)
    (hMismatch : ∀ (objectId : Int) (fieldValues : List Int) (salt : Int),
      new.get hashEqCellSlot = some objectId →
      new.getAll fields = some fieldValues →
      new.get saltField = some salt →
      (⟨objectId, fields, saltField, digestField, fieldValues, salt⟩ : Opening).Admissible →
      new.get digestField ≠
        some (digestWith deployed ⟨objectId, fields, saltField, digestField, fieldValues, salt⟩)) :
    Pred.eval (.hashEq fields saltField digestField) old new = false := by
  cases heval : Pred.eval (.hashEq fields saltField digestField) old new with
  | false => rfl
  | true =>
    obtain ⟨cell, xs, r, hcell, hvals, hsalt, hadm, hcommit⟩ :=
      (Pred.hashEq_sound fields saltField digestField old new).mp heval
    exact absurd hcommit (hMismatch cell xs r hcell hvals hsalt hadm)

/-- Specialization of `hashEq_rejects_mismatched_digest` to a state whose `(objectId, fieldValues, salt)`
reads are given explicitly: if `new.get digestField` is not `some (digestWith deployed o)`,
`Pred.eval (.hashEq fields saltField digestField) old new = false`. -/
theorem hashEq_rejects_wrong_commit_value
    (fields : List Pred.Slot) (saltField digestField : Pred.Slot)
    (old new : Pred.State)
    (objectId : Int) (fieldValues : List Int) (salt : Int)
    (hObj : new.get hashEqCellSlot = some objectId)
    (hVals : new.getAll fields = some fieldValues)
    (hSalt : new.get saltField = some salt)
    (hMismatch : new.get digestField ≠
      some (digestWith deployed ⟨objectId, fields, saltField, digestField, fieldValues, salt⟩)) :
    Pred.eval (.hashEq fields saltField digestField) old new = false := by
  apply hashEq_rejects_mismatched_digest fields saltField digestField old new
  intro cell xs r hcell hvals hsalt _
  rw [hObj] at hcell; cases hcell
  rw [hVals] at hvals; cases hvals
  rw [hSalt] at hsalt; cases hsalt
  exact hMismatch

/-- **Concrete binding up to `cSHAKE256("DREGG.PRED.HASHEQ/v2")` collision**:
If two state writes `new` and `new'` both pass `Pred.eval (.hashEq fields saltField digestField)`
with the same committed digest at `digestField`, then either they open the exact same
`(objectId, fieldValues, salt)` tuple or their canonical opening preimages collide under
`Pred.HashEqDigest.deployed` (`cSHAKE256("DREGG.PRED.HASHEQ/v2")`). -/
theorem hashEq_concrete_binding
    {fields : List Pred.Slot} {saltField digestField : Pred.Slot}
    {old new old' new' : Pred.State}
    (h : Pred.eval (.hashEq fields saltField digestField) old new = true)
    (h' : Pred.eval (.hashEq fields saltField digestField) old' new' = true)
    (sameCommit : new.get digestField = new'.get digestField) :
    (new.get hashEqCellSlot = new'.get hashEqCellSlot ∧
      new.getAll fields = new'.getAll fields ∧
      new.get saltField = new'.get saltField) ∨
      CollisionAmong deployed (fun x =>
        ∃ o, (hashEqOpening new fields saltField digestField = some o ∨
          hashEqOpening new' fields saltField digestField = some o) ∧ x = o.preimage) := by
  rcases Pred.hashEq_binds_or_collides h h' sameCommit with ⟨o, ho, ho'⟩ | hcol
  · obtain ⟨hcell, hvals, hsalt, -⟩ := hashEqOpening_eq_some.mp ho
    obtain ⟨hcell', hvals', hsalt', -⟩ := hashEqOpening_eq_some.mp ho'
    exact .inl ⟨by rw [hcell, hcell'], by rw [hvals, hvals'], by rw [hsalt, hsalt']⟩
  · exact .inr hcol

/-! ## §4. Computable Audit Fixtures & Positive/Negative Test Vectors -/

/-- Encode a list of `Data` items using `ObjectiveBendDemandData`'s `.variant "nil"` / `"cons"`
representation for `SeatStore.decodeList`. -/
def encodeDataList : List Data → Data
  | [] => .variant "nil" (.record [])
  | h :: t => .variant "cons" (.record [("head", h), ("tail", encodeDataList t)])

/-- Encode a `Seats.Transfer` as a `Data` record for `SeatStore.decodeTransfer`. -/
def encodeTransferData (t : Transfer) : Data :=
  .record
    [ ("source", .natural t.source)
    , ("destination", .natural t.destination)
    , ("asset", .natural t.asset)
    , ("amount", .natural t.amount) ]

/-- Encode a `CertifiedClearing.Certificate` as a `Data` record for `SeatStore.decodeCertificate`. -/
def encodeCertificateData (price bidPotential askPotential : Nat) (slacks : List Nat) : Data :=
  .record
    [ ("price", .natural price)
    , ("bidPotential", .natural bidPotential)
    , ("askPotential", .natural askPotential)
    , ("slacks", encodeDataList (slacks.map Data.natural)) ]

/-- The 4-transfer full clearing of `CertifiedClearing.Example` ordered with currency (`C`) first
and goods (`G`) second so `decodeMarket` infers `⟨C, G, 0⟩ = Example.market` when `"market"` is
omitted. -/
def exampleInferredTransfers : List Transfer :=
  [ ⟨Example.aliceSeat, Example.carolSeat, Example.C, 8⟩
  , ⟨Example.carolSeat, Example.aliceSeat, Example.G, 2⟩
  , ⟨Example.bobSeat, Example.daveSeat, Example.C, 12⟩
  , ⟨Example.daveSeat, Example.bobSeat, Example.G, 3⟩ ]

/-- Valid certificate `Data` for `CertifiedClearing.Example.honest` (`price = 4`,
`potentials = (0, 1)`, `slacks = [0, 0, 2, 2]`). -/
def exampleHonestCertData : Data :=
  encodeCertificateData 4 0 1 [0, 0, 2, 2]

/-- Explicit-market `.variant "clear"` action `Data` for `Example.fullClearing`. -/
def exampleClearExplicitData : Data :=
  .variant "clear" (.record
    [ ("market", .record
        [ ("currency", .natural Example.C)
        , ("goods", .natural Example.G)
        , ("epsilon", .natural 0) ])
    , ("moves", encodeDataList (Example.fullClearing.map encodeTransferData))
    , ("certificate", exampleHonestCertData) ])

/-- Inferred-market (`DrexBatch.obend` style, `"market"` omitted) `.variant "clear"` action
`Data` for `exampleInferredTransfers`. -/
def exampleClearInferredData : Data :=
  .variant "clear" (.record
    [ ("moves", encodeDataList (exampleInferredTransfers.map encodeTransferData))
    , ("certificate", exampleHonestCertData) ])

/-- Unbooked transfer (account `999` is not an order seat). -/
def unbookedTransfer : Transfer :=
  ⟨999, Example.aliceSeat, Example.G, 1⟩

/-- Concrete `Pred.HashEqDigest.Opening` for a sealed order reveal on cell `42` with fields
`["order/price", "order/qty"]`, salt slot `"order/salt"`, and commit slot `"order/commit"`. -/
def auditOrderOpening : Opening :=
  { cell := 42
    valueSlots := ["order/price", "order/qty"]
    blinderSlot := "order/salt"
    commitSlot := "order/commit"
    values := [11, 5]
    blinder := 9001 }

/-- Committed `cSHAKE256("DREGG.PRED.HASHEQ/v2")` digest for `auditOrderOpening`. -/
def auditOrderCommitDigest : Int :=
  digestWith deployed auditOrderOpening

/-- Pre-state before reveal (carries only the target cell id and the commitment). -/
def auditOrderOldState : Pred.State :=
  ⟨[ ("request/target", 42)
   , ("order/commit", auditOrderCommitDigest) ]⟩

/-- Honest post-state revealing `order/price = 11`, `order/qty = 5`, `order/salt = 9001`. -/
def auditOrderValidNewState : Pred.State :=
  ⟨[ ("request/target", 42)
   , ("order/price", 11)
   , ("order/qty", 5)
   , ("order/salt", 9001)
   , ("order/commit", auditOrderCommitDigest) ]⟩

/-- The `Pred.hashEq` predicate atom for the sealed order tuple. -/
def auditOrderHashEqPred : Pred :=
  .hashEq ["order/price", "order/qty"] "order/salt" "order/commit"

/-- Computable audit function covering:
1. `Cert-F` clearing acceptance (both explicit market and inferred market when `market` is omitted),
2. `Cert-F` conservation / order-book / uniform-price violation rejection,
3. `Cert-F` complementary slackness / duality gap & dual feasibility violation rejection,
4. `Pred.hashEq` valid opening acceptance under `cSHAKE256("DREGG.PRED.HASHEQ/v2")`, and
5. `Pred.hashEq` forged reveal rejection (tampered price, tampered quantity, tampered salt,
   tampered cell id, tampered commit digest, missing field, and out-of-range blinder). -/
def checkCertifyingSolversAudit : Bool :=
  let fuel := 16
  let expectedExplicit : SeatStore.PlanAction :=
    .clear Example.market Example.fullClearing Example.honest
  let expectedInferred : SeatStore.PlanAction :=
    .clear Example.market exampleInferredTransfers Example.honest
  -- 1. `SeatStore.decodeAction` accepts both explicit-market and inferred-market `.variant "clear"`
  let decodeExplicitOk := decodeAction fuel exampleClearExplicitData == some expectedExplicit
  let decodeInferredOk := decodeAction fuel exampleClearInferredData == some expectedInferred
  -- 2. `CertifiedClearing.clear` and `SeatStore.stepCertifiedPlan` accept both and conserve assets
  let clearExplicitOk :=
    match CertifiedClearing.clear Example.opened 6 1 Example.market
        Example.fullClearing Example.honest with
    | .ok next =>
        next.book.totalAsset Example.G == Example.opened.book.totalAsset Example.G &&
        next.book.totalAsset Example.C == Example.opened.book.totalAsset Example.C
    | .error _ => false
  let stepInferredOk :=
    match stepCertifiedPlan 6 Example.drex (fun i => i + 100) Example.opened 0 expectedInferred with
    | .ok (next, _) =>
        next.book.totalAsset Example.G == Example.opened.book.totalAsset Example.G &&
        next.book.totalAsset Example.C == Example.opened.book.totalAsset Example.C
    | .error _ => false
  -- 3. Conservation / uniform-price / unbooked-seat violation rejection
  let conservationAndUniformRejectOk :=
    -- Unbalanced goods transfer (Carol sends 2 G to Alice, Dave sends 2 G instead of 3 G, Bob pays 8 C,
    -- while Dave's ask requires 12 C for 3 G): rejected by `clear`
    !(CertifiedClearing.clear Example.opened 6 1 Example.market
      [⟨Example.carolSeat, Example.aliceSeat, Example.G, 2⟩,
       ⟨Example.aliceSeat, Example.carolSeat, Example.C, 8⟩,
       ⟨Example.daveSeat, Example.bobSeat, Example.G, 2⟩,
       ⟨Example.bobSeat, Example.daveSeat, Example.C, 8⟩] Example.honest).isOk &&
    -- Non-uniform payment (Alice pays 10 C instead of 8 C at price 4) rejected with `.notUniform`
    (CertifiedClearing.judge Example.market Example.book Example.unevenClearing Example.honest ==
      .error (.notUniform Example.aliceSeat)) &&
    -- Transfer touching a non-order account rejected with `.notAnOrder`
    (CertifiedClearing.judge Example.market Example.book [unbookedTransfer] Example.honest ==
      .error (.notAnOrder unbookedTransfer))
  -- 4. Complementary slackness / duality gap & dual feasibility violation rejection
  let slackRejectOk :=
    -- Suboptimal partial fill has duality gap 6 > epsilon 0
    (CertifiedClearing.judge Example.market Example.book
      Example.partialClearing Example.honest ==
      .error (.uncertified 6 0)) &&
    -- Forged dual slack [0, 0, 0, 0] with zero potentials violates dual feasibility
    (CertifiedClearing.judge Example.market Example.book
      Example.fullClearing ⟨4, (0, 0), [0, 0, 0, 0]⟩ ==
      .error (.uncertified (-10) 0)) &&
    -- Negative dual slack [-1, 0, 2, 2] rejected
    !(CertifiedClearing.judge Example.market Example.book
      Example.fullClearing ⟨4, (0, 1), [-1, 0, 2, 2]⟩).isOk &&
    -- Wrong slack count rejected with `.slackCount 4 2`
    (CertifiedClearing.judge Example.market Example.book
      Example.fullClearing ⟨4, (0, 1), [0, 0]⟩ ==
      .error (.slackCount 4 2))
  -- 5. `Pred.hashEq` valid opening acceptance
  let hashEqAcceptOk :=
    Pred.eval auditOrderHashEqPred auditOrderOldState auditOrderValidNewState
  -- 6. `Pred.hashEq` forged reveal rejection
  let forgedPriceState : Pred.State :=
    ⟨[ ("request/target", 42)
     , ("order/price", 12)
     , ("order/qty", 5)
     , ("order/salt", 9001)
     , ("order/commit", auditOrderCommitDigest) ]⟩
  let forgedQtyState : Pred.State :=
    ⟨[ ("request/target", 42)
     , ("order/price", 11)
     , ("order/qty", 6)
     , ("order/salt", 9001)
     , ("order/commit", auditOrderCommitDigest) ]⟩
  let forgedSaltState : Pred.State :=
    ⟨[ ("request/target", 42)
     , ("order/price", 11)
     , ("order/qty", 5)
     , ("order/salt", 9002)
     , ("order/commit", auditOrderCommitDigest) ]⟩
  let forgedCellState : Pred.State :=
    ⟨[ ("request/target", 43)
     , ("order/price", 11)
     , ("order/qty", 5)
     , ("order/salt", 9001)
     , ("order/commit", auditOrderCommitDigest) ]⟩
  let forgedCommitState : Pred.State :=
    ⟨[ ("request/target", 42)
     , ("order/price", 11)
     , ("order/qty", 5)
     , ("order/salt", 9001)
     , ("order/commit", auditOrderCommitDigest + 1) ]⟩
  let missingQtyState : Pred.State :=
    ⟨[ ("request/target", 42)
     , ("order/price", 11)
     , ("order/salt", 9001)
     , ("order/commit", auditOrderCommitDigest) ]⟩
  let negativeSaltState : Pred.State :=
    ⟨[ ("request/target", 42)
     , ("order/price", 11)
     , ("order/qty", 5)
     , ("order/salt", -1)
     , ("order/commit", auditOrderCommitDigest) ]⟩
  let hashEqRejectOk :=
    !Pred.eval auditOrderHashEqPred auditOrderOldState forgedPriceState &&
    !Pred.eval auditOrderHashEqPred auditOrderOldState forgedQtyState &&
    !Pred.eval auditOrderHashEqPred auditOrderOldState forgedSaltState &&
    !Pred.eval auditOrderHashEqPred auditOrderOldState forgedCellState &&
    !Pred.eval auditOrderHashEqPred auditOrderOldState forgedCommitState &&
    !Pred.eval auditOrderHashEqPred auditOrderOldState missingQtyState &&
    !Pred.eval auditOrderHashEqPred auditOrderOldState negativeSaltState
  decodeExplicitOk &&
  decodeInferredOk &&
  clearExplicitOk &&
  stepInferredOk &&
  conservationAndUniformRejectOk &&
  slackRejectOk &&
  hashEqAcceptOk &&
  hashEqRejectOk

#guard (decodeAction 16 exampleClearExplicitData ==
  some (.clear Example.market Example.fullClearing Example.honest)) = true
#guard (decodeAction 16 exampleClearInferredData ==
  some (.clear Example.market exampleInferredTransfers Example.honest)) = true
#guard (CertifiedClearing.clear Example.opened 6 1 Example.market
  Example.fullClearing Example.honest).isOk = true
#guard (CertifiedClearing.judge Example.market Example.book
  Example.unevenClearing Example.honest == .error (.notUniform Example.aliceSeat)) = true
#guard (CertifiedClearing.judge Example.market Example.book
  Example.partialClearing Example.honest == .error (.uncertified 6 0)) = true
#guard (CertifiedClearing.judge Example.market Example.book
  Example.fullClearing ⟨4, (0, 0), [0, 0, 0, 0]⟩ == .error (.uncertified (-10) 0)) = true
#guard Pred.eval auditOrderHashEqPred auditOrderOldState auditOrderValidNewState = true
#guard Pred.eval auditOrderHashEqPred auditOrderOldState
  ⟨[ ("request/target", 42)
   , ("order/price", 12)
   , ("order/qty", 5)
   , ("order/salt", 9001)
   , ("order/commit", auditOrderCommitDigest) ]⟩ = false
#guard checkCertifyingSolversAudit = true

/-! ## §5. Axiom Audit -/

#assert_axioms decodeMarket_inferred
#assert_axioms decodeMarket_explicit
#assert_axioms decodeAction_clear_iff
#assert_axioms decodeAction_clear_inferred
#assert_axioms verifyClearing_sound
#assert_axioms decoded_clear_action_sound
#assert_axioms hashEq_deployed_cshake256_image
#assert_axioms hashEq_rejects_mismatched_digest
#assert_axioms hashEq_rejects_wrong_commit_value
#assert_axioms hashEq_concrete_binding

/-- info: 'Minidregg.Assurance.DeployedCertifyingSolvers.verifyClearing_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyClearing_sound
/-- info: 'Minidregg.Assurance.DeployedCertifyingSolvers.decoded_clear_action_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_clear_action_sound
/-- info: 'Minidregg.Assurance.DeployedCertifyingSolvers.hashEq_rejects_mismatched_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hashEq_rejects_mismatched_digest
/-- info: 'Minidregg.Assurance.DeployedCertifyingSolvers.hashEq_concrete_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hashEq_concrete_binding

end Minidregg.Assurance.DeployedCertifyingSolvers
