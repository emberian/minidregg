/-
Typed, source-owned quote for one provider call, by the route the call took.
The operator pins a per-route tariff in the Host profile and funds an
independent AgentGrain allowance. Neither the reported counts nor this quote
authenticate a provider invoice. The native receiver still decides whether an
authored settlement is admitted, under the provider purse's route law
(`Kernel.ProviderRoute`), which charges by the route recorded at reserve.
-/
import Kernel.AgentGrain
import Theory.AssertAxioms

namespace Minidregg.Kernel.ProviderMetering

open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler
open Minidregg.Kernel

set_option autoImplicit false

/-- The payer of one provider call, fixed when the purse reserves for it.
* `user`: the friend's own provider key. The friend pays the provider
  directly; Mini charges only the per-operation fee for the turn.
* `pool`: the operator's key, funded by the purse. Metered.
* `homelab`: a keyless upstream the operator runs. Priced like the pool
  (a per-operation fee plus optional metered rates).
There is no `none` route: a call without a payer is refused before any
reserve, so no purse ever holds for it (`ProviderRoute.none_route_reserves_nothing`). -/
inductive Route where
  | user
  | pool
  | homelab
  deriving DecidableEq, Repr

/-- The code the purse records in its route field (field 4). Zero is "no
call in flight". -/
def Route.code : Route → Int
  | .user => 1
  | .pool => 2
  | .homelab => 3

def Route.name : Route → String
  | .user => "user"
  | .pool => "pool"
  | .homelab => "homelab"

def Route.ofName? : String → Option Route
  | "user" => some .user
  | "pool" => some .pool
  | "homelab" => some .homelab
  | _ => none

def Route.ofCode? : Int → Option Route
  | 1 => some .user
  | 2 => some .pool
  | 3 => some .homelab
  | _ => none

theorem Route.ofCode_code (route : Route) : Route.ofCode? route.code = some route := by
  cases route <;> rfl

theorem Route.ofName_name (route : Route) : Route.ofName? route.name = some route := by
  cases route <;> rfl

/-- A metered route's rates. All three are in **credit**: a purse is funded
only by `Kernel.PurseRefill`, which burns the pay tariff's credit asset 1:1
into the purse's allowance, so one permission micro-unit is one credit and
`inputMicroPerMillion = 20000000` means 20 credits per million input tokens. -/
structure Rate where
  perOp : Nat
  inputMicroPerMillion : Nat
  outputMicroPerMillion : Nat
  deriving DecidableEq, Repr

/-- The per-route provider tariff (schema v2). The user route has a
per-operation fee and nothing else: it has no rate fields, so no token count
can reach a user-route charge. The version is an operator-controlled tariff
identity, not a provider price feed. -/
structure Tariff where
  version : Nat
  model : String
  userPerOp : Nat
  pool : Rate
  homelab : Rate
  deriving DecidableEq, Repr

/-- The per-operation fees, the part of the tariff the provider purse's
installed law carries as constants. -/
structure Schedule where
  user : Nat
  pool : Nat
  homelab : Nat
  deriving DecidableEq, Repr

def Tariff.schedule (tariff : Tariff) : Schedule :=
  ⟨tariff.userPerOp, tariff.pool.perOp, tariff.homelab.perOp⟩

def Schedule.perOp (schedule : Schedule) : Route → Nat
  | .user => schedule.user
  | .pool => schedule.pool
  | .homelab => schedule.homelab

def Tariff.perOp (tariff : Tariff) (route : Route) : Nat :=
  tariff.schedule.perOp route

/-- The metered rates of a route; the user route has none. -/
def Tariff.rate? (tariff : Tariff) : Route → Option Rate
  | .user => none
  | .pool => some tariff.pool
  | .homelab => some tariff.homelab

/-- Counts asserted in one complete upstream response. The parser, not the
worker, must construct these from the retained response bytes. -/
structure Usage where
  promptTokens : Nat
  completionTokens : Nat
  totalTokens : Nat
  deriving DecidableEq, Repr

def maxReportedTokens : Nat := 1000000000
def maxRate : Nat := 1000000000000
def million : Nat := 1000000

def Rate.valid (rate : Rate) : Prop :=
  rate.perOp ≤ maxRate ∧
  rate.inputMicroPerMillion ≤ maxRate ∧
  rate.outputMicroPerMillion ≤ maxRate

instance (rate : Rate) : Decidable rate.valid := by
  unfold Rate.valid; infer_instance

def Tariff.valid (tariff : Tariff) : Prop :=
  0 < tariff.version ∧
  0 < tariff.model.toUTF8.size ∧
  tariff.model.toUTF8.size ≤ 256 ∧
  tariff.userPerOp ≤ maxRate ∧
  tariff.pool.valid ∧
  tariff.homelab.valid

instance (tariff : Tariff) : Decidable tariff.valid := by
  unfold Tariff.valid; infer_instance

def Usage.valid (usage : Usage) : Prop :=
  usage.totalTokens = usage.promptTokens + usage.completionTokens ∧
  usage.promptTokens ≤ maxReportedTokens ∧
  usage.completionTokens ≤ maxReportedTokens

instance (usage : Usage) : Decidable usage.valid := by
  unfold Usage.valid; infer_instance

def weighted (rate : Rate) (usage : Usage) : Nat :=
  usage.promptTokens * rate.inputMicroPerMillion +
    usage.completionTokens * rate.outputMicroPerMillion

/-- Round the metered part upward once, to an integral permission
micro-unit. No floating-point arithmetic or per-category double rounding. -/
def metered (rate : Rate) (usage : Usage) : Nat :=
  (weighted rate usage + million - 1) / million

/-- The one rounding point is the ceiling of the aggregate numerator,
including the zero-usage case. -/
theorem metered_rounding (rate : Rate) (usage : Usage) :
    weighted rate usage ≤ metered rate usage * million ∧
      metered rate usage * million < weighted rate usage + million := by
  unfold metered million
  omega

/-- The charge for one call on a route: its per-operation fee, plus, on a
metered route, the metered usage. A user-route call ignores the usage. -/
def charge (tariff : Tariff) (route : Route) (usage : Usage) : Nat :=
  tariff.perOp route +
    match tariff.rate? route with
    | none => 0
    | some rate => metered rate usage

theorem charge_user (tariff : Tariff) (usage : Usage) :
    charge tariff .user usage = tariff.userPerOp := by
  simp [charge, Tariff.rate?, Tariff.perOp, Tariff.schedule, Schedule.perOp]

theorem charge_pool (tariff : Tariff) (usage : Usage) :
    charge tariff .pool usage = tariff.pool.perOp + metered tariff.pool usage := by
  simp [charge, Tariff.rate?, Tariff.perOp, Tariff.schedule, Schedule.perOp]

theorem charge_homelab (tariff : Tariff) (usage : Usage) :
    charge tariff .homelab usage = tariff.homelab.perOp + metered tariff.homelab usage := by
  simp [charge, Tariff.rate?, Tariff.perOp, Tariff.schedule, Schedule.perOp]

/-- The largest charge a metered call can reach under per-call token
ceilings: what the reserve must cover. -/
def maxCharge (tariff : Tariff) (route : Route) (maxInput maxOutput : Nat) : Nat :=
  charge tariff route ⟨maxInput, maxOutput, maxInput + maxOutput⟩

theorem metered_monotone (rate : Rate) (usage : Usage) (maxInput maxOutput : Nat)
    (input : usage.promptTokens ≤ maxInput) (output : usage.completionTokens ≤ maxOutput) :
    metered rate usage ≤ metered rate ⟨maxInput, maxOutput, maxInput + maxOutput⟩ := by
  unfold metered weighted
  apply Nat.div_le_div_right
  have := Nat.mul_le_mul_right rate.inputMicroPerMillion input
  have := Nat.mul_le_mul_right rate.outputMicroPerMillion output
  dsimp only
  omega

/-- A call within the token ceilings never charges more than `maxCharge`. -/
theorem charge_le_maxCharge (tariff : Tariff) (route : Route) (usage : Usage)
    (maxInput maxOutput : Nat)
    (input : usage.promptTokens ≤ maxInput) (output : usage.completionTokens ≤ maxOutput) :
    charge tariff route usage ≤ maxCharge tariff route maxInput maxOutput := by
  unfold maxCharge
  cases route with
  | user => simp [charge_user]
  | pool =>
      rw [charge_pool, charge_pool]
      have := metered_monotone tariff.pool usage maxInput maxOutput input output
      omega
  | homelab =>
      rw [charge_homelab, charge_homelab]
      have := metered_monotone tariff.homelab usage maxInput maxOutput input output
      omega

/-- Unambiguous length-prefixing keeps model, version, route and rates
distinct before the repository's domain-separated cSHAKE projection. -/
def rateBytes (rate : Rate) : List UInt8 :=
  Sp800185Cshake256.leftEncode rate.perOp ++
  Sp800185Cshake256.leftEncode rate.inputMicroPerMillion ++
  Sp800185Cshake256.leftEncode rate.outputMicroPerMillion

def tariffBytes (tariff : Tariff) : List UInt8 :=
  Sp800185Cshake256.encodeString tariff.model.toUTF8.toList ++
  Sp800185Cshake256.leftEncode tariff.version ++
  Sp800185Cshake256.leftEncode tariff.userPerOp ++
  rateBytes tariff.pool ++
  rateBytes tariff.homelab

def tariffDigest (tariff : Tariff) : Digest :=
  (Sp800185Cshake256.hash "DREGG.PROVIDER.TARIFF/v2".toUTF8.toList
    (tariffBytes tariff)).digest

def requestDigest (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.PROVIDER.REQUEST/v1".toUTF8.toList bytes).digest

def responseDigest (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.PROVIDER.RESPONSE/v1".toUTF8.toList bytes).digest

/-- The amount a quote may name: a user-route call is its fee whatever the
response says; a metered route needs the parsed usage. -/
def quoteAmount (tariff : Tariff) : Route → Option Usage → Option Nat
  | .user, _ => some tariff.userPerOp
  | route, some usage => some (charge tariff route usage)
  | _, none => none

/-- A quote identifies the exact retained request/response bytes, the route,
the reported usage (metered routes only), the configured tariff and the held
allowance. Its evidence is external data; the proof fields establish only
arithmetic and allowance bounds. -/
structure Quote where
  tariff : Tariff
  tariffValid : tariff.valid
  route : Route
  usage : Option Usage
  usageValid : ∀ observed, usage = some observed → observed.valid
  request : List UInt8
  response : List UInt8
  reserve : Nat
  amount : Nat
  amountExact : quoteAmount tariff route usage = some amount
  amountBound : amount ≤ reserve

def prepare (tariff : Tariff) (route : Route) (usage : Option Usage)
    (request response : List UInt8) (reserve : Nat) : Option Quote :=
  if ht : tariff.valid then
    if hv : ∀ observed, usage = some observed → observed.valid then
      match ha : quoteAmount tariff route usage with
      | none => none
      | some amount =>
          if hb : amount ≤ reserve then
            some ⟨tariff, ht, route, usage, hv, request, response, reserve, amount, ha, hb⟩
          else none
    else none
  else none

/-- A user-route quote is exactly the per-operation fee. -/
theorem Quote.user_is_per_op (quote : Quote) (user : quote.route = .user) :
    quote.amount = quote.tariff.userPerOp := by
  have exact := quote.amountExact
  rw [user] at exact
  simp [quoteAmount] at exact
  exact exact.symm

/-- A pool-route quote is the per-operation fee plus the metered usage. -/
theorem Quote.pool_is_metered (quote : Quote) (pool : quote.route = .pool) :
    ∃ usage, quote.usage = some usage ∧
      quote.amount = quote.tariff.pool.perOp + metered quote.tariff.pool usage := by
  have exact := quote.amountExact
  rw [pool] at exact
  cases h : quote.usage with
  | none => rw [h] at exact; simp [quoteAmount] at exact
  | some usage =>
      rw [h] at exact
      simp [quoteAmount, charge_pool] at exact
      exact ⟨usage, rfl, exact.symm⟩

def Quote.operation (quote : Quote) : AgentGrain.Operation :=
  .settle (Int.ofNat quote.amount)

theorem Quote.operation_after (quote : Quote) (state : AgentGrain.State) :
    quote.operation.after state = AgentGrain.settle state (Int.ofNat quote.amount) := rfl

theorem Quote.charge_within_hold (quote : Quote) :
    0 ≤ (Int.ofNat quote.amount : Int) ∧
      (Int.ofNat quote.amount : Int) ≤ Int.ofNat quote.reserve := by
  constructor
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_le.mpr quote.amountBound

/-- The controller must establish this equality from the fresh signed
provider state; the quote's reserve field alone is not a receipt. -/
theorem Quote.charge_within_signed_hold (quote : Quote) (state : AgentGrain.State)
    (held : state.reserved = Int.ofNat quote.reserve) :
    0 ≤ (Int.ofNat quote.amount : Int) ∧
      (Int.ofNat quote.amount : Int) ≤ state.reserved := by
  simpa [held] using quote.charge_within_hold

theorem Quote.exact_budget_change (quote : Quote) (state : AgentGrain.State) :
    (quote.operation.after state).remaining +
      (quote.operation.after state).reserved =
      state.remaining + state.reserved - Int.ofNat quote.amount := by
  simp [Quote.operation_after, AgentGrain.settle]

/-- Once the native receiver admits the exact authored settlement, its budget
decreases by precisely the Lean quote. The quote does not itself prove receipt
authenticity, authority, or receiver admission. -/
theorem Quote.admitted_budget_nonincrease (quote : Quote) (state : AgentGrain.State)
    (admitted : AgentGrain.accepts state (quote.operation.after state) = true) :
    (quote.operation.after state).remaining +
      (quote.operation.after state).reserved ≤ state.remaining + state.reserved :=
  AgentGrain.accepted_budget_nonincrease state (quote.operation.after state) admitted

#assert_axioms Route.ofCode_code
#assert_axioms Route.ofName_name
#assert_axioms metered_rounding
#assert_axioms charge_user
#assert_axioms charge_pool
#assert_axioms charge_homelab
#assert_axioms metered_monotone
#assert_axioms charge_le_maxCharge
#assert_axioms Quote.user_is_per_op
#assert_axioms Quote.pool_is_metered
#assert_axioms Quote.charge_within_signed_hold
#assert_axioms Quote.exact_budget_change
#assert_axioms Quote.admitted_budget_nonincrease

end Minidregg.Kernel.ProviderMetering
