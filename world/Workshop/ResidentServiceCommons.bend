# Source-authored service commons over ordinary world state, canonical money,
# admitted room request rows and BendActivity pending/outcome identities.
# These typed proposals are NOT native authority, provider truth or receipts.
import Base
import ./MarketMath.bend as Math
import ./CanonicalBookSettlement.bend as Book

type Pin is Data:
  Pin{resource: Nat, root: List<&2, Nat>}

type Method is Data:
  Method{artifact: List<&2, Nat>, program: List<&2, Nat>, exportName: List<&2, Nat>,
    inputSchema: List<&2, Nat>, resultSchema: List<&2, Nat>}

type Identity is Data:
  Identity{request: List<&2, Nat>, method: Method, input: List<&2, Nat>, context: List<&2, Nat>}

type Payment is Data:
  Payment{book: Nat, root: List<&2, Nat>, payer: Nat, escrow: Nat,
    providerAccount: Nat, asset: Nat, available: Nat}

type Request is Data:
  Request{identity: Identity, residentHome: Pin, room: Pin,
    consumer: List<&2, Nat>, recipient: List<&2, Nat>, audience: List<&2, Nat>,
    keyEpoch: List<&2, Nat>, acceptor: List<&2, Nat>, criterion: Method,
    dispatchDeadline: Nat, units: Nat, budget: Nat, payment: Payment}

# Claim/evidence remains an authored provider assertion; source identity does not
# prove the capability advertised. Current native provider authority is separate.
type Offer is Data:
  Offer{identity: Identity, provider: List<&2, Nat>, providerHome: Pin,
    capacity: Nat, rate: Nat, expires: Nat, claim: List<&2, Nat>}

# Sponsor/group rule is an exact bounded spending endorsement, NOT a statement
# that provider's claim or future answer is true. Native reads bind its provenance.
type Sponsorship is Data:
  Sponsorship{identity: Identity, provider: List<&2, Nat>, policy: Pin,
    maxAmount: Nat, approved: Bool}

type Reservation is Data:
  Reservation{request: Request, offer: Offer, sponsorship: Sponsorship, amount: Nat}

# Existing public resident request row identity: request CELL + SEQUENCE and
# assigned Hermes and the EXACT request/method/input/context binding.
# identity equals the original native operation bytes, not a fresh wrapper ID.
# Native operation identity is retained through uncertain work.
type Run is Data:
  Run{identity: List<&2, Nat>, requestCell: Nat, sequence: Nat, assignedResident: Nat,
    operation: List<&2, Nat>, activity: Pin, ordinal: Nat, binding: Identity}

type Completion is Data:
  Completion{run: Run, provider: List<&2, Nat>, output: List<&2, Nat>,
    recipient: List<&2, Nat>, audience: List<&2, Nat>, keyEpoch: List<&2, Nat>,
    receipt: Pin}

type Review is Data:
  Review{runIdentity: List<&2, Nat>, output: List<&2, Nat>, criterion: Method,
    reviewer: List<&2, Nat>, accepted: Bool}

type State is Data:
  Vacant{}
  Held{reservation: Reservation}
  Running{reservation: Reservation, run: Run}
  Uncertain{reservation: Reservation, run: Run}
  Delivered{reservation: Reservation, run: Run, completion: Completion}
  Finished{reservation: Reservation, run: Run, completion: Completion, review: Review}
  Cancelled{reservation: Reservation}

# Logical effects are lowered ONLY by generic native Plan/Activity/book bridges.
# Neither request identity nor these constructors can select a capability.
type Effect is Data:
  Money{book: Nat, expectedRoot: List<&2, Nat>, transfer: Book.Transfer}
  Capacity{home: Pin, before: Nat, after: Nat}
  PublishRequest{home: Pin, room: Pin, request: Request, run: Run}
  AwaitExisting{run: Run}
  RetainCompletion{run: Run, completion: Completion}
  ReturnResult{recipient: List<&2, Nat>, audience: List<&2, Nat>,
    keyEpoch: List<&2, Nat>, output: List<&2, Nat>}

type Transition is Data:
  Refused{unchanged: State}
  Proposed{expected: State, successor: State, effects: List<&2, Effect>}

def method_eq(a: Method, b: Method) -> Bool:
  match a b:
    case Method{artifact, program, exportName, inputSchema, resultSchema}
        Method{otherArtifact, otherProgram, otherExport, otherInput, otherResult}:
      Bool.and(Bytes.eq(artifact, otherArtifact), Bool.and(Bytes.eq(program, otherProgram),
        Bool.and(Bytes.eq(exportName, otherExport), Bool.and(Bytes.eq(inputSchema, otherInput),
          Bytes.eq(resultSchema, otherResult)))))

def identity_eq(a: Identity, b: Identity) -> Bool:
  match a b:
    case Identity{request, method, input, context} Identity{otherRequest, otherMethod, otherInput, otherContext}:
      Bool.and(Bytes.eq(request, otherRequest), Bool.and(method_eq(method, otherMethod),
        Bool.and(Bytes.eq(input, otherInput), Bytes.eq(context, otherContext))))

def pin_eq(a: Pin, b: Pin) -> Bool:
  match a b:
    case Pin{id, root} Pin{otherId, otherRoot}:
      Bool.and(Nat.eq(id, otherId), Bytes.eq(root, otherRoot))

def run_eq(a: Run, b: Run) -> Bool:
  match a b:
    case Run{identity, requestCell, sequence, assigned, operation, activity, ordinal, binding}
        Run{otherIdentity, otherCell, otherSequence, otherAssigned, otherOperation, otherActivity, otherOrdinal, otherBinding}:
      Bool.and(Bytes.eq(identity, otherIdentity), Bool.and(Nat.eq(requestCell, otherCell),
        Bool.and(Nat.eq(sequence, otherSequence), Bool.and(Nat.eq(assigned, otherAssigned),
          Bool.and(Bytes.eq(operation, otherOperation), Bool.and(pin_eq(activity, otherActivity),
            Bool.and(Nat.eq(ordinal, otherOrdinal), identity_eq(binding, otherBinding))))))))

def choose(before: State, next: State, effects: List<&2, Effect>, allowed: Bool) -> Transition:
  match allowed:
    case False{}:
      Refused{before}
    case True{}:
      Proposed{before, next, effects}

def reserve_choice(+request: Request, +offer: Offer, +sponsorship: Sponsorship,
    +amount: Nat, allowed: Bool) -> Transition:
  match request offer:
    case Request{identity, residentHome, room, consumer, recipient, audience, keyEpoch,
        acceptor, criterion, deadline, units, budget,
        Payment{book, root, payer, escrow, providerAccount, asset, available}}
        Offer{offerIdentity, provider, +providerHome, +capacity, rate, expires, claim}:
      choose(Vacant{}, Held{Reservation{request, offer, sponsorship, amount}},
        [Money{book, root, Book.Transfer{payer, escrow, asset, amount}},
         Capacity{providerHome, capacity, Math.sub(capacity, units)}], allowed)

def reserve(+request: Request, +offer: Offer, +sponsorship: Sponsorship, +now: Nat) -> Transition:
  match request offer sponsorship:
    case Request{+identity, residentHome, room, consumer, recipient, audience, keyEpoch,
        acceptor, criterion, +deadline, +units, budget,
        Payment{book, root, +payer, +escrow, providerAccount, asset, available}}
        Offer{offerIdentity, +provider, providerHome, capacity, rate, +expires, claim}
        Sponsorship{sponsorIdentity, sponsorProvider, policy, maxAmount, approved}:
      +amount = Math.mul(rate, units)
      reserve_choice(request, offer, sponsorship, amount,
        Bool.and(identity_eq(identity, offerIdentity), Bool.and(identity_eq(identity, sponsorIdentity),
          Bool.and(Bytes.eq(provider, sponsorProvider), Bool.and(approved,
            Bool.and(Math.lt(0n, units), Bool.and(Math.le(units, capacity),
              Bool.and(Math.le(now, expires), Bool.and(Math.le(expires, deadline),
                Bool.and(Math.le(amount, budget), Bool.and(Math.le(amount, maxAmount),
                  Bool.and(Math.le(amount, available), Math.not(Nat.eq(payer, escrow))))))))))))))

# Starting means retaining this exact pending operation BEFORE dispatch. It does
# not claim the physical provider call occurred. No checkpoint is client supplied.
def start_held(+reservation: Reservation, +run: Run, +now: Nat) -> Transition:
  match reservation:
    case Reservation{+request, offer, sponsorship, amount}:
      match request:
        case Request{identity, residentHome, room, consumer, recipient, audience, keyEpoch,
            acceptor, criterion, deadline, units, budget, payment}:
          match run:
            case Run{nativeIdentity, requestCell, sequence, assigned, operation, activity, ordinal, boundIdentity}:
              choose(Held{reservation}, Running{reservation, run},
                [PublishRequest{residentHome, room, request, run}],
                Bool.and(Math.le(now, deadline), Bool.and(identity_eq(identity, boundIdentity),
                  Bytes.eq(nativeIdentity, operation))))

def start(state: State, run: Run, now: Nat) -> Transition:
  match state:
    case Held{reservation}:
      start_held(reservation, run, now)
    case Vacant{}:
      Refused{state}
    case Running{reservation, active}:
      Refused{state}
    case Uncertain{reservation, active}:
      Refused{state}
    case Delivered{reservation, active, completion}:
      Refused{state}
    case Finished{reservation, active, completion, review}:
      Refused{state}
    case Cancelled{reservation}:
      Refused{state}

# Uncertain work retains the exact run. Recovery requests an observation of the
# existing operation, never a second dispatch and never timeout-driven payout.
def uncertain(state: State) -> Transition:
  match state:
    case Running{+reservation, +run}:
      Proposed{state, Uncertain{reservation, run}, [AwaitExisting{run}]}
    case Uncertain{+reservation, +run}:
      Proposed{state, state, [AwaitExisting{run}]}
    case Vacant{}:
      Refused{state}
    case Held{reservation}:
      Refused{state}
    case Delivered{reservation, run, completion}:
      Refused{state}
    case Finished{reservation, run, completion, review}:
      Refused{state}
    case Cancelled{reservation}:
      Refused{state}

def completion_matches(request: Request, offer: Offer, run: Run, completion: Completion) -> Bool:
  match request offer completion:
    case Request{identity, residentHome, room, consumer, recipient, audience, keyEpoch,
        acceptor, criterion, deadline, units, budget, payment}
        Offer{offerIdentity, provider, providerHome, capacity, rate, expires, claim}
        Completion{observedRun, observedProvider, output, observedRecipient, observedAudience, observedEpoch, receipt}:
      Bool.and(run_eq(run, observedRun), Bool.and(Bytes.eq(provider, observedProvider),
        Bool.and(Bytes.eq(recipient, observedRecipient), Bool.and(Bytes.eq(audience, observedAudience),
          Bytes.eq(keyEpoch, observedEpoch)))))

# completion is an admitted native observation bound to the exact pending
# operation; a provider's opaque uploaded receipt bytes are not that observation.
def deliver_active(before: State, +reservation: Reservation, +run: Run,
    +completion: Completion) -> Transition:
  match reservation:
    case Reservation{request, offer, sponsorship, amount}:
      choose(before, Delivered{reservation, run, completion}, [RetainCompletion{run, completion}],
        completion_matches(request, offer, run, completion))

def deliver(state: State, completion: Completion) -> Transition:
  match state:
    case Running{+reservation, +run}:
      deliver_active(state, reservation, run, completion)
    case Uncertain{+reservation, +run}:
      deliver_active(state, reservation, run, completion)
    case Vacant{}:
      Refused{state}
    case Held{reservation}:
      Refused{state}
    case Delivered{reservation, run, prior}:
      Refused{state}
    case Finished{reservation, run, prior, review}:
      Refused{state}
    case Cancelled{reservation}:
      Refused{state}

def review_matches(request: Request, run: Run, completion: Completion, review: Review) -> Bool:
  match request run completion review:
    case Request{identity, residentHome, room, consumer, recipient, audience, keyEpoch,
        acceptor, criterion, deadline, units, budget, payment}
        Run{runIdentity, cell, sequence, assigned, operation, activity, ordinal, binding}
        Completion{observedRun, provider, output, observedRecipient, observedAudience, observedEpoch, receipt}
        Review{reviewRun, reviewedOutput, reviewCriterion, reviewer, accepted}:
      Bool.and(Bytes.eq(runIdentity, reviewRun), Bool.and(Bytes.eq(output, reviewedOutput),
        Bool.and(method_eq(criterion, reviewCriterion), Bool.and(Bytes.eq(acceptor, reviewer), accepted))))

# Capacity return uses a fresh admitted provider-home snapshot, not the original
# now-stale reservation root. The exact same native intent installs payment,
# phase and return commitment; source proposal alone authorizes none of these.
def accept_delivered(+reservation: Reservation, +run: Run, +completion: Completion,
    +review: Review, +capacityHome: Pin, +currentCapacity: Nat,
    currentBookRoot: List<&2, Nat>) -> Transition:
  match reservation:
    case Reservation{+request, offer, sponsorship, +amount}:
      match request offer:
        case Request{identity, residentHome, room, consumer, requestRecipient, requestAudience, requestEpoch,
            acceptor, criterion, deadline, +units, budget,
            Payment{book, oldRoot, payer, escrow, providerAccount, asset, available}}
            Offer{offerIdentity, offerProvider, Pin{providerHomeId, providerRoot}, capacity, rate, expires, claim}:
          match completion capacityHome:
            case Completion{observedRun, provider, +output, +recipient, +audience, +epoch, receipt}
                Pin{currentHomeId, currentHomeRoot}:
              choose(Delivered{reservation, run, completion}, Finished{reservation, run, completion, review},
                [Money{book, currentBookRoot, Book.Transfer{escrow, providerAccount, asset, amount}},
                 Capacity{capacityHome, currentCapacity, Math.add(currentCapacity, units)},
                 ReturnResult{recipient, audience, epoch, output}],
                Bool.and(Nat.eq(providerHomeId, currentHomeId), review_matches(request, run, completion, review)))

def accept(state: State, review: Review, capacityHome: Pin, capacity: Nat,
    currentBookRoot: List<&2, Nat>) -> Transition:
  match state:
    case Delivered{reservation, run, completion}:
      accept_delivered(reservation, run, completion, review, capacityHome, capacity, currentBookRoot)
    case Vacant{}:
      Refused{state}
    case Held{reservation}:
      Refused{state}
    case Running{reservation, run}:
      Refused{state}
    case Uncertain{reservation, run}:
      Refused{state}
    case Finished{reservation, run, completion, prior}:
      Refused{state}
    case Cancelled{reservation}:
      Refused{state}

def cancel_held(+reservation: Reservation, +actor: List<&2, Nat>, +now: Nat,
    +capacityHome: Pin, +currentCapacity: Nat, currentBookRoot: List<&2, Nat>) -> Transition:
  match reservation:
    case Reservation{request, offer, sponsorship, amount}:
      match request offer:
        case Request{identity, residentHome, room, +consumer, recipient, audience, keyEpoch,
            acceptor, criterion, deadline, +units, budget,
            Payment{book, root, payer, escrow, providerAccount, asset, available}}
            Offer{offerIdentity, provider, Pin{homeId, oldHomeRoot}, capacity, rate, expires, claim}:
          match capacityHome:
            case Pin{currentId, currentRoot}:
              choose(Held{reservation}, Cancelled{reservation},
                [Money{book, currentBookRoot, Book.Transfer{escrow, payer, asset, amount}},
                 Capacity{capacityHome, currentCapacity, Math.add(currentCapacity, units)}],
                Bool.and(Nat.eq(homeId, currentId), Math.choose_bool(True{},
                  Bytes.eq(actor, consumer), Math.lt(deadline, now))))

# Only unstarted reservations can cancel/refund here. Started/uncertain work
# requires exact native reconciliation; elapsed time is not proof of nonexecution.
def cancel(state: State, actor: List<&2, Nat>, now: Nat, capacityHome: Pin,
    capacity: Nat, currentBookRoot: List<&2, Nat>) -> Transition:
  match state:
    case Held{reservation}:
      cancel_held(reservation, actor, now, capacityHome, capacity, currentBookRoot)
    case Vacant{}:
      Refused{state}
    case Running{reservation, run}:
      Refused{state}
    case Uncertain{reservation, run}:
      Refused{state}
    case Delivered{reservation, run, completion}:
      Refused{state}
    case Finished{reservation, run, completion, review}:
      Refused{state}
    case Cancelled{reservation}:
      Refused{state}

law uncertain_keeps_run:
  for +reservation: Reservation
  for +run: Run
  {uncertain(Running{reservation, run}) ==
    Proposed{Running{reservation, run}, Uncertain{reservation, run}, [AwaitExisting{run}]} : Transition}

def uncertain_keeps_run(reservation, run):
  {==}

law uncertain_cannot_redispatch:
  for +reservation: Reservation
  for +run: Run
  for other: Run
  for now: Nat
  {start(Uncertain{reservation, run}, other, now) == Refused{Uncertain{reservation, run}} : Transition}

def uncertain_cannot_redispatch(reservation, run, other, now):
  {==}

law uncertain_cannot_timeout_refund:
  for +reservation: Reservation
  for +run: Run
  for actor: List<&2, Nat>
  for now: Nat
  for home: Pin
  for capacity: Nat
  for root: List<&2, Nat>
  {cancel(Uncertain{reservation, run}, actor, now, home, capacity, root) ==
    Refused{Uncertain{reservation, run}} : Transition}

def uncertain_cannot_timeout_refund(reservation, run, actor, now, home, capacity, root):
  {==}

law finished_cannot_pay_twice:
  for +reservation: Reservation
  for +run: Run
  for +completion: Completion
  for +prior: Review
  for review: Review
  for home: Pin
  for capacity: Nat
  for root: List<&2, Nat>
  {accept(Finished{reservation, run, completion, prior}, review, home, capacity, root) ==
    Refused{Finished{reservation, run, completion, prior}} : Transition}

def finished_cannot_pay_twice(reservation, run, completion, prior, review, home, capacity, root):
  {==}


