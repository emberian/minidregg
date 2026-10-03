# Shared-consequence story methods over admitted actor/property/resource inputs.
# This module computes candidate typed writes; it never submits a native effect.
# World.Plan admission must bind every input root/source and check current rights.
# Each property has one authoritative owner, never one copy per player's bag.
import Base

type SourceVersion is Data:
  SourceVersion{artifact: List<&2, Nat>, definition: List<&2, Nat>, revision: Nat}

type Ref is Data:
  Ref{target: Nat, root: List<&2, Nat>}

def ref_target(ref: Ref) -> Nat:
  match ref:
    case Ref{target, root}:
      target

def bool_not(equal: Bool) -> Bool:
  match equal:
    case True{}:
      False{}
    case False{}:
      True{}

def distinct(a: Nat, b: Nat) -> Bool:
  bool_not(Nat.eq(a, b))

# Roles must refer to distinct native targets; copied roots do not create roles.
def roles_distinct(+ruleRef: Ref, +playerRef: Ref, +resourceRef: Ref) -> Bool:
  Bool.and(distinct(ref_target(ruleRef), ref_target(playerRef)),
    Bool.and(distinct(ref_target(ruleRef), ref_target(resourceRef)),
      distinct(ref_target(playerRef), ref_target(resourceRef))))

type Owner is Data:
  Ground{}
  Held{subject: Nat}

def owner_word(owner: Owner) -> Nat:
  match owner:
    case Ground{}:
      0n
    case Held{subject}:
      1n+subject

def held_by(+owner: Owner, subject: Nat) -> Bool:
  match owner:
    case Ground{}:
      False{}
    case Held{holder}:
      Nat.eq(holder, subject)

type Player is Data:
  Player{ref: Ref, subject: Nat, scene: Nat, turn: Nat}

type Property is Data:
  Property{ref: Ref, scene: Nat, owner: Owner, generation: Nat}

type Supply is Data:
  Supply{ref: Ref, remaining: Nat, generation: Nat}

type Edge is Data:
  Edge{src: Nat, dst: Nat, cost: Nat}

type Rules is Data:
  Rules{source: SourceVersion, ref: Ref, edges: List<&2, Edge>}

def take_roles(ruleRef: Ref, player: Player, property: Property) -> Bool:
  match player property:
    case Player{playerRef, subject, scene, turn}
         Property{propertyRef, propScene, owner, generation}:
      roles_distinct(ruleRef, playerRef, propertyRef)

def move_roles(ruleRef: Ref, player: Player, supply: Supply) -> Bool:
  match player supply:
    case Player{playerRef, subject, scene, turn}
         Supply{supplyRef, available, generation}:
      roles_distinct(ruleRef, playerRef, supplyRef)

def source_eq(a: SourceVersion, b: SourceVersion) -> Bool:
  match a b:
    case SourceVersion{artifactA, definitionA, revisionA}
         SourceVersion{artifactB, definitionB, revisionB}:
      Bool.and(Bytes.eq(artifactA, artifactB),
        Bool.and(Bytes.eq(definitionA, definitionB), Nat.eq(revisionA, revisionB)))

# A true source match establishes every full source/export byte and revision.
def source_eq_sound(+a: SourceVersion, +b: SourceVersion,
    +e: Truth(source_eq(a, b))) -> {a == b : SourceVersion}:
  match a b:
    case SourceVersion{+artifactA, +definitionA, +revisionA}
         SourceVersion{+artifactB, +definitionB, +revisionB}:
      %Bytes.eq_sound(artifactA, artifactB,
        Bool.and_left(Bytes.eq(artifactA, artifactB),
          Bool.and(Bytes.eq(definitionA, definitionB), Nat.eq(revisionA, revisionB)), e)) :
        {SourceVersion{artifactA, definitionA, revisionA} == SourceVersion{_, definitionB, revisionB} : SourceVersion}
      %Bytes.eq_sound(definitionA, definitionB,
        Bool.and_left(Bytes.eq(definitionA, definitionB), Nat.eq(revisionA, revisionB),
          Bool.and_right(Bytes.eq(artifactA, artifactB),
            Bool.and(Bytes.eq(definitionA, definitionB), Nat.eq(revisionA, revisionB)), e))) :
        {SourceVersion{artifactA, definitionA, revisionA} == SourceVersion{artifactA, _, revisionB} : SourceVersion}
      %Nat.eq_sound(revisionA, revisionB,
        Bool.and_right(Bytes.eq(definitionA, definitionB), Nat.eq(revisionA, revisionB),
          Bool.and_right(Bytes.eq(artifactA, artifactB),
            Bool.and(Bytes.eq(definitionA, definitionB), Nat.eq(revisionA, revisionB)), e))) :
        {SourceVersion{artifactA, definitionA, revisionA} == SourceVersion{artifactA, definitionA, _} : SourceVersion}
      {==}

def edge_eq(a: Edge, b: Edge) -> Bool:
  match a b:
    case Edge{srcA, dstA, costA} Edge{srcB, dstB, costB}:
      Bool.and(Nat.eq(srcA, srcB), Bool.and(Nat.eq(dstA, dstB), Nat.eq(costA, costB)))

def contains_edge.fin(equal: Bool, restFound: Bool) -> Bool:
  match equal:
    case True{}:
      True{}
    case False{}:
      restFound

def contains_edge(+edge: Edge, edges: List<&2, Edge>) -> Bool:
  match edges:
    case Nil{}:
      False{}
    case Con{candidate, rest}:
      contains_edge.fin(edge_eq(edge, candidate), contains_edge(edge, rest))

# Fields use the existing native scalar store: player scene0/turn1;
# shared property scene0/owner1/generation2; shared supply amount0/generation1.
# Expected values and roots are independent admission guards, not authority.
type Write is Data:
  Write{field: Nat, before: Nat, after: Nat}

type Effects is Data:
  NoEffects{}
  ScalarEffect{ref: Ref, writes: List<&2, Write>, rest: Effects}

type Reads is Data:
  NoReads{}
  ReadRoot{ref: Ref, rest: Reads}

type Candidate is Data:
  Candidate{source: SourceVersion, reads: Reads, effects: Effects}

type Result is Data:
  Refused{reason: Nat}
  Proposed{candidate: Candidate}

# Refusal codes:1 changed source revision,2 property already held,3 wrong scene,
# 4 absent authored edge,5 insufficient shared supply,6 aliased role targets,
# 7 property already ground,8 holder differs from acting player. No mutation on refusal.
def take.scene(source: SourceVersion, ruleRef: Ref, +playerRef: Ref, subject: Nat,
    +turn: Nat, +propertyRef: Ref, +generation: Nat, sameScene: Bool) -> Result:
  match sameScene:
    case False{}:
      Refused{3n}
    case True{}:
      Proposed{Candidate{source, ReadRoot{ruleRef,
        ReadRoot{playerRef, ReadRoot{propertyRef, NoReads{}}}},
        ScalarEffect{playerRef, [Write{1n, turn, 1n+turn}],
          ScalarEffect{propertyRef,
            [Write{1n, 0n, 1n+subject}, Write{2n, generation, 1n+generation}],
            NoEffects{}}}}}

def take_same(source: SourceVersion, ruleRef: Ref,
    player: Player, property: Property) -> Result:
  match player property:
    case Player{+playerRef, subject, +scene, +turn}
         Property{+propertyRef, propScene, owner, +generation}:
      match owner:
        case Held{holder}:
          Refused{2n}
        case Ground{}:
          take.scene(source, ruleRef, playerRef, subject, turn, propertyRef,
            generation, Nat.eq(scene, propScene))

def take.distinct(source: SourceVersion, ruleRef: Ref,
    player: Player, property: Property, separate: Bool) -> Result:
  match separate:
    case False{}:
      Refused{6n}
    case True{}:
      take_same(source, ruleRef, player, property)

def take.fin(source: SourceVersion, +ruleRef: Ref,
    +player: Player, +property: Property, same: Bool) -> Result:
  match same:
    case False{}:
      Refused{1n}
    case True{}:
      take.distinct(source, ruleRef, player, property, take_roles(ruleRef, player, property))

def take(expected: SourceVersion, rules: Rules, player: Player, property: Property) -> Result:
  match rules:
    case Rules{+source, ruleRef, edges}:
      take.fin(source, ruleRef, player, property, source_eq(expected, source))

# A held property's location follows its holder; dropping installs its current
# room and makes the single global property available again, in one joint Plan.
def drop.held(sameHolder: Bool, source: SourceVersion, ruleRef: Ref,
    +playerRef: Ref, +scene: Nat, +turn: Nat, +propertyRef: Ref,
    propScene: Nat, holder: Nat, +generation: Nat) -> Result:
  match sameHolder:
    case False{}:
      Refused{8n}
    case True{}:
      Proposed{Candidate{source, ReadRoot{ruleRef,
        ReadRoot{playerRef, ReadRoot{propertyRef, NoReads{}}}},
        ScalarEffect{playerRef, [Write{1n, turn, 1n+turn}],
          ScalarEffect{propertyRef,
            [Write{0n, propScene, scene}, Write{1n, 1n+holder, 0n},
             Write{2n, generation, 1n+generation}], NoEffects{}}}}}

def drop_same(source: SourceVersion, ruleRef: Ref,
    player: Player, property: Property) -> Result:
  match player property:
    case Player{playerRef, subject, scene, turn}
         Property{propertyRef, propScene, owner, generation}:
      match owner:
        case Ground{}:
          Refused{7n}
        case Held{+holder}:
          drop.held(Nat.eq(holder, subject), source, ruleRef, playerRef, scene, turn,
            propertyRef, propScene, holder, generation)

def drop.distinct(source: SourceVersion, ruleRef: Ref,
    player: Player, property: Property, separate: Bool) -> Result:
  match separate:
    case False{}:
      Refused{6n}
    case True{}:
      drop_same(source, ruleRef, player, property)

def drop.fin(source: SourceVersion, +ruleRef: Ref,
    +player: Player, +property: Property, same: Bool) -> Result:
  match same:
    case False{}:
      Refused{1n}
    case True{}:
      drop.distinct(source, ruleRef, player, property, take_roles(ruleRef, player, property))

def drop(expected: SourceVersion, rules: Rules, player: Player, property: Property) -> Result:
  match rules:
    case Rules{+source, ruleRef, edges}:
      drop.fin(source, ruleRef, player, property, source_eq(expected, source))

law another_holder_cannot_drop:
  for source: SourceVersion
  for ruleRef: Ref
  for playerRef: Ref
  for scene: Nat
  for turn: Nat
  for propertyRef: Ref
  for propScene: Nat
  for holder: Nat
  for generation: Nat
  {drop.held(False{}, source, ruleRef, playerRef, scene, turn,
    propertyRef, propScene, holder, generation) == Refused{8n} : Result}

def another_holder_cannot_drop(source, ruleRef, playerRef, scene, turn, propertyRef,
    propScene, holder, generation):
  {==}

type MaybeSpend is Data:
  NotEnough{}
  Enough{remaining: Nat}

def spend(cost: Nat, available: Nat) -> MaybeSpend:
  match cost available:
    case 0n remaining:
      Enough{remaining}
    case 1n+cost 0n:
      NotEnough{}
    case 1n+cost 1n+remaining:
      spend(cost, remaining)

# A successful spend conserves the exact authored quantity for every input.
# Insufficient supply returns a refusal; there is no saturated/negative write.
def plus(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n+p:
      1n+plus(p, b)

def SpendCorrect(cost: Nat, available: Nat, spent: MaybeSpend) -> Data:
  match spent:
    case NotEnough{}:
      Unit
    case Enough{remaining}:
      {plus(cost, remaining) == available : Nat}

def spend_step(+cost: Nat, +available: Nat, +spent: MaybeSpend,
    e: SpendCorrect(cost, available, spent)) ->
    SpendCorrect(1n+cost, 1n+available, spent):
  match spent:
    case NotEnough{}:
      Unit{}
    case Enough{remaining}:
      %e : {1n+plus(cost, remaining) == 1n+_ : Nat}
      {==}

law spend_conserves:
  for +cost: Nat
  for +available: Nat
  SpendCorrect(cost, available, spend(cost, available))

def spend_conserves(cost, available):
  match cost available:
    case 0n remaining:
      {==}
    case 1n+cost 0n:
      Unit{}
    case 1n+cost 1n+remaining:
      spend_step(cost, remaining, spend(cost, remaining), spend_conserves(cost, remaining))

def move_spend(spent: MaybeSpend, source: SourceVersion, ruleRef: Ref, player: Player,
    supply: Supply, dst: Nat) -> Result:
  match spent:
    case NotEnough{}:
      Refused{5n}
    case Enough{remaining}:
      match player supply:
        case Player{+playerRef, subject, scene, +turn}
             Supply{+supplyRef, available, +generation}:
          Proposed{Candidate{source, ReadRoot{ruleRef,
            ReadRoot{playerRef, ReadRoot{supplyRef, NoReads{}}}},
            ScalarEffect{playerRef,
              [Write{0n, scene, dst}, Write{1n, turn, 1n+turn}],
              ScalarEffect{supplyRef,
                [Write{0n, available, remaining}, Write{1n, generation, 1n+generation}],
                NoEffects{}}}}}

def move.scene(sameScene: Bool, source: SourceVersion, ruleRef: Ref, player: Player, +supply: Supply,
    dst: Nat, cost: Nat) -> Result:
  match sameScene:
    case False{}:
      Refused{3n}
    case True{}:
      match supply:
        case Supply{supplyRef, +available, generation}:
          move_spend(spend(cost, available), source, ruleRef, player,
            Supply{supplyRef, available, generation}, dst)

def move_allowed(permitted: Bool, source: SourceVersion, ruleRef: Ref, +player: Player,
    +supply: Supply, edge: Edge) -> Result:
  match permitted:
    case False{}:
      Refused{4n}
    case True{}:
      match player supply edge:
        case Player{playerRef, subject, +scene, turn}
             Supply{supplyRef, +available, generation} Edge{src, dst, cost}:
          move.scene(Nat.eq(scene, src), source, ruleRef, Player{playerRef, subject, scene, turn},
            Supply{supplyRef, available, generation}, dst, cost)

def move.distinct(source: SourceVersion, ruleRef: Ref, edges: List<&2, Edge>,
    player: Player, supply: Supply, +edge: Edge, separate: Bool) -> Result:
  match separate:
    case False{}:
      Refused{6n}
    case True{}:
      move_allowed(contains_edge(edge, edges), source, ruleRef, player, supply, edge)

def move.fin(source: SourceVersion, +ruleRef: Ref, edges: List<&2, Edge>,
    +player: Player, +supply: Supply, edge: Edge, same: Bool) -> Result:
  match same:
    case False{}:
      Refused{1n}
    case True{}:
      move.distinct(source, ruleRef, edges, player, supply, edge, move_roles(ruleRef, player, supply))

def move(expected: SourceVersion, rules: Rules,
    player: Player, supply: Supply, edge: Edge) -> Result:
  match rules:
    case Rules{+source, ruleRef, edges}:
      move.fin(source, ruleRef, edges, player, supply, edge, source_eq(expected, source))

# Narrative remains attributed provider output; a suggested candidate is data.
# The resident has no function here that installs it or bypasses a receiver law.
type Narrative is Data:
  Narrative{request: List<&2, Nat>, resident: List<&2, Nat>,
    source: SourceVersion, observed: Reads, text: List<&2, Nat>, suggestion: Result}

def gm_reply(request: List<&2, Nat>, resident: List<&2, Nat>,
    source: SourceVersion, observed: Reads, text: List<&2, Nat>, suggestion: Result) -> Narrative:
  Narrative{request, resident, source, observed, text, suggestion}

# General single-owner law: two successful holder observations agree exactly.
def holder_exact(+owner: Owner, +a: Nat, +b: Nat,
    ea: Truth(held_by(owner, a)), eb: Truth(held_by(owner, b))) -> {a == b : Nat}:
  match owner:
    case Ground{}:
      Empty.absurd({a == b : Nat}, ea)
    case Held{+holder}:
      %Nat.eq_sound(holder, a, ea) : {_ == b : Nat}
      Nat.eq_sound(holder, b, eb)

law held_property_cannot_be_taken:
  for source: SourceVersion
  for ruleRef: Ref
  for playerRef: Ref
  for subject: Nat
  for scene: Nat
  for turn: Nat
  for propertyRef: Ref
  for propScene: Nat
  for holder: Nat
  for generation: Nat
  {take_same(source, ruleRef, Player{playerRef, subject, scene, turn},
    Property{propertyRef, propScene, Held{holder}, generation}) == Refused{2n} : Result}

def held_property_cannot_be_taken(source, ruleRef, playerRef, subject, scene, turn,
    propertyRef, propScene, holder, generation):
  {==}

law source_mismatch_no_effects:
  for source: SourceVersion
  for ruleRef: Ref
  for player: Player
  for property: Property
  {take.fin(source, ruleRef, player, property, False{}) == Refused{1n} : Result}

def source_mismatch_no_effects(source, ruleRef, player, property):
  {==}

law gm_reply_exact_fields:
  for request: List<&2, Nat>
  for resident: List<&2, Nat>
  for source: SourceVersion
  for observed: Reads
  for text: List<&2, Nat>
  for suggestion: Result
  {gm_reply(request, resident, source, observed, text, suggestion) ==
    Narrative{request, resident, source, observed, text, suggestion} : Narrative}

def gm_reply_exact_fields(request, resident, source, observed, text, suggestion):
  {==}

# These are general entry-gate laws; native target/root binding remains receiving work.
law aliased_roles_no_take_effects:
  for source: SourceVersion
  for ruleRef: Ref
  for player: Player
  for property: Property
  {take.distinct(source, ruleRef, player, property, False{}) == Refused{6n} : Result}

def aliased_roles_no_take_effects(source, ruleRef, player, property):
  {==}

law aliased_roles_no_move_effects:
  for source: SourceVersion
  for ruleRef: Ref
  for edges: List<&2, Edge>
  for player: Player
  for supply: Supply
  for edge: Edge
  {move.distinct(source, ruleRef, edges, player, supply, edge, False{}) == Refused{6n} : Result}

def aliased_roles_no_move_effects(source, ruleRef, edges, player, supply, edge):
  {==}

# Every successful take emits both ordered effects and all three read roots.
# This is a source theorem; native atomicity/current authority are receiver laws.
law take_joint_effects:
  for source: SourceVersion
  for ruleRef: Ref
  for +playerRef: Ref
  for subject: Nat
  for +turn: Nat
  for +propertyRef: Ref
  for +generation: Nat
  {take.scene(source, ruleRef, playerRef, subject, turn, propertyRef, generation, True{}) ==
    Proposed{Candidate{source, ReadRoot{ruleRef,
      ReadRoot{playerRef, ReadRoot{propertyRef, NoReads{}}}},
      ScalarEffect{playerRef, [Write{1n, turn, 1n+turn}],
        ScalarEffect{propertyRef,
          [Write{1n, 0n, 1n+subject}, Write{2n, generation, 1n+generation}], NoEffects{}}}}} : Result}

def take_joint_effects(source, ruleRef, playerRef, subject, turn, propertyRef, generation):
  {==}

law move_source_mismatch_no_effects:
  for source: SourceVersion
  for ruleRef: Ref
  for edges: List<&2, Edge>
  for player: Player
  for supply: Supply
  for edge: Edge
  {move.fin(source, ruleRef, edges, player, supply, edge, False{}) == Refused{1n} : Result}

def move_source_mismatch_no_effects(source, ruleRef, edges, player, supply, edge):
  {==}
