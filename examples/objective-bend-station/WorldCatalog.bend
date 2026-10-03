# Authored metadata/catalog references for an inhabited Station.
# These are source declarations and projections, never a second world heap.
# Fields of player/property/supply resources remain the SharedConsequences schema.
# Every sourceDocSlot indexes a separately admitted current readable vector.
import Base
import ./SharedConsequences.bend as Station

type Scene is Data:
  Scene{id: Nat, title: List<&2, Nat>, description: List<&2, Nat>, sourceDocSlot: Nat}

type Object is Data:
  Object{resourceID: Nat, title: List<&2, Nat>, description: List<&2, Nat>, sourceDocSlot: Nat}

type Role is Data:
  Role{title: List<&2, Nat>, instructions: List<&2, Nat>, sourceDocSlot: Nat}

type Catalog is Data:
  Catalog{source: Station.SourceVersion, ruleRef: Station.Ref,
    scenes: List<&2, Scene>, properties: List<&2, Object>,
    supplies: List<&2, Object>, roles: List<&2, Role>}

# A source catalog declaration can be replaced through governed source adoption;
# its property references identify existing native objects, never copied state.
def catalog(source: Station.SourceVersion, ruleRef: Station.Ref,
    scenes: List<&2, Scene>, properties: List<&2, Object>, supplies: List<&2, Object>,
    roles: List<&2, Role>) -> Catalog:
  Catalog{source, ruleRef, scenes, properties, supplies, roles}

type Location is Data:
  GroundAt{scene: Nat}
  HeldBy{subject: Nat}

# A held prop's room is obtained only from its holder's admitted player view.
# This projection exposes no inferred holder location when that view is absent.
def location(property: Station.Property) -> Location:
  match property:
    case Station.Property{ref, scene, owner, generation}:
      match owner:
        case Station.Ground{}:
          GroundAt{scene}
        case Station.Held{subject}:
          HeldBy{subject}

# Inventory is a query of the same global property observations, not a bag copy.
def inventory.fin(include: Bool, +property: Station.Property,
    rest: List<&2, Station.Property>) -> List<&2, Station.Property>:
  match include:
    case False{}:
      rest
    case True{}:
      Con{property, rest}

def inventory.item(subject: Nat, +property: Station.Property,
    rest: List<&2, Station.Property>) -> List<&2, Station.Property>:
  match property:
    case Station.Property{ref, scene, +owner, generation}:
      inventory.fin(Station.held_by(owner, subject), Station.Property{ref, scene, owner, generation}, rest)

def inventory(+subject: Nat, properties: List<&2, Station.Property>) -> List<&2, Station.Property>:
  match properties:
    case Nil{}:
      Nil{}
    case Con{+property, rest}:
      inventory.item(subject, property, inventory(subject, rest))

# Native admitted-sample binding must prove every projected property Ref unique.
# These source definitions never decide whether a caller was allowed to observe.
law location_from_global_owner:
  for ref: Station.Ref
  for scene: Nat
  for subject: Nat
  for generation: Nat
  {location(Station.Property{ref, scene, Station.Held{subject}, generation}) ==
    HeldBy{subject} : Location}

def location_from_global_owner(ref, scene, subject, generation):
  {==}
