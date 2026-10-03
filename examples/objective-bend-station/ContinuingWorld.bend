# Continuing multiuser world projections/affordances over actual shared samples.
# Inputs must come from native admitted reads; a source data value is not a grant.
# Alternative next actions share one captured base; selecting one re-enters
# current source/native admission. Alternatives are not an ordered auto-script.
import Base
import ./SharedConsequences.bend as Station

type MoveOption is Data:
  MoveOption{edge: Station.Edge, candidate: Station.Result}

type PropertyOption is Data:
  PropertyOption{resource: Station.Ref, take: Station.Result, drop: Station.Result}

def moves(+expected: Station.SourceVersion, +rules: Station.Rules,
    +player: Station.Player, +supply: Station.Supply,
    edges: List<&2, Station.Edge>) -> List<&2, MoveOption>:
  match edges:
    case Nil{}:
      Nil{}
    case Con{+edge, rest}:
      Con{MoveOption{edge, Station.move(expected, rules, player, supply, edge)},
        moves(expected, rules, player, supply, rest)}

def property_option(+expected: Station.SourceVersion, +rules: Station.Rules,
    +player: Station.Player, +property: Station.Property) -> PropertyOption:
  match property:
    case Station.Property{+ref, scene, owner, generation}:
      +same = Station.Property{ref, scene, owner, generation}
      PropertyOption{ref, Station.take(expected, rules, player, same),
        Station.drop(expected, rules, player, same)}

def properties(+expected: Station.SourceVersion, +rules: Station.Rules,
    +player: Station.Player, observed: List<&2, Station.Property>) -> List<&2, PropertyOption>:
  match observed:
    case Nil{}:
      Nil{}
    case Con{property, rest}:
      Con{property_option(expected, rules, player, property), properties(expected, rules, player, rest)}

# Calling a helper to compute alternative candidates creates no native action.
# The exact public method identity is pinned later by native source-run admission.
law move_option_uses_shared_method:
  for +expected: Station.SourceVersion
  for +rules: Station.Rules
  for +player: Station.Player
  for +supply: Station.Supply
  for +edge: Station.Edge
  {moves(expected, rules, player, supply, Con{edge, Nil{}}) ==
    Con{MoveOption{edge, Station.move(expected, rules, player, supply, edge)}, Nil{}} : List<&2, MoveOption>}

def move_option_uses_shared_method(expected, rules, player, supply, edge):
  {==}
