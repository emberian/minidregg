# An author-owned station rule source, importing the reusable consequence law.
# The receiver binds currentSource to THIS published source artifact/export and
# ruleRef to its current rule resource. An arbitrary claimed ID is not enough.
# Scene0=airlock,1=engineering,2=infirmary. Both players draw from one oxygen store.
import Base
import ./SharedConsequences.bend as Station

# Authored graph and costs are source data, not a privileged Rust rule table.
def edges() -> List<&2, Station.Edge>:
  [Station.Edge{0n, 1n, 1n}, Station.Edge{1n, 0n, 1n},
   Station.Edge{1n, 2n, 2n}, Station.Edge{2n, 1n, 1n}]

def rules(currentSource: Station.SourceVersion, ruleRef: Station.Ref) -> Station.Rules:
  Station.Rules{currentSource, ruleRef, edges()}

def take(expected: Station.SourceVersion, currentSource: Station.SourceVersion,
    ruleRef: Station.Ref, player: Station.Player, property: Station.Property) -> Station.Result:
  Station.take(expected, rules(currentSource, ruleRef), player, property)

def drop(expected: Station.SourceVersion, currentSource: Station.SourceVersion,
    ruleRef: Station.Ref, player: Station.Player, property: Station.Property) -> Station.Result:
  Station.drop(expected, rules(currentSource, ruleRef), player, property)

def move(expected: Station.SourceVersion, currentSource: Station.SourceVersion,
    ruleRef: Station.Ref, player: Station.Player, supply: Station.Supply,
    edge: Station.Edge) -> Station.Result:
  Station.move(expected, rules(currentSource, ruleRef), player, supply, edge)

# A changed authored edge table is a new source artifact. A previous source
# identity is refused; approving that replacement does not grant installation.
law refused_old_source:
  for source: Station.SourceVersion
  for ruleRef: Station.Ref
  for player: Station.Player
  for supply: Station.Supply
  for edge: Station.Edge
  {Station.move.fin(source, ruleRef, edges(), player, supply, edge, False{}) ==
    Station.Refused{1n} : Station.Result}

def refused_old_source(source, ruleRef, player, supply, edge):
  {==}
