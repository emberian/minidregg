# Public source method exports for the canonical scalar Plan result.
# The receiver binds THIS package/export identity and its exact selected inputs.
# Source helper names are never independently granted by this method interface.
import Base
import ./SharedConsequences.bend as Station
import ./EngineeringStation.bend as Author
import ./NativePlans.bend as Bridge
import ./WorldPlanScalar.bend as World

def take(expected: Station.SourceVersion, currentSource: Station.SourceVersion,
    ruleRef: Station.Ref, player: Station.Player, property: Station.Property) -> World.PlanResult:
  Bridge.result_plan(Author.take(expected, currentSource, ruleRef, player, property))

def drop(expected: Station.SourceVersion, currentSource: Station.SourceVersion,
    ruleRef: Station.Ref, player: Station.Player, property: Station.Property) -> World.PlanResult:
  Bridge.result_plan(Author.drop(expected, currentSource, ruleRef, player, property))

def move(expected: Station.SourceVersion, currentSource: Station.SourceVersion,
    ruleRef: Station.Ref, player: Station.Player, supply: Station.Supply,
    edge: Station.Edge) -> World.PlanResult:
  Bridge.result_plan(Author.move(expected, currentSource, ruleRef, player, supply, edge))
