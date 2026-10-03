# A larger author-owned station graph and catalog, reusable over born objects.
# Scenes0..5 Airlock/Engineering/Infirmary/Commons/Workshop/Garden.
# Catalog docslot order is a required selected-input contract, not implicit read.
import Base
import ./SharedConsequences.bend as Station
import ./WorldCatalog.bend as Catalog

# Traversal costs are authored here; all occupants consume one sampled supply.
def edges() -> List<&2, Station.Edge>:
  [Station.Edge{0n, 1n, 1n}, Station.Edge{1n, 0n, 1n},
   Station.Edge{1n, 2n, 2n}, Station.Edge{2n, 1n, 1n},
   Station.Edge{1n, 3n, 1n}, Station.Edge{3n, 1n, 1n},
   Station.Edge{3n, 4n, 1n}, Station.Edge{4n, 3n, 1n},
   Station.Edge{3n, 5n, 2n}, Station.Edge{5n, 3n, 1n},
   Station.Edge{4n, 1n, 2n}, Station.Edge{1n, 4n, 1n}]

def scenes() -> List<&2, Catalog.Scene>:
  [Catalog.Scene{0n, [65n, 105n, 114n, 108n, 111n, 99n, 107n], Nil{}, 0n},
    Catalog.Scene{1n, [69n, 110n, 103n, 105n, 110n, 101n, 101n, 114n, 105n, 110n, 103n], Nil{}, 1n},
    Catalog.Scene{2n, [73n, 110n, 102n, 105n, 114n, 109n, 97n, 114n, 121n], Nil{}, 2n},
    Catalog.Scene{3n, [67n, 111n, 109n, 109n, 111n, 110n, 115n], Nil{}, 3n},
    Catalog.Scene{4n, [87n, 111n, 114n, 107n, 115n, 104n, 111n, 112n], Nil{}, 4n},
    Catalog.Scene{5n, [71n, 97n, 114n, 100n, 101n, 110n], Nil{}, 5n}]

def catalog(source: Station.SourceVersion, ruleRef: Station.Ref,
    properties: List<&2, Catalog.Object>, supplies: List<&2, Catalog.Object>,
    roles: List<&2, Catalog.Role>) -> Catalog.Catalog:
  Catalog.catalog(source, ruleRef, scenes(), properties, supplies, roles)

def rules(source: Station.SourceVersion, ruleRef: Station.Ref) -> Station.Rules:
  Station.Rules{source, ruleRef, edges()}

def take(expected: Station.SourceVersion, source: Station.SourceVersion,
    ruleRef: Station.Ref, player: Station.Player, property: Station.Property) -> Station.Result:
  Station.take(expected, rules(source, ruleRef), player, property)

def drop(expected: Station.SourceVersion, source: Station.SourceVersion,
    ruleRef: Station.Ref, player: Station.Player, property: Station.Property) -> Station.Result:
  Station.drop(expected, rules(source, ruleRef), player, property)

def move(expected: Station.SourceVersion, source: Station.SourceVersion,
    ruleRef: Station.Ref, player: Station.Player, supply: Station.Supply,
    edge: Station.Edge) -> Station.Result:
  Station.move(expected, rules(source, ruleRef), player, supply, edge)
