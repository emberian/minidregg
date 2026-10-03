# Source examples accompany the general SharedConsequences library laws.
# IDs/digests are tiny synthetic inputs, not deployed grants.
# Roots use the real native digestStream Nat codec: digits followed by255.
import Base
import ./SharedConsequences.bend as Station

def source() -> Station.SourceVersion:
  Station.SourceVersion{[1n], [2n], 1n}

def rules() -> Station.Rules:
  Station.Rules{source(), Station.Ref{1n, [11n, 255n]}, [Station.Edge{0n, 1n, 1n}]}

def alice() -> Station.Player:
  Station.Player{Station.Ref{2n, [12n, 255n]}, 7n, 0n, 0n}

def key_ground() -> Station.Property:
  Station.Property{Station.Ref{3n, [13n, 255n]}, 0n, Station.Ground{}, 0n}

def take_key() -> Station.Result:
  Station.take(source(), rules(), alice(), key_ground())

law take_key_joint:
  {take_key() == Station.Proposed{Station.Candidate{source(),
    Station.ReadRoot{Station.Ref{1n, [11n, 255n]}, Station.ReadRoot{Station.Ref{2n, [12n, 255n]}, Station.ReadRoot{Station.Ref{3n, [13n, 255n]}, Station.NoReads{}}}},
    Station.ScalarEffect{Station.Ref{2n, [12n, 255n]}, [Station.Write{1n, 0n, 1n}],
      Station.ScalarEffect{Station.Ref{3n, [13n, 255n]},
        [Station.Write{1n, 0n, 8n}, Station.Write{2n, 0n, 1n}], Station.NoEffects{}}}}} : Station.Result}

def take_key_joint():
  {==}

# Bob sees the same property, at its changed owner and changed generation/root.
# He has his own player cell; carrying an item is never replicated into it.
def bob_cannot_duplicate() -> Station.Result:
  Station.take(source(), rules(),
    Station.Player{Station.Ref{4n, [14n, 255n]}, 9n, 0n, 0n},
    Station.Property{Station.Ref{3n, [23n, 255n]}, 0n, Station.Held{7n}, 1n})

law bob_refused:
  {bob_cannot_duplicate() == Station.Refused{2n} : Station.Result}

def bob_refused():
  {==}

def move_alice() -> Station.Result:
  Station.move(source(), rules(), alice(),
    Station.Supply{Station.Ref{5n, [15n, 255n]}, 1n, 0n}, Station.Edge{0n, 1n, 1n})

law move_shared_supply:
  {move_alice() == Station.Proposed{Station.Candidate{source(),
    Station.ReadRoot{Station.Ref{1n, [11n, 255n]}, Station.ReadRoot{Station.Ref{2n, [12n, 255n]}, Station.ReadRoot{Station.Ref{5n, [15n, 255n]}, Station.NoReads{}}}},
    Station.ScalarEffect{Station.Ref{2n, [12n, 255n]},
      [Station.Write{0n, 0n, 1n}, Station.Write{1n, 0n, 1n}],
      Station.ScalarEffect{Station.Ref{5n, [15n, 255n]},
        [Station.Write{0n, 1n, 0n}, Station.Write{1n, 0n, 1n}], Station.NoEffects{}}}}} : Station.Result}

def move_shared_supply():
  {==}

def bob_no_supply() -> Station.Result:
  Station.move(source(), rules(),
    Station.Player{Station.Ref{4n, [14n, 255n]}, 9n, 0n, 0n},
    Station.Supply{Station.Ref{5n, [25n, 255n]}, 0n, 1n}, Station.Edge{0n, 1n, 1n})

law shared_shortage_refused:
  {bob_no_supply() == Station.Refused{5n} : Station.Result}

def shared_shortage_refused():
  {==}

law stale_rule_refused:
  {Station.take(Station.SourceVersion{[1n], [2n], 0n}, rules(), alice(), key_ground()) ==
    Station.Refused{1n} : Station.Result}

def stale_rule_refused():
  {==}

# A copied role target cannot masquerade as the separately held global property.
law aliased_property_refused:
  {Station.take(source(), rules(), alice(),
    Station.Property{Station.Ref{2n, [12n, 255n]}, 0n, Station.Ground{}, 0n}) ==
    Station.Refused{6n} : Station.Result}

def aliased_property_refused():
  {==}

# Alice carries the same key into engineering; dropping updates its room/owner.
def drop_key() -> Station.Result:
  Station.drop(source(), rules(),
    Station.Player{Station.Ref{2n, [22n, 255n]}, 7n, 1n, 2n},
    Station.Property{Station.Ref{3n, [23n, 255n]}, 0n, Station.Held{7n}, 1n})

law drop_key_joint:
  {drop_key() == Station.Proposed{Station.Candidate{source(),
    Station.ReadRoot{Station.Ref{1n, [11n, 255n]}, Station.ReadRoot{Station.Ref{2n, [22n, 255n]},
      Station.ReadRoot{Station.Ref{3n, [23n, 255n]}, Station.NoReads{}}}},
    Station.ScalarEffect{Station.Ref{2n, [22n, 255n]}, [Station.Write{1n, 2n, 3n}],
      Station.ScalarEffect{Station.Ref{3n, [23n, 255n]},
        [Station.Write{0n, 0n, 1n}, Station.Write{1n, 8n, 0n}, Station.Write{2n, 1n, 2n}],
        Station.NoEffects{}}}}} : Station.Result}

def drop_key_joint():
  {==}

law bob_cannot_drop_alice_key:
  {Station.drop(source(), rules(),
    Station.Player{Station.Ref{4n, [14n, 255n]}, 9n, 0n, 0n},
    Station.Property{Station.Ref{3n, [23n, 255n]}, 0n, Station.Held{7n}, 1n}) ==
    Station.Refused{8n} : Station.Result}

def bob_cannot_drop_alice_key():
  {==}
