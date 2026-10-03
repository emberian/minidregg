# Closed source values for actual source-machine/Plan-decoder receiving checks.
# These synthetic resource IDs/digests prove no current grants or installation.
import Base
import ./Receiving.bend as Example
import ./NativePlans.bend as Bridge
import ./WorldPlanScalar.bend as World

def take_key_plan() -> World.PlanResult:
  Bridge.result_plan(Example.take_key())

def held_key_refusal() -> World.PlanResult:
  Bridge.result_plan(Example.bob_cannot_duplicate())

def move_plan() -> World.PlanResult:
  Bridge.result_plan(Example.move_alice())

def exhausted_supply_refusal() -> World.PlanResult:
  Bridge.result_plan(Example.bob_no_supply())

law source_refusal_retained:
  {held_key_refusal() == World.Refused{2n} : World.PlanResult}

def source_refusal_retained():
  {==}

law source_take_plan_exact:
  {take_key_plan() == World.Planned{World.NativePlan{
    [World.Ref{1n, [11n, 255n]}, World.Ref{2n, [12n, 255n]}, World.Ref{3n, [13n, 255n]}],
    [World.ScalarEffect{World.Ref{2n, [12n, 255n]}, [World.Write{1n, 0n, 1n}]},
     World.ScalarEffect{World.Ref{3n, [13n, 255n]},
       [World.Write{1n, 0n, 8n}, World.Write{2n, 0n, 1n}]}]}} : World.PlanResult}

def source_take_plan_exact():
  {==}
