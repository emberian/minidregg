/- Hosted conversation receiving obligations, stated before receiving proofs.
The source admission uses the generated descriptor reader; physical outcomes
must additionally instantiate these trace obligations against the native sender. -/
module
public import Effects.Revival.HostedConversation
@[expose] public section
namespace Minidregg.Effects.Revival.HostedConversation
structure Binding where
  (app subject session appGeneration sessionGeneration : Nat)
  deriving DecidableEq
structure Intent where
  binding : Binding
  operation : Nat
  preimage : List UInt8
  deriving DecidableEq
inductive Event where
  | admitted (intent : Intent)
  | retained (intent : Intent)
  | sent (intent : Intent) (bytes : List UInt8)
  | uncertain (intent : Intent)
  deriving DecidableEq
/-- A candidate receiver is judged on its own trace, not through its own decoder.
Every physical send has both current admission and exact earlier custody; an
uncertain operation can never silently send again, including after reconnect. -/
def sameOperation (a b : Intent) : Bool :=
  a.binding == b.binding && a.operation == b.operation

def checks (current : Intent → Prop) (lowers : Intent → List UInt8 → Prop)
    (before : List Event) : List Event → Prop
  | [] => True
  | event :: rest =>
    (match event with
      | .sent intent bytes =>
        current intent ∧ lowers intent bytes ∧ .admitted intent ∈ before ∧ .retained intent ∈ before ∧
          before.all (fun prior => match prior with
            | .uncertain earlier | .sent earlier _ => !sameOperation earlier intent
            | _ => true) = true
      | _ => True) ∧ checks current lowers (before ++ [event]) rest

def Receives (current : Intent → Prop) (lowers : Intent → List UInt8 → Prop)
    (trace : List Event) : Prop := checks current lowers [] trace
def Keystone (receiver : Intent → List Event) (current : Intent → Prop)
    (lowers : Intent → List UInt8 → Prop) : Prop :=
  ∀ intent, Receives current lowers (receiver intent)
def poleBinding : Binding := ⟨1, 2, 3, 4, 5⟩
def poleIntent : Intent := ⟨poleBinding, 6, [7, 8]⟩
def exactPole (intent : Intent) (bytes : List UInt8) : Prop := bytes = intent.preimage
def delivered (intent : Intent) : List Event :=
  [.admitted intent, .retained intent, .sent intent intent.preimage]
def replayed (intent : Intent) : List Event :=
  delivered intent ++ [.uncertain intent, .sent intent intent.preimage]
def ghost (intent : Intent) : List Event :=
  [.admitted intent, .retained intent, .sent intent [9]]
def Satisfiable : Prop := Receives (fun _ => True) exactPole (delivered poleIntent)
def Teeth : Prop :=
  ¬ Receives (fun _ => False) exactPole (delivered poleIntent) ∧
  ¬ Receives (fun _ => True) exactPole (replayed poleIntent) ∧
  ¬ Receives (fun _ => True) exactPole [.admitted poleIntent, .sent poleIntent poleIntent.preimage] ∧
  ¬ Receives (fun _ => True) exactPole (ghost poleIntent)
def Premise : Prop := ∃ current intent, current intent ∧ Receives current exactPole (delivered intent)
end Minidregg.Effects.Revival.HostedConversation
