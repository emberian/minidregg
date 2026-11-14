/- The actual declaration's gate, including inhabited poles, before proofs. -/
module
public import Effects.Revival.HostedConversationEngine
@[expose] public section
namespace Minidregg.Effects.Revival.HostedConversationEngine
open HostedLifecycle
/-- No legacy hand arm is allowed beside the lifecycle declaration. -/
def Keystone : Prop :=
  Dispatches receivingRegistry [] (dispatch receivingRegistry) ∧ receivingHandler.Lawful

def context : Context := ⟨true,true,true,false,false,[]⟩
def openOperation : Operation := ⟨0,0,[1],[2],[3]⟩
def Satisfiable : Prop :=
  ∃ state, receive context openOperation {} = .ok state ∧ state.emitted = some openOperation ∧
    state.pending = some openOperation ∧ state.receipt = none

def Teeth : Prop :=
  receive {context with current := false} openOperation {} =
    .error (.refused 0 "currentAuthority" .empty) ∧
  receive {context with retained := false} openOperation {} =
    .error (.refused 0 "exactPreimage" .empty) ∧
  (∀ state, receive context openOperation {} = .ok state →
    receive context openOperation state = .error (.refused 0 "channelState" .empty))

def Premise : Prop := ∃ ctx : Context, ctx.current = true ∧ ctx.retained = true ∧ ctx.budget = true
end Minidregg.Effects.Revival.HostedConversationEngine
