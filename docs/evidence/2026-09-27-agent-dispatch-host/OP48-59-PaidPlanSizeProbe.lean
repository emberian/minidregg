import Kernel.ApplicationDispatchAgentPaidAuthoring
open Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.ApplicationDispatchAgentPaidAuthoring

def zd : Digest := ⟨0⟩
def zc : CapabilityId := ⟨0⟩
def zs : SubjectId := ⟨0⟩
def app : ApplicationDispatchCodec.App :=
  ⟨0, 0, 0, 0, 0, zd, zd, 0, 0, zd, zc⟩
def session : ApplicationDispatchCodec.Session :=
  ⟨.web, 0, 0, 0, 0, zs, zc, .agent 0 0⟩
def http : ApplicationDispatchCodec.Request :=
  ⟨0, [], [], [], [], []⟩
def base : ApplicationDispatchAuthoring.Request :=
  ⟨0, 0, 0, 0, zc, zc, zc, http⟩
def agent : ApplicationDispatchAgentAuthoring.Request :=
  ⟨base, 0, zc, zc⟩
def fixed : Request := ⟨agent, 1, zc, zc, zs, 0, 0, 0⟩
def ctx : ApplicationDispatchAgentReserveContext.Context :=
  ⟨zd, zd, app, session, 0, zd, 0, 0, 1, 0, zs, 0, 0, 0, 0, zd⟩
def paid : PaidRequest := ⟨fixed, ctx, 0⟩
def signing : NativeHostCodec.SigningPlan :=
  ⟨zd, zd, zd, 0, .invoke [], []⟩
def plan (n : Nat) : PaidPlan :=
  ⟨paid, ⟨base, List.replicate n (0 : UInt8), signing, []⟩, signing⟩
#eval let n := 8388608; let encoded := paidPlanCodec.encode (plan n); (n, encoded.length, encoded.length - n)
