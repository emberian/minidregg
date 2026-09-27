/- Exact v1 fn consumer scope wire, factored below NativeHostReplay. -/
import Compiler.NativeHostCodec

namespace Minidregg.Kernel.FnConsumerScope

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

structure Scope where
  history : List UInt8
  incarnation : List UInt8
  consumer : List UInt8
  principal : List UInt8
  query : List UInt8
  queryVersion : Nat
  viewVersion : Nat
  registrationEpoch : Nat
  deriving DecidableEq, Repr

def scopeStream : StreamCodec Scope :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream (StreamCodec.product bytesStream
        (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))))
    (fun scope => (scope.history, scope.incarnation, scope.consumer,
      scope.principal, scope.query, scope.queryVersion, scope.viewVersion,
      scope.registrationEpoch))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1,
      wire.2.2.2.2.1, wire.2.2.2.2.2.1, wire.2.2.2.2.2.2.1,
      wire.2.2.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def maxPollScan : Nat := 16

def validName (value : List UInt8) : Bool :=
  !value.isEmpty && value.length ≤ 64

def Scope.valid (scope : Scope) : Bool :=
  [scope.history, scope.incarnation, scope.consumer, scope.principal,
    scope.query].all validName &&
  scope.queryVersion ≤ 4294967295 && scope.viewVersion ≤ 4294967295 &&
  scope.registrationEpoch > 0 && scope.registrationEpoch ≤ 4294967295

end Minidregg.Kernel.FnConsumerScope
