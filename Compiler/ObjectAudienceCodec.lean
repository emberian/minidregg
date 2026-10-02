import Theory.ObjectAudience
import Compiler.StoreCodec

namespace Minidregg.Compiler.ObjectAudienceCodec
open Minidregg.Theory.ObjectAudience
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
set_option autoImplicit false

/-- A structural sum encodes modes canonically; invalid mode tags fail decoding. -/
def modeStream : StreamCodec Mode :=
  StreamCodec.xmap (StreamCodec.sum StoreCodec.unitStream StoreCodec.unitStream)
    (fun mode => match mode with | .active => .inl () | .frozen => .inr ())
    (fun mode => match mode with | .inl _ => .active | .inr _ => .frozen)
    (by intro mode; cases mode <;> rfl)

def stateStream : StreamCodec State :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product modeStream (StreamCodec.product StreamCodec.nat StreamCodec.nat))))))))))
    (fun state => (state.object, state.epoch, state.parent, state.transition,
      state.audience, state.devices, state.history, state.manifest, state.mode, state.authoritySnapshot, state.deviceSnapshot))
    (fun (object, epoch, parent, transition, audience, devices, history, manifest, mode, authoritySnapshot, deviceSnapshot) =>
      ⟨object, epoch, parent, transition, audience, devices, history, manifest, mode, authoritySnapshot, deviceSnapshot⟩)
    (by intro state; cases state; rfl)

end Minidregg.Compiler.ObjectAudienceCodec
