/-
# Theory.ExceptDecidableEq -- `DecidableEq (Except ε α)` with an exposed body

Batteries derives `DecidableEq Except` inside a module section without `@[expose]`, so under the
module system its body is not in the public olean: neither `decide` nor the kernel can evaluate it
in an importing module, and every `decide` on an `Except` equality is stuck. This instance is the
same decision procedure with its body exposed; it takes priority over Batteries' where imported.
-/
module

@[expose] public section

namespace Minidregg.Theory

instance (priority := high) exceptDecidableEq {ε α : Type _} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b =>
      if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (fun e => by cases e)
  | .error _, .ok _ => isFalse (fun e => by cases e)

end Minidregg.Theory

end
