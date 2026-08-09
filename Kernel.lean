/-
# Kernel — the 3 verbs over the product camera (ATLAS §7).

The conservation ALGEBRA of all three verbs is landed: move (State) ·
create/gwrite (Verbs) — plain state functions + conservation/frame theorems.
The executor tier (Gate) is the kernel MODEL of the 4-leg admission gate:
Verb = admission × footprint, fail-closed admit, gate soundness
(fail-closed/conserves/frame), the first Kernel @[export]. Its footprint-Fpu
refinement and the AIR arithmetization (Compiler lane) are named residuals.
-/
import Kernel.Camera  -- the four-substance product resource algebra (the camera tier)
import Kernel.State   -- the minimal kernel state: accounts + bal + caps + one UKey map; Σ-conservation
import Kernel.Turn    -- the turn as a wide pullback (hyperedge): cone + balance, legs_agree, the binding tooth
import Kernel.TurnLimit  -- N2a: the hyperedge cone data IS a wide-pullback limit (Types.isLimit), keystones
import Kernel.TurnBalancedLimit  -- N2b: conservation as the balance equalizer over N2a's limit; the conserving turn is universal
import Kernel.DeclaredHyperedge  -- computable flat N-incidence turns jointly authorize, balance, compose, and commit one canonical post; this is the call-forest replacement carrier
import Kernel.TypedCellHyperedge  -- schema-polymorphic joint accepted effects over typed fields/resources, one validated post, and an explicit resource law
import Kernel.SparseAuthenticatedState  -- typed sparse ROM/RAM/append-only namespaces, fresh allocation, exact trace footprints/roots/bus rows
import Kernel.Receipt    -- the receipt word Q: uproj faithfulness + the frame as a receipt fact (OB-3's kernel side)
import Kernel.Verbs   -- create + gwrite: the remaining conservation-algebra verbs, conservation (honest side-conditions) + frames + the receipt bridge
import Kernel.PrivateTurn  -- the private-witness turn: the hyperedge at carrier Pub × Priv; publicView blind to the witness ([PRIVATE-TURN-kernel])
import Kernel.Gate    -- the gated executor MODEL: Verb = admission × footprint, the 4-leg fail-closed gateOK, admit + soundness (fail-closed/conserves/frame/no-TOCTOU), @[export minidregg_gate_ok]
