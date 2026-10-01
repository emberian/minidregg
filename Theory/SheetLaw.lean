/-
# Theory.SheetLaw — the MUD sheet law, as written, judged by the kernel

`deploy/shell/templates/mud/sheet/law.sheet.json` (branch `mud-law-fix`, commit `8280b8d7`), composed
as the templates' README says: `all [law.management, clause 1, …, clause 33]`. §2 is that JSON written
out as a `Pred` term, one `def` per clause, placeholder `{X}` ↦ `p.X`; nothing is re-sorted, dropped or
simplified. §2 is generated, not hand-edited: the mechanical embed (one recursive render of the JSON
predicate tree) reproduces `1ee44ed`'s §2 byte for byte from `1ee44ed`'s JSON, and this §2 from
`8280b8d7`'s. Slot spellings are the renderer's: `field NAME view` ↦ `resource/field/{n}/{view}` by
`sheet/fields.json`, `joint I KIND NAME view` ↦ `joint/index/{I}/resource/field/{n}/{view}`,
`clock now` ↦ `clock/now`.

What the kernel supplies on this branch. `DeclaredResourceController.step` gives the policy
`old = project(pre, pre)` and `new = project(pre, post)` (`DeclaredResourceProjection.scalarSlots`),
behind the request slots, plus `joint/target/{target}/…` slots for the other legs. It supplies **no
`clock/now` slot** (K-CLOCK) and **no `joint/index/…` slot** (K-JOINT-INDEX). Absent slots fail closed,
so on this branch:

* clauses 10, 11, 19, 23 (clock) and 14–18, 26, 27 (joint) refuse whenever their guarded branch is
  needed. Consequences proved below: the referee cannot lower hp at all (`combat_death_refused_without_joint`),
  the owner cannot declare a strike (`owner_strike_refused_without_clock`), and **no one can revive a
  dead sheet** (`revive_needs_clock`, `dead_stays_dead_without_clock`);
* clauses 25, 27, 28 and 29 state their timers positively (`leSlotsOff clock/now … NEG_…`), so a
  missing clock refuses them too: no death without the clock (`death_needs_clock`). On `1ee44ed`
  they wrapped the atom in `not`, which passed while the clock was absent.

The slot-to-slot atoms (`eqSlots`, `leSlots`, `leSlotsOff`) are k-sloteq's and k-offset's, merged into
this branch for these laws; wave-c alone cannot express either law.

§6 models the kernel's view with the clock and `joint/index` slots as optional extras, so the poles
that need K-CLOCK / K-JOINT-INDEX are stated with them present, and the wave-c poles without.

Counterexample found on `1ee44ed`'s law (`referee_kills_healthy_sheet`): no clause tied a death to hp,
so the referee could write `alive 1 → 0, deaths +1` on a sheet at full hp with no attacker. Clause 33
(`alive 1 → 0 ⇒ hp ≤ 0`, `death_needs_hp`) closes it: `smite_refused`, while
`death_reachable_by_strike` still admits the combat death.

The kernel theorems (§5) are over `DeclaredResourceController.CheckedLeg`, the per-leg record every
`AcceptedInvocation` carries: its `Authorized` value forces the committed predicate to hold on
`step prepared tuple incidence` (`canonical_context_verifies_sound`), so whatever the sheet law
implies of an (old, new) pair holds of every admitted leg whose installed law is the sheet law.
-/
import Pred.Core
import Kernel.DeclaredResourceController

namespace Minidregg.Theory.SheetLaw

open Minidregg.Pred (Pred State eval)
open Minidregg.Kernel.DeclaredResourceProjection (Values fieldName pairName scalarSlots)
set_option autoImplicit false

/-! ## §1. The realm constants the law is instantiated at -/

/-- The `{UPPER}` placeholders of `law.management ; law.sheet`. -/
structure Params where
  S : Int
  REF : Int
  W_FOUNDER : Int
  MAXHIT_LT : Int
  HPMAX : Int
  HOME : Int
  NEG_RESPAWN : Int
  NEG_COST : Int
  NEG_ECOST : Int
  LANTERN : Int

/-! ## §2. The law, literally (`law.management.json`, then `sheet/law.sheet.json` clauses 1–33) -/

section Law
set_option linter.unusedVariables false

def management (p : Params) : Pred :=
  Pred.any [
    .eq "request/verb" 1,
    .eq "request/verb" 2,
    Pred.all [
      .memberOf "request/verb" [3, 4, 5],
      .eq "request/subject" p.W_FOUNDER]]

/-- clause 1 -/
def sheetClause1 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .eq "request/subject" p.S,
    .eq "request/subject" p.REF]

/-- clause 2 -/
def sheetClause2 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .eq "resource/field/0/after" p.S]

/-- clause 3 -/
def sheetClause3 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    Pred.all [
      .memberOf "resource/field/5/after" [0, 1],
      .memberOf "resource/field/7/after" [0, 1, 2, 3, 4, 9],
      .memberOf "resource/field/10/after" [0, 1],
      .memberOf "resource/field/11/after" [0, 1],
      .memberOf "resource/field/12/after" [0, 1],
      .memberOf "resource/field/13/after" [0, 1],
      .memberOf "resource/field/14/after" [0, 1, 2, 3, 4, 5]]]

/-- clause 4 -/
def sheetClause4 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .monotone "resource/field/6/after"]

/-- clause 5 -/
def sheetClause5 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .eq "resource/field/6/delta" 0,
    Pred.all [
      .eq "resource/field/5/before" 1,
      .eq "resource/field/5/after" 0,
      .eq "resource/field/6/delta" 1]]

/-- clause 6 -/
def sheetClause6 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.le "resource/field/2/after" 0),
    .eq "resource/field/5/after" 0]

/-- clause 7 -/
def sheetClause7 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.S),
    .eq "resource/field/5/before" 1,
    Pred.all [
      .eq "resource/field/7/after" 9,
      .eq "resource/field/1/delta" 0,
      .eq "resource/field/8/delta" 0]]

/-- clause 8 -/
def sheetClause8 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.S),
    Pred.all [
      .eq "resource/field/2/delta" 0,
      .eq "resource/field/3/delta" 0,
      .eq "resource/field/4/delta" 0,
      .eq "resource/field/5/delta" 0,
      .eq "resource/field/6/delta" 0,
      .eq "resource/field/9/delta" 0,
      .eq "resource/field/10/delta" 0,
      .eq "resource/field/11/delta" 0,
      .eq "resource/field/12/delta" 0,
      .eq "resource/field/13/delta" 0]]

/-- clause 9 -/
def sheetClause9 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.S),
    .not (.eq "resource/field/7/after" 9),
    .eq "resource/field/5/before" 0]

/-- clause 10 -/
def sheetClause10 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.S),
    .not (.memberOf "resource/field/7/after" [1, 3, 4]),
    .leSlots "resource/field/3/before" "clock/now"]

/-- clause 11 -/
def sheetClause11 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.S),
    .not (.eq "resource/field/7/after" 2),
    .leSlots "resource/field/4/before" "clock/now"]

/-- clause 12 -/
def sheetClause12 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.S),
    .eq "resource/field/11/before" 0,
    Pred.all [
      .not (.memberOf "resource/field/7/after" [1, 3, 4]),
      .eq "resource/field/1/delta" 0]]

/-- clause 13 -/
def sheetClause13 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.S),
    .not (.eq "resource/field/7/after" 2),
    .eq "resource/field/10/before" 0]

/-- clause 14 -/
def sheetClause14 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.S),
    .eq "resource/field/1/delta" 0,
    .eqSlots "resource/field/1/before" "joint/index/1/resource/field/0/after"]

/-- clause 15 -/
def sheetClause15 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.S),
    .eq "resource/field/1/delta" 0,
    .eqSlots "resource/field/1/after" "joint/index/2/resource/field/0/after"]

/-- clause 16 -/
def sheetClause16 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.S),
    .eq "resource/field/1/delta" 0,
    Pred.any [
      .eqSlots "joint/index/1/resource/field/8/after" "joint/index/2/resource/field/0/after",
      .eqSlots "joint/index/1/resource/field/11/after" "joint/index/2/resource/field/0/after",
      .eqSlots "joint/index/1/resource/field/14/after" "joint/index/2/resource/field/0/after",
      .eqSlots "joint/index/1/resource/field/17/after" "joint/index/2/resource/field/0/after",
      .eqSlots "joint/index/1/resource/field/20/after" "joint/index/2/resource/field/0/after",
      .eqSlots "joint/index/1/resource/field/23/after" "joint/index/2/resource/field/0/after",
      .eqSlots "joint/index/1/resource/field/26/after" "joint/index/2/resource/field/0/after",
      .eqSlots "joint/index/1/resource/field/29/after" "joint/index/2/resource/field/0/after",
      .eqSlots "joint/index/1/resource/field/32/after" "joint/index/2/resource/field/0/after",
      .eqSlots "joint/index/1/resource/field/35/after" "joint/index/2/resource/field/0/after",
      .eqSlots "joint/index/1/resource/field/38/after" "joint/index/2/resource/field/0/after",
      .eqSlots "joint/index/1/resource/field/41/after" "joint/index/2/resource/field/0/after"]]

/-- clause 17 -/
def sheetClause17 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.S),
    .eq "resource/field/1/delta" 0,
    Pred.all [
      Pred.any [
        .not (.eqSlots "joint/index/1/resource/field/8/after" "joint/index/2/resource/field/0/after"),
        .eq "joint/index/1/resource/field/9/after" 0,
        Pred.all [
          .eqSlots "joint/index/1/resource/field/10/after" "joint/index/3/resource/field/0/after",
          .eqSlots "joint/index/3/resource/field/2/after" "request/subject"]],
      Pred.any [
        .not (.eqSlots "joint/index/1/resource/field/11/after" "joint/index/2/resource/field/0/after"),
        .eq "joint/index/1/resource/field/12/after" 0,
        Pred.all [
          .eqSlots "joint/index/1/resource/field/13/after" "joint/index/3/resource/field/0/after",
          .eqSlots "joint/index/3/resource/field/2/after" "request/subject"]],
      Pred.any [
        .not (.eqSlots "joint/index/1/resource/field/14/after" "joint/index/2/resource/field/0/after"),
        .eq "joint/index/1/resource/field/15/after" 0,
        Pred.all [
          .eqSlots "joint/index/1/resource/field/16/after" "joint/index/3/resource/field/0/after",
          .eqSlots "joint/index/3/resource/field/2/after" "request/subject"]],
      Pred.any [
        .not (.eqSlots "joint/index/1/resource/field/17/after" "joint/index/2/resource/field/0/after"),
        .eq "joint/index/1/resource/field/18/after" 0,
        Pred.all [
          .eqSlots "joint/index/1/resource/field/19/after" "joint/index/3/resource/field/0/after",
          .eqSlots "joint/index/3/resource/field/2/after" "request/subject"]],
      Pred.any [
        .not (.eqSlots "joint/index/1/resource/field/20/after" "joint/index/2/resource/field/0/after"),
        .eq "joint/index/1/resource/field/21/after" 0,
        Pred.all [
          .eqSlots "joint/index/1/resource/field/22/after" "joint/index/3/resource/field/0/after",
          .eqSlots "joint/index/3/resource/field/2/after" "request/subject"]],
      Pred.any [
        .not (.eqSlots "joint/index/1/resource/field/23/after" "joint/index/2/resource/field/0/after"),
        .eq "joint/index/1/resource/field/24/after" 0,
        Pred.all [
          .eqSlots "joint/index/1/resource/field/25/after" "joint/index/3/resource/field/0/after",
          .eqSlots "joint/index/3/resource/field/2/after" "request/subject"]],
      Pred.any [
        .not (.eqSlots "joint/index/1/resource/field/26/after" "joint/index/2/resource/field/0/after"),
        .eq "joint/index/1/resource/field/27/after" 0,
        Pred.all [
          .eqSlots "joint/index/1/resource/field/28/after" "joint/index/3/resource/field/0/after",
          .eqSlots "joint/index/3/resource/field/2/after" "request/subject"]],
      Pred.any [
        .not (.eqSlots "joint/index/1/resource/field/29/after" "joint/index/2/resource/field/0/after"),
        .eq "joint/index/1/resource/field/30/after" 0,
        Pred.all [
          .eqSlots "joint/index/1/resource/field/31/after" "joint/index/3/resource/field/0/after",
          .eqSlots "joint/index/3/resource/field/2/after" "request/subject"]],
      Pred.any [
        .not (.eqSlots "joint/index/1/resource/field/32/after" "joint/index/2/resource/field/0/after"),
        .eq "joint/index/1/resource/field/33/after" 0,
        Pred.all [
          .eqSlots "joint/index/1/resource/field/34/after" "joint/index/3/resource/field/0/after",
          .eqSlots "joint/index/3/resource/field/2/after" "request/subject"]],
      Pred.any [
        .not (.eqSlots "joint/index/1/resource/field/35/after" "joint/index/2/resource/field/0/after"),
        .eq "joint/index/1/resource/field/36/after" 0,
        Pred.all [
          .eqSlots "joint/index/1/resource/field/37/after" "joint/index/3/resource/field/0/after",
          .eqSlots "joint/index/3/resource/field/2/after" "request/subject"]],
      Pred.any [
        .not (.eqSlots "joint/index/1/resource/field/38/after" "joint/index/2/resource/field/0/after"),
        .eq "joint/index/1/resource/field/39/after" 0,
        Pred.all [
          .eqSlots "joint/index/1/resource/field/40/after" "joint/index/3/resource/field/0/after",
          .eqSlots "joint/index/3/resource/field/2/after" "request/subject"]],
      Pred.any [
        .not (.eqSlots "joint/index/1/resource/field/41/after" "joint/index/2/resource/field/0/after"),
        .eq "joint/index/1/resource/field/42/after" 0,
        Pred.all [
          .eqSlots "joint/index/1/resource/field/43/after" "joint/index/3/resource/field/0/after",
          .eqSlots "joint/index/3/resource/field/2/after" "request/subject"]]]]

/-- clause 18 -/
def sheetClause18 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.S),
    .eq "resource/field/1/delta" 0,
    .eq "joint/index/2/resource/field/2/after" 0,
    Pred.all [
      .eq "joint/index/3/resource/field/1/after" p.LANTERN,
      .eqSlots "joint/index/3/resource/field/2/after" "request/subject",
      .not (.le "joint/index/3/resource/field/5/after" 0)],
    Pred.all [
      .eq "joint/index/4/resource/field/1/after" p.LANTERN,
      .eqSlots "joint/index/4/resource/field/2/after" "request/subject",
      .not (.le "joint/index/4/resource/field/5/after" 0)]]

/-- clause 19 -/
def sheetClause19 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.S),
    .eq "resource/field/1/delta" 0,
    .eq "joint/index/2/resource/field/3/after" 0,
    .leSlots "clock/now" "joint/index/2/resource/field/4/after"]

/-- clause 20 -/
def sheetClause20 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.REF),
    .eq "resource/field/1/delta" 0,
    Pred.all [
      .eq "resource/field/5/before" 0,
      .eq "resource/field/5/after" 1]]

/-- clause 21 -/
def sheetClause21 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.REF),
    .le "resource/field/2/delta" 0,
    Pred.all [
      .eq "resource/field/5/before" 0,
      .eq "resource/field/5/after" 1]]

/-- clause 22 -/
def sheetClause22 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.REF),
    .not (.le "resource/field/2/delta" p.MAXHIT_LT)]

/-- clause 23 -/
def sheetClause23 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (Pred.all [
        .eq "resource/field/5/before" 0,
        .eq "resource/field/5/after" 1]),
    Pred.all [
      .eq "request/subject" p.REF,
      .eq "resource/field/7/before" 9,
      .leSlots "resource/field/9/before" "clock/now",
      .eq "resource/field/2/after" p.HPMAX,
      .eq "resource/field/1/after" p.HOME,
      .eq "resource/field/7/after" 0]]

/-- clause 24 -/
def sheetClause24 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .eq "resource/field/9/delta" 0,
    Pred.all [
      .eq "resource/field/5/before" 1,
      .eq "resource/field/5/after" 0]]

/-- clause 25 -/
def sheetClause25 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (Pred.all [
        .eq "resource/field/5/before" 1,
        .eq "resource/field/5/after" 0]),
    .leSlotsOff "clock/now" "resource/field/9/after" p.NEG_RESPAWN]

/-- clause 26 -/
def sheetClause26 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    Pred.all [
      .not (.le "resource/field/2/delta" (-1)),
      .le "resource/field/10/delta" 0,
      .le "resource/field/11/delta" 0,
      .le "resource/field/12/delta" 0],
    Pred.all [
      .eq "resource/field/5/before" 1,
      .memberOf "joint/index/0/resource/field/7/before" [1, 2],
      .eqSlots "joint/index/0/resource/field/8/before" "resource/field/0/after",
      .eq "joint/index/0/resource/field/5/before" 1,
      .eqSlots "joint/index/0/resource/field/1/after" "resource/field/1/after"]]

/-- clause 27 -/
def sheetClause27 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    Pred.all [
      .not (.le "resource/field/2/delta" (-1)),
      .le "resource/field/10/delta" 0,
      .le "resource/field/11/delta" 0,
      .le "resource/field/12/delta" 0],
    Pred.all [
      .eq "joint/index/0/resource/field/7/before" 1,
      .leSlots "joint/index/0/resource/field/3/before" "clock/now",
      .leSlotsOff "clock/now" "joint/index/0/resource/field/3/after" p.NEG_COST],
    Pred.all [
      .eq "joint/index/0/resource/field/7/before" 2,
      .leSlots "joint/index/0/resource/field/4/before" "clock/now",
      .leSlotsOff "clock/now" "joint/index/0/resource/field/4/after" p.NEG_ECOST]]

/-- clause 28 -/
def sheetClause28 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.REF),
    .eq "resource/field/3/delta" 0,
    Pred.all [
      .memberOf "resource/field/7/before" [1, 3, 4],
      .not (.le "resource/field/3/delta" (-1)),
      .leSlotsOff "clock/now" "resource/field/3/after" p.NEG_COST]]

/-- clause 29 -/
def sheetClause29 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.REF),
    .eq "resource/field/4/delta" 0,
    Pred.all [
      .eq "resource/field/7/before" 2,
      .not (.le "resource/field/4/delta" (-1)),
      .leSlotsOff "clock/now" "resource/field/4/after" p.NEG_ECOST]]

/-- clause 30 -/
def sheetClause30 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.REF),
    Pred.all [
      .eq "resource/field/7/delta" 0,
      .eq "resource/field/8/delta" 0,
      .eq "resource/field/14/delta" 0],
    Pred.all [
      .eq "resource/field/7/after" 0,
      .eq "resource/field/8/after" 0,
      .eq "resource/field/14/after" 0]]

/-- clause 31 -/
def sheetClause31 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .eq "resource/field/13/before" 0,
    .le "resource/field/11/delta" 0]

/-- clause 32 -/
def sheetClause32 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .le "resource/field/13/delta" 0,
    .eq "resource/field/7/before" 3]

/-- clause 33 -/
def sheetClause33 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (Pred.all [
        .eq "resource/field/5/before" 1,
        .eq "resource/field/5/after" 0]),
    .le "resource/field/2/after" 0]


end Law

/-- The installed sheet law: management is clause 0, then clauses 1–33 in file order. -/
def sheetClauses (p : Params) : List Pred :=
  [management p,
   sheetClause1 p, sheetClause2 p, sheetClause3 p, sheetClause4 p, sheetClause5 p, sheetClause6 p, sheetClause7 p, sheetClause8 p,
   sheetClause9 p, sheetClause10 p, sheetClause11 p, sheetClause12 p, sheetClause13 p, sheetClause14 p, sheetClause15 p, sheetClause16 p,
   sheetClause17 p, sheetClause18 p, sheetClause19 p, sheetClause20 p, sheetClause21 p, sheetClause22 p, sheetClause23 p, sheetClause24 p,
   sheetClause25 p, sheetClause26 p, sheetClause27 p, sheetClause28 p, sheetClause29 p, sheetClause30 p, sheetClause31 p, sheetClause32 p,
   sheetClause33 p]

def sheetLaw (p : Params) : Pred := Pred.all (sheetClauses p)

/-! ## §3. Reading atoms as propositions -/

section Atoms
variable {o n : State}

theorem ev_eq {s : String} {v : Int} : eval (.eq s v) o n = true ↔ n.get s = some v := by
  simp [eval, Minidregg.Pred.evalWith]

theorem ev_le {s : String} {v : Int} :
    eval (.le s v) o n = true ↔ ∃ x, n.get s = some x ∧ x ≤ v := by
  simp only [eval, Minidregg.Pred.evalWith]; cases n.get s <;> simp

theorem ev_memberOf {s : String} {xs : List Int} :
    eval (.memberOf s xs) o n = true ↔ ∃ x, n.get s = some x ∧ x ∈ xs := by
  simp only [eval, Minidregg.Pred.evalWith]; cases n.get s <;> simp

theorem ev_monotone {s : String} :
    eval (.monotone s) o n = true ↔ ∃ a b, o.get s = some a ∧ n.get s = some b ∧ a ≤ b := by
  simp only [eval, Minidregg.Pred.evalWith]; cases o.get s <;> cases n.get s <;> simp

theorem ev_eqSlots {a b : String} :
    eval (.eqSlots a b) o n = true ↔ ∃ x, n.get a = some x ∧ n.get b = some x := by
  simp only [eval, Minidregg.Pred.evalWith]; cases n.get a <;> cases n.get b <;> simp [eq_comm]

theorem ev_leSlots {a b : String} :
    eval (.leSlots a b) o n = true ↔ ∃ x y, n.get a = some x ∧ n.get b = some y ∧ x ≤ y := by
  simp only [eval, Minidregg.Pred.evalWith]; cases n.get a <;> cases n.get b <;> simp [eq_comm]

theorem ev_leSlotsOff {a b : String} {k : Int} :
    eval (.leSlotsOff a b k) o n = true ↔
      ∃ x y, n.get a = some x ∧ n.get b = some y ∧ x ≤ y + k := by
  simp only [eval, Minidregg.Pred.evalWith]; cases n.get a <;> cases n.get b <;> simp

theorem ev_not {q : Pred} : eval (.not q) o n = true ↔ ¬ eval q o n = true := by
  simp [Minidregg.Pred.eval_not]

theorem ev_all {ps : List Pred} : eval (Pred.all ps) o n = true ↔ ∀ q ∈ ps, eval q o n = true := by
  simp [Minidregg.Pred.eval_all]

theorem ev_any {ps : List Pred} : eval (Pred.any ps) o n = true ↔ ∃ q ∈ ps, eval q o n = true := by
  simp [Minidregg.Pred.eval_any]

end Atoms

/-- A clause of an admitted sheet step holds. -/
theorem sheet_clause {p : Params} {o n : State} (h : eval (sheetLaw p) o n = true) {q : Pred}
    (hq : q ∈ sheetClauses p) : eval q o n = true :=
  ev_all.mp h q hq

/-! ## §4. Law-level consequences: every (old, new) pair the sheet law admits -/

/-- **`stranger_write_bounded`** (law form). A subject that is neither the sheet's owner nor the
referee has no admitted `mutate` (verb 2) at all: the fields the law leaves open to strangers are
none. What such a subject may still do is observe (verb 1), and the founder alone may
delegate/install/revoke (verbs 3–5). -/
theorem stranger_write_bounded (p : Params) (o n : State) (x : Int)
    (admitted : eval (sheetLaw p) o n = true) (subject : n.get "request/subject" = some x)
    (notOwner : x ≠ p.S) (notReferee : x ≠ p.REF) :
    n.get "request/verb" = some 1 ∨
      (x = p.W_FOUNDER ∧ ∃ v ∈ [(3 : Int), 4, 5], n.get "request/verb" = some v) := by
  have c0 := sheet_clause admitted (q := management p) (by simp [sheetClauses])
  have c1 := sheet_clause admitted (q := sheetClause1 p) (by simp [sheetClauses])
  simp only [management, sheetClause1, ev_any, ev_all, ev_not, ev_eq, ev_memberOf,
    List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, subject,
    Option.some.injEq, forall_eq_or_imp, forall_eq] at c0 c1
  rcases c1 with c1 | c1 | c1
  · rcases c0 with c0 | c0 | ⟨⟨v, hv, mem⟩, hf⟩
    · exact .inl c0
    · exact absurd c0 c1
    · exact .inr ⟨hf, v, by simpa using mem, hv⟩
  · exact absurd c1 notOwner
  · exact absurd c1 notReferee

/-- **Clause 4 (deaths-monotone), per step.** Every admitted mutate carries a `deaths` value in both
views and the new one is not smaller. -/
theorem deaths_monotone_step (p : Params) (o n : State)
    (admitted : eval (sheetLaw p) o n = true) (verb : n.get "request/verb" = some 2) :
    ∃ a b, o.get "resource/field/6/after" = some a ∧ n.get "resource/field/6/after" = some b ∧
      a ≤ b := by
  have c4 := sheet_clause admitted (q := sheetClause4 p) (by simp [sheetClauses])
  simp only [sheetClause4, ev_any, ev_not, ev_eq, ev_monotone, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left, verb, not_true_eq_false, false_or] at c4
  exact c4

/-- **Clause 3 (range), the `alive` part.** An admitted mutate leaves `alive ∈ {0, 1}`. -/
theorem alive_after_range (p : Params) (o n : State)
    (admitted : eval (sheetLaw p) o n = true) (verb : n.get "request/verb" = some 2) :
    ∃ x, n.get "resource/field/5/after" = some x ∧ (x = 0 ∨ x = 1) := by
  have c3 := sheet_clause admitted (q := sheetClause3 p) (by simp [sheetClauses])
  simp only [sheetClause3, ev_any, ev_all, ev_not, ev_eq, ev_memberOf, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, verb, not_true_eq_false,
    false_or, forall_eq_or_imp, forall_eq] at c3
  obtain ⟨⟨x, hx, mem⟩, -⟩ := c3
  exact ⟨x, hx, by simpa using mem⟩

/-- **Clause 23 (revive): the only way `alive` rises.** An admitted mutate that takes `alive` from
0 to 1 was written by the referee, after a prayer (`intent` before = 9), at or after the respawn
time on the clock, to full hp, at HOME, clearing the intent. -/
theorem alive_raised_only_by_revive (p : Params) (o n : State)
    (admitted : eval (sheetLaw p) o n = true) (verb : n.get "request/verb" = some 2)
    (wasDead : n.get "resource/field/5/before" = some 0)
    (nowAlive : n.get "resource/field/5/after" = some 1) :
    n.get "request/subject" = some p.REF ∧ n.get "resource/field/7/before" = some 9 ∧
      (∃ r t, n.get "resource/field/9/before" = some r ∧ n.get "clock/now" = some t ∧ r ≤ t) ∧
      n.get "resource/field/2/after" = some p.HPMAX ∧
      n.get "resource/field/1/after" = some p.HOME ∧
      n.get "resource/field/7/after" = some 0 := by
  have c23 := sheet_clause admitted (q := sheetClause23 p) (by simp [sheetClauses])
  simp only [sheetClause23, ev_any, ev_all, ev_not, ev_eq, ev_leSlots, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, verb, wasDead, nowAlive,
    not_true_eq_false, false_or, forall_eq_or_imp, forall_eq, and_self] at c23
  obtain ⟨hs, hi, ⟨r, t, hr, ht, hle⟩, hh, ha, hi'⟩ := c23
  exact ⟨hs, hi, ⟨r, t, hr, ht, hle⟩, hh, ha, hi'⟩

/-- Without a `clock/now` slot (this branch: K-CLOCK has not landed) no admitted mutate raises
`alive`: a dead sheet cannot be revived by anyone. -/
theorem revive_needs_clock (p : Params) (o n : State) (verb : n.get "request/verb" = some 2)
    (noClock : n.get "clock/now" = none)
    (wasDead : n.get "resource/field/5/before" = some 0)
    (nowAlive : n.get "resource/field/5/after" = some 1) :
    eval (sheetLaw p) o n = false := by
  apply Bool.eq_false_iff.mpr
  intro admitted
  obtain ⟨-, -, ⟨r, t, -, ht, -⟩, -⟩ := alive_raised_only_by_revive p o n admitted verb wasDead nowAlive
  rw [noClock] at ht
  cases ht

/-- The owner (when it is not also the referee) never raises its own `alive`. -/
theorem owner_cannot_raise_alive (p : Params) (o n : State) (distinct : p.S ≠ p.REF)
    (verb : n.get "request/verb" = some 2) (owner : n.get "request/subject" = some p.S)
    (wasDead : n.get "resource/field/5/before" = some 0)
    (nowAlive : n.get "resource/field/5/after" = some 1) :
    eval (sheetLaw p) o n = false := by
  apply Bool.eq_false_iff.mpr
  intro admitted
  obtain ⟨hs, -⟩ := alive_raised_only_by_revive p o n admitted verb wasDead nowAlive
  rw [owner] at hs
  exact distinct (Option.some.inj hs)

/-! ## §6. The kernel's view of one step over the declared field store

`view t pre post` is the slot list `DeclaredResourceController.projectWithCommon` hands the policy for
the primary target, restricted to what this law reads: the two request slots it names
(`CanonicalRuntimeProfile.requestSlots` spells them `request/verb`, `request/subject`), then the
target's own `scalarSlots pre post` (the kernel function, not a copy), then the slots that have not
landed: `clock/now` (K-CLOCK) and `joint/index/{i}/resource/field/{n}/{view}` (K-JOINT-INDEX), each
optional. The policy's old state is `view t pre pre` and its new state `view t pre post`
(`PolicyStepContext.ofPreparedTuple`: `project logicalPre`, `project logicalPost`, both against the
pre-state). The lookup lemmas below prove that the names the law reads resolve to the store values,
whatever the store holds. -/

/-- The request slots the law reads. -/
def request (verb subject : Int) : List (String × Int) :=
  [("request/verb", verb), ("request/subject", subject)]

/-- K-CLOCK's slot, when it is present. -/
def clockSlots : Option Int → List (String × Int)
  | none => []
  | some t => [("clock/now", t)]

/-- K-JOINT-INDEX's slot name, as `render.py` spells it. -/
def jointName (i n : Nat) (v : String) : String := s!"joint/index/{i}/resource/field/{n}/{v}"

def jointSlots (j : List (Nat × Nat × String × Int)) : List (String × Int) :=
  j.map fun q => (jointName q.1 q.2.1 q.2.2.1, q.2.2.2)

/-- One mutate or observe on the cell: who, which verb, the clock and joint slots the step exposes
(empty on this branch), and the post-state of the declared fields. -/
structure Turn where
  verb : Int
  subject : Int
  now : Option Int
  joint : List (Nat × Nat × String × Int)
  post : Values

def view (t : Turn) (pre post : Values) : State :=
  ⟨request t.verb t.subject ++ scalarSlots pre post ++ clockSlots t.now ++ jointSlots t.joint⟩

/-- The law's verdict on a turn from `pre`. -/
def admits (law : Pred) (pre : Values) (t : Turn) : Bool :=
  eval law (view t pre pre) (view t pre t.post)

section Names

def lastc (s : String) : Option Char := s.toList.getLast?
def headc (s : String) : Option Char := s.toList.head?

theorem lastc_append (s t : String) (h : t.toList ≠ []) : lastc (s ++ t) = lastc t := by
  unfold lastc
  rw [String.toList_append, List.getLast?_append]
  cases hl : t.toList.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hl) h
  | some c => rfl

theorem headc_append (s t : String) (h : s.toList ≠ []) : headc (s ++ t) = headc s := by
  unfold headc
  rw [String.toList_append]
  cases hs : s.toList with
  | nil => exact absurd hs h
  | cons c cs => rfl

theorem ne_of_lastc {s t : String} (h : lastc s ≠ lastc t) : s ≠ t := fun e => h (congrArg lastc e)
theorem ne_of_headc {s t : String} (h : headc s ≠ headc t) : s ≠ t := fun e => h (congrArg headc e)

theorem fieldName_def (N : Nat) (v : String) :
    fieldName N v = "resource/field/" ++ toString N ++ "/" ++ v := rfl

theorem pairName_def (a b : Nat) :
    pairName a b = "resource/pair/" ++ toString a ++ "/" ++ toString b ++ "/delta" := rfl

theorem jointName_def (i n : Nat) (v : String) :
    jointName i n v = "joint/index/" ++ toString i ++ "/resource/field/" ++ toString n ++ "/" ++ v :=
  rfl

theorem lastc_fieldName (N : Nat) (v : String) (h : v.toList ≠ []) :
    lastc (fieldName N v) = lastc v := by
  rw [fieldName_def]; exact lastc_append _ _ h

theorem lastc_after (N : Nat) : lastc (fieldName N "after") = some 'r' := by
  rw [lastc_fieldName _ _ (by decide)]; decide
theorem lastc_before (N : Nat) : lastc (fieldName N "before") = some 'e' := by
  rw [lastc_fieldName _ _ (by decide)]; decide
theorem lastc_delta (N : Nat) : lastc (fieldName N "delta") = some 'a' := by
  rw [lastc_fieldName _ _ (by decide)]; decide
theorem lastc_pairName (a b : Nat) : lastc (pairName a b) = some 'a' := by
  rw [pairName_def, lastc_append _ _ (by decide)]; decide

theorem headc_fieldName (N : Nat) (v : String) : headc (fieldName N v) = some 'r' := by
  rw [fieldName_def]; simp only [String.append_assoc]
  rw [headc_append _ _ (by decide)]; decide
theorem headc_jointName (i n : Nat) (v : String) : headc (jointName i n v) = some 'j' := by
  rw [jointName_def]; simp only [String.append_assoc]
  rw [headc_append _ _ (by decide)]; decide

/-- The kernel's field names are injective in the field number. -/
theorem fieldName_inj {a b : Nat} {v : String} : fieldName a v = fieldName b v ↔ a = b := by
  constructor
  · intro h
    rw [fieldName_def, fieldName_def, String.append_left_inj, String.append_left_inj,
      String.append_right_inj, Nat.toString_eq_repr, Nat.toString_eq_repr] at h
    exact Nat.repr_injective h
  · rintro rfl; rfl

/-- A pair-delta name is never a field name. -/
theorem pairName_ne_fieldName (a b N : Nat) (v : String) : pairName a b ≠ fieldName N v := by
  intro h
  have ep : pairName a b = "resource/" ++ ("pair/" ++ toString a ++ "/" ++ toString b ++ "/delta") := by
    rw [pairName_def, show "resource/pair/" = "resource/" ++ "pair/" by decide]
    simp only [String.append_assoc]
  have ef : fieldName N v = "resource/" ++ ("field/" ++ toString N ++ "/" ++ v) := by
    rw [fieldName_def, show "resource/field/" = "resource/" ++ "field/" by decide]
    simp only [String.append_assoc]
  rw [ep, ef, String.append_right_inj] at h
  have hc := congrArg headc h
  simp only [String.append_assoc] at hc
  rw [headc_append _ _ (by decide), headc_append _ _ (by decide)] at hc
  exact absurd hc (by decide)

end Names

section Lookup
open Minidregg.Kernel.DeclaredResourceProjection (get)

theorem state_get (l : List (String × Int)) (k : String) :
    (State.mk l).get k = (l.find? (fun q => q.1 == k)).map (·.2) := rfl

theorem find_none {l : List (String × Int)} {k : String} (h : ∀ q ∈ l, q.1 ≠ k) :
    l.find? (fun q => q.1 == k) = none := by
  rw [List.find?_eq_none]; intro q hq; simpa using h q hq

/-- `scalarSlots`, split into its four runs (definitionally). -/
theorem scalarSlots_split (pre post : Values) :
    scalarSlots pre post =
      pre.map (fun p => (fieldName p.1 "before", p.2)) ++
      post.map (fun p => (fieldName p.1 "after", p.2)) ++
      post.filterMap (fun p => (get pre p.1).map fun old => (fieldName p.1 "delta", p.2 - old)) ++
      post.flatMap (fun a => post.filterMap fun b => do
        let oldA ← get pre a.1
        let oldB ← get pre b.1
        return (pairName a.1 b.1, a.2 + b.2 - oldA - oldB)) := rfl

theorem mem_pairs {pre post : Values} {q : String × Int}
    (h : q ∈ post.flatMap (fun a => post.filterMap fun b => do
        let oldA ← get pre a.1
        let oldB ← get pre b.1
        return (pairName a.1 b.1, a.2 + b.2 - oldA - oldB))) :
    ∃ a b, q.1 = pairName a b := by
  simp only [List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨a, -, b, -, hb⟩ := h
  cases ha : get pre a.1 <;> cases hb' : get pre b.1 <;> simp [ha, hb'] at hb
  exact ⟨a.1, b.1, by rw [← hb]⟩

theorem mem_deltas {pre post : Values} {q : String × Int}
    (h : q ∈ post.filterMap (fun p => (get pre p.1).map fun old => (fieldName p.1 "delta", p.2 - old))) :
    ∃ m, q.1 = fieldName m "delta" := by
  simp only [List.mem_filterMap, Option.map_eq_some_iff] at h
  obtain ⟨p, -, old, -, rfl⟩ := h
  exact ⟨p.1, rfl⟩

theorem mem_joint {j : List (Nat × Nat × String × Int)} {q : String × Int} (h : q ∈ jointSlots j) :
    ∃ i n v, q.1 = jointName i n v := by
  simp only [jointSlots, List.mem_map] at h
  obtain ⟨r, -, rfl⟩ := h
  exact ⟨_, _, _, rfl⟩

theorem mem_clock {c : Option Int} {q : String × Int} (h : q ∈ clockSlots c) : q.1 = "clock/now" := by
  cases c <;> simp [clockSlots] at h
  rw [h]

theorem mem_request {v s : Int} {q : String × Int} (h : q ∈ request v s) :
    q.1 = "request/verb" ∨ q.1 = "request/subject" := by
  simp [request] at h
  rcases h with rfl | rfl <;> simp

/-- A field name is never one of the request, clock, pair or joint names. -/
theorem request_ne_field {v s : Int} {q : String × Int} (h : q ∈ request v s) (N : Nat) (w : String)
    (hw : lastc w = some 'r' ∨ lastc w = some 'e' ∨ lastc w = some 'a') (hne : w.toList ≠ []) :
    q.1 ≠ fieldName N w := by
  apply ne_of_lastc
  rw [lastc_fieldName _ _ hne]
  rcases mem_request h with e | e <;> rw [e] <;> rcases hw with hw | hw | hw <;> rw [hw] <;> decide

theorem clock_ne_field {c : Option Int} {q : String × Int} (h : q ∈ clockSlots c) (N : Nat) (w : String)
    (hw : lastc w = some 'r' ∨ lastc w = some 'e' ∨ lastc w = some 'a') (hne : w.toList ≠ []) :
    q.1 ≠ fieldName N w := by
  apply ne_of_lastc
  rw [lastc_fieldName _ _ hne, mem_clock h]
  rcases hw with hw | hw | hw <;> rw [hw] <;> decide

theorem joint_ne_field {j : List (Nat × Nat × String × Int)} {q : String × Int} (h : q ∈ jointSlots j)
    (N : Nat) (w : String) : q.1 ≠ fieldName N w := by
  obtain ⟨i, n, v, e⟩ := mem_joint h
  apply ne_of_headc
  rw [e, headc_jointName, headc_fieldName]
  decide

/-- **The new-view `after` slot is the post-state's field.** -/
theorem get_after (t : Turn) (pre post : Values) (N : Nat) :
    (view t pre post).get (fieldName N "after") = get post N := by
  have hw : lastc "after" = some 'r' ∨ lastc "after" = some 'e' ∨ lastc "after" = some 'a' :=
    .inl (by decide)
  have hreq := find_none (l := request t.verb t.subject) (k := fieldName N "after") (fun q hq => request_ne_field hq N _ hw (by decide))
  have hbef := find_none (l := pre.map (fun p => (fieldName p.1 "before", p.2))) (k := fieldName N "after")
    (fun q hq => by
      simp only [List.mem_map] at hq
      obtain ⟨p, -, rfl⟩ := hq
      exact ne_of_lastc (by rw [lastc_before, lastc_after]; decide))
  have haft : (post.map (fun p => (fieldName p.1 "after", p.2))).find? (fun q => q.1 == fieldName N "after") =
      (post.find? (fun q => q.1 == N)).map (fun p => (fieldName p.1 "after", p.2)) := by
    have hp : ((fun q : String × Int => q.1 == fieldName N "after") ∘
        fun p : Nat × Int => (fieldName p.1 "after", p.2)) = (fun q => q.1 == N) := by
      funext p; simp [fieldName_inj]
    rw [List.find?_map, hp]
  have hdel := find_none (k := fieldName N "after")
    (l := post.filterMap (fun p => (get pre p.1).map fun old => (fieldName p.1 "delta", p.2 - old)))
    (fun q hq => by
      obtain ⟨m, e⟩ := mem_deltas hq
      rw [e]; exact ne_of_lastc (by rw [lastc_delta, lastc_after]; decide))
  have hpair := find_none (k := fieldName N "after")
    (l := post.flatMap (fun a => post.filterMap fun b => do
        let oldA ← get pre a.1
        let oldB ← get pre b.1
        return (pairName a.1 b.1, a.2 + b.2 - oldA - oldB)))
    (fun q hq => by
      obtain ⟨a, b, e⟩ := mem_pairs hq
      rw [e]; exact pairName_ne_fieldName a b N _)
  have hclock := find_none (k := fieldName N "after") (l := clockSlots t.now)
    (fun q hq => clock_ne_field hq N _ hw (by decide))
  have hjoint := find_none (k := fieldName N "after") (l := jointSlots t.joint)
    (fun q hq => joint_ne_field hq N _)
  simp only [view, state_get, scalarSlots_split, List.find?_append, hreq, hbef, haft, hdel, hpair,
    hclock, hjoint, Option.none_or, Option.or_none, Option.map_map]
  rfl

/-- **The `before` slot is the pre-state's field** (in either view). -/
theorem get_before (t : Turn) (pre post : Values) (N : Nat) :
    (view t pre post).get (fieldName N "before") = get pre N := by
  have hw : lastc "before" = some 'r' ∨ lastc "before" = some 'e' ∨ lastc "before" = some 'a' :=
    .inr (.inl (by decide))
  have hreq := find_none (l := request t.verb t.subject) (k := fieldName N "before") (fun q hq => request_ne_field hq N _ hw (by decide))
  have hbef : (pre.map (fun p => (fieldName p.1 "before", p.2))).find? (fun q => q.1 == fieldName N "before") =
      (pre.find? (fun q => q.1 == N)).map (fun p => (fieldName p.1 "before", p.2)) := by
    have hp : ((fun q : String × Int => q.1 == fieldName N "before") ∘
        fun p : Nat × Int => (fieldName p.1 "before", p.2)) = (fun q => q.1 == N) := by
      funext p; simp [fieldName_inj]
    rw [List.find?_map, hp]
  have haft := find_none (l := post.map (fun p => (fieldName p.1 "after", p.2))) (k := fieldName N "before")
    (fun q hq => by
      simp only [List.mem_map] at hq
      obtain ⟨p, -, rfl⟩ := hq
      exact ne_of_lastc (by rw [lastc_before, lastc_after]; decide))
  have hdel := find_none (k := fieldName N "before")
    (l := post.filterMap (fun p => (get pre p.1).map fun old => (fieldName p.1 "delta", p.2 - old)))
    (fun q hq => by
      obtain ⟨m, e⟩ := mem_deltas hq
      rw [e]; exact ne_of_lastc (by rw [lastc_delta, lastc_before]; decide))
  have hpair := find_none (k := fieldName N "before")
    (l := post.flatMap (fun a => post.filterMap fun b => do
        let oldA ← get pre a.1
        let oldB ← get pre b.1
        return (pairName a.1 b.1, a.2 + b.2 - oldA - oldB)))
    (fun q hq => by
      obtain ⟨a, b, e⟩ := mem_pairs hq
      rw [e]; exact pairName_ne_fieldName a b N _)
  have hclock := find_none (k := fieldName N "before") (l := clockSlots t.now)
    (fun q hq => clock_ne_field hq N _ hw (by decide))
  have hjoint := find_none (k := fieldName N "before") (l := jointSlots t.joint)
    (fun q hq => joint_ne_field hq N _)
  simp only [view, state_get, scalarSlots_split, List.find?_append, hreq, hbef, haft, hdel, hpair,
    hclock, hjoint, Option.none_or, Option.or_none, Option.map_map]
  rfl

/-- **The `delta` slot is post − pre** when the pre-state has the field. -/
theorem get_delta (t : Turn) (pre post : Values) (N : Nat) (o : Int) (hpre : get pre N = some o) :
    (view t pre post).get (fieldName N "delta") = (get post N).map (· - o) := by
  have hw : lastc "delta" = some 'r' ∨ lastc "delta" = some 'e' ∨ lastc "delta" = some 'a' :=
    .inr (.inr (by decide))
  have hreq := find_none (l := request t.verb t.subject) (k := fieldName N "delta") (fun q hq => request_ne_field hq N _ hw (by decide))
  have hbef := find_none (l := pre.map (fun p => (fieldName p.1 "before", p.2))) (k := fieldName N "delta")
    (fun q hq => by
      simp only [List.mem_map] at hq
      obtain ⟨p, -, rfl⟩ := hq
      exact ne_of_lastc (by rw [lastc_before, lastc_delta]; decide))
  have haft := find_none (l := post.map (fun p => (fieldName p.1 "after", p.2))) (k := fieldName N "delta")
    (fun q hq => by
      simp only [List.mem_map] at hq
      obtain ⟨p, -, rfl⟩ := hq
      exact ne_of_lastc (by rw [lastc_delta, lastc_after]; decide))
  have hdel : (post.filterMap (fun p => (get pre p.1).map fun old => (fieldName p.1 "delta", p.2 - old))).find?
      (fun q => q.1 == fieldName N "delta") =
      (post.find? (fun q => q.1 == N)).map (fun p => (fieldName p.1 "delta", p.2 - o)) := by
    rw [List.find?_filterMap]
    have hp : (fun a : Nat × Int => ((get pre a.1).map fun old => (fieldName a.1 "delta", a.2 - old)).any
        (fun q => q.1 == fieldName N "delta")) = (fun q => q.1 == N) := by
      funext a
      by_cases ha : a.1 = N
      · simp [ha, hpre]
      · cases get pre a.1 <;> simp [fieldName_inj, ha]
    rw [hp]
    cases hf : post.find? (fun q => q.1 == N) with
    | none => rfl
    | some a =>
      have : a.1 = N := by simpa using List.find?_some hf
      simp [this, hpre]
  have hpair := find_none (k := fieldName N "delta")
    (l := post.flatMap (fun a => post.filterMap fun b => do
        let oldA ← get pre a.1
        let oldB ← get pre b.1
        return (pairName a.1 b.1, a.2 + b.2 - oldA - oldB)))
    (fun q hq => by
      obtain ⟨a, b, e⟩ := mem_pairs hq
      rw [e]; exact pairName_ne_fieldName a b N _)
  have hclock := find_none (k := fieldName N "delta") (l := clockSlots t.now)
    (fun q hq => clock_ne_field hq N _ hw (by decide))
  have hjoint := find_none (k := fieldName N "delta") (l := jointSlots t.joint)
    (fun q hq => joint_ne_field hq N _)
  simp only [view, state_get, scalarSlots_split, List.find?_append, hreq, hbef, haft, hdel, hpair,
    hclock, hjoint, Option.none_or, Option.or_none, Option.map_map]
  simp only [Minidregg.Kernel.DeclaredResourceProjection.get, Option.map_map]
  rfl

theorem get_verb (t : Turn) (pre post : Values) : (view t pre post).get "request/verb" = some t.verb := by
  simp [view, state_get, request]

theorem get_subject (t : Turn) (pre post : Values) :
    (view t pre post).get "request/subject" = some t.subject := by
  simp [view, state_get, request]

theorem get_clock (t : Turn) (pre post : Values) : (view t pre post).get "clock/now" = t.now := by
  have hreq : (request t.verb t.subject).find? (fun q => q.1 == "clock/now") = none := by
    simp [request]
  have hscalar := find_none (k := "clock/now") (l := scalarSlots pre post) (fun q hq => by
    rw [scalarSlots_split] at hq
    simp only [List.mem_append] at hq
    rcases hq with ((hq | hq) | hq) | hq
    · simp only [List.mem_map] at hq
      obtain ⟨p, -, rfl⟩ := hq
      exact ne_of_lastc (by rw [lastc_before]; decide)
    · simp only [List.mem_map] at hq
      obtain ⟨p, -, rfl⟩ := hq
      exact ne_of_lastc (by rw [lastc_after]; decide)
    · obtain ⟨m, e⟩ := mem_deltas hq
      rw [e]; exact ne_of_lastc (by rw [lastc_delta]; decide)
    · obtain ⟨a, b, e⟩ := mem_pairs hq
      rw [e]; exact ne_of_lastc (by rw [lastc_pairName]; decide))
  have hjoint := find_none (k := "clock/now") (l := jointSlots t.joint) (fun q hq => by
    obtain ⟨i, n, v, e⟩ := mem_joint hq
    rw [e]; exact ne_of_headc (by rw [headc_jointName]; decide))
  cases hc : t.now with
  | none => simp [view, state_get, List.find?_append, hreq, hscalar, hjoint, hc, clockSlots]
  | some x => simp [view, state_get, List.find?_append, hreq, hscalar, hc, clockSlots]

end Lookup

/-! ## §7. Histories: an accepted log is a list of admitted mutates, each from the last one's post -/

section History
open Minidregg.Kernel.DeclaredResourceProjection (get)

/-- The (pre, turn) pairs of a log started at `v`: each turn's pre-state is the previous post. -/
def stepsOf : Values → List Turn → List (Values × Turn)
  | _, [] => []
  | v, t :: ts => (v, t) :: stepsOf t.post ts

/-- The field store after the whole log. -/
def final : Values → List Turn → Values
  | v, [] => v
  | _, t :: ts => final t.post ts

/-- A cell's write history: every step is a mutate (verb 2) the law admits from the state the
previous step left. (The durable CAS is what makes each step's pre the previous post; a turn
prepared against an older root is refused `staleReadGuard` before the law is read,
`DurableDataIntent.stale_read_guard_rejected`.) -/
def Accepted (law : Pred) (v : Values) (ts : List Turn) : Prop :=
  ∀ s ∈ stepsOf v ts, s.2.verb = 2 ∧ admits law s.1 s.2 = true

instance (law : Pred) (v : Values) (ts : List Turn) : Decidable (Accepted law v ts) := by
  unfold Accepted; infer_instance

theorem Accepted.tail {law : Pred} {v : Values} {t : Turn} {ts : List Turn}
    (h : Accepted law v (t :: ts)) : Accepted law t.post ts :=
  fun s hs => h s (by simp [stepsOf, hs])

theorem Accepted.head {law : Pred} {v : Values} {t : Turn} {ts : List Turn}
    (h : Accepted law v (t :: ts)) : t.verb = 2 ∧ admits law v t = true :=
  h (v, t) (by simp [stepsOf])

/-- **`deaths` never falls along an accepted history** (clause 4, by induction over the log). -/
theorem deaths_monotone_over_history (p : Params) :
    ∀ (v : Values) (ts : List Turn), Accepted (sheetLaw p) v ts →
      ∀ d, get v 6 = some d → ∃ d', get (final v ts) 6 = some d' ∧ d ≤ d'
  | v, [], _, d, hd => ⟨d, hd, le_refl d⟩
  | v, t :: ts, acc, d, hd => by
    obtain ⟨verb, adm⟩ := acc.head
    obtain ⟨a, b, ha, hb, hab⟩ := deaths_monotone_step p _ _ adm (by rw [get_verb, verb])
    have ha' := ha; have hb' := hb
    rw [show "resource/field/6/after" = fieldName 6 "after" from rfl, get_after] at ha' hb'
    rw [hd] at ha'
    cases ha'
    obtain ⟨d', hd', hle⟩ := deaths_monotone_over_history p t.post ts acc.tail b hb'
    exact ⟨d', hd', le_trans hab hle⟩

/-- **Every step of an accepted history that raises `alive` is clause 23's revive**: the referee,
after a prayer, at or after the respawn time on a clock the step exposes, to full hp at HOME. -/
theorem alive_raised_only_by_revive_over_history (p : Params) (v : Values) (ts : List Turn)
    (acc : Accepted (sheetLaw p) v ts) :
    ∀ s ∈ stepsOf v ts, get s.1 5 = some 0 → get s.2.post 5 = some 1 →
      s.2.subject = p.REF ∧ get s.1 7 = some 9 ∧
      (∃ now r, s.2.now = some now ∧ get s.1 9 = some r ∧ r ≤ now) ∧
      get s.2.post 2 = some p.HPMAX ∧ get s.2.post 1 = some p.HOME := by
  intro s hs dead alive
  obtain ⟨verb, adm⟩ := acc s hs
  have r := alive_raised_only_by_revive p _ _ adm (by rw [get_verb, verb])
    (by rw [show "resource/field/5/before" = fieldName 5 "before" from rfl, get_before, dead])
    (by rw [show "resource/field/5/after" = fieldName 5 "after" from rfl, get_after, alive])
  obtain ⟨hs', hi, ⟨r, t, hr, ht, hle⟩, hh, ha, -⟩ := r
  rw [get_subject] at hs'
  rw [show "resource/field/7/before" = fieldName 7 "before" from rfl, get_before] at hi
  rw [show "resource/field/9/before" = fieldName 9 "before" from rfl, get_before] at hr
  rw [get_clock] at ht
  rw [show "resource/field/2/after" = fieldName 2 "after" from rfl, get_after] at hh
  rw [show "resource/field/1/after" = fieldName 1 "after" from rfl, get_after] at ha
  exact ⟨Option.some.inj hs', hi, ⟨t, r, ht, hr, hle⟩, hh, ha⟩

/-- **A dead sheet stays dead along any accepted history that never exposes a clock** — every
history on this branch. -/
theorem dead_stays_dead_without_clock (p : Params) :
    ∀ (v : Values) (ts : List Turn), Accepted (sheetLaw p) v ts →
      (∀ s ∈ stepsOf v ts, s.2.now = none) →
      get v 5 = some 0 → get (final v ts) 5 = some 0
  | v, [], _, _, h => h
  | v, t :: ts, acc, noClock, dead => by
    obtain ⟨verb, adm⟩ := acc.head
    obtain ⟨x, hx, h01⟩ := alive_after_range p _ _ adm (by rw [get_verb, verb])
    rw [show "resource/field/5/after" = fieldName 5 "after" from rfl, get_after] at hx
    have tNone : t.now = none := noClock (v, t) (by simp [stepsOf])
    have post0 : get t.post 5 = some 0 := by
      rcases h01 with rfl | rfl
      · exact hx
      · obtain ⟨-, -, ⟨now, r, hn, -⟩, -⟩ :=
          alive_raised_only_by_revive_over_history p v (t :: ts) acc (v, t) (by simp [stepsOf])
            dead hx
        rw [tNone] at hn; cases hn
    exact dead_stays_dead_without_clock p t.post ts acc.tail
      (fun s hs => noClock s (by simp [stepsOf, hs])) post0

/-- **`owner_alive_monotone_over_history`** (MUD.md §5 item 6): along any accepted history of the
sheet, `deaths` is monotone, and `alive` rises only through clause 23's revive. -/
theorem owner_alive_monotone_over_history (p : Params) (v : Values) (ts : List Turn)
    (acc : Accepted (sheetLaw p) v ts) :
    (∀ d, get v 6 = some d → ∃ d', get (final v ts) 6 = some d' ∧ d ≤ d') ∧
    (∀ s ∈ stepsOf v ts, get s.1 5 = some 0 → get s.2.post 5 = some 1 →
      s.2.subject = p.REF ∧ get s.1 7 = some 9 ∧
      (∃ now r, s.2.now = some now ∧ get s.1 9 = some r ∧ r ≤ now) ∧
      get s.2.post 2 = some p.HPMAX ∧ get s.2.post 1 = some p.HOME) :=
  ⟨deaths_monotone_over_history p v ts acc, alive_raised_only_by_revive_over_history p v ts acc⟩

end History

/-- **`death_needs_hp`** (clause 33, the converse of clause 6): an admitted mutate that takes `alive`
1 → 0 leaves `hp ≤ 0`. With clause 6, `alive` falls exactly when hp crosses 0. -/
theorem death_needs_hp (p : Params) (o n : State) (admitted : eval (sheetLaw p) o n = true)
    (verb : n.get "request/verb" = some 2)
    (wasAlive : n.get "resource/field/5/before" = some 1)
    (nowDead : n.get "resource/field/5/after" = some 0) :
    ∃ h, n.get "resource/field/2/after" = some h ∧ h ≤ 0 := by
  have c := sheet_clause admitted (q := sheetClause33 p) (by simp [sheetClauses])
  simp only [sheetClause33, ev_any, ev_all, ev_not, ev_eq, ev_le, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, verb, wasAlive,
    nowDead, not_true_eq_false, false_or, and_self] at c
  exact c

/-- **`death_needs_clock`** (clause 25 in its positive `leSlotsOff` form): with no `clock/now` slot no
admitted mutate takes `alive` 1 → 0. With `revive_needs_clock`, `alive` is constant on a clockless
step. -/
theorem death_needs_clock (p : Params) (o n : State) (verb : n.get "request/verb" = some 2)
    (noClock : n.get "clock/now" = none)
    (wasAlive : n.get "resource/field/5/before" = some 1)
    (nowDead : n.get "resource/field/5/after" = some 0) :
    eval (sheetLaw p) o n = false := by
  apply Bool.eq_false_iff.mpr
  intro admitted
  have c := sheet_clause admitted (q := sheetClause25 p) (by simp [sheetClauses])
  simp only [sheetClause25, ev_any, ev_all, ev_not, ev_eq, ev_leSlotsOff, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, verb,
    wasAlive, nowDead, noClock, not_true_eq_false, false_or, and_self] at c
  obtain ⟨x, y, hx, -⟩ := c
  cases hx

/-! ## §5. The kernel: every admitted leg satisfies its installed law

`CheckedLeg` is what `DeclaredResourceController.verifyAndAuthorizeLeg` returns and what every
`AcceptedInvocation` carries for each incidence. Its `Authorized` value is the canonical compiled
policy gate (`CanonicalPolicyConfig.portal`), bound to the step context `step prepared tuple incidence`
(`CredentialAuthorityPolicyRegistry.config` sets `stepBinding := .canonical step`). -/

section Kernel
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Theory.TypedAuthorization

/-- Any value of the canonical `Authorized` type forces the resolved committed predicate to hold on
the bound step context. -/
theorem authorized_policy_eval {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) (context : PolicyStepContext)
    (canonical : config.stepBinding = .canonical context)
    {state : AuthState} {kind : ResourceKind} {request : Request kind}
    (authorized : Authorized config.portal state request) :
    ∃ committed, config.registry.resolve request.policyId request.policyRevision = some committed ∧
      eval committed.record.predicate context.oldState context.newState = true := by
  have verified := authorized.policyVerified
  rw [portal_verifyCommittedPolicy, Bool.and_eq_true] at verified
  exact (canonical_context_verifies_sound context canonical verified.2).2.2.2

variable {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient}
  {durable : Durable} {command : Command}

/-- **Every checked leg satisfies its installed law** on the controller's own step context. -/
theorem checked_leg_policy_eval
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command} {envelope : List UInt8}
    (leg : CheckedLeg prepared tuple incidence envelope) :
    ∃ committed, (policyConfig prepared tuple incidence).registry.resolve
        (tuple.request incidence).2.policyId (tuple.request incidence).2.policyRevision = some committed ∧
      eval committed.record.predicate (step prepared tuple incidence).oldState
        (step prepared tuple incidence).newState = true := by
  have authorized : Authorized (policyConfig prepared tuple incidence).portal
      prepared.authority.snapshot.authState (tuple.request incidence).2 := by
    with_unfolding_all exact leg.authorization
  exact authorized_policy_eval _ _ rfl authorized

/-- The leg's installed law is the sheet law at `p`. -/
def SheetInstalled (p : Params)
    {prepared : PreparedInvocation deployment profile ambient durable command}
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) : Prop :=
  ∀ committed, (policyConfig prepared tuple incidence).registry.resolve
      (tuple.request incidence).2.policyId (tuple.request incidence).2.policyRevision = some committed →
    committed.record.predicate = sheetLaw p

theorem sheet_leg_admitted (p : Params)
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command} {envelope : List UInt8}
    (leg : CheckedLeg prepared tuple incidence envelope) (installed : SheetInstalled p tuple incidence) :
    eval (sheetLaw p) (step prepared tuple incidence).oldState
      (step prepared tuple incidence).newState = true := by
  obtain ⟨committed, resolved, holds⟩ := checked_leg_policy_eval leg
  rw [installed committed resolved] at holds
  exact holds

/-- **`stranger_write_bounded`, kernel form.** On a leg the controller admitted under the sheet law,
a subject that is neither owner nor referee did not mutate. -/
theorem kernel_stranger_write_bounded (p : Params)
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command} {envelope : List UInt8}
    (leg : CheckedLeg prepared tuple incidence envelope) (installed : SheetInstalled p tuple incidence)
    (x : Int) (subject : (step prepared tuple incidence).newState.get "request/subject" = some x)
    (notOwner : x ≠ p.S) (notReferee : x ≠ p.REF) :
    (step prepared tuple incidence).newState.get "request/verb" ≠ some 2 := by
  intro verb
  rcases stranger_write_bounded p _ _ x (sheet_leg_admitted p leg installed) subject notOwner
    notReferee with h | ⟨-, v, hv, h⟩
  · rw [verb] at h; cases h
  · rw [verb] at h; simp at hv; rcases hv with rfl | rfl | rfl <;> cases h

/-- **Deaths monotone, kernel form**: an admitted mutate leg under the sheet law carries `deaths` in
both of the controller's views, not decreasing. -/
theorem kernel_deaths_monotone (p : Params)
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command} {envelope : List UInt8}
    (leg : CheckedLeg prepared tuple incidence envelope) (installed : SheetInstalled p tuple incidence)
    (verb : (step prepared tuple incidence).newState.get "request/verb" = some 2) :
    ∃ a b, (step prepared tuple incidence).oldState.get "resource/field/6/after" = some a ∧
      (step prepared tuple incidence).newState.get "resource/field/6/after" = some b ∧ a ≤ b :=
  deaths_monotone_step p _ _ (sheet_leg_admitted p leg installed) verb

/-- **Revive, kernel form**: an admitted mutate leg that raises `alive` is clause 23's, and needs a
`clock/now` slot the controller does not yet supply. -/
theorem kernel_alive_raised_only_by_revive (p : Params)
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command} {envelope : List UInt8}
    (leg : CheckedLeg prepared tuple incidence envelope) (installed : SheetInstalled p tuple incidence)
    (verb : (step prepared tuple incidence).newState.get "request/verb" = some 2)
    (wasDead : (step prepared tuple incidence).newState.get "resource/field/5/before" = some 0)
    (nowAlive : (step prepared tuple incidence).newState.get "resource/field/5/after" = some 1) :
    (step prepared tuple incidence).newState.get "request/subject" = some p.REF ∧
      ∃ t, (step prepared tuple incidence).newState.get "clock/now" = some t := by
  obtain ⟨hs, -, ⟨-, t, -, ht, -⟩, -⟩ :=
    alive_raised_only_by_revive p _ _ (sheet_leg_admitted p leg installed) verb wasDead nowAlive
  exact ⟨hs, t, ht⟩

end Kernel

/-! ## §8. Poles on concrete sheets, by `decide`

Tidewrack's constants (`tidewrack/realm.json`: MAXHIT_LT −7, HPMAX 10, NEG_RESPAWN 0, NEG_COST −3,
NEG_ECOST −4, LANTERN 2; HOME = the shrine, 105). The subject numbers are this file's: the sheet's
owner is 7, the referee 3, the founder 1, a stranger 9. Field numbers are `sheet/fields.json`:
id 0, at 1, hp 2, bal 3, eq 4, alive 5, deaths 6, intent 7, target 8, respawn 9, aff-asthma 10,
aff-paralysis 11, aff-clumsiness 12, def-ward 13, skill 14. -/

section Poles

def tidewrack : Params :=
  { S := 7, REF := 3, W_FOUNDER := 1, MAXHIT_LT := -7, HPMAX := 10, HOME := 105,
    NEG_RESPAWN := 0, NEG_COST := -3, NEG_ECOST := -4, LANTERN := 2 }

/-- A sheet from its fifteen fields, in `fields.json` order. -/
def sheet (at' hp bal eq alive deaths intent target respawn asthma paralysis clumsiness ward skill : Int) :
    Values :=
  [(0, 7), (1, at'), (2, hp), (3, bal), (4, eq), (5, alive), (6, deaths), (7, intent), (8, target),
   (9, respawn), (10, asthma), (11, paralysis), (12, clumsiness), (13, ward), (14, skill)]

/-- Alive at the harbour (room 101), hp 3. -/
def live : Values := sheet 101 3 0 0 1 0 0 0 0 0 0 0 0 0
/-- After a strike for 5: hp −2, dead, one death, respawn at tick 100. -/
def slain : Values := sheet 101 (-2) 0 0 0 1 0 0 100 0 0 0 0 0
/-- Dead and praying. -/
def prayed : Values := sheet 101 (-2) 0 0 0 1 9 0 100 0 0 0 0 0
/-- Revived at the shrine, full hp. -/
def revived : Values := sheet 105 10 0 0 1 1 0 0 100 0 0 0 0 0
/-- Dead at full hp: nobody struck it. -/
def smitten : Values := sheet 101 3 0 0 0 1 0 0 0 0 0 0 0 0
/-- The owner aims at sheet 5 with skill 2 (no intent yet). -/
def aimed : Values := sheet 101 3 0 0 1 0 0 5 0 0 0 0 0 2
/-- The owner declares a strike (intent 1) at sheet 5 with skill 1. -/
def striking : Values := sheet 101 3 0 0 1 0 1 5 0 0 0 0 0 1

/-- The attacker at joint index 0 (K-JOINT-INDEX): a live sheet in room 101 whose pending intent was
a strike (1) naming sheet 7, with balance 0 before and paid to 103 after. -/
def attacker : List (Nat × Nat × String × Int) :=
  [(0, 7, "before", 1), (0, 8, "before", 7), (0, 5, "before", 1), (0, 1, "after", 101),
   (0, 3, "before", 0), (0, 3, "after", 103)]

/-- The referee's resolution of the strike, with the clock at 100 and the attacker at joint 0. -/
def strikeTurn : Turn := ⟨2, 3, some 100, attacker, slain⟩
/-- The same write on this branch: no clock slot, no joint slot. -/
def strikeTurnWaveC : Turn := ⟨2, 3, none, [], slain⟩
/-- The referee kills a healthy sheet: no hp change, no attacker. -/
def smiteTurn : Turn := ⟨2, 3, none, [], smitten⟩
def prayTurn : Turn := ⟨2, 7, none, [], prayed⟩
def reviveTurn : Turn := ⟨2, 3, some 105, [], revived⟩
def reviveTurnWaveC : Turn := ⟨2, 3, none, [], revived⟩
def ownerReviveTurn : Turn := ⟨2, 7, some 105, [], revived⟩
def ownerAimTurn : Turn := ⟨2, 7, none, [], aimed⟩
def strangerAimTurn : Turn := ⟨2, 9, some 100, [], aimed⟩
def strangerLookTurn : Turn := ⟨1, 9, none, [], live⟩
def ownerStrikeTurn : Turn := ⟨2, 7, some 100, [], striking⟩
def ownerStrikeTurnWaveC : Turn := ⟨2, 7, none, [], striking⟩

set_option maxRecDepth 20000 in
/-- **Satisfiable pole.** With K-CLOCK and K-JOINT-INDEX's slots present, the referee's resolution of
a paid strike takes a live sheet (hp 3) to `alive = 0`, and the law admits it. -/
theorem death_reachable_by_strike :
    admits (sheetLaw tidewrack) live strikeTurn = true ∧
      Minidregg.Kernel.DeclaredResourceProjection.get live 5 = some 1 ∧
      Minidregg.Kernel.DeclaredResourceProjection.get live 2 = some 3 ∧
      Minidregg.Kernel.DeclaredResourceProjection.get slain 5 = some 0 := by
  decide

/-- **Without the joint and clock slots the combat death is refused**: clause 25 fails closed on the
missing clock, and the referee cannot lower hp at all (clauses 26 and 27 fail closed). -/
theorem combat_death_refused_without_joint :
    admits (sheetLaw tidewrack) live strikeTurnWaveC = false := by
  decide

/-- **The referee cannot kill a healthy sheet** (clause 33). `alive 1 → 0, deaths +1` at hp 3, no
attacker, no clock: refused. On `1ee44ed`'s law this turn was admitted (the counterexample
`referee_kills_healthy_sheet`); `death_reachable_by_strike` is the paired satisfiable pole. -/
theorem smite_refused :
    admits (sheetLaw tidewrack) live smiteTurn = false := by
  decide

/-- **Refutable pole: the owner's `alive := 1` is refused**, even with the clock present. -/
theorem owner_revive_refused : admits (sheetLaw tidewrack) prayed ownerReviveTurn = false := by
  decide

/-- **Clause 23's pole: the shrine's revive is admitted** after a prayer, with the clock present. -/
theorem shrine_revive_admitted : admits (sheetLaw tidewrack) prayed reviveTurn = true := by
  decide

/-- ...and refused on this branch, where the clock slot is absent. -/
theorem shrine_revive_refused_without_clock :
    admits (sheetLaw tidewrack) prayed reviveTurnWaveC = false := by
  decide

/-- The dead owner's prayer is admitted (clauses 7 and 9), with no clock. -/
theorem dead_owner_pray_admitted : admits (sheetLaw tidewrack) slain prayTurn = true := by
  decide

/-- **`stranger_write_bounded`, poles.** The stranger's write is refused; the owner's same write is
admitted; the stranger's observe is admitted. -/
theorem stranger_write_poles :
    admits (sheetLaw tidewrack) live strangerAimTurn = false ∧
      admits (sheetLaw tidewrack) live ownerAimTurn = true ∧
      admits (sheetLaw tidewrack) live strangerLookTurn = true := by
  decide

/-- The owner's strike intent needs the clock (clause 10): admitted with it, refused on this branch. -/
theorem owner_strike_refused_without_clock :
    admits (sheetLaw tidewrack) live ownerStrikeTurn = true ∧
      admits (sheetLaw tidewrack) live ownerStrikeTurnWaveC = false := by
  decide

set_option maxRecDepth 20000 in
/-- **A whole life, as an accepted history**: struck dead, prays, revived at the shrine. `deaths`
goes 0 → 1 and `alive` 1 → 0 → 1, the rise by the referee's revive. -/
theorem a_life_accepted :
    Accepted (sheetLaw tidewrack) live [strikeTurn, prayTurn, reviveTurn] ∧
      final live [strikeTurn, prayTurn, reviveTurn] = revived := by
  decide

set_option maxRecDepth 20000 in
/-- A history with the owner's own revive in it is not accepted. -/
theorem owner_revive_history_refused :
    ¬ Accepted (sheetLaw tidewrack) live [strikeTurn, prayTurn, ownerReviveTurn] := by
  decide

/-- **`death_is_reachable`** (MUD.md §2.3 / §5 item 6). A live sheet can be killed by an admitted
turn (the strike above), and no admitted turn raises `alive` except clause 23's revive by the
referee (for every realm's constants and every pair of views). -/
theorem death_is_reachable :
    (admits (sheetLaw tidewrack) live strikeTurn = true ∧
      Minidregg.Kernel.DeclaredResourceProjection.get live 5 = some 1 ∧
      Minidregg.Kernel.DeclaredResourceProjection.get live 2 = some 3 ∧
      Minidregg.Kernel.DeclaredResourceProjection.get slain 5 = some 0) ∧
    ∀ (p : Params) (o n : State), eval (sheetLaw p) o n = true →
      n.get "request/verb" = some 2 → n.get "resource/field/5/before" = some 0 →
      n.get "resource/field/5/after" = some 1 →
      n.get "request/subject" = some p.REF ∧ n.get "resource/field/7/before" = some 9 ∧
      (∃ r t, n.get "resource/field/9/before" = some r ∧ n.get "clock/now" = some t ∧ r ≤ t) ∧
      n.get "resource/field/2/after" = some p.HPMAX ∧
      n.get "resource/field/1/after" = some p.HOME ∧
      n.get "resource/field/7/after" = some 0 :=
  ⟨death_reachable_by_strike, alive_raised_only_by_revive⟩

end Poles

/-! ## Axiom pins -/

/-- info: 'Minidregg.Theory.SheetLaw.stranger_write_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stranger_write_bounded
/-- info: 'Minidregg.Theory.SheetLaw.deaths_monotone_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deaths_monotone_step
/-- info: 'Minidregg.Theory.SheetLaw.alive_after_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms alive_after_range
/-- info: 'Minidregg.Theory.SheetLaw.alive_raised_only_by_revive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms alive_raised_only_by_revive
/-- info: 'Minidregg.Theory.SheetLaw.revive_needs_clock' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revive_needs_clock
/-- info: 'Minidregg.Theory.SheetLaw.owner_cannot_raise_alive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms owner_cannot_raise_alive
/-- info: 'Minidregg.Theory.SheetLaw.death_needs_hp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms death_needs_hp
/-- info: 'Minidregg.Theory.SheetLaw.death_needs_clock' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms death_needs_clock
/-- info: 'Minidregg.Theory.SheetLaw.fieldName_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fieldName_inj
/-- info: 'Minidregg.Theory.SheetLaw.pairName_ne_fieldName' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairName_ne_fieldName
/-- info: 'Minidregg.Theory.SheetLaw.get_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms get_after
/-- info: 'Minidregg.Theory.SheetLaw.get_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms get_before
/-- info: 'Minidregg.Theory.SheetLaw.get_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms get_delta
/-- info: 'Minidregg.Theory.SheetLaw.get_verb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms get_verb
/-- info: 'Minidregg.Theory.SheetLaw.get_subject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms get_subject
/-- info: 'Minidregg.Theory.SheetLaw.get_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms get_clock
/-- info: 'Minidregg.Theory.SheetLaw.deaths_monotone_over_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deaths_monotone_over_history
/-- info: 'Minidregg.Theory.SheetLaw.alive_raised_only_by_revive_over_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms alive_raised_only_by_revive_over_history
/-- info: 'Minidregg.Theory.SheetLaw.dead_stays_dead_without_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dead_stays_dead_without_clock
/-- info: 'Minidregg.Theory.SheetLaw.owner_alive_monotone_over_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms owner_alive_monotone_over_history
/-- info: 'Minidregg.Theory.SheetLaw.authorized_policy_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorized_policy_eval
/-- info: 'Minidregg.Theory.SheetLaw.checked_leg_policy_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_leg_policy_eval
/-- info: 'Minidregg.Theory.SheetLaw.sheet_leg_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sheet_leg_admitted
/-- info: 'Minidregg.Theory.SheetLaw.kernel_stranger_write_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kernel_stranger_write_bounded
/-- info: 'Minidregg.Theory.SheetLaw.kernel_deaths_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kernel_deaths_monotone
/-- info: 'Minidregg.Theory.SheetLaw.kernel_alive_raised_only_by_revive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kernel_alive_raised_only_by_revive
/-- info: 'Minidregg.Theory.SheetLaw.death_reachable_by_strike' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms death_reachable_by_strike
/-- info: 'Minidregg.Theory.SheetLaw.death_is_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms death_is_reachable
/-- info: 'Minidregg.Theory.SheetLaw.combat_death_refused_without_joint' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms combat_death_refused_without_joint
/-- info: 'Minidregg.Theory.SheetLaw.smite_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms smite_refused
/-- info: 'Minidregg.Theory.SheetLaw.owner_revive_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms owner_revive_refused
/-- info: 'Minidregg.Theory.SheetLaw.shrine_revive_admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms shrine_revive_admitted
/-- info: 'Minidregg.Theory.SheetLaw.shrine_revive_refused_without_clock' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms shrine_revive_refused_without_clock
/-- info: 'Minidregg.Theory.SheetLaw.dead_owner_pray_admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms dead_owner_pray_admitted
/-- info: 'Minidregg.Theory.SheetLaw.stranger_write_poles' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms stranger_write_poles
/-- info: 'Minidregg.Theory.SheetLaw.owner_strike_refused_without_clock' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms owner_strike_refused_without_clock
/-- info: 'Minidregg.Theory.SheetLaw.a_life_accepted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms a_life_accepted
/-- info: 'Minidregg.Theory.SheetLaw.owner_revive_history_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms owner_revive_history_refused

end Minidregg.Theory.SheetLaw
