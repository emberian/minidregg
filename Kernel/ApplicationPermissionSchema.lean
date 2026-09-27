/-
Pure ordered Sandstorm ViewInfo permission/role metadata and role-selection math.
This describes an application and a requested role only. It does not establish
that the descriptor is installed, that a share exists, or that the session has
any grant; those are current native admission obligations.
-/
import Kernel.ApplicationGrainSessionEnrollment

namespace Minidregg.Kernel.ApplicationPermissionSchema
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.ApplicationGrainSessionEnrollment
set_option autoImplicit false

/-- Index in `Schema.permissions` is the persistent Sandstorm permission ID. -/
structure Permission where
  name : List UInt8
  obsolete : Bool
  deriving DecidableEq, Repr

/-- Index in `Schema.roles` is the persistent Sandstorm role ID. Short masks
are retained as such; an absent bit at a current permission index is false. -/
structure Role where
  permissions : List Bool
  obsolete : Bool
  default : Bool
  deriving DecidableEq, Repr

/-- The entire role-relevant ViewInfo projection. `denied` is the UiView proxy
mask, not an app-issued grant ceiling. Labels/localizations are UI metadata and
are not read by permission resolution. -/
structure Schema where
  version : Nat
  permissions : List Permission
  roles : List Role
  denied : List Bool
  deriving DecidableEq, Repr

def permissionStream : StreamCodec Permission :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream StreamCodec.bool)
    (fun p => (p.name, p.obsolete))
    (fun (name, obsolete) => ⟨name, obsolete⟩)
    (by intro p; cases p; rfl)

def roleStream : StreamCodec Role :=
  StreamCodec.xmap
    (StreamCodec.product (StreamCodec.list StreamCodec.bool)
      (StreamCodec.product StreamCodec.bool StreamCodec.bool))
    (fun r => (r.permissions, r.obsolete, r.default))
    (fun (permissions, obsolete, default) => ⟨permissions, obsolete, default⟩)
    (by intro r; cases r; rfl)

def schemaStream : StreamCodec Schema :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product (StreamCodec.list permissionStream)
        (StreamCodec.product (StreamCodec.list roleStream)
          (StreamCodec.list StreamCodec.bool))))
    (fun s => (s.version, s.permissions, s.roles, s.denied))
    (fun (version, permissions, roles, denied) =>
      ⟨version, permissions, roles, denied⟩)
    (by intro s; cases s; rfl)

private def schemaFrame : List UInt8 :=
  "DREGG/APPLICATION/PERMISSION-SCHEMA/v1".toUTF8.toList

private def rawSchemaCodec : LawfulCodec Schema where
  encode s := schemaFrame ++ schemaStream.encode s
  decode bytes := if bytes.take schemaFrame.length = schemaFrame then
    schemaStream.toLawful.decode (bytes.drop schemaFrame.length) else none
  decode_encode := by
    intro s
    have decoded := schemaStream.toLawful.decode_encode s
    change schemaStream.toLawful.decode (schemaStream.encode s) = some s at decoded
    simp [decoded]

def schemaCodec : LawfulCodec Schema :=
  ResourceBirthCodec.strictCodec rawSchemaCodec

def Schema.root (s : Schema) : Digest :=
  (Sp800185Cshake256.hash
    "DREGG/APPLICATION/PERMISSION-SCHEMA-ROOT/v1".toUTF8.toList
    (schemaCodec.encode s)).digest

theorem schema_decode_encode (s : Schema) :
    schemaCodec.decode (schemaCodec.encode s) = some s :=
  schemaCodec.decode_encode s

theorem schema_bytes_injective : Function.Injective schemaCodec.encode := by
  intro left right same
  have decoded := congrArg schemaCodec.decode same
  exact Option.some.inj (by simpa only [schemaCodec.decode_encode] using decoded)

theorem decoded_canonical {bytes : List UInt8} {s : Schema}
    (decoded : schemaCodec.decode bytes = some s) :
    schemaCodec.encode s = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawSchemaCodec decoded

private def asciiLetter (c : UInt8) : Bool :=
  (65 ≤ c.toNat && c.toNat ≤ 90) || (97 ≤ c.toNat && c.toNat ≤ 122)

private def asciiDigit (c : UInt8) : Bool :=
  48 ≤ c.toNat && c.toNat ≤ 57

/-- Sandstorm PermissionDef names are identifiers: ASCII alphanumeric, first
byte a letter. Empty and duplicate names cannot be mapped to stable IDs. -/
def Permission.validName (name : List UInt8) : Bool :=
  match name with
  | [] => false
  | first :: rest => asciiLetter first &&
      rest.all (fun c => asciiLetter c || asciiDigit c) &&
      decide (name.length ≤ 256)

/-- Explicit bounds avoid silently truncating a wire role ID or mask. Short
historical masks are allowed, but masks longer than current definitions are
not. A schema with two defaults cannot resolve `RoleBasis.none` safely. -/
def Schema.valid (s : Schema) : Bool :=
  decide (0 < s.version) &&
  decide (s.permissions.length ≤ 256) &&
  decide (s.roles.length ≤ 256) &&
  decide (s.denied.length ≤ s.permissions.length) &&
  s.permissions.all (fun p => Permission.validName p.name) &&
  decide (s.permissions.map (·.name)).Nodup &&
  s.roles.all (fun r => decide (r.permissions.length ≤ s.permissions.length)) &&
  decide ((s.roles.filter (·.default)).length ≤ 1)

private def nameKnown (s : Schema) (name : List UInt8) : Bool :=
  s.permissions.any (fun p => p.name == name)

/-- The chosen base is only role math. `none` selects the single default role,
or the empty set when no default exists; `allAccess` is all current schema bits.
Obsolete roles remain addressable because IDs persist across upgrades. -/
def Schema.chosenBase (s : Schema) (basis : RoleBasis) : Option (List Bool) :=
  match basis with
  | .none => some ((s.roles.find? (·.default)).map (·.permissions) |>.getD [])
  | .allAccess => some (List.replicate s.permissions.length true)
  | .role roleId => (s.roles[roleId]?).map (·.permissions)

/-- One normalized bit, after requested additions/removals and the view's
denied mask. A missing bit in a short historical role mask is false. -/
def Schema.resolveBit (s : Schema) (base : List Bool)
    (assignment : RoleAssignment) (i : Nat) (permission : Permission) : Bool :=
  ((base[i]?.getD false) || assignment.added.contains permission.name) &&
    !(assignment.removed.contains permission.name) &&
    !(s.denied[i]?.getD false)

def Schema.resolveVector (s : Schema) (base : List Bool)
    (assignment : RoleAssignment) : List Bool :=
  s.permissions.mapIdx fun i permission =>
    s.resolveBit base assignment i permission

/-- Reject stale schema selectors, malformed metadata, unknown deltas, and
out-of-range role IDs. Result length is exactly the current permission count.
The result is NOT a session grant; native admission must intersect/check the
app-issued current grant ceiling and selected governed descriptor. -/
def Schema.resolve (s : Schema) (assignment : RoleAssignment) : Option (List Bool) := do
  if !s.valid || !assignment.valid ||
     assignment.roleVersion != s.version ||
     assignment.roleSchemaRoot != s.root ||
     !assignment.added.all (nameKnown s) ||
     !assignment.removed.all (nameKnown s) then none else
  let base ← s.chosenBase assignment.basis
  some (s.resolveVector base assignment)

theorem resolveBit_denied (s : Schema) (base : List Bool)
    (assignment : RoleAssignment) (i : Nat) (p : Permission)
    (denied : s.denied[i]?.getD false = true) :
    s.resolveBit base assignment i p = false := by
  simp [Schema.resolveBit, denied]

theorem resolveVector_length (s : Schema) (base : List Bool)
    (assignment : RoleAssignment) :
    (s.resolveVector base assignment).length = s.permissions.length := by
  simp [Schema.resolveVector]

theorem resolveVector_denied (s : Schema) (base : List Bool)
    (assignment : RoleAssignment) (i : Nat)
    (denied : s.denied[i]?.getD false = true) :
    (s.resolveVector base assignment)[i]?.getD false = false := by
  simp only [Schema.resolveVector, List.getElem?_mapIdx]
  cases found : s.permissions[i]? with
  | none => simp
  | some permission =>
      simp [resolveBit_denied s base assignment i permission denied]

theorem chosenBase_allAccess (s : Schema) :
    s.chosenBase .allAccess = some (List.replicate s.permissions.length true) := by
  simp [Schema.chosenBase]

theorem chosenBase_role (s : Schema) (roleId : Nat) :
    s.chosenBase (.role roleId) = (s.roles[roleId]?).map (·.permissions) := by
  simp [Schema.chosenBase]

theorem chosenBase_none_without_default (s : Schema)
    (noDefault : s.roles.find? (·.default) = none) :
    s.chosenBase .none = some [] := by
  simp [Schema.chosenBase, noDefault]

/-- Pointwise comparison for a separately selected, current app-issued ceiling.
This relation does not attest that the ceiling itself is authorized. -/
def withinCeiling (requested ceiling : List Bool) : Prop :=
  requested.length = ceiling.length ∧
    ∀ i : Nat, requested[i]?.getD false = true → ceiling[i]?.getD false = true

theorem withinCeiling_refl (bits : List Bool) : withinCeiling bits bits := by
  simp [withinCeiling]

/-- Mini dispatch packs permission ID `i` into Nat bit `2^i`. This explicit
mapping is distinct from Cap'n Proto's wire encoding of `List(Bool)`. -/
def bitsToNat : List Bool → Nat
  | [] => 0
  | bit :: rest => (if bit then 1 else 0) + 2 * bitsToNat rest

def natToBits : Nat → Nat → List Bool
  | 0, _ => []
  | width + 1, value => (value % 2 == 1) :: natToBits width (value / 2)

theorem bitsToNat_width (bits : List Bool) : bitsToNat bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [bitsToNat]
  | cons bit rest ih =>
      cases bit <;> simp [bitsToNat, pow_succ] <;> omega

theorem natToBits_bitsToNat (bits : List Bool) :
    natToBits bits.length (bitsToNat bits) = bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      cases bit with
      | false => simpa [bitsToNat, natToBits] using ih
      | true =>
          have div : (1 + 2 * bitsToNat rest) / 2 = bitsToNat rest := by omega
          simpa [bitsToNat, natToBits, div] using ih

theorem bitsToNat_injective_at_width (left right : List Bool)
    (sameWidth : left.length = right.length)
    (sameValue : bitsToNat left = bitsToNat right) : left = right := by
  calc
    left = natToBits left.length (bitsToNat left) := (natToBits_bitsToNat left).symm
    _ = natToBits right.length (bitsToNat right) := by rw [sameWidth, sameValue]
    _ = right := natToBits_bitsToNat right

end Minidregg.Kernel.ApplicationPermissionSchema
