/-
# Compiler.FnWireGrammar — fn's wire-grammar language, one interpreter, both round trips

fn publishes its wire formats as GRAMMARS in one data language (`fn-wire-grammar`,
version 1). The normative description is fn `planning/design/wire-grammar-2026-10-04.md`
§2, read at fn d420a2b5; the families and vectors are fn `specs/wire-grammar.json`,
vendored as `protocol/fn/wire-grammar.json`, loaded by `Compiler.FnWireJson` and pinned by
`Compiler.FnWirePinned`. This module is Mini's ONE interpreter of that language:

* `decode g xs` reads one value of `g` from the front of `xs` and returns it with the
  exact unconsumed suffix, or a named `Refusal`;
* `encode g v` writes a value of `g`, or refuses a non-value;
* `Grammar.wf` is the static rule set (decidable, so a loaded grammar is checked, never
  assumed).

and proves, once for every well-formed grammar:

* `decode_encode` — `encode g v = ok b` implies `decode g (b ++ r) = ok (v, r)` when `g`
  is delimited or `r = []`;
* `encode_decode` — `decode g xs = ok (v, r)` implies `encode g v = ok b` with
  `b ++ r = xs` (CANONICITY: every accepted octet string is the encoding of its value).

Refusals are named and distinct, and the decoder is sequential (the first refusal met is
the answer): `trailer` (a frame whose trailer is not BLAKE3-256 of its protected prefix,
checked before the payload is decoded), `whereFailed` (a `where` node's fields decode and
one of its checks fails; fn's word `where`), `malformed` (every other refusal). These are
fn's three words (`fnRefusals`), and `FnWireRoundTrip.decode_answers` proves the decoder
gives no other. `limit` is Mini's own work bound, answered only by `decodeWithin` (the input
exceeds the caller's bound; refused before any decoding work).

The base64 is `Kernel.Base64` (the tree's one codec, with its own two round trips); the
frame digest is `Compiler.Blake3.hash`, used here only through its length.
-/
import Kernel.Base64
import Compiler.Blake3

namespace Minidregg.Compiler.FnWire

set_option autoImplicit false

open Minidregg.Kernel
open Minidregg.Compiler

/-! ## The language -/

/-- The octet classes of `bytes`, `rest` and `line` fields. -/
inductive OctetClass where
  /-- Every octet. -/
  | any
  /-- RFC 3629 UTF-8 (strict: no overlongs, no surrogates, nothing above U+10FFFF). -/
  | utf8
  /-- HTAB, SP and `!`..`~` (an RFC 5322 field body; it excludes CR). -/
  | header
  deriving DecidableEq, Repr

/-- A check over the elements of a `seq` value (0-based positions). -/
inductive Check where
  /-- element `i` ≤ element `j` -/
  | le (i j : Nat)
  /-- element `i` = element `j` -/
  | eq (i j : Nat)
  /-- element `k` = element `j` − element `i`, with `i ≤ j` -/
  | diff (k j i : Nat)
  deriving DecidableEq, Repr

/-- A grammar. `seq` and `tag` are cons chains (`seqNil`/`seqCons`, `tagNil`/`tagArm`),
so the type is a plain inductive and every function and proof is plain structural
recursion; `Grammar.wf` requires a `seqCons` tail to be a seq and a `tagArm`'s `more` to be
a tag of the same width. The JSON loader builds the chains from fn's arrays. -/
inductive Grammar where
  | const (octets : List UInt8)
  | uint (w lo hi : Nat)
  | bytes (w lo hi : Nat) (cls : OctetClass)
  | rest (lo hi : Nat) (cls : OctetClass)
  | line (lo hi : Nat) (cls : OctetClass)
  | base64Lines (width lo hi : Nat)
  | enum (w base : Nat) (names : List String)
  | seqNil
  | seqCons (head tail : Grammar)
  | tagNil (w : Nat)
  | tagArm (w code : Nat) (name : String) (arm more : Grammar)
  | maybe (g : Grammar)
  | where_ (g : Grammar) (checks : List Check)
  | frame (magic : List UInt8) (version kind : UInt8) (max : Nat) (payload : Grammar)
  deriving DecidableEq, Repr

/-- A value. `const` ↦ `null`, `uint` ↦ `nat`, `bytes`/`rest`/`line`/`base64Lines` ↦
`octets`, `enum` ↦ `name`, `seq` ↦ `list`, `maybe` ↦ `list []` or `list [v]`,
`tag` ↦ `tagged`, `where`/`frame` ↦ their inner value (fn §2 "Value JSON"). -/
inductive Value where
  | null
  | nat (n : Nat)
  | octets (b : List UInt8)
  | name (s : String)
  | list (vs : List Value)
  | tagged (name : String) (v : Value)

/-- The named refusals. -/
inductive Refusal where
  | malformed
  | whereFailed
  | trailer
  | limit
  deriving DecidableEq, Repr

/-- The refusals of fn's language, in fn's order (`words.refusals` of the exported file:
`trailer`, `where`, `malformed`). -/
def fnRefusals : List Refusal := [.trailer, .whereFailed, .malformed]

/-- A refusal's word. fn's three are fn's words; `limit` is Mini's own work bound. -/
def Refusal.fnWord : Refusal → String
  | .malformed => "malformed"
  | .whereFailed => "where"
  | .trailer => "trailer"
  | .limit => "limit"

/-! ## Big-endian naturals of a fixed width -/

def leBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => UInt8.ofNat (n % 256) :: leBytes w (n / 256)

def leValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leValue bs

/-- `n` as `w` octets, most significant first. -/
def beBytes (w n : Nat) : List UInt8 := (leBytes w n).reverse

/-- The natural `xs` carries, most significant octet first. -/
def beValue (xs : List UInt8) : Nat := leValue xs.reverse

theorem length_leBytes : ∀ (w n : Nat), (leBytes w n).length = w
  | 0, _ => rfl
  | w + 1, n => by simp [leBytes, length_leBytes w]

theorem length_beBytes (w n : Nat) : (beBytes w n).length = w := by
  simp [beBytes, length_leBytes]

theorem leValue_leBytes : ∀ (w n : Nat), n < 256 ^ w → leValue (leBytes w n) = n
  | 0, n, h => by simp at h; simp [leBytes, leValue, h]
  | w + 1, n, h => by
      have hdiv : n / 256 < 256 ^ w := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        rw [Nat.pow_succ] at h; exact h
      simp only [leBytes, leValue, leValue_leBytes w (n / 256) hdiv, UInt8.toNat_ofNat']
      omega

theorem leBytes_leValue : ∀ (xs : List UInt8), leBytes xs.length (leValue xs) = xs
  | [] => rfl
  | b :: bs => by
      have hb := b.toNat_lt
      simp only [leBytes, leValue]
      have h1 : (b.toNat + 256 * leValue bs) % 256 = b.toNat := by omega
      have h2 : (b.toNat + 256 * leValue bs) / 256 = leValue bs := by omega
      rw [h1, h2, leBytes_leValue bs, UInt8.ofNat_toNat]

theorem leValue_lt : ∀ (xs : List UInt8), leValue xs < 256 ^ xs.length
  | [] => by simp [leValue]
  | b :: bs => by
      have hb := b.toNat_lt
      have ih := leValue_lt bs
      simp only [leValue, List.length_cons, Nat.pow_succ]
      have : (2:Nat) ^ 8 = 256 := rfl
      omega

theorem beValue_beBytes {w n : Nat} (h : n < 256 ^ w) : beValue (beBytes w n) = n := by
  simp [beValue, beBytes, leValue_leBytes w n h]

theorem beBytes_beValue (xs : List UInt8) : beBytes xs.length (beValue xs) = xs := by
  have := leBytes_leValue xs.reverse
  simp only [List.length_reverse] at this
  simp [beBytes, beValue, this]

theorem beValue_lt (xs : List UInt8) : beValue xs < 256 ^ xs.length := by
  have := leValue_lt xs.reverse
  simpa [beValue] using this

/-! ## Octet classes -/

def headerOctet (b : UInt8) : Bool := b.toNat == 9 || (32 ≤ b.toNat && b.toNat ≤ 126)

def utf8Cont (c : UInt8) : Bool := 0x80 ≤ c.toNat && c.toNat ≤ 0xBF

/-- RFC 3629 §4 (Unicode Table 3-7): the well-formed UTF-8 byte sequences. -/
def utf8Valid : List UInt8 → Bool
  | [] => true
  | b :: rest =>
    if b.toNat < 0x80 then utf8Valid rest else
    match rest with
    | [] => false
    | c1 :: rest1 =>
      if 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF then utf8Cont c1 && utf8Valid rest1 else
      match rest1 with
      | [] => false
      | c2 :: rest2 =>
        if (b.toNat = 0xE0 ∧ 0xA0 ≤ c1.toNat ∧ c1.toNat ≤ 0xBF) ∨
           (((0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC) ∨ (0xEE ≤ b.toNat ∧ b.toNat ≤ 0xEF)) ∧
              utf8Cont c1 = true) ∨
           (b.toNat = 0xED ∧ 0x80 ≤ c1.toNat ∧ c1.toNat ≤ 0x9F) then
          utf8Cont c2 && utf8Valid rest2 else
        match rest2 with
        | [] => false
        | c3 :: rest3 =>
          if (b.toNat = 0xF0 ∧ 0x90 ≤ c1.toNat ∧ c1.toNat ≤ 0xBF) ∨
             (0xF1 ≤ b.toNat ∧ b.toNat ≤ 0xF3 ∧ utf8Cont c1 = true) ∨
             (b.toNat = 0xF4 ∧ 0x80 ≤ c1.toNat ∧ c1.toNat ≤ 0x8F) then
            utf8Cont c2 && utf8Cont c3 && utf8Valid rest3
          else false

def classOk : OctetClass → List UInt8 → Bool
  | .any, _ => true
  | .utf8, xs => utf8Valid xs
  | .header, xs => xs.all headerOctet

/-! ## Checks -/

def natAt (vs : List Value) (i : Nat) : Option Nat :=
  match vs[i]? with
  | some (.nat n) => some n
  | _ => none

def Check.holds (vs : List Value) : Check → Bool
  | .le i j => match natAt vs i, natAt vs j with
    | some a, some b => decide (a ≤ b)
    | _, _ => false
  | .eq i j => match natAt vs i, natAt vs j with
    | some a, some b => decide (a = b)
    | _, _ => false
  | .diff k j i => match natAt vs k, natAt vs j, natAt vs i with
    | some a, some b, some c => decide (c ≤ b ∧ a = b - c)
    | _, _, _ => false

def checksHold (v : Value) (cs : List Check) : Bool :=
  match v with
  | .list vs => cs.all (·.holds vs)
  | _ => false

/-! ## Lines: text cut into lines of `w` octets, each followed by CR LF -/

def lines (w : Nat) (t : List UInt8) : List UInt8 :=
  if t = [] ∨ w = 0 then [] else
  if t.length ≤ w then t ++ [13, 10] else
  t.take w ++ 13 :: 10 :: lines w (t.drop w)
termination_by t.length
decreasing_by
  have hw : w ≠ 0 := fun h' => by simp_all
  simp only [List.length_drop]; omega

def unlines (w : Nat) (xs : List UInt8) : List UInt8 :=
  if xs = [] ∨ w = 0 then [] else
  if xs.length ≤ w + 2 then xs.take (xs.length - 2) else
  xs.take w ++ unlines w (xs.drop (w + 2))
termination_by xs.length
decreasing_by simp only [List.length_drop]; omega

/-! ## Static rules -/

def widthOk (w : Nat) : Bool := w == 1 || w == 2 || w == 4 || w == 8

def distinct : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinct xs

def position (s : String) : List String → Nat
  | [] => 0
  | x :: xs => if x = s then 0 else position s xs + 1

def Grammar.isSeq : Grammar → Bool
  | .seqNil | .seqCons _ _ => true
  | _ => false

def Grammar.tagWidth : Grammar → Option Nat
  | .tagNil w | .tagArm w _ _ _ _ => some w
  | _ => none

def Grammar.tagCodes : Grammar → List Nat
  | .tagArm _ c _ _ more => c :: more.tagCodes
  | _ => []

def Grammar.tagNames : Grammar → List String
  | .tagArm _ _ n _ more => n :: more.tagNames
  | _ => []

/-- Every encoding is followed by nothing the decoder reads: the decoder stops at the end
of the encoding whatever follows. -/
def Grammar.delimited : Grammar → Bool
  | .const _ | .uint _ _ _ | .bytes _ _ _ _ | .line _ _ _ | .enum _ _ _ | .frame _ _ _ _ _ => true
  | .rest _ _ _ | .base64Lines _ _ _ | .maybe _ => false
  | .seqNil | .tagNil _ => true
  | .seqCons h t => h.delimited && t.delimited
  | .tagArm _ _ _ arm more => arm.delimited && more.delimited
  | .where_ g _ => g.delimited

/-- No value encodes to no octets. -/
def Grammar.nonempty : Grammar → Bool
  | .const o => !o.isEmpty
  | .uint _ _ _ | .bytes _ _ _ _ | .line _ _ _ | .enum _ _ _ | .frame _ _ _ _ _ => true
  | .tagNil _ | .tagArm _ _ _ _ _ => true
  | .rest lo _ _ => 0 < lo
  | .base64Lines _ lo _ => 0 < lo
  | .seqNil => false
  | .seqCons h t => h.nonempty || t.nonempty
  | .maybe _ => false
  | .where_ g _ => g.nonempty

/-- The static rules of fn §2: widths in {1,2,4,8} and bounds that fit them; distinct tag
codes and names, distinct enum names; a non-delimited (tail-only) element only last in a
seq; `maybe` of a grammar that never encodes to nothing; `where` over a seq (a check naming
a position past the end or a non-number fails when decoding, fn §2); a `line` of the `header` class (the only class that
excludes CR); a frame's magic of 4 octets and `max < 2^32`. -/
def Grammar.wf : Grammar → Bool
  | .const _ => true
  | .uint w lo hi => widthOk w && decide (lo ≤ hi) && decide (hi < 256 ^ w)
  | .bytes w lo hi _ => widthOk w && decide (lo ≤ hi) && decide (hi < 256 ^ w)
  | .rest lo hi _ => decide (lo ≤ hi)
  | .line lo hi cls => decide (lo ≤ hi) && cls == .header
  | .base64Lines width lo hi => decide (0 < width) && decide (lo ≤ hi)
  | .enum w base names =>
      widthOk w && !names.isEmpty && distinct names && decide (base + names.length ≤ 256 ^ w)
  | .seqNil => true
  | .seqCons h t => h.wf && t.isSeq && (t == .seqNil || h.delimited) && t.wf
  | .tagNil w => widthOk w
  | .tagArm w code name arm more =>
      widthOk w && decide (code < 256 ^ w) && more.tagWidth == some w &&
        !more.tagCodes.contains code && !more.tagNames.contains name && arm.wf && more.wf
  | .maybe g => g.wf && g.nonempty
  | .where_ g _ => g.isSeq && g.wf
  | .frame magic _ _ max g => magic.length == 4 && decide (max < 2 ^ 32) && g.wf

/-! ## The encoder -/

/-- A frame's protected prefix: MAGIC VERSION KIND LENGTH(u32) PAYLOAD. -/
def framePrefix (magic : List UInt8) (version kind : UInt8) (payload : List UInt8) :
    List UInt8 :=
  magic ++ version :: kind :: (beBytes 4 payload.length ++ payload)

def encode : Grammar → Value → Except Refusal (List UInt8)
  | .const o, .null => .ok o
  | .uint w lo hi, .nat n => if lo ≤ n ∧ n ≤ hi then .ok (beBytes w n) else .error .malformed
  | .bytes w lo hi c, .octets b =>
      if lo ≤ b.length ∧ b.length ≤ hi ∧ classOk c b = true then .ok (beBytes w b.length ++ b)
      else .error .malformed
  | .rest lo hi c, .octets b =>
      if lo ≤ b.length ∧ b.length ≤ hi ∧ classOk c b = true then .ok b else .error .malformed
  | .line lo hi c, .octets b =>
      if lo ≤ b.length ∧ b.length ≤ hi ∧ classOk c b = true then .ok (b ++ [13, 10])
      else .error .malformed
  | .base64Lines width lo hi, .octets b =>
      if lo ≤ b.length ∧ b.length ≤ hi then .ok (lines width (Base64.encode b))
      else .error .malformed
  | .enum w base names, .name s =>
      if s ∈ names then .ok (beBytes w (base + position s names)) else .error .malformed
  | .seqNil, .list [] => .ok []
  | .seqCons h t, .list (v :: vs) =>
      match encode h v, encode t (.list vs) with
      | .ok a, .ok b => .ok (a ++ b)
      | .error e, _ => .error e
      | .ok _, .error e => .error e
  | .tagArm w code name arm more, .tagged n v =>
      if n = name then
        match encode arm v with
        | .ok b => .ok (beBytes w code ++ b)
        | .error e => .error e
      else encode more (.tagged n v)
  | .maybe _, .list [] => .ok []
  | .maybe g, .list [v] => encode g v
  | .where_ g cs, v =>
      match encode g v with
      | .ok b => if checksHold v cs then .ok b else .error .whereFailed
      | .error e => .error e
  | .frame magic version kind max g, v =>
      match encode g v with
      | .ok p =>
          if p.length ≤ max then
            .ok (framePrefix magic version kind p ++ Blake3.hash (framePrefix magic version kind p))
          else .error .malformed
      | .error e => .error e
  | _, _ => .error .malformed

/-! ## The decoder -/

/-- One value of `g` from the front of `xs`, with the exact unconsumed suffix. -/
def decode : Grammar → List UInt8 → Except Refusal (Value × List UInt8)
  | .const o, xs =>
      if xs.take o.length = o then .ok (.null, xs.drop o.length) else .error .malformed
  | .uint w lo hi, xs =>
      if w ≤ xs.length ∧ lo ≤ beValue (xs.take w) ∧ beValue (xs.take w) ≤ hi then
        .ok (.nat (beValue (xs.take w)), xs.drop w)
      else .error .malformed
  | .bytes w lo hi c, xs =>
      if w ≤ xs.length ∧ lo ≤ beValue (xs.take w) ∧ beValue (xs.take w) ≤ hi ∧
          beValue (xs.take w) ≤ (xs.drop w).length ∧
          classOk c ((xs.drop w).take (beValue (xs.take w))) = true then
        .ok (.octets ((xs.drop w).take (beValue (xs.take w))),
          (xs.drop w).drop (beValue (xs.take w)))
      else .error .malformed
  | .rest lo hi c, xs =>
      if classOk c xs = true ∧ lo ≤ xs.length ∧ xs.length ≤ hi then .ok (.octets xs, [])
      else .error .malformed
  | .line lo hi c, xs =>
      if (xs.dropWhile (· != 13)).take 2 = [13, 10] ∧
          classOk c (xs.takeWhile (· != 13)) = true ∧
          lo ≤ (xs.takeWhile (· != 13)).length ∧ (xs.takeWhile (· != 13)).length ≤ hi then
        .ok (.octets (xs.takeWhile (· != 13)), (xs.dropWhile (· != 13)).drop 2)
      else .error .malformed
  | .base64Lines width lo hi, xs =>
      if lines width (unlines width xs) = xs then
        match Base64.decode (unlines width xs) with
        | some v => if lo ≤ v.length ∧ v.length ≤ hi then .ok (.octets v, []) else .error .malformed
        | none => .error .malformed
      else .error .malformed
  | .enum w base names, xs =>
      if h : w ≤ xs.length ∧ base ≤ beValue (xs.take w) ∧
          beValue (xs.take w) < base + names.length then
        .ok (.name (names[beValue (xs.take w) - base]'(by omega)), xs.drop w)
      else .error .malformed
  | .seqNil, xs => .ok (.list [], xs)
  | .seqCons h t, xs =>
      match decode h xs with
      | .ok (v, r) =>
          match decode t r with
          | .ok (.list vs, r') => .ok (.list (v :: vs), r')
          | .ok _ => .error .malformed
          | .error e => .error e
      | .error e => .error e
  | .tagNil _, _ => .error .malformed
  | .tagArm w code name arm more, xs =>
      if w ≤ xs.length ∧ beValue (xs.take w) = code then
        match decode arm (xs.drop w) with
        | .ok (v, r) => .ok (.tagged name v, r)
        | .error e => .error e
      else decode more xs
  | .maybe g, xs =>
      match xs with
      | [] => .ok (.list [], [])
      | x :: xs' =>
          match decode g (x :: xs') with
          | .ok (v, r) => .ok (.list [v], r)
          | .error e => .error e
  | .where_ g cs, xs =>
      match decode g xs with
      | .ok (v, r) => if checksHold v cs then .ok (v, r) else .error .whereFailed
      | .error e => .error e
  | .frame magic version kind max g, xs =>
      match xs with
      | m0 :: m1 :: m2 :: m3 :: ver :: knd :: l0 :: l1 :: l2 :: l3 :: body =>
          if [m0, m1, m2, m3] = magic ∧ ver = version ∧ knd = kind ∧
              beValue [l0, l1, l2, l3] ≤ max ∧ beValue [l0, l1, l2, l3] + 32 ≤ body.length then
            if (body.drop (beValue [l0, l1, l2, l3])).take 32 =
                Blake3.hash ([m0, m1, m2, m3] ++ ver :: knd ::
                  ([l0, l1, l2, l3] ++ body.take (beValue [l0, l1, l2, l3]))) then
              match decode g (body.take (beValue [l0, l1, l2, l3])) with
              | .ok (v, []) => .ok (v, (body.drop (beValue [l0, l1, l2, l3])).drop 32)
              | .ok _ => .error .malformed
              | .error e => .error e
            else .error .trailer
          else .error .malformed
      | _ => .error .malformed

/-- A whole message: one value and nothing left over. -/
def decodeAll (g : Grammar) (xs : List UInt8) : Except Refusal Value :=
  match decode g xs with
  | .ok (v, []) => .ok v
  | .ok _ => .error .malformed
  | .error e => .error e

/-- `decodeAll` under an explicit work bound: an input longer than `limit` octets is
refused `limit` before any decoding work (the decoder's work and every allocation it
makes are linear in the input; no declared length is allocated before it is checked
against the octets present). -/
def decodeWithin (limit : Nat) (g : Grammar) (xs : List UInt8) : Except Refusal Value :=
  if xs.length ≤ limit then decodeAll g xs else .error .limit

theorem decodeWithin_of_le {limit : Nat} {g : Grammar} {xs : List UInt8}
    (h : xs.length ≤ limit) : decodeWithin limit g xs = decodeAll g xs := by
  simp [decodeWithin, h]

theorem decodeWithin_refuses_over {limit : Nat} {g : Grammar} {xs : List UInt8}
    (h : limit < xs.length) : decodeWithin limit g xs = .error .limit := by
  simp [decodeWithin]; omega

end Minidregg.Compiler.FnWire
