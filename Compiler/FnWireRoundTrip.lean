/-
# Compiler.FnWireRoundTrip — the interpreter's two round trips, for every well-formed grammar

`decode_encode` (dec ∘ enc = id on values, with any suffix after a delimited grammar) and
`encode_decode` (enc ∘ dec = id on accepted octets: canonicity), over `Compiler.FnWireGrammar`.
Nothing here unfolds the hash: a frame's trailer enters only through `Blake3.length_hash`.
-/
import Compiler.FnWireGrammar
import Theory.AxiomPin

namespace Minidregg.Compiler.FnWire

set_option autoImplicit false

open Minidregg.Kernel
open Minidregg.Compiler

/-! ## List plumbing -/

theorem take_of_append {a r : List UInt8} {w : Nat} (h : a.length = w) :
    (a ++ r).take w = a := by subst h; exact List.take_left

theorem drop_of_append {a r : List UInt8} {w : Nat} (h : a.length = w) :
    (a ++ r).drop w = r := by subst h; exact List.drop_left

theorem header_no_cr {b : List UInt8} (h : classOk .header b = true) :
    ∀ x ∈ b, (x != 13) = true := by
  intro x hx
  simp only [classOk, List.all_eq_true] at h
  have hx' := h x hx
  simp only [headerOctet, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq] at hx'
  have : x ≠ 13 := by
    intro e; subst e; simp at hx'
  simpa using this

theorem takeWhile_dropWhile_cr : ∀ (b rest : List UInt8), (∀ x ∈ b, (x != 13) = true) →
    (b ++ 13 :: rest).takeWhile (· != 13) = b ∧
      (b ++ 13 :: rest).dropWhile (· != 13) = 13 :: rest
  | [], rest, _ => by simp
  | y :: ys, rest, h => by
      have hy := h y (by simp)
      have ih := takeWhile_dropWhile_cr ys rest (fun x hx => h x (by simp [hx]))
      simp only [List.cons_append, List.takeWhile_cons, List.dropWhile_cons, hy, ih,
        if_true, and_self]

/-! ## Lines -/

theorem lines_nil (w : Nat) : lines w [] = [] := by rw [lines]; simp

theorem lines_short {w : Nat} {t : List UInt8} (hw : 0 < w) (ht : t ≠ []) (hle : t.length ≤ w) :
    lines w t = t ++ [13, 10] := by
  rw [lines]; simp [ht, hle]; omega

theorem lines_long {w : Nat} {t : List UInt8} (hw : 0 < w) (hgt : w < t.length) :
    lines w t = t.take w ++ 13 :: 10 :: lines w (t.drop w) := by
  rw [lines]
  have ht : t ≠ [] := by intro h; subst h; simp at hgt
  have : ¬ t.length ≤ w := by omega
  simp [ht, this]; omega

theorem lines_ne_nil {w : Nat} {t : List UInt8} (hw : 0 < w) (ht : t ≠ []) : lines w t ≠ [] := by
  by_cases hle : t.length ≤ w
  · rw [lines_short hw ht hle]; simp
  · rw [lines_long hw (by omega)]; simp

theorem unlines_lines {w : Nat} (hw : 0 < w) :
    ∀ (n : Nat) (t : List UInt8), t.length = n → unlines w (lines w t) = t := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro t hn
    by_cases ht : t = []
    · subst ht; rw [lines_nil, unlines]; simp
    · by_cases hle : t.length ≤ w
      · rw [lines_short hw ht hle, unlines]
        have : t.length + 2 ≤ w + 2 := by omega
        simp [ht, this]; omega
      · have hgt : w < t.length := by omega
        rw [lines_long hw hgt]
        have hd : t.drop w ≠ [] := by
          intro h; have := congrArg List.length h; simp at this; omega
        have hL := lines_ne_nil hw hd
        have hLpos : 0 < (lines w (t.drop w)).length := by
          cases hc : lines w (t.drop w) with
          | nil => exact absurd hc hL
          | cons _ _ => simp
        have htw : (t.take w).length = w := by simp; omega
        rw [unlines]
        have hlen : ¬ (t.take w ++ 13 :: 10 :: lines w (t.drop w)).length ≤ w + 2 := by
          simp only [List.length_append, List.length_cons, htw]; omega
        have hne : ¬ (t.take w ++ 13 :: 10 :: lines w (t.drop w) = [] ∨ w = 0) := by
          simp; omega
        rw [if_neg hne, if_neg hlen, take_of_append htw]
        have hdrop : (t.take w ++ 13 :: 10 :: lines w (t.drop w)).drop (w + 2) =
            lines w (t.drop w) := by
          rw [List.drop_append]; simp [htw]
        rw [hdrop, ih (t.drop w).length (by simp; omega) (t.drop w) rfl, List.take_append_drop]

theorem unlines_lines' {w : Nat} (hw : 0 < w) (t : List UInt8) : unlines w (lines w t) = t :=
  unlines_lines hw t.length t rfl

/-! ## Enumerations -/

theorem position_lt : ∀ {s : String} {names : List String}, s ∈ names →
    position s names < names.length
  | _, [], h => by simp at h
  | s, x :: xs, h => by
      simp only [position, List.length_cons]
      split
      · omega
      · have : s ∈ xs := by
          rcases List.mem_cons.mp h with e | e
          · exact absurd e.symm (by assumption)
          · exact e
        have := position_lt this; omega

theorem getElem_position : ∀ {s : String} {names : List String} (h : s ∈ names),
    names[position s names]'(position_lt h) = s
  | _, [], h => by simp at h
  | s, x :: xs, h => by
      by_cases e : x = s
      · simp [position, e]
      · have hs : s ∈ xs := by
          rcases List.mem_cons.mp h with e' | e'
          · exact absurd e'.symm e
          · exact e'
        simp only [position, e, if_false, List.getElem_cons_succ]
        exact getElem_position hs

theorem position_getElem : ∀ {names : List String}, distinct names = true →
    ∀ (i : Nat) (hi : i < names.length), position names[i] names = i
  | [], _, i, hi => by simp at hi
  | x :: xs, hd, i, hi => by
      simp only [distinct, Bool.and_eq_true, Bool.not_eq_true'] at hd
      cases i with
      | zero => simp [position]
      | succ i =>
          simp only [List.getElem_cons_succ, position]
          have hmem : xs[i]'(by simp at hi; omega) ∈ xs := List.getElem_mem _
          have hne : x ≠ xs[i]'(by simp at hi; omega) := by
            intro e
            have : xs.contains x = true := by rw [e]; simp [hmem]
            rw [hd.1] at this; cases this
          simp only [hne, if_false]
          rw [position_getElem hd.2 i]

/-! ## Encoder inversions -/

theorem encode_const {o : List UInt8} {v : Value} {b : List UInt8} :
    encode (.const o) v = .ok b ↔ v = .null ∧ b = o := by
  cases v <;> simp [encode, eq_comm]

theorem encode_uint {w lo hi : Nat} {v : Value} {b : List UInt8} :
    encode (.uint w lo hi) v = .ok b ↔
      ∃ n, v = .nat n ∧ lo ≤ n ∧ n ≤ hi ∧ b = beBytes w n := by
  cases v with
  | nat n =>
    simp only [encode]
    by_cases hc : lo ≤ n ∧ n ≤ hi
    · rw [if_pos hc]; constructor
      · intro h; cases h; exact ⟨n, rfl, hc.1, hc.2, rfl⟩
      · rintro ⟨m, hm, -, -, rfl⟩; cases hm; rfl
    · rw [if_neg hc]; constructor
      · intro h; cases h
      · rintro ⟨m, hm, h1, h2, -⟩; cases hm; exact absurd ⟨h1, h2⟩ hc
  | _ => simp [encode]

theorem encode_bytes {w lo hi : Nat} {c : OctetClass} {v : Value} {b : List UInt8} :
    encode (.bytes w lo hi c) v = .ok b ↔
      ∃ bs, v = .octets bs ∧ lo ≤ bs.length ∧ bs.length ≤ hi ∧ classOk c bs = true ∧
        b = beBytes w bs.length ++ bs := by
  cases v with
  | octets bs =>
    simp only [encode]
    by_cases hc : lo ≤ bs.length ∧ bs.length ≤ hi ∧ classOk c bs = true
    · rw [if_pos hc]; constructor
      · intro h; cases h; exact ⟨bs, rfl, hc.1, hc.2.1, hc.2.2, rfl⟩
      · rintro ⟨m, hm, -, -, -, rfl⟩; cases hm; rfl
    · rw [if_neg hc]; constructor
      · intro h; cases h
      · rintro ⟨m, hm, h1, h2, h3, -⟩; cases hm; exact absurd ⟨h1, h2, h3⟩ hc
  | _ => simp [encode]

theorem encode_rest {lo hi : Nat} {c : OctetClass} {v : Value} {b : List UInt8} :
    encode (.rest lo hi c) v = .ok b ↔
      v = .octets b ∧ lo ≤ b.length ∧ b.length ≤ hi ∧ classOk c b = true := by
  cases v with
  | octets bs =>
    simp only [encode]
    by_cases hc : lo ≤ bs.length ∧ bs.length ≤ hi ∧ classOk c bs = true
    · rw [if_pos hc]; constructor
      · intro h; cases h; exact ⟨rfl, hc⟩
      · rintro ⟨hm, -⟩; cases hm; rfl
    · rw [if_neg hc]; constructor
      · intro h; cases h
      · rintro ⟨hm, h⟩; cases hm; exact absurd h hc
  | _ => simp [encode]

theorem encode_line {lo hi : Nat} {c : OctetClass} {v : Value} {b : List UInt8} :
    encode (.line lo hi c) v = .ok b ↔
      ∃ bs, v = .octets bs ∧ lo ≤ bs.length ∧ bs.length ≤ hi ∧ classOk c bs = true ∧
        b = bs ++ [13, 10] := by
  cases v with
  | octets bs =>
    simp only [encode]
    by_cases hc : lo ≤ bs.length ∧ bs.length ≤ hi ∧ classOk c bs = true
    · rw [if_pos hc]; constructor
      · intro h; cases h; exact ⟨bs, rfl, hc.1, hc.2.1, hc.2.2, rfl⟩
      · rintro ⟨m, hm, -, -, -, rfl⟩; cases hm; rfl
    · rw [if_neg hc]; constructor
      · intro h; cases h
      · rintro ⟨m, hm, h1, h2, h3, -⟩; cases hm; exact absurd ⟨h1, h2, h3⟩ hc
  | _ => simp [encode]

theorem encode_base64Lines {width lo hi : Nat} {v : Value} {b : List UInt8} :
    encode (.base64Lines width lo hi) v = .ok b ↔
      ∃ bs, v = .octets bs ∧ lo ≤ bs.length ∧ bs.length ≤ hi ∧
        b = lines width (Base64.encode bs) := by
  cases v with
  | octets bs =>
    simp only [encode]
    by_cases hc : lo ≤ bs.length ∧ bs.length ≤ hi
    · rw [if_pos hc]; constructor
      · intro h; cases h; exact ⟨bs, rfl, hc.1, hc.2, rfl⟩
      · rintro ⟨m, hm, -, -, rfl⟩; cases hm; rfl
    · rw [if_neg hc]; constructor
      · intro h; cases h
      · rintro ⟨m, hm, h1, h2, -⟩; cases hm; exact absurd ⟨h1, h2⟩ hc
  | _ => simp [encode]

theorem encode_enum {w base : Nat} {names : List String} {v : Value} {b : List UInt8} :
    encode (.enum w base names) v = .ok b ↔
      ∃ s, v = .name s ∧ s ∈ names ∧ b = beBytes w (base + position s names) := by
  cases v with
  | name s =>
    simp only [encode]
    by_cases hc : s ∈ names
    · rw [if_pos hc]; constructor
      · intro h; cases h; exact ⟨s, rfl, hc, rfl⟩
      · rintro ⟨m, hm, -, rfl⟩; cases hm; rfl
    · rw [if_neg hc]; constructor
      · intro h; cases h
      · rintro ⟨m, hm, h1, -⟩; cases hm; exact absurd h1 hc
  | _ => simp [encode]

theorem encode_seqNil {v : Value} {b : List UInt8} :
    encode .seqNil v = .ok b ↔ v = .list [] ∧ b = [] := by
  cases v with
  | list vs => cases vs <;> simp [encode, eq_comm]
  | _ => simp [encode]

theorem encode_seqCons {h t : Grammar} {v : Value} {b : List UInt8} :
    encode (.seqCons h t) v = .ok b ↔
      ∃ x xs a c, v = .list (x :: xs) ∧ encode h x = .ok a ∧ encode t (.list xs) = .ok c ∧
        b = a ++ c := by
  cases v with
  | list vs =>
    cases vs with
    | nil => simp [encode]
    | cons x xs =>
      simp only [encode]
      constructor
      · intro hb
        split at hb
        · rename_i a c ha hc; cases hb; exact ⟨x, xs, a, c, rfl, ha, hc, rfl⟩
        · cases hb
        · cases hb
      · rintro ⟨x', xs', a, c, he, ha, hc, rfl⟩
        cases he
        rw [ha, hc]
  | _ => simp [encode]

theorem encode_tagNil {w : Nat} {v : Value} {b : List UInt8} :
    encode (.tagNil w) v ≠ .ok b := by
  cases v <;> simp [encode]

theorem encode_tagArm {w code : Nat} {name : String} {arm more : Grammar} {v : Value}
    {b : List UInt8} :
    encode (.tagArm w code name arm more) v = .ok b ↔
      ∃ n x, v = .tagged n x ∧
        ((n = name ∧ ∃ a, encode arm x = .ok a ∧ b = beBytes w code ++ a) ∨
         (n ≠ name ∧ encode more (.tagged n x) = .ok b)) := by
  cases v with
  | tagged n x =>
    simp only [encode]
    by_cases e : n = name
    · subst e
      simp only [if_true]
      constructor
      · intro hb
        split at hb
        · rename_i a ha; cases hb; exact ⟨n, x, rfl, Or.inl ⟨rfl, a, ha, rfl⟩⟩
        · cases hb
      · rintro ⟨n', x', he, (⟨-, a, ha, rfl⟩ | ⟨hne, -⟩)⟩
        · cases he; rw [ha]
        · cases he; exact absurd rfl hne
    · simp only [e, if_false]
      constructor
      · intro hb; exact ⟨n, x, rfl, Or.inr ⟨e, hb⟩⟩
      · rintro ⟨n', x', he, (⟨hn, -⟩ | ⟨-, hb⟩)⟩
        · cases he; exact absurd hn e
        · cases he; exact hb
  | _ => simp [encode]

theorem encode_maybe {g : Grammar} {v : Value} {b : List UInt8} :
    encode (.maybe g) v = .ok b ↔
      (v = .list [] ∧ b = []) ∨ ∃ x, v = .list [x] ∧ encode g x = .ok b := by
  cases v with
  | list vs =>
    match vs with
    | [] => simp [encode, eq_comm]
    | [x] => simp [encode]
    | _ :: _ :: _ => simp [encode]
  | _ => simp [encode]

theorem encode_where {g : Grammar} {cs : List Check} {v : Value} {b : List UInt8} :
    encode (.where_ g cs) v = .ok b ↔ encode g v = .ok b ∧ checksHold v cs = true := by
  simp only [encode]
  cases he : encode g v with
  | ok a =>
    by_cases hc : checksHold v cs = true
    · simp only [hc, if_true]; constructor
      · intro h; cases h; exact ⟨rfl, trivial⟩
      · rintro ⟨h, -⟩; exact h
    · simp only [hc, if_false, Bool.false_eq_true]; constructor
      · intro h; cases h
      · rintro ⟨-, h⟩; exact h.elim
  | error e => simp

theorem encode_frame {magic : List UInt8} {version kind : UInt8} {max : Nat} {g : Grammar}
    {v : Value} {b : List UInt8} :
    encode (.frame magic version kind max g) v = .ok b ↔
      ∃ p, encode g v = .ok p ∧ p.length ≤ max ∧
        b = framePrefix magic version kind p ++ Blake3.hash (framePrefix magic version kind p) := by
  simp only [encode]
  cases he : encode g v with
  | ok p =>
    by_cases hc : p.length ≤ max
    · simp only [hc, if_true]; constructor
      · intro h; cases h; exact ⟨p, rfl, hc, rfl⟩
      · rintro ⟨q, hq, -, rfl⟩; cases hq; rfl
    · simp only [hc, if_false]; constructor
      · intro h; cases h
      · rintro ⟨q, hq, h, -⟩; cases hq; exact absurd h hc
  | error e => simp

theorem encode_sized {w lo hi : Nat} {g : Grammar} {v : Value} {b : List UInt8} :
    encode (.sized w lo hi g) v = .ok b ↔
      ∃ p, encode g v = .ok p ∧ lo ≤ p.length ∧ p.length ≤ hi ∧
        b = beBytes w p.length ++ p := by
  simp only [encode]
  cases he : encode g v with
  | ok p =>
    by_cases hc : lo ≤ p.length ∧ p.length ≤ hi
    · simp only [hc, and_self, if_true]; constructor
      · intro h; cases h; exact ⟨p, rfl, hc.1, hc.2, rfl⟩
      · rintro ⟨q, hq, -, -, rfl⟩; cases hq; rfl
    · simp only [hc, if_false]; constructor
      · intro h; cases h
      · rintro ⟨q, hq, h1, h2, -⟩; cases hq; exact absurd ⟨h1, h2⟩ hc
  | error e => simp

/-! ## Static facts -/

theorem widthOk_pos {w : Nat} (h : widthOk w = true) : 0 < w := by
  simp [widthOk] at h; omega

theorem nonempty_of_tagWidth {g : Grammar} {w : Nat} (h : g.tagWidth = some w) :
    g.nonempty = true := by
  cases g <;> simp_all [Grammar.tagWidth, Grammar.nonempty]

theorem base64_encode_ne_nil : ∀ {bs : List UInt8}, bs ≠ [] → Base64.encode bs ≠ []
  | [], h => absurd rfl h
  | [_], _ => by simp [Base64.encode]
  | [_, _], _ => by simp [Base64.encode]
  | _ :: _ :: _ :: _, _ => by simp [Base64.encode]

theorem tag_codes_lt : ∀ (g : Grammar) (w : Nat), g.wf = true → g.tagWidth = some w →
    ∀ c ∈ g.tagCodes, c < 256 ^ w := by
  intro g
  induction g with
  | tagArm w' code name arm more _ ihmore =>
    intro w hwf htw c hc
    simp only [Grammar.tagWidth, Option.some.injEq] at htw
    subst htw
    simp only [Grammar.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
    simp only [Grammar.tagCodes, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hwf.1.1.1.1.1.2
    · exact ihmore w' hwf.2 hwf.1.1.1.1.2 c hc
  | _ => intro w _ _ c hc; simp [Grammar.tagCodes] at hc

theorem encode_tag_prefix : ∀ (g : Grammar) (w : Nat) (v : Value) (b : List UInt8),
    g.wf = true → g.tagWidth = some w → encode g v = .ok b →
    ∃ c ∈ g.tagCodes, ∃ b', b = beBytes w c ++ b' := by
  intro g
  induction g with
  | tagNil w' => intro w v b _ _ he; exact absurd he encode_tagNil
  | tagArm w' code name arm more _ ihmore =>
    intro w v b hwf htw he
    simp only [Grammar.tagWidth, Option.some.injEq] at htw
    subst htw
    simp only [Grammar.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
    obtain ⟨n, x, rfl, (⟨-, a, -, rfl⟩ | ⟨-, hm⟩)⟩ := encode_tagArm.mp he
    · exact ⟨code, by simp [Grammar.tagCodes], a, rfl⟩
    · obtain ⟨c, hc, b', rfl⟩ := ihmore w' _ _ hwf.2 hwf.1.1.1.1.2 hm
      exact ⟨c, by simp [Grammar.tagCodes, hc], b', rfl⟩
  | _ => intro w v b _ htw; simp [Grammar.tagWidth] at htw

theorem encode_ne_nil : ∀ (g : Grammar) (v : Value) (b : List UInt8),
    g.wf = true → g.nonempty = true → encode g v = .ok b → b ≠ [] := by
  intro g
  induction g with
  | const o =>
    intro v b _ hne he
    obtain ⟨-, rfl⟩ := encode_const.mp he
    simpa [Grammar.nonempty] using hne
  | uint w lo hi =>
    intro v b hwf _ he
    obtain ⟨n, -, -, -, rfl⟩ := encode_uint.mp he
    simp only [Grammar.wf, Bool.and_eq_true] at hwf
    have := widthOk_pos hwf.1.1
    intro h; have := congrArg List.length h; simp [length_beBytes] at this; omega
  | bytes w lo hi c =>
    intro v b hwf _ he
    obtain ⟨bs, -, -, -, -, rfl⟩ := encode_bytes.mp he
    simp only [Grammar.wf, Bool.and_eq_true] at hwf
    have := widthOk_pos hwf.1.1
    intro h; have := congrArg List.length h; simp [length_beBytes] at this; omega
  | rest lo hi c =>
    intro v b _ hne he
    obtain ⟨-, h1, -, -⟩ := encode_rest.mp he
    simp [Grammar.nonempty] at hne
    intro h; subst h; simp at h1; omega
  | line lo hi c =>
    intro v b _ _ he
    obtain ⟨bs, -, -, -, -, rfl⟩ := encode_line.mp he
    simp
  | base64Lines width lo hi =>
    intro v b hwf hne he
    obtain ⟨bs, -, h1, -, rfl⟩ := encode_base64Lines.mp he
    simp [Grammar.nonempty] at hne
    simp only [Grammar.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    have hbs : bs ≠ [] := by intro h; subst h; simp at h1; omega
    exact lines_ne_nil hwf.1 (base64_encode_ne_nil hbs)
  | enum w base names =>
    intro v b hwf _ he
    obtain ⟨s, -, -, rfl⟩ := encode_enum.mp he
    simp only [Grammar.wf, Bool.and_eq_true] at hwf
    have := widthOk_pos hwf.1.1.1
    intro h; have := congrArg List.length h; simp [length_beBytes] at this; omega
  | seqNil => intro v b _ hne; simp [Grammar.nonempty] at hne
  | seqCons h t ihh iht =>
    intro v b hwf hne he
    obtain ⟨x, xs, a, c, rfl, ha, hc, rfl⟩ := encode_seqCons.mp he
    simp only [Grammar.wf, Bool.and_eq_true] at hwf
    simp only [Grammar.nonempty, Bool.or_eq_true] at hne
    rcases hne with hne | hne
    · have := ihh x a hwf.1.1.1 hne ha; simp [this]
    · have := iht (.list xs) c hwf.2 hne hc; simp [this]
  | tagNil w => intro v b _ _ he; exact absurd he encode_tagNil
  | tagArm w code name arm more _ ihmore =>
    intro v b hwf _ he
    simp only [Grammar.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
    obtain ⟨n, x, rfl, (⟨-, a, -, rfl⟩ | ⟨-, hm⟩)⟩ := encode_tagArm.mp he
    · have := widthOk_pos hwf.1.1.1.1.1.1
      intro h; have := congrArg List.length h; simp [length_beBytes] at this; omega
    · exact ihmore _ _ hwf.2 (nonempty_of_tagWidth hwf.1.1.1.1.2) hm
  | maybe g _ => intro v b _ hne; simp [Grammar.nonempty] at hne
  | where_ g cs ih =>
    intro v b hwf hne he
    simp only [Grammar.wf, Bool.and_eq_true] at hwf
    exact ih v b hwf.2 (by simpa [Grammar.nonempty] using hne) (encode_where.mp he).1
  | frame magic version kind max g _ =>
    intro v b _ _ he
    obtain ⟨p, -, -, rfl⟩ := encode_frame.mp he
    simp [framePrefix]
  | sized w lo hi g _ =>
    intro v b hwf _ he
    obtain ⟨p, -, -, -, rfl⟩ := encode_sized.mp he
    simp only [Grammar.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    have := widthOk_pos hwf.1.1.1
    intro h; have := congrArg List.length h; simp [length_beBytes] at this; omega

/-! ## dec ∘ enc -/

/-- **dec ∘ enc = id.** For every well-formed grammar, the encoding of a value decodes to
that value and leaves exactly the octets that followed it, when the grammar is delimited
(or nothing follows). -/
theorem decode_encode : ∀ (g : Grammar) (v : Value) (b r : List UInt8),
    g.wf = true → encode g v = .ok b → (g.delimited = true ∨ r = []) →
    decode g (b ++ r) = .ok (v, r) := by
  intro g
  induction g with
  | const o =>
    intro v b r _ he _
    obtain ⟨rfl, rfl⟩ := encode_const.mp he
    simp [decode]
  | uint w lo hi =>
    intro v b r hwf he _
    obtain ⟨n, rfl, h1, h2, rfl⟩ := encode_uint.mp he
    simp only [Grammar.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    have hlen := length_beBytes w n
    have hv : beValue (beBytes w n) = n := beValue_beBytes (by omega)
    simp only [decode, take_of_append hlen, drop_of_append hlen, hv]
    rw [if_pos (by simp [hlen]; omega)]
  | bytes w lo hi c =>
    intro v b r hwf he _
    obtain ⟨bs, rfl, h1, h2, h3, rfl⟩ := encode_bytes.mp he
    simp only [Grammar.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    have hlen := length_beBytes w bs.length
    have hv : beValue (beBytes w bs.length) = bs.length := beValue_beBytes (by omega)
    rw [List.append_assoc]
    simp only [decode, take_of_append hlen, drop_of_append hlen, hv, List.take_left,
      List.drop_left]
    rw [if_pos (by simp [hlen, h3]; omega)]
  | rest lo hi c =>
    intro v b r _ he hd
    rcases hd with hd | rfl
    · simp [Grammar.delimited] at hd
    obtain ⟨rfl, h1, h2, h3⟩ := encode_rest.mp he
    simp [decode, h1, h2, h3]
  | line lo hi c =>
    intro v b r hwf he _
    obtain ⟨bs, rfl, h1, h2, h3, rfl⟩ := encode_line.mp he
    simp only [Grammar.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
    obtain ⟨-, rfl⟩ := hwf
    obtain ⟨ht, hd⟩ := takeWhile_dropWhile_cr bs (10 :: r) (header_no_cr h3)
    have hx : bs ++ [13, 10] ++ r = bs ++ 13 :: 10 :: r := by simp
    rw [hx]
    simp only [decode, ht, hd]
    rw [if_pos (by simp [h1, h2, h3])]
    simp
  | base64Lines width lo hi =>
    intro v b r hwf he hd
    rcases hd with hd | rfl
    · simp [Grammar.delimited] at hd
    obtain ⟨bs, rfl, h1, h2, rfl⟩ := encode_base64Lines.mp he
    simp only [Grammar.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    simp [decode, unlines_lines' hwf.1, Base64.decode_encode, h1, h2]
  | enum w base names =>
    intro v b r hwf he _
    obtain ⟨s, rfl, hs, rfl⟩ := encode_enum.mp he
    simp only [Grammar.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    have hpos := position_lt hs
    have hlen := length_beBytes w (base + position s names)
    have hv : beValue (beBytes w (base + position s names)) = base + position s names :=
      beValue_beBytes (by omega)
    simp only [decode, take_of_append hlen, drop_of_append hlen, hv]
    rw [dif_pos (by simp [hlen]; omega)]
    simp only [Nat.add_sub_cancel_left, getElem_position hs]
  | seqNil =>
    intro v b r _ he _
    obtain ⟨rfl, rfl⟩ := encode_seqNil.mp he
    simp [decode]
  | seqCons h t ihh iht =>
    intro v b r hwf he hd
    obtain ⟨x, xs, a, c, rfl, ha, hc, rfl⟩ := encode_seqCons.mp he
    simp only [Grammar.wf, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hwf
    obtain ⟨⟨⟨hwh, -⟩, hlast⟩, hwt⟩ := hwf
    have hdt : t.delimited = true ∨ r = [] := by
      rcases hd with hd | hd
      · simp only [Grammar.delimited, Bool.and_eq_true] at hd; exact Or.inl hd.2
      · exact Or.inr hd
    have h2 := iht (.list xs) c r hwt hc hdt
    have hdh : h.delimited = true ∨ c ++ r = [] := by
      rcases hlast with hl | hl
      · subst hl
        obtain ⟨-, rfl⟩ := encode_seqNil.mp hc
        rcases hd with hd | hd
        · simp only [Grammar.delimited, Bool.and_eq_true] at hd; exact Or.inl hd.1
        · simp [hd]
      · exact Or.inl hl
    have h1 := ihh x a (c ++ r) hwh ha hdh
    rw [List.append_assoc]
    simp only [decode, h1, h2]
  | tagNil w => intro v b r _ he; exact absurd he encode_tagNil
  | tagArm w code name arm more iharm ihmore =>
    intro v b r hwf he hd
    simp only [Grammar.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.not_eq_true'] at hwf
    obtain ⟨⟨⟨⟨⟨⟨hw, hcode⟩, htw⟩, hcodes⟩, -⟩, hwarm⟩, hwmore⟩ := hwf
    have hda : arm.delimited = true ∨ r = [] := by
      rcases hd with hd | hd
      · simp only [Grammar.delimited, Bool.and_eq_true] at hd; exact Or.inl hd.1
      · exact Or.inr hd
    have hdm : more.delimited = true ∨ r = [] := by
      rcases hd with hd | hd
      · simp only [Grammar.delimited, Bool.and_eq_true] at hd; exact Or.inl hd.2
      · exact Or.inr hd
    obtain ⟨n, x, rfl, (⟨rfl, a, ha, rfl⟩ | ⟨hne, hm⟩)⟩ := encode_tagArm.mp he
    · have hlen := length_beBytes w code
      have hv := beValue_beBytes hcode
      have h1 := iharm x a r hwarm ha hda
      rw [List.append_assoc]
      simp only [decode, take_of_append hlen, drop_of_append hlen, hv, h1]
      rw [if_pos (by simp [hlen])]
    · obtain ⟨c, hcmem, b', rfl⟩ := encode_tag_prefix more w _ _ hwmore htw hm
      have hc : c < 256 ^ w := tag_codes_lt more w hwmore htw c hcmem
      have hne' : c ≠ code := by
        intro e; subst e
        have : more.tagCodes.contains c = true := by simp [hcmem]
        rw [hcodes] at this; cases this
      have h2 := ihmore (.tagged n x) (beBytes w c ++ b') r hwmore hm hdm
      simp only [decode]
      rw [if_neg]
      · exact h2
      · intro hh
        have hv := hh.2
        rw [List.append_assoc, take_of_append (length_beBytes w c), beValue_beBytes hc] at hv
        exact hne' hv
  | maybe g ih =>
    intro v b r hwf he hd
    rcases hd with hd | rfl
    · simp [Grammar.delimited] at hd
    simp only [Grammar.wf, Bool.and_eq_true] at hwf
    rcases encode_maybe.mp he with ⟨rfl, rfl⟩ | ⟨x, rfl, hx⟩
    · simp [decode]
    · have hne := encode_ne_nil g x b hwf.1 hwf.2 hx
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
      have h1 := ih x (y :: ys) [] hwf.1 hx (Or.inr rfl)
      simp only [List.append_nil] at h1 ⊢
      simp only [decode, h1]
  | where_ g cs ih =>
    intro v b r hwf he hd
    obtain ⟨hg, hc⟩ := encode_where.mp he
    simp only [Grammar.wf, Bool.and_eq_true] at hwf
    have h1 := ih v b r hwf.2 hg (by simpa [Grammar.delimited] using hd)
    simp only [decode, h1, hc, if_true]
  | frame magic version kind max g ih =>
    intro v b r hwf he _
    obtain ⟨p, hp, hmax, rfl⟩ := encode_frame.mp he
    simp only [Grammar.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
    obtain ⟨⟨hmagic, hmax32⟩, hwg⟩ := hwf
    obtain ⟨m0, m1, m2, m3, rfl⟩ : ∃ m0 m1 m2 m3, magic = [m0, m1, m2, m3] := by
      match magic, hmagic with
      | [m0, m1, m2, m3], _ => exact ⟨m0, m1, m2, m3, rfl⟩
    have h4 : (2 : Nat) ^ 32 = 256 ^ 4 := by decide
    have hv0 : beValue (beBytes 4 p.length) = p.length := beValue_beBytes (by omega)
    obtain ⟨l0, l1, l2, l3, hl⟩ : ∃ l0 l1 l2 l3, beBytes 4 p.length = [l0, l1, l2, l3] := by
      have := length_beBytes 4 p.length
      match hb : beBytes 4 p.length, this with
      | [l0, l1, l2, l3], _ => exact ⟨l0, l1, l2, l3, rfl⟩
    rw [hl] at hv0
    have hp' := ih v p [] hwg hp (Or.inr rfl)
    rw [List.append_nil] at hp'
    generalize hDdef : Blake3.hash (framePrefix [m0, m1, m2, m3] version kind p) = D
    have hD : D.length = 32 := by rw [← hDdef]; exact Blake3.length_hash _
    have hDeq : D = Blake3.hash ([m0, m1, m2, m3] ++ version :: kind :: ([l0, l1, l2, l3] ++ p)) := by
      rw [← hDdef, framePrefix, hl]
    have hx : framePrefix [m0, m1, m2, m3] version kind p ++ D ++ r =
        m0 :: m1 :: m2 :: m3 :: version :: kind :: l0 :: l1 :: l2 :: l3 :: (p ++ (D ++ r)) := by
      simp [framePrefix, hl]
    rw [hx]
    simp only [decode, hv0, List.take_left, List.drop_left, take_of_append hD,
      drop_of_append hD, hp']
    rw [if_pos (by simp [hmax, hD]), if_pos hDeq]
  | sized w lo hi g ih =>
    intro v b r hwf he _
    obtain ⟨p, hp, h1, h2, rfl⟩ := encode_sized.mp he
    simp only [Grammar.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨⟨hw, hlh⟩, hhi⟩, hwg⟩ := hwf
    have hlen := length_beBytes w p.length
    have hv : beValue (beBytes w p.length) = p.length := beValue_beBytes (by omega)
    have hp' := ih v p [] hwg hp (Or.inr rfl)
    rw [List.append_nil] at hp'
    rw [List.append_assoc]
    simp only [decode, take_of_append hlen, drop_of_append hlen, hv, List.take_left,
      List.drop_left, hp']
    rw [if_pos (by simp [hlen]; omega)]

/-! ## enc ∘ dec -/

theorem decode_tag_name : ∀ (g : Grammar) (xs : List UInt8) (v : Value) (r : List UInt8),
    g.wf = true → (∃ w, g.tagWidth = some w) → decode g xs = .ok (v, r) →
    ∃ n x, v = .tagged n x ∧ n ∈ g.tagNames := by
  intro g
  induction g with
  | tagNil w => intro xs v r _ _ hd; simp [decode] at hd
  | tagArm w code name arm more _ ihmore =>
    intro xs v r hwf _ hd
    simp only [Grammar.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
    simp only [decode] at hd
    split at hd
    · split at hd
      · rename_i x r' _; cases hd; exact ⟨name, x, rfl, by simp [Grammar.tagNames]⟩
      · cases hd
    · obtain ⟨n, x, rfl, hn⟩ := ihmore xs v r hwf.2 ⟨w, hwf.1.1.1.1.2⟩ hd
      exact ⟨n, x, rfl, by simp [Grammar.tagNames, hn]⟩
  | _ => intro xs v r _ hw; obtain ⟨w, hw⟩ := hw; simp [Grammar.tagWidth] at hw

theorem beBytes_take {xs : List UInt8} {w : Nat} (h : w ≤ xs.length) :
    beBytes w (beValue (xs.take w)) = xs.take w := by
  have hl : (xs.take w).length = w := by simp; omega
  have := beBytes_beValue (xs.take w)
  rwa [hl] at this

/-- **enc ∘ dec = id (canonicity).** For every well-formed grammar, an accepted octet
string is the encoding of the value it decodes to, followed by exactly the suffix the
decoder returned: each value has exactly one accepted encoding. -/
theorem encode_decode : ∀ (g : Grammar) (xs : List UInt8) (v : Value) (r : List UInt8),
    g.wf = true → decode g xs = .ok (v, r) → ∃ b, encode g v = .ok b ∧ b ++ r = xs := by
  intro g
  induction g with
  | const o =>
    intro xs v r _ hd
    simp only [decode] at hd
    split at hd
    · rename_i h; cases hd
      refine ⟨o, encode_const.mpr ⟨rfl, rfl⟩, ?_⟩
      conv => rhs; rw [← List.take_append_drop o.length xs]
      rw [h]
    · cases hd
  | uint w lo hi =>
    intro xs v r _ hd
    simp only [decode] at hd
    split at hd
    · rename_i h; cases hd
      refine ⟨_, encode_uint.mpr ⟨_, rfl, h.2.1, h.2.2, rfl⟩, ?_⟩
      rw [beBytes_take h.1, List.take_append_drop]
    · cases hd
  | bytes w lo hi c =>
    intro xs v r _ hd
    simp only [decode] at hd
    split at hd
    · rename_i h; cases hd
      obtain ⟨h0, h1, h2, h3, h4⟩ := h
      have hbl : ((xs.drop w).take (beValue (xs.take w))).length = beValue (xs.take w) := by
        rw [List.length_take]; exact Nat.min_eq_left h3
      refine ⟨_, encode_bytes.mpr ⟨_, rfl, by rw [hbl]; exact h1, by rw [hbl]; exact h2, h4, rfl⟩, ?_⟩
      rw [hbl, beBytes_take h0, List.append_assoc, List.take_append_drop, List.take_append_drop]
    · cases hd
  | rest lo hi c =>
    intro xs v r _ hd
    simp only [decode] at hd
    split at hd
    · rename_i h; cases hd
      exact ⟨xs, encode_rest.mpr ⟨rfl, h.2.1, h.2.2, h.1⟩, List.append_nil xs⟩
    · cases hd
  | line lo hi c =>
    intro xs v r _ hd
    simp only [decode] at hd
    split at hd
    · rename_i h; cases hd
      obtain ⟨h0, h1, h2, h3⟩ := h
      refine ⟨_, encode_line.mpr ⟨_, rfl, h2, h3, h1, rfl⟩, ?_⟩
      rw [List.append_assoc, ← h0, List.take_append_drop, List.takeWhile_append_dropWhile]
    · cases hd
  | base64Lines width lo hi =>
    intro xs v r _ hd
    simp only [decode] at hd
    split at hd
    · rename_i hl
      split at hd
      · rename_i bs hbs
        split at hd
        · rename_i hb; cases hd
          refine ⟨_, encode_base64Lines.mpr ⟨bs, rfl, hb.1, hb.2, rfl⟩, ?_⟩
          rw [Base64.encode_decode hbs, hl, List.append_nil]
        · cases hd
      · cases hd
    · cases hd
  | enum w base names =>
    intro xs v r hwf hd
    simp only [Grammar.wf, Bool.and_eq_true] at hwf
    simp only [decode] at hd
    split at hd
    · rename_i h; cases hd
      have hi : beValue (xs.take w) - base < names.length := by omega
      refine ⟨_, encode_enum.mpr ⟨_, rfl, List.getElem_mem hi, rfl⟩, ?_⟩
      rw [position_getElem hwf.1.2 _ hi, Nat.add_sub_cancel' h.2.1, beBytes_take h.1,
        List.take_append_drop]
    · cases hd
  | seqNil =>
    intro xs v r _ hd
    simp only [decode] at hd; cases hd
    exact ⟨[], encode_seqNil.mpr ⟨rfl, rfl⟩, rfl⟩
  | seqCons h t ihh iht =>
    intro xs v r hwf hd
    simp only [Grammar.wf, Bool.and_eq_true] at hwf
    simp only [decode] at hd
    split at hd
    · rename_i x r1 hx
      split at hd
      · rename_i vs r' hvs
        cases hd
        obtain ⟨a, ha, hae⟩ := ihh xs x r1 hwf.1.1.1 hx
        obtain ⟨c, hc, hce⟩ := iht r1 (.list vs) r hwf.2 hvs
        exact ⟨a ++ c, encode_seqCons.mpr ⟨x, vs, a, c, rfl, ha, hc, rfl⟩,
          by rw [List.append_assoc, hce, hae]⟩
      · cases hd
      · cases hd
    · cases hd
  | tagNil w => intro xs v r _ hd; simp [decode] at hd
  | tagArm w code name arm more iharm ihmore =>
    intro xs v r hwf hd
    simp only [Grammar.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.not_eq_true'] at hwf
    obtain ⟨⟨⟨⟨⟨⟨_, _⟩, htw⟩, _⟩, hnames⟩, hwarm⟩, hwmore⟩ := hwf
    simp only [decode] at hd
    split at hd
    · rename_i hcond
      split at hd
      · rename_i x r' hx; cases hd
        obtain ⟨a, ha, hae⟩ := iharm _ x r hwarm hx
        refine ⟨beBytes w code ++ a, encode_tagArm.mpr ⟨name, x, rfl, Or.inl ⟨rfl, a, ha, rfl⟩⟩, ?_⟩
        rw [← hcond.2, beBytes_take hcond.1, List.append_assoc, hae, List.take_append_drop]
      · cases hd
    · obtain ⟨n, x, rfl, hn⟩ := decode_tag_name more xs v r hwmore ⟨w, htw⟩ hd
      have hne : n ≠ name := by
        intro e; subst e
        have : more.tagNames.contains n = true := by simp [hn]
        rw [hnames] at this; cases this
      obtain ⟨b, hb, hbe⟩ := ihmore xs _ r hwmore hd
      exact ⟨b, encode_tagArm.mpr ⟨n, x, rfl, Or.inr ⟨hne, hb⟩⟩, hbe⟩
  | maybe g ih =>
    intro xs v r hwf hd
    simp only [Grammar.wf, Bool.and_eq_true] at hwf
    simp only [decode] at hd
    split at hd
    · cases hd; exact ⟨[], encode_maybe.mpr (Or.inl ⟨rfl, rfl⟩), rfl⟩
    · split at hd
      · rename_i x r' hx; cases hd
        obtain ⟨b, hb, hbe⟩ := ih _ x r hwf.1 hx
        exact ⟨b, encode_maybe.mpr (Or.inr ⟨x, rfl, hb⟩), hbe⟩
      · cases hd
  | where_ g cs ih =>
    intro xs v r hwf hd
    simp only [Grammar.wf, Bool.and_eq_true] at hwf
    simp only [decode] at hd
    cases hx : decode g xs with
    | error e => rw [hx] at hd; cases hd
    | ok p =>
      obtain ⟨x, r'⟩ := p
      rw [hx] at hd
      by_cases hc : checksHold x cs = true
      · simp only [hc, if_true] at hd
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hd)
        obtain ⟨b, hb, hbe⟩ := ih xs x r' hwf.2 hx
        exact ⟨b, encode_where.mpr ⟨hb, hc⟩, hbe⟩
      · simp only [hc, if_false, Bool.false_eq_true] at hd; cases hd
  | frame magic version kind max g ih =>
    intro xs v r hwf hd
    simp only [Grammar.wf, Bool.and_eq_true] at hwf
    simp only [decode] at hd
    split at hd
    · rename_i m0 m1 m2 m3 ver knd l0 l1 l2 l3 body
      split at hd
      · rename_i hc
        split at hd
        · rename_i ht
          cases hx : decode g (body.take (beValue [l0, l1, l2, l3])) with
          | error e => rw [hx] at hd; cases hd
          | ok q =>
            obtain ⟨x, r'⟩ := q
            rw [hx] at hd
            cases r' with
            | cons _ _ => cases hd
            | nil =>
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hd)
              obtain ⟨p, hp, hpe⟩ := ih _ x [] hwf.2 hx
              rw [List.append_nil] at hpe
              obtain ⟨rfl, rfl, rfl, hn, hlen⟩ := hc
              have hpl : p.length = beValue [l0, l1, l2, l3] := by
                rw [hpe, List.length_take]; omega
              have e4 : beBytes 4 p.length = [l0, l1, l2, l3] := by
                rw [hpl]; exact beBytes_beValue [l0, l1, l2, l3]
              refine ⟨_, encode_frame.mpr ⟨p, hp, by omega, rfl⟩, ?_⟩
              rw [hpe] at e4
              subst hpe
              simp only [framePrefix, e4]
              rw [← ht]
              simp only [List.append_assoc, List.cons_append, List.nil_append,
                List.take_append_drop]
        · cases hd
      · cases hd
    · cases hd
  | sized w lo hi g ih =>
    intro xs v r hwf hd
    simp only [Grammar.wf, Bool.and_eq_true] at hwf
    simp only [decode] at hd
    split at hd
    · rename_i h
      cases hx : decode g ((xs.drop w).take (beValue (xs.take w))) with
      | error e => rw [hx] at hd; cases hd
      | ok q =>
        obtain ⟨x, r'⟩ := q
        rw [hx] at hd
        cases r' with
        | cons _ _ => cases hd
        | nil =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hd)
          obtain ⟨p, hp, hpe⟩ := ih _ x [] hwf.2 hx
          rw [List.append_nil] at hpe
          obtain ⟨h0, h1, h2, h3⟩ := h
          have hpl : p.length = beValue (xs.take w) := by
            rw [hpe, List.length_take]; omega
          refine ⟨_, encode_sized.mpr ⟨p, hp, by omega, by omega, rfl⟩, ?_⟩
          rw [hpl, beBytes_take h0, hpe, List.append_assoc, List.take_append_drop,
            List.take_append_drop]
    · cases hd

/-! ## Whole messages -/

/-- `dec ∘ enc = id` on whole messages, for every well-formed grammar. -/
theorem decodeAll_encode {g : Grammar} {v : Value} {b : List UInt8} (hwf : g.wf = true)
    (he : encode g v = .ok b) : decodeAll g b = .ok v := by
  have := decode_encode g v b [] hwf he (Or.inr rfl)
  rw [List.append_nil] at this
  simp [decodeAll, this]

/-- `enc ∘ dec = id` on whole messages, for every well-formed grammar: canonicity. -/
theorem encode_decodeAll {g : Grammar} {xs : List UInt8} {v : Value} (hwf : g.wf = true)
    (hd : decodeAll g xs = .ok v) : encode g v = .ok xs := by
  simp only [decodeAll] at hd
  cases hv : decode g xs with
  | error e => rw [hv] at hd; cases hd
  | ok q =>
    obtain ⟨v', r⟩ := q
    rw [hv] at hd
    cases r with
    | cons _ _ => cases hd
    | nil =>
      cases hd
      obtain ⟨b, hb, hbe⟩ := encode_decode g xs v [] hwf hv
      rw [List.append_nil] at hbe; rw [hb, hbe]

/-- Each value has at most one accepted encoding, and each accepted encoding one value. -/
theorem decodeAll_injective {g : Grammar} {xs ys : List UInt8} {v : Value} (hwf : g.wf = true)
    (hx : decodeAll g xs = .ok v) (hy : decodeAll g ys = .ok v) : xs = ys := by
  have := encode_decodeAll hwf hx
  rw [encode_decodeAll hwf hy] at this
  cases this; rfl

#assert_axioms decode_encode encode_decode decodeAll_encode encode_decodeAll
  decodeAll_injective unlines_lines' position_getElem getElem_position

/-! ## The decoder's answers (fn `fn-wg-decode-answers`) -/

/-- Every refusal the decoder gives is one of fn's three words; it never answers `limit`
(that is `decodeWithin`'s, before decoding). For EVERY grammar, well formed or not. -/
theorem decode_refusal_mem : ∀ (g : Grammar) (xs : List UInt8) (e : Refusal),
    decode g xs = .error e → e ∈ fnRefusals := by
  intro g
  induction g with
  | seqCons h t ihh iht =>
    intro xs e hd
    simp only [decode] at hd
    split at hd
    · split at hd
      · cases hd
      · cases hd; simp [fnRefusals]
      · rename_i heq; cases hd; exact iht _ _ heq
    · rename_i heq; cases hd; exact ihh _ _ heq
  | tagArm w code name arm more iharm ihmore =>
    intro xs e hd
    simp only [decode] at hd
    split at hd
    · split at hd
      · cases hd
      · rename_i heq; cases hd; exact iharm _ _ heq
    · exact ihmore _ _ hd
  | maybe g ih =>
    intro xs e hd
    simp only [decode] at hd
    split at hd
    · cases hd
    · split at hd
      · cases hd
      · rename_i heq; cases hd; exact ih _ _ heq
  | where_ g cs ih =>
    intro xs e hd
    simp only [decode] at hd
    split at hd
    · split at hd
      · cases hd
      · cases hd; simp [fnRefusals]
    · rename_i heq; cases hd; exact ih _ _ heq
  | frame magic version kind max g ih =>
    intro xs e hd
    simp only [decode] at hd
    split at hd
    · split at hd
      · split at hd
        · split at hd
          · cases hd
          · cases hd; simp [fnRefusals]
          · rename_i heq; cases hd; exact ih _ _ heq
        · cases hd; simp [fnRefusals]
      · cases hd; simp [fnRefusals]
    · cases hd; simp [fnRefusals]
  | sized w lo hi g ih =>
    intro xs e hd
    simp only [decode] at hd
    split at hd
    · split at hd
      · cases hd
      · cases hd; simp [fnRefusals]
      · rename_i heq; cases hd; exact ih _ _ heq
    · cases hd; simp [fnRefusals]
  | base64Lines width lo hi =>
    intro xs e hd
    simp only [decode] at hd
    split at hd
    · split at hd
      · split at hd
        · cases hd
        · cases hd; simp [fnRefusals]
      · cases hd; simp [fnRefusals]
    · cases hd; simp [fnRefusals]
  | seqNil => intro xs e hd; simp [decode] at hd
  | tagNil w => intro xs e hd; simp only [decode] at hd; cases hd; simp [fnRefusals]
  | _ =>
    intro xs e hd
    simp only [decode] at hd
    split at hd
    · cases hd
    · cases hd; simp [fnRefusals]

/-- An accepted answer's rest is a suffix of the input: the decoder consumes from the front
and nothing else. For EVERY grammar. -/
theorem decode_rest_suffix : ∀ (g : Grammar) (xs : List UInt8) (v : Value) (r : List UInt8),
    decode g xs = .ok (v, r) → r <:+ xs := by
  intro g
  induction g with
  | const o =>
    intro xs v r hd; simp only [decode] at hd
    split at hd
    · cases hd; exact List.drop_suffix _ _
    · cases hd
  | uint w lo hi =>
    intro xs v r hd; simp only [decode] at hd
    split at hd
    · cases hd; exact List.drop_suffix _ _
    · cases hd
  | bytes w lo hi c =>
    intro xs v r hd; simp only [decode] at hd
    split at hd
    · cases hd; exact (List.drop_suffix _ _).trans (List.drop_suffix _ _)
    · cases hd
  | rest lo hi c =>
    intro xs v r hd; simp only [decode] at hd
    split at hd
    · cases hd; exact List.nil_suffix
    · cases hd
  | line lo hi c =>
    intro xs v r hd; simp only [decode] at hd
    split at hd
    · cases hd
      refine (List.drop_suffix _ _).trans ?_
      exact ⟨xs.takeWhile (· != 13), List.takeWhile_append_dropWhile⟩
    · cases hd
  | base64Lines width lo hi =>
    intro xs v r hd; simp only [decode] at hd
    split at hd
    · split at hd
      · split at hd
        · cases hd; exact List.nil_suffix
        · cases hd
      · cases hd
    · cases hd
  | enum w base names =>
    intro xs v r hd; simp only [decode] at hd
    split at hd
    · cases hd; exact List.drop_suffix _ _
    · cases hd
  | sized w lo hi g ih =>
    intro xs v r hd; simp only [decode] at hd
    split at hd
    · split at hd
      · obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj hd)
        exact (List.drop_suffix _ _).trans (List.drop_suffix _ _)
      · cases hd
      · cases hd
    · cases hd
  | seqNil => intro xs v r hd; simp only [decode] at hd; cases hd; exact List.suffix_refl _
  | seqCons h t ihh iht =>
    intro xs v r hd; simp only [decode] at hd
    split at hd
    · rename_i x r1 hx
      split at hd
      · rename_i vs r2 hvs
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj hd)
        exact (iht _ _ _ hvs).trans (ihh _ _ _ hx)
      · cases hd
      · cases hd
    · cases hd
  | tagNil w => intro xs v r hd; simp [decode] at hd
  | tagArm w code name arm more iharm ihmore =>
    intro xs v r hd; simp only [decode] at hd
    split at hd
    · split at hd
      · rename_i x r1 hx
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj hd)
        exact (iharm _ _ _ hx).trans (List.drop_suffix _ _)
      · cases hd
    · exact ihmore _ _ _ hd
  | maybe g ih =>
    intro xs v r hd; simp only [decode] at hd
    split at hd
    · cases hd; exact List.nil_suffix
    · split at hd
      · rename_i x r1 hx
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj hd)
        exact ih _ _ _ hx
      · cases hd
  | where_ g cs ih =>
    intro xs v r hd; simp only [decode] at hd
    split at hd
    · rename_i x r1 hx
      split at hd
      · obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj hd)
        exact ih _ _ _ hx
      · cases hd
    · cases hd
  | frame magic version kind max g ih =>
    intro xs v r hd; simp only [decode] at hd
    split at hd
    · rename_i m0 m1 m2 m3 ver knd l0 l1 l2 l3 body
      split at hd
      · split at hd
        · split at hd
          · obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj hd)
            refine (List.drop_suffix _ _).trans ((List.drop_suffix _ _).trans ?_)
            exact ⟨[m0, m1, m2, m3, ver, knd, l0, l1, l2, l3], rfl⟩
          · cases hd
          · cases hd
        · cases hd
      · cases hd
    · cases hd

/-- **fn-wg-decode-answers, Mini's side.** For every grammar and every input the decoder
answers exactly one of: accepted, with a value and a rest that is a suffix of the input
(the octets consumed are the prefix before it); or refused, with one of fn's three words
`trailer`, `where`, `malformed` (a refusal consumes nothing: it carries no position). -/
theorem decode_answers (g : Grammar) (xs : List UInt8) :
    (∃ v r, decode g xs = .ok (v, r) ∧ r <:+ xs) ∨
      (∃ e, decode g xs = .error e ∧ e ∈ fnRefusals) := by
  cases hd : decode g xs with
  | ok p => exact Or.inl ⟨p.1, p.2, rfl, decode_rest_suffix g xs p.1 p.2 hd⟩
  | error e => exact Or.inr ⟨e, rfl, decode_refusal_mem g xs e hd⟩

/-- The `utf8` class is RFC 3629: an overlong encoding and a surrogate are refused, and a
four-octet scalar and the last scalar U+10FFFF are accepted; one past it is refused. -/
theorem utf8Valid_table :
    utf8Valid [0xC0, 0x80] = false ∧ utf8Valid [0xE0, 0x80, 0x80] = false ∧
      utf8Valid [0xED, 0xA0, 0x80] = false ∧ utf8Valid [0xF0, 0x9F, 0x98, 0x80] = true ∧
      utf8Valid [0xF4, 0x8F, 0xBF, 0xBF] = true ∧ utf8Valid [0xF4, 0x90, 0x80, 0x80] = false := by
  decide

#assert_axioms decode_refusal_mem decode_rest_suffix decode_answers utf8Valid_table

end Minidregg.Compiler.FnWire
