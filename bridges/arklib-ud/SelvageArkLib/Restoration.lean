import SelvageArkLib.StateRestoration
import SelvageArkLib.StepCoins

/-!
# Selvage's state-restoration game as an ArkLib restoration adversary

A deterministic Selvage prover `P : SrProver r s` making `t` moves becomes an ArkLib adversary
for `protocol (List.replicate r.k (round r))` with input type `Stmt r ⊕ SrMove r s` and salt type
`Salt s`. A move `⟨st, pfx⟩` with `1 ≤ pfx.length ≤ k` is the ArkLib key of round
`pfx.length - 1` at input `.inl st`. Any other move (a junk query of Selvage's game, which never
affects the final challenges) is the round-zero key at input `.inr move`, an input that is never
in the statement set. The encoding is injective (`decodeKey_encodeMove`), so the adversary makes
exactly `t` oracle queries and the merged ArkLib theorem applies with `Q = t`.
-/

noncomputable section

open Classical

namespace SelvageArkLib.StateRestoration

open Minidregg.Selvage
open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree
open Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration

variable {r : Reduction} [Finite r.PMsg] {s : ℕ}

/-- ArkLib's restoration input: a Selvage statement, or a junk Selvage move. -/
abbrev Input (r : Reduction) (s : ℕ) : Type := Stmt r ⊕ SrMove r s

/-- ArkLib restoration keys for the `n`-round presentation. -/
abbrev RKey (r : Reduction) [Finite r.PMsg] (s n : ℕ) : Type :=
  Key (Input r s) (Minidregg.Selvage.Salt s) (List.replicate n (round r))

/-- Every restoration key answers in Selvage's challenge alphabet. -/
theorem key_challenge_eq : (n : ℕ) → (key : RKey r s n) → key.Challenge = r.Chal
  | 0, key => key.elim
  | _ + 1, .inl _ => rfl
  | n + 1, .inr (_, _, key) => key_challenge_eq n key

/-- The salted prefix recorded by a key, outermost round first. -/
def keyPrefix : (n : ℕ) → RKey r s n → List (r.PMsg × Minidregg.Selvage.Salt s)
  | 0, key => key.elim
  | _ + 1, .inl (_, message, salt) => [(message, salt)]
  | n + 1, .inr (message, salt, key) => (message, salt) :: keyPrefix n key

/-- Encode a salted prefix of length `1 ..= n` at input `z`. -/
def encodePrefix (z : Input r s) :
    (n : ℕ) → List (r.PMsg × Minidregg.Selvage.Salt s) → Option (RKey r s n)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, [(message, salt)] => some (Key.here (round := round r) z message salt)
  | n + 1, (message, salt) :: x :: rest =>
      (encodePrefix z n (x :: rest)).map (Key.later (round := round r) message salt)

theorem encodePrefix_input (z : Input r s) :
    (n : ℕ) → (pfx : List (r.PMsg × Minidregg.Selvage.Salt s)) → (key : RKey r s n) →
    encodePrefix z n pfx = some key → key.input = z ∧ keyPrefix n key = pfx
  | 0, _, _, h => by simp [encodePrefix] at h
  | _ + 1, [], _, h => by simp [encodePrefix] at h
  | _ + 1, [(message, salt)], key, h => by
      simp only [encodePrefix, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
  | n + 1, (message, salt) :: x :: rest, key, h => by
      simp only [encodePrefix, Option.map_eq_some_iff] at h
      obtain ⟨inner, hinner, rfl⟩ := h
      obtain ⟨hz, hp⟩ := encodePrefix_input z n (x :: rest) inner hinner
      exact ⟨hz, by simp [keyPrefix, hp]⟩

/-- The round-zero key carrying a junk input. -/
def junkKey : (n : ℕ) → 0 < n → Input r s → RKey r s n
  | 0, h, _ => absurd h (Nat.lt_irrefl 0)
  | _ + 1, _, z => Key.here (round := round r) z (Classical.arbitrary r.PMsg) (fun _ => false)

theorem junkKey_input : (n : ℕ) → (h : 0 < n) → (z : Input r s) → (junkKey n h z).input = z
  | 0, h, _ => absurd h (Nat.lt_irrefl 0)
  | _ + 1, _, _ => rfl

/-- The restoration key of a Selvage move. -/
def encodeMove (q : SrMove r s) : RKey r s r.k :=
  (encodePrefix (.inl q.stmt) r.k q.pfx).getD (junkKey r.k r.k_pos (.inr q))

/-- Recover the Selvage move from a restoration key. -/
def decodeKey (key : RKey r s r.k) : SrMove r s :=
  match key.input with
  | .inl st => ⟨st, keyPrefix r.k key⟩
  | .inr q => q

theorem decodeKey_encodeMove (q : SrMove r s) : decodeKey (encodeMove q) = q := by
  unfold encodeMove
  cases h : encodePrefix (.inl q.stmt) r.k q.pfx with
  | some key =>
      obtain ⟨hz, hp⟩ := encodePrefix_input (.inl q.stmt) r.k q.pfx key h
      simp only [Option.getD_some, decodeKey, hz, hp]
  | none =>
      simp only [Option.getD_none, decodeKey, junkKey_input]

theorem encodeMove_injective : Function.Injective (encodeMove (r := r) (s := s)) := fun q q' h => by
  rw [← decodeKey_encodeMove q, ← decodeKey_encodeMove q', h]

/-- The restoration oracle's answer at a Selvage move, read in Selvage's alphabet. -/
def toChal {n : ℕ} (key : RKey r s n) (u : key.Challenge) : r.Chal :=
  cast (key_challenge_eq n key) u

/-- A complete ArkLib message sequence from a list of salted messages (missing entries padded). -/
def messagesOf : (n : ℕ) → List (r.PMsg × Minidregg.Selvage.Salt s) →
    Messages (Minidregg.Selvage.Salt s) (List.replicate n (round r))
  | 0, _ => PUnit.unit
  | n + 1, [] => (Classical.arbitrary r.PMsg, (fun _ => false), messagesOf n [])
  | n + 1, (message, salt) :: rest => (message, salt, messagesOf n rest)

/-- The salted messages of a Selvage output, in round order. -/
def outputPrefix (o : SrOutput r s) : List (r.PMsg × Minidregg.Selvage.Salt s) :=
  List.ofFn fun i => (o.πs i, o.σs i)

/-- The restoration oracle specification of the Selvage presentation. -/
abbrev rspec (r : Reduction) [Finite r.PMsg] (s : ℕ) :=
  oracleSpec (Input r s) (Minidregg.Selvage.Salt s) (List.replicate r.k (round r))

/-- The Selvage game's `j` remaining moves, answering each through the restoration oracle. -/
def adversarySteps (P : SrProver r s) :
    ℕ → List r.Chal → OracleComp (rspec r s) (List r.Chal)
  | 0, responses => pure responses
  | j + 1, responses => do
      let u ← liftM ((rspec r s).query (encodeMove (P.move responses)))
      adversarySteps P j (responses ++ [toChal (encodeMove (P.move responses)) u])

/-- **The induced ArkLib adversary** of a Selvage prover with `t` moves: play the moves through
the restoration oracle, then output Selvage's statement, salted messages, and candidate witness. -/
def adversary (P : SrProver r s) (t : ℕ) :
    OracleComp (rspec r s)
      (Input r s × Messages (Minidregg.Selvage.Salt s) (List.replicate r.k (round r)) × r.W) := do
  let responses ← adversarySteps P t []
  let o := P.out responses
  pure (.inl o.stmt, messagesOf r.k (outputPrefix o), o.w')

theorem adversarySteps_queryBound (P : SrProver r s) :
    (j : ℕ) → (responses : List r.Chal) → IsTotalQueryBound (adversarySteps P j responses) j
  | 0, _ => trivial
  | j + 1, responses => by
      simp only [adversarySteps, isTotalQueryBound_query_bind_iff]
      exact ⟨by omega, fun _ => by simpa using adversarySteps_queryBound P j _⟩

/-- The induced adversary makes at most `t` restoration queries. -/
theorem adversary_queryBound (P : SrProver r s) (t : ℕ) :
    IsTotalQueryBound (adversary P t) t := by
  change IsTotalQueryBound (adversary P t) (t + 0)
  exact isTotalQueryBound_bind (adversarySteps_queryBound P t []) fun _ => trivial

/-! ## The adversary phase under one coin per query -/

section Steps

attribute [local instance] SampleableType.ofFintype

/-- The step-coin restoration oracle of the Selvage presentation. -/
abbrev stepImpl (r : Reduction) [Finite r.PMsg] (s : ℕ) :
    QueryImpl (rspec r s) (StateT ((rspec r s).QueryCache × List r.Chal) ProbComp) :=
  StepCoins.stepCoinImpl (C := r.Chal) (key_challenge_eq r.k)

/-- Selvage's log lookup, as an option. -/
def logLookup (L : List (SrMove r s × r.Chal)) (q : SrMove r s) : Option r.Chal :=
  (L.find? fun e => decide (e.1 = q)).map Prod.snd

/-- The restoration cache agrees with Selvage's game log at every move. -/
def CacheAgrees (cache : (rspec r s).QueryCache) (L : List (SrMove r s × r.Chal)) : Prop :=
  ∀ q, (cache (encodeMove q)).map (toChal (encodeMove q)) = logLookup L q

theorem toChal_cast {n : ℕ} (key : RKey r s n) (c : r.Chal) :
    toChal key (cast (key_challenge_eq n key).symm c) = c := by
  simp [toChal]

theorem logLookup_append_of_some {L : List (SrMove r s × r.Chal)} {q : SrMove r s}
    {e : SrMove r s × r.Chal} (h : L.find? (fun e => decide (e.1 = q)) = some e) (q' : SrMove r s) :
    logLookup (L ++ [(q, e.2)]) q' = logLookup L q' := by
  unfold logLookup
  rw [List.find?_append]
  cases hq' : L.find? (fun e => decide (e.1 = q')) with
  | some e' => simp
  | none =>
      have hne : q' ≠ q := by
        rintro rfl
        rw [h] at hq'
        exact Option.some_ne_none _ hq'
      simp [List.find?_cons, Ne.symm hne]

theorem logLookup_append_of_none {L : List (SrMove r s × r.Chal)} {q : SrMove r s}
    (h : L.find? (fun e => decide (e.1 = q)) = none) (c : r.Chal) (q' : SrMove r s) :
    logLookup (L ++ [(q, c)]) q' = if q' = q then some c else logLookup L q' := by
  unfold logLookup
  rw [List.find?_append]
  by_cases hq : q' = q
  · subst hq
    simp [h]
  · simp [hq, Ne.symm hq]

/-- **The adversary phase is Selvage's lazily sampled game.** Starting from a cache that agrees
with log `L`, the induced adversary's remaining moves on coins `cs` (one per move) return
exactly the responses of Selvage's `runFrom P L cs`, consume exactly those coins, and leave a
cache that agrees with the extended log. -/
theorem adversarySteps_run (P : SrProver r s) :
    (cs rest : List r.Chal) → (L : List (SrMove r s × r.Chal)) →
    (cache : (rspec r s).QueryCache) → CacheAgrees cache L →
    ∃ cache', (simulateQ (stepImpl r s) (adversarySteps P cs.length (L.map Prod.snd))).run
        (cache, cs ++ rest) =
          pure ((runFrom P L cs).map Prod.snd, (cache', rest)) ∧
        CacheAgrees cache' (runFrom P L cs)
  | [], rest, L, cache, hagree => ⟨cache, by simp [adversarySteps], hagree⟩
  | c :: cs, rest, L, cache, hagree => by
      set q := P.move (L.map Prod.snd) with hq
      have hrun :
          (simulateQ (stepImpl r s) (adversarySteps P (cs.length + 1) (L.map Prod.snd))).run
              (cache, c :: cs ++ rest) =
            ((stepImpl r s) (encodeMove q)).run (cache, c :: (cs ++ rest)) >>= fun p =>
              (simulateQ (stepImpl r s) (adversarySteps P cs.length
                (L.map Prod.snd ++ [toChal (encodeMove q) p.1]))).run p.2 := by
        simp only [adversarySteps, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          List.cons_append]
        rfl
      rw [List.length_cons, hrun]
      cases hfind : L.find? (fun e => decide (e.1 = q)) with
      | some e =>
          have hlook := hagree q
          rw [show logLookup L q = some e.2 by simp [logLookup, hfind]] at hlook
          obtain ⟨v, hv, hvc⟩ := Option.map_eq_some_iff.mp hlook
          rw [StepCoins.stepCoinImpl_run_cons_some _ hv, pure_bind]
          have hstep : stepOnce P L c = L ++ [(q, e.2)] := by
            rw [stepOnce_eq, ← hq, hfind]
          have hagree' : CacheAgrees cache (L ++ [(q, e.2)]) := fun q' => by
            rw [logLookup_append_of_some hfind]
            exact hagree q'
          obtain ⟨cache', hres, hag⟩ := adversarySteps_run P cs rest _ cache hagree'
          refine ⟨cache', ?_, ?_⟩
          · rw [runFrom_cons, hstep, ← hres, hvc]
            simp
          · rw [runFrom_cons, hstep]
            exact hag
      | none =>
          have hlook := hagree q
          rw [show logLookup L q = none by simp [logLookup, hfind]] at hlook
          have hnone : cache (encodeMove q) = none := Option.map_eq_none_iff.mp hlook
          rw [StepCoins.stepCoinImpl_run_cons_none _ hnone, pure_bind]
          have hstep : stepOnce P L c = L ++ [(q, c)] := by
            rw [stepOnce_eq, ← hq, hfind]
          have hagree' : CacheAgrees
              (cache.cacheQuery (encodeMove q)
                (cast (key_challenge_eq r.k (encodeMove q)).symm c)) (L ++ [(q, c)]) := by
            intro q'
            rw [logLookup_append_of_none hfind]
            by_cases hq' : q' = q
            · subst hq'
              simp [toChal_cast]
            · have hk : encodeMove q' ≠ encodeMove q := fun h => hq' (encodeMove_injective h)
              rw [if_neg hq', OracleSpec.QueryCache.cacheQuery_of_ne _ _ hk]
              exact hagree q'
          obtain ⟨cache', hres, hag⟩ := adversarySteps_run P cs rest _ _ hagree'
          refine ⟨cache', ?_, ?_⟩
          · rw [runFrom_cons, hstep, ← hres, toChal_cast]
            simp
          · rw [runFrom_cons, hstep]
            exact hag

end Steps

end SelvageArkLib.StateRestoration
