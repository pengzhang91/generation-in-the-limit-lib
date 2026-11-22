import GenLimit.Paper00A_PositiveDataInference.Effective.InferenceMachine
import GenLimit.Support.ComputableLastSearch

/-!
# Normalization of ordinary inference

This connects the event machine used in Theorems 4 and 5 to the total
prefix learner used in Theorems 1–3. On a history of length t, inspect all
positions (n, k) with n, k ≤ t using evaluator fuel t. Return the last visible
guess in chronological order. Once a stable correct guess has been seen,
every later visible guess has that same index. This also preserves a finite
sequence ending in a last guess.
-/

namespace GenLimit.Angluin.InferenceMachine

open Nat.Partrec (Code)
open GenLimit.Support

private def paddedPrefix (h : List ℕ) (n : ℕ) := textPrefix (fun i => (h[i]?).getD 0) n

private theorem prefix_comp : Computable₂ paddedPrefix :=
  (Primrec.list_map (Primrec.list_range.comp Primrec.snd)
    (Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.fst)
      Primrec.snd) (Primrec.const 0)).to₂).to_comp.to₂

private theorem prefix_eq (s : ℕ → ℕ) {n t : ℕ} (hn : n ≤ t) :
    paddedPrefix (textPrefix s t) n = textPrefix s n := by
  apply List.map_congr_left
  intro k hk
  have hkt := (List.mem_range.mp hk).trans_le hn
  simp [textPrefix, hkt]

private def visible (e : Code) (h : List ℕ) (q : ℕ) : Option ℕ :=
  let width := h.length + 1
  Code.evaln h.length e (Encodable.encode (paddedPrefix h (q / width), q % width))

private theorem visible_comp (e : Code) : Computable₂ (visible e) := by
  have ht : Computable (fun p : List ℕ × ℕ => p.1.length) := Primrec.list_length.to_comp.comp Computable.fst
  have hw := Primrec.succ.to_comp.comp ht
  have hpos := (prefix_comp.comp Computable.fst (Primrec.nat_div.to_comp.comp Computable.snd hw)).pair
    (Primrec.nat_mod.to_comp.comp Computable.snd hw)
  exact (Code.primrec_evaln.to_comp.comp ((ht.pair (Computable.const e)).pair
    (Primrec.encode.to_comp.comp hpos))).to₂

private def learner (e : Code) (h : List ℕ) : ℕ :=
  let width := h.length + 1
  let q := lastTrue (fun xs i => (visible e xs i).isSome) h (width * width)
  (visible e h (q.getD 0)).getD 0

private theorem learner_comp (e : Code) : Computable (learner e) := by
  have hw : Computable (fun h : List ℕ => h.length + 1) := (Primrec.succ.comp Primrec.list_length).to_comp
  have hq := (lastTrue_computable (Primrec.option_isSome.to_comp.comp (visible_comp e)).to₂).comp
    Computable.id (Primrec.nat_mul.to_comp.comp hw hw)
  exact Computable.option_getD ((visible_comp e).comp Computable.id (Computable.option_getD hq (Computable.const 0)))
    (Computable.const 0)

private theorem normalize {F : EffectiveIndexedFamily} {M : InferenceMachine}
    (hid : M.Identifies F) : EffectiveInferrable F := by
  obtain ⟨e, he⟩ := M.exists_guess_code
  refine ⟨learner e, learner_comp e, fun i s hp => ?_⟩
  obtain ⟨n, k, j, hj, heq, hstable⟩ := hid i s hp
  obtain ⟨fuel, hfuel⟩ := Code.evaln_complete.mp ((he _ _ _).2 hj)
  refine ⟨j, heq, max fuel (max n k), fun t ht => ?_⟩
  let w := t + 1
  let q := w * n+k
  let h := textPrefix s t
  have hpos : 0 < w := Nat.zero_lt_succ _
  have hn : n ≤ t := by omega
  have hk : k < w := by dsimp [w]; omega
  have hdiv : q / w = n := by
    dsimp only [q]; rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hk, Nat.add_zero]
  have hmod : q % w = k := by simp [q, Nat.add_mod, Nat.mod_eq_of_lt hk]
  have hlt : q < w * w := by
    have hh := Nat.mul_le_mul_left w (show n + 1 ≤ w from Nat.succ_le_succ hn)
    dsimp [q]; rw [Nat.mul_succ] at hh; omega
  have hvis : visible e h q = some j := by
    simp only [visible, h, textPrefix_length]
    change Code.evaln t e (Encodable.encode (paddedPrefix (textPrefix s t) (q / w), q % w)) = some j
    rw [hdiv, hmod, prefix_eq s hn]
    exact Code.evaln_mono (by omega : fuel ≤ t) hfuel
  let p := fun (xs : List ℕ) u => (visible e xs u).isSome
  have htrue : p h q = true := by simp [p, hvis]
  cases hl : lastTrue p h (w * w) with
  | none =>
    have := (lastTrue_eq_none_iff _ _ _).1 hl q hlt
    simp [htrue] at this
  | some u =>
    have hqu := lastTrue_ge_of_true hl hlt htrue
    obtain ⟨hu, htu⟩ := lastTrue_spec hl
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp htu
    have hm : u / w ≤ t := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpos).2 hu)
    have hg' : M.Guesses s (u / w) (u % w) g := by
      apply (he _ _ _).1
      apply Code.evaln_sound (k := t)
      simpa [visible, h, w, prefix_eq s hm] using hg
    have hng : n ≤ u / w := hdiv ▸ Nat.div_le_div_right hqu
    have heqg : g = j := by
      by_cases hsame : n = u / w
      · have hk' : k ≤ u % w := by
          have hb := Nat.mod_add_div u w
          rw [← hsame] at hb
          dsimp [q] at hqu
          omega
        rcases eq_or_lt_of_le hk' with h | h
        · rw [← h, ← hsame] at hg'
          exact Option.some.inj (Part.mem_unique hg' hj)
        · exact hstable _ _ _ (Or.inr ⟨hsame, h⟩) hg'
      · exact hstable _ _ _ (Or.inl (by omega)) hg'
    change learner e h = j
    unfold learner
    simp only [show h.length = t from textPrefix_length s t]
    change (visible e h ((lastTrue p h (w * w)).getD 0)).getD 0 = j
    simp [hl, hg, heqg]

/-- Ordinary effective inference has the same power in the prefix and
request/guess models, including machines that eventually stop guessing. -/
theorem exists_identifies_iff (F : EffectiveIndexedFamily) :
    (∃ M : InferenceMachine, M.Identifies F) ↔ EffectiveInferrable F := by
  constructor
  · rintro ⟨M, hM⟩; exact normalize hM
  · rintro ⟨learner, hc, hid⟩; exact ⟨_, ofIdentifier_identifies hc hid⟩

end GenLimit.Angluin.InferenceMachine
