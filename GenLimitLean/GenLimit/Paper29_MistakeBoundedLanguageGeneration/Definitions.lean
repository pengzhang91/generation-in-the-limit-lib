import Mathlib.Data.Finset.Range
import Mathlib.Data.Set.Finite.Basic

/-!
# Mistake-bounded language generation: trace definitions

Paper-facing trace notions for Kleinberg--Peale--Reingold,
*Mistake-Bounded Language Generation*, arXiv:2605.10809v1.
-/

namespace GenLimit.MistakeBounded

/-- `true` at precisely the rounds on which the generator makes a mistake. -/
abbrev MistakeTrace := ℕ → Bool

/-- Number of mistakes strictly before round `t`. -/
def mistakeCount (trace : MistakeTrace) (t : ℕ) : ℕ :=
  ((Finset.range t).filter fun s => trace s = true).card

@[simp] theorem mistakeCount_zero (trace : MistakeTrace) :
    mistakeCount trace 0 = 0 := by
  simp [mistakeCount]

theorem mistakeCount_succ (trace : MistakeTrace) (t : ℕ) :
    mistakeCount trace (t + 1) =
      mistakeCount trace t + if trace t = true then 1 else 0 := by
  classical
  by_cases h : trace t = true
  · simp [mistakeCount, Finset.filter_insert, Finset.range_add_one, h]
  · simp [mistakeCount, Finset.filter_insert, Finset.range_add_one, h]

theorem mistakeCount_mono
    (trace : MistakeTrace) {s t : ℕ} (hst : s ≤ t) :
    mistakeCount trace s ≤ mistakeCount trace t := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨lt_of_lt_of_le hi.1 hst, hi.2⟩

/-- Uniform finite bound on the total number of mistakes. -/
def TotalMistakesAtMost (trace : MistakeTrace) (bound : ℕ) : Prop :=
  ∀ t, mistakeCount trace t ≤ bound

/-- No mistakes occur at or after `last`. -/
def LastMistakeBefore (trace : MistakeTrace) (last : ℕ) : Prop :=
  ∀ t, last ≤ t → trace t = false

/-- The set of mistake rounds is finite. -/
def FinitelyManyMistakes (trace : MistakeTrace) : Prop :=
  ({t | trace t = true} : Set ℕ).Finite

theorem lastMistakeBefore_implies_finite
    {trace : MistakeTrace} {last : ℕ}
    (h : LastMistakeBefore trace last) :
    FinitelyManyMistakes trace := by
  apply (Finset.finite_toSet (Finset.range last)).subset
  intro t ht
  simp only [Set.mem_setOf_eq] at ht
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hnot
  have hlast : last ≤ t := Nat.le_of_not_gt hnot
  have := h t hlast
  simp [ht] at this

/-- An eventual correctness theorem immediately yields finite total
mistakes; this is the abstract content used in Lemma 7.1. -/
theorem eventual_no_mistakes
    {trace : MistakeTrace} (h : ∃ T, ∀ t, T ≤ t → trace t = false) :
    FinitelyManyMistakes trace := by
  obtain ⟨T, hT⟩ := h
  exact lastMistakeBefore_implies_finite hT

/-- If no mistakes occur from round `last` onward, then there are at most
`last` mistakes in total. -/
theorem lastMistakeBefore_implies_totalMistakesAtMost
    {trace : MistakeTrace} {last : ℕ}
    (h : LastMistakeBefore trace last) :
    TotalMistakesAtMost trace last := by
  intro t
  classical
  have hsubset :
      (Finset.range t).filter (fun s => trace s = true) ⊆
        Finset.range last := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs
    simp only [Finset.mem_range]
    by_contra hnot
    have hlast : last ≤ s := Nat.le_of_not_gt hnot
    have hfalse := h s hlast
    simp [hs.2] at hfalse
  calc
    mistakeCount trace t =
        ((Finset.range t).filter
          (fun s => trace s = true)).card := rfl
    _ ≤ (Finset.range last).card :=
      Finset.card_le_card hsubset
    _ = last := by simp

end GenLimit.MistakeBounded
