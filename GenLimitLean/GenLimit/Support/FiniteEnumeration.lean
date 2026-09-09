import Mathlib.Data.Finset.Basic

/-!
# Finite stage-by-stage enumeration infrastructure

Paper-independent definitions and lemmas for a procedure that emits at most
one natural number at each stage. A paper-specific API can keep its original
names as compatibility abbreviations while reusing this implementation.
-/

namespace GenLimit.Support

/-- The set enumerated by a stage-by-stage output procedure at input `i`. -/
def enumeratedSet
    (emit : ℕ → ℕ → Option ℕ) (i : ℕ) : Set ℕ :=
  {x | ∃ stage, emit i stage = some x}

/-- Content emitted strictly before stage `n`, with duplicates removed. -/
def stageContents
    (emit : ℕ → ℕ → Option ℕ) (i n : ℕ) : Finset ℕ :=
  ((List.range n).filterMap (emit i)).toFinset

theorem mem_stageContents_iff
    {emit : ℕ → ℕ → Option ℕ} {i n x : ℕ} :
    x ∈ stageContents emit i n ↔
      ∃ stage < n, emit i stage = some x := by
  simp [stageContents]

theorem stageContents_mono
    {emit : ℕ → ℕ → Option ℕ} {i n m : ℕ} (hnm : n ≤ m) :
    stageContents emit i n ⊆ stageContents emit i m := by
  intro x hx
  obtain ⟨stage, hstage, hout⟩ := mem_stageContents_iff.mp hx
  exact mem_stageContents_iff.mpr
    ⟨stage, lt_of_lt_of_le hstage hnm, hout⟩

/-- Finitely many emitted values all occur before one common stage. -/
theorem finite_emissions_bounded
    {emit : ℕ → ℕ → Option ℕ} {i : ℕ} (T : Finset ℕ)
    (hT : ∀ x, x ∈ T → ∃ stage, emit i stage = some x) :
    ∃ N, ∀ x, x ∈ T → ∃ stage < N, emit i stage = some x := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert x T hxT ih =>
      obtain ⟨stageX, hstageX⟩ := hT x (by simp)
      have hTail : ∀ y, y ∈ T → ∃ stage, emit i stage = some y := by
        intro y hy
        exact hT y (by simp [hy])
      obtain ⟨NT, hNT⟩ := ih hTail
      refine ⟨max (stageX + 1) NT, ?_⟩
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact ⟨stageX,
          lt_of_lt_of_le (Nat.lt_succ_self stageX) (Nat.le_max_left _ _),
          hstageX⟩
      · obtain ⟨stage, hstage, hout⟩ := hNT y hy
        exact ⟨stage, lt_of_lt_of_le hstage (Nat.le_max_right _ _), hout⟩

end GenLimit.Support
