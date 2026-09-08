import Mathlib.Order.Minimal

/-!
# Stabilization and eventual thresholds

Paper-independent facts for combining finitely many eventual thresholds and
for sequences whose natural-number values cannot move indefinitely.
-/

namespace GenLimit.Support

/-- Finitely many explicitly indexed eventual properties have one common
threshold. -/
theorem eventually_forall_lt
    {P : ℕ → ℕ → Prop} {n : ℕ}
    (hP : ∀ i, i < n → ∃ T, ∀ t, T ≤ t → P i t) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i < n → P i t := by
  induction n with
  | zero =>
      exact ⟨0, by simp⟩
  | succ n ih =>
      obtain ⟨T₀, hT₀⟩ := ih (fun i hi => hP i (Nat.lt_succ_of_lt hi))
      obtain ⟨T₁, hT₁⟩ := hP n (Nat.lt_succ_self n)
      refine ⟨max T₀ T₁, ?_⟩
      intro t ht i hi
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hi | rfl
      · exact hT₀ t (le_trans (Nat.le_max_left _ _) ht) i hi
      · exact hT₁ t (le_trans (Nat.le_max_right _ _) ht)

/-- A non-increasing natural-number sequence eventually becomes constant. -/
theorem antitone_nat_eventually_constant
    (f : ℕ → ℕ) (hf : Antitone f) :
    ∃ M, ∀ m, M ≤ m → f m = f M := by
  obtain ⟨v, ⟨M, rfl⟩, hmin⟩ :=
    Nat.lt_wfRel.wf.has_min (Set.range f) ⟨f 0, ⟨0, rfl⟩⟩
  refine ⟨M, ?_⟩
  intro m hm
  apply Nat.le_antisymm (hf hm)
  apply Nat.le_of_not_gt
  intro hlt
  exact hmin (f m) ⟨m, rfl⟩ hlt

end GenLimit.Support
