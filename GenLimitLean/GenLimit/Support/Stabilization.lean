import Mathlib.Order.Minimal

/-!
# Stabilization of natural-number sequences

Paper-independent stabilization facts for monotone and antitone sequences
whose values cannot move indefinitely.
-/

namespace GenLimit.Support

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
