import GenLimit.Paper01_LanguageGeneration.Critical
import GenLimit.Paper39_DenseGeneration.Critical

/-!
# #01 to #39: criticality comparison

This comparison imports both paper-specific notions.  Neither paper's core
development depends on the bridge.
-/

namespace GenLimit

/-- The stronger #01 notion of criticality implies #39 recursive criticality. -/
theorem critical_recursiveCritical
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ}
    (h : Critical C stream t n) : RecursiveCritical C stream t n := by
  cases n with
  | zero => simpa [RecursiveCritical] using h.1
  | succ n =>
      rw [RecursiveCritical]
      refine ⟨h.1, ?_⟩
      intro j hj hjcrit
      exact h.2 j (Nat.le_trans hj (Nat.le_succ n))
        (recursiveCritical_consistent hjcrit)

end GenLimit
