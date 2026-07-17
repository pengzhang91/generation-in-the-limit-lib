import GenLimit.KM.Critical
import GenLimit.DenseGeneration.Critical

/-!
# Bridge from KM criticality to recursive criticality

This comparison imports both paper-specific notions.  Neither paper's core
development depends on the bridge.
-/

namespace GenLimit

/-- The stronger KM notion of criticality implies recursive criticality. -/
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
