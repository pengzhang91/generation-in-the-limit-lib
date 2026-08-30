import GenLimit.Paper01_LanguageGeneration.Critical
import GenLimit.Paper39_DenseGeneration.Critical

/-!
# #01 to the earlier #39 manuscript: criticality comparison

Public arXiv-v1 #39 directly reuses #01 `Critical`; no bridge is needed for
that identity. This module records only the one-way comparison with #39's
preserved earlier-manuscript `RecursiveCritical`. Neither development depends
on this comparison theorem.
-/

namespace GenLimit

/-- Direct KM criticality implies the earlier-manuscript recursive notion. -/
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
