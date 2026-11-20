import GenLimit.NoRegretLanguageGeneration.AnytimeAgnosticReal

namespace PredictionToGeneration

/-- The agnostic generator itself works on realizable streams. -/
theorem agnostic_no_regret_implies_realizable (H : HypothesisClass X)
    (ha : AgnosticNoRegret H) : RealizableNoRegret H := by
  obtain ⟨G,r,hs,hG⟩ := ha
  refine ⟨G, fun k => ?_⟩
  obtain ⟨N,hN⟩ := hs k
  refine ⟨N, fun xs hn hl h hh hr => ?_⟩
  have hb := hG xs hn h hh
  rw [regret_eq_mistakes h (G.play xs) hr] at hb
  have hm : mistakes h (G.play xs)≤r xs.length := by exact_mod_cast hb
  exact (Nat.mul_le_mul_left k hm).trans (hN xs.length hl)

end PredictionToGeneration
