import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

namespace PredictionToGeneration

/-- The natural-log inequality used by the agnostic multiplicative potential. -/
theorem log_one_add_lower {u : ℝ} (hu : -(1/2 : ℝ) ≤ u) :
    u - u^2 ≤ Real.log (1+u) := by
  let f := fun x : ℝ => Real.log (1+x) - x + x^2
  have hd (x : ℝ) (hx : -(1/2 : ℝ) ≤ x) :
      HasDerivAt f (x*(1+2*x)/(1+x)) x := by
    have hp : 1+x ≠ 0 := by linarith
    convert ((((hasDerivAt_id x).const_add 1).log hp).sub (hasDerivAt_id x)).add
      ((hasDerivAt_id x).pow 2) using 1 <;> dsimp [f]
    field_simp
    ring
  by_cases hpos : 0 ≤ u
  · have hc : ContinuousOn f (Set.Icc 0 u) := fun x hx =>
      (hd x (by have := hx.1; linarith)).continuousAt.continuousWithinAt
    have hm : MonotoneOn f (Set.Icc 0 u) := monotoneOn_of_hasDerivWithinAt_nonneg
      (convex_Icc _ _) hc
      (fun x hx => (hd x (by have := (interior_subset hx).1; linarith)).hasDerivWithinAt)
      (fun x hx => by
        have hx0 : 0 ≤ x := (interior_subset hx).1
        positivity)
    have ht := hm (by exact ⟨le_rfl, hpos⟩) (by exact ⟨hpos, le_rfl⟩) hpos
    dsimp [f] at ht
    norm_num at ht
    linarith
  · have hn : u ≤ 0 := le_of_not_ge hpos
    have hc : ContinuousOn f (Set.Icc u 0) := fun x hx =>
      (hd x (hu.trans hx.1)).continuousAt.continuousWithinAt
    have hm : AntitoneOn f (Set.Icc u 0) := antitoneOn_of_hasDerivWithinAt_nonpos
      (convex_Icc _ _) hc
      (fun x hx => (hd x (hu.trans (interior_subset hx).1)).hasDerivWithinAt)
      (fun x hx => by
        have hx0 : x ≤ 0 := (interior_subset hx).2
        have hxl : -(1/2 : ℝ) ≤ x := hu.trans (interior_subset hx).1
        apply div_nonpos_of_nonpos_of_nonneg
        · exact mul_nonpos_of_nonpos_of_nonneg hx0 (by linarith)
        · linarith)
    have ht := hm (by exact ⟨le_rfl, hn⟩) (by exact ⟨hn, le_rfl⟩) hn
    dsimp [f] at ht
    norm_num at ht
    linarith

end PredictionToGeneration

