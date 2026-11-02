import GenLimit.Paper21_GenerationInMetricSpaces.Example48Positive
import GenLimit.Paper21_GenerationInMetricSpaces.OrthogonalCovering
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Orthogonal axis geometry for the remaining Hilbert examples

The underlying space is the same genuine real `ℓ²(ℕ)` used by Example 4.8.
These lemmas expose its inner product and link standard-axis families to the
ambient-center covering estimate of Appendix C.1.
-/

namespace GenLimit.MetricSpaces.HilbertAxisReservoir

noncomputable section

@[simp] theorem norm_axisPoint (c : ℝ) (k : ℕ) : ‖axisPoint c k‖ = |c| := by
  simpa only [axisPoint, Real.norm_eq_abs] using
    lp.norm_single (E := fun _ : ℕ => ℝ) (by norm_num : 0 < (2 : ENNReal)) k c

@[simp] theorem axisPoint_zero (k : ℕ) : axisPoint 0 k = 0 := by
  apply norm_eq_zero.mp
  simp

theorem axisPoint_injective {c : ℝ} (hc : c ≠ 0) : Function.Injective (axisPoint c) := by
  intro i j hij
  exact (axisPoint_eq_axisPoint_of_left_ne_zero hc hij).2

theorem inner_axisPoint_of_ne (c d : ℝ) {i j : ℕ} (hij : i ≠ j) :
    inner ℝ (axisPoint c i) (axisPoint d j) = 0 := by
  change inner ℝ (lp.single (E := fun _ : ℕ => ℝ) 2 i c)
    (lp.single (E := fun _ : ℕ => ℝ) 2 j d) = 0
  rw [lp.inner_single_left]
  simp [hij]

theorem axis_range_infinite {c : ℝ} (hc : c ≠ 0) (f : ℕ → ℕ)
    (hf : Function.Injective f) : (Set.range (fun k => axisPoint c (f k))).Infinite :=
  Set.infinite_range_of_injective ((axisPoint_injective hc).comp hf)

theorem axis_range_orthogonal (c : ℝ) (f : ℕ → ℕ) :
    ∀ x ∈ Set.range (fun k => axisPoint c (f k)),
      ∀ y ∈ Set.range (fun k => axisPoint c (f k)),
        x ≠ y → inner ℝ x y = 0 := by
  rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ hne
  apply inner_axisPoint_of_ne
  intro heq
  exact hne (congrArg (axisPoint c) heq)

theorem axis_range_norm {c : ℝ} (hc : 0 ≤ c) (f : ℕ → ℕ) :
    ∀ x ∈ Set.range (fun k => axisPoint c (f k)), ‖x‖ = c := by
  rintro x ⟨i, rfl⟩
  simp [abs_of_nonneg hc]

end

end GenLimit.MetricSpaces.HilbertAxisReservoir
