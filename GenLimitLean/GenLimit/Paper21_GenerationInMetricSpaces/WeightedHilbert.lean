import GenLimit.Paper21_GenerationInMetricSpaces.HilbertGeometry
import GenLimit.Paper21_GenerationInMetricSpaces.BiLipschitzTransfer
import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# The weighted Hilbert metric of Example 4.11

Odd coordinates have weight one and even coordinates have weight one half
before taking the ordinary Hilbert norm. Thus the squared coordinate
weights are exactly `1` and `1/4`, as in Appendix C.5.
-/

namespace GenLimit.MetricSpaces.HilbertAxisReservoir.WeightedHilbert

open GenLimit.Generic

noncomputable section

def weight (k : ℕ) : ℝ := if k % 2 = 1 then 1 else 1 / 2

theorem weight_pos (k : ℕ) : 0 < weight k := by unfold weight; split <;> norm_num
theorem weight_le_one (k : ℕ) : weight k ≤ 1 := by unfold weight; split <;> norm_num
theorem half_le_weight (k : ℕ) : 1 / 2 ≤ weight k := by unfold weight; split <;> norm_num

theorem coordinate_bound (x : Hilbert2) (k : ℕ) : ‖weight k * x k‖ ≤ ‖x k‖ := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (weight_pos k)]
  exact mul_le_of_le_one_left (norm_nonneg _) (weight_le_one k)

def weightedMap (x : Hilbert2) : Hilbert2 :=
  ⟨fun k => weight k * x k, memℓp_gen' (C := ‖x‖ ^ (2 : ENNReal).toReal) (by
    intro S
    apply le_trans (Finset.sum_le_sum (fun k hk =>
      Real.rpow_le_rpow (norm_nonneg _) (coordinate_bound x k) (by norm_num)))
    exact lp.sum_rpow_le_norm_rpow (by norm_num) x S)⟩

@[simp] theorem weightedMap_apply (x : Hilbert2) (k : ℕ) :
    weightedMap x k = weight k * x k := rfl

@[simp] theorem weightedMap_zero : weightedMap 0 = 0 := by
  apply lp.ext
  funext k
  simp

theorem weightedMap_sub (x y : Hilbert2) : weightedMap (x - y) = weightedMap x - weightedMap y := by
  apply lp.ext
  funext k
  change weight k * (x k - y k) = weight k * x k - weight k * y k
  ring

theorem norm_mono {x y : Hilbert2} (h : ∀ k, ‖x k‖ ≤ ‖y k‖) : ‖x‖ ≤ ‖y‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg y)
  intro S
  exact (Finset.sum_le_sum (fun k hk =>
    Real.rpow_le_rpow (norm_nonneg _) (h k) (by norm_num))).trans
      (lp.sum_rpow_le_norm_rpow (by norm_num) y S)

theorem norm_weighted_le (x : Hilbert2) : ‖weightedMap x‖ ≤ ‖x‖ :=
  norm_mono (coordinate_bound x)

theorem norm_le_twice_weighted (x : Hilbert2) : ‖x‖ ≤ 2 * ‖weightedMap x‖ := by
  have h : ‖x‖ ≤ ‖(2 : ℝ) • weightedMap x‖ := by
    apply norm_mono
    intro k
    change ‖x k‖ ≤ ‖(2 : ℝ) * (weight k * x k)‖
    calc
      ‖x k‖ = 1 * ‖x k‖ := by ring
      _ ≤ (2 * weight k) * ‖x k‖ := mul_le_mul_of_nonneg_right
        (by linarith [half_le_weight k]) (norm_nonneg _)
      _ = ‖(2 : ℝ) * (weight k * x k)‖ := by
        rw [norm_mul, norm_mul, Real.norm_ofNat, Real.norm_eq_abs (weight k),
          abs_of_pos (weight_pos k)]
        ring
  simpa only [norm_smul, Real.norm_ofNat] using h

theorem weightedMap_injective : Function.Injective weightedMap := by
  intro x y hxy
  apply lp.ext
  funext k
  have h := congrArg (fun z : Hilbert2 => z k) hxy
  exact mul_left_cancel₀ (weight_pos k).ne' h

def weightedDistance (x y : Hilbert2) : ℝ := dist (weightedMap x) (weightedMap y)

def weightedMetric : MetricSpace Hilbert2 :=
  MetricSpace.induced weightedMap weightedMap_injective inferInstance

theorem weightedMetric_dist (x y : Hilbert2) :
    @dist Hilbert2 weightedMetric.toDist x y = weightedDistance x y := rfl

theorem distance_le (x y : Hilbert2) : weightedDistance x y ≤ dist x y := by
  simpa only [weightedDistance, dist_eq_norm, ← weightedMap_sub] using norm_weighted_le (x - y)

theorem half_distance_le (x y : Hilbert2) : dist x y / 2 ≤ weightedDistance x y := by
  have h := norm_le_twice_weighted (x - y)
  rw [weightedMap_sub] at h
  change ‖x - y‖ / 2 ≤ ‖weightedMap x - weightedMap y‖
  linarith

theorem mutually_dominated : MutuallyLipschitzDominated dist weightedDistance 1 2 := by
  constructor
  · intro x y
    simpa only [one_mul] using distance_le x y
  · intro x y
    have h := half_distance_le x y
    linarith

/-- The induced weighted metric has exactly the ordinary Hilbert topology. -/
theorem weightedMetric_topology :
    weightedMetric.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace Hilbert2) := by
  have hLip : LipschitzWith 1 weightedMap := LipschitzWith.of_dist_le_mul (by
    intro x y
    simpa only [NNReal.coe_one, one_mul] using distance_le x y)
  have hAnti : AntilipschitzWith 2 weightedMap := AntilipschitzWith.of_le_mul_dist (by
    intro x y
    have h := half_distance_le x y
    change dist x y ≤ (2 : ℝ) * weightedDistance x y
    linarith)
  exact (hAnti.isUniformInducing hLip.uniformContinuous).isInducing.eq_induced.symm

@[simp] theorem weightedMap_axisPoint (c : ℝ) (k : ℕ) :
    weightedMap (axisPoint c k) = axisPoint (weight k * c) k := by
  apply lp.ext
  funext j
  change weight j * axisPoint c k j = axisPoint (weight k * c) k j
  by_cases hj : j = k
  · subst j
    simp
  · rw [axisPoint_apply_ne c hj, axisPoint_apply_ne (weight k * c) hj, mul_zero]

@[simp] theorem weightedDistance_self (x : Hilbert2) : weightedDistance x x = 0 := dist_self _

theorem weightedDistance_zero_axis (c : ℝ) (k : ℕ) :
    weightedDistance 0 (axisPoint c k) = |weight k * c| := by
  simp [weightedDistance]

theorem coordinate_le_distance (x : Hilbert2) (c : ℝ) (k : ℕ) :
    |weight k * x k - weight k * c| ≤ weightedDistance x (axisPoint c k) := by
  rw [weightedDistance, dist_eq_norm]
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (weightedMap x - weightedMap (axisPoint c k)) k
  simpa [Real.norm_eq_abs] using h

/-- Pulling a finite cover forward proves the corresponding covering-number
lower bound for the weighted distance. Centers remain arbitrary ambient points. -/
theorem coveringNumberAtLeast_pullback {γ : ℝ} {S : Finset Hilbert2} {d : ℕ}
    (h : CoveringNumberAtLeast dist γ
      (weightedMap '' (S : Set Hilbert2)) d) :
    CoveringNumberAtLeast weightedDistance γ (S : Set Hilbert2) d := by
  classical
  intro C hC
  have hcover : (weightedMap '' (S : Set Hilbert2)) ⊆
      closedNeighborhood dist (C.image weightedMap : Set Hilbert2) γ := by
    rintro z ⟨x, hx, rfl⟩ η hη
    obtain ⟨y, hy, hclose⟩ := hC hx η hη
    exact ⟨weightedMap y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hclose⟩
  exact (h _ hcover).trans Finset.card_image_le

end
end GenLimit.MetricSpaces.HilbertAxisReservoir.WeightedHilbert
