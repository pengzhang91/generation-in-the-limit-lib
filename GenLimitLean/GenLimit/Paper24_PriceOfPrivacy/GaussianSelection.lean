import GenLimit.Paper24_PriceOfPrivacy.GaussianPrivacy
import GenLimit.Support.DiscreteIID
import Mathlib.Probability.Moments.SubGaussian

/-! Gaussian noisy argmax, with its event privacy and finite-window
misclassification bound. Ties select the least maximizing index. -/

namespace GenLimit.PriceOfPrivacy.Gaussian

open MeasureTheory ProbabilityTheory Set DiscreteIID
open scoped ENNReal NNReal Classical
noncomputable section

variable {k : ℕ} [NeZero k]

private def maxima (z : Fin k → ℝ) : Finset (Fin k) :=
  Finset.univ.filter fun i => ∀ j, z j ≤ z i

private theorem maxima_nonempty (z : Fin k → ℝ) : (maxima z).Nonempty := by
  obtain ⟨i,_,best⟩ := Finset.univ.exists_max_image z Finset.univ_nonempty
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun j => best j (Finset.mem_univ _)⟩⟩

def argmax (z : Fin k → ℝ) := (maxima z).min' (maxima_nonempty z)

theorem argmax_max (z : Fin k → ℝ) (i : Fin k) : z i ≤ z (argmax z) :=
  (Finset.mem_filter.mp ((maxima z).min'_mem (maxima_nonempty z))).2 i

private theorem argmax_eq (z : Fin k → ℝ) (i : Fin k) :
    argmax z = i ↔ (∀ j, z j ≤ z i) ∧ (∀ j < i, z j < z i) := by
  constructor
  · rintro rfl
    refine ⟨argmax_max z,fun j hj => lt_of_le_of_ne (argmax_max z j) ?_⟩
    intro eq
    have mem : j ∈ maxima z := Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun t => eq ▸ argmax_max z t⟩
    exact hj.not_ge ((maxima z).min'_le j mem)
  · rintro ⟨best,earlier⟩
    have mem : i ∈ maxima z := Finset.mem_filter.mpr ⟨Finset.mem_univ _,best⟩
    exact le_antisymm ((maxima z).min'_le i mem)
      (le_of_not_gt fun lt => (earlier _ lt).not_ge (argmax_max z i))

theorem measurable_argmax : Measurable (argmax (k := k)) := by
  apply measurable_to_countable
  intro z
  let i := argmax z
  have eq : argmax ⁻¹' {i} = {y : Fin k → ℝ | ∀ j, y j ≤ y i} ∩
      {y | ∀ j < i, y j < y i} := by ext y; exact argmax_eq y i
  rw [show argmax ⁻¹' {argmax z} = _ from eq]
  apply MeasurableSet.inter
  · simp only [setOf_forall]; exact MeasurableSet.iInter fun _ => measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _)
  · simp only [setOf_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)

def law (s : Fin k → ℝ) (v : ℝ≥0) : PMF (Fin k) :=
  letI := Measure.isProbabilityMeasure_map (μ := vectorLaw s v) measurable_argmax.aemeasurable
  ((vectorLaw s v).map argmax).toPMF

private theorem event_eq (s : Fin k → ℝ) (v : ℝ≥0) (F : Set (Fin k)) :
    probability (law s v) F = (vectorLaw s v).real (argmax ⁻¹' F) := by
  have hm : MeasurableSet F := (Set.to_countable _).measurableSet
  letI := Measure.isProbabilityMeasure_map (μ := vectorLaw s v) measurable_argmax.aemeasurable
  unfold probability law
  rw [←PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm, Measure.toPMF_toMeasure,
    Measure.map_apply measurable_argmax hm]
  rfl

theorem selection_private (s t : Fin k → ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (ε δ : ℝ) (he : ε ∈ Ioo 0 1) (hd : δ ∈ Ioo 0 1)
    (cal : 2*Real.log ((5/4)/δ)*energy s t ≤ ε^2*v) (F : Set (Fin k)) :
    probability (law s v) F ≤ Real.exp ε * probability (law t v) F + δ := by
  rw [event_eq,event_eq]
  exact event_private s t hv ε δ he hd cal (measurable_argmax ((Set.to_countable _).measurableSet))

omit [NeZero k] in
private theorem coord_subgaussian (s : Fin k → ℝ) (v : ℝ≥0) (i : Fin k) :
    HasSubgaussianMGF (fun z : Fin k → ℝ => z i - s i) v (vectorLaw s v) := by
  have h : HasSubgaussianMGF id v (gaussianReal 0 v) := by
    constructor
    · exact integrable_exp_mul_gaussianReal
    · intro t; simp [mgf_id_gaussianReal]
  let f := fun z : Fin k → ℝ => z i - s i
  have eq : (vectorLaw s v).map f = gaussianReal 0 v := by
    have eval := measurePreserving_eval (fun j => gaussianReal (s j) v) i
    calc
      _ = ((vectorLaw s v).map (Function.eval i)).map (· - s i) :=
        (Measure.map_map (measurable_id'.sub_const (s i)) (measurable_pi_apply i)).symm
      _ = (gaussianReal (s i) v).map (· - s i) := congrArg (Measure.map (· - s i)) eval.map_eq
      _ = _ := by rw [gaussianReal_map_sub_const,sub_self]
  rw [←eq] at h
  have evalMeas : Measurable (fun z : Fin k → ℝ => z i) := measurable_pi_apply i
  have hf : Measurable f := evalMeas.sub measurable_const
  exact HasSubgaussianMGF.of_map (Y := f) (X := id) hf.aemeasurable h

theorem event_margin (s : Fin k → ℝ) (v : ℝ≥0) (F : Set (Fin k)) (i₀ : Fin k)
    (Γ : ℝ) (pos : 0 < Γ) (gap : ∀ i ∈ F, Γ ≤ s i₀-s i) :
    probability (law s v) F ≤ 2*k*Real.exp (-Γ^2/(8*v)) := by
  let M := vectorLaw s v
  let high (i : Fin k) := {z : Fin k → ℝ | Γ/2 ≤ z i-s i}
  let low (i : Fin k) := {z : Fin k → ℝ | Γ/2 ≤ -(z i-s i)}
  have sub : argmax ⁻¹' F ⊆ ⋃ i, high i ∪ low i := by
    intro z hz
    by_contra avoid
    have h (i : Fin k) : z ∉ high i ∧ z ∉ low i :=
      not_or.mp fun hi => avoid (Set.mem_iUnion.mpr ⟨i,hi⟩)
    have hlow := (h i₀).2
    have hhigh := (h (argmax z)).1
    change ¬Γ/2 ≤ -(z i₀-s i₀) at hlow
    change ¬Γ/2 ≤ z (argmax z)-s (argmax z) at hhigh
    linarith [gap _ hz,argmax_max z i₀]
  have tail (i : Fin k) : M.real (high i ∪ low i) ≤ 2*Real.exp (-Γ^2/(8*v)) := by
    have sg := coord_subgaussian s v i
    have upper := sg.measure_ge_le (show 0 ≤ Γ/2 by positivity)
    have lower := sg.neg.measure_ge_le (show 0 ≤ Γ/2 by positivity)
    change M.real (high i) ≤ _ at upper
    change M.real (low i) ≤ _ at lower
    have e : -(Γ/2)^2/(2*(v:ℝ)) = -Γ^2/(8*v) := by ring
    rw [e] at upper lower
    linarith [measureReal_union_le (μ := M) (high i) (low i)]
  rw [event_eq]
  calc
    _ ≤ M.real (⋃ i, high i ∪ low i) := measureReal_mono sub
    _ ≤ ∑ i, M.real (high i ∪ low i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : Fin k, 2*Real.exp (-Γ^2/(8*v)) := Finset.sum_le_sum fun i _ => tail i
    _ = _ := by simp; ring

end
end GenLimit.PriceOfPrivacy.Gaussian
