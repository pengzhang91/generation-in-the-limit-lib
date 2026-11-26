import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.Model
import GenLimit.Support.DiscreteSampleAtoms
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! # Hoeffding bounds for the library's finite ordered IID samples -/
namespace GenLimit.AgnosticLanguage
open DiscreteIID MeasureTheory ProbabilityTheory
open scoped Classical BigOperators
noncomputable section

private theorem sample_tuple_atom (q : PMF α) (n : ℕ) (v : Fin n → α) :
    samples q n (List.ofFn v) = ∏ i, q (v i) := by
  induction n with
  | zero => simp [samples]
  | succ n ih =>
    rw [List.ofFn_succ, Fin.prod_univ_succ]
    have h := samples_cons q (v 0) (List.ofFn fun i ↦ v (Fin.succ i))
    simp only [List.length_ofFn] at h
    rw [h,ih]

private theorem tuple_probability {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (q : PMF α) (n : ℕ) (E : Set (List α)) :
    probability (samples q n) E =
      (Measure.pi (fun _ : Fin n ↦ q.toMeasure)).real {v | List.ofFn v ∈ E} := by
  letI : MeasurableSpace (List α) := ⊤
  letI : DiscreteMeasurableSpace (List α) := ⟨fun _ ↦ trivial⟩
  let μ := Measure.pi (fun _ : Fin n ↦ q.toMeasure)
  have hmeas : Measurable (@List.ofFn α n) := measurable_of_countable _
  have he : (samples q n).toMeasure = μ.map List.ofFn := by
    apply Measure.ext_of_singleton
    intro xs
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), Measure.map_apply hmeas (measurableSet_singleton _)]
    by_cases hx : xs.length = n
    · subst n
      let v := xs.get
      have hxs : List.ofFn v = xs := List.ofFn_get xs
      have hpre : List.ofFn ⁻¹' {xs} = ({v} : Set (Fin xs.length → α)) := by
        ext w
        change List.ofFn w = xs ↔ w = v
        exact ⟨fun h ↦ List.ofFn_injective (h.trans hxs.symm),fun h ↦ h ▸ hxs⟩
      rw [hpre, ← Set.univ_pi_singleton]
      change _ = Measure.pi _ _
      rw [Measure.pi_pi]
      simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      simpa only [hxs] using sample_tuple_atom q xs.length v
    · have hzero : samples q n xs = 0 := by
        by_contra hn
        exact hx ((samples_support q n xs).mp hn).1
      have hpre : List.ofFn ⁻¹' {xs} = (∅ : Set (Fin n → α)) := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro v hv
        exact hx ((show List.ofFn v = xs from hv) ▸ List.length_ofFn)
      simp [hpre,hzero]
  rw [probability, ← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (DiscreteMeasurableSpace.forall_measurableSet _),
    he, Measure.map_apply hmeas (DiscreteMeasurableSpace.forall_measurableSet _)]
  rfl

def empirical (E : Set α) (xs : List α) : ℝ :=
  (xs.map (E.indicator (fun _ ↦ (1:ℝ)))).sum / xs.length

/-- Two-sided Hoeffding for an empirical fraction. The sample law is the
ordered-list law used by the statistical generation and identification modules. -/
theorem empirical_deviation (q : PMF α) [Countable α] (E : Set α) (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ : 0 < δ) :
    probability (samples q n) {xs | δ ≤ |empirical E xs - probability q E|} ≤
      2 * Real.exp (-2 * n * δ^2) := by
  letI : MeasurableSpace α := ⊤
  letI : DiscreteMeasurableSpace α := ⟨fun _ ↦ trivial⟩
  let μ := Measure.pi (fun _ : Fin n ↦ q.toMeasure)
  let X := E.indicator (fun _ ↦ (1:ℝ))
  let m := probability q E
  let Y := fun (i : Fin n) (v : Fin n → α) ↦ X (v i) - m
  have hm : ∫ x, X x ∂q.toMeasure = m := by
    rw [show X = E.indicator (1 : α → ℝ) from rfl, integral_indicator_one (DiscreteMeasurableSpace.forall_measurableSet _),
      Measure.real_def, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (DiscreteMeasurableSpace.forall_measurableSet _)]
    rfl
  have hsg : HasSubgaussianMGF (fun x ↦ X x - m) (1/4) q.toMeasure := by
    have hb (x : α) : X x ∈ Set.Icc 0 1 := by by_cases h : x ∈ E <;> simp [X,h]
    have h := hasSubgaussianMGF_of_mem_Icc (μ := q.toMeasure) (measurable_of_countable X).aemeasurable (Filter.Eventually.of_forall hb)
    rw [hm] at h
    convert h using 1
    norm_num
  have hcoord (i : Fin n) : HasSubgaussianMGF (Y i) (1/4) μ := by
    apply HasSubgaussianMGF.of_map (X := fun x ↦ X x - m) (μ := μ) (measurable_pi_apply i).aemeasurable
    change HasSubgaussianMGF _ _ ((Measure.pi (fun _ : Fin n ↦ q.toMeasure)).map (Function.eval i))
    rw [(measurePreserving_eval (fun _ : Fin n ↦ q.toMeasure) i).map_eq]
    exact hsg
  have indep : iIndepFun Y μ := iIndepFun_pi (μ := fun _ : Fin n ↦ q.toMeasure) (X := fun _ x ↦ X x - m) (fun _ ↦ (measurable_of_countable _).aemeasurable)
  have indepNeg : iIndepFun (fun i v ↦ -Y i v) μ :=
    iIndepFun_pi (μ := fun _ : Fin n ↦ q.toMeasure) (X := fun _ x ↦ -(X x - m)) (fun _ ↦ (measurable_of_countable _).aemeasurable)
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hu := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun indep (s := Finset.univ)
    (fun i _ ↦ hcoord i) (mul_nonneg hn'.le hδ.le)
  have hl := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun indepNeg (s := Finset.univ)
    (fun i _ ↦ (hcoord i).neg) (mul_nonneg hn'.le hδ.le)
  have heq : -((n:ℝ)*δ)^2 / (2 * ((Finset.univ.sum (fun _ : Fin n ↦ (1/4 : NNReal)) : NNReal) : ℝ)) = -2*n*δ^2 := by
    simp; field_simp; ring
  simp only [heq] at hu hl
  rw [tuple_probability]
  let up := {v | (n:ℝ)*δ ≤ ∑ i, Y i v}
  let down := {v | (n:ℝ)*δ ≤ ∑ i, -Y i v}
  have sub : {v : Fin n → α | List.ofFn v ∈ {xs | δ ≤ |empirical E xs - probability q E|}} ⊆ up ∪ down := by
    intro v hv
    change δ ≤ |empirical E (List.ofFn v) - m| at hv
    have hav : empirical E (List.ofFn v) = (∑ i, X (v i)) / n := by
      simp [empirical, X, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    rw [hav,le_abs] at hv
    change (n:ℝ)*δ ≤ ∑ i, Y i v ∨ (n:ℝ)*δ ≤ ∑ i, -Y i v
    simp only [Y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_neg_distrib]
    rcases hv with h | h
    · left; have := (le_div_iff₀ hn').mp (show δ+m ≤ (∑ i, X (v i)) / n by linarith); linarith
    · right; have := (div_le_iff₀ hn').mp (show (∑ i, X (v i)) / n ≤ m-δ by linarith); linarith
  apply (measureReal_mono sub).trans ((measureReal_union_le up down).trans _)
  exact (add_le_add hu hl).trans_eq (by ring)

end
end GenLimit.AgnosticLanguage
