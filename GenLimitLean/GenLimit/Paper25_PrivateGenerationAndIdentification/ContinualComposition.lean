import GenLimit.Support.DifferentialPrivacy
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! A privacy inequality on every finite transcript extends to all measurable
events of the complete output stream, with the same privacy parameters. -/
namespace GenLimit.PrivateLimit

open MeasureTheory Set Privacy
open scoped ENNReal symmDiff
noncomputable section

private theorem extend_bound {ι : Type*} {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    (μ ν : Measure (∀ i, Y i)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {b δ : ℝ} (hb : 0 ≤ b)
    (bound : ∀ T ∈ measurableCylinders Y, μ.real T ≤ b*ν.real T+δ) :
    ∀ E, MeasurableSet E → μ.real E ≤ b*ν.real E+δ := by
  intro E hm
  have alg : IsSetAlgebra (measurableCylinders Y) :=
    ⟨empty_mem_measurableCylinders Y, fun _ => compl_mem_measurableCylinders, fun _ _ => union_mem_measurableCylinders⟩
  have dense := Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite (μ+ν) alg
    (generateFrom_measurableCylinders (α := Y)).symm
  by_contra! h
  let η := (μ.real E-(b*ν.real E+δ))/(1+b)
  have hp : 0 < η := div_pos (sub_pos.mpr h) (by linarith)
  obtain ⟨T,ht,err⟩ := dense.approx E hm (measure_ne_top _ _) η hp
  have hr := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr err
  change (μ+ν).real (E ∆ T) < _ at hr
  rw [measureReal_add_apply, ENNReal.toReal_ofReal hp.le] at hr
  have ht' := dense.measurable T ht
  have hμ := (abs_le.mp (abs_measureReal_sub_le_measureReal_symmDiff (μ := μ)
    hm.nullMeasurableSet ht'.nullMeasurableSet)).2
  have hν := (abs_le.mp (abs_measureReal_sub_le_measureReal_symmDiff (μ := ν)
    hm.nullMeasurableSet ht'.nullMeasurableSet)).1
  have total : μ.real (E ∆ T) + b*ν.real (E ∆ T) <
      μ.real E - (b*ν.real E+δ) := by
    have hh := (lt_div_iff₀ (show 0 < 1+b by linarith)).mp hr
    nlinarith [measureReal_nonneg (μ := ν) (s := E ∆ T),
      mul_nonneg hb (measureReal_nonneg (μ := μ) (s := E ∆ T))]
  nlinarith [bound T ht,mul_nonneg hb (show 0 ≤ ν.real (E ∆ T)+ν.real E-ν.real T by linarith)]

/-- Continual-release composition can be proved on arbitrary finite
coordinate sets and every measurable event in the finite output space. -/
theorem private_of_finite_transcripts {X Y : Type*} [MeasurableSpace Y] (M : ContinualRelease X Y)
    (ε δ : ℝ) (hδ : 0 ≤ δ)
    (finite : ∀ u v, Neighbors u v → ∀ I : Finset ℕ, ∀ B : Set (I → Y), MeasurableSet B →
      (M.law u).real (cylinder I B) ≤ Real.exp ε*(M.law v).real (cylinder I B)+δ) :
    DifferentiallyPrivate ε (ENNReal.ofReal δ) M.law := by
  intro u v adj E hm
  letI := M.probability u
  letI := M.probability v
  have bound := extend_bound (M.law u) (M.law v) (Real.exp_pos ε).le (δ := δ)
    (fun T ht => by
      obtain ⟨I,B,hB,rfl⟩ := (mem_measurableCylinders _).mp ht
      exact finite u v adj I B hB) E hm
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _),ENNReal.ofReal_ne_top⟩)).mp
  simpa only [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    ENNReal.ofReal_ne_top,ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos ε).le,
    ENNReal.toReal_ofReal hδ,Measure.real_def] using bound

private theorem finite_product_bound {ι Y : Type*} [Fintype ι] [Countable Y]
    [MeasurableSpace Y] [MeasurableSingletonClass Y] (p q : ι → PMF Y) (a : ι → ℝ)
    (ε : ℝ) (budget : ∑ j, a j ≤ ε)
    (atoms : ∀ j y, p j y ≤ ENNReal.ofReal (Real.exp (a j))*q j y)
    (B : Set (ι → Y)) (hm : MeasurableSet B) :
    (Measure.pi fun j => (p j).toMeasure) B ≤ ENNReal.ofReal (Real.exp ε) *
      (Measure.pi fun j => (q j).toMeasure) B := by
  classical
  let law (r : ι → PMF Y) := Measure.pi fun j => (r j).toMeasure
  have mass (r : ι → PMF Y) (v : ι → Y) : law r {v} = ∏ j, r j (v j) := by
    rw [←univ_pi_singleton]
    simp only [law,Measure.pi_pi,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  have event (r : ι → PMF Y) : law r B = ∑' v, B.indicator (fun x => law r {x}) v := by
    letI : IsProbabilityMeasure (law r) := by dsimp [law]; infer_instance
    conv_lhs => rw [← (law r).toPMF_toMeasure,PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm,
      PMF.toOuterMeasure_apply]
    rfl
  change law p B ≤ ENNReal.ofReal (Real.exp ε)*law q B
  rw [event,event,←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro v
  by_cases h : v ∈ B
  · simp only [indicator_of_mem h,mass]
    calc
      _ ≤ ∏ j, (ENNReal.ofReal (Real.exp (a j))*q j (v j)) :=
        Finset.prod_le_prod' (fun j _ => atoms j (v j))
      _ ≤ _ := by
        rw [Finset.prod_mul_distrib,← ENNReal.ofReal_prod_of_nonneg
          (fun j _ => (Real.exp_pos (a j)).le),←Real.exp_sum]
        exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr budget)) _
  · simp [h]

/-- Countably many independent discrete releases compose whenever every
finite subfamily fits the privacy budget. The conclusion covers all
events of their joint infinite product law. -/
theorem private_independent_releases {X Y : Type*} [Countable Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (q : (ℕ → X) → ℕ → PMF Y) (ε : ℝ)
    (costs : ∀ u v, Neighbors u v → ∃ a : ℕ → ℝ, (∀ I : Finset ℕ, ∑ j ∈ I, a j ≤ ε) ∧
      ∀ j y, q u j y ≤ ENNReal.ofReal (Real.exp (a j))*q v j y) :
    DifferentiallyPrivate ε 0 (fun u => Measure.infinitePi (fun j => (q u j).toMeasure)) := by
  intro u v adj E hE
  obtain ⟨a,budget,step⟩ := costs u v adj
  let M (s : ℕ → X) := Measure.infinitePi fun j => (q s j).toMeasure
  haveI (s : ℕ → X) : IsProbabilityMeasure (M s) := by dsimp [M]; infer_instance
  have h := extend_bound (M u) (M v) (Real.exp_pos ε).le (δ := 0) (fun T ht => by
    obtain ⟨I,B,hB,rfl⟩ := (mem_measurableCylinders _).mp ht
    have b : ∑ j : I, a j ≤ ε := (Finset.sum_attach I a).le.trans (budget I)
    have hp := finite_product_bound (fun j : I => q u j) (fun j : I => q v j) (fun j : I => a j)
      ε b (fun j y => step j y) B hB
    have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hp
    have cylinder_eq (s : ℕ → X) : M s (cylinder I B) = (Measure.pi fun j : I => (q s j).toMeasure) B :=
      Measure.infinitePi_cylinder (fun j => (q s j).toMeasure) hB
    simpa only [Measure.real_def,cylinder_eq,add_zero,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos ε).le] using hr) E hE
  change M u E ≤ _*M v E+0
  rw [add_zero]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))).mp
  simpa only [add_zero,ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos ε).le,Measure.real_def] using h

/-- On disjoint input blocks, a single replacement affects at most one
release. The entire sequence therefore has the privacy cost of one block. -/
theorem private_parallel_releases {X Y : Type*} [Countable Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (q : (ℕ → X) → ℕ → PMF Y) {ε : ℝ} (he : 0 ≤ ε)
    (blocks : ∀ u v, Neighbors u v → ∃ k : ℕ, (∀ j ≠ k, q u j = q v j) ∧
      ∀ y, q u k y ≤ ENNReal.ofReal (Real.exp ε)*q v k y) :
    DifferentiallyPrivate ε 0 (fun u => Measure.infinitePi (fun j => (q u j).toMeasure)) := by
  apply private_independent_releases
  intro u v adj
  obtain ⟨k,same,one⟩ := blocks u v adj
  refine ⟨fun j => if j = k then ε else 0,?_,?_⟩
  · intro I
    by_cases h : k ∈ I <;> simp [h,he]
  · intro j y
    by_cases h : j = k
    · subst j; simpa using one y
    · simp [h,same j h]

/-- Deterministic post-processing may repeat epoch releases and transform
them into the word or hypothesis stream observed by the user. -/
theorem private_transcript_map {X Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    {law : (ℕ → X) → Measure Y} {ε : ℝ} {δ : ℝ≥0∞}
    (dp : DifferentiallyPrivate ε δ law) {f : Y → Z} (hf : Measurable f) :
    DifferentiallyPrivate ε δ (fun s => (law s).map f) := by
  intro u v adj E hm
  simpa only [Measure.map_apply hf hm] using dp u v adj (f ⁻¹' E) (hf hm)

end
end GenLimit.PrivateLimit
