import GenLimit.Paper08_HallucinationDetection.Probabilistic
import GenLimit.Paper03_HallucinationAndModeCollapse.StatisticalNecessity
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Algebra.BigOperators.Fin

/-! # Finite iid samples and almost-sure hallucination detection

The finite-prefix marginal of the infinite iid stream is the ordered PMF
used in P03. This connects the almost-sure identifier recovered by P08 to
P03's necessity theorem for eventual error below one half.
-/
namespace GenLimit.Bridge.Paper03ToPaper08IID

open HallucinationDetection HallucinationModeCollapse DiscreteIID MeasureTheory Filter
open scoped Topology ENNReal BigOperators

local instance : MeasurableSpace (List ℕ) := ⊤
local instance : DiscreteMeasurableSpace (List ℕ) := ⟨fun _ ↦ trivial⟩

private theorem samples_ofFn (p : PMF ℕ) {n : ℕ} (v : Fin n → ℕ) :
    samples p n (List.ofFn v) = ∏ i, p (v i) := by
  classical
  induction n with
  | zero => simp [samples]
  | succ n ih =>
    rw [List.ofFn_succ, samples, PMF.bind_apply, Fin.prod_univ_succ]
    let xs := List.ofFn (fun i : Fin n ↦ v i.succ)
    have hm (x : ℕ) : (PMF.map (List.cons x) (samples p n)) (v 0 :: xs) =
        if v 0 = x then samples p n xs else 0 := by
      rw [PMF.map_apply]
      by_cases h : v 0 = x
      · simp only [h,List.cons.injEq,true_and,if_true]
        rw [tsum_eq_single xs (fun a ha ↦ if_neg ha.symm),if_pos rfl]
      · simp [h]
    simp_rw [show List.ofFn (fun i : Fin n ↦ v i.succ) = xs from rfl,hm,mul_ite,mul_zero]
    rw [tsum_eq_single (v 0) (fun a ha ↦ if_neg ha.symm),if_pos rfl]
    simpa [xs] using congrArg (p (v 0) * ·) (ih (fun i ↦ v i.succ))

private theorem measurable_prefix (n : ℕ) : Measurable (fun s : ℕ → ℕ ↦ textPrefix s n) := by
  simp_rw [textPrefix_eq_ofFn]
  exact (measurable_of_countable (f := fun f : Fin n → ℕ ↦ List.ofFn f)).comp
    (measurable_pi_lambda _ (fun i : Fin n ↦ measurable_pi_apply i.val))

/-- Finite ordered marginal, including zero-length and repeated observations. -/
theorem iid_prefix_marginal (p : PMF ℕ) (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure)).map (fun s ↦ textPrefix s n) =
      (samples p n).toMeasure := by
  classical
  apply Measure.ext_of_singleton
  intro xs
  rw [Measure.map_apply (measurable_prefix n) (.singleton _),
    PMF.toMeasure_apply_singleton _ _ (.singleton _)]
  by_cases he : xs.length = n
  · subst n
    let v := xs.get
    let y (i : ℕ) := if h : i < xs.length then v ⟨i,h⟩ else 0
    have hpre : (fun s : ℕ → ℕ ↦ textPrefix s xs.length) ⁻¹' {xs} =
        Set.pi (Finset.range xs.length : Set ℕ) (fun i ↦ {y i}) := by
      ext s
      change textPrefix s xs.length = xs ↔ ∀ i ∈ Finset.range xs.length, s i ∈ ({y i} : Set ℕ)
      rw [textPrefix_eq_ofFn]
      constructor
      · intro h i hi
        have hv : (fun i : Fin xs.length ↦ s i) = xs.get :=
          List.ofFn_injective (h.trans (List.ofFn_get xs).symm)
        have := congrFun hv ⟨i,Finset.mem_range.mp hi⟩
        simpa [y,hi,v,Finset.mem_range.mp hi] using this
      · intro h
        apply Eq.trans _ (List.ofFn_get xs)
        apply congrArg List.ofFn
        funext i
        simpa [y,i.isLt] using h i (Finset.mem_range.mpr i.isLt)
    rw [hpre,Measure.infinitePi_pi _ (fun _ _ ↦ .singleton _)]
    simp_rw [PMF.toMeasure_apply_singleton _ _ (.singleton _)]
    rw [← Fin.prod_univ_eq_prod_range]
    have hp := samples_ofFn p v
    simpa [y,v] using hp.symm
  · have hs : (fun s : ℕ → ℕ ↦ textPrefix s n) ⁻¹' {xs} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro s hs
      exact he (by simpa using (congrArg List.length (show textPrefix s n = xs from hs)).symm)
    rw [hs,measure_empty]
    exact (PMF.apply_eq_zero_iff _ _).mpr (fun h ↦ he ((samples_support p n xs).mp h).1) |>.symm

/-- Almost-sure eventual detection for every full-support iid sampling law
is equivalent to the finite tell-tale condition, on the coded domain ℕ. -/
theorem iid_detection_iff_conditionTwo (C : Generic.LanguageFamily ℕ) :
    IIDDetectable C ↔ Angluin.ConditionTwo C := by
  rw [iid_detectable_iff_identifiable]
  constructor
  · rintro ⟨M,hm⟩
    apply conditionTwo_of_eventual_small_error C (deterministicIdentifier M)
    intro z p hp
    let μ := Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure)
    let B : Set (List ℕ) := {xs | C (M xs) ≠ C z}
    let E (n : ℕ) := (fun s : ℕ → ℕ ↦ textPrefix s n) ⁻¹' B
    have he : Tendsto (fun n ↦ μ (E n)) atTop (𝓝 0) := by
      rw [← measure_empty (μ := μ)]
      apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty
        (fun n ↦ measurable_prefix n (.of_discrete))
      filter_upwards [hm z p hp] with s hs
      obtain ⟨j,hj,T,hT⟩ := hs
      filter_upwards [eventually_ge_atTop T] with n hn
      simp [B,hT n hn,hj]
    have he' := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp he
    have hs : ∀ᶠ n : ℕ in atTop, (μ (E n)).toReal < (1/2 : ℝ) :=
      he'.eventually_lt_const (by norm_num)
    filter_upwards [hs] with n hn
    rw [identificationError_deterministic]
    change ((samples p n).toOuterMeasure B).toReal < _
    rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (.of_discrete),
      ← iid_prefix_marginal, Measure.map_apply (measurable_prefix _) (.of_discrete)]
    exact hn
  · intro h
    obtain ⟨M,hm⟩ := (Angluin.semanticallyInferrable_iff_conditionTwo C).2 h
    refine ⟨M,fun z p hp ↦ ?_⟩
    filter_upwards [iid_presents_support p] with s hs
    exact hm z s (hp ▸ hs)

end GenLimit.Bridge.Paper03ToPaper08IID
