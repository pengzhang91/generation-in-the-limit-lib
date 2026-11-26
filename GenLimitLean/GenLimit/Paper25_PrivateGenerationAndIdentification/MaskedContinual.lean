import GenLimit.Paper25_PrivateGenerationAndIdentification.MaskedRelease
import GenLimit.Paper25_PrivateGenerationAndIdentification.PrivateGenerationLower

/-! Start a private continual generator with the masked one-observation
release. Later epochs use the finite-family mechanism with larger public
prefixes. Their total privacy budget is one and their errors are summable. -/
namespace GenLimit.PrivateLimit.MaskedContinual

open MaskedRelease Set Filter Privacy MeasureTheory DiscreteIID
open scoped Classical ENNReal
noncomputable section

private abbrev Family (h : ℕ) := Fin (4*h) → Set ℕ

private def finish (h : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => 2*(4*h)*(j+2)*(j+3)*(j+10)

private def scheme {h : ℕ} (C : Family h) (bd : SubcollectionClosureBound (range C) 0) :
    Epoch.Scheme where
  count _ := 4*h
  family _ := C
  dim _ := 0
  bound _ := bd
  finish := finish h
  initial := rfl

private def pool (h : ℕ) := 32*(Epoch.horizon (finish h) 0 + 1)
private instance (h : ℕ) : NeZero (pool h) := ⟨by unfold pool; positivity⟩
private abbrev index (h : ℕ) : Label h ≃ Fin (4*h) := finProdFinEquiv

private def draw {h : ℕ} (C : Family h) (bd : SubcollectionClosureBound (range C) 0)
    (s : ℕ → ℕ) : ℕ → PMF ℕ
  | 0 => generator (C ∘ index h) (pool h) (Epoch.observations s 1)
  | j+1 => Epoch.sample (scheme C bd) 1 s (j+1)

private theorem depends {h : ℕ} (C : Family h) (bd : SubcollectionClosureBound (range C) 0)
    (u v : ℕ → ℕ) (j : ℕ) (agree : ∀ i ≤ finish h j, u i = v i) :
    draw C bd u j = draw C bd v j := by
  cases j with
  | zero => simp [draw,Epoch.observations,agree 0 (by rfl)]
  | succ j => exact Epoch.sample_depends (scheme C bd) 1 u v _ agree

private def mechanism {h : ℕ} (C : Family h) (bd : SubcollectionClosureBound (range C) 0) :=
  Epoch.release (finish h) rfl (draw C bd) (depends C bd)

private theorem private_release {h : ℕ} (C : Family h) (bd : SubcollectionClosureBound (range C) 0) :
    DifferentiallyPrivate (budget h + 1) 0 (mechanism C bd).law := by
  have nonneg : 0 ≤ budget h := Real.log_nonneg (by
    have := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := 3*h)
    linarith : 1 ≤ 128*(2:ℝ)^(3*h))
  apply Epoch.release_private
  apply private_independent_releases
  intro u v adj
  let a (j : ℕ) := (if j = 0 then budget h else 0) + Epoch.cost 1 j
  refine ⟨a, ?_, ?_⟩
  · intro I
    simp only [a,Finset.sum_add_distrib]
    apply add_le_add _ (Epoch.budget (by norm_num) I)
    by_cases hz : 0 ∈ I <;> simp [hz,nonneg]
  · rintro (_ | j) y
    · apply (Epoch.private_prefix nonneg (generator_private (C ∘ index h) (pool h)) adj y).trans
      apply mul_le_mul_right'
      gcongr
      simp [a, (Epoch.cost_pos (by norm_num : (0:ℝ) < 1) 0).le]
    · simpa [a,draw,Epoch.sample] using
        (Epoch.private_prefix (Epoch.cost_pos (by norm_num : (0:ℝ) < 1) (j+1)).le
          (FiniteCore.word_private C 0 (finish h (j+1)+1) (Epoch.horizon (finish h) (j+1))
            (Epoch.cost_pos (by norm_num : (0:ℝ) < 1) (j+1))) adj y)

private def error : ℕ → ℝ
  | 0 => 5/16
  | j+1 => (1/128)*(1/2)^j

private theorem sum_error : Summable error ∧ ∑' j, error j = 21/64 := by
  have geom := summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
  have tail : Summable (fun j => error (j+1)) := geom.mul_left _
  have sum : Summable error := (summable_nat_add_iff 1).mp tail
  refine ⟨sum,?_⟩
  rw [sum.tsum_eq_zero_add]
  change 5/16 + ∑' j : ℕ, (1/128:ℝ)*(1/2)^j = 21/64
  rw [geom.tsum_mul_left,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

private theorem error_nonneg (j : ℕ) : 0 ≤ error j := by cases j <;> dsimp [error] <;> positivity

private theorem late_error {h : ℕ} (hh : 0 < h) (C : Family h)
    (bd : SubcollectionClosureBound (range C) 0) (j : ℕ) :
    Epoch.errorAt (scheme C bd) 1 (j+1) ≤ error (j+1) := by
  have hp : 0 < (h:ℝ) := by exact_mod_cast hh
  have ratio : -(Epoch.cost 1 (j+1))*((finish h (j+1)+1:ℕ):ℝ)/(2*(4*h:ℕ)) ≤ -(j+10:ℝ) := by
    simp only [Epoch.cost,finish,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_succ]
    field_simp
    nlinarith
  have log_le : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have exp_le := Real.exp_le_exp.mpr (ratio.trans
    (show -(j+10:ℝ) ≤ -((j+10:ℕ):ℝ)*Real.log 2 by push_cast; nlinarith [mul_le_mul_of_nonneg_left log_le (show (0:ℝ) ≤ j+10 by positivity)]))
  rw [show -((j+10:ℕ):ℝ)*Real.log 2 = -(((j+10:ℕ):ℝ)*Real.log 2) by ring,
    Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)] at exp_le
  simp only [Epoch.errorAt,scheme,FiniteCore.errorTerm,Nat.cast_zero,sub_zero]
  apply (mul_le_mul_of_nonneg_left exp_le (by norm_num : (0:ℝ) ≤ 5)).trans
  simp only [error,pow_add,mul_inv_rev,one_div,inv_pow]
  norm_num
  linarith [show (0:ℝ) ≤ ((2:ℝ)^j)⁻¹ by positivity]

private theorem epoch_error {h : ℕ} (hh : 0 < h) (C : Family h)
    (bd : SubcollectionClosureBound (range C) 0) (z : Fin (4*h)) (s : ℕ → ℕ)
    (inj : Function.Injective s) (sub : range s ⊆ C z) (j : ℕ) :
    (Epoch.productLaw (draw C bd) s).real (Epoch.badEpoch (scheme C bd) (C z) s j) ≤ error j := by
  let H := Epoch.horizon (finish h) j
  let B := Epoch.badWord (C z) s H
  have hm : MeasurableSet B := .of_discrete
  have eval := measurePreserving_eval_infinitePi (fun i => (draw C bd s i).toMeasure) j
  change ((Measure.infinitePi (fun i => (draw C bd s i).toMeasure)) ((Function.eval j) ⁻¹' B)).toReal ≤ _
  rw [eval.measure_preimage hm.nullMeasurableSet, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm]
  cases j with
  | zero =>
    have overlap : SubcollectionClosureBound (range (C ∘ index h)) 0 := by
      rwa [(index h).surjective.range_comp]
    have mem : s 0 ∈ (C ∘ index h) ((index h).symm z) := by
      rw [Function.comp_apply,Equiv.apply_symm_apply]
      exact sub (mem_range_self 0)
    have upper := generator_error _ overlap _ mem (Epoch.observations s H) (pool h)
    simp only [Epoch.observations,List.length_map,List.length_range] at upper
    change probability (generator (C ∘ index h) (pool h) (Epoch.observations s 1)) B ≤ 5/16
    simp only [Epoch.observations,List.range_one,List.map_cons,List.map_nil]
    unfold B Epoch.badWord
    simp only [Function.comp_apply,Equiv.apply_symm_apply] at upper
    apply upper.trans
    have sz : (H:ℝ)/(pool h) ≤ 1/32 := by
      apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (pool h)))).mpr
      simp only [pool,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,H]
      linarith
    linarith
  | succ j =>
    apply le_trans _ (late_error hh C bd j)
    have hb := FiniteCore.word_failure C bd (Epoch.cost_pos (by norm_num : (0:ℝ) < 1) (j+1)) z
      (Epoch.observations s (finish h (j+1)+1)) (Epoch.observations s H)
      (List.nodup_range.map inj) (fun x hx => by
        obtain ⟨i,_,rfl⟩ := Epoch.mem_observations.mp hx
        exact sub (mem_range_self _))
    simpa only [Epoch.observations,List.length_map,List.length_range] using hb

private theorem correct {h : ℕ} (hh : 0 < h) (C : Family h)
    (bd : SubcollectionClosureBound (range C) 0) :
    Packing.UniformFrom (mechanism C bd) (range C) 1 ∧
      ∀ z s, Function.Injective s → range s = C z →
        ∀ᵐ y ∂(mechanism C bd).law s, ∃ T, y ∉ Epoch.failsAfter (C z) s T := by
  let P := scheme C bd
  have estimates (z : Fin (4*h)) (s : ℕ → ℕ) (inj : Function.Injective s) (eq : range s = C z) :=
    epoch_error hh C bd z s inj eq.subset
  constructor
  · rintro _ ⟨z,rfl⟩ s inj eq
    let μ := Epoch.productLaw (draw C bd) s
    have bound : μ (⋃ j, Epoch.badEpoch P (C z) s j) ≤ ENNReal.ofReal (21/64) := by
      apply (measure_iUnion_le _).trans
      rw [←sum_error.2, ENNReal.ofReal_tsum_of_nonneg error_nonneg sum_error.1]
      apply ENNReal.tsum_le_tsum
      intro j
      simpa only [Measure.real_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
        ENNReal.ofReal_le_ofReal (estimates z s inj eq j)
    let M := mechanism C bd
    letI := M.probability s
    have fail : (M.law s).real (Epoch.failsAfter (C z) s 0) ≤ 21/64 := by
      change ((μ.map (Epoch.playback P.finish)) (Epoch.failsAfter (C z) s 0)).toReal ≤ _
      rw [Measure.map_apply (Epoch.measurable_playback _) (Epoch.measurable_failsAfter ..)]
      have sub := Epoch.late_failure P (C z) s (r := 0) (t := 0) (by rfl)
      have b := (measure_mono (μ := μ) sub).trans (by simpa using bound)
      simpa only [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (21/64:ℝ))] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top b
    change 2/3 ≤ (M.law s).real (Epoch.failsAfter (C z) s 0)ᶜ
    rw [measureReal_compl (Epoch.measurable_failsAfter ..),measureReal_univ_eq_one]
    linarith
  · intro z s inj eq
    let μ := Epoch.productLaw (draw C bd) s
    have avoid := Voting.eventually_avoid μ (Epoch.badEpoch P (C z) s) sum_error.1
      (Eventually.of_forall (estimates z s inj eq))
    change ∀ᵐ y ∂μ.map (Epoch.playback P.finish), ∃ T, y ∉ Epoch.failsAfter (C z) s T
    apply (ae_map_iff (Epoch.measurable_playback _).aemeasurable ?_).mpr
    · filter_upwards [avoid] with y hy
      obtain ⟨r,hr⟩ := eventually_atTop.mp hy
      refine ⟨max r (P.finish r),fun bad => ?_⟩
      obtain ⟨l,hl⟩ := mem_iUnion.mp (Epoch.late_failure P (C z) s le_rfl bad)
      exact hr (r+l) (by omega) hl
    · simp only [setOf_exists]
      exact MeasurableSet.iUnion fun T => (Epoch.measurable_failsAfter ..).compl

/-- A deterministic generator guaranteed to succeed from the first observation
forces every nonempty intersection of a subcollection to be infinite. -/
theorem bound_of_first_observation (C : Set (Set ℕ)) (G : Generic.Generator ℕ)
    (ok : ∀ K ∈ C, ∀ n, 0 < n → ∀ xs : Fin n → ℕ, Function.Injective xs →
      range xs ⊆ K → G n xs ∈ K \ range xs) : SubcollectionClosureBound C 0 := by
  intro V sub fin
  by_contra! pos
  let S := ⋂₀ V
  letI : Fintype S := fin.fintype
  have nonempty : S.Nonempty := (Set.ncard_pos fin).mp pos
  letI : Nonempty S := nonempty.to_subtype
  let e := (Fintype.equivFin S).symm
  let xs := fun i => (e i : ℕ)
  have hits : range xs = S := by
    ext x
    exact ⟨fun ⟨i,h⟩ => h ▸ (e i).property,fun hx => ⟨e.symm ⟨x,hx⟩,by simp [xs]⟩⟩
  have member (K : Set ℕ) (hK : K ∈ V) :=
    ok K (sub hK) _ Fintype.card_pos xs (Subtype.val_injective.comp e.injective)
      (hits.subset.trans (sInter_subset_of_mem hK))
  have common : G _ xs ∈ S := mem_sInter.mpr (fun K hK => (member K hK).1)
  rcases V.eq_empty_or_nonempty with rfl | ⟨K,hK⟩
  · exact Set.infinite_univ (by simpa using fin)
  · exact (member K hK).2 (hits.symm.subset common)

/-- For any logarithmic allowance and all sufficiently large k = 4h, every
family that generates nonprivately from one observation admits an almost-sure
private continual generator beating C.3's proposed lower bound at m = 1. -/
theorem continual_counterexample (a b : ℝ) :
    ∀ᶠ h : ℕ in atTop, ∀ C : Fin (4*h) → Set ℕ,
      (∃ G : Generic.Generator ℕ, ∀ K ∈ range C, ∀ n, 0 < n → ∀ xs : Fin n → ℕ,
        Function.Injective xs → range xs ⊆ K → G n xs ∈ K \ range xs) →
      ∃ (ε : ℝ) (M : ContinualRelease ℕ ℕ), 0 < ε ∧
        ε < (4*h:ℕ)*Real.log 2 - a*Real.log (4*h) - b ∧
        DifferentiallyPrivate ε 0 M.law ∧ Packing.UniformFrom M (range C) 1 ∧
        ∀ z s, Function.Injective s → range s = C z →
          ∀ᵐ y ∂M.law s, ∃ T, y ∉ Epoch.failsAfter (C z) s T := by
  filter_upwards [below_published_bound a (b+1),eventually_ge_atTop 1] with h below hh
  rintro C ⟨G,ok⟩
  have bd := bound_of_first_observation _ G ok
  have nonneg : 0 ≤ budget h := Real.log_nonneg (by
    have := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := 3*h)
    linarith : 1 ≤ 128*(2:ℝ)^(3*h))
  refine ⟨budget h + 1, mechanism C bd, by linarith, ?_, private_release C bd, correct hh C bd⟩
  push_cast
  linarith

end
end GenLimit.PrivateLimit.MaskedContinual
