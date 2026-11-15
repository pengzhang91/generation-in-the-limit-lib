import GenLimit.NoRegretLanguageGeneration.CommonProfiles
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace PredictionToGeneration.CommonProfiles

abbrev HasRealizableProfile (r : Nat → ℝ) : Prop :=
  ∃ f : Nat → Nat,
    Countable {h // ArbitraryProfiles.H f h} ∧ UUS (ArbitraryProfiles.H f) ∧
    RealizableNoRegret (ArbitraryProfiles.H f) ∧
    (fun t : Nat => (MF (ArbitraryProfiles.H f) t : ℝ)) =Θ[Filter.atTop] r

theorem power_sublinear {a : ℝ} (ha : a < 1) :
    (fun t : Nat => (t : ℝ) ^ a) =o[Filter.atTop] (fun t : Nat => (t : ℝ)) := by
  have hr : (fun x : ℝ => x ^ a) =o[Filter.atTop] (fun x : ℝ => x) := by
    apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr
    · have ht := tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 - a by linarith)
      apply ht.congr'
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      rw [show -(1 - a) = a - 1 by ring, Real.rpow_sub hx, Real.rpow_one]
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      intro he
      exact False.elim (ne_of_gt hx he)
  exact hr.comp_tendsto tendsto_natCast_atTop_atTop

theorem power_profile (a : ℝ) (ha : 0 < a) (ha' : a < 1) :
    HasRealizableProfile (fun t : Nat => (t : ℝ) ^ a) := by
  apply realize_real_profile
  · refine ⟨0, ?_⟩
    intro i j _ hij
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hij) (le_of_lt ha)
  · exact (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  · exact power_sublinear ha'
  · refine ⟨(8 : ℝ) ^ a, Real.rpow_nonneg (by norm_num) _, 0, ?_⟩
    intro t _
    simp only [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) (Nat.cast_nonneg t)]
    exact le_rfl

end PredictionToGeneration.CommonProfiles

namespace PredictionToGeneration.CommonProfiles

noncomputable def logPower (b : ℝ) (t : Nat) : ℝ := Real.log ((t : ℝ) + 1) ^ b

theorem shifted_nat_tendsto : Filter.Tendsto (fun t : Nat => (t : ℝ) + 1) Filter.atTop Filter.atTop :=
  tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

theorem shifted_nat_bigO : (fun t : Nat => (t : ℝ) + 1) =O[Filter.atTop] (fun t : Nat => (t : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with t ht
  have hp : (1 : ℝ) ≤ t := by exact_mod_cast ht
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t : ℝ) + 1)]
  rw [abs_of_nonneg (Nat.cast_nonneg t)]
  linarith

theorem logPower_monotone (b : ℝ) (hb : 0 ≤ b) : Monotone (logPower b) := by
  intro i j hij
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  apply Real.rpow_le_rpow (Real.log_nonneg (by linarith))
  · apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  · exact hb

theorem logPower_tendsto (b : ℝ) (hb : 0 < b) :
    Filter.Tendsto (logPower b) Filter.atTop Filter.atTop :=
  (tendsto_rpow_atTop hb).comp (Real.tendsto_log_atTop.comp shifted_nat_tendsto)

theorem logPower_sublinear (b : ℝ) : logPower b =o[Filter.atTop] (fun t : Nat => (t : ℝ)) := by
  have hs : logPower b =o[Filter.atTop] (fun t : Nat => (t : ℝ) + 1) := by
    simpa [logPower, Function.comp_def, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop b (show (0 : ℝ) < 1 by norm_num)).comp_tendsto shifted_nat_tendsto
  exact hs.trans_isBigO shifted_nat_bigO

theorem logPower_scale (b : ℝ) (hb : 0 ≤ b) (t : Nat) (ht : 8 ≤ t) :
    logPower b (8 * t) ≤ (2 : ℝ) ^ b * logPower b t := by
  have ht' : (8 : ℝ) ≤ t := by exact_mod_cast ht
  have hpoly : (8 : ℝ) * t + 1 ≤ ((t : ℝ) + 1) ^ 2 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg t) (show (0 : ℝ) ≤ t - 6 by linarith)]
  have hlog := Real.log_le_log (show (0 : ℝ) < 8 * t + 1 by positivity) hpoly
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hp : 0 ≤ Real.log ((8 : ℝ) * t + 1) := Real.log_nonneg (by linarith only [ht'] )
  have hr := Real.rpow_le_rpow hp hlog hb
  rw [Real.mul_rpow (by norm_num) (Real.log_nonneg (by linarith only [ht'] ))] at hr
  simpa [logPower, Nat.cast_mul] using hr

theorem logarithmic_profile (b : ℝ) (hb : 0 < b) : HasRealizableProfile (logPower b) := by
  apply realize_real_profile
  · exact ⟨0, fun _ _ _ hij => logPower_monotone b (le_of_lt hb) hij⟩
  · exact logPower_tendsto b hb
  · exact logPower_sublinear b
  · exact ⟨(2 : ℝ) ^ b, Real.rpow_nonneg (by norm_num) _, 8, fun t ht => logPower_scale b (le_of_lt hb) t ht⟩

end PredictionToGeneration.CommonProfiles


namespace PredictionToGeneration.CommonProfiles

noncomputable def powerLog (a b : ℝ) (t : Nat) : ℝ := (t : ℝ) ^ a * logPower b t

theorem powerLog_sublinear (a b : ℝ) (ha : 0 ≤ a) (ha' : a < 1) :
    powerLog a b =o[Filter.atTop] (fun t : Nat => (t : ℝ)) := by
  have hpower : (fun t : Nat => (t : ℝ) ^ a) =O[Filter.atTop] (fun t : Nat => ((t : ℝ) + 1) ^ a) := by
    apply Asymptotics.IsBigO.of_bound 1
    apply Filter.Eventually.of_forall
    intro t
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) a),
      abs_of_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (t : ℝ) + 1) a), one_mul]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) ha
  have hlog : logPower b =o[Filter.atTop] (fun t : Nat => ((t : ℝ) + 1) ^ (1 - a)) := by
    exact (isLittleO_log_rpow_rpow_atTop b (show 0 < 1 - a by linarith)).comp_tendsto shifted_nat_tendsto
  have hh := hpower.mul_isLittleO hlog
  have he : (fun t : Nat => ((t : ℝ) + 1) ^ a * ((t : ℝ) + 1) ^ (1 - a)) =
      (fun t : Nat => (t : ℝ) + 1) := by
    funext t
    rw [← Real.rpow_add (by positivity), show a + (1 - a) = 1 by ring, Real.rpow_one]
  rw [he] at hh
  exact hh.trans_isBigO shifted_nat_bigO

theorem powerLog_profile (a b : ℝ) (ha : 0 < a) (ha' : a < 1) (hb : 0 < b) :
    HasRealizableProfile (powerLog a b) := by
  apply realize_real_profile
  · refine ⟨0, ?_⟩
    intro i j _ hij
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    apply mul_le_mul
    · exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hij) (le_of_lt ha)
    · exact logPower_monotone b (le_of_lt hb) hij
    · exact Real.rpow_nonneg (Real.log_nonneg (by linarith only [hi])) _
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).atTop_mul_atTop₀ (logPower_tendsto b hb)
  · exact powerLog_sublinear a b (le_of_lt ha) ha'
  · refine ⟨(8 : ℝ) ^ a * (2 : ℝ) ^ b, by positivity, 8, ?_⟩
    intro t ht
    have hl := logPower_scale b (le_of_lt hb) t ht
    have hp : (0 : ℝ) ≤ (8 : ℝ) ^ a * (t : ℝ) ^ a := by positivity
    have hm := mul_le_mul_of_nonneg_left hl hp
    dsimp [powerLog]
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) (Nat.cast_nonneg t)]
    convert hm using 1; ring

end PredictionToGeneration.CommonProfiles



