import GenLimit.NoRegretLanguageGeneration.NamedProfiles
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

namespace PredictionToGeneration.CommonProfiles

noncomputable def nearLinear (b : ℝ) (t : Nat) : ℝ := (t : ℝ) / logPower b t
noncomputable def shiftedNearLinear (b : ℝ) (t : Nat) : ℝ := ((t : ℝ) + 1) / logPower b t

theorem logPower_pos (b : ℝ) (t : Nat) (ht : 1 ≤ t) : 0 < logPower b t := by
  apply Real.rpow_pos_of_pos
  apply Real.log_pos
  have hp : (1 : ℝ) ≤ t := by exact_mod_cast ht
  linarith

theorem shiftedNearLinear_sublinear (b : ℝ) (hb : 0 < b) :
    shiftedNearLinear b =o[Filter.atTop] (fun t : Nat => (t : ℝ)) := by
  have hh : shiftedNearLinear b =o[Filter.atTop] (fun t : Nat => (t : ℝ) + 1) := by
    apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr
    · have hi := (logPower_tendsto b hb).inv_tendsto_atTop
      apply hi.congr'
      apply Filter.Eventually.of_forall
      intro t
      dsimp [shiftedNearLinear]
      have ht : (t : ℝ) + 1 ≠ 0 := by positivity
      by_cases hl : logPower b t = 0
      · simp [hl]
      · field_simp
    · apply Filter.Eventually.of_forall
      intro t ht
      have hp : (0 : ℝ) < (t : ℝ) + 1 := by positivity
      exact False.elim (ne_of_gt hp ht)
  exact hh.trans_isBigO shifted_nat_bigO

theorem shiftedNearLinear_tendsto (b : ℝ) :
    Filter.Tendsto (shiftedNearLinear b) Filter.atTop Filter.atTop := by
  have hh : logPower b =o[Filter.atTop] (fun t : Nat => (t : ℝ) + 1) := by
    simpa [logPower, Function.comp_def, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop b (show (0 : ℝ) < 1 by norm_num)).comp_tendsto shifted_nat_tendsto
  have hz := hh.tendsto_div_nhds_zero
  have hpos : ∀ᶠ t : Nat in Filter.atTop, 0 < logPower b t / ((t : ℝ) + 1) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with t ht
    exact div_pos (logPower_pos b t ht) (by positivity)
  have hgt : Filter.Tendsto (fun t : Nat => logPower b t / ((t : ℝ) + 1))
      Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := tendsto_nhdsWithin_iff.mpr ⟨hz, hpos⟩
  simpa [Pi.inv_def, shiftedNearLinear] using hgt.inv_tendsto_nhdsGT_zero

theorem shiftedNearLinear_monotone_tail (b : ℝ) (hb : 0 < b) :
    ∃ N : Nat, ∀ i j, N ≤ i → i ≤ j → shiftedNearLinear b i ≤ shiftedNearLinear b j := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp b + 1)
  refine ⟨N, ?_⟩
  intro i j hNi hij
  have hi : Real.exp b ≤ (i : ℝ) + 1 := by
    have hn : (N : ℝ) ≤ i := by exact_mod_cast hNi
    linarith
  have hij' : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
  have hj : Real.exp b ≤ (j : ℝ) + 1 := le_trans hi hij'
  have hi1 : 1 ≤ i := by
    have he : (0 : ℝ) < Real.exp b := Real.exp_pos _
    have hn : (N : ℝ) ≤ i := by exact_mod_cast hNi
    have : (0 : ℝ) < i := by linarith
    exact_mod_cast (show (1 : Nat) ≤ i by exact Nat.pos_iff_ne_zero.mp (by exact_mod_cast this) |> Nat.one_le_iff_ne_zero.mpr)
  have hj1 : 1 ≤ j := by omega
  have hlog : Real.log ((j : ℝ) + 1) / ((j : ℝ) + 1) ^ (1 / b) ≤
      Real.log ((i : ℝ) + 1) / ((i : ℝ) + 1) ^ (1 / b) :=
    Real.log_div_self_rpow_antitoneOn (one_div_pos.mpr hb)
      (by simpa using hi) (by simpa using hj) hij'
  have hinonneg : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hjnonneg : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hnonneg : 0 ≤ Real.log ((j : ℝ) + 1) / ((j : ℝ) + 1) ^ (1 / b) := by
    exact div_nonneg (Real.log_nonneg (by linarith only [hinonneg, hjnonneg])) (Real.rpow_nonneg (by positivity) _)
  have hp := Real.rpow_le_rpow hnonneg hlog (le_of_lt hb)
  rw [Real.div_rpow (Real.log_nonneg (by linarith only [hinonneg, hjnonneg])) (Real.rpow_nonneg (by positivity) _) b,
    Real.div_rpow (Real.log_nonneg (by linarith only [hinonneg, hjnonneg])) (Real.rpow_nonneg (by positivity) _) b] at hp
  rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
    one_div_mul_cancel (ne_of_gt hb), Real.rpow_one, Real.rpow_one] at hp
  have hc := (div_le_div_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1) (by positivity : (0 : ℝ) < (i : ℝ) + 1)).mp hp
  apply (div_le_div_iff₀ (logPower_pos b i hi1) (logPower_pos b j hj1)).mpr
  dsimp [logPower] at *
  nlinarith

theorem shiftedNearLinear_scale (b : ℝ) (hb : 0 < b) (t : Nat) (ht : 1 ≤ t) :
    shiftedNearLinear b (8 * t) ≤ 8 * shiftedNearLinear b t := by
  have hm := logPower_monotone b (le_of_lt hb) (show t ≤ 8 * t by omega)
  have hp := logPower_pos b t ht
  have hp8 := logPower_pos b (8 * t) (by omega)
  dsimp [shiftedNearLinear]
  have hh := (div_le_div_iff₀ hp8 hp).mpr (show
      (((8 * t : Nat) : ℝ) + 1) * logPower b t ≤ (8 * ((t : ℝ) + 1)) * logPower b (8 * t) by
    push_cast
    nlinarith)
  simpa [mul_div_assoc] using hh

theorem nearLinear_shift_theta (b : ℝ) :
    shiftedNearLinear b =Θ[Filter.atTop] nearLinear b := by
  constructor
  · apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with t ht
    have hp := logPower_pos b t ht
    have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hn : 0 ≤ nearLinear b t := div_nonneg (Nat.cast_nonneg _) (le_of_lt hp)
    have hs : 0 ≤ shiftedNearLinear b t := div_nonneg (by positivity) (le_of_lt hp)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hn, abs_of_nonneg hs]
    dsimp [nearLinear, shiftedNearLinear]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hp hp).mpr
    nlinarith
  · apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with t ht
    have hp := logPower_pos b t ht
    have hn : 0 ≤ nearLinear b t := div_nonneg (Nat.cast_nonneg _) (le_of_lt hp)
    have hs : 0 ≤ shiftedNearLinear b t := div_nonneg (by positivity) (le_of_lt hp)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hn, abs_of_nonneg hs, one_mul]
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hp)

theorem nearLinear_profile (b : ℝ) (hb : 0 < b) : HasRealizableProfile (nearLinear b) := by
  obtain ⟨f, hc, hu, hn, ht⟩ := realize_real_profile (shiftedNearLinear b)
    (shiftedNearLinear_monotone_tail b hb) (shiftedNearLinear_tendsto b)
    (shiftedNearLinear_sublinear b hb) ⟨8, by norm_num, 1, shiftedNearLinear_scale b hb⟩
  exact ⟨f, hc, hu, hn, ht.trans (nearLinear_shift_theta b)⟩

end PredictionToGeneration.CommonProfiles


