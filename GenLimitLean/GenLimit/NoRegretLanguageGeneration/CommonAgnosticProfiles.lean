import GenLimit.NoRegretLanguageGeneration.ArbitraryAgnosticProfiles
import GenLimit.NoRegretLanguageGeneration.NearLinearProfile

namespace PredictionToGeneration.CommonProfiles

abbrev HasAgnosticProfile (r : Nat → ℝ) : Prop :=
  ∃ f : Nat → Nat,
    Countable {h // ArbitraryProfiles.H f h} ∧ UUS (ArbitraryProfiles.H f) ∧
    AgnosticNoRegret (ArbitraryProfiles.H f) ∧
    (fun t : Nat => (SMF (ArbitraryProfiles.H f) t : ℝ)) =Θ[Filter.atTop] r

/-- Real-valued common profiles, with finite initial irregularities removed,
are realized by an agnostic no-regret class and one anytime generator. -/
theorem realize_real_agnostic_profile (r : Nat → ℝ)
    (hmono : ∃ N : Nat, ∀ i j, N ≤ i → i ≤ j → r i ≤ r j)
    (hlarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hsmall : r =o[Filter.atTop] (fun t : Nat => (t : ℝ)))
    (hstable : ∃ C : ℝ, 0 ≤ C ∧ ∃ M : Nat, ∀ t, M ≤ t → r (8*t) ≤ C*r t) :
    HasAgnosticProfile r := by
  obtain ⟨N,hN⟩ := hmono
  let f := regularize r N
  have hm := regularize_monotone r N hN
  have ht := regularize_theta r N hlarge hsmall
  have hf : NatSublinear f := (natSublinear_iff_isLittleO f).mpr (ht.1.trans_isLittleO hsmall)
  refine ⟨f,Blocks.countable_class _ _,Blocks.uus _ _ ArbitraryProfiles.size_positive,
    ArbitraryProfiles.agnostic_no_regret f hm hf,?_⟩
  exact (ArbitraryProfiles.agnostic_theta_of_rescaling f hm
    (fun t ht => (regularize_admissible r N t ht).2)
    (regularize_stable r N hlarge hsmall hstable)).trans ht

theorem agnostic_power_profile (a : ℝ) (ha : 0 < a) (ha' : a < 1) :
    HasAgnosticProfile (fun t : Nat => (t : ℝ) ^ a) := by
  apply realize_real_agnostic_profile
  · refine ⟨0, ?_⟩
    intro i j _ hij
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hij) (le_of_lt ha)
  · exact (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  · exact power_sublinear ha'
  · refine ⟨(8 : ℝ) ^ a, Real.rpow_nonneg (by norm_num) _, 0, ?_⟩
    intro t _
    simp only [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) (Nat.cast_nonneg t)]
    exact le_rfl


theorem agnostic_logarithmic_profile (b : ℝ) (hb : 0 < b) : HasAgnosticProfile (logPower b) := by
  apply realize_real_agnostic_profile
  · exact ⟨0, fun _ _ _ hij => logPower_monotone b (le_of_lt hb) hij⟩
  · exact logPower_tendsto b hb
  · exact logPower_sublinear b
  · exact ⟨(2 : ℝ) ^ b, Real.rpow_nonneg (by norm_num) _, 8, fun t ht => logPower_scale b (le_of_lt hb) t ht⟩


theorem agnostic_powerLog_profile (a b : ℝ) (ha : 0 < a) (ha' : a < 1) (hb : 0 < b) :
    HasAgnosticProfile (powerLog a b) := by
  apply realize_real_agnostic_profile
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
    convert hm using 1 <;> ring


theorem agnostic_nearLinear_profile (b : ℝ) (hb : 0 < b) : HasAgnosticProfile (nearLinear b) := by
  obtain ⟨f,hc,hu,hn,ht⟩ := realize_real_agnostic_profile (shiftedNearLinear b)
    (shiftedNearLinear_monotone_tail b hb) (shiftedNearLinear_tendsto b)
    (shiftedNearLinear_sublinear b hb) ⟨8,by norm_num,1,shiftedNearLinear_scale b hb⟩
  exact ⟨f,hc,hu,hn,ht.trans (nearLinear_shift_theta b)⟩

end PredictionToGeneration.CommonProfiles
