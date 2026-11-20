import GenLimit.NoRegretLanguageGeneration.PredictionAnytime

namespace PredictionToGeneration

theorem finite_ldim_agnostic_littleO (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (d : Nat) (hd : 0<d) (hld : LdimLE H d) :
    (fun t => (SMF H t : ℝ)) =o[Filter.atTop] (fun t : Nat => (t : ℝ)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have he : 0<c^2/(16*(d : ℝ)) := by positivity
  filter_upwards [(ldimLog_sublinear d hd).bound he] with t ht
  simp only [Real.norm_natCast]
  rw [Real.norm_eq_abs, abs_of_nonneg (ldimLog_nonneg d t), Real.norm_natCast] at ht
  have hm := mul_le_mul_of_nonneg_left ht (show (0:ℝ)≤16*(d : ℝ)*(t : ℝ) by positivity)
  have heq : 16*(d : ℝ)*(t : ℝ)*(c^2/(16*(d : ℝ))*(t : ℝ))=(c*(t : ℝ))^2 := by
    field_simp
  rw [heq] at hm
  have hs := Real.sq_sqrt (show 0≤(d : ℝ)*(t : ℝ)*ldimLog d t from
    mul_nonneg (by positivity) (ldimLog_nonneg d t))
  have hb := finite_ldim_agnostic_rate H hu hne d t hd hld
  change (SMF H t : ℝ)≤4*Real.sqrt ((d : ℝ)*(t : ℝ)*ldimLog d t) at hb
  have hnon : 0≤c*(t : ℝ) := by positivity
  nlinarith [Real.sqrt_nonneg ((d : ℝ)*(t : ℝ)*ldimLog d t)]

theorem finite_ldim_realizable_littleO (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (d : Nat) (hd : 0<d) (hld : LdimLE H d) :
    (fun t => (MF H t : ℝ)) =o[Filter.atTop] (fun t : Nat => (t : ℝ)) := by
  have hb : (fun t => (MF H t : ℝ)) =O[Filter.atTop] (fun t => (SMF H t : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound'
    apply Filter.Eventually.of_forall
    intro t
    simp only [Real.norm_natCast]
    exact_mod_cast mf_le_smf H hu hne t
  exact hb.trans_isLittleO (finite_ldim_agnostic_littleO H hu hne d hd hld)

theorem finite_ldim_no_regret (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (d : Nat) (hd : 0<d) (hld : LdimLE H d) :
    RealizableNoRegret H ∧ AgnosticNoRegret H := by
  exact ⟨(realizable_no_regret_iff_isLittleO H hu hne).mpr
    (finite_ldim_realizable_littleO H hu hne d hd hld),
    (agnostic_no_regret_iff_isLittleO H hu hne).mpr
    (finite_ldim_agnostic_littleO H hu hne d hd hld)⟩

end PredictionToGeneration

