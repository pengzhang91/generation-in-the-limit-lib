import GenLimit.NoRegretLanguageGeneration.PredictionRates
import GenLimit.NoRegretLanguageGeneration.AnytimeAgnosticReal
import GenLimit.NoRegretLanguageGeneration.NamedProfiles

namespace PredictionToGeneration

noncomputable def ldimLog (d T : Nat) : ℝ := Real.logb 2 (1+(T : ℝ)/d)

theorem ldimLog_nonneg (d T : Nat) : 0 ≤ ldimLog d T := by
  apply div_nonneg
  · exact Real.log_nonneg (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  · exact (Real.log_pos (by norm_num : (1:ℝ)<2)).le

theorem ldimLog_monotone (d : Nat) : Monotone (ldimLog d) := by
  intro i j hij
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  apply Real.log_le_log (by positivity)
  exact add_le_add_left (div_le_div_of_nonneg_right (by exact_mod_cast hij) (Nat.cast_nonneg d)) _

theorem ldimLog_tendsto (d : Nat) (hd : 0<d) :
    Filter.Tendsto (ldimLog d) Filter.atTop Filter.atTop := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have ht : Filter.Tendsto (fun t : Nat => 1+(t : ℝ)/d) Filter.atTop Filter.atTop := tendsto_const_nhds.add_atTop (tendsto_natCast_atTop_atTop.atTop_div_const hd')
  exact (Real.tendsto_log_atTop.comp ht).atTop_div_const (Real.log_pos (by norm_num))

theorem ldimLog_sublinear (d : Nat) (hd : 0<d) :
    ldimLog d =o[Filter.atTop] (fun t : Nat => (t : ℝ)) := by
  have hd' : (1:ℝ)≤d := by exact_mod_cast hd
  have hdom : ldimLog d =O[Filter.atTop] CommonProfiles.logPower 1 := by
    apply Asymptotics.IsBigO.of_bound (1/Real.log 2)
    apply Filter.Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (ldimLog_nonneg d t)]
    simp only [CommonProfiles.logPower, Real.rpow_one, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.log_nonneg (show (1:ℝ)≤(t : ℝ)+1 by exact le_add_of_nonneg_left (Nat.cast_nonneg t)))]
    dsimp [ldimLog, Real.logb]
    rw [one_div_mul_eq_div]
    apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    apply Real.log_le_log (by positivity)
    have hh := div_le_self (Nat.cast_nonneg t) hd'
    linarith
  exact hdom.trans_isLittleO (CommonProfiles.logPower_sublinear 1)

private theorem unbounded_of_tendsto {b : Nat → ℝ}
    (hb : Filter.Tendsto b Filter.atTop Filter.atTop) : ∀ c : ℝ, ∃ t, c<b t := by
  intro c
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp ((Filter.tendsto_atTop.mp hb) (c+1))
  exact ⟨N, by linarith [hN N le_rfl]⟩

theorem finite_ldim_realizable_anytime (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (d : Nat) (hd : 0<d) (hld : LdimLE H d) :
    ∃ G : Generator X, ∀ xs, xs.Nodup → 1≤xs.length →
      ∀ h, H h → Realizes h (G.play xs) →
        (mistakes h (G.play xs) : ℝ) ≤ 4+16*(d : ℝ)*ldimLog d xs.length := by
  let b : Nat → ℝ := fun t => 1+4*(d : ℝ)*ldimLog d t
  have hm : Monotone b := fun i j hij => add_le_add_left
    (mul_le_mul_of_nonneg_left (ldimLog_monotone d hij) (by positivity)) _
  have ht : Filter.Tendsto b Filter.atTop Filter.atTop :=
    tendsto_const_nhds.add_atTop ((ldimLog_tendsto d hd).const_mul_atTop (by positivity))
  obtain ⟨G,hG⟩ := horizon_to_anytime_real H hu hne b hm (unbounded_of_tendsto ht)
    (fun t _ => by dsimp [b]; linarith [mul_nonneg (show (0:ℝ)≤4*d by positivity) (ldimLog_nonneg d t)])
    (fun t _ => (finite_ldim_realizable_rate H hu hne d t hd hld).trans (by dsimp [b,ldimLog]; linarith))
  refine ⟨G, fun xs hn hl h hh hr => ?_⟩
  convert hG xs hn hl h hh hr using 1 <;> dsimp [b] <;> ring

theorem finite_ldim_agnostic_anytime (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (d : Nat) (hd : 0<d) (hld : LdimLE H d) :
    ∃ G : Generator X, ∀ xs, xs.Nodup → 1≤xs.length →
      ∀ h, H h → (regret h (G.play xs) : ℝ) ≤
        4+16*Real.sqrt ((d : ℝ)*(xs.length : ℝ)*ldimLog d xs.length) := by
  let a : Nat → ℝ := fun t => (d : ℝ)*(t : ℝ)*ldimLog d t
  have ha : ∀ t, 0≤a t := fun t => mul_nonneg (by positivity) (ldimLog_nonneg d t)
  have ham : Monotone a := by
    intro i j hij
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (Nat.cast_nonneg d))
      (ldimLog_monotone d hij) (ldimLog_nonneg d i) (by positivity)
  have hat : Filter.Tendsto a Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by exact_mod_cast hd)).atTop_mul_atTop₀
      (ldimLog_tendsto d hd)
  have hst : Filter.Tendsto (fun t => Real.sqrt (a t)) Filter.atTop Filter.atTop := by
    simpa only [Real.sqrt_eq_rpow] using (tendsto_rpow_atTop (show (0:ℝ)<1/2 by norm_num)).comp hat
  let b : Nat → ℝ := fun t => 1+4*Real.sqrt (a t)
  have hm : Monotone b := fun i j hij => add_le_add_left
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (ham hij)) (by norm_num)) _
  have ht : Filter.Tendsto b Filter.atTop Filter.atTop :=
    tendsto_const_nhds.add_atTop (hst.const_mul_atTop (by norm_num))
  obtain ⟨G,hG⟩ := agnostic_horizon_to_anytime_real H hu hne b hm (unbounded_of_tendsto ht)
    (fun t _ => by dsimp [b]; linarith [Real.sqrt_nonneg (a t)])
    (fun t => (finite_ldim_agnostic_rate H hu hne d t hd hld).trans (by dsimp [b,a,ldimLog]; linarith))
  refine ⟨G, fun xs hn hl h hh => ?_⟩
  convert hG xs hn hl h hh using 1 <;> dsimp [b,a] <;> ring

end PredictionToGeneration


