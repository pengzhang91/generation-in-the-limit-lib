import GenLimit.NoRegretLanguageGeneration.CommonAgnosticProfiles
import GenLimit.NoRegretLanguageGeneration.AnytimeAgnosticReal

namespace PredictionToGeneration.CommonProfiles

/-- One generator has a uniform asymptotic regret rate across all legal streams. -/
def UniformAgnosticRate (H : HypothesisClass X) (r : Nat → ℝ) : Prop :=
  ∃ G : Generator X, ∃ C : ℝ, 0  ≤  C ∧ ∃ N : Nat, ∀ xs,
    xs.Nodup → N  ≤  xs.length → ∀ h,H h → (regret h (G.play xs) : ℝ)  ≤  C*r xs.length

theorem regularize_unbounded (r : Nat → ℝ) (N : Nat)
    (hlarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hsmall : r =o[Filter.atTop] (fun t : Nat => (t : ℝ))) :
    ∀ c : Nat, ∃ t,c  <  regularize r N t := by
  intro c
  have hb := regularize_eventual_bounds r N hlarge hsmall
  have hl := hlarge.eventually (Filter.eventually_gt_atTop (2*(c+1 : ℝ)))
  obtain ⟨t,ht,hr⟩ := (hb.and hl).exists
  refine ⟨t,?_⟩
  have : (c : ℝ)  <  regularize r N t := by linarith [ht.2]
  exact_mod_cast this

theorem regularized_anytime_rate (r : Nat → ℝ) (N : Nat)
    (hmono : ∀ i j,N ≤ i → i ≤ j → r i ≤ r j)
    (hlarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hsmall : r =o[Filter.atTop] (fun t : Nat => (t : ℝ)))
    (hstable : ∃ C : ℝ,0 ≤ C ∧ ∃ M : Nat,∀ t,M ≤ t → r (8*t) ≤ C*r t) :
    UniformAgnosticRate (ArbitraryProfiles.H (regularize r N)) r := by
  let f := regularize r N
  let b := fun t => max 4 (f (8*t))
  have hfmono := regularize_monotone r N hmono
  have hbmono : ∀ i j,i ≤ j → b i ≤ b j := by
    intro i j hij
    have hh := hfmono (show 8*i ≤ 8*j by omega)
    dsimp [b,f]
    omega
  have hbunbounded : ∀ c : Nat,∃ t,c < b t := by
    intro c
    obtain ⟨t,ht⟩ := regularize_unbounded r N hlarge hsmall c
    have hh := hfmono (show t ≤ 8*t by omega)
    exact ⟨t,by dsimp [b,f] at *; omega⟩
  have hb : ∀ t,SMF (ArbitraryProfiles.H f) t ≤ b t := by
    intro t
    by_cases ht : 4 ≤ t
    · exact Nat.le_trans (ArbitraryProfiles.agnostic_upper f hfmono t ht) (Nat.le_max_right _ _)
    · have hh := smf_le_horizon (ArbitraryProfiles.H f) t
      dsimp [b]
      omega
  obtain ⟨G,hG⟩ := agnostic_horizon_to_anytime_nat (ArbitraryProfiles.H f)
    (Blocks.uus _ _ ArbitraryProfiles.size_positive) (Blocks.nonempty_class _ _) b hbmono hbunbounded
    (fun t _ => by dsimp [b]; omega) hb
  obtain ⟨C,hC,M,hM⟩ := hstable
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp (regularize_eventual_bounds r N hlarge hsmall)
  obtain ⟨L,hL⟩ := Filter.eventually_atTop.mp (hlarge.eventually (Filter.eventually_ge_atTop 1))
  refine ⟨G,16+4*C,by positivity,max 1 (max M (max K L)),?_⟩
  intro xs hn hlen h hh
  have hreg := hG xs hn (by omega) h hh
  have hreg' : (regret h (G.play xs) : ℝ)  ≤  4*(b xs.length : ℝ) := by exact_mod_cast hreg
  have hf8 := (hK (8*xs.length) (by omega)).1
  have hr8 := hM xs.length (by omega)
  have hr := hL xs.length (by omega)
  have hb' : (b xs.length : ℝ)  ≤  4+(f (8*xs.length):ℝ) := by
    exact_mod_cast (show b xs.length ≤ 4+f (8*xs.length) from by dsimp [b]; omega)
  dsimp [f] at hb'
  nlinarith

abbrev HasQuantitativeAgnosticProfile (r : Nat → ℝ) : Prop :=
  ∃ f : Nat → Nat,Countable {h // ArbitraryProfiles.H f h} ∧ UUS (ArbitraryProfiles.H f) ∧
    AgnosticNoRegret (ArbitraryProfiles.H f) ∧
    UniformAgnosticRate (ArbitraryProfiles.H f) r ∧
    (fun t : Nat => (SMF (ArbitraryProfiles.H f) t : ℝ)) =Θ[Filter.atTop] r

theorem realize_real_quantitative_profile (r : Nat → ℝ)
    (hmono : ∃ N : Nat,∀ i j,N ≤ i → i ≤ j → r i ≤ r j)
    (hlarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hsmall : r =o[Filter.atTop] (fun t : Nat => (t : ℝ)))
    (hstable : ∃ C : ℝ,0 ≤ C ∧ ∃ M : Nat,∀ t,M ≤ t → r (8*t) ≤ C*r t) :
    HasQuantitativeAgnosticProfile r := by
  obtain ⟨N,hN⟩ := hmono
  let f := regularize r N
  have hm := regularize_monotone r N hN
  have ht := regularize_theta r N hlarge hsmall
  have hf : NatSublinear f := (natSublinear_iff_isLittleO f).mpr (ht.1.trans_isLittleO hsmall)
  refine ⟨f,Blocks.countable_class _ _,Blocks.uus _ _ ArbitraryProfiles.size_positive,
    ArbitraryProfiles.agnostic_no_regret f hm hf,regularized_anytime_rate r N hN hlarge hsmall hstable,?_⟩
  exact (ArbitraryProfiles.agnostic_theta_of_rescaling f hm
    (fun t ht => (regularize_admissible r N t ht).2)
    (regularize_stable r N hlarge hsmall hstable)).trans ht






theorem quantitative_agnostic_power_profile (a : ℝ) (ha : 0 < a) (ha' : a < 1) :
    HasQuantitativeAgnosticProfile (fun t : Nat => (t : ℝ) ^ a) := by
  apply realize_real_quantitative_profile
  · refine ⟨0, ?_⟩
    intro i j _ hij
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hij) (le_of_lt ha)
  · exact (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  · exact power_sublinear ha'
  · refine ⟨(8 : ℝ) ^ a, Real.rpow_nonneg (by norm_num) _, 0, ?_⟩
    intro t _
    simp only [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) (Nat.cast_nonneg t)]
    exact le_rfl



theorem quantitative_agnostic_logarithmic_profile (b : ℝ) (hb : 0 < b) : HasQuantitativeAgnosticProfile (logPower b) := by
  apply realize_real_quantitative_profile
  · exact ⟨0, fun _ _ _ hij => logPower_monotone b (le_of_lt hb) hij⟩
  · exact logPower_tendsto b hb
  · exact logPower_sublinear b
  · exact ⟨(2 : ℝ) ^ b, Real.rpow_nonneg (by norm_num) _, 8, fun t ht => logPower_scale b (le_of_lt hb) t ht⟩



theorem quantitative_agnostic_powerLog_profile (a b : ℝ) (ha : 0 < a) (ha' : a < 1) (hb : 0 < b) :
    HasQuantitativeAgnosticProfile (powerLog a b) := by
  apply realize_real_quantitative_profile
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



theorem quantitative_agnostic_nearLinear_profile (b : ℝ) (hb : 0 < b) :
    HasQuantitativeAgnosticProfile (nearLinear b) := by
  obtain ⟨f,hc,hu,hn,hr,ht⟩ := realize_real_quantitative_profile (shiftedNearLinear b)
    (shiftedNearLinear_monotone_tail b hb) (shiftedNearLinear_tendsto b)
    (shiftedNearLinear_sublinear b hb) ⟨8,by norm_num,1,shiftedNearLinear_scale b hb⟩
  refine ⟨f,hc,hu,hn,?_,ht.trans (nearLinear_shift_theta b)⟩
  obtain ⟨G,C,hC,N,hN⟩ := hr
  refine ⟨G,2*C,by positivity,max N 1,?_⟩
  intro xs hnd hlen h hh
  have hg := hN xs hnd (by omega) h hh
  have hpos := logPower_pos b xs.length (by omega)
  have ht' : (1 : ℝ) ≤ xs.length := by exact_mod_cast (show 1≤xs.length by omega)
  have hs : shiftedNearLinear b xs.length ≤ 2*nearLinear b xs.length := by
    dsimp [shiftedNearLinear,nearLinear]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hpos.le
  have hmul := mul_le_mul_of_nonneg_left hs hC
  nlinarith

end PredictionToGeneration.CommonProfiles
