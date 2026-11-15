import GenLimit.NoRegretLanguageGeneration.ArbitraryProfiles

namespace PredictionToGeneration.CommonProfiles

/-- Finite initial irregularities and noninteger profile values are removed
before applying the integer-valued arbitrary-profile theorem. -/
noncomputable def regularize (r : Nat → ℝ) (N t : Nat) : Nat :=
  min t (max 1 (Nat.floor (r (max N t))))

theorem regularize_admissible (r : Nat → ℝ) (N t : Nat) (ht : 1 ≤ t) :
    1 ≤ regularize r N t ∧ regularize r N t ≤ t := by
  unfold regularize
  omega

theorem regularize_monotone (r : Nat → ℝ) (N : Nat)
    (hr : ∀ i j, N ≤ i → i ≤ j → r i ≤ r j) : Monotone (regularize r N) := by
  intro i j hij
  have hm : max N i ≤ max N j := by omega
  have hf := Nat.floor_mono (hr (max N i) (max N j) (by omega) hm)
  unfold regularize
  omega

theorem regularize_eventual_bounds (r : Nat → ℝ) (N : Nat)
    (hlarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hsmall : r =o[Filter.atTop] (fun t : Nat => (t : ℝ))) :
    ∀ᶠ t : Nat in Filter.atTop,
      (regularize r N t : ℝ) ≤ r t ∧ r t ≤ 2 * (regularize r N t : ℝ) := by
  have hlo : ∀ᶠ t : Nat in Filter.atTop, (2 : ℝ) ≤ r t := hlarge.eventually (Filter.eventually_ge_atTop 2)
  have hup := hsmall.def (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hlo, hup, Filter.eventually_ge_atTop N] with t hlo hup ht
  have hp : 0 ≤ r t := by linarith
  simp only [Real.norm_eq_abs, one_mul, abs_of_nonneg hp] at hup
  rw [abs_of_nonneg (Nat.cast_nonneg t)] at hup
  have hf : Nat.floor (r t) ≤ t := by
    have hfloor := Nat.floor_le hp
    exact_mod_cast (show (Nat.floor (r t) : ℝ) ≤ (t : ℝ) by linarith)
  have hfloor : 1 ≤ Nat.floor (r t) := Nat.le_floor (by norm_num; linarith)
  have he : regularize r N t = Nat.floor (r t) := by
    simp only [regularize, Nat.max_eq_right ht, Nat.max_eq_right hfloor, Nat.min_eq_right hf]
  rw [he]
  constructor
  · exact Nat.floor_le hp
  · have hh := Nat.lt_floor_add_one (r t)
    have hh' : (1 : ℝ) ≤ Nat.floor (r t) := by exact_mod_cast hfloor
    linarith

theorem regularize_theta (r : Nat → ℝ) (N : Nat)
    (hlarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hsmall : r =o[Filter.atTop] (fun t : Nat => (t : ℝ))) :
    (fun t => (regularize r N t : ℝ)) =Θ[Filter.atTop] r := by
  have hb := regularize_eventual_bounds r N hlarge hsmall
  constructor
  · apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [hb] with t ht
    have hp : 0 ≤ r t := le_trans (Nat.cast_nonneg _) ht.1
    simpa [Real.norm_eq_abs, abs_of_nonneg hp] using ht.1
  · apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [hb] with t ht
    have hp : 0 ≤ r t := le_trans (Nat.cast_nonneg _) ht.1
    simpa [Real.norm_eq_abs, abs_of_nonneg hp] using ht.2

theorem regularize_stable (r : Nat → ℝ) (N : Nat)
    (hlarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hsmall : r =o[Filter.atTop] (fun t : Nat => (t : ℝ)))
    (hstable : ∃ C : ℝ, 0 ≤ C ∧ ∃ M : Nat, ∀ t, M ≤ t → r (8 * t) ≤ C * r t) :
    ∃ C M : Nat, ∀ t, M ≤ t → regularize r N (8 * t) ≤ C * regularize r N t := by
  obtain ⟨C, hC, M, hM⟩ := hstable
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (regularize_eventual_bounds r N hlarge hsmall)
  obtain ⟨D, hD⟩ := exists_nat_gt (2 * C)
  refine ⟨D, max M K, ?_⟩
  intro t ht
  have h1 := hK t (by omega)
  have h8 := hK (8 * t) (by omega)
  have hs := hM t (by omega)
  have hnonneg : (0 : ℝ) ≤ regularize r N t := Nat.cast_nonneg _
  have hh : (regularize r N (8 * t) : ℝ) ≤ (D : ℝ) * regularize r N t := by
    nlinarith
  exact_mod_cast hh

/-- A reusable rigorous form of the common-profiles corollary. It handles
real-valued profiles and finite initial failures of monotonicity automatically. -/
theorem realize_real_profile (r : Nat → ℝ)
    (hmono : ∃ N : Nat, ∀ i j, N ≤ i → i ≤ j → r i ≤ r j)
    (hlarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hsmall : r =o[Filter.atTop] (fun t : Nat => (t : ℝ)))
    (hstable : ∃ C : ℝ, 0 ≤ C ∧ ∃ M : Nat, ∀ t, M ≤ t → r (8 * t) ≤ C * r t) :
    ∃ f : Nat → Nat,
      Countable {h // ArbitraryProfiles.H f h} ∧ UUS (ArbitraryProfiles.H f) ∧
      RealizableNoRegret (ArbitraryProfiles.H f) ∧
      (fun t : Nat => (MF (ArbitraryProfiles.H f) t : ℝ)) =Θ[Filter.atTop] r := by
  obtain ⟨N, hN⟩ := hmono
  let f := regularize r N
  have hm := regularize_monotone r N hN
  have ht := regularize_theta r N hlarge hsmall
  have hf : NatSublinear f := (natSublinear_iff_isLittleO f).mpr (ht.1.trans_isLittleO hsmall)
  refine ⟨f, Blocks.countable_class _ _, Blocks.uus _ _ ArbitraryProfiles.size_positive,
    ArbitraryProfiles.no_regret f hm hf, ?_⟩
  exact (ArbitraryProfiles.theta_of_rescaling f hm
    (fun t ht => (regularize_admissible r N t ht).2)
    (regularize_stable r N hlarge hsmall hstable)).trans ht

end PredictionToGeneration.CommonProfiles



