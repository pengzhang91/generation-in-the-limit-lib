import GenLimit.Paper17_InfiniteContamination.AlgorithmNine

/-! # The noise and displacement parameters printed in Theorem 7.7 -/

namespace GenLimit.InfiniteContamination

open GenLimit.KleinbergWei

/-- An odd prefix cannot have at most half noise and at most half as many
available target ranks as observations. Eventual bounds suffice because a
long prefix absorbs the ranks occurring before the displacement bound starts. -/
theorem no_half_noise_half_displacement
    (K : OrderedLanguage) (s : Generic.Stream ℕ) (hinj : Function.Injective s)
    {c M : ℝ} (hc : c ≤ 1/2) (hM : M ≤ 1/2)
    (hnoise : ConstantNoise s K.carrier c)
    (hbound : BoundedDisplacement K s K.carrier M) : False := by
  obtain ⟨T, hT⟩ := hbound
  obtain ⟨U, hU⟩ := hnoise
  let rank := fun i ↦ canonicalRank K K.carrier (s i)
  let B := max U (∑ i ∈ Finset.range T, rank i)
  let n := 2 * B + 1
  have hn : 0 < n := by dsimp [n]; omega
  have hprefix := lemma_7_5_finite_prefix_core K s K.carrier (by rfl) n B (by
    intro i hi
    by_cases ht : i < T
    · exact (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (rank j))
        (Finset.mem_range.mpr ht)).trans (le_max_right ..)
    · have h := (hT i (by omega)).trans
          (mul_le_mul_of_nonneg_right hM (by positivity))
      have hi' : (i : ℝ) + 1 ≤ 2 * (B : ℝ) + 1 := by
        exact_mod_cast (show i+1 ≤ 2*B+1 from hi)
      have hr : (2 : ℝ) * rank i ≤ 2 * (B : ℝ) + 1 := by dsimp [rank]; linarith
      have hr' : 2 * rank i ≤ 2 * B + 1 := by exact_mod_cast hr
      change rank i ≤ B
      omega)
  have htrue : trueCount s K.carrier n ≤ B := by
    simpa only [empiricalTargetCount_eq_trueCount_of_injective s hinj,
      OrderedLanguage.prefixCount_carrier] using hprefix
  have hUn : U ≤ n := (le_max_left ..).trans (show B ≤ n by dsimp [n]; omega)
  have hrate := (hU n hUn).trans hc
  rw [empiricalNoiseRate, if_neg hn.ne'] at hrate
  have hcount := (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mp hrate
  have hh : (2 : ℝ) * noiseCount s K.carrier n ≤ n := by linarith
  have hh' : 2 * noiseCount s K.carrier n ≤ n := by exact_mod_cast hh
  have hsum := trueCount_add_noiseCount s K.carrier n
  dsimp [n] at *
  omega

/-- For every k ≥ 2 the printed adversary class is empty, for every target.
Consequently any generator vacuously succeeds on that class. -/
theorem theorem_7_7_no_admissible_stream (k : ℕ) (hk : 2 ≤ k)
    (K : OrderedLanguage) (s : Generic.Stream ℕ) (hinj : Function.Injective s)
    (hnoise : ConstantNoise s K.carrier (1 / k)) :
    ¬ BoundedDisplacement K s K.carrier (1 / k) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hk'
  exact no_half_noise_half_displacement K s hinj h h hnoise

end GenLimit.InfiniteContamination
