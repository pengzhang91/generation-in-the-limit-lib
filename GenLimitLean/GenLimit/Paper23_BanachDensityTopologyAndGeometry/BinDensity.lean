import GenLimit.Paper23_BanachDensityTopologyAndGeometry.BinAccounting

/-! Uniform interval estimates in ambient coordinates imply the source
Banach bound for windows in the increasing order of the actual target. -/
namespace GenLimit.KleinbergWei.Banach.SpatialBins
open Set Filter
open scoped Classical ENNReal
noncomputable section

private theorem rank_counts (K O : Set ℕ) (hi : K.Infinite) (m k : ℕ) :
    let E := OrderedLanguage.increasing K hi
    let S := (Finset.Ico (E.enumeration m) (E.enumeration (m+k))).filter (· ∈ K)
    S.card = k ∧ (S.filter (· ∈ O)).card = windowCount (E.rankSet O) m k := by
  let E := OrderedLanguage.increasing K hi
  let e := E.enumeration
  let S := (Finset.Ico (e m) (e (m+k))).filter (· ∈ K)
  let I := Finset.Ico m (m+k)
  have inc : StrictMono e := OrderedLanguage.increasing_strictMono K hi
  have cover : range e=K := E.range_enumeration
  have image : I.image e = S := by
    ext x; constructor
    · rintro h; obtain ⟨i,mem,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨l,u⟩ := Finset.mem_Ico.mp mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨inc.monotone l,inc u⟩,cover ▸ mem_range_self i⟩
    · intro h; obtain ⟨bd,inK⟩ := Finset.mem_filter.mp h
      obtain ⟨i,rfl⟩ := cover.symm ▸ inK
      obtain ⟨l,u⟩ := Finset.mem_Ico.mp bd
      exact Finset.mem_image.mpr ⟨i,Finset.mem_Ico.mpr ⟨inc.le_iff_le.mp l,inc.lt_iff_lt.mp u⟩,rfl⟩
  change S.card = k ∧ (S.filter (· ∈ O)).card = windowCount (E.rankSet O) m k
  rw [←image,Finset.card_image_of_injective _ inc.injective,Finset.filter_image]
  simp [windowCount,I,OrderedLanguage.rankSet,e,Finset.card_image_of_injective _ inc.injective]

private theorem half_of_estimate (A : Set ℕ) (cost base : ℕ) (edge : ℕ → ℕ)
    (bound : ∀ M ≥ base, 0 < M → ∀ m k, k ≤ 2*windowCount A m k + cost*(k/M+2)+edge M) :
    ENNReal.ofReal (1/2) ≤ lowerBanachDensity A := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  have lt : (r:ℝ) < 1/2 := (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).mp hr
  let δ := (1/2:ℝ)-r
  have pos : 0 < δ := sub_pos.mpr lt
  obtain ⟨q,hq⟩ := exists_nat_gt ((cost:ℝ)/δ)
  let M := max base (q+1)
  have big : q ≤ M := (Nat.le_succ _).trans (le_max_right ..)
  have cm : (cost:ℝ) ≤ δ*M := by
    have h := (div_lt_iff₀ pos).mp hq
    have le : (q:ℝ) ≤ (M:ℝ) := by exact_mod_cast big
    nlinarith [mul_le_mul_of_nonneg_left le pos.le]
  have mpos : 0 < M := (Nat.succ_pos q).trans_le (le_max_right ..)
  obtain ⟨N,hN⟩ := exists_nat_gt ((2*cost+edge M : ℝ)/δ)
  apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun _ => le_top))
  filter_upwards [eventually_ge_atTop (N+1)] with k hk
  apply le_iInf; intro m
  split_ifs
  · have h := bound M (le_max_left ..) mpos m k
    let a := windowCount A m k
    let b := k/M
    have numeric : (k:ℝ) ≤ 2*a + cost*(b+2)+edge M := by exact_mod_cast h
    have mul : (M:ℝ)*(b:ℝ) ≤ k := by exact_mod_cast Nat.mul_div_le k M
    have c₁ : (cost:ℝ)*b ≤ δ*k := by
      nlinarith [mul_le_mul_of_nonneg_right cm (by positivity : 0 ≤ (b:ℝ)),
        mul_le_mul_of_nonneg_left mul pos.le]
    have c₂ : (2*cost+edge M:ℝ) ≤ δ*k := by
      have h := (div_lt_iff₀ pos).mp hN
      have kn : (N:ℝ) ≤ k := by exact_mod_cast (show N ≤ k by omega)
      nlinarith [mul_le_mul_of_nonneg_left kn pos.le]
    have kp : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have rat : (r:ℝ) ≤ a/k := by
      apply (le_div_iff₀ kp).mpr
      dsimp only [δ] at c₁ c₂; nlinarith
    simpa only [windowRatio,if_neg (by omega : k≠0),ENNReal.ofReal_div_of_pos kp,
      ENNReal.ofReal_natCast,ENNReal.ofReal_coe_nnreal,a] using ENNReal.ofReal_le_ofReal rat
  · exact le_top

theorem banach_half {C : LanguageFamily} (B : SpatialBins C) (z : ℕ) (hi : (C z).Infinite) (O : Set ℕ)
    (cost start : ℕ) (perBin : ∀ j ≥ start, ∀ l u, let K := (Finset.Ico l u).filter (· ∈ C z)
      (B.cell j ∩ K).card ≤ 2*(B.cell j ∩ K.filter (· ∈ O)).card+cost) :
    ENNReal.ofReal (1/2) ≤ lowerBanachDensity ((OrderedLanguage.increasing (C z) hi).rankSet O) := by
  apply half_of_estimate _ cost (max z start) B.edge
  intro M large pos m k
  let E := OrderedLanguage.increasing (C z) hi
  have bound := B.window_accounting z O cost start perBin M pos ((le_max_left ..).trans large)
    ((le_max_right ..).trans large) (E.enumeration m) (E.enumeration (m+k))
  obtain ⟨size,hits⟩ := rank_counts (C z) O hi m k
  dsimp only at bound size hits
  simpa only [size,hits,E] using bound

end
end GenLimit.KleinbergWei.Banach.SpatialBins
