import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankGeneration

/-! Uniform relative count estimates for all ambient intervals. The
additive constant may depend on the presentation and the tolerance. -/
namespace GenLimit.KleinbergWei.Banach
open Set DensityMeasures
open scoped Classical
noncomputable section

theorem interval_counts {C : LanguageFamily} (inf : ∀ z, (C z).Infinite)
    {R : ℕ} (hr : TowerTopology.FiniteRankAtMost (range C) R)
    (B : SpatialBins C) {z s} (pres : Presents s (C z)) {ε : ℝ} (pos : 0 < ε) :
    let O := range (OrderedFocus.play (IntervalGenerator.rule hr B inf) s)
    ∃ H : ℕ, ∀ l u, let K := (Finset.Ico l u).filter (· ∈ C z)
      H ≤ K.card → (1/2-ε)*(K.card:ℝ) ≤ (K.filter (· ∈ O)).card := by
  let O := range (OrderedFocus.play (IntervalGenerator.rule hr B inf) s)
  obtain ⟨J,cert⟩ := finite_rank_bin_counts inf hr B pres
  let cost := 2*R
  obtain ⟨p,hp⟩ := exists_nat_gt ((cost:ℝ)/ε)
  let M := max (max J z) (p+1)
  have mj : J ≤ M := (le_max_left ..).trans (le_max_left ..)
  have mz : z ≤ M := (le_max_right ..).trans (le_max_left ..)
  have mp : p+1 ≤ M := le_max_right ..
  have cm : (cost:ℝ) ≤ ε*M := by
    have a := (div_lt_iff₀ pos).mp hp
    have b : (p:ℝ) ≤ M := by exact_mod_cast (show p ≤ M by omega)
    nlinarith [mul_le_mul_of_nonneg_left b pos.le]
  obtain ⟨N,hn⟩ := exists_nat_gt ((2*cost+B.edge M:ℝ)/ε)
  refine ⟨N,fun l u => ?_⟩
  let K := (Finset.Ico l u).filter (· ∈ C z)
  change N ≤ K.card → (1/2-ε)*(K.card:ℝ) ≤ ((K.filter (· ∈ O)).card:ℝ)
  intro hk
  have bound := B.window_accounting z O cost J cert M (by omega) mz mj l u
  let b := K.card/M
  have num : (K.card:ℝ) ≤ 2*((K.filter (· ∈ O)).card:ℝ)+cost*(b+2)+B.edge M := by
    exact_mod_cast bound
  have mb : (M:ℝ)*b ≤ K.card := by exact_mod_cast Nat.mul_div_le K.card M
  have lin : (cost:ℝ)*b ≤ ε*K.card := by
    nlinarith only [mul_le_mul_of_nonneg_right cm (Nat.cast_nonneg (α := ℝ) b),mul_le_mul_of_nonneg_left mb pos.le]
  have hle : (N:ℝ) ≤ K.card := by exact_mod_cast hk
  have c := (div_lt_iff₀ pos).mp hn
  change (1/2-ε)*(K.card:ℝ) ≤ ((K.filter (· ∈ O)).card:ℝ)
  nlinarith only [num,lin,c,mul_le_mul_of_nonneg_left hle pos.le]

end
end GenLimit.KleinbergWei.Banach
