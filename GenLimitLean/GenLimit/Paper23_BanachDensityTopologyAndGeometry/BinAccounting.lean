import GenLimit.Paper23_BanachDensityTopologyAndGeometry.SpatialBins
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity
import GenLimit.Core.NaturalDensity

/-! Sum a uniform per-bin interval error over a relative window.
At most two intersected bins are partial. Each full bin of index at
least M contains at least M target words. -/
namespace GenLimit.KleinbergWei.Banach.SpatialBins
open Set Filter
open scoped Classical ENNReal
noncomputable section
variable {C : LanguageFamily} (B : SpatialBins C)

private theorem sum_cells (S : Finset ℕ) (J : Finset ℕ) :
    ∑ j ∈ J, (B.cell j ∩ S).card = (S.filter fun x => B.number x ∈ J).card := by
  rw [←Finset.sum_card_fiberwise_eq_card_filter S J B.number]
  apply Finset.sum_congr rfl; intro j _
  congr 1; ext x; simp [B.cell_iff,and_comm]

theorem window_accounting (z : ℕ) (O : Set ℕ) (cost start : ℕ)
    (perBin : ∀ j ≥ start, ∀ l u, let K := (Finset.Ico l u).filter (· ∈ C z)
      (B.cell j ∩ K).card ≤ 2*(B.cell j ∩ K.filter (· ∈ O)).card+cost)
    (M : ℕ) (positive : 0 < M) (hz : z ≤ M) (late : start ≤ M) (l u : ℕ) :
    let K := (Finset.Ico l u).filter (· ∈ C z)
    K.card ≤ 2*(K.filter (· ∈ O)).card + cost*(K.card/M+2) + B.edge M := by
  let K := (Finset.Ico l u).filter (· ∈ C z)
  let A := K.filter (· ∈ O)
  change K.card ≤ 2*A.card + cost*(K.card/M+2) + B.edge M
  let L := B.number l; let U := B.number u
  let J := Finset.Icc (max M L) U
  let I := Finset.Ico (max M (L+1)) U
  have lower := Finset.mem_Ico.mp (B.in_cell l)
  have upper := Finset.mem_Ico.mp (B.in_cell u)
  have inner (j : ℕ) (hj : j ∈ I) : M ≤ (B.cell j ∩ K).card := by
    obtain ⟨low,hi⟩ := Finset.mem_Ico.mp hj
    have m : M ≤ j := (le_max_left ..).trans low
    have ldist : L+1 ≤ j := (le_max_right ..).trans low
    have lb := B.strict.monotone ldist
    have ub := B.strict.monotone (show j+1 ≤ U from hi)
    have contained : (B.cell j).filter (· ∈ C z) ⊆ B.cell j ∩ K := by
      intro x hx; obtain ⟨hcell,mem⟩ := Finset.mem_filter.mp hx
      obtain ⟨a,b⟩ := Finset.mem_Ico.mp hcell
      exact Finset.mem_inter.mpr ⟨hcell,Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
        ⟨(lower.2.le.trans lb).trans a,b.trans_le (ub.trans upper.1)⟩,mem⟩⟩
    exact (m.trans (Nat.le_succ _)).trans ((B.thick j z (hz.trans m)).trans (Finset.card_le_card contained))
  have budget : I.card*M ≤ K.card := calc
    I.card*M = ∑ _j ∈ I, M := by simp
    _ ≤ ∑ j ∈ I, (B.cell j ∩ K).card := Finset.sum_le_sum inner
    _ ≤ K.card := by rw [B.sum_cells]; exact Finset.card_filter_le ..
  have num : J.card ≤ K.card/M+2 := by
    have h := (Nat.le_div_iff_mul_le positive).mpr budget
    simp only [I,J,Nat.card_Ico,Nat.card_Icc] at *; omega
  have cover : K ⊆ (K.filter fun x => B.number x ∈ J) ∪ Finset.range (B.edge M) := by
    intro x hx
    obtain ⟨bd,_⟩ := Finset.mem_filter.mp hx
    obtain ⟨xl,xu⟩ := Finset.mem_Ico.mp bd
    by_cases good : M ≤ B.number x
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,Finset.mem_Icc.mpr
        ⟨max_le good (B.number_mono xl),B.number_mono xu.le⟩⟩)
    · have lt : B.number x+1 ≤ M := by omega
      exact Finset.mem_union_right _ (Finset.mem_range.mpr ((Finset.mem_Ico.mp (B.in_cell x)).2.trans_le (B.strict.monotone lt)))
  have subtotal : ∑ j ∈ J, (B.cell j ∩ K).card ≤ 2*(∑ j ∈ J, (B.cell j ∩ A).card)+J.card*cost := calc
    _ ≤ ∑ j ∈ J, (2*(B.cell j ∩ A).card+cost) := Finset.sum_le_sum fun j hj =>
      perBin j (late.trans ((le_max_left ..).trans (Finset.mem_Icc.mp hj).1)) l u
    _ = _ := by simp [Finset.sum_add_distrib,Finset.mul_sum]
  rw [B.sum_cells,B.sum_cells] at subtotal
  have floor := (Finset.card_le_card cover).trans (Finset.card_union_le ..)
  rw [Finset.card_range] at floor
  have gen := Finset.card_filter_le A (fun x => B.number x ∈ J)
  have scaled := Nat.mul_le_mul_left cost num
  rw [Nat.mul_comm J.card cost] at subtotal
  omega

end
end GenLimit.KleinbergWei.Banach.SpatialBins
