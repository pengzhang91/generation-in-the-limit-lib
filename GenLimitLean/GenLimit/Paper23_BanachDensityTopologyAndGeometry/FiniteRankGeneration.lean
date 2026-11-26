import GenLimit.Paper23_BanachDensityTopologyAndGeometry.IntervalGenerator
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.BinDensity

/-! Theorem 4.5, using a fixed partition adapted to the countable family
and inherited adjacent matchings. The same finite-history rule works
on all exact presentations and requires no advance knowledge of the target. -/
namespace GenLimit.KleinbergWei.Banach
open Set TowerTopology DensityMeasures DensityMeasures.FiniteRankParent
open scoped Classical ENNReal
noncomputable section

theorem finite_rank_bin_counts {C : LanguageFamily} (inf : ∀ z, (C z).Infinite)
    {R : ℕ} (hr : TowerTopology.FiniteRankAtMost (range C) R)
    (B : SpatialBins C) {z s} (pres : Presents s (C z)) :
    let A := IntervalGenerator.rule hr B inf
    let O := range (OrderedFocus.play A s)
    ∃ J, ∀ j ≥ J, ∀ l u, let K := (Finset.Ico l u).filter (· ∈ C z)
      (B.cell j ∩ K).card ≤ 2*(B.cell j ∩ K.filter (· ∈ O)).card+2*R := by
  let A := IntervalGenerator.rule hr B inf
  let O := range (OrderedFocus.play A s)
  obtain ⟨J,cert⟩ := IntervalGenerator.eventual_seed hr B pres
  refine ⟨J,?_⟩
  intro j late l u
  by_cases visit : ∃ t, B.number (s t)=j
  · let v := IntervalGenerator.seed B s j
    have reach := cert j late visit
    have cover (x y : ℕ) (inK : x ∈ C z) (link : ForestMatching.mate hr (B.cell j) v x=some y) :
        x ∈ O ∨ y ∈ O := by
      obtain ⟨ne,hy,back⟩ := ForestMatching.mate_spec hr _ _ link
      have hx := (ForestMatching.mate_spec hr _ _ back).2.1
      have f : IntervalGenerator.planned hr B s x=some y := by simpa [IntervalGenerator.planned,B.cell_iff.mp hx,v] using link
      have g : IntervalGenerator.planned hr B s y=some x := by simpa [IntervalGenerator.planned,B.cell_iff.mp hy,v] using back
      exact IntervalGenerator.protects hr B inf pres inK f g ne
    have count := ForestMatching.count hr (B.cell j) v reach O l u cover
    have eq : ((B.cell j).filter (· ∈ C z)) ∩ Finset.Ico l u = B.cell j ∩ ((Finset.Ico l u).filter (· ∈ C z)) := by
      ext; simp; tauto
    change (((B.cell j).filter (· ∈ C z)) ∩ Finset.Ico l u).card ≤ 2*((((B.cell j).filter (· ∈ C z)) ∩ Finset.Ico l u).filter (· ∈ O)).card+2*R at count
    have eqHit (S : Finset ℕ) : ((B.cell j ∩ S).filter (· ∈ O)) = B.cell j ∩ (S.filter (· ∈ O)) := by
      ext; simp; tauto
    rw [eq,eqHit] at count
    exact count
  · have empty : B.cell j ∩ ((Finset.Ico l u).filter (· ∈ C z)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr; intro x hx
      obtain ⟨h,inside⟩ := Finset.mem_inter.mp hx
      obtain ⟨t,rfl⟩ := (show x ∈ range s from pres.symm ▸ (Finset.mem_filter.mp inside).2)
      exact visit ⟨t,B.cell_iff.mp h⟩
    simp [empty]

theorem finite_rank_generation (C : LanguageFamily) (inf : ∀ z, (C z).Infinite)
    {R : ℕ} (hr : TowerTopology.FiniteRankAtMost (range C) R) :
    ∃ A : List ℕ → ℕ, ∀ z s, Presents s (C z) →
      OrderedFocus.ElementValid s (OrderedFocus.play A s) (C z) ∧
        ENNReal.ofReal (1/2) ≤ lowerBanachDensity
          ((OrderedLanguage.increasing (C z) (inf z)).rankSet (range (OrderedFocus.play A s))) := by
  let B := SpatialBins.build C inf
  let A := IntervalGenerator.rule hr B inf
  refine ⟨A,?_⟩
  intro z s pres
  refine ⟨IntervalGenerator.validity hr B inf pres,?_⟩
  let O := range (OrderedFocus.play A s)
  obtain ⟨J,bound⟩ := finite_rank_bin_counts inf hr B pres
  exact B.banach_half z (inf z) O (2*R) J bound

end
end GenLimit.KleinbergWei.Banach
