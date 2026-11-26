import GenLimit.Paper23_BanachDensityTopologyAndGeometry.TileGenerator
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.ForestCounts

/-! Sum the local board guarantees across forest layers and spatial tiles.
Only finitely many early tiles can have an incorrect seed. -/
namespace GenLimit.KleinbergWei.Banach.TileGenerator
open Set Finset TowerTopology DensityMeasures DensityMeasures.FiniteRankParent LatticeTiles
open scoped Classical
noncomputable section
variable {d L R : ℕ} {C : LanguageFamily} (hr : FiniteRankAtMost (FamilySpace C) R)
  (e : ℕ → Lattice d) (inj : Function.Injective e)

def sectionWords (K : Set ℕ) (l u : Lattice d) :=
  ((Finset.Icc l u).preimage e inj.injOn).filter (· ∈ K)

theorem mem_section {K l u x} : x ∈ sectionWords e inj K l u ↔ e x ∈ Finset.Icc l u ∧ x ∈ K := by
  simp [sectionWords]

/-- For every rectangle, a fixed-scale online generator loses one additive
logarithmic budget per tile and ancestor, and a finite startup cost. -/
theorem global_count (pos : 0 < L) {q : ℝ} (hq : 0 < q) (h1 : q ≤ 1/2)
    (inf : ∀ z, (C z).Infinite) {z s} (pres : Presents s (C z)) :
    let O := range (OrderedFocus.play (rule (L:=L) hr e inj q inf) s)
    ∃ H : ℕ, ∀ l u : Lattice d, let T := sectionWords e inj (C z) l u
      (1/2-q)*(T.card:ℝ) ≤ (T.filter (· ∈ O)).card +
        (indices L l u).card*(R*loss d L q) + H := by
  let O := range (OrderedFocus.play (rule (L:=L) hr e inj q inf) s)
  obtain ⟨H,est⟩ := ForestGames.global_count hr (cells (L:=L) e inj) (exact_bins e inj pos) O hq pres
  refine ⟨H,fun l u => ?_⟩
  let Q := (Finset.Icc l u).preimage e inj.injOn
  apply est Q (indices L l u) (loss d L q) (loss_nonneg d pos hq)
    (fun _ hx => number_mem pos (Finset.mem_preimage.mp hx))
  intro k meet i hi sub
  have bound := layer_count hr e inj pos hq h1 inf pres k l u meet i hi sub
  let D := board (L:=L) hr e inj k (TileSeed.seed (number L ∘ e) C s k) i
  have eq : D.filter (· ∈ Q) = D.filter (fun x => e x ∈ Finset.Icc l u) := by ext; simp [Q]
  change (1/2-q)*((D.filter (· ∈ Q)).card:ℝ)-loss d L q ≤ ((D.filter (· ∈ Q)).filter (· ∈ O)).card
  rw [eq]
  exact bound

end
end GenLimit.KleinbergWei.Banach.TileGenerator
