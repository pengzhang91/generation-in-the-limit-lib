import GenLimit.Paper23_BanachDensityTopologyAndGeometry.ForestGames
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.TileTests

/-! The finite-rank strategy on a fixed grid. At the first visit to a
tile its seed determines disjoint boards, one per ancestor layer.
A local game continues across every interruption by other boards. -/
namespace GenLimit.KleinbergWei.Banach.TileGenerator
open Set Finset TowerTopology DensityMeasures DensityMeasures.FiniteRankParent LatticeTiles
open scoped Classical
noncomputable section
variable {d L R : ℕ} {C : LanguageFamily} (hr : FiniteRankAtMost (FamilySpace C) R)
  (e : ℕ → Lattice d) (inj : Function.Injective e)

def bin (k : Lattice d) : Finset ℕ := (cell L k).preimage e inj.injOn

def board (k : Lattice d) (v : FamilyPoint C) (i : ℕ) :=
  ForestMatching.layer hr (bin (L := L) e inj k) v i

theorem board_mem {k v i x} (h : x ∈ board (L := L) hr e inj k v i) : e x ∈ cell L k := by
  have mem := (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).1
  exact Finset.mem_preimage.mp mem

def cells : ForestGames.Cells (Lattice d) := ⟨number L ∘ e,bin (L:=L) e inj⟩

theorem exact_bins (pos : 0 < L) {k x} :
    x ∈ (cells (L:=L) e inj).bin k ↔ (cells (L:=L) e inj).address x = k :=
  by simp [cells,bin,cell_iff pos]

def game (q : ℝ) : ForestGames.Game (Lattice d) where
  move k D h x :=
    let E := tests (L:=L) e k D
    FiniteGame.recommend E (fun _ => 1) q (FiniteGame.run E (fun _ => 1) q D h) x
  legal := by
    intro k D h x y hit
    have active := FiniteGame.active_input _ _ _ hit
    obtain ⟨inside,fresh,different⟩ := FiniteGame.recommendation_fresh _ _ _ hit
    exact ⟨active,inside,by simp [fresh,different]⟩

def plan (q : ℝ) := ForestGames.plan hr (cells (L:=L) e inj) (game (L:=L) e q)
def fallback := ForestGames.fallback
def rule (q : ℝ) (inf : ∀ z, (C z).Infinite) :=
  ForestGames.rule hr (cells (L:=L) e inj) (game (L:=L) e q) inf

theorem validity (q : ℝ) (inf : ∀ z, (C z).Infinite) {z s} (pres : Presents s (C z)) :
    OrderedFocus.ElementValid s (OrderedFocus.play (rule (L:=L) hr e inj q inf) s) (C z) :=
  ForestGames.validity hr _ _ inf pres

theorem layer_count (pos : 0 < L) {q : ℝ} (hq : 0 < q) (h1 : q ≤ 1/2)
    (inf : ∀ z, (C z).Infinite) {z s} (pres : Presents s (C z)) (k l u : Lattice d)
    (meet : k ∈ indices L l u) (i : ℕ) (hi : i < R)
    (subset : ∀ x ∈ board (L:=L) hr e inj k (TileSeed.seed (number L ∘ e) C s k) i, x ∈ C z) :
    let D := board (L:=L) hr e inj k (TileSeed.seed (number L ∘ e) C s k) i
    let X := D.filter (fun x => e x ∈ Finset.Icc l u)
    let O := range (OrderedFocus.play (rule (L:=L) hr e inj q inf) s)
    (1/2-q)*(X.card:ℝ)-loss d L q ≤ (X.filter (· ∈ O)).card :=
  local_bound pos e meet _ (fun _ h => board_mem hr e inj h) hq h1 s
    (fun x hx => pres.symm ▸ subset x hx) _ _ (fun h => inf (indexHistoryRule C h))
    (ForestGames.routes hr (cells (L:=L) e inj) (game (L:=L) e q)
      (fun hx => (exact_bins e inj pos).mp hx) s k hi)

end
end GenLimit.KleinbergWei.Banach.TileGenerator
