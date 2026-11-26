import GenLimit.Paper23_BanachDensityTopologyAndGeometry.TileSeed
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.LocalReplies

/-! Run finite response games independently on the ancestor layers of a spatial
partition. Each cell fixes its forest seed at its first input. -/
namespace GenLimit.KleinbergWei.Banach.ForestGames
open Set Finset TowerTopology DensityMeasures DensityMeasures.FiniteRankParent
open scoped Classical
noncomputable section

structure Cells (I : Type*) where
  address : ℕ → I
  bin : I → Finset ℕ

structure Game (I : Type*) where
  move : I → Finset ℕ → List ℕ → ℕ → Option ℕ
  legal : ∀ {k D h x y}, move k D h x = some y → x ∈ D ∧ y ∈ D ∧ y ∉ h ++ [x]

variable {I : Type*} {R : ℕ} {C : LanguageFamily}
  (hr : FiniteRankAtMost (FamilySpace C) R) (cells : Cells I) (game : Game I)

def board (k : I) (v : FamilyPoint C) (i : ℕ) :=
  ForestMatching.layer hr (cells.bin k) v i

theorem board_mem {k v i x} (h : x ∈ board hr cells k v i) : x ∈ cells.bin k :=
  (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).1

def plan (h : List ℕ) (x : ℕ) :=
  let addr := cells.address
  let k := addr x
  let v := TileSeed.atHistory addr C h x
  if ex : ∃ i < R, x ∈ board hr cells k v i then
    game.move k (board hr cells k v (Nat.find ex)) h x
  else none

def fallback (C : LanguageFamily) (h : List ℕ) := C (indexHistoryRule C h)

def rule (inf : ∀ z, (C z).Infinite) := LocalReplies.rule (plan hr cells game)
  (fallback C) (fun h => inf (indexHistoryRule C h))

theorem routes (aligned : ∀ {k x}, x ∈ cells.bin k → cells.address x = k) (s : ℕ → ℕ) (k : I) {i : ℕ} (hi : i < R)
    (t y : ℕ) (hit : game.move k (board hr cells k (TileSeed.seed cells.address C s k) i)
      (textPrefix s t) (s t) = some y) :
    plan hr cells game (textPrefix s t) (s t) = some y := by
  let v := TileSeed.seed cells.address C s k
  have hx : s t ∈ board hr cells k v i := (game.legal hit).1
  have kq := aligned (board_mem hr cells hx)
  dsimp only [plan]
  rw [TileSeed.agrees,show cells.address (s t) = k from kq]
  have ex : ∃ j < R, s t ∈ board hr cells k v j := ⟨i,hi,hx⟩
  rw [dif_pos ex,ForestMatching.unique_layer hr _ v (Nat.find_spec ex).2 hx]
  exact hit

private theorem from_plan (s : ℕ → ℕ) {t y : ℕ}
    (hit : plan hr cells game (textPrefix s t) (s t) = some y) :
    let k := cells.address (s t)
    let v := TileSeed.seed cells.address C s k
    ∃ i < R, s t ∈ board hr cells k v i ∧ y ∈ board hr cells k v i := by
  dsimp only [plan] at hit
  rw [TileSeed.agrees] at hit
  split at hit
  next ex => exact ⟨_,(Nat.find_spec ex).1,(Nat.find_spec ex).2,(game.legal hit).2.1⟩
  next => contradiction

theorem validity (inf : ∀ z, (C z).Infinite) {z s} (pres : Presents s (C z)) :
    OrderedFocus.ElementValid s (OrderedFocus.play (rule hr cells game inf) s) (C z) := by
  let A := rule hr cells game inf
  let out := OrderedFocus.play A s
  let addr := cells.address
  obtain ⟨bad,good⟩ := TileSeed.eventually_reaches addr C hr pres
  obtain ⟨T,acc⟩ := StaticForest.guesses_reach hr pres
  have dec := LocalReplies.decision (plan hr cells game) (fallback C)
    (fun h => inf (indexHistoryRule C h)) s
  have fresh (t j : ℕ) (lt : j < t) : out j ≠ out t := (dec t).2.1 j lt
  have mono : Function.Injective out := by
    intro i j eq; rcases lt_trichotomy i j with lt | eq' | gt
    · exact (fresh _ _ lt eq).elim
    · exact eq'
    · exact (fresh _ _ gt eq.symm).elim
  let mistakes := bad.biUnion cells.bin
  have eventual := mono.tendsto_cofinite.eventually (mistakes.finite_toSet.compl_mem_cofinite)
  rw [Nat.cofinite_eq_atTop] at eventual
  obtain ⟨N,far⟩ := Filter.eventually_atTop.mp eventual
  refine ⟨max T N,fun t ht => ⟨?_,?_,fresh t⟩⟩
  · rcases (dec t).2.2 with hit | backup
    · obtain ⟨i,_,hx,hy⟩ := from_plan hr cells game s hit
      have notBad : addr (s t) ∉ bad := fun hb => far t (by omega) (Finset.mem_biUnion.mpr
        ⟨_,hb,board_mem hr cells hy⟩)
      exact ForestMatching.layer_closed hr _ _ (good t notBad) hx hy (show s t ∈ C z by rw [←pres]; exact mem_range_self t)
    · change out t ∈ C (indexHistoryRule C (textPrefix s (t+1))) at backup
      rw [indexHistoryRule_prefix] at backup
      exact StaticForest.subset_of_reaches hr (acc t (by omega)).1 backup
  · intro j le eq
    exact (dec t).1 (mem_textPrefix_iff.mpr ⟨j,by omega,eq⟩)

theorem credited (aligned : ∀ {k x}, x ∈ cells.bin k → cells.address x = k)
    (inf : ∀ z, (C z).Infinite) (s : ℕ → ℕ) (k : I) {i : ℕ} (hi : i < R)
    {t y : ℕ} (hit : game.move k (board hr cells k (TileSeed.seed cells.address C s k) i)
      (textPrefix s t) (s t) = some y) :
    y ∈ range (OrderedFocus.play (rule hr cells game inf) s) :=
  LocalReplies.credited _ _ _ (routes hr cells game aligned s k hi t y hit)
    (textPrefix_succ s t ▸ (game.legal hit).2.2)

end
end GenLimit.KleinbergWei.Banach.ForestGames
