import GenLimit.Paper23_BanachDensityTopologyAndGeometry.StaticRankForest
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.AdjacentMatching

/-! Freeze a matching in a finite bin using the forest vertex identified
at its first visit. Pair the seed language in increasing order, then pair
the additional words of each successive ancestor separately. Every
ancestor inherits the entire earlier matching. In particular, when the
true target is an ancestor, all mates of its words stay in the target,
and at most two interval endpoints per forest level are lost. -/
namespace GenLimit.KleinbergWei.Banach.ForestMatching
open Set TowerTopology DensityMeasures.FiniteRankParent StaticForest
open scoped Classical
noncomputable section
variable {C : LanguageFamily} {R : ℕ} (hr : FiniteRankAtMost (FamilySpace C) R)
    (B : Finset ℕ) (v : FamilyPoint C)

def visible : ℕ → Finset ℕ
  | 0 => ∅
  | i+1 => B.filter (· ∈ ((parent hr)^[i] v).val)

theorem visible_mono : Monotone (visible hr B v) := by
  apply monotone_nat_of_le_succ
  intro i
  cases i with
  | zero => exact Finset.empty_subset _
  | succ i =>
    intro x hx
    obtain ⟨inB,inside⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr; refine ⟨inB,?_⟩
    rw [Function.iterate_succ_apply']; exact sub_parent hr _ inside

def layer (i : ℕ) := visible hr B v (i+1) \ visible hr B v i

theorem unique_layer {x i j : ℕ} (hi : x ∈ layer hr B v i) (hj : x ∈ layer hr B v j) : i=j := by
  obtain ⟨ai,bi⟩ := Finset.mem_sdiff.mp hi; obtain ⟨aj,bj⟩ := Finset.mem_sdiff.mp hj
  rcases lt_trichotomy i j with h | eq | h
  · exact (bj (visible_mono hr B v (show i+1 ≤ j from h) ai)).elim
  · exact eq
  · exact (bi (visible_mono hr B v (show j+1 ≤ i from h) aj)).elim

def mate (x : ℕ) : Option ℕ :=
  if h : ∃ i < R, x ∈ layer hr B v i then AdjacentMatching.mate (layer hr B v (Nat.find h)) x else none

private theorem on_layer {x i : ℕ} (hi : i < R) (hx : x ∈ layer hr B v i) :
    mate hr B v x = AdjacentMatching.mate (layer hr B v i) x := by
  have ex : ∃ i < R, x ∈ layer hr B v i := ⟨i,hi,hx⟩
  rw [mate,dif_pos ex,unique_layer hr B v (Nat.find_spec ex).2 hx]

/-- A point and every other word in its layer lie on the same side of
each ancestor in the chain from the seed to the true target. -/
theorem layer_closed {K : FamilyPoint C} (reach : Reaches hr v K) {x y i : ℕ}
    (hx : x ∈ layer hr B v i) (hy : y ∈ layer hr B v i) (inK : x ∈ K.val) : y ∈ K.val := by
  obtain ⟨m,_,atK⟩ := bounded_path hr reach
  obtain ⟨a,b⟩ := Finset.mem_sdiff.mp hx
  have hB := (Finset.mem_filter.mp a).1
  have seen : x ∈ visible hr B v (m+1) := Finset.mem_filter.mpr ⟨hB,atK.symm ▸ inK⟩
  have le : i ≤ m := le_of_not_gt fun gt => b (visible_mono hr B v (show m+1 ≤ i from gt) seen)
  have mem := visible_mono hr B v (Nat.succ_le_succ le) (Finset.mem_sdiff.mp hy).1
  exact atK ▸ (Finset.mem_filter.mp mem).2

private theorem found {x y : ℕ} (h : mate hr B v x = some y) :
    ∃ i < R, x ∈ layer hr B v i ∧ y ∈ layer hr B v i ∧
      AdjacentMatching.mate (layer hr B v i) x=some y := by
  unfold mate at h; split at h
  next ex =>
    obtain ⟨hx,hy⟩ := AdjacentMatching.mem_of_mate h
    exact ⟨_,(Nat.find_spec ex).1,hx,hy,h⟩
  next => contradiction

theorem mate_spec {x y : ℕ} (h : mate hr B v x = some y) :
    x ≠ y ∧ y ∈ B ∧ mate hr B v y = some x := by
  obtain ⟨i,lt,_,hy,hit⟩ := found hr B v h
  obtain ⟨ne,back⟩ := AdjacentMatching.mate_spec hit
  exact ⟨ne,(Finset.mem_filter.mp (Finset.mem_sdiff.mp hy).1).1,(on_layer hr B v lt hy).trans back⟩

theorem target_closed {K : FamilyPoint C} (reach : Reaches hr v K) {x y : ℕ}
    (inK : x ∈ K.val) (h : mate hr B v x=some y) : y ∈ K.val := by
  obtain ⟨i,_,hx,hy,_⟩ := found hr B v h
  exact layer_closed hr B v reach hx hy inK

/-- A bin containing a descendant seed loses at most two points per CB
level, uniformly over every interval in that bin. -/
theorem count {K : FamilyPoint C} (reach : Reaches hr v K) (O : Set ℕ) (l u : ℕ)
    (cover : ∀ x y, x ∈ K.val → mate hr B v x=some y → x ∈ O ∨ y ∈ O) :
    ((B.filter (· ∈ K.val)) ∩ Finset.Ico l u).card ≤
      2*(((B.filter (· ∈ K.val)) ∩ Finset.Ico l u).filter (· ∈ O)).card+2*R := by
  obtain ⟨m,lt,atK⟩ := bounded_path hr reach
  let V (i : ℕ) := visible hr B v i ∩ Finset.Ico l u
  have est (n : ℕ) (hn : n ≤ m+1) :
      (V n).card ≤ 2*((V n).filter (· ∈ O)).card+2*n := by
    induction n with
    | zero => simp [V,visible]
    | succ i ih =>
      have old := ih (by omega)
      let D := layer hr B v i ∩ Finset.Ico l u
      have hit (x y) (h : AdjacentMatching.mate (layer hr B v i) x=some y) : x ∈ O ∨ y ∈ O := by
        have hx := (AdjacentMatching.mem_of_mate h).1
        have up := visible_mono hr B v hn (Finset.mem_sdiff.mp hx).1
        have inK : x ∈ K.val := atK ▸ (Finset.mem_filter.mp up).2
        exact cover x y inK ((on_layer hr B v (by omega) hx).trans h)
      have new := AdjacentMatching.interval_count (layer hr B v i) O l u hit
      change D.card ≤ 2*(D.filter (· ∈ O)).card+2 at new
      have sub : V i ⊆ V (i+1) := Finset.inter_subset_inter_right (visible_mono hr B v (Nat.le_succ i))
      have diff : V (i+1) \ V i = D := by ext x; simp only [V,D,layer,Finset.mem_inter,Finset.mem_sdiff]; tauto
      have diff' : (V (i+1)).filter (· ∈ O) \ (V i).filter (· ∈ O) = D.filter (· ∈ O) := by
        rw [←diff]; ext; simp; tauto
      have total := Finset.card_sdiff_add_card_eq_card sub
      have hits := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter (p:=(· ∈ O)) sub)
      rw [diff] at total; rw [diff'] at hits; omega
  have last := est (m+1) le_rfl
  dsimp only [V,visible] at last
  rw [atK] at last; omega

end
end GenLimit.KleinbergWei.Banach.ForestMatching
