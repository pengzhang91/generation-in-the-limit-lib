import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RegionPotential

/-! Downward selection of local requirements for a finite packet of rectangle
traces, as in Appendix A.3 of arXiv:2611.14887v1. For each trace, every
point in a qualifying region belongs to its deepest qualifying region.
Cutoffs can depend on the region and the resulting bounds retain the exact
mass of discarded points. -/
namespace GenLimit.KleinbergWei.Banach.RegionGame
open Finset
open scoped Classical
noncomputable section
variable {V : Type*} [PartialOrder V] (T : Hierarchy V) (γ α : V → ℝ)

def Hierarchy.eligible (X : Finset ℕ) (v : V) : Prop := γ v ≤ (X ∩ T.region v).card

def Hierarchy.remainder (X : Finset ℕ) (v : V) : Finset ℕ :=
  (X ∩ T.region v).filter fun x => T.eligible γ X v ∧
    ∀ u, v < u → x ∈ T.region u → ¬ T.eligible γ X u

private theorem mem_remainder {X : Finset ℕ} {v : V} {x : ℕ} :
    x ∈ T.remainder γ X v ↔ x ∈ X ∩ T.region v ∧ T.eligible γ X v ∧
    ∀ u, v < u → x ∈ T.region u → ¬ T.eligible γ X u := Finset.mem_filter

private theorem remainder_sub (X : Finset ℕ) (v : V) : T.remainder γ X v ⊆ X :=
  (Finset.filter_subset ..).trans Finset.inter_subset_left

/-- All data used to form a local requirement are inside its own region. -/
theorem remainder_clip (X : Finset ℕ) (v : V) :
    T.remainder γ (X ∩ T.region v) v = T.remainder γ X v := by
  have same {u : V} (below : v ≤ u) : (X ∩ T.region v) ∩ T.region u = X ∩ T.region u := by
    rw [Finset.inter_assoc,Finset.inter_eq_right.mpr (T.nested below)]
  have eligible {u : V} (below : v ≤ u) :
      T.eligible γ (X ∩ T.region v) u ↔ T.eligible γ X u := by
    simp only [Hierarchy.eligible,same below]
  ext x
  rw [mem_remainder,mem_remainder,same le_rfl,eligible le_rfl]
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  exact forall_congr' fun u => forall_congr' fun below => by rw [eligible below.le]

private theorem disjoint_remainders (X : Finset ℕ) {u v : V} (ne : u ≠ v) :
    Disjoint (T.remainder γ X u) (T.remainder γ X v) := by
  rw [Finset.disjoint_left]
  intro x hu hv
  obtain ⟨xu,yesu,deepu⟩ := Finset.mem_filter.mp hu
  obtain ⟨xv,yesv,deepv⟩ := Finset.mem_filter.mp hv
  have ru := (Finset.mem_inter.mp xu).2
  have rv := (Finset.mem_inter.mp xv).2
  rcases T.path ru rv with le | le
  · exact deepu v (lt_of_le_of_ne le ne) rv yesv
  · exact deepv u (lt_of_le_of_ne le ne.symm) ru yesu

/-- Equation (35). Removing all qualifying descendants bounds every
remainder's intersection with each smaller region by that region's cutoff. -/
theorem remainder_sparse (X : Finset ℕ) {v u : V} (below : v < u) (pos : 0 < γ u) :
    (((T.remainder γ X v) ∩ T.region u).card : ℝ) < γ u := by
  by_cases eligible : T.eligible γ X u
  · have empty : T.remainder γ X v ∩ T.region u = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x mem
      obtain ⟨kept,reg⟩ := Finset.mem_inter.mp mem
      exact ((mem_remainder T γ).mp kept).2.2 u below reg eligible
    simpa [empty] using pos
  · have sub : T.remainder γ X v ∩ T.region u ⊆ X ∩ T.region u :=
      Finset.inter_subset_inter (remainder_sub T γ X v) Finset.Subset.rfl
    exact (Nat.cast_le.mpr (Finset.card_le_card sub)).trans_lt (lt_of_not_ge eligible)

variable [Fintype V]

/-- Points outside every eligible region. A large rectangle that straddles
several tiles can have some points of this kind in its sparse boundary tiles. -/
def Hierarchy.uncovered (X : Finset ℕ) : Finset ℕ :=
  X.filter fun x => ¬ ∃ v, x ∈ T.region v ∧ T.eligible γ X v

private theorem covered (X : Finset ℕ) :
    X \ Finset.univ.biUnion (T.remainder γ X) = T.uncovered γ X := by
  ext x
  simp only [Finset.mem_sdiff,Finset.mem_biUnion,Finset.mem_univ,true_and,
    Hierarchy.uncovered,Finset.mem_filter]
  apply and_congr_right
  intro hx
  apply not_congr
  constructor
  · rintro ⟨v,mem⟩
    obtain ⟨both,yes,_⟩ := (mem_remainder T γ).mp mem
    exact ⟨v,(Finset.mem_inter.mp both).2,yes⟩
  · rintro ⟨v,reg,yes⟩
    let candidates := Finset.univ.filter (fun w => x ∈ T.region w ∧ T.eligible γ X w)
    have hv : v ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _,reg,yes⟩
    obtain ⟨w,mem,deep⟩ := candidates.exists_maximal ⟨_,hv⟩
    obtain ⟨rw,good⟩ := (Finset.mem_filter.mp mem).2
    exact ⟨w,(mem_remainder T γ).mpr ⟨Finset.mem_inter.mpr ⟨hx,rw⟩,good,
      fun u lt ru gu => lt.not_ge (deep (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ru,gu⟩) lt.le)⟩⟩

def Hierarchy.discard (X : Finset ℕ) (v : V) : ℝ :=
  if α v ≤ (T.remainder γ X v).card then 0 else (T.remainder γ X v).card

def Hierarchy.requests (packet : Finset (Finset ℕ)) (v : V) : Finset (Finset ℕ) :=
  (packet.image (fun X => T.remainder γ X v)).filter (fun Q => α v ≤ Q.card)

/-- Claim A.4 with the actual discarded and uncovered populations.
The finite strategy is shared by every trace in the packet. -/
theorem canForce_packet (packet : Finset (Finset ℕ)) {rate : ℝ}
    (localGame : ClaimGame.CanForce T.board (fun W => ∀ v, ∀ Q ∈ T.requests γ α packet v,
      rate * (Q.card : ℝ) ≤ (Q.filter (· ∈ W)).card)) :
    ClaimGame.CanForce T.board (fun W => ∀ X ∈ packet,
      rate * ((X.card:ℝ) - (T.uncovered γ X).card - ∑ v, T.discard γ α X v) ≤
        (X.filter (· ∈ W)).card) := by
  obtain ⟨move,safe,wins⟩ := localGame
  refine ⟨move,safe,fun h play exhausted X mem => ?_⟩
  let W := BoardPermutations.earned move h
  let Q := T.remainder γ X
  let hits (v : V) := (Q v).filter (· ∈ W)
  have sub : Finset.univ.biUnion Q ⊆ X := by
    intro x hx
    obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp hx
    exact remainder_sub T γ X v hv
  have allCount := Finset.card_sdiff_add_card_eq_card sub
  rw [covered T γ X,Finset.card_biUnion (fun _ _ _ _ ne => disjoint_remainders T γ X ne)] at allCount
  have balance : ((T.uncovered γ X).card : ℝ) + ∑ v, ((Q v).card:ℝ) = X.card := by
    exact_mod_cast allCount
  have subHits : Finset.univ.biUnion hits ⊆ X.filter (· ∈ W) := by
    intro x hx
    obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨inQ,hit⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨remainder_sub T γ X v inQ,hit⟩
  have totalHits := Finset.card_le_card subHits
  rw [Finset.card_biUnion (fun _ _ _ _ ne =>
    (disjoint_remainders T γ X ne).mono (Finset.filter_subset ..) (Finset.filter_subset ..))] at totalHits
  have cap : ∑ v, ((hits v).card:ℝ) ≤ (X.filter (· ∈ W)).card := by exact_mod_cast totalHits
  have each (v : V) : rate * ((Q v).card:ℝ) ≤ (hits v).card + rate * T.discard γ α X v := by
    by_cases keep : α v ≤ (T.remainder γ X v).card
    · have req : Q v ∈ T.requests γ α packet v := Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem _ mem,keep⟩
      simpa only [Hierarchy.discard,if_pos keep,mul_zero,add_zero] using wins h play exhausted v (Q v) req
    · simp only [Hierarchy.discard,if_neg keep]
      linarith [Nat.cast_nonneg (α:=ℝ) (hits v).card]
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => each v)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum] at sum
  change _ ≤ ((X.filter (· ∈ W)).card : ℝ)
  rw [←balance]
  linarith

/-- Claim A.3, allowing each region to use its own size cutoffs.
Incomparable regions at one level have disjoint traces. -/
theorem discard_bound {L : Type*} [Fintype L] (level : V → L)
    (separate : ∀ v u, v < u → level v ≠ level u) (δ : L → ℝ)
    (pos : ∀ j, 0 ≤ δ j) (budget : ∀ v, α v ≤ δ (level v) * γ v) (X : Finset ℕ) :
    ∑ v, T.discard γ α X v ≤ (∑ j, δ j) * X.card := by
  let M v := X ∩ T.region v
  have per (v : V) : T.discard γ α X v ≤ δ (level v) * (M v).card := by
    have nn : 0 ≤ δ (level v) * (M v).card := mul_nonneg (pos _) (Nat.cast_nonneg _)
    unfold Hierarchy.discard
    split
    · exact nn
    next small =>
      by_cases existsPoint : (T.remainder γ X v).Nonempty
      · obtain ⟨x,hx⟩ := existsPoint
        have yes := ((mem_remainder T γ).mp hx).2.1
        exact (le_of_lt (lt_of_not_ge small)).trans ((budget _).trans (mul_le_mul_of_nonneg_left yes (pos _)))
      · simpa [Finset.not_nonempty_iff_eq_empty.mp existsPoint] using nn
  have layers (j : L) : ∑ v ∈ Finset.univ.filter (fun v => level v = j), ((M v).card:ℝ) ≤ X.card := by
    let J := Finset.univ.filter (fun v => level v = j)
    have dis : (↑J : Set V).PairwiseDisjoint M := by
      intro u hu v hv ne
      change Disjoint (M u) (M v)
      rw [Finset.disjoint_left]
      intro x xu xv
      have same := (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
      rcases T.path (Finset.mem_inter.mp xu).2 (Finset.mem_inter.mp xv).2 with le | le
      · exact separate u v (lt_of_le_of_ne le ne) same
      · exact separate v u (lt_of_le_of_ne le ne.symm) same.symm
    have sub : J.biUnion M ⊆ X := by
      intro x hx
      obtain ⟨v,_,mem⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_inter.mp mem).1
    have count := Finset.card_le_card sub
    rw [Finset.card_biUnion dis] at count
    exact_mod_cast count
  rw [←Finset.sum_fiberwise_of_maps_to (g:=level) (s:=Finset.univ) (t:=Finset.univ)
    (fun _ _ => Finset.mem_univ _) (T.discard γ α X),Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  apply le_trans _ (mul_le_mul_of_nonneg_left (layers j) (pos j))
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun v hv => by simpa only [(Finset.mem_filter.mp hv).2] using per v

/-- When a test meets several tiles at its chosen scale, only the tiles
below their own cutoff can contain an uncovered point. -/
theorem uncovered_bound (X : Finset ℕ) (tiles : Finset V) (nonneg : ∀ v ∈ tiles, 0 ≤ γ v)
    (cover : ∀ x ∈ X, ∃ v ∈ tiles, x ∈ T.region v) :
    ((T.uncovered γ X).card : ℝ) ≤ ∑ v ∈ tiles, γ v := by
  let part v := T.uncovered γ X ∩ T.region v
  have sub : T.uncovered γ X ⊆ tiles.biUnion part := by
    intro x hx
    obtain ⟨v,mem,inside⟩ := cover x (Finset.mem_filter.mp hx).1
    exact Finset.mem_biUnion.mpr ⟨v,mem,Finset.mem_inter.mpr ⟨hx,inside⟩⟩
  have total := (Finset.card_le_card sub).trans (Finset.card_biUnion_le (t:=part))
  calc
    ((T.uncovered γ X).card : ℝ) ≤ ∑ v ∈ tiles, ((part v).card:ℝ) := by exact_mod_cast total
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v mem
      by_cases yes : T.eligible γ X v
      · have empty : part v = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun x hx => by
          obtain ⟨unc,inside⟩ := Finset.mem_inter.mp hx
          exact (Finset.mem_filter.mp unc).2 ⟨v,inside,yes⟩
        simpa [empty] using nonneg v mem
      · have small : part v ⊆ X ∩ T.region v :=
          Finset.inter_subset_inter (Finset.filter_subset ..) Finset.Subset.rfl
        exact (Nat.cast_le.mpr (Finset.card_le_card small)).trans (le_of_not_ge yes)

end
end GenLimit.KleinbergWei.Banach.RegionGame
