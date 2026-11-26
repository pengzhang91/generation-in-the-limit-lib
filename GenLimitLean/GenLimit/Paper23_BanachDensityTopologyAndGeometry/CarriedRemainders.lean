import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RegionRectangles

/-! A bottom-up alternative to the local requirements in Appendix A.3 of
arXiv:2611.14887v1. A region sends its unassigned points to its ancestors
whenever it has too few to make a requirement of its own. This preserves
light intersections with descendants without summing discard losses over
all retained scales. -/
namespace GenLimit.KleinbergWei.Banach.RegionGame.CarriedRemainders
open Finset Real LogPowerCriterion BoardPermutations
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] [PartialOrder V] (T : Hierarchy V) (α : V → ℝ)

private def height (v : V) := (Finset.univ.filter (v < ·)).card

private theorem height_lt {u v : V} (below : v < u) : height u < height v := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
  · exact fun w hw => Finset.mem_filter.mpr ⟨Finset.mem_univ _,below.trans (Finset.mem_filter.mp hw).2⟩
  · intro eq
    have mem : u ∈ Finset.univ.filter (v < ·) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,below⟩
    rw [←eq] at mem
    exact (lt_irrefl u) (Finset.mem_filter.mp mem).2

/-- Assign the residual trace to this region only when it reaches the local
cutoff. Strict descendants have already made their assignments. -/
def chunk (X : Finset ℕ) (v : V) : Finset ℕ :=
  let below := Finset.univ.biUnion (fun u => if _h : v < u then chunk X u else ∅)
  let left := (X ∩ T.region v) \ below
  if α v ≤ left.card then left else ∅
termination_by height v
decreasing_by exact height_lt (by assumption)

private def freeAt (X : Finset ℕ) (v : V) : Finset ℕ :=
  (X ∩ T.region v).filter fun x => ∀ u, v < u → x ∉ chunk T α X u

private theorem chunk_eq (X : Finset ℕ) (v : V) :
    chunk T α X v = if α v ≤ (freeAt T α X v).card then freeAt T α X v else ∅ := by
  rw [chunk]
  have same : (X ∩ T.region v) \ Finset.univ.biUnion (fun u => if v < u then chunk T α X u else ∅) =
      freeAt T α X v := by
    ext x
    simp only [freeAt,Finset.mem_sdiff,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_filter]
    apply and_congr_right
    intro _
    constructor
    · intro absent u below hit
      exact absent ⟨u,by simpa [below] using hit⟩
    · rintro missing ⟨u,hit⟩
      by_cases below : v < u
      · exact missing u below (by simpa [below] using hit)
      · simp [below] at hit
  simp only [dite_eq_ite,same]

private theorem chunk_sub (X : Finset ℕ) (v : V) : chunk T α X v ⊆ freeAt T α X v := by
  rw [chunk_eq]; split <;> simp

theorem chunk_local (X : Finset ℕ) (v : V) : chunk T α X v ⊆ X ∩ T.region v :=
  (chunk_sub T α X v).trans (Finset.filter_subset ..)

theorem chunk_large {X : Finset ℕ} {v : V} (nonempty : (chunk T α X v).Nonempty) :
    α v ≤ (chunk T α X v).card := by
  rw [chunk_eq] at nonempty ⊢
  split <;> simp_all

theorem disjoint_chunks (X : Finset ℕ) {u v : V} (ne : u ≠ v) :
    Disjoint (chunk T α X u) (chunk T α X v) := by
  rw [Finset.disjoint_left]
  intro x hu hv
  obtain ⟨xu,du⟩ := Finset.mem_filter.mp (chunk_sub T α X u hu)
  obtain ⟨xv,dv⟩ := Finset.mem_filter.mp (chunk_sub T α X v hv)
  rcases T.path (Finset.mem_inter.mp xu).2 (Finset.mem_inter.mp xv).2 with le | le
  · exact du v (lt_of_le_of_ne le ne) hv
  · exact dv u (lt_of_le_of_ne le ne.symm) hu

/-- All leftovers from a subtree, after its own region got a chance to
absorb them, fit below one cutoff. -/
private theorem leftover_lt (X : Finset ℕ) (v : V) (pos : 0 < α v) :
    (((freeAt T α X v) \ chunk T α X v).card:ℝ) < α v := by
  rw [chunk_eq]; split
  · simpa using pos
  next small => simpa using lt_of_not_ge small

/-- Ancestor labels still satisfy the light-intersection requirement, with
the *same* cutoff that decides whether the descendant makes a label. -/
theorem chunk_sparse (X : Finset ℕ) {v u : V} (below : v < u) (pos : 0 < α u) :
    (((chunk T α X v) ∩ T.region u).card:ℝ) < α u := by
  apply lt_of_le_of_lt _ (leftover_lt T α X u pos)
  apply Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro x hx
  obtain ⟨inV,reg⟩ := Finset.mem_inter.mp hx
  obtain ⟨inside,absent⟩ := Finset.mem_filter.mp (chunk_sub T α X v inV)
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp inside).1,reg⟩,fun w hw => absent w (below.trans hw)⟩,
    absent u below⟩

/-- Agreement inside a region determines the assignment throughout that
region. Consequently local labels can still be counted by rectangular traces. -/
theorem chunk_congr {X Y : Finset ℕ} (v : V) (same : X ∩ T.region v = Y ∩ T.region v) :
    chunk T α X v = chunk T α Y v := by
  have freeEq : freeAt T α X v = freeAt T α Y v := by
    unfold freeAt
    rw [same]
    apply Finset.filter_congr
    intro x _
    apply forall_congr'
    intro u
    apply forall_congr'
    intro h
    have clip (Z : Finset ℕ) : (Z ∩ T.region v) ∩ T.region u = Z ∩ T.region u := by
      rw [Finset.inter_assoc,Finset.inter_eq_right.mpr (T.nested h.le)]
    have localEq : X ∩ T.region u = Y ∩ T.region u := (clip X).symm.trans ((congrArg (· ∩ T.region u) same).trans (clip Y))
    have child : chunk T α X u = chunk T α Y u := chunk_congr u localEq
    rw [child]
  rw [chunk_eq,chunk_eq,freeEq]
termination_by height v
decreasing_by exact height_lt (by assumption)

def missing (X : Finset ℕ) := X \ Finset.univ.biUnion (chunk T α X)

/-- Cover a trace by any collection of regions. The entire unassigned mass
costs at most the sum of their cutoffs, independently of the tree depth. -/
theorem missing_bound (X : Finset ℕ) (tiles : Finset V) (pos : ∀ v ∈ tiles, 0 < α v)
    (cover : ∀ x ∈ X, ∃ v ∈ tiles, x ∈ T.region v) :
    ((missing T α X).card:ℝ) ≤ ∑ v ∈ tiles, α v := by
  let rest (v : V) := freeAt T α X v \ chunk T α X v
  have sub : missing T α X ⊆ tiles.biUnion rest := by
    intro x hx
    obtain ⟨inX,unused⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨v,mem,inside⟩ := cover x inX
    have absent (u : V) : x ∉ chunk T α X u := fun h => unused (Finset.mem_biUnion.mpr ⟨u,Finset.mem_univ _,h⟩)
    exact Finset.mem_biUnion.mpr ⟨v,mem,Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_inter.mpr ⟨inX,inside⟩,fun u _ => absent u⟩,absent v⟩⟩
  have card := (Finset.card_le_card sub).trans (Finset.card_biUnion_le (t:=rest))
  apply le_trans (by exact_mod_cast card : ((missing T α X).card:ℝ) ≤ ∑ v ∈ tiles, ((rest v).card:ℝ))
  exact Finset.sum_le_sum (fun v hv => (leftover_lt T α X v (pos v hv)).le)

/-- Nonempty labels in a region for a prescribed packet of traces. -/
def requests (packet : Finset (Finset ℕ)) (v : V) :=
  (packet.image (fun X => chunk T α X v)).filter Finset.Nonempty

/-- The carried labels in a node can be counted from its own population. -/
theorem card_requests {d} (e : ℕ → Lattice d) (S : Finset (Lattice d × Lattice d)) (v : V) :
    (requests T α (S.image (boardTrace e T.board)) v).card ≤ 1+(T.board ∩ T.region v).card^(2*d) := by
  apply (Finset.card_filter_le ..).trans
  apply card_clipped_image
  intro X
  apply chunk_congr
  simp

theorem quota_sum {X : Finset ℕ} {packet : Finset (Finset ℕ)} (mem : X ∈ packet)
    (W : Set ℕ) (rate : ℝ)
    (localWin : ∀ v, ∀ Q ∈ requests T α packet v, rate*(Q.card:ℝ) ≤ (Q.filter (· ∈ W)).card) :
    rate*((X.card:ℝ)-(missing T α X).card) ≤ (X.filter (· ∈ W)).card := by
  let Q := chunk T α X
  let out (v : V) := (Q v).filter (· ∈ W)
  have bounds (v : V) : rate*((Q v).card:ℝ) ≤ ((out v).card:ℝ) := by
    by_cases nonempty : (Q v).Nonempty
    · exact localWin v _ (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ mem,nonempty⟩)
    · simp only [out,Finset.not_nonempty_iff_eq_empty.mp nonempty,Finset.card_empty,
        Nat.cast_zero,mul_zero,Finset.filter_empty,le_refl]
  have sub : Finset.univ.biUnion Q ⊆ X := by
    rintro x hx
    obtain ⟨v,_,hit⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp (chunk_local T α X v hit)).1
  have balance := Finset.card_sdiff_add_card_eq_card sub
  rw [Finset.card_biUnion (fun _ _ _ _ ne => disjoint_chunks T α X ne)] at balance
  have counts : (missing T α X).card + ∑ v, (Q v).card = X.card := balance
  have castCounts : (missing T α X).card + ∑ v, ((Q v).card:ℝ) = (X.card:ℝ) := by exact_mod_cast counts
  have included : Finset.univ.biUnion out ⊆ X.filter (· ∈ W) := by
    intro x hx
    obtain ⟨v,_,hit⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨belongs,white⟩ := Finset.mem_filter.mp hit
    exact Finset.mem_filter.mpr ⟨sub (Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,belongs⟩),white⟩
  have hits := Finset.card_le_card included
  rw [Finset.card_biUnion (fun _ _ _ _ ne => (disjoint_chunks T α X ne).mono
    (Finset.filter_subset ..) (Finset.filter_subset ..))] at hits
  rw [show (X.card:ℝ)-(missing T α X).card = ∑ v, ((Q v).card:ℝ) by linarith,Finset.mul_sum]
  exact (Finset.sum_le_sum (fun v _ => bounds v)).trans (by exact_mod_cast hits)

/-- The geometric side of the logarithmic game now has a single cost for
covering each rectangle. No hypothesis about a sum of losses over levels
is required by this allocation. -/
theorem logarithmic_packet {d} (e : ℕ → Lattice d) (S : Finset (Lattice d × Lattice d))
    {q c : ℝ} (hq : 0 < q) (small : q ≤ 1/2)
    (cover : ∀ r ∈ S, (∀ i, r.1 i < r.2 i) → ∃ tiles : Finset V,
      (∀ v ∈ tiles, 0 < α v) ∧ (∀ x ∈ boardTrace e T.board r, ∃ v ∈ tiles, x ∈ T.region v) ∧
        ∑ v ∈ tiles, α v ≤ q * (c * logSites r))
    (localGame : ClaimGame.CanForce T.board (fun W => ∀ v,
      ∀ Q ∈ requests T α (S.image (boardTrace e T.board)) v,
      (1/2-q/2)*(Q.card:ℝ) ≤ (Q.filter (· ∈ W)).card)) :
    ClaimGame.CanForce T.board (PacketQuota e q c 0 T.board S) := by
  obtain ⟨move,safe,win⟩ := localGame
  refine ⟨move,safe,fun h play done r hr wide large => ?_⟩
  let X := boardTrace e T.board r
  have enough : c*logSites r ≤ X.card := by simpa only [add_zero,rpow_one] using large
  obtain ⟨tiles,pos,covered,cost⟩ := cover r hr wide
  have unpaid := (missing_bound T α X tiles pos covered).trans
    (cost.trans (mul_le_mul_of_nonneg_left enough hq.le))
  have hits := quota_sum T α (Finset.mem_image_of_mem _ hr) (earned move h) _ (win h play done)
  change (1/2-q/2)*((X.card:ℝ)-(missing T α X).card) ≤ ((X.filter (· ∈ earned move h)).card:ℝ) at hits
  change (1/2-q)*(X.card:ℝ) ≤ ((X.filter (· ∈ earned move h)).card:ℝ)
  have raw := (mul_le_mul_of_nonneg_left (sub_le_sub_left unpaid (X.card:ℝ))
    (show (0:ℝ) ≤ 1/2-q/2 by linarith)).trans hits
  nlinarith only [raw,mul_nonneg (sq_nonneg q) (Nat.cast_nonneg (α:=ℝ) X.card)]

end
end GenLimit.KleinbergWei.Banach.RegionGame.CarriedRemainders
