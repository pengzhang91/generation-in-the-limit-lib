import GenLimit.Paper23_BanachDensityTopologyAndGeometry.BoardPermutations
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.AdjacentMatching

/-! Exact half for supports carried by ordered chains with at most
logarithmically many chains crossing each rectangle. The number of chains
in the support and the gaps along them can both be unbounded. -/
namespace GenLimit.KleinbergWei.Banach.ChainRows
open BoardPermutations Finset Real Set Filter
open scoped Classical ENNReal
noncomputable section

private def fibre (row : ℕ → ℕ) (D : Finset ℕ) (k : ℕ) := D.filter (fun x => row x = k)

private def play (row : ℕ → ℕ) (D : Finset ℕ) (h : List ℕ) (x : ℕ) : Option ℕ :=
  (AdjacentMatching.mate (fibre row D (row x)) x).filter (fun y => decide (y ∉ h))

private theorem legal (row : ℕ → ℕ) (D : Finset ℕ) : Legal D (play row D) := by
  intro h x y hit
  obtain ⟨pair,fresh⟩ : AdjacentMatching.mate (fibre row D (row x)) x = some y ∧ y ∉ h := by
    simpa [play,Option.filter_eq_some_iff] using hit
  obtain ⟨xin,yin⟩ := AdjacentMatching.mem_of_mate pair
  exact ⟨(mem_filter.mp xin).1,(mem_filter.mp yin).1,
    by simpa only [List.mem_append,List.mem_singleton,not_or] using
      And.intro fresh (AdjacentMatching.mate_spec pair).1.symm⟩

private theorem covered {row D k x y} (pair : AdjacentMatching.mate (fibre row D k) x = some y)
    (h : List ℕ) (seen : x ∈ h ∨ y ∈ h) : x ∈ earned (play row D) h ∨ y ∈ earned (play row D) h := by
  obtain ⟨xin,yin⟩ := AdjacentMatching.mem_of_mate pair
  have xr := (mem_filter.mp xin).2
  have yr := (mem_filter.mp yin).2
  have flip := (AdjacentMatching.mate_spec pair).2
  induction h using List.reverseRecOn with
  | nil => simp at seen
  | append_singleton h z ih =>
    by_cases old : x ∈ h ∨ y ∈ h
    · exact (ih old).imp (fun m => earned_mono _ (List.prefix_append ..) m)
        (fun m => earned_mono _ (List.prefix_append ..) m)
    · push_neg at old
      simp only [List.mem_append,List.mem_singleton,old.1,old.2,false_or] at seen
      rcases seen with rfl | rfl
      · exact Or.inr (earned_push.mpr (.inr (by simp [play,xr,pair,old.2])))
      · exact Or.inl (earned_push.mpr (.inr (by simp [play,yr,flip,old.1])))

/-- Natural indices within each row follow the lattice product order. -/
def Ordered {d} (e : ℕ → Lattice d) (row : ℕ → ℕ) : Prop :=
  ∀ ⦃x y : ℕ⦄, row x = row y → x ≤ y → e x ≤ e y

def OrderedOn {d} (e : ℕ → Lattice d) (row : ℕ → ℕ) (D : Finset ℕ) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, row x = row y → x ≤ y → e x ≤ e y

private theorem interval {d} {e : ℕ → Lattice d} {row : ℕ → ℕ}
    (D : Finset ℕ) (ordered : OrderedOn e row D) (k : ℕ) (l u : Lattice d) :
    ∃ a b, (fibre row D k).filter (fun x => e x ∈ Finset.Icc l u) =
      fibre row D k ∩ Finset.Ico a b := by
  let T := (fibre row D k).filter (fun x => e x ∈ Finset.Icc l u)
  by_cases ne : T.Nonempty
  · refine ⟨T.min' ne,T.max' ne + 1,Finset.ext fun x => ?_⟩
    have lo := Finset.mem_filter.mp (T.min'_mem ne)
    have hi := Finset.mem_filter.mp (T.max'_mem ne)
    constructor
    · intro m
      exact mem_inter.mpr ⟨(mem_filter.mp m).1,mem_Ico.mpr ⟨T.min'_le _ m,Nat.lt_succ_of_le (T.le_max' _ m)⟩⟩
    · intro m
      obtain ⟨onRow,bounds⟩ := mem_inter.mp m
      obtain ⟨left,right⟩ := mem_Ico.mp bounds
      obtain ⟨dx,loc⟩ := mem_filter.mp onRow
      obtain ⟨dl,rl⟩ := mem_filter.mp lo.1
      obtain ⟨dr,rr⟩ := mem_filter.mp hi.1
      exact mem_filter.mpr ⟨onRow,mem_Icc.mpr
        ⟨(mem_Icc.mp lo.2).1.trans (ordered _ dl x dx (rl.trans loc.symm) left),
         (ordered x dx _ dr (loc.trans rr.symm) (Nat.le_of_lt_succ right)).trans (mem_Icc.mp hi.2).2⟩⟩
  · exact ⟨0,0,by simpa [T] using Finset.not_nonempty_iff_eq_empty.mp ne⟩

/-- Pair adjacent board points on each row. The terminal deficit in any
rectangle is at most one point per represented row, regardless of row spacing. -/
theorem rectangle_count {d} (e : ℕ → Lattice d) (row : ℕ → ℕ) (D : Finset ℕ)
    (ordered : OrderedOn e row D) : ∃ move : Move, Legal D move ∧ ∀ h : List ℕ, D ⊆ h.toFinset →
      ∀ l u : Lattice d, let T := D.filter (fun x => e x ∈ Finset.Icc l u)
        T.card ≤ 2 * (T.filter (· ∈ earned move h)).card + 2 * (T.image row).card := by
  refine ⟨play row D,fun hit => legal row D hit,fun h full l u => ?_⟩
  let T := D.filter (fun x => e x ∈ Finset.Icc l u)
  let W := earned (play row D) h
  let G := T.filter (· ∈ W)
  let J := T.image row
  have mem (x) (hx : x ∈ T) : row x ∈ J := Finset.mem_image_of_mem row hx
  have localCount (k) (_ : k ∈ J) :
      (T.filter (fun x => row x=k)).card ≤ 2*(G.filter (fun x => row x=k)).card+2 := by
    obtain ⟨a,b,r⟩ := interval D ordered k l u
    have hit := AdjacentMatching.interval_count (fibre row D k) W a b
      (fun x _ p => covered p h (Or.inl (List.mem_toFinset.mp
        (full (mem_filter.mp (AdjacentMatching.mem_of_mate p).1).1))))
    have eq : T.filter (fun x => row x=k) = fibre row D k ∩ Finset.Ico a b := by
      rw [←r]; ext x; simp [T,fibre]; tauto
    have eqG : G.filter (fun x => row x=k) = (T.filter (fun x => row x=k)).filter (· ∈ W) := by
      ext x; simp [G]; tauto
    rwa [eqG,eq]
  have total := Finset.card_eq_sum_card_fiberwise mem
  have wins := Finset.card_eq_sum_card_fiberwise (fun x (hx : x ∈ G) => mem x (mem_filter.mp hx).1)
  change T.card ≤ 2*G.card+2*J.card
  rw [total,wins]
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,
    Nat.cast_id,Nat.mul_comm J.card 2] using Finset.sum_le_sum localCount

/-- Uniform bound on the number of represented rows in a positive-width rectangle. -/
def LogarithmicallyManyRows {d} (e : ℕ → Lattice d) (row : ℕ → ℕ) : Prop :=
  ∃ b : ℝ, 0 ≤ b ∧ ∀ (D : Finset ℕ) (l u : Lattice d), (∀ i, l i < u i) →
    (((D.filter (fun x => e x ∈ Finset.Icc l u)).image row).card:ℝ) ≤
      b * (1+log (geometricVolume l u))

/-- A row partition may be chosen separately on each finite subboard of K.
The coefficient is uniform on that target. -/
def RowCover {d} (e : ℕ → Lattice d) (K : Set ℕ) : Prop :=
  ∃ b : ℝ, 0 ≤ b ∧ ∀ (D : Finset ℕ), (D : Set ℕ) ⊆ K → ∃ row : ℕ → ℕ, OrderedOn e row D ∧
    ∀ (l u : Lattice d), (∀ i, l i < u i) →
      (((D.filter (fun x => e x ∈ Finset.Icc l u)).image row).card:ℝ) ≤ b*(1+log (geometricVolume l u))

private theorem finite_on {d} {e : ℕ → Lattice d} {K : Set ℕ} (cover : RowCover e K) :
    FiniteRectangleResponseOn e 0 K := by
  obtain ⟨b,bn,boards⟩ := cover
  refine ⟨b,bn,fun D sub => (board_response_iff ..).mpr ?_⟩
  obtain ⟨row,ordered,bound⟩ := boards D sub
  obtain ⟨move,safe,count⟩ := rectangle_count e row D ordered
  refine ⟨move,safe,fun h _ full l u wide => ?_⟩
  let T := D.filter (fun x => e x ∈ Finset.Icc l u)
  have hits : (T.card:ℝ) ≤ 2*(T.filter (· ∈ earned move h)).card + 2*(T.image row).card := by
    exact_mod_cast count h full.ge l u
  have rows := bound l u wide
  change ((T.image row).card:ℝ) ≤ _ at rows
  change (1/2-0)*(T.card:ℝ)-_ ≤ ((T.filter (· ∈ earned move h)).card:ℝ)
  linarith

/-- One generator works even if qualifying targets use different row
partitions and bounds and the other members of the family have neither. -/
theorem exact_half_on_supported_targets {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    (C : LanguageFamily) (inf : ∀ z, (C z).Infinite) {R : ℕ}
    (rank : TowerTopology.FiniteRankAtMost (range C) R) (f : ℕ → ℝ) (grows : Tendsto f atTop atTop) :
    ∃ A : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), range s = e '' C z →
      cubeValid A s (e '' C z) ∧ (RowCover e (C z) →
        ENNReal.ofReal (1/2) ≤ filteredRectangularDensity f (range (cubePlay A s)) (e '' C z)) := by
  obtain ⟨A,works⟩ := filtered_generation_on_supported_targets e inj (show (0:ℝ) ≤ 0 from le_rfl)
    f grows C inf rank
  refine ⟨A,fun z s pres => ?_⟩
  obtain ⟨valid,dense⟩ := works z s pres
  exact ⟨valid,fun cert => by simpa only [sub_zero] using dense (finite_on cert)⟩

theorem exact_half {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    (row : ℕ → ℕ) (ordered : Ordered e row) (few : LogarithmicallyManyRows e row)
    (C : LanguageFamily) (inf : ∀ z, (C z).Infinite) {R : ℕ}
    (rank : TowerTopology.FiniteRankAtMost (range C) R) (f : ℕ → ℝ) (grows : Tendsto f atTop atTop) :
    ∃ A : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), range s = e '' C z →
      cubeValid A s (e '' C z) ∧
      ENNReal.ofReal (1/2) ≤ filteredRectangularDensity f (range (cubePlay A s)) (e '' C z) := by
  obtain ⟨b,bn,bound⟩ := few
  obtain ⟨A,works⟩ := exact_half_on_supported_targets e inj C inf rank f grows
  refine ⟨A,fun z s pres => ?_⟩
  obtain ⟨valid,dense⟩ := works z s pres
  exact ⟨valid,dense ⟨b,bn,fun D _ => ⟨row,fun _ _ _ _ same le => ordered same le,bound D⟩⟩⟩

end
end GenLimit.KleinbergWei.Banach.ChainRows
