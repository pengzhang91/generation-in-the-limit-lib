import GenLimit.Paper23_BanachDensityTopologyAndGeometry.ForestCounts
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.ShellDensity
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.VolumeError

/-! A sufficient finite game for the unrestricted filtered generation theorem.
The game has a known finite target, one causal reply per input, and terminal
counts tested on rectangles. Its loss uses the query's geometric volume. -/
namespace GenLimit.KleinbergWei.Banach
open Set Filter Finset Real DensityMeasures
open scoped Classical ENNReal
noncomputable section

/-- The terminal guarantee only inspects a finite prefix, which can include
repeated words and visits outside the board. -/
def BoardEstimate {d} (e : ℕ → Lattice d) (q b : ℝ) (D : Finset ℕ)
    (move : List ℕ → ℕ → Option ℕ) : Prop :=
  ∀ (s : ℕ → ℕ) n, D ⊆ (textPrefix s n).toFinset → ∀ l u : Lattice d,
    (∀ i, l i < u i) →
    let X := D.filter (fun x => e x ∈ Finset.Icc l u)
    (1/2-q)*(X.card:ℝ) - b*(1+log (geometricVolume l u)) ≤
      (X.filter (fun y => ∃ t < n, move (textPrefix s t) (s t) = some y)).card

def BoardResponse {d} (e : ℕ → Lattice d) (q b : ℝ) (D : Finset ℕ) : Prop :=
  ∃ move : List ℕ → ℕ → Option ℕ,
    (∀ {h x y}, move h x = some y → x ∈ D ∧ y ∈ D ∧ y ∉ h ++ [x]) ∧ BoardEstimate e q b D move

/-- The strategy for a finite board is chosen before any inputs. The constant
is shared by all boards. -/
def FiniteRectangleResponse {d} (e : ℕ → Lattice d) (q : ℝ) : Prop :=
  ∃ b : ℝ, 0 ≤ b ∧ ∀ D : Finset ℕ, BoardResponse e q b D

/-- One constant for all finite subboards of a single target. Other targets
can have different constants and can be supported on different geometries. -/
def FiniteRectangleResponseOn {d} (e : ℕ → Lattice d) (q : ℝ) (K : Set ℕ) : Prop :=
  ∃ b : ℝ, 0 ≤ b ∧ ∀ D : Finset ℕ, (D : Set ℕ) ⊆ K → BoardResponse e q b D

private theorem positive_volume {d} {l u : Lattice d} (wide : ∀ i, l i < u i) :
    0 < geometricVolume l u :=
  Finset.prod_pos (fun i _ => by have := wide i; omega)

private theorem enlarge_estimate {d} {e : ℕ → Lattice d} {q b c D move} (le : b ≤ c)
    (small : BoardEstimate e q b D move) : BoardEstimate e q c D move := by
  intro s n covered l u wide
  have nonneg := Real.log_nonneg (show (1:ℝ) ≤ geometricVolume l u by exact_mod_cast positive_volume wide)
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_right le (by linarith : 0 ≤ 1+log (geometricVolume l u))) _).trans
    (small s n covered l u wide)

private theorem some_integer_estimate {d} (e : ℕ → Lattice d) {q : ℝ} (hq : 0 ≤ q) (D : Finset ℕ) :
    ∃ n : ℕ, BoardResponse e q n D := by
  refine ⟨D.card,fun _ _ => none,by simp,fun _ _ _ l u wide => ?_⟩
  let X := D.filter (fun x => e x ∈ Finset.Icc l u)
  have vp := positive_volume wide
  have lognonneg := Real.log_nonneg (show (1:ℝ) ≤ geometricVolume l u by exact_mod_cast vp)
  have small : (X.card:ℝ) ≤ D.card := by exact_mod_cast (Finset.card_filter_le .. : X.card ≤ D.card)
  change (1/2-q)*(X.card:ℝ) - D.card*(1+log (geometricVolume l u)) ≤ _
  exact (show (1/2-q)*(X.card:ℝ) - D.card*(1+log (geometricVolume l u)) ≤ 0 by
    nlinarith [mul_nonneg hq (Nat.cast_nonneg (α:=ℝ) X.card),
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) D.card) lognonneg]).trans (Nat.cast_nonneg _)

private def shellCells {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    (f : ℕ → ℝ) (grows : Tendsto f atTop atTop) : ForestGames.Cells ℕ where
  address x := FilterShells.index f grows (FilterShells.radius (e x))
  bin k := (FilterShells.region f grows d k).preimage e inj.injOn

/-- Assemble the counts earned by arbitrary finite-board moves. The loss can
depend on the query. The generator and its finite startup cost are chosen
before the query or its loss is specified. -/
theorem cell_counts_of_board_moves {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    {q : ℝ} (hq : 0 ≤ q) (cells : ForestGames.Cells ℕ)
    (exactBins : ∀ {k x}, x ∈ cells.bin k ↔ cells.address x = k)
    (C : LanguageFamily) (inf : ∀ z, (C z).Infinite) {R : ℕ}
    (rank : TowerTopology.FiniteRankAtMost (range C) R)
    (move : Finset ℕ → List ℕ → ℕ → Option ℕ)
    (legal : ∀ D, ∀ {h x y}, move D h x = some y → x ∈ D ∧ y ∈ D ∧ y ∉ h ++ [x]) :
    ∃ A : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), range s = e '' C z →
      cubeValid A s (e '' C z) ∧ ∃ H : ℕ, ∀ (l u : Lattice d) (J : Finset ℕ),
      (∀ x, e x ∈ Finset.Icc l u → cells.address x ∈ J) →
      ∀ loss : ℕ → ℝ, (∀ k, 0 ≤ loss k) →
      (∀ k ∈ J, ∀ D : Finset ℕ, D ⊆ cells.bin k → (D : Set ℕ) ⊆ C z → ∀ (t : ℕ → ℕ) n, D ⊆ (textPrefix t n).toFinset →
        let X := D.filter (fun x => e x ∈ Finset.Icc l u)
        (1/2-q)*(X.card:ℝ)-loss k ≤
          (X.filter (fun y => ∃ j < n, move D (textPrefix t j) (t j) = some y)).card) →
      (1/2-q)*((Rectangles.box (e '' C z) l u).card:ℝ) ≤
        (Rectangles.box (range (cubePlay A s) ∩ (e '' C z)) l u).card + (∑ k ∈ J, R*loss k)+H := by
  let game : ForestGames.Game ℕ := ⟨fun _ D => move D,fun {k D h x y} hit => legal D hit⟩
  let G := ForestGames.rule rank cells game inf
  refine ⟨LatticeTransport.lift e G,fun z s pres => ?_⟩
  let t := Function.invFun e ∘ s
  let O := range (OrderedFocus.play G t)
  obtain ⟨full,outputs,carries⟩ := LatticeTransport.run e inj pres G
  obtain ⟨H,est⟩ := ForestGames.global_count_with_cell_losses rank cells exactBins O hq full
  refine ⟨carries (ForestGames.validity rank cells game inf full),H,?_⟩
  intro l u J cover loss nn counts
  let Q := (Finset.Icc l u).preimage e inj.injOn
  have localBound (k : ℕ) (hk : k ∈ J) : ForestGames.LayerCount rank cells O Q q (loss k) k
      (TileSeed.seed cells.address C t k) (C z) := by
    intro i hi sub
    let D := ForestGames.board rank cells k (TileSeed.seed cells.address C t k) i
    obtain ⟨n,covered⟩ := FiniteGame.prefix_covers (D:=D) (s:=t)
      (fun x hx => full.symm ▸ sub x hx)
    have bound := counts k hk D (fun _ hx => ForestGames.board_mem rank cells hx) (fun x hx => sub x hx) t n covered
    let X := D.filter (fun x => e x ∈ Finset.Icc l u)
    have incl : X.filter (fun y => ∃ j < n, move D (textPrefix t j) (t j) = some y) ⊆
        X.filter (· ∈ O) := by
      intro y hy
      obtain ⟨mem,j,_,hit⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨mem,ForestGames.credited rank cells game (fun hx => exactBins.mp hx) inf t k hi hit⟩
    have same : D.filter (· ∈ Q) = X := by ext x; simp [X,Q]
    change (1/2-q)*((D.filter (· ∈ Q)).card:ℝ)-loss k ≤ ((D.filter (· ∈ Q)).filter (· ∈ O)).card
    rw [same]
    exact bound.trans (by exact_mod_cast Finset.card_le_card incl)
  have bound := est Q J loss nn (fun x hx => cover x (Finset.mem_preimage.mp hx))
    localBound
  let K := C z
  have eq : (TileGenerator.sectionWords e inj K l u).filter (· ∈ O) =
      TileGenerator.sectionWords e inj (O ∩ K) l u := by
    ext; simp only [Finset.mem_filter,TileGenerator.mem_section,Set.mem_inter_iff]; tauto
  change (1/2-q)*((TileGenerator.sectionWords e inj K l u).card:ℝ) ≤
    (((TileGenerator.sectionWords e inj K l u).filter (· ∈ O)).card:ℝ) + (∑ k ∈ J, R*loss k)+H at bound
  rw [eq,section_card,section_card] at bound
  rw [outputs,←Set.image_inter inj]
  exact bound

theorem shell_counts_of_board_moves {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    {q : ℝ} (hq : 0 ≤ q) (f : ℕ → ℝ) (grows : Tendsto f atTop atTop)
    (C : LanguageFamily) (inf : ∀ z, (C z).Infinite) {R : ℕ}
    (rank : TowerTopology.FiniteRankAtMost (range C) R)
    (move : Finset ℕ → List ℕ → ℕ → Option ℕ)
    (legal : ∀ D, ∀ {h x y}, move D h x = some y → x ∈ D ∧ y ∈ D ∧ y ∉ h ++ [x]) :
    ∃ A : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), range s = e '' C z →
      cubeValid A s (e '' C z) ∧ ∃ H : ℕ, ∀ (l u : Lattice d) (J : Finset ℕ),
      (∀ x ∈ Finset.Icc l u, FilterShells.index f grows (FilterShells.radius x) ∈ J) →
      ∀ loss : ℝ, 0 ≤ loss →
      (∀ D : Finset ℕ, (D : Set ℕ) ⊆ C z → ∀ (t : ℕ → ℕ) n, D ⊆ (textPrefix t n).toFinset →
        let X := D.filter (fun x => e x ∈ Finset.Icc l u)
        (1/2-q)*(X.card:ℝ)-loss ≤
          (X.filter (fun y => ∃ j < n, move D (textPrefix t j) (t j) = some y)).card) →
      (1/2-q)*((Rectangles.box (e '' C z) l u).card:ℝ) ≤
        (Rectangles.box (range (cubePlay A s) ∩ (e '' C z)) l u).card + J.card*(R*loss)+H := by
  let cells := shellCells e inj f grows
  have exactBins {k x} : x ∈ cells.bin k ↔ cells.address x = k := by
    simp [cells,shellCells,FilterShells.mem_region]
  obtain ⟨G,works⟩ := cell_counts_of_board_moves e inj hq cells exactBins C inf rank move legal
  refine ⟨G,fun z s pres => ?_⟩
  obtain ⟨valid,H,counts⟩ := works z s pres
  refine ⟨valid,H,fun l u J cover loss nn localBound => ?_⟩
  simpa only [Finset.sum_const,nsmul_eq_mul] using counts l u J
    (fun x hx => cover (e x) hx) (fun _ => loss) (fun _ => nn) (fun _ _ D _ => localBound D)

/-- One generator is valid on the entire finite-rank family and attains the
requested density on every member admitting its own subboard estimate.
Neither the target, its constant nor its strategies are given to the generator. -/
theorem filtered_generation_on_supported_targets {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    {q : ℝ} (hq : 0 ≤ q)
    (f : ℕ → ℝ) (grows : Tendsto f atTop atTop) (C : LanguageFamily)
    (inf : ∀ z, (C z).Infinite) {R : ℕ} (rank : TowerTopology.FiniteRankAtMost (range C) R) :
    ∃ A : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), range s = e '' C z →
      cubeValid A s (e '' C z) ∧
      (FiniteRectangleResponseOn e q (C z) →
        ENNReal.ofReal (1/2-q) ≤ filteredRectangularDensity f (range (cubePlay A s)) (e '' C z)) := by
  let best (D : Finset ℕ) := Nat.find (some_integer_estimate e hq D)
  have attain (D : Finset ℕ) : BoardResponse e q (best D) D := Nat.find_spec (some_integer_estimate e hq D)
  choose move legal terminal using attain
  obtain ⟨A,works⟩ := shell_counts_of_board_moves e inj hq f grows C inf rank move legal
  refine ⟨A,fun z s pres => ?_⟩
  obtain ⟨valid,H,counts⟩ := works z s pres
  refine ⟨valid,?_⟩
  rintro ⟨c,_,boards⟩
  let b : ℝ := (⌈c⌉₊ : ℕ)
  have nn : 0 ≤ b := Nat.cast_nonneg _
  apply FilterShells.density_of_shell_counts _ _ f grows _ ((R:ℝ)*b) H (by positivity) (by positivity)
  intro l u J cover widths
  let loss := b*(1+log (geometricVolume l u))
  have lp : 0 ≤ log (geometricVolume l u) := Real.log_nonneg (by exact_mod_cast positive_volume widths)
  have bound := counts l u J cover loss (mul_nonneg nn (by linarith)) (by
    intro D sub t n covered
    obtain ⟨other,safe,estimate⟩ := boards D sub
    have fits : BoardResponse e q (⌈c⌉₊:ℕ) D := ⟨other,safe,enlarge_estimate (Nat.le_ceil c) estimate⟩
    have least : (best D:ℝ) ≤ b := Nat.cast_le.mpr (Nat.find_min' (some_integer_estimate e hq D) fits)
    exact enlarge_estimate least (terminal D) t n covered l u widths)
  dsimp only [loss] at bound
  linarith only [bound,show (J.card:ℝ)*(R*(b*(1+log (geometricVolume l u)))) =
    J.card*(R*b)*(1+log (geometricVolume l u)) by ring]

theorem filtered_generation_of_finite_response_nonneg {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    {q : ℝ} (hq : 0 ≤ q) (finite : FiniteRectangleResponse e q)
    (f : ℕ → ℝ) (grows : Tendsto f atTop atTop) (C : LanguageFamily)
    (inf : ∀ z, (C z).Infinite) {R : ℕ} (rank : TowerTopology.FiniteRankAtMost (range C) R) :
    ∃ A : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), range s = e '' C z →
      cubeValid A s (e '' C z) ∧
      ENNReal.ofReal (1/2-q) ≤ filteredRectangularDensity f (range (cubePlay A s)) (e '' C z) := by
  obtain ⟨b,nn,boards⟩ := finite
  obtain ⟨A,works⟩ := filtered_generation_on_supported_targets e inj hq f grows C inf rank
  refine ⟨A,fun z s pres => ?_⟩
  obtain ⟨valid,dense⟩ := works z s pres
  exact ⟨valid,dense ⟨b,nn,fun D _ => boards D⟩⟩

theorem filtered_generation_of_finite_response {d} (e : ℕ → Lattice d) (inj : Function.Injective e)
    {q : ℝ} (hq : 0 < q) (finite : FiniteRectangleResponse e q)
    (f : ℕ → ℝ) (grows : Tendsto f atTop atTop) (C : LanguageFamily)
    (inf : ∀ z, (C z).Infinite) {R : ℕ} (rank : TowerTopology.FiniteRankAtMost (range C) R) :
    ∃ A : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), range s = e '' C z →
      cubeValid A s (e '' C z) ∧
      ENNReal.ofReal (1/2-q) ≤ filteredRectangularDensity f (range (cubePlay A s)) (e '' C z) :=
  filtered_generation_of_finite_response_nonneg e inj hq.le finite f grows C inf rank

end
end GenLimit.KleinbergWei.Banach
