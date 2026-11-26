import GenLimit.Paper23_BanachDensityTopologyAndGeometry.DenseBoxGeneration
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.IdentificationCheck
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.OrderedBoards
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.ChainGeneration
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RectangleColoring
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.IntervalOptimality
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.ReorderedIntervals
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.CubeObstruction
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.CubeOptimality
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RectangleObstruction
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.AmbientWindows
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.Results.Supporting

/-! # Main results of Kleinberg and Wei on Banach density and geometry -/

namespace GenLimit.KleinbergWei.Banach.Results

/-- Overview Theorem 2.2 / Corollary 4.2. There is a countable family
of infinite languages, containing ℕ, on which every valid generator has
an exact injective presentation of ℕ with lower Banach density zero. -/
theorem theorem_2_2 :
    ∃ C : Set (Set ℕ), C.Countable ∧ Set.univ ∈ C ∧ (∀ K ∈ C, K.Infinite) ∧
      ∀ A : List ℕ → ℕ,
        (∀ K ∈ C, ∀ s : ℕ → ℕ, Set.range s = K → Function.Injective s →
          ∃ T, ∀ t ≥ T, A (textPrefix s t) ∈ K ∧ A (textPrefix s t) ∉ textPrefix s t) →
        ∃ s : ℕ → ℕ, Function.Injective s ∧ Set.range s = Set.univ ∧
          lowerBanachDensity (Set.range fun t => A (textPrefix s (t+1))) = 0 := by
  refine ⟨Adversary.periodicFamily,Adversary.periodic_countable,Adversary.univ_member,?_,?_⟩
  · rintro _ ⟨⟨p,k,j⟩,rfl⟩; exact Adversary.level_infinite p (Nat.succ_pos k) j
  · intro A valid
    let B (p : List ℕ) : Finset ℕ := {A p}
    have good : Adversary.ValidOn B Adversary.periodicFamily := by
      intro K hK s eq inj
      obtain ⟨T,hT⟩ := valid K hK s eq inj
      exact ⟨T,fun t ht x hx => (Finset.mem_singleton.mp hx).symm ▸ hT t ht⟩
    obtain ⟨s,inj,all,zero⟩ := Adversary.unrestricted_obstruction B good
    exact ⟨s,inj,all,by simpa [B,Set.range,eq_comm] using zero⟩

/-- Theorem 4.1 with ambient endpoints and a target-count denominator.
A single sparse hard target works for every valid finite-output generator. -/
theorem theorem_4_1_ambient (f : ℕ → WithTop ℕ) (mono : Monotone f)
    (unbounded : ∀ n : ℕ, ∃ k, (n : WithTop ℕ) ≤ f k) :
    ∃ C : Set (Set ℕ), C.Countable ∧ (∀ L ∈ C, L.Infinite) ∧
      ∃ K ∈ C, ∀ A : List ℕ → Finset ℕ, Adversary.ValidOn A C →
        ∃ s : ℕ → ℕ, Set.range s = K ∧ Function.Injective s ∧
          Adversary.ambientRelativeWindowDensity f {x | ∃ t, x ∈ A (textPrefix s (t+1))} K = 0 :=
  Adversary.ambient_obstruction f mono unbounded

/-- Corollary 4.3. The same family obstructs every finite output speed.
The proof even permits the size of each finite output to depend on the history. -/
theorem corollary_4_3 :
    ∃ C : Set (Set ℕ), C.Countable ∧ Set.univ ∈ C ∧ (∀ K ∈ C, K.Infinite) ∧
      ∀ A : List ℕ → Finset ℕ, Adversary.ValidOn A C →
        ∃ s : ℕ → ℕ, Function.Injective s ∧ Set.range s = Set.univ ∧
          lowerBanachDensity {x | ∃ t, x ∈ A (textPrefix s (t+1))} = 0 := by
  refine ⟨Adversary.periodicFamily,Adversary.periodic_countable,Adversary.univ_member,?_,
    Adversary.unrestricted_obstruction⟩
  rintro _ ⟨⟨p,k,j⟩,rfl⟩; exact Adversary.level_infinite p (Nat.succ_pos k) j

open DensityMeasures

/-- Theorem 4.5 and Overview 2.3. One generator attains half of each
finite-rank target in lower Banach density. Even the singleton class
containing the known language ℕ forces the matching speed-one upper bound. -/
theorem theorem_4_5 :
    (∀ (C : LanguageFamily) (inf : ∀ z, (C z).Infinite) (R : ℕ),
      FiniteRankAtMost (Set.range C) R →
      ∃ A : List ℕ → ℕ, ∀ z s, Presents s (C z) →
        OrderedFocus.ElementValid s (OrderedFocus.play A s) (C z) ∧
        ENNReal.ofReal (1/2) ≤ lowerBanachDensity
          ((OrderedLanguage.increasing (C z) (inf z)).rankSet (Set.range (OrderedFocus.play A s)))) ∧
    (FiniteRankAtMost (Set.range fun _ : ℕ => (Set.univ : Set ℕ)) 1 ∧
      ∀ A : List ℕ → ℕ, (∀ s, Presents s Set.univ →
        OrderedFocus.ElementValid s (OrderedFocus.play A s) Set.univ) →
        ∃ s, Function.Injective s ∧ Presents s Set.univ ∧
          lowerBanachDensity (Set.range (OrderedFocus.play A s)) ≤ ENNReal.ofReal (1/2)) := by
  refine ⟨fun C inf _ hr => finite_rank_generation C inf hr,singleton_rank_one,fun A valid => ?_⟩
  obtain ⟨s,inj,pres,upper⟩ := singleton_window_upper A valid
  refine ⟨s,inj,pres,?_⟩
  simpa only [lowerWindowDensity_top] using upper (fun _ => ⊤) ⟨monotone_const,fun _ => le_top⟩

/-- Corollary 4.6. The generator simultaneously handles all admissible
window bounds, including the unbounded bounds of the source statement. -/
theorem corollary_4_6 (C : LanguageFamily) (inf : ∀ z, (C z).Infinite)
    {R : ℕ} (hr : FiniteRankAtMost (Set.range C) R) :
    ∃ A : List ℕ → ℕ, ∀ z s, Presents s (C z) →
      OrderedFocus.ElementValid s (OrderedFocus.play A s) (C z) ∧
      ∀ f, AdmissibleWindowBound f → ENNReal.ofReal (1/2) ≤ lowerWindowDensity f
        ((OrderedLanguage.increasing (C z) (inf z)).rankSet (Set.range (OrderedFocus.play A s))) := by
  obtain ⟨A,good⟩ := finite_rank_generation C inf hr
  refine ⟨A,fun z s pres => ?_⟩
  obtain ⟨valid,half⟩ := good z s pres
  exact ⟨valid,fun _ hf => half.trans (lowerBanachDensity_le_windowDensity hf)⟩

/-- Corollary 4.7. For any prescribed reordering e, the original words
can be generated validly with the half-density guarantee in that order. -/
theorem corollary_4_7 (C : LanguageFamily) (inf : ∀ z, (C z).Infinite)
    {R : ℕ} (hr : FiniteRankAtMost (Set.range C) R) (e : ℕ ≃ ℕ) :
    ∃ A : List ℕ → ℕ, ∀ z s, Presents s (C z) →
      OrderedFocus.ElementValid s (OrderedFocus.play A s) (C z) ∧
      ENNReal.ofReal (1/2) ≤ lowerBanachDensity
        ((OrderedLanguage.increasing (e ⁻¹' C z) ((inf z).preimage (fun x _ => e.surjective x))).rankSet
          (e ⁻¹' Set.range (OrderedFocus.play A s))) :=
  reordered_generation C inf hr e

/-- Overview Theorem 2.4 / Theorem 5.1, using the rectangular density of
Definition 1.1 and the output-count growth premise printed in Section 5.
The same exact enumeration witnesses both limits for each valid generator. -/
theorem theorem_5_1 (d : ℕ) :
    ∃ K : Set (Lattice (d+2)), K.Infinite ∧
      ∀ A : List (Lattice (d+2)) → Lattice (d+2),
        (∀ s : ℕ → Lattice (d+2), Set.range s = K → Function.Injective s →
          ∃ T, ∀ t ≥ T, A (textPrefix s t) ∈ K ∧ A (textPrefix s t) ∉ textPrefix s t) →
        ∃ s : ℕ → Lattice (d+2), Set.range s = K ∧ Function.Injective s ∧
          Rectangles.lowerDensity (Set.range (cubePlay A s)) K = 0 ∧
          Rectangles.outputThresholdDensity (Set.range (cubePlay A s)) K = 0 :=
  ⟨Rectangles.language d,Rectangles.infinite d,Rectangles.obstruction d⟩

/-- Corrected Corollary 5.4, including the strengthening to translated
cubes. A single presentation works for every growing nondecreasing
filter that admits arbitrarily large volume-to-denominator ratios. -/
theorem corollary_5_4_corrected (d : ℕ) :
    ∃ C : Set (Set (Lattice (d+1))), C.Countable ∧ (∀ L ∈ C, L.Infinite) ∧
      ∃ K ∈ C, ∀ A : List (Lattice (d+1)) → Finset (Lattice (d+1)),
        (∀ L ∈ C, ∀ s : ℕ → Lattice (d+1), Set.range s = L → Function.Injective s →
          ∃ T, ∀ t ≥ T, ∀ x ∈ A (textPrefix s t), x ∈ L ∧ x ∉ textPrefix s t) →
        ∃ s : ℕ → Lattice (d+1), Set.range s = K ∧ Function.Injective s ∧
          ∀ f : ℕ → ℝ, Monotone f → Filter.Tendsto f Filter.atTop Filter.atTop →
          FilteredObstruction.feasible f →
          filteredRectangularDensityOn MovingCubes.IsCube f {x | ∃ j, x ∈ A (textPrefix s (j+1))} K = 0 := by
  obtain ⟨C,count,inf,K,mem,force⟩ := CubeObstruction.sufficient d
  refine ⟨C,count,inf,K,mem,fun A valid => ?_⟩
  obtain ⟨s,full,inj,zero⟩ := force A valid
  exact ⟨s,full,inj,fun f mono grows feasible => zero f
    (CubeObstruction.of_rectangular_feasible (Nat.succ_pos d) mono grows feasible)⟩

/-- Theorem 5.5 for chain targets. For each divergent filter, one generator is valid
on every target and attains density at least one half on each target whose points are
pairwise comparable coordinatewise. This includes every target on the integer line.
When `e` is monotone, `filtered_chain_generation` in `ChainGeneration.lean` gives
one generator that works for all divergent filters simultaneously. -/
theorem theorem_5_5_on_chain_targets {d : ℕ} (e : ℕ → Lattice d) (inj : Function.Injective e)
    (C : LanguageFamily) (inf : ∀ z, (C z).Infinite) {R : ℕ}
    (rank : TowerTopology.FiniteRankAtMost (Set.range C) R)
    (f : ℕ → ℝ) (grows : Filter.Tendsto f Filter.atTop Filter.atTop) :
    ∃ G : List (Lattice d) → Lattice d, ∀ z s, Set.range s = e '' C z →
      cubeValid G s (e '' C z) ∧
        ((∀ x ∈ C z, ∀ y ∈ C z, e x ≤ e y ∨ e y ≤ e x) →
          ENNReal.ofReal (1/2) ≤ filteredRectangularDensity f (Set.range (cubePlay G s)) (e '' C z)) :=
  OrderedBoards.on_chain_targets e inj C inf rank f grows

/-- Theorem 5.5 when high-threshold boxes have a positive lower bound on target
occupancy. The same generator handles every presentation and filter at this floor. -/
theorem theorem_5_5_positive_occupancy {d : ℕ} (e : ℕ → Lattice d) (inj : Function.Injective e)
    (C : LanguageFamily) (inf : ∀ z, (C z).Infinite) {R : ℕ}
    (rank : TowerTopology.FiniteRankAtMost (Set.range C) R)
    {ε ρ : ℝ} (he : 0 < ε) (density : 0 < ρ) :
    ∃ A : List (Lattice d) → Lattice d, ∀ z (s : ℕ → Lattice d), Set.range s = e '' C z →
      cubeValid A s (e '' C z) ∧ ∀ f : ℕ → ℝ, Filter.Tendsto f Filter.atTop Filter.atTop →
        (∃ N : ℕ, ∀ l u, admissibleBox f (e '' C z) N (l,u) →
          ρ*geometricVolume l u ≤ (Rectangles.box (e '' C z) l u).card) →
        ENNReal.ofReal (1/2-ε) ≤ filteredRectangularDensity f (Set.range (cubePlay A s)) (e '' C z) :=
  filtered_dense_box_generation e inj C inf rank he density

/-- Counterexample to Corollary 5.7 under exact identification. The rank-two
family admits a valid generator attaining half for the fixed-shape density
(19). No learner and generator can satisfy the two published conclusions
together, even on injective full presentations. -/
theorem corollary_5_7_counterexample (d : ℕ) (R : FixedShape.Box (d+1))
    (wide : ∀ i, R.1 i < R.2 i) (ε : ℝ) :
    ∃ (C : LanguageFamily) (e : ℕ → Lattice (d+1)), Function.Injective e ∧
      (∀ z, (C z).Infinite) ∧ TowerTopology.FiniteRankAtMost (Set.range C) 2 ∧
      (∃ G : List (Lattice (d+1)) → Lattice (d+1), ∀ z s, Set.range s = e '' C z →
        cubeValid G s (e '' C z) ∧ ENNReal.ofReal (1/2) ≤
          FixedShape.density R (Set.range (cubePlay G s)) (e '' C z)) ∧
      ¬ ∃ (M : List (Lattice (d+1)) → Set (Lattice (d+1))) (G : List (Lattice (d+1)) → Lattice (d+1)),
        ∀ z s, Set.range s = e '' C z → Function.Injective s →
          (∃ T, ∀ t ≥ T, M (textPrefix s t) = e '' C z) ∧
          ENNReal.ofReal (1/2-ε) ≤ FixedShape.density R (Set.range (cubePlay G s)) (e '' C z) := by
  obtain ⟨C,e,inj,inf,rank,⟨G,generate⟩,cannot⟩ := IdentificationCheck.fixed_shape_separation d
  refine ⟨C,e,inj,inf,rank,⟨G,fun z s full => ?_⟩,?_⟩
  · obtain ⟨valid,lower⟩ := generate z s full
    exact ⟨valid,lower R wide⟩
  · rintro ⟨M,A,both⟩
    exact cannot ⟨M,fun z s full one => (both z s full one).1⟩

/-- Theorem 5.8. A single generator works for all targets in the countable
family. In every positive dimension a singleton class gives the matching
speed-one upper bound against any generator valid on that class. -/
theorem theorem_5_8 :
    (∀ (d : ℕ) (C : ℕ → Set (Lattice d)), (∀ z, (C z).Infinite) →
      ∃ A : List (Lattice d) → Lattice d, ∀ z s, Set.range s = C z →
        cubeValid A s (C z) ∧
          1 / 2 ≤ centeredLowerDensity (Set.range (cubePlay A s)) (C z)) ∧
    (∀ d : ℕ, ∃ K : Set (Lattice (d+1)), K.Infinite ∧
      ∀ A : List (Lattice (d+1)) → Lattice (d+1),
        (∀ s, Set.range s = K → cubeValid A s K) →
        ∃ s, Function.Injective s ∧ Set.range s = K ∧
          centeredLowerDensity (Set.range (cubePlay A s)) K ≤ 1 / 2) :=
  ⟨fun _ C => centered_generation C, centered_singleton_upper⟩

/-- Corrected Theorem 5.9. The longest side counts lattice sites, and the
least nonnegative tier includes dense overflow. One coloring of the
whole lattice works for every nonempty rectangular trace of P with the
published discrepancy constants. -/
theorem theorem_5_9_corrected {d : ℕ} (hd : 0 < d) (P : Set (Lattice d))
    (ε α : ℝ) (he : 0 < ε) (ha : 0 < α) :
    ∃ color : Lattice d → Bool, ∀ l u, ∀ h : (Rectangles.box P l u).Nonempty,
      let m := (Rectangles.box P l u).card
      let j := TierGeometry.tier
        (TierGeometry.baseline ε α d * (TierGeometry.span l u : ℝ)^α) m h.card_pos
      |∑ v ∈ Rectangles.box P l u, RandomSigns.sign (color v)| ≤
        TierWeights.threshold ε (TierGeometry.scale d α) m j :=
  rectangle_coloring hd P ε α he ha

end GenLimit.KleinbergWei.Banach.Results
