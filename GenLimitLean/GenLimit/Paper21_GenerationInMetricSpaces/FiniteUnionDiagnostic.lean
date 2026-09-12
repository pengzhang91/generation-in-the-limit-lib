import GenLimit.Paper21_GenerationInMetricSpaces.NonuniformCharacterization
import GenLimit.Paper21_GenerationInMetricSpaces.Common.WeightedStarMetric
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Countable
import Mathlib.Topology.MetricSpace.Basic

/-!
# Theorems 3.5--3.6: finite-union diagnostic and concrete separation

Source: Jiaxun Li, Vinod Raman, and Ambuj Tewari,
*On Generation in Metric Spaces*, arXiv:2602.07710v1.

Printed Theorem 3.5 claims that a finite union of classes with finite
`(ε, ε')`-scale-closure dimension is `(ε, ε')`-generatable in the limit.
The proof tries to detect the target component by measuring how much of a
dense common-core sequence has entered the closed `ε`-neighbourhood of the
observed prefix.

That argument is not valid for the source's closed-neighbourhood semantics:

* membership in the closed neighbourhood of an infinite range is an
  infimum condition and need not occur at any finite prefix;
* a point outside the target may nevertheless lie in its `ε`-neighbourhood.

The omitted-hub weighted star below turns the first defect into an exact
counterexample to the theorem statement.  Two targets share a countable
core whose radii tend to zero.  A stream enumerating that core is a
radius-one presentation of either target, even though no tail point is in
the radius-one neighbourhood of any finite prefix.  The shared core itself
is covered at radius one after two observations.  Hence the common stream
eventually admits no output correct for both targets.

Each singleton component has scale-closure dimension zero: its only
nonempty version-space core is its target, which has no finite radius-one
cover.  Thus both components are uniformly generatable, while their
two-element union is not generatable in the limit.

An additional remote tail makes the whole ambient space have infinite
radius-two covering number.  Consequently the same construction gives the
positive existential content of Theorem 3.6 at `r = 2` and
`ε = ε' = 1`, in the stronger form where both component classes are
uniformly generatable.  The source's universal transport to every ambient
space of infinite `r`-covering number is proved separately in `Theorem36`.
-/

namespace GenLimit.MetricSpaces.FiniteUnionCounterexample

noncomputable section

/-- A countable star with its zero-radius hub omitted. -/
inductive Point where
  | core (n : ℕ)
  | tail (side : Bool) (n : ℕ)
  | remote (n : ℕ)
  deriving DecidableEq

open Point

private def pointCode :
    Point → ℕ ⊕ ((Bool × ℕ) ⊕ ℕ)
  | core n => Sum.inl n
  | tail side n => Sum.inr (Sum.inl (side, n))
  | remote n => Sum.inr (Sum.inr n)

private theorem pointCode_injective :
    Function.Injective pointCode := by
  intro x y h
  cases x <;> cases y <;>
    simp_all [pointCode]

instance instCountablePoint : Countable Point :=
  pointCode_injective.countable

instance instNonemptyPoint : Nonempty Point :=
  ⟨core 0⟩

/-- The omitted-hub arm length.  Core arms converge to zero, target-tail
arms have length one, and remote arms have length three. -/
def radius : Point → ℝ
  | core n => 1 / (n + 1 : ℝ)
  | tail _ _ => 1
  | remote _ => 3

private theorem radius_pos (x : Point) :
    0 < radius x := by
  cases x with
  | core n =>
      simp only [radius]
      positivity
  | tail side n =>
      norm_num [radius]
  | remote n =>
      norm_num [radius]

private theorem radius_nonneg (x : Point) :
    0 ≤ radius x :=
  (radius_pos x).le

/-- Distinct points have distance equal to the sum of their arm lengths. -/
def starDistance : Distance Point :=
  fun x y => if x = y then 0 else radius x + radius y

@[simp] theorem starDistance_self (x : Point) :
    starDistance x x = 0 :=
  WeightedStar.distance_self radius x

theorem starDistance_comm (x y : Point) :
    starDistance x y = starDistance y x :=
  WeightedStar.distance_comm radius x y

theorem starDistance_triangle (x y z : Point) :
    starDistance x z ≤
      starDistance x y + starDistance y z :=
  WeightedStar.distance_triangle radius radius_nonneg x y z

private theorem radius_pair_pos
    {x y : Point} (_hxy : x ≠ y) :
    0 < radius x + radius y :=
  add_pos (radius_pos x) (radius_pos y)

/-- The explicit kernel is a genuine metric. -/
instance instMetricSpacePoint : MetricSpace Point where
  dist := starDistance
  dist_self := starDistance_self
  dist_comm := starDistance_comm
  dist_triangle := starDistance_triangle
  eq_of_dist_eq_zero :=
    WeightedStar.eq_of_distance_eq_zero radius radius_pair_pos

/-- The example space is countable, hence separable. -/
theorem point_separable :
    TopologicalSpace.SeparableSpace Point := by
  infer_instance

/-- The shared sequence converging to the omitted hub. -/
def coreSet : Set Point :=
  Set.range core

/-- The private tail on one side of the counterexample. -/
def tailSet (side : Bool) : Set Point :=
  Set.range (tail side)

/-- One target consists of the shared core and one private tail. -/
def target (side : Bool) : GenLimit.Generic.Language Point :=
  coreSet ∪ tailSet side

/-- The singleton class containing one target. -/
def targetClass (side : Bool) :
    GenLimit.Generic.LanguageClass Point :=
  {target side}

/-- The two-element class in the finite-union counterexample. -/
def pairedClass : GenLimit.Generic.LanguageClass Point :=
  targetClass false ∪ targetClass true

/-- The displayed pair is literally a finite `Bool`-indexed class cover. -/
theorem pairedClass_eq_iUnion_targetClass :
    pairedClass = ⋃ side : Bool, targetClass side := by
  ext L
  simp [pairedClass]

/-- The common adversarial stream enumerates the shared core. -/
def commonStream : GenLimit.Generic.Stream Point :=
  core

@[simp] theorem commonStream_range :
    Set.range commonStream = coreSet :=
  rfl

private theorem core_mem_target (side : Bool) (n : ℕ) :
    core n ∈ target side :=
  Set.mem_union_left _ ⟨n, rfl⟩

private theorem tail_mem_target (side : Bool) (n : ℕ) :
    tail side n ∈ target side :=
  Set.mem_union_right _ ⟨n, rfl⟩

private theorem core_radius_tends_to_zero
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ n, radius (core n) < δ := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  exact ⟨n, by simpa only [radius] using hn⟩

/-- Every private tail point lies in the closed radius-one neighbourhood of
the infinite shared core, with the boundary infimum never attained. -/
theorem tail_mem_closedNeighborhood_coreSet
    (side : Bool) (n : ℕ) :
    tail side n ∈
      closedNeighborhood starDistance coreSet 1 := by
  intro η hη
  obtain ⟨k, hk⟩ :=
    core_radius_tends_to_zero (sub_pos.mpr hη)
  refine ⟨core k, ⟨k, rfl⟩, ?_⟩
  rw [starDistance, if_neg (by simp), radius]
  simp only [radius] at hk ⊢
  linarith

/-- The shared core stream is a valid radius-one presentation of either
target. -/
theorem commonStream_metricPresentation
    (side : Bool) :
    MetricPresentation starDistance 1 commonStream (target side) := by
  constructor
  · rintro x ⟨n, rfl⟩
    exact core_mem_target side n
  · intro x hx
    rcases hx with hxCore | hxTail
    · obtain ⟨n, rfl⟩ := hxCore
      intro η hη
      exact ⟨core n, ⟨n, rfl⟩,
        by rw [starDistance_self]; linarith⟩
    · obtain ⟨n, rfl⟩ := hxTail
      exact tail_mem_closedNeighborhood_coreSet side n

private theorem core_succ_radius_le_half (n : ℕ) :
    radius (core (n + 1)) ≤ (1 / 2 : ℝ) := by
  simp only [radius]
  apply one_div_le_one_div_of_le
  · norm_num
  · have hn : 0 ≤ (n : ℝ) := by positivity
    push_cast
    linarith

private theorem core_one_distance_core_succ_le_one
    (n : ℕ) :
    starDistance (core 1) (core (n + 1)) ≤ 1 := by
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [starDistance, if_neg (by simp), radius]
      have hbound := core_succ_radius_le_half (n + 1)
      norm_num at hbound ⊢
      linarith

/-- After the first two shared observations, their radius-one
neighbourhood contains the whole shared core. -/
theorem coreSet_subset_sample_two_neighborhood :
    coreSet ⊆
      closedNeighborhood starDistance
        (GenLimit.Generic.sample commonStream 2 : Set Point) 1 := by
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  cases n with
  | zero =>
      intro η hη
      refine ⟨core 0, ?_, ?_⟩
      · exact GenLimit.Generic.mem_sample_iff.mpr
          ⟨0, by omega, rfl⟩
      · rw [starDistance_self]
        linarith
  | succ n =>
      intro η hη
      refine ⟨core 1, ?_, ?_⟩
      · exact GenLimit.Generic.mem_sample_iff.mpr
          ⟨1, by omega, rfl⟩
      · exact
          lt_of_le_of_lt
            (core_one_distance_core_succ_le_one n) hη

/-- The two targets intersect exactly in the shared core. -/
theorem target_false_inter_target_true :
    target false ∩ target true = coreSet := by
  ext x
  cases x with
  | core n =>
      simp [target, coreSet, tailSet]
  | tail side n =>
      cases side <;>
        simp [target, coreSet, tailSet]
  | remote n =>
      simp [target, coreSet, tailSet]

private theorem tail_injective (side : Bool) :
    Function.Injective (tail side) := by
  intro n m h
  cases h
  rfl

/-- Every finite ambient-center set has a strictly positive minimum arm
length. -/
private theorem finite_centers_min_radius_pos
    (centers : Finset Point) (hcenters : centers.Nonempty) :
    0 <
      (centers.image radius).min'
        (hcenters.image radius) := by
  have hmem :=
    Finset.min'_mem (centers.image radius)
      (hcenters.image radius)
  obtain ⟨x, _hx, hxradius⟩ :=
    Finset.mem_image.mp hmem
  rw [← hxradius]
  exact radius_pos x

private theorem tail_not_mem_closedNeighborhood_finset
    (side : Bool) (n : ℕ) (centers : Finset Point)
    (hTailCenters : tail side n ∉ centers) :
    tail side n ∉
      closedNeighborhood starDistance (centers : Set Point) 1 := by
  intro hnear
  by_cases hcenters : centers.Nonempty
  · let radii := centers.image radius
    let m := radii.min' (hcenters.image radius)
    have hmPos : 0 < m :=
      finite_centers_min_radius_pos centers hcenters
    obtain ⟨y, hyCenters, hydist⟩ :=
      hnear (1 + m / 2) (by linarith)
    have hyNe : y ≠ tail side n := by
      intro hy
      subst y
      exact hTailCenters hyCenters
    have hmLe : m ≤ radius y := by
      exact Finset.min'_le radii (radius y)
        (Finset.mem_image.mpr ⟨y, hyCenters, rfl⟩)
    rw [starDistance, if_neg hyNe, radius] at hydist
    linarith
  · have hEmpty : centers = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcenters
    subst centers
    obtain ⟨y, hy, _⟩ := hnear 2 (by norm_num)
    simp at hy

/-- The boundary membership in the infinite-range neighbourhood is never
witnessed by a finite prefix.  This is the first invalid inference in the
printed proof of Theorem 3.5. -/
theorem tail_not_mem_finite_prefix_neighborhood
    (side : Bool) (n t : ℕ) :
    tail side n ∉
      closedNeighborhood starDistance
        (GenLimit.Generic.sample commonStream t : Set Point) 1 := by
  apply tail_not_mem_closedNeighborhood_finset
  intro hmem
  obtain ⟨k, _hkt, hEq⟩ :=
    GenLimit.Generic.mem_sample_iff.mp hmem
  change core k = tail side n at hEq
  cases hEq

/-- Neither target has a finite closed radius-one cover. -/
theorem target_not_hasFiniteCover_one (side : Bool) :
    ¬ HasFiniteCover starDistance 1 (target side) := by
  rintro ⟨centers, hcover⟩
  have htailInfinite :
      (Set.range (tail side)).Infinite :=
    Set.infinite_range_of_injective
      (tail_injective side)
  obtain ⟨x, ⟨n, rfl⟩, hxCenters⟩ :=
    htailInfinite.exists_notMem_finset centers
  exact
    tail_not_mem_closedNeighborhood_finset
      side n centers hxCenters
      (hcover (tail_mem_target side n))

/-- The paired class satisfies radius-one UUS. -/
theorem pairedClass_uus :
    UniformlyUnboundedSupportAt starDistance 1 pairedClass := by
  intro L hL
  rcases hL with hL | hL
  · have hEq : L = target false :=
      Set.mem_singleton_iff.mp hL
    subst L
    exact target_not_hasFiniteCover_one false
  · have hEq : L = target true :=
      Set.mem_singleton_iff.mp hL
    subst L
    exact target_not_hasFiniteCover_one true

/-- A nonempty singleton version space has the singleton target as its
common core. -/
theorem commonCore_singleton_eq
    {L : GenLimit.Generic.Language Point}
    {S : Finset Point}
    (hversion :
      (versionSpace
        ({L} : GenLimit.Generic.LanguageClass Point) S).Nonempty) :
    commonCore ({L} : GenLimit.Generic.LanguageClass Point) S = L := by
  obtain ⟨K, hKClass, hSK⟩ := hversion
  have hKL : K = L :=
    Set.mem_singleton_iff.mp hKClass
  have hSL : (S : Set Point) ⊆ L := by
    simpa [hKL] using hSK
  apply Set.Subset.antisymm
  · intro x hx
    exact hx L ⟨Set.mem_singleton L, hSL⟩
  · intro x hx K hK
    have hKL' : K = L :=
      Set.mem_singleton_iff.mp hK.1
    simpa [hKL'] using hx

/-- If a target has no finite novelty-scale cover, its singleton class has
scale-closure dimension zero. -/
theorem singleton_hasFiniteScaleClosureDimension_of_no_finiteCover
    {ρ : Distance Point} {ε ε' : ℝ}
    {L : GenLimit.Generic.Language Point}
    (hNoCover : ¬ HasFiniteCover ρ ε' L) :
    HasFiniteScaleClosureDimension ρ ε ε'
      ({L} : GenLimit.Generic.LanguageClass Point) := by
  refine ⟨0, ?_⟩
  intro d _hd
  rintro ⟨S, hversion, _hcoveringEq, hcoreCover⟩
  apply hNoCover
  rw [commonCore_singleton_eq hversion] at hcoreCover
  exact hcoreCover

/-- Each singleton component has `(1,1)`-scale-closure dimension zero. -/
theorem targetClass_finiteScaleClosureDimension
    (side : Bool) :
    HasFiniteScaleClosureDimension starDistance 1 1
      (targetClass side) := by
  exact
    singleton_hasFiniteScaleClosureDimension_of_no_finiteCover
      (target_not_hasFiniteCover_one side)

/-- Each component is uniformly generatable by the valid sufficiency half
of Theorem 3.1. -/
theorem targetClass_uniformlyGeneratable
    (side : Bool) :
    UniformlyGeneratableAt starDistance 1 1
      (targetClass side) := by
  exact finite_scaleClosureDimension_implies_uniform
    starDistance_self (by norm_num)
      (targetClass_finiteScaleClosureDimension side)

/-- The shared presentation defeats every proposed limit generator for the
two-element union. -/
theorem pairedClass_not_generatableInLimit :
    ¬ GeneratableInLimitAt starDistance 1 1 pairedClass := by
  rintro ⟨gen, hgen⟩
  have hFalseClass : target false ∈ pairedClass :=
    Or.inl (Set.mem_singleton (target false))
  have hTrueClass : target true ∈ pairedClass :=
    Or.inr (Set.mem_singleton (target true))
  obtain ⟨TFalse, hFalse⟩ :=
    hgen (target false) hFalseClass commonStream
      (commonStream_metricPresentation false)
  obtain ⟨TTrue, hTrue⟩ :=
    hgen (target true) hTrueClass commonStream
      (commonStream_metricPresentation true)
  let s := max (max TFalse TTrue) 2
  have hTFalse : TFalse ≤ s :=
    (Nat.le_max_left TFalse TTrue).trans
      (Nat.le_max_left (max TFalse TTrue) 2)
  have hTTrue : TTrue ≤ s :=
    (Nat.le_max_right TFalse TTrue).trans
      (Nat.le_max_left (max TFalse TTrue) 2)
  have hTwo : 2 ≤ s :=
    Nat.le_max_right (max TFalse TTrue) 2
  have hCorrectFalse := hFalse s hTFalse
  have hCorrectTrue := hTrue s hTTrue
  have hOutputCore :
      GenLimit.Generic.output gen commonStream s ∈ coreSet := by
    rw [← target_false_inter_target_true]
    exact ⟨hCorrectFalse.1, hCorrectTrue.1⟩
  have hSampleMono :
      (GenLimit.Generic.sample commonStream 2 : Set Point) ⊆
        (GenLimit.Generic.sample commonStream s : Set Point) :=
    GenLimit.Generic.sample_mono hTwo
  have hOutputNear :
      GenLimit.Generic.output gen commonStream s ∈
        closedNeighborhood starDistance
          (GenLimit.Generic.sample commonStream s : Set Point) 1 :=
    inClosedNeighborhood_mono_centers hSampleMono
      (coreSet_subset_sample_two_neighborhood hOutputCore)
  exact hCorrectFalse.2 hOutputNear

private theorem remote_injective :
    Function.Injective remote := by
  intro n m h
  cases h
  rfl

/-- The remote arms make the ambient radius-two covering number infinite. -/
theorem univ_not_hasFiniteCover_two :
    ¬ HasFiniteCover starDistance 2 (Set.univ : Set Point) := by
  rintro ⟨centers, hcover⟩
  have hremoteInfinite :
      (Set.range remote).Infinite :=
    Set.infinite_range_of_injective remote_injective
  obtain ⟨x, ⟨n, rfl⟩, hxCenters⟩ :=
    hremoteInfinite.exists_notMem_finset centers
  obtain ⟨y, hyCenters, hydist⟩ :=
    hcover (Set.mem_univ (remote n))
      (5 / 2 : ℝ) (by norm_num)
  have hyNe : y ≠ remote n := by
    intro hy
    subst y
    exact hxCenters hyCenters
  rw [starDistance, if_neg hyNe, radius] at hydist
  have hyRadius := radius_pos y
  linarith

/-- Exact counterexample to printed Theorem 3.5.  All scales are positive,
the ambient metric is separable, the union is UUS, and both members of the
finite class cover have finite scale-closure dimension. -/
theorem theorem_3_5_finite_union_implication_false :
    TopologicalSpace.SeparableSpace Point ∧
      UniformlyUnboundedSupportAt starDistance 1 pairedClass ∧
      pairedClass = ⋃ side : Bool, targetClass side ∧
      (∀ side,
        HasFiniteScaleClosureDimension starDistance 1 1
          (targetClass side)) ∧
      ¬ GeneratableInLimitAt starDistance 1 1 pairedClass :=
  ⟨point_separable, pairedClass_uus,
    pairedClass_eq_iUnion_targetClass,
    targetClass_finiteScaleClosureDimension,
    pairedClass_not_generatableInLimit⟩

/-- A concrete, stronger separation of the form asserted by Theorem 3.6.
At `r = 2` and `ε = ε' = r/2`, the ambient space has infinite
`r`-covering number, both component classes are uniform (hence the second is
non-uniform), but their union is not generatable in the limit. -/
theorem theorem_3_6_concrete_stronger_separation :
    ¬ HasFiniteCover starDistance 2 (Set.univ : Set Point) ∧
      UniformlyGeneratableAt starDistance 1 1
        (targetClass false) ∧
      NonuniformlyGeneratableAt starDistance 1 1
        (targetClass true) ∧
      ¬ GeneratableInLimitAt starDistance 1 1
        (targetClass false ∪ targetClass true) := by
  refine ⟨univ_not_hasFiniteCover_two,
    targetClass_uniformlyGeneratable false,
    metric_uniform_implies_nonuniform
      (targetClass_uniformlyGeneratable true), ?_⟩
  simpa only [pairedClass] using
    pairedClass_not_generatableInLimit

end

end GenLimit.MetricSpaces.FiniteUnionCounterexample
